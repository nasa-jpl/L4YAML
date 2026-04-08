import Lean4Yaml
import Lean

/-!
# Theorem Coverage Analyzer

Analyzes the quality and coverage of theorems in `Lean4Yaml`:

1. **Leaf theorems** — defined but never cited in any other proof or definition
2. **Short-name duplicates** — same local name appearing in 2+ modules
3. **`native_decide` leaves** — leaf theorems proved by `native_decide`:
   - Ground (0 explicit `∀`): prime candidates for demotion to `#guard`
   - Universal (≥1 explicit `∀`): keep as theorem, consider whether `#guard` coverage is sufficient

## Usage

```
lake build analyzethms
lake exe analyzethms [output-dir]   # default: .
```

Writes four files to `<output-dir>/`:
- `leaf_thms.json`          — all theorems never cited in any other proof
- `native_decide_leaves.json` — leaf theorems using `native_decide`
- `duplicates.json`         — theorems sharing a short name across modules
- `stats.txt`               — summary counts (also printed to stdout)
-/

open Lean

/-- Is the name in the `Lean4Yaml` namespace? -/
private def isProjectName (n : Name) : Bool :=
  match n with
  | .str p _ => p == `Lean4Yaml || isProjectName p
  | .num p _ => isProjectName p
  | .anonymous => false

/-- The last string component of a name (local name). -/
private def lastName : Name → String
  | .str _ s  => s
  | .num _ n  => toString n
  | .anonymous => "<anonymous>"

/-- Count explicit `∀` binders at the head of a type.
    0 = ground proposition (concrete); ≥1 = universally quantified. -/
private def countExplicitForalls : Expr → Nat
  | .forallE _ _ body .default        => 1 + countExplicitForalls body
  | .forallE _ _ body .implicit       => countExplicitForalls body
  | .forallE _ _ body .strictImplicit => countExplicitForalls body
  | .forallE _ _ body .instImplicit   => countExplicitForalls body
  | _                                  => 0

/-- Does the proof term reference `native_decide`? -/
private def usesNativeDecide (e : Expr) : Bool :=
  e.getUsedConstantsAsSet.contains `ofReduceBool

/-- Escape a string for JSON. -/
private def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | _    => acc.push c

/-- Module name for a declaration (falls back to prefix for auto-generated names). -/
private def getModuleName (env : Environment) (n : Name) : String :=
  let idx := env.getModuleIdxFor? n <|> env.getModuleIdxFor? n.getPrefix
  match idx with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none   => "<unknown>"

/-- Start line for a declaration (from `declRangeExt`). -/
private def getLine (env : Environment) (n : Name) : Option Nat :=
  let ranges := declRangeExt.find? (level := .exported) env n <|>
                declRangeExt.find? (level := .server)   env n
  ranges.map fun dr => dr.range.pos.line

/-- Format a source location as a JSON snippet. -/
private def locJson (env : Environment) (n : Name) : String :=
  let modStr  := jsonEscape (getModuleName env n)
  let lineStr := match getLine env n with | some l => toString l | none => "null"
  s!"\"module\":\"{modStr}\",\"line\":{lineStr}"

unsafe def main (args : List String) : IO Unit := do
  let outDir := args.headD "."

  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Lean4Yaml }] {} 0

  IO.FS.createDirAll outDir

  -- ── Collect all project constants ──────────────────────────────────────────
  let allConsts : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc n ci =>
      if isProjectName n then acc.push (n, ci) else acc

  -- ── Build theorem set ──────────────────────────────────────────────────────
  let mut projectThms : NameHashSet := {}
  for (n, ci) in allConsts do
    match ci with
    | .thmInfo _ => projectThms := projectThms.insert n
    | _ => pure ()

  -- ── Compute cited set ─────────────────────────────────────────────────────
  -- A theorem is "cited" if it appears in the proof term (value) of *any*
  -- other declaration in the project (theorem or definition).
  let mut citedThms : NameHashSet := {}
  for (_, ci) in allConsts do
    let proofExpr? : Option Expr := match ci with
      | .thmInfo  v => some v.value
      | .defnInfo v => some v.value
      | _ => none
    if let some e := proofExpr? then
      for dep in e.getUsedConstantsAsSet.toArray do
        if projectThms.contains dep then
          citedThms := citedThms.insert dep

  -- ── 1. Leaf theorems ──────────────────────────────────────────────────────
  let mut leafThms : Array Name :=
    projectThms.toList.toArray.filter (fun n => !citedThms.contains n)
  leafThms := leafThms.qsort (fun a b => a.toString < b.toString)

  -- ── 2. native_decide leaves ───────────────────────────────────────────────
  -- (name, number_of_explicit_foralls)
  let mut ndLeaves : Array (Name × Nat) :=
    leafThms.filterMap fun n =>
      match env.find? n with
      | some (.thmInfo v) =>
        if usesNativeDecide v.value then
          some (n, countExplicitForalls v.type)
        else none
      | _ => none

  -- ── 3. Short-name duplicate groups ────────────────────────────────────────
  -- Group all project theorem names by their local (last) component.
  let sortedByShort :=
    projectThms.toList.toArray.qsort (fun a b =>
      let sa := lastName a; let sb := lastName b
      if sa == sb then a.toString < b.toString else sa < sb)

  let mut dupGroups : Array (String × Array Name) := #[]
  if sortedByShort.size > 0 then
    let mut curShort := lastName sortedByShort[0]!
    let mut curGroup : Array Name := #[sortedByShort[0]!]
    for i in [1:sortedByShort.size] do
      let n := sortedByShort[i]!
      let s := lastName n
      if s == curShort then
        curGroup := curGroup.push n
      else
        if curGroup.size ≥ 2 then
          dupGroups := dupGroups.push (curShort, curGroup)
        curShort := s
        curGroup := #[n]
    if curGroup.size ≥ 2 then
      dupGroups := dupGroups.push (curShort, curGroup)
  -- Filter to duplicates across different modules (same-module pairs are less interesting)
  let crossModuleDups := dupGroups.filter fun (_, names) =>
    let mods := names.map (getModuleName env)
    mods.toList.eraseDups.length ≥ 2

  -- ── Build stats ───────────────────────────────────────────────────────────
  let totalThms      := projectThms.size
  let citedCount     := citedThms.size
  let leafCount      := leafThms.size
  let ndLeafCount    := ndLeaves.size
  let groundNdCount  := ndLeaves.filter (fun (_, nq) => nq == 0) |>.size
  let univNdCount    := ndLeafCount - groundNdCount
  let dupGroupCount  := crossModuleDups.size
  let dupThmCount    := crossModuleDups.foldl (init := 0) fun acc (_, names) => acc + names.size

  -- ── Write leaf_thms.json ─────────────────────────────────────────────────
  let mut leafLines : Array String := #["["]
  for i in [:leafThms.size] do
    let n    := leafThms[i]!
    let comma := if i + 1 < leafThms.size then "," else ""
    let ci?  := env.find? n
    let nq   := match ci? with | some (.thmInfo v) => countExplicitForalls v.type | _ => 0
    let nd   := match ci? with | some (.thmInfo v) => usesNativeDecide v.value    | _ => false
    leafLines := leafLines.push
      s!"  \{{locJson env n},\"name\":\"{jsonEscape n.toString}\",\"foralls\":{nq},\"native_decide\":{nd}}{comma}"
  leafLines := leafLines.push "]"
  IO.FS.writeFile (outDir ++ "/leaf_thms.json") ("\n".intercalate leafLines.toList ++ "\n")

  -- ── Write native_decide_leaves.json ──────────────────────────────────────
  let mut ndLines : Array String := #["["]
  for i in [:ndLeaves.size] do
    let (n, nq) := ndLeaves[i]!
    let comma   := if i + 1 < ndLeaves.size then "," else ""
    let assessment := if nq == 0 then "demote_to_guard" else "keep_as_thm"
    ndLines := ndLines.push
      s!"  \{{locJson env n},\"name\":\"{jsonEscape n.toString}\",\"foralls\":{nq},\"assessment\":\"{assessment}\"}{comma}"
  ndLines := ndLines.push "]"
  IO.FS.writeFile (outDir ++ "/native_decide_leaves.json") ("\n".intercalate ndLines.toList ++ "\n")

  -- ── Write duplicates.json ─────────────────────────────────────────────────
  let mut dupLines : Array String := #["["]
  for i in [:crossModuleDups.size] do
    let (short, names) := crossModuleDups[i]!
    let comma := if i + 1 < crossModuleDups.size then "," else ""
    let occurrences := names.map fun n =>
      let lineStr := match getLine env n with | some l => toString l | none => "null"
      s!"\{\"name\":\"{jsonEscape n.toString}\",\"module\":\"{jsonEscape (getModuleName env n)}\",\"line\":{lineStr}}"
    let occArr := "[" ++ ",".intercalate occurrences.toList ++ "]"
    dupLines := dupLines.push
      s!"  \{\"shortName\":\"{jsonEscape short}\",\"count\":{names.size},\"occurrences\":{occArr}}{comma}"
  dupLines := dupLines.push "]"
  IO.FS.writeFile (outDir ++ "/duplicates.json") ("\n".intercalate dupLines.toList ++ "\n")

  -- ── Write stats.txt ───────────────────────────────────────────────────────
  let pct (n k : Nat) : String :=
    if k == 0 then "0%" else s!"{n * 100 / k}%"
  let statsLines := [
    s!"Total project theorems:              {totalThms}",
    s!"Cited (used in ≥1 proof or def):     {citedCount}  ({pct citedCount totalThms})",
    s!"Leaf (never cited):                  {leafCount}  ({pct leafCount totalThms})",
    s!"  ↳ proved by native_decide:         {ndLeafCount}",
    s!"    ↳ ground (0 explicit ∀) — #guard candidates: {groundNdCount}",
    s!"    ↳ universal (≥1 explicit ∀):     {univNdCount}",
    s!"Cross-module duplicate groups:       {dupGroupCount}",
    s!"  ↳ total theorems in dup groups:    {dupThmCount}",
    s!"",
    s!"Files written to: {outDir}/",
    s!"  leaf_thms.json            ({leafCount} entries)",
    s!"  native_decide_leaves.json ({ndLeafCount} entries)",
    s!"  duplicates.json           ({dupGroupCount} groups)",
    s!"  stats.txt",
  ]
  IO.FS.writeFile (outDir ++ "/stats.txt") ("\n".intercalate statsLines ++ "\n")

  -- ── Print to stdout ───────────────────────────────────────────────────────
  for line in statsLines do
    IO.println line
