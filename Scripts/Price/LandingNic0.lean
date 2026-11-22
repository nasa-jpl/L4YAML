module

public import Scripts.Price.Attribute
meta import Scripts.Price.Attribute

/-!
# Scripts.Price.LandingNic0 — `landing_nic0_price.py` (item 210): item 154's flag at the block landing

A consumer's name or `all` adds `h_nic0_probe` to the landing lemma(s) and counts the SITES
that apply them; `payers` reads what each landing site spends on the flag (no Lean run);
`drop` renames each carrier's real `h_nic0` binder and asks whether its body spends it.
-/

namespace Scripts.Price.LandingNic0

open Scripts.Price.Attribute
open Scripts.Punt.Price (padLeft padRight take isWordChar isLemmaHead)

public section

def lemmas : List (String × String) :=
  [("accum_block_on_noPending", "sp_block"), ("accum_block_on_closeThenBlock", "sp_scan"),
   ("accum_block_on_pendingContent", "sp_scan"), ("accum_block_on_pendingBlockContent", "sp_scan"),
   ("accum_block_on_pendingBlock", "sp_scan")]
def names : List String := lemmas.map (·.1)
def probeLine : String := "    -- LANDING NIC0 PROBE (scripts/landing_nic0_price.py)"
def conclusion : String := "    ∃ sp_gram' sp_block' sp_flow' sp_scan',"
def modes : List String := names ++ ["all", "payers", "drop"]
def usageModes : String := "|".intercalate modes

/-- `next(i for i, l in enumerate(lines) if re.match(rf"^lemma {name}\b", l))`. -/
def lemmaStart (lines : Array String) (name : String) : Except String Nat :=
  match (Array.range lines.size).find? (fun i => isLemmaHead name lines[i]!) with
  | some i => .ok i
  | none => .error s!"StopIteration: lemma {name} not found"

/-- `signature_end(lines, name)`: the `) :` line before the lemma's conclusion. -/
def signatureEnd (lines : Array String) (name : String) : Except String Nat := do
  let start ← lemmaStart lines name
  match (Array.range lines.size).find? (fun i => i ≥ start && lines[i]! == conclusion) with
  | none => throw s!"StopIteration: conclusion of {name} not found"
  | some concl =>
    if !(rstrip lines[concl - 1]!).endsWith ") :" then throw s!"AssertionError: {lines[concl - 1]!}"
    return concl - 1

def applyProbe (lines : Array String) (which : String) : Except String (Array String × Array String) := do
  let targets := if which == "all" then names else [which]
  let mut withEnd : Array (String × Nat) := #[]
  for n in targets do withEnd := withEnd.push (n, ← signatureEnd lines n)
  let mut out := lines
  for (n, _) in bottomUp withEnd do
    let sig ← signatureEnd out n
    let var := (lemmas.lookup n).getD "sp_scan"
    out ← spliceSig out sig probeLine s!"    (h_nic0_probe : {var}.col = 0 → sc.needIndentCheck = true) :"
  return (out, sortedStrs targets.toArray)

/-- `apply_drop(lines, name)`: rename the consumer's `h_nic0` binder (arity kept) → the
    patched lines and the binder's 1-based line. -/
def applyDrop (lines : Array String) (name : String) : Except String (Array String × Nat) := do
  let start ← lemmaStart lines name
  let some stop := (Array.range lines.size).find? (fun i => i ≥ start && lines[i]! == conclusion)
    | throw s!"StopIteration: conclusion of {name} not found"
  let sig := (Array.range lines.size).filter fun i => start ≤ i && i < stop && (lines[i]!.splitOn "(h_nic0 :").length > 1
  if sig.size != 1 then throw s!"AssertionError: {name}: {sig.size} `h_nic0` binders"
  let i := sig[0]!
  return (lines.set! i (lines[i]!.replace "(h_nic0 :" "(h_nic0_dropped :"), i + 1)

def headline (which : String) (ns : Array String) : String := s!"probe: {which} -> {", ".intercalate ns.toList}"

def anchors (patched : Array String) (ns : Array String) : Array Anchor := Id.run do
  let mut out : Array Anchor := #[]
  for i in [0:patched.size] do
    let line := patched[i]!
    for n in ns do
      if (line.splitOn n).length > 1 && !isLemmaHead n line && !isComment line then out := out.push (i + 1, n)
  return out

def report (patched : Array String) (ns : Array String) (log : String) : Array String := Id.run do
  let census := errorLines log
  let (groups, unanchored) := anchorErrors (anchors patched ns) (sortedNat census)
  let decls := byDecl patched groups unanchored
  let mut out : Array String := #["", s!"raw error sites: {census.size}",
    s!"applications:    {groups.size + unanchored.size}   <- the site census",
    s!"declarations:    {decls.size}", ""]
  out := out ++ declLines decls
  if ns.size > 1 then
    out := out.push "" |>.push "by probed lemma:"
    for n in ns do
      let lns := sortedNat ((groups.filter fun ((_, m), _) => m == n).map (·.1.1))
      out := out.push s!"  {padLeft (toString lns.size) 3}  {padRight n 36} {joinL lns}"
  let casc := cascades groups
  if !casc.isEmpty then
    out := out.push "" |>.push s!"collapsed cascades ({cascadeCount groups} errors were not sites):"
    for ((aline, n), hits) in casc do
      out := out.push s!"  L{aline}  {n}  <- errors at {joinNats hits}"
  if !unanchored.isEmpty then
    out := out.push "" |>.push s!"UNANCHORED ({unanchored.size}): no application precedes these, so they are counted one-for-one and the total is a CEILING:"
    for raw in unanchored do out := out.push s!"  L{raw}  in {enclosingDecl patched raw}"
  if census.isEmpty then out := out.push "  (none -- the premise is already discharged everywhere)"
  return out

/-- `(^|[ (·])(accum_block_on_\w+)\b` at its leftmost match → the name. -/
def landingApp? (line : String) : Option String := Id.run do
  let parts := line.splitOn "accum_block_on_"
  let cs := line.toList.toArray
  let mut pos := 0
  for k in [0:parts.length - 1] do
    pos := pos + parts[k]!.length
    let prev := if pos == 0 then none else some cs[pos - 1]!
    if pos == 0 || prev == some ' ' || prev == some '(' || prev == some '·' then
      let rest := (cs.extract (pos + "accum_block_on_".length) cs.size).toList.takeWhile isWordChar
      return some ("accum_block_on_" ++ String.ofList rest)
    pos := pos + "accum_block_on_".length
  return none

#guard landingApp? "  exact accum_block_on_pendingBlock x" == some "accum_block_on_pendingBlock"
#guard landingApp? "  (accum_block_on_noPending' x)" == some "accum_block_on_noPending"
#guard landingApp? "  h_accum_block_on_noPending x" == none

def payerForms : List (String × (String → Bool)) :=
  [("a RELAY of the consumer's own premise (item 208)", fun s => s == "h_nic0" || s == "h_nic0)"),
   ("the PARK's own field (items 154/206/207)", fun s =>
      s.startsWith "h_nic0" &&
        let rest := (Scripts.Punt.Price.drop s 6).toList
        let ws := rest.takeWhile isWordChar
        !ws.isEmpty && (rest.drop ws.length == [] || rest.drop ws.length == [')'])),
   ("`PendingNode.nic0`, the park-agnostic reader (item 207)", fun s =>
      (s.splitOn "PendingNode.nic0").length > 1 ||
        (s.splitOn ".nic0").zipIdx.any fun (p, k) => k > 0 && (p.toList.head?.all fun c => !isWordChar c)),
   ("a COLUMN refutation -- the park cannot stand at a line start", fun s =>
      (s.splitOn "nic0_of_col_pos").length > 1 || (s.splitOn "absurd").length > 1)]
def otherRoute : String := "another route -- the consumer takes no flag"

#guard (payerForms.find? (·.2 "h_nic0F)")).map (·.1) == some "the PARK's own field (items 154/206/207)"
#guard (payerForms.find? (·.2 "(PendingNode.nic0 h)")).map (·.1) == some "`PendingNode.nic0`, the park-agnostic reader (item 207)"
#guard (payerForms.find? (·.2 "h.nic0x")).isNone
#guard (payerForms.find? (·.2 "h.nic0 x")).isSome

/-- `payers_census()`: what each landing site spends on the flag (its last argument). -/
def payersReport (lines : Array String) : Array String := Id.run do
  let mut census : Array (String × Array (Nat × String × String)) := #[]
  for i in [0:lines.size] do
    let line := lines[i]!
    if let some name := landingApp? line then
      if names.contains name && !isComment line && !isLemmaHead name line && !((line.splitOn "`").length > 1) then
        let ind := indentOf line
        let mut last := ""
        for j in [i + 1:lines.size] do
          let t := lines[j]!
          if (strip t).isEmpty then continue
          if indentOf t ≤ ind && !isComment t then break
          if !isComment t then last := strip t
        let kind := ((payerForms.find? (·.2 last)).map (·.1)).getD otherRoute
        census := addTo census kind (i + 1, name, last)
  let total := census.foldl (· + ·.2.size) 0
  let mut out : Array String := #[s!"landing applications: {total}", ""]
  for (kind, hits) in stableSort census (fun a b => b.2.size < a.2.size) do
    out := out.push s!"  {padLeft (toString hits.size) 3}  {kind}"
    for (ln, name, text) in hits do
      out := out.push s!"         L{padRight (toString ln) 6} {padRight name 36} {take text 44}"
  return out

/-- `drop_census()`'s carriers: the consumers whose first 400 lines hold `(h_nic0 :`. -/
def carriers (lines : Array String) : Except String (List String) := do
  let mut out : List String := []
  for n in names do
    let start ← lemmaStart lines n
    let window := lines.extract start (start + 400)
    if window.any (fun l => (l.splitOn "(h_nic0 :").length > 1) then out := out ++ [n]
  return out

def carriersLine (cs : List String) : String :=
  s!"carriers of the real premise: {cs.length} ({", ".intercalate cs})"

def dropLines (name : String) (hits : Array Nat) : Array String :=
  let verdict := if hits.isEmpty then "VESTIGIAL -- the body never reads it" else "SPENT"
  #[s!"  {padLeft (toString hits.size) 3}  {padRight name 36} {verdict}"] ++
    (if hits.isEmpty then #[] else #[s!"       {joinL hits}"])

private def sample : Array String := #[
  "lemma accum_block_on_pendingBlock (x : Nat)",
  "    (h_nic0 : True) :",
  conclusion,
  "    True := by trivial",
  "lemma site : True := by",
  "  exact accum_block_on_pendingBlock 0",
  "    h_nic0F",
  "  done"]

#guard (applyProbe sample "accum_block_on_pendingBlock").toOption.map (fun p => p.1[3]!) ==
  some "    (h_nic0_probe : sp_scan.col = 0 → sc.needIndentCheck = true) :"
#guard (applyProbe sample "accum_block_on_noPending").toOption == none
#guard (applyDrop sample "accum_block_on_pendingBlock").toOption.map (fun p => (p.1[1]!, p.2)) == some ("    (h_nic0_dropped : True) :", 2)
#guard anchors sample #["accum_block_on_pendingBlock"] == #[(6, "accum_block_on_pendingBlock")]
#guard payersReport sample == #["landing applications: 1", "", "    1  the PARK's own field (items 154/206/207)",
  "         L6      accum_block_on_pendingBlock          h_nic0F"]
#guard (carriers sample).toOption == none
#guard dropLines "accum_block_on_pendingBlock" #[7, 9] == #["    2  accum_block_on_pendingBlock          SPENT", "       L7, L9"]
#guard dropLines "x" #[] == #["    0  x                                    VESTIGIAL -- the body never reads it"]

end

end Scripts.Price.LandingNic0
