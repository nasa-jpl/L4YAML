import L4YAML
import Lean

/-!
# Key Theorem Bipartite Graph Generator

Generates focused, non-dense bipartite DOT graphs for key capstone theorems.

Each graph shows:
- **Left side (blue):** Functions the theorem proves a property about
- **Right side (green):** Theorem dependency chain (theorems used in the proof)
- **Center (gold):** The key theorem itself, with arrows going left to functions
  and arrows coming in from the right from supporting theorems

Key theorems are selected by either:
- The `@[key_theorem]` attribute on individual theorems, or
- A heuristic that identifies capstone theorems (high in-degree in
  the proof dependency DAG, used by multiple other proofs, etc.), or
- The built-in catalogue of 20 hand-curated capstone theorems.

## Proof Dependency Analysis

Unlike naïve approaches that only track project-internal theorem
references, this tool also surfaces **selected stdlib theorem
dependencies**. For example, `advance_offset_lt` depends on
`String.Pos.Raw.lt_next` — a critical stdlib lemma that provides
the strict inequality. Without surfacing this, the graph would
show zero proof dependencies, losing key structural information.

**Filtering heuristic for stdlib deps**: We include non-project
theorem dependencies that are NOT proof-infrastructure combinators
(`Eq.mpr`, `congrArg`, `congr`, `funext`, etc.) and are likely
domain-relevant lemmas the user explicitly invoked.

## Functorial Lifting / Parallel Dependency Chains

When function F₁ calls F₂ and theorem T₁ (about F₁) depends on
theorem T₂ (about F₂), we say the proof dependency **lifts** the
function dependency. This makes the `about` relation a (partial)
**graph homomorphism** from the proof dependency DAG to the function
call DAG.

We call a maximal chain F₁ → F₂ → ⋯ → Fₖ with corresponding
T₁ → T₂ → ⋯ → Tₖ a **functorial chain**. The `--chain` mode
extracts and visualizes these parallel dependency structures.

## Usage

```
lake build theoremgraph
lake exe theoremgraph [--list] [--dot <name>] [--chain <name>] [--doc-base <url>] [output-dir]
```

- `--list`              — Print the catalogue of key theorems
- `--dot <name>`        — Generate a single DOT file for one key theorem
- `--chain <name>`      — Generate a functorial chain DOT for one key theorem
- `--doc-base <url>`    — Base URL prefix for doc-gen4 links (e.g. `../../../api/`)
- No args / `output-dir` — Generate all DOT files + chain files + index HTML

## Graphviz rendering

```bash
for f in tmp/graphs/*.dot; do dot -Tsvg "$f" -o "${f%.dot}.svg"; done
```
-/

open Lean

/-- Is the name in the `L4YAML` or `ParserNodeProofs` namespace? -/
def isProjectName (n : Name) : Bool :=
  match n with
  | .str p _ => p == `L4YAML || p == `ParserNodeProofs || isProjectName p
  | .num p _ => isProjectName p
  | .anonymous => false

/-- Module name for a declaration. -/
def getModuleName (env : Environment) (n : Name) : String :=
  let idx := env.getModuleIdxFor? n <|> env.getModuleIdxFor? n.getPrefix
  match idx with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none   => "<unknown>"

/-- Short display name: strip common prefixes. -/
def shortName (n : Name) : String :=
  let s := n.toString
  if s.startsWith "L4YAML.Proofs." then (s.drop 14).toString
  else if s.startsWith "L4YAML.Scanner." then (s.drop 15).toString
  else if s.startsWith "L4YAML." then (s.drop 7).toString
  else s

/-- Compute the doc-gen4 URL for a declaration.
    Module `A.B.C` maps to `{base}A/B/C.html`, declaration `A.B.C.foo` maps to
    `{base}A/B/C.html#A.B.C.foo`. Returns `none` if the module is unknown. -/
def declDocUrl (env : Environment) (n : Name) (docBase : String) : Option String :=
  let idx := env.getModuleIdxFor? n <|> env.getModuleIdxFor? n.getPrefix
  match idx with
  | some i =>
    let modName := env.header.moduleNames[i.toNat]!
    let modPath := modName.toString.replace "." "/"
    let fqn := n.toString
    some s!"{docBase}{modPath}.html#{fqn}"
  | none => none

/-- Percent-encode characters that are unsafe in file names.
    Encodes `"`, `:`, `<`, `>`, `|`, `*`, `?`, `'`, `\r`, `\n`
    using `_xx` where `xx` is the lowercase hex code of the character.
    This matches the GitHub Actions artifact upload restrictions (NTFS-safe). -/
def sanitizeFileName (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if "\":?*<>|'\r\n".any (· == c) then
      let hex := (String.ofList (Nat.toDigits 16 c.toNat)).toLower
      let hex := if hex.length == 1 then "0" ++ hex else hex
      acc ++ "_" ++ hex
    else acc.push c

/-- Escape a string for DOT/JSON. -/
def dotEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | _    => acc.push c

/-- Get the used constants from an expression, filtered to project names. -/
def projectDeps (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.filter isProjectName

/-- Get ALL used constants from an expression (no project filter). -/
def allDeps (e : Expr) : NameSet :=
  e.getUsedConstantsAsSet

/-! ## Stdlib Dependency Filtering

The proof term of even a simple theorem like `advance_offset_lt`
references 59 constants. Most are proof-infrastructure combinators
(`Eq.mpr`, `congrArg`, `ite`, `Decidable.casesOn`) that obscure
the real mathematical content.

We surface a stdlib theorem dependency only if it is "domain-relevant":
a lemma the author explicitly invoked (e.g., `String.Pos.Raw.lt_next`)
rather than a combinator inserted by tactic elaboration.
-/

/-- Names of proof-infrastructure combinators to exclude from stdlib deps. -/
def proofInfraNames : NameHashSet := Id.run do
  let names : Array Name := #[
    -- Equality combinators
    `Eq.mpr, `Eq.mp, `Eq.symm, `Eq.trans, `Eq.subst, `Eq.ndrec, `Eq.rec,
    `congrArg, `congr, `congrFun, `congrFun', `eq_of_heq, `HEq.refl,
    -- Conditional/decidable infrastructure
    `ite_cond_eq_true, `if_pos, `if_neg, `ite_congr, `dite_cond_eq_true,
    `eq_true, `eq_false,
    -- Proof combinators
    `funext, `propext, `Classical.em, `Classical.choice,
    `absurd, `False.elim, `True.intro,
    `And.intro, `And.left, `And.right,
    `Or.inl, `Or.inr, `Or.elim,
    -- No-confusion
    `noConfusion_of_Nat, `Nat.noConfusion,
    -- Other infrastructure
    `rfl, `Iff.intro, `Iff.mp, `Iff.mpr,
    `id, `id_def
  ]
  let mut set : NameHashSet := {}
  for n in names do set := set.insert n
  return set

/-- Is this a proof-infrastructure combinator we should skip? -/
def isProofInfra (n : Name) : Bool :=
  proofInfraNames.contains n

/-- Get domain-relevant stdlib theorem dependencies of a theorem.
    These are non-project theorems that are NOT proof-infrastructure. -/
def getStdlibThmDeps (env : Environment) (thmName : Name) : Array Name :=
  match env.find? thmName with
  | some (.thmInfo v) =>
    let all := v.value.getUsedConstantsAsSet
    all.toArray.filter fun n =>
      !isProjectName n && !isProofInfra n &&
      match env.find? n with
      | some (.thmInfo _) => true
      | _ => false
  | _ => #[]

/-! ## Key Theorem Selection Predicate

A theorem is considered "key" if ANY of these hold:
1. It carries `@[key_theorem]`
2. It appears in the built-in catalogue
3. (Heuristic) It has high "proof in-degree" — many other project
   theorems reference it in their proof terms
-/

/-- Built-in catalogue of capstone theorems (fallback when no annotations exist). -/
def catalogueTheorems : Array (String × Name × String) := #[
  -- Pipeline capstones
  ("scan_produces_valid_tokens",
   `L4YAML.Proofs.ScannerCorrectness.scan_produces_valid_tokens,
   "Scanner output satisfies ValidTokenStream"),
  ("parseStream_sound",
   `L4YAML.Proofs.ParserSoundness.parseStream_sound,
   "Parser produces only valid YAML ASTs"),
  ("parseYaml_ok_iff",
   `L4YAML.Proofs.Completeness.parseYaml_ok_iff,
   "parseYaml succeeds iff input is valid YAML"),
  ("parseYaml_pipeline",
   `L4YAML.Proofs.Composition.parseYaml_pipeline,
   "End-to-end scanner-parser pipeline composition"),
  ("parseYamlRaw_pipeline",
   `L4YAML.Proofs.Composition.parseYamlRaw_pipeline,
   "Raw pipeline: scan then parse composes correctly"),
  ("parseYamlRaw_ok_decompose",
   `L4YAML.Proofs.Composition.parseYamlRaw_ok_decompose,
   "Successful parse decomposes into scan + parse steps"),
  -- Scanner properties
  ("advance_offset_lt",
   `L4YAML.Proofs.ScannerProgress.advance_offset_lt,
   "Scanner advance strictly increases offset (termination)"),
  ("scanLoop_success_emits_streamEnd",
   `L4YAML.Proofs.ScannerCorrectness.scanLoop_success_emits_streamEnd,
   "Successful scan loop always emits STREAM_END"),
  -- Parser properties
  ("parseNode_anchors_grow",
   `ParserNodeProofs.parseNode_anchors_grow,
   "Anchor set grows monotonically through parseNode"),
  ("parseNode_aliases_resolve'",
   `ParserNodeProofs.parseNode_aliases_resolve',
   "All aliases in parseNode output resolve to anchors"),
  ("parseStream_output_anchors_wellformed",
   `L4YAML.Proofs.ParserGrammable.parseStream_output_anchors_wellformed,
   "Output anchors are well-formed after parseStream"),
  -- Soundness
  ("toYamlValue_correct",
   `L4YAML.Proofs.Soundness.toYamlValue_correct,
   "AST-to-value conversion matches specification"),
  ("nodeToValue_total",
   `L4YAML.Proofs.Soundness.nodeToValue_total,
   "Every AST node can be converted to a value"),
  ("nodeToValue_deterministic",
   `L4YAML.Proofs.Soundness.nodeToValue_deterministic,
   "AST-to-value conversion is deterministic"),
  ("scalar_content_preserved",
   `L4YAML.Proofs.Soundness.scalar_content_preserved,
   "Scalar content is preserved through parsing"),
  -- Round-trip
  ("contentEq_refl",
   `L4YAML.Proofs.RoundTrip.contentEq_refl,
   "Content equality is reflexive"),
  ("contentEq_symm",
   `L4YAML.Proofs.RoundTrip.contentEq_symm,
   "Content equality is symmetric"),
  ("contentEq_trans",
   `L4YAML.Proofs.RoundTrip.contentEq_trans,
   "Content equality is transitive"),
  ("emit_content_invariant",
   `L4YAML.Proofs.ScannerEmitBridge.emit_content_invariant,
   "Emitter preserves content equality"),
  ("escapeTag_roundtrip",
   `L4YAML.Proofs.RoundTrip.escapeTag_roundtrip,
   "Tag escape/unescape round-trips correctly")
]

/-- Collect the effective set of key theorems: annotation-based + catalogue + heuristic.
    Returns array of (short_name, FQN, description). -/
def collectKeyTheorems (env : Environment) (projectThms : NameHashSet)
    : Array (String × Name × String) := Id.run do
  let mut result : Array (String × Name × String) := #[]
  let mut seen : NameHashSet := {}

  -- 1. Annotated key theorems (highest priority)
  let annotated := L4YAML.getAllKeyTheorems env
  for (name, ref) in annotated do
    if !seen.contains name then
      seen := seen.insert name
      let desc := ref.description.getD name.toString
      let short := shortName name
      result := result.push (short, name, desc)

  -- 2. Built-in catalogue (if not already covered by annotations)
  for (short, fqn, desc) in catalogueTheorems do
    if !seen.contains fqn && (env.find? fqn).isSome then
      seen := seen.insert fqn
      result := result.push (short, fqn, desc)

  -- 3. Heuristic: theorems with high proof in-degree (≥ 5 other project
  --    theorems use them). Only add if not already in the set.
  let mut inDegree : Std.HashMap Name Nat := {}
  for n in projectThms.toList do
    match env.find? n with
    | some (.thmInfo v) =>
      for dep in projectDeps v.value do
        if projectThms.contains dep then
          inDegree := inDegree.insert dep ((inDegree.getD dep 0) + 1)
    | _ => pure ()
  for (n, deg) in inDegree.toList do
    if deg >= 5 && !seen.contains n then
      seen := seen.insert n
      result := result.push (shortName n, n, s!"(heuristic: used by {deg} proofs)")

  return result

/-- Collect the effective set of key functions: annotation-based + heuristic.
    Returns array of (short_name, FQN, description). -/
def collectKeyFunctions (env : Environment) (projectDefs projectThms : NameHashSet)
    : Array (String × Name × String) := Id.run do
  let mut result : Array (String × Name × String) := #[]
  let mut seen : NameHashSet := {}

  -- 1. Annotated key functions
  let annotated := L4YAML.getAllKeyFunctions env
  for (name, ref) in annotated do
    if !seen.contains name then
      seen := seen.insert name
      let desc := ref.description.getD name.toString
      result := result.push (shortName name, name, desc)

  -- 2. Heuristic: functions mentioned in ≥ 3 project theorem types
  let mut thmAboutCount : Std.HashMap Name Nat := {}
  for n in projectThms.toList do
    match env.find? n with
    | some (.thmInfo v) =>
      for dep in projectDeps v.type do
        if projectDefs.contains dep then
          thmAboutCount := thmAboutCount.insert dep ((thmAboutCount.getD dep 0) + 1)
    | _ => pure ()
  for (n, cnt) in thmAboutCount.toList do
    if cnt >= 3 && !seen.contains n then
      seen := seen.insert n
      result := result.push (shortName n, n, s!"(heuristic: {cnt} theorems about it)")

  return result

/-- Collect transitive theorem dependencies up to a depth limit.
    Now includes BOTH project and selected stdlib theorem deps. -/
def collectThmDeps (env : Environment) (projectThms : NameHashSet)
    (root : Name) (maxDepth : Nat := 3) : NameHashSet := Id.run do
  let mut visited : NameHashSet := {}
  let mut frontier : Array Name := #[root]
  for _ in [:maxDepth] do
    let mut nextFrontier : Array Name := #[]
    for n in frontier do
      if visited.contains n then continue
      visited := visited.insert n
      match env.find? n with
      | some (.thmInfo v) =>
        -- Project theorem deps
        let deps := projectDeps v.value |>.filter fun d =>
          projectThms.contains d && !visited.contains d
        nextFrontier := nextFrontier ++ deps
        -- Selected stdlib theorem deps (depth 1 only from root)
        if n == root then
          let stdDeps := getStdlibThmDeps env n
          for sd in stdDeps do
            if !visited.contains sd then
              visited := visited.insert sd
      | _ => pure ()
    frontier := nextFrontier
  return visited.erase root

/-- Collect functions a theorem is about (mentioned in type). -/
def collectAbout (env : Environment) (projectDefs : NameHashSet)
    (n : Name) : Array Name :=
  match env.find? n with
  | some (.thmInfo v) => projectDeps v.type |>.filter projectDefs.contains
  | _ => #[]

/-- Classify a constant as def/thm/etc. -/
def classifyConst (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo _   => "def"
  | .thmInfo _    => "thm"
  | .axiomInfo _  => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

/-! ## Bipartite DOT Generation -/

/-- Generate a bipartite DOT graph for a single key theorem.
    Left: functions it proves about.  Right: theorems it depends on.
    Center: the key theorem itself.
    Now includes stdlib theorem deps (shown in orange). -/
def generateBipartiteDot (env : Environment) (projectDefs projectThms : NameHashSet)
    (thmName : Name) (description : String) (docBase : String := "") : String := Id.run do
  let about := collectAbout env projectDefs thmName
  let deps := collectThmDeps env projectThms thmName (maxDepth := 2)
  let stdlibDeps := getStdlibThmDeps env thmName

  let mut depAbout : Array (Name × Array Name) := #[]
  for dep in deps.toList do
    let da := collectAbout env projectDefs dep
    if da.size > 0 then
      depAbout := depAbout.push (dep, da)

  let thmShort := shortName thmName
  let thmMod := getModuleName env thmName
  let lbr := "{"
  let rbr := "}"

  let mut dot := s!"digraph \"{dotEscape thmShort}\" {lbr}\n"
  dot := dot ++ "  rankdir=LR;\n"
  dot := dot ++ "  newrank=true;\n"
  dot := dot ++ "  node [fontsize=10, fontname=\"Helvetica\"];\n"
  dot := dot ++ "  edge [arrowsize=0.7];\n"
  dot := dot ++ s!"  label=\"{dotEscape thmShort}\\n{dotEscape description}\\n({dotEscape thmMod})\";\n"
  dot := dot ++ "  labelloc=t; fontsize=13; fontname=\"Helvetica Bold\";\n\n"

  -- Subgraph: functions
  dot := dot ++ s!"  subgraph cluster_functions {lbr}\n"
  dot := dot ++ "    label=\"Functions\";\n"
  dot := dot ++ "    style=dashed; color=\"#4a90d9\"; fontcolor=\"#4a90d9\";\n"
  dot := dot ++ "    node [shape=box, style=filled, fillcolor=\"#dce9f7\", color=\"#4a90d9\"];\n"
  let mut allFunctions : NameHashSet := {}
  for f in about do allFunctions := allFunctions.insert f
  for (_, da) in depAbout do
    for f in da do allFunctions := allFunctions.insert f
  for f in allFunctions.toList do
    let fShort := shortName f
    let kind := match env.find? f with
      | some ci => classifyConst ci
      | none => "?"
    -- Highlight @[key_function]-tagged functions
    let extra := if L4YAML.isKeyFunction env f then ", penwidth=3" else ""
    let urlAttr := if docBase.isEmpty then "" else
      match declDocUrl env f docBase with
      | some u => s!", URL=\"{dotEscape u}\", target=\"_blank\""
      | none => ""
    dot := dot ++ s!"    \"{dotEscape f.toString}\" [label=\"{dotEscape fShort}\\n({kind})\"{extra}{urlAttr}];\n"
  dot := dot ++ s!"  {rbr}\n\n"

  -- Subgraph: key theorem
  dot := dot ++ s!"  subgraph cluster_key {lbr}\n"
  dot := dot ++ "    label=\"Key Theorem\";\n"
  dot := dot ++ "    style=dashed; color=\"#d4a017\"; fontcolor=\"#d4a017\";\n"
  dot := dot ++ s!"    \"{dotEscape thmName.toString}\" [shape=doubleoctagon, style=filled, fillcolor=\"#fff3cd\", color=\"#d4a017\", label=\"{dotEscape thmShort}\", fontsize=12{if docBase.isEmpty then "" else match declDocUrl env thmName docBase with | some u => s!", URL=\"{dotEscape u}\", target=\"_blank\"" | none => ""}];\n"
  dot := dot ++ s!"  {rbr}\n\n"

  -- Subgraph: project theorem dependencies
  dot := dot ++ s!"  subgraph cluster_proofs {lbr}\n"
  dot := dot ++ "    label=\"Proof Dependencies\";\n"
  dot := dot ++ "    style=dashed; color=\"#28a745\"; fontcolor=\"#28a745\";\n"
  dot := dot ++ "    node [shape=ellipse, style=filled, fillcolor=\"#d4edda\", color=\"#28a745\"];\n"
  for dep in deps.toList do
    if isProjectName dep then
      let depShort := shortName dep
      let depMod := getModuleName env dep
      let modLabel := if depMod.startsWith "L4YAML.Proofs." then (depMod.drop 14).toString
                      else if depMod.startsWith "L4YAML." then (depMod.drop 7).toString
                      else depMod
      let urlAttr := if docBase.isEmpty then "" else
        match declDocUrl env dep docBase with
        | some u => s!", URL=\"{dotEscape u}\", target=\"_blank\""
        | none => ""
      dot := dot ++ s!"    \"{dotEscape dep.toString}\" [label=\"{dotEscape depShort}\\n({dotEscape modLabel})\"{urlAttr}];\n"
  dot := dot ++ s!"  {rbr}\n\n"

  -- Subgraph: stdlib theorem dependencies (orange)
  if stdlibDeps.size > 0 then
    dot := dot ++ s!"  subgraph cluster_stdlib {lbr}\n"
    dot := dot ++ "    label=\"Stdlib Lemmas\";\n"
    dot := dot ++ "    style=dashed; color=\"#e67e22\"; fontcolor=\"#e67e22\";\n"
    dot := dot ++ "    node [shape=ellipse, style=filled, fillcolor=\"#fdebd0\", color=\"#e67e22\"];\n"
    for dep in stdlibDeps do
      let depShort := dep.toString
      let urlAttr := if docBase.isEmpty then "" else
        match declDocUrl env dep docBase with
        | some u => s!", URL=\"{dotEscape u}\", target=\"_blank\""
        | none => ""
      dot := dot ++ s!"    \"{dotEscape dep.toString}\" [label=\"{dotEscape depShort}\"{urlAttr}];\n"
    dot := dot ++ s!"  {rbr}\n\n"

  -- Edges: key theorem -> functions
  dot := dot ++ "  // Key theorem proves properties about these functions\n"
  for f in about do
    dot := dot ++ s!"  \"{dotEscape thmName.toString}\" -> \"{dotEscape f.toString}\" [color=\"#4a90d9\", style=bold, label=\"about\", fontsize=8, fontcolor=\"#4a90d9\"];\n"

  -- Edges: project proof deps -> key theorem
  dot := dot ++ "\n  // Supporting theorems used in proof\n"
  let directDeps := match env.find? thmName with
    | some (.thmInfo v) => projectDeps v.value |>.filter projectThms.contains
    | _ => #[]
  for dep in directDeps do
    if deps.contains dep then
      dot := dot ++ s!"  \"{dotEscape dep.toString}\" -> \"{dotEscape thmName.toString}\" [color=\"#28a745\"];\n"

  -- Edges: stdlib deps -> key theorem
  for dep in stdlibDeps do
    dot := dot ++ s!"  \"{dotEscape dep.toString}\" -> \"{dotEscape thmName.toString}\" [color=\"#e67e22\", style=bold];\n"

  -- Edges: dep theorems -> functions
  dot := dot ++ "\n  // Supporting theorems also prove about functions\n"
  for (dep, da) in depAbout do
    for f in da do
      dot := dot ++ s!"  \"{dotEscape dep.toString}\" -> \"{dotEscape f.toString}\" [color=\"#999999\", style=dotted, arrowsize=0.5];\n"

  -- Edges between deps
  dot := dot ++ "\n  // Inter-dependency edges\n"
  for dep in deps.toList do
    if isProjectName dep then
      match env.find? dep with
      | some (.thmInfo v) =>
        let subDeps := projectDeps v.value |>.filter fun d =>
          projectThms.contains d && deps.contains d
        for sd in subDeps do
          dot := dot ++ s!"  \"{dotEscape sd.toString}\" -> \"{dotEscape dep.toString}\" [color=\"#cccccc\", style=dashed, arrowsize=0.4];\n"
      | _ => pure ()

  dot := dot ++ s!"{rbr}\n"
  return dot

/-! ## Functorial Chain Analysis

A **functorial chain** captures the parallel structure:

```
    F₁ ──calls──→ F₂ ──calls──→ F₃
    ↑ about         ↑ about        ↑ about
    T₁ ──uses───→ T₂ ──uses───→ T₃
```

The `about` relation from theorems to functions is a (partial) graph
homomorphism from the proof DAG to the call DAG. A functorial chain
is a connected component where every proof edge lifts a call edge.

In category theory terms:
- Objects: functions (in the call graph category) and theorems (in the proof graph category)
- `about` is a functor from Proof → Call (mapping each theorem to the function it proves something about)
- A functorial chain is a path in Proof whose image under `about` is a path in Call

This property is sometimes called a **simulation** (in process algebra)
or a **fibration** (in categorical semantics).
-/

/-- Get function call dependencies (functions called by a function's body). -/
def getFunctionCallDeps (env : Environment) (projectDefs : NameHashSet)
    (fn : Name) : Array Name :=
  match env.find? fn with
  | some (.defnInfo v) => projectDeps v.value |>.filter projectDefs.contains
  | _ => #[]

/-- A chain link: a theorem T about function F, where T's proof uses T'
    (about F'), and F calls F'. -/
structure ChainLink where
  theorem_name : Name
  function_name : Name
  deriving Inhabited, BEq, Hashable

/-- Find functorial chains rooted at a key theorem.
    Walks the proof dependency DAG, and for each dep theorem T₂,
    checks if T₂ is about a function F₂ that is called by a function
    F₁ that the parent theorem T₁ is about. -/
def findFunctorialChains (env : Environment) (projectDefs projectThms : NameHashSet)
    (root : Name) (maxDepth : Nat := 4) : Array (Array ChainLink) := Id.run do
  let rootAbout := collectAbout env projectDefs root
  if rootAbout.isEmpty then return #[]

  -- Build chains via DFS
  let mut chains : Array (Array ChainLink) := #[]

  -- For each function the root theorem is about, start a chain
  for rootFn in rootAbout do
    let mut stack : Array (Array ChainLink × Name × Name) := #[]
    -- (current_chain, current_thm, current_fn)
    stack := stack.push (#[{ theorem_name := root, function_name := rootFn }], root, rootFn)

    while stack.size > 0 do
      let (chain, curThm, curFn) := stack.back!
      stack := stack.pop

      if chain.size > maxDepth then
        chains := chains.push chain
        continue

      -- Get proof deps of curThm
      let thmDeps := match env.find? curThm with
        | some (.thmInfo v) => projectDeps v.value |>.filter projectThms.contains
        | _ => #[]

      -- Get call deps of curFn
      let fnDeps := getFunctionCallDeps env projectDefs curFn

      let mut extended := false
      for depThm in thmDeps do
        let depAbout := collectAbout env projectDefs depThm
        for depFn in depAbout do
          -- Check if depFn is called by curFn (functorial condition)
          if fnDeps.contains depFn then
            let link : ChainLink := { theorem_name := depThm, function_name := depFn }
            -- Avoid cycles
            if !chain.any (fun l => l.theorem_name == depThm && l.function_name == depFn) then
              stack := stack.push (chain.push link, depThm, depFn)
              extended := true

      if !extended && chain.size > 1 then
        chains := chains.push chain

  -- Deduplicate and return longest chains
  return chains.qsort (fun a b => a.size > b.size) |>.toList.take 10 |>.toArray

/-- Generate a functorial chain DOT graph.
    Shows parallel function and theorem ladders with cross-links. -/
def generateChainDot (env : Environment) (projectDefs projectThms : NameHashSet)
    (thmName : Name) (description : String) (docBase : String := "") : String := Id.run do
  let chains := findFunctorialChains env projectDefs projectThms thmName
  let thmShort := shortName thmName
  let lbr := "{"
  let rbr := "}"

  let mut dot := s!"digraph \"chain_{dotEscape thmShort}\" {lbr}\n"
  dot := dot ++ "  rankdir=TB;\n"
  dot := dot ++ "  newrank=true;\n"
  dot := dot ++ "  node [fontsize=10, fontname=\"Helvetica\"];\n"
  dot := dot ++ "  edge [arrowsize=0.7];\n"
  dot := dot ++ s!"  label=\"Functorial Chains: {dotEscape thmShort}\\n{dotEscape description}\";\n"
  dot := dot ++ "  labelloc=t; fontsize=13; fontname=\"Helvetica Bold\";\n\n"

  if chains.isEmpty then
    dot := dot ++ s!"  \"{dotEscape thmName.toString}\" [label=\"{dotEscape thmShort}\\n(no functorial chains found)\", shape=doubleoctagon, style=filled, fillcolor=\"#fff3cd\"];\n"
    dot := dot ++ s!"{rbr}\n"
    return dot

  -- Collect unique functions and theorems across all chains
  let mut allFns : NameHashSet := {}
  let mut allThms : NameHashSet := {}
  for chain in chains do
    for link in chain do
      allFns := allFns.insert link.function_name
      allThms := allThms.insert link.theorem_name

  -- Function column (left)
  dot := dot ++ s!"  subgraph cluster_fns {lbr}\n"
  dot := dot ++ "    label=\"Functions (Call Chain)\";\n"
  dot := dot ++ "    style=dashed; color=\"#4a90d9\"; fontcolor=\"#4a90d9\";\n"
  dot := dot ++ "    node [shape=box, style=filled, fillcolor=\"#dce9f7\", color=\"#4a90d9\"];\n"
  for f in allFns.toList do
    let fShort := shortName f
    let extra := if L4YAML.isKeyFunction env f then ", penwidth=3" else ""
    let urlAttr := if docBase.isEmpty then "" else
      match declDocUrl env f docBase with
      | some u => s!", URL=\"{dotEscape u}\", target=\"_blank\""
      | none => ""
    dot := dot ++ s!"    \"{dotEscape f.toString}\" [label=\"{dotEscape fShort}\"{extra}{urlAttr}];\n"
  dot := dot ++ s!"  {rbr}\n\n"

  -- Theorem column (right)
  dot := dot ++ s!"  subgraph cluster_thms {lbr}\n"
  dot := dot ++ "    label=\"Theorems (Proof Chain)\";\n"
  dot := dot ++ "    style=dashed; color=\"#28a745\"; fontcolor=\"#28a745\";\n"
  dot := dot ++ "    node [shape=ellipse, style=filled, fillcolor=\"#d4edda\", color=\"#28a745\"];\n"
  for t in allThms.toList do
    let tShort := shortName t
    let extra := if t == thmName then ", shape=doubleoctagon, fillcolor=\"#fff3cd\", color=\"#d4a017\"" else ""
    let urlAttr := if docBase.isEmpty then "" else
      match declDocUrl env t docBase with
      | some u => s!", URL=\"{dotEscape u}\", target=\"_blank\""
      | none => ""
    dot := dot ++ s!"    \"{dotEscape t.toString}\" [label=\"{dotEscape tShort}\"{extra}{urlAttr}];\n"
  dot := dot ++ s!"  {rbr}\n\n"

  -- Edges
  let mut fnEdges : NameHashSet := {}
  let mut thmEdges : NameHashSet := {}
  let mut aboutEdges : NameHashSet := {}

  for chain in chains do
    for i in [:chain.size] do
      let link := chain[i]!
      -- about edge: theorem -> function
      let aboutKey := link.theorem_name ++ link.function_name
      if !aboutEdges.contains aboutKey then
        aboutEdges := aboutEdges.insert aboutKey
        dot := dot ++ s!"  \"{dotEscape link.theorem_name.toString}\" -> \"{dotEscape link.function_name.toString}\" [color=\"#999999\", style=dotted, label=\"about\", fontsize=8];\n"

      if i + 1 < chain.size then
        let next := chain[i + 1]!
        -- function call edge
        let fnKey := link.function_name ++ next.function_name
        if !fnEdges.contains fnKey then
          fnEdges := fnEdges.insert fnKey
          dot := dot ++ s!"  \"{dotEscape link.function_name.toString}\" -> \"{dotEscape next.function_name.toString}\" [color=\"#4a90d9\", style=bold, label=\"calls\", fontsize=8];\n"
        -- theorem dep edge
        let thmKey := link.theorem_name ++ next.theorem_name
        if !thmEdges.contains thmKey then
          thmEdges := thmEdges.insert thmKey
          dot := dot ++ s!"  \"{dotEscape link.theorem_name.toString}\" -> \"{dotEscape next.theorem_name.toString}\" [color=\"#28a745\", style=bold, label=\"uses\", fontsize=8];\n"

  dot := dot ++ s!"{rbr}\n"
  return dot

/-! ## Index HTML Generation -/

def generateIndexHtml (bipartiteEntries chainEntries : Array (String × String)) : String := Id.run do
  let mut html := "<!DOCTYPE html>\n<html><head><title>L4YAML Key Theorem Dependency Graphs</title>\n"
  html := html ++ "<style>body{font-family:sans-serif;max-width:900px;margin:2em auto}"
  html := html ++ "h1{color:#333}h2{color:#555;border-bottom:1px solid #ddd}"
  html := html ++ ".thm{margin:1.5em 0;padding:1em;border:1px solid #ddd;border-radius:8px}"
  html := html ++ ".thm h3{margin-top:0;color:#4a90d9} object{max-width:100%;border:1px solid #eee}</style>\n"
  html := html ++ "</head><body>\n<h1>L4YAML &mdash; Key Theorem Dependency Graphs</h1>\n"
  html := html ++ "<p>Each bipartite graph shows: <span style='color:#4a90d9'>functions</span> (left) "
  html := html ++ "&larr; <span style='color:#d4a017'>key theorem</span> (center) &larr; "
  html := html ++ "<span style='color:#28a745'>proof dependencies</span> (right)"
  html := html ++ " &larr; <span style='color:#e67e22'>stdlib lemmas</span> (far right)</p>\n"
  html := html ++ "<h2>Bipartite Dependency Graphs</h2>\n"
  for (shortN, desc) in bipartiteEntries do
    html := html ++ s!"<div class='thm'><h3>{shortN}</h3>\n"
    html := html ++ s!"<p>{desc}</p>\n"
    html := html ++ s!"<object data='{shortN}.svg' type='image/svg+xml' width='100%'>{shortN} dependency graph</object>\n</div>\n"
  if chainEntries.size > 0 then
    html := html ++ "<h2>Functorial Chain Graphs</h2>\n"
    html := html ++ "<p>Parallel function-call and theorem-proof chains where the <em>about</em> "
    html := html ++ "relation lifts call edges to proof edges.</p>\n"
    for (shortN, desc) in chainEntries do
      html := html ++ s!"<div class='thm'><h3>{shortN} (chain)</h3>\n"
      html := html ++ s!"<p>{desc}</p>\n"
      html := html ++ s!"<object data='chain_{shortN}.svg' type='image/svg+xml' width='100%'>{shortN} chain graph</object>\n</div>\n"
  html := html ++ "</body></html>\n"
  return html

/-! ## Coverage Report -/

def printCoverage (env : Environment) (projectDefs projectThms : NameHashSet) : IO Unit := do
  let keyFns := collectKeyFunctions env projectDefs projectThms
  let keyThms := collectKeyTheorems env projectThms
  IO.println "Key Function / Key Theorem Coverage"
  IO.println "===================================="
  IO.println ""
  let mut coveredCount := 0
  for (fnShort, fnFqn, fnDesc) in keyFns do
    let mut thmNames : Array String := #[]
    for (_, thmFqn, _) in keyThms do
      match env.find? thmFqn with
      | some (.thmInfo v) =>
        if v.type.getUsedConstantsAsSet.contains fnFqn then
          thmNames := thmNames.push (shortName thmFqn)
      | _ => pure ()
    if thmNames.isEmpty then
      IO.println s!"  ✗ {fnShort}"
      IO.println s!"    {fnDesc}"
      IO.println s!"    No key theorem coverage"
    else
      coveredCount := coveredCount + 1
      IO.println s!"  ✓ {fnShort}"
      IO.println s!"    {fnDesc}"
      IO.println s!"    Key theorems: {", ".intercalate thmNames.toList}"
    IO.println ""
  IO.println s!"Coverage: {coveredCount}/{keyFns.size} key functions have key theorem coverage"

/-! ## Main -/

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `L4YAML }] {} 0

  -- Extract --doc-base <url> from args (if present)
  let rec extractDocBase : List String → String × List String
    | "--doc-base" :: base :: rest => (base, rest)
    | x :: xs => let (db, ys) := extractDocBase xs; (db, x :: ys)
    | [] => ("", [])
  let (docBase, args) := extractDocBase args

  -- Build project def/thm sets
  let allConsts : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc n ci =>
      if isProjectName n then acc.push (n, ci) else acc

  let mut projectDefs : NameHashSet := {}
  let mut projectThms : NameHashSet := {}
  for (n, ci) in allConsts do
    match ci with
    | .defnInfo _ | .opaqueInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ =>
      projectDefs := projectDefs.insert n
    | .thmInfo _ =>
      projectThms := projectThms.insert n
    | _ => pure ()

  -- Collect key theorems from all sources
  let keyThms := collectKeyTheorems env projectThms

  match args with
  | ["--list"] =>
    IO.println "Key Theorem Catalogue"
    IO.println "====================="
    IO.println ""
    -- Show annotated key theorems
    let annotated := L4YAML.getAllKeyTheorems env
    if annotated.size > 0 then
      IO.println s!"@[key_theorem] annotated ({annotated.size}):"
      for (name, ref) in annotated do
        IO.println s!"  ✓ {shortName name} — {ref.toString}"
      IO.println ""
    -- Show annotated key functions
    let annotatedFns := L4YAML.getAllKeyFunctions env
    if annotatedFns.size > 0 then
      IO.println s!"@[key_function] annotated ({annotatedFns.size}):"
      for (name, ref) in annotatedFns do
        IO.println s!"  ✓ {shortName name} — {ref.toString}"
      IO.println ""
    -- Show effective catalogue
    IO.println s!"Effective key theorems ({keyThms.size}):"
    for (short, fqn, desc) in keyThms do
      let isAnnotated := L4YAML.isKeyTheorem env fqn
      let source := if isAnnotated then "@" else "C"
      IO.println s!"  [{source}] {short}"
      IO.println s!"      {desc}"
      IO.println ""
    IO.println "Legend: [@] = annotated, [C] = catalogue/heuristic"

  | ["--dot", name] =>
    match keyThms.find? (fun (s, _, _) => s == name) with
    | some (_, fqn, desc) =>
      match env.find? fqn with
      | some _ => IO.println (generateBipartiteDot env projectDefs projectThms fqn desc docBase)
      | none => IO.eprintln s!"Error: theorem {fqn} not found in environment"
    | none =>
      IO.eprintln s!"Error: '{name}' is not a recognized key theorem. Use --list to see options."

  | ["--chain", name] =>
    match keyThms.find? (fun (s, _, _) => s == name) with
    | some (_, fqn, desc) =>
      match env.find? fqn with
      | some _ => IO.println (generateChainDot env projectDefs projectThms fqn desc docBase)
      | none => IO.eprintln s!"Error: theorem {fqn} not found in environment"
    | none =>
      IO.eprintln s!"Error: '{name}' is not a recognized key theorem. Use --list to see options."

  | ["--coverage"] =>
    printCoverage env projectDefs projectThms

  | _ =>
    let outDir := args.headD "tmp/graphs"
    IO.FS.createDirAll outDir

    let mut bipartiteEntries : Array (String × String) := #[]
    let mut chainEntries : Array (String × String) := #[]
    let mut generated := 0
    let mut skipped := 0

    for (short, fqn, desc) in keyThms do
      match env.find? fqn with
      | some _ =>
        let safeShort := sanitizeFileName short
        -- Bipartite graph
        let dot := generateBipartiteDot env projectDefs projectThms fqn desc docBase
        let path := s!"{outDir}/{safeShort}.dot"
        IO.FS.writeFile path dot
        IO.println s!"  ✓ {path}"
        bipartiteEntries := bipartiteEntries.push (safeShort, desc)
        -- Functorial chain graph
        let chainDot := generateChainDot env projectDefs projectThms fqn desc docBase
        let chainPath := s!"{outDir}/chain_{safeShort}.dot"
        IO.FS.writeFile chainPath chainDot
        IO.println s!"  ✓ {chainPath}"
        chainEntries := chainEntries.push (safeShort, desc)
        generated := generated + 1
      | none =>
        IO.eprintln s!"  ✗ {short} — not found in environment, skipping"
        skipped := skipped + 1

    -- Write index HTML
    let indexHtml := generateIndexHtml bipartiteEntries chainEntries
    IO.FS.writeFile s!"{outDir}/index.html" indexHtml
    IO.println s!"\nGenerated {generated} bipartite + {generated} chain DOT files, skipped {skipped}"
    IO.println s!"Output: {outDir}/"
    let renderHint := "To render: for f in " ++ outDir ++ "/*.dot; do dot -Tsvg \"$f\" -o \"${f%.dot}.svg\"; done"
    IO.println renderHint
