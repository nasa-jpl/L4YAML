import Lean4Yaml
import Lean

/-!
# Declaration Dependency Graph Extractor

Extracts three dependency graphs from the `Lean4Yaml` environment:

1. **Function call graph** — which definitions call which other definitions
2. **Theorem dependency graph** — which theorems use which other theorems in their proofs
3. **Function–theorem map** — which functions each theorem is *about* (mentions in its statement)

## Usage

```
lake build depgraph
./.lake/build/bin/depgraph > dep-graphs.json
```

The output is a single JSON object with three keys: `defCalls`, `thmDeps`, `thmAbout`.
Each is an array of `{"name": "...", "deps": ["...", ...]}` objects.

Pipe through `jq` or load in Python for visualization (e.g., Graphviz DOT, d3-force).

## Graphviz example

```bash
./.lake/build/bin/depgraph --dot calls   > calls.dot   && dot -Tsvg calls.dot -o calls.svg
./.lake/build/bin/depgraph --dot thmdeps > thmdeps.dot  && sfdp -Tsvg thmdeps.dot -o thmdeps.svg
./.lake/build/bin/depgraph --dot about   > about.dot    && dot -Tsvg about.dot -o about.svg
```
-/

open Lean

/-- Is the name in the `Lean4Yaml` namespace (our project)? -/
private def isProjectName (n : Name) : Bool :=
  match n with
  | .str p _ => p == `Lean4Yaml || isProjectName p
  | .num p _ => isProjectName p
  | .anonymous => false

/-- Classify a ConstantInfo as "def", "thm", "inductive", "ctor", "axiom", etc. -/
private def classifyConst (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo _   => "def"
  | .thmInfo _    => "thm"
  | .axiomInfo _  => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

/-- Get the used constants from an expression, filtered to project names. -/
private def projectDeps (e : Expr) : Array Name :=
  let used := e.getUsedConstantsAsSet
  used.toArray.filter isProjectName

/-- Escape a string for JSON output (handles quotes and backslashes). -/
private def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | _    => acc.push c

/-- Format an array of names as a JSON array of strings. -/
private def jsonNameArray (ns : Array Name) : String :=
  let items := ns.map fun n => s!"\"{jsonEscape n.toString}\""
  "[" ++ ",".intercalate items.toList ++ "]"

/-- Source location: module (file) name + line range. -/
structure SrcLoc where
  module : String     -- e.g. "Lean4Yaml.Scanner"
  line   : Nat        -- start line
  endLine : Nat       -- end line
  deriving Inhabited

/-- A dependency record: name, classification, source location, and dependency list. -/
structure DepRecord where
  name : Name
  kind : String
  loc  : Option SrcLoc
  deps : Array Name
  deriving Inhabited

private def srcLocToJson (loc : Option SrcLoc) : String :=
  match loc with
  | none => "null"
  | some l => s!"\{\"module\":\"{jsonEscape l.module}\",\"line\":{l.line},\"endLine\":{l.endLine}}"

private def depRecordToJson (r : DepRecord) : String :=
  s!"\{\"name\":\"{jsonEscape r.name.toString}\",\"kind\":\"{r.kind}\",\"loc\":{srcLocToJson r.loc},\"deps\":{jsonNameArray r.deps}}"

/-- Emit a DOT graph from an array of DepRecords. -/
private def toDot (title : String) (records : Array DepRecord) : String :=
  let header := s!"digraph \"{jsonEscape title}\" \{\n  rankdir=LR;\n  node [shape=box, fontsize=10];\n"
  let edges := records.foldl (init := "") fun acc r =>
    r.deps.foldl (init := acc) fun acc2 dep =>
      acc2 ++ s!"  \"{jsonEscape r.name.toString}\" -> \"{jsonEscape dep.toString}\";\n"
  header ++ edges ++ "}\n"

/-- Strip common prefixes for shorter labels in DOT output. -/
private def shortName (n : Name) : String :=
  -- Drop the `Lean4Yaml.` prefix for readability
  let s := n.toString
  if s.startsWith "Lean4Yaml." then (s.drop 9).toString else s

/-- Emit a DOT graph with short labels. -/
private def toDotShort (title : String) (records : Array DepRecord)
    (colorFn : String → String := fun _ => "black") : String :=
  let header := s!"digraph \"{jsonEscape title}\" \{\n  rankdir=LR;\n  node [shape=box, fontsize=9, style=filled];\n  edge [arrowsize=0.6];\n"
  -- Collect all referenced names for node declarations
  let allNamesList := Id.run do
    let mut s : NameHashSet := {}
    for r in records do
      s := s.insert r.name
      for dep in r.deps do
        s := s.insert dep
    return s.toList
  let nodes := allNamesList.foldl (init := "") fun acc n =>
    let short := shortName n
    let color := colorFn (classifyConstByName n records)
    acc ++ s!"  \"{jsonEscape n.toString}\" [label=\"{jsonEscape short}\", fillcolor=\"{color}\"];\n"
  let edges := records.foldl (init := "") fun acc r =>
    r.deps.foldl (init := acc) fun acc2 dep =>
      acc2 ++ s!"  \"{jsonEscape r.name.toString}\" -> \"{jsonEscape dep.toString}\";\n"
  header ++ nodes ++ edges ++ "}\n"
where
  classifyConstByName (n : Name) (records : Array DepRecord) : String :=
    match records.find? (fun r => r.name == n) with
    | some r => r.kind
    | none => "unknown"

unsafe def main (args : List String) : IO Unit := do
  -- Initialize search path and import the full Lean4Yaml environment
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Lean4Yaml }] {} 0

  -- Build a lookup from Name → SrcLoc using declRangeExt and module index
  let getLocation (n : Name) : Option SrcLoc :=
    -- Try the name itself, then fall back to its prefix (for auto-generated defs)
    let ranges := declRangeExt.find? (level := .exported) env n <|>
                  declRangeExt.find? (level := .server) env n <|>
                  declRangeExt.find? (level := .exported) env n.getPrefix <|>
                  declRangeExt.find? (level := .server) env n.getPrefix
    let modIdx := env.getModuleIdxFor? n <|> env.getModuleIdxFor? n.getPrefix
    match ranges, modIdx with
    | some dr, some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      some { module := modName.toString
             line := dr.range.pos.line
             endLine := dr.range.endPos.line }
    | some dr, none =>
      some { module := "<unknown>"
             line := dr.range.pos.line
             endLine := dr.range.endPos.line }
    | none, some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      some { module := modName.toString, line := 0, endLine := 0 }
    | none, none => none

  -- Collect all project constants into a flat array
  let allConsts : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc n ci =>
      if isProjectName n then acc.push (n, ci) else acc

  -- Build sets of project def and thm names
  let mut projectDefs : NameHashSet := {}
  let mut projectThms : NameHashSet := {}
  for (n, ci) in allConsts do
    match ci with
    | .defnInfo _ | .opaqueInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ =>
      projectDefs := projectDefs.insert n
    | .thmInfo _ =>
      projectThms := projectThms.insert n
    | _ => pure ()

  -- Extract dependencies
  let mut defCalls : Array DepRecord := #[]    -- graph 1: def → def calls
  let mut thmDeps : Array DepRecord := #[]     -- graph 2: thm → thm proof deps
  let mut thmAbout : Array DepRecord := #[]    -- graph 3: thm → def statement refs

  for (n, ci) in allConsts do
    match ci with
    | .defnInfo v =>
      let valueDeps := projectDeps v.value
      let callDeps := valueDeps.filter projectDefs.contains
      if callDeps.size > 0 then
        defCalls := defCalls.push { name := n, kind := "def", loc := getLocation n, deps := callDeps }
    | .thmInfo v =>
      -- Graph 2: proof dependencies (theorem → theorems used in proof)
      let proofAllDeps := projectDeps v.value
      let proofThmDeps := proofAllDeps.filter projectThms.contains
      if proofThmDeps.size > 0 then
        thmDeps := thmDeps.push { name := n, kind := "thm", loc := getLocation n, deps := proofThmDeps }
      -- Graph 3: what functions is this theorem about? (type mentions)
      let typeDeps := projectDeps v.type
      let typeDefDeps := typeDeps.filter projectDefs.contains
      if typeDefDeps.size > 0 then
        thmAbout := thmAbout.push { name := n, kind := "thm", loc := getLocation n, deps := typeDefDeps }
    | _ => pure ()

  -- Sort for deterministic output
  defCalls := defCalls.qsort (fun a b => a.name.toString < b.name.toString)
  thmDeps := thmDeps.qsort (fun a b => a.name.toString < b.name.toString)
  thmAbout := thmAbout.qsort (fun a b => a.name.toString < b.name.toString)

  -- Output mode
  match args with
  | ["--dot", "calls"] =>
    IO.println (toDotShort "Function Call Graph" defCalls (fun k =>
      if k == "def" then "#b3d9ff" else if k == "inductive" then "#ffe0b3" else "white"))
  | ["--dot", "thmdeps"] =>
    IO.println (toDotShort "Theorem Proof Dependencies" thmDeps (fun _ => "#d4edda"))
  | ["--dot", "about"] =>
    -- Bipartite: theorems → definitions
    let bipartite := thmAbout.map fun r => { r with kind := "thm" }
    IO.println (toDotShort "Theorems About Functions" bipartite (fun k =>
      if k == "thm" then "#d4edda" else if k == "def" then "#b3d9ff" else "#ffe0b3"))
  | ["--stats"] =>
    IO.println s!"Project definitions:  {projectDefs.size}"
    IO.println s!"Project theorems:     {projectThms.size}"
    IO.println s!"Def→def call edges:   {defCalls.foldl (init := 0) fun acc r => acc + r.deps.size}"
    IO.println s!"Thm→thm proof edges:  {thmDeps.foldl (init := 0) fun acc r => acc + r.deps.size}"
    IO.println s!"Thm→def about edges:  {thmAbout.foldl (init := 0) fun acc r => acc + r.deps.size}"
    IO.println s!"Defs with callees:    {defCalls.size}"
    IO.println s!"Thms with proof deps: {thmDeps.size}"
    IO.println s!"Thms about defs:      {thmAbout.size}"
  | ["--json", "calls"] =>
    IO.println "["
    for i in [:defCalls.size] do
      let comma := if i + 1 < defCalls.size then "," else ""
      IO.println s!"  {depRecordToJson defCalls[i]!}{comma}"
    IO.println "]"
  | ["--json", "thmdeps"] =>
    IO.println "["
    for i in [:thmDeps.size] do
      let comma := if i + 1 < thmDeps.size then "," else ""
      IO.println s!"  {depRecordToJson thmDeps[i]!}{comma}"
    IO.println "]"
  | ["--json", "about"] =>
    IO.println "["
    for i in [:thmAbout.size] do
      let comma := if i + 1 < thmAbout.size then "," else ""
      IO.println s!"  {depRecordToJson thmAbout[i]!}{comma}"
    IO.println "]"
  | _ =>
    -- Default: full JSON with all three graphs
    IO.println "{"
    IO.println "  \"defCalls\": ["
    for i in [:defCalls.size] do
      let comma := if i + 1 < defCalls.size then "," else ""
      IO.println s!"    {depRecordToJson defCalls[i]!}{comma}"
    IO.println "  ],"
    IO.println "  \"thmDeps\": ["
    for i in [:thmDeps.size] do
      let comma := if i + 1 < thmDeps.size then "," else ""
      IO.println s!"    {depRecordToJson thmDeps[i]!}{comma}"
    IO.println "  ],"
    IO.println "  \"thmAbout\": ["
    for i in [:thmAbout.size] do
      let comma := if i + 1 < thmAbout.size then "," else ""
      IO.println s!"    {depRecordToJson thmAbout[i]!}{comma}"
    IO.println "  ]"
    IO.println "}"
