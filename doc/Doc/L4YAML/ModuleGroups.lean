/-
  L4YAML Documentation — Module organization table.

  Defines `:::moduleGroups`, a Verso block directive that walks each
  declared group's source directory at doc-elaboration time and renders
  the `Architecture > Module Organization` table.  Replaces the
  hand-typed three-column table in `Architecture.lean`, so the file
  list per group stays in sync as modules move under `L4YAML/`.

  Edit `groups` below when reorganizing top-level dirs or rewriting
  a group's purpose prose.  Inline-code spans in prose use Markdown
  backticks: `"…the `scanNextToken` dispatch…"`.
-/
import Lean
import VersoManual
import Doc.L4YAML.CellDsl

open Lean Elab
open Verso Doc Elab
open Verso.Genre Manual
open Doc.L4YAML.CellDsl

namespace Doc.L4YAML.ModuleGroups

structure Group where
  /-- Group name (column 1). -/
  name  : String
  /-- One or more source directories to scan, relative to the repo root.
      Every `.lean` file under these dirs (recursive) is listed in column 2. -/
  dirs  : List String
  /-- Free-form purpose prose (column 3). Backtick-delimited spans
      become inline code. -/
  prose : String
  /-- If `true`, list every `.lean` file in column 2. If `false`, show
      just the file count (useful for the `Proofs/` subtree where the
      full enumeration is overwhelming). -/
  listFiles : Bool := true

/-- Source of truth for the module organization table. Keep ordered roughly
    by data-flow direction (input → output). -/
def groups : Array Group := #[
  { name  := "Spec",
    dirs  := ["L4YAML/Spec", "L4YAML/Token"],
    prose :=
      "Type definitions, token types, grammar inductive, " ++
      "spec production predicates." },
  { name  := "Config",
    dirs  := ["L4YAML/Config"],
    prose :=
      "Parser limits and configuration presets " ++
      "(`strict` / `default` / `permissive` / `unlimited` / `safe_tags`)." },
  { name  := "Scanner",
    dirs  := ["L4YAML/Scanner"],
    prose :=
      "Character-to-token conversion with full state management. " ++
      "Split into role-named submodules; the umbrella `Scanner.lean` " ++
      "owns flow-collection indicators and the `scanNextToken` " ++
      "dispatch / `scan` / `scanLoop` main loop." },
  { name  := "Parser",
    dirs  := ["L4YAML/Parser"],
    prose :=
      "Token-to-AST recursive descent. `Composition.lean` owns the " ++
      "user-facing pipeline (`parseYaml*`, `scanAndParse`, comment " ++
      "classification); `TokenParser.lean` keeps the 14-function " ++
      "mutually-recursive block plus `parseStream` / `parseDocument`; " ++
      "`State.lean` holds `ParseState` + `NodeProperties` helpers; " ++
      "`Fuel.lean` factors out the `initialFuel := 4*N+4` formula." },
  { name  := "Surface",
    dirs  := ["L4YAML/Surface"],
    prose :=
      "Formal YAML 1.2.2 surface-syntax grammar productions used to " ++
      "state and discharge the acceptance-strictness theorem." },
  { name  := "Schema",
    dirs  := ["L4YAML/Schema"],
    prose :=
      "Core Schema type resolution, structural API (`Api.lean`), and " ++
      "deriving for round-tripping user types via `FromToYaml.lean`." },
  { name  := "Output",
    dirs  := ["L4YAML/Output"],
    prose :=
      "Canonical `Emitter.lean`, style-aware `Dump.lean`, and " ++
      "`RoundTrip.lean` (`emit ∘ parse = id` properties)." },
  { name  := "FFI",
    dirs  := ["L4YAML/FFI"],
    prose :=
      "C/Python/Rust bindings via `@[export]`. The companion `ffi/`, " ++
      "`python/`, and `rust/` directories outside `L4YAML/` carry the " ++
      "non-Lean glue." },
  { name      := "Proofs",
    dirs      := ["L4YAML/Proofs"],
    prose     :=
      "Machine-checked theorems for soundness, completeness, progress, " ++
      "and well-formedness.",
    listFiles := false }
]

/-! ## File-system walk -/

/-- Locate the repo root from the doc-build's cwd (one of `cwd` or `cwd/..`). -/
def resolveRepoRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  let candidates := #[cwd, cwd / ".."]
  for c in candidates do
    if ← (c / "L4YAML.lean").pathExists then return c
  throw (IO.userError s!"can't find repo root from {cwd}")

/-- Collect every `.lean` file under `dir` (recursive), returning bare
    file names (no path) sorted ASCII-ascending. -/
def collectLeanFiles (dir : System.FilePath) : IO (Array String) := do
  if !(← dir.pathExists) then return #[]
  let entries ← System.FilePath.walkDir dir
  let names := entries.filterMap fun p =>
    if p.extension == some "lean" then p.fileName else none
  return names.qsort (· < ·)

/-! ## Build the table -/

/-- Build the cells (row-major, header first). -/
def buildCells : IO (Array Cell) := do
  let root ← resolveRepoRoot
  let mut out : Array Cell := #[
    [.text "Group"], [.text "Key Modules"], [.text "Purpose"]
  ]
  for g in groups do
    out := out.push [.text g.name]
    let mut files : Array String := #[]
    for d in g.dirs do
      files := files ++ (← collectLeanFiles (root / d))
    let modulesCell : Cell :=
      if !g.listFiles then
        [.text s!"{files.size} modules"]
      else
        match files.toList with
        | []      => [.text "—"]
        | f :: rs => rs.foldl (init := [Run.code f])
                       (fun acc x => acc ++ [.text ", ", .code x])
    out := out.push modulesCell
    out := out.push (parseProse g.prose)
  return out

/-! ## Directive -/

/-- `:::moduleGroups` — render the Architecture > Module Organization
    table from the `groups` source-of-truth, walking each group's source
    directory for the file list. -/
@[directive]
def moduleGroups : DirectiveExpanderOf Unit
  | (), _ => do
    let cells ← Doc.L4YAML.ModuleGroups.buildCells
    buildTableSyntax 3 (header := true) cells

end Doc.L4YAML.ModuleGroups
