/-
  L4YAML Documentation — At-a-Glance table from the embedded stats payload.

  Defines `:::statsTable`, a Verso block directive that renders the
  at-a-glance table (which used to live as hand-typed numbers in
  `doc/Doc/L4YAML/Overview.lean`) from `Doc.L4YAML.StatsData.statsJson?`
  — the `stats.json` payload embedded as a Lean string literal by
  `lake exe collect-stats --emit-lean`.

  The payload is an IMPORT, not an elaboration-time file read, so Lake
  tracks it: regenerating `StatsData.lean` re-elaborates exactly the
  modules that use this directive. The committed `StatsData.lean` is a
  `none` placeholder — every cell renders `"?"` and the doc builds
  hermetically from a fresh clone. Missing fields likewise render as
  `"?"` when an older payload is embedded.

  Schema mirrors `tools/CollectStats.lean` (schema_version 2).
-/
import Lean
import VersoManual
import Doc.L4YAML.CellDsl
import Doc.L4YAML.StatsData

open Lean Elab
open Verso Doc Elab
open Verso.Genre Manual
open Lean.Doc.Syntax
open Doc.L4YAML.CellDsl

namespace Doc.L4YAML.StatsTable

/-! ## JSON loading -/

/-- Parse the embedded payload. The committed placeholder (`none`)
    yields `Json.null`, so every lookup misses and renders `"?"` — a
    fresh-clone build stays green. A malformed GENERATED payload is a
    hard error: it can only come from a broken `--emit-lean`. -/
def loadJson : Except String Json :=
  match StatsData.statsJson? with
  | none   => .ok Json.null
  | some s => Json.parse s

/-! ## JSON path helpers -/

/-- Walk `j` along `path` (object keys); return `none` if any key is missing. -/
def jPath (j : Json) (path : List String) : Option Json :=
  path.foldlM (fun (cur : Json) k => (cur.getObjValAs? Json k).toOption) j

def jNat (j : Json) (path : List String) : Option Nat :=
  jPath j path >>= fun x => x.getNat?.toOption

/-! ## Number formatting -/

private def addCommas : List Char → List Char
  | [] => []
  | c :: rest =>
    let tail := addCommas rest
    if rest.length > 0 && rest.length % 3 == 0 then c :: ',' :: tail
    else c :: tail

def withCommas (n : Nat) : String :=
  String.ofList (addCommas (toString n).toList)

def withCommasOpt : Option Nat → String
  | some n => withCommas n
  | none   => "?"

def natOpt : Option Nat → String
  | some n => toString n
  | none   => "?"

def fracOpt (p? t? : Option Nat) : String :=
  match p?, t? with
  | some p, some t => s!"{withCommas p}/{withCommas t}"
  | _, _ => "?"

/-! ## Row builder -/

/-- Build the at-a-glance table rows from parsed `stats.json`.
    Returns a flat list of cells (header row first, two cells per row). -/
def buildCells (j : Json) : Array Cell := Id.run do
  let envThm        := jNat j ["env", "theorems"]
  let proofMods     := jNat j ["static", "proofs", "lean_files"]
  let proofLines    := jNat j ["static", "proofs", "lines"]
  let guardsLib     := jNat j ["static", "library", "guards"]
  let guardsTests   := jNat j ["static", "tests", "guards"]
  let guards        := match guardsLib, guardsTests with
                       | some a, some b => some (a + b)
                       | some a, none   => some a
                       | none,   some b => some b
                       | _,      _      => none
  let envAxioms     := jNat j ["env", "axioms"]
  let envSorry      := jNat j ["env", "theorems_with_direct_sorry"]
  let partialDefs   := jNat j ["static", "library", "partial_defs"]
  let suitesPassed  := jNat j ["test_suites", "total_passed"]
  let suiteCount    := jNat j ["test_suites", "suite_count"]
  let specPassed    := jNat j ["spec_examples", "passed"]
  let specTotal     := jNat j ["spec_examples", "total"]
  let ytsApplicable := jNat j ["yaml_test_suite", "applicable"]
  let ytsCorrect    := jNat j ["yaml_test_suite", "correct"]
  let ytsCorrectRate := jNat j ["yaml_test_suite", "correctRate"]
  let ytsTotal      := jNat j ["yaml_test_suite", "total"]
  let ytsPassed     := jNat j ["yaml_test_suite", "passed"]
  let ytsSkipped    := jNat j ["yaml_test_suite", "skipped"]

  let ytsTotalCell : Cell :=
    match ytsTotal, ytsPassed, ytsSkipped with
    | some t, some _, some sk =>
      let pct : Nat := if t == 0 then 0 else 100 * (t - sk) / t
      [.text s!"{t - sk}/{t} ({pct}%; {sk} skipped are YAML 1.1/1.3)"]
    | _, _, _ => [.text "?"]

  let rows : Array (Cell × Cell) := #[
    ( [.text "Key Metric"], [.text "Value"] ),

    ( [.text "Machine-checked theorems"],
      [.text s!"{withCommasOpt envThm} across {natOpt proofMods} proof modules (~{withCommasOpt proofLines} lines)"] ),

    ( [.text "Compile-time ", .code "#guard", .text " tests"],
      [.text s!"{withCommasOpt guards} (kernel-evaluated at build time)"] ),

    ( [.text "Axioms / ", .code "sorry", .text " / ", .code "partial def"],
      [.text s!"{natOpt envAxioms} / {natOpt envSorry} / {natOpt partialDefs}"] ),

    ( [.text "Runtime test suites"],
      [.text s!"{withCommasOpt suitesPassed} tests across {natOpt suiteCount} suites"] ),

    ( [.text "Spec examples passing"],
      let suffix : String := match specPassed, specTotal with
        | some p, some t => if t > 0 && p == t then " (100%)" else ""
        | _, _ => ""
      [.text s!"{fracOpt specPassed specTotal}{suffix}"] ),

    ( [.text "yaml-test-suite IDs"],
      [.text s!"{fracOpt ytsCorrect ytsApplicable} YAML 1.2.2-applicable ({natOpt ytsCorrectRate}%)"] ),

    ( [.text "yaml-test-suite total"], ytsTotalCell )
  ]

  -- Flatten into a single array of cells (one ListItem each); the table
  -- renderer chunks back into 2-column rows.
  let mut out : Array Cell := #[]
  for (a, b) in rows do
    out := out.push a |>.push b
  return out

/-! ## Directive -/

/-- `:::statsTable` — render the at-a-glance table from the embedded
    `Doc.L4YAML.StatsData` payload.
    Schema mirrors `tools/CollectStats.lean` (schema_version 2). -/
@[directive]
def statsTable : DirectiveExpanderOf Unit
  | (), _ => do
    match Doc.L4YAML.StatsTable.loadJson with
    | .error e => throwError "StatsData payload parse error: {e}"
    | .ok j => buildTableSyntax 2 (header := true) (buildCells j)

end Doc.L4YAML.StatsTable
