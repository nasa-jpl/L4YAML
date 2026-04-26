/-
  CollectStats.lean — emit `stats.json` summarising L4YAML's verification
  posture.  Replaces the hand-typed numbers in `doc/Doc/L4YAML/Overview.lean`
  with a regenerated JSON file the docs read from.

  Usage:
      lake exe collect-stats [OUT]            # writes to OUT (default: docs/reports/stats.json)

  Three data sources, no test-suite reruns:
    * source-scan counts: `theorems`, `lemmas`, `lines`, `partial_defs`, `guards`
    * environment-scan counts (after loading the compiled `L4YAML` environment):
      `axioms_total`, `theorems_with_sorry`, `theorems_with_custom_axiom` —
      these are kernel-accurate and use `Lean.collectAxioms` to follow
      transitive dependencies.
    * dynamic counts: parsed from the existing test-runner outputs in
      `docs/reports/` (so `scripts/run-all-tests.sh` must have run first
      for those numbers to be present)

  Build-job totals are not derivable without running `lake build` — pass them
  via the `BUILD_JOBS_TOTAL` / `BUILD_JOBS_PASSED` env vars (CI sets these).
-/
import Lean
import L4YAML

open Lean (Json toJson)
open System (FilePath)

namespace L4YAML.CollectStats

/-! ## Source-tree scan -/

structure FileStats where
  theorems    : Nat := 0
  lemmas      : Nat := 0
  axioms      : Nat := 0
  partialDefs : Nat := 0
  guards      : Nat := 0
  lines       : Nat := 0
  deriving Inhabited

instance : Add FileStats where
  add a b := {
    theorems    := a.theorems    + b.theorems,
    lemmas      := a.lemmas      + b.lemmas,
    axioms      := a.axioms      + b.axioms,
    partialDefs := a.partialDefs + b.partialDefs,
    guards      := a.guards      + b.guards,
    lines       := a.lines       + b.lines,
  }

/-- Scan a single `.lean` file: simple per-line keyword counting.  We do not
    attempt to detect `sorry` here — that is done kernel-accurately via
    `Lean.collectAxioms` in `scanEnvAction`, so any heuristic here would just
    introduce false positives. -/
def scanFile (p : FilePath) : IO FileStats := do
  let content ← IO.FS.readFile p
  let allLines := content.splitOn "\n"
  let mut s : FileStats := { lines := allLines.length }
  for raw in allLines do
    let t := raw.trimAsciiStart.copy
    if t.startsWith "theorem "     then s := { s with theorems    := s.theorems + 1 }
    if t.startsWith "lemma "       then s := { s with lemmas      := s.lemmas + 1 }
    if t.startsWith "axiom "       then s := { s with axioms      := s.axioms + 1 }
    if t.startsWith "partial def " then s := { s with partialDefs := s.partialDefs + 1 }
    if t.startsWith "#guard "      then s := { s with guards      := s.guards + 1 }
  return s

/-- Recursively walk `dir`, collecting every `.lean` file. -/
def collectLeanFiles (dir : FilePath) : IO (Array FilePath) := do
  let entries ← System.FilePath.walkDir dir
  return entries.filter fun p => p.extension == some "lean"

structure RegionStats where
  files : Nat := 0
  stats : FileStats := {}
  deriving Inhabited

/-- Scan a directory tree, accumulating per-region stats. Returns
    `(file_count, summed_FileStats)` for `.lean` files under `dir`. -/
def scanRegion (dir : FilePath) : IO RegionStats := do
  if ! (← dir.pathExists) then return {}
  let files ← collectLeanFiles dir
  let mut acc : FileStats := {}
  for f in files do
    acc := acc + (← scanFile f)
  return { files := files.size, stats := acc }

structure StaticStats where
  library : RegionStats   -- L4YAML/  (production)
  proofs  : RegionStats   -- L4YAML/Proofs/  (subset of library)
  tests   : RegionStats   -- Tests/ + Demo/
  deriving Inhabited

def scanStatic (root : FilePath) : IO StaticStats := do
  let library ← scanRegion (root / "L4YAML")
  let proofs  ← scanRegion (root / "L4YAML" / "Proofs")
  -- Combine Tests/ + Demo/ into a single "tests" bucket.
  let tDir ← scanRegion (root / "Tests")
  let dDir ← scanRegion (root / "Demo")
  let tests : RegionStats := {
    files := tDir.files + dDir.files,
    stats := tDir.stats + dDir.stats,
  }
  return { library, proofs, tests }

/-! ## Test-runner output parsing -/

/-- Parse a single `"N/M"` fragment into `(N, M)`. -/
private def parseFraction (s : String) : Option (Nat × Nat) :=
  let parts : List String := s.splitOn "/"
  match parts with
  | [pStr, mStr] =>
    match String.toNat? pStr, String.toNat? mStr with
    | some pn, some mn => some (pn, mn)
    | _, _ => none
  | _ => none

/-- Scrape the trailing `=== Results: N/M passed ===` line from a runner's
    text output. Returns `(passed, total)` if found, else `none`. -/
def parseResultsLine (text : String) : Option (Nat × Nat) := Id.run do
  let lines := text.splitOn "\n"
  let mut found : Option (Nat × Nat) := none
  for line in lines.reverse do
    let t := line.trimAscii
    if t.startsWith "=== Results:" && t.endsWith "passed ===" then
      let body := ((t.drop "=== Results:".length).trimAscii).copy
      let frac := (body.splitOn " ").headD ""
      match parseFraction frac with
      | some pair => found := some pair; break
      | none      => pure ()
  return found

/-- Each suite the doc cares about: the runner's report file (relative to
    `docs/reports/`) and the suite's display name. -/
def runtimeSuites : List (String × String) := [
  ("unit-tests.txt",          "unit-tests"),
  ("explicitkeytests.txt",    "explicit-key-tests"),
  ("flowtests.txt",           "flow-tests"),
  ("validationtests.txt",     "validation-tests"),
  ("dumproundtrip.txt",       "dump-roundtrip"),
  ("rawparsetests.txt",       "raw-parse-tests"),
  ("scannertests.txt",        "scanner-tests"),
  ("scannerspecexamples.txt", "scanner-spec-examples"),
  ("adversarialtests.txt",    "adversarial-tests"),
  ("mutationtests.txt",       "mutation-tests"),
  ("propertytests.txt",       "property-tests"),
  ("productioncoverage.txt",  "production-coverage"),
  ("limittests.txt",          "limit-tests"),
  ("schemadump.txt",          "schema-dump"),
  ("demo.txt",                "demo"),
  ("flowregressioncheck.txt", "flow-regression-check"),
  ("errorstagediag.txt",      "error-stage-diag"),
  ("scalarstagediag.txt",     "scalar-stage-diag"),
]

structure SuiteResult where
  name   : String
  passed : Nat
  total  : Nat

def gatherTestSuites (reportsDir : FilePath) : IO (Array SuiteResult) := do
  let mut out : Array SuiteResult := #[]
  for (file, name) in runtimeSuites do
    let p := reportsDir / file
    if ← p.pathExists then
      let txt ← IO.FS.readFile p
      if let some (pn, mn) := parseResultsLine txt then
        out := out.push { name, passed := pn, total := mn }
  return out

/-! ## Spec-examples & yaml-test-suite -/

structure SpecExamples where
  passed : Nat
  total  : Nat

def gatherSpecExamples (reportsDir : FilePath) : IO (Option SpecExamples) := do
  let p := reportsDir / "specexamples.txt"
  if ! (← p.pathExists) then return none
  let txt ← IO.FS.readFile p
  return parseResultsLine txt |>.map fun (passed, total) => { passed, total }

/-- Decode the yaml-test-suite breakdown from `coverage-summary.json` written
    by `suiterunner --html`.  Schema (relevant subset):
        { "overall": { "applicable": …, "correct": …, "correctRate": …,
                       "passed": …, "expectedFail": …, "skipped": …,
                       "failed": …, "total": … }, … } -/
def gatherYamlTestSuite (reportsDir : FilePath) : IO (Option Json) := do
  let p := reportsDir / "coverage-summary.json"
  if ! (← p.pathExists) then return none
  let txt ← IO.FS.readFile p
  match Json.parse txt with
  | .error _ => return none
  | .ok j    => return j.getObjValAs? Json "overall" |>.toOption

/-! ## Environment-based axiom + sorry analysis

  The source-scan numbers above are heuristics. For the kernel-accurate
  counts (axioms, theorems whose proof transitively depends on `sorryAx`),
  we load the compiled `L4YAML` environment via `importModules` and call
  `Lean.collectAxioms` on each theorem. -/

/-- Lean's stock axioms (always present in any Lean program). Filtered out
    of `axioms_total` so the count reflects user-declared axioms only. -/
def builtinAxioms : Lean.NameSet :=
  ([`Classical.choice, `propext, `Quot.sound, `sorryAx,
    `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler,
    `Lean.trustReducibility].foldl (·.insert ·) Lean.NameSet.empty)

/-- The `sorry` tactic compiles to `sorryAx`. -/
def sorryAxName : Lean.Name := `sorryAx

structure EnvStats where
  totalThms              : Nat := 0   -- theorems in L4YAML.* namespace
  totalAxioms            : Nat := 0   -- user-declared axioms (excludes builtins)
  thmsWithDirectSorry    : Nat := 0   -- thms whose own proof term mentions sorryAx
  thmsWithSorry          : Nat := 0   -- thms whose proof transitively depends on sorryAx
  thmsWithCustomAxiom    : Nat := 0   -- thms transitively depending on a user-declared axiom
  customAxiomNames       : Array String := #[]  -- names of any custom axioms found
  deriving Inhabited

/-- Run the env walk inside `CoreM` so we can call `Lean.collectAxioms`
    (which needs `[MonadEnv m]`). -/
def scanEnvAction (rootName : Lean.Name) : Lean.CoreM EnvStats := do
  let env ← Lean.getEnv
  let mut s : EnvStats := {}
  for (name, info) in env.constants do
    -- Only L4YAML.* declarations count; this excludes Std/Init/Lean.
    if !rootName.isPrefixOf name then continue
    -- Skip auto-generated equation lemmas (`._eq_1` etc.) and macro scopes.
    if name.isInternal || name.hasMacroScopes then continue
    match info with
    | .axiomInfo _ =>
      if !builtinAxioms.contains name then
        s := { s with
          totalAxioms      := s.totalAxioms + 1,
          customAxiomNames := s.customAxiomNames.push name.toString }
    | .thmInfo thmInfo =>
      s := { s with totalThms := s.totalThms + 1 }
      -- Direct sorry: `sorryAx` appears in the theorem's own proof term.
      -- This matches Lean's "declaration uses sorry" warnings (one per
      -- source-level `sorry` keyword in a top-level theorem body).
      let directSorry := thmInfo.value.foldConsts (init := false)
        fun n acc => acc || n == sorryAxName
      if directSorry then
        s := { s with thmsWithDirectSorry := s.thmsWithDirectSorry + 1 }
      let axs ← Lean.collectAxioms name
      if axs.contains sorryAxName then
        s := { s with thmsWithSorry := s.thmsWithSorry + 1 }
      -- A "custom axiom" here means a user-declared L4YAML axiom. We
      -- exclude `Name.isInternalDetail` to skip Lean's auto-generated
      -- `_native.native_decide.ax_*` axioms (one per `native_decide` call).
      -- Those are stock kernel infrastructure trusted via `Lean.ofReduceBool`,
      -- not project-declared axioms.
      let customs := axs.filter fun a =>
        rootName.isPrefixOf a && !a.isInternalDetail
      if !customs.isEmpty then
        s := { s with
          thmsWithCustomAxiom := s.thmsWithCustomAxiom + 1,
          customAxiomNames    :=
            customs.foldl (fun acc a => acc.push a.toString) s.customAxiomNames }
    | _ => continue
  return s

/-- Load the compiled `L4YAML` environment and run the env walk. The exe
    was compiled with `import L4YAML`, so the .olean files are guaranteed
    on disk when Lake invokes us. -/
unsafe def scanEnv (rootName : Lean.Name) : IO EnvStats := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := rootName }] {} 0
  let coreCtx : Lean.Core.Context :=
    { fileName := "<collect-stats>", fileMap := default }
  let coreState : Lean.Core.State := { env }
  let (s, _) ← (scanEnvAction rootName).toIO coreCtx coreState
  return s

/-! ## Build-job count (env-var injected) -/

structure BuildJobs where
  total  : Nat
  passed : Nat

def gatherBuildJobs : IO (Option BuildJobs) := do
  let totalStr  ← IO.getEnv "BUILD_JOBS_TOTAL"
  let passedStr ← IO.getEnv "BUILD_JOBS_PASSED"
  match totalStr, passedStr with
  | some t, some p =>
    match t.toNat?, p.toNat? with
    | some tn, some pn => return some { total := tn, passed := pn }
    | _, _ => return none
  | _, _ => return none

/-! ## Aggregate + emit -/

unsafe def buildJson (root : FilePath) : IO Json := do
  let stat ← scanStatic root
  let reportsDir := root / "docs" / "reports"
  let suites ← gatherTestSuites reportsDir
  let specEx ← gatherSpecExamples reportsDir
  let yts    ← gatherYamlTestSuite reportsDir
  let bj     ← gatherBuildJobs
  let envS   ← scanEnv `L4YAML

  let suiteCount  := suites.size
  let totalTests  := suites.foldl (init := 0) fun a r => a + r.total
  let totalPassed := suites.foldl (init := 0) fun a r => a + r.passed

  let suitesJson : Json := Json.arr <| suites.map fun r =>
    Json.mkObj [
      ("name",   Json.str r.name),
      ("passed", toJson r.passed),
      ("total",  toJson r.total),
    ]

  let regionJson (r : RegionStats) : Json := Json.mkObj [
    ("lean_files",           toJson r.files),
    ("lines",                toJson r.stats.lines),
    ("theorems",             toJson r.stats.theorems),
    ("lemmas",               toJson r.stats.lemmas),
    ("theorems_plus_lemmas", toJson (r.stats.theorems + r.stats.lemmas)),
    ("axioms",               toJson r.stats.axioms),
    ("partial_defs",         toJson r.stats.partialDefs),
    ("guards",               toJson r.stats.guards),
  ]
  let staticJson := Json.mkObj [
    ("library", regionJson stat.library),  -- L4YAML/  (production)
    ("proofs",  regionJson stat.proofs),   -- L4YAML/Proofs/  (subset of library)
    ("tests",   regionJson stat.tests),    -- Tests/ + Demo/
  ]

  let testsJson := Json.mkObj [
    ("suite_count",  toJson suiteCount),
    ("total_tests",  toJson totalTests),
    ("total_passed", toJson totalPassed),
    ("suites",       suitesJson),
  ]

  let specExJson : Json := match specEx with
    | none   => Json.null
    | some s => Json.mkObj [("passed", toJson s.passed), ("total", toJson s.total)]

  let bjJson : Json := match bj with
    | none   => Json.null
    | some b => Json.mkObj [("total", toJson b.total), ("passed", toJson b.passed)]

  let envJson := Json.mkObj [
    ("theorems",                       toJson envS.totalThms),
    ("axioms",                         toJson envS.totalAxioms),
    ("theorems_with_direct_sorry",     toJson envS.thmsWithDirectSorry),
    ("theorems_with_transitive_sorry", toJson envS.thmsWithSorry),
    ("theorems_with_custom_axiom",     toJson envS.thmsWithCustomAxiom),
    ("custom_axiom_names",
      Json.arr (envS.customAxiomNames.map Json.str)),
  ]

  let now ← IO.monoMsNow
  return Json.mkObj [
    ("schema_version", toJson (2 : Nat)),
    ("generated_at_ms", toJson now),
    ("static",          staticJson),
    ("env",             envJson),
    ("build_jobs",      bjJson),
    ("test_suites",     testsJson),
    ("spec_examples",   specExJson),
    ("yaml_test_suite", yts.getD Json.null),
  ]

unsafe def main (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  -- Find the repo root: caller may invoke from `cwd = repo` or `cwd = repo/doc`.
  let candidates : List FilePath := [cwd, cwd / "..", cwd / "../.."]
  let mut rootOpt : Option FilePath := none
  for c in candidates do
    if ← (c / "L4YAML.lean").pathExists then
      rootOpt := some c; break
  let root := rootOpt.getD cwd

  let outPath : FilePath := match args with
    | [p] => FilePath.mk p
    | _   => root / "docs" / "reports" / "stats.json"

  let json ← buildJson root
  IO.FS.createDirAll (outPath.parent.getD ".")
  IO.FS.writeFile outPath json.pretty
  IO.println s!"collect-stats: wrote {outPath}"
  return 0

end L4YAML.CollectStats

unsafe def main (args : List String) : IO UInt32 := L4YAML.CollectStats.main args
