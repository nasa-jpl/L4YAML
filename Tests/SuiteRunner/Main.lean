import Lean4Yaml
import Tests.SuiteRunner.Meta
import Tests.SuiteRunner.HtmlReport
import Tests.VerifiedResult
import Tests.Main
import Tests.ExplicitKeyTests
import Tests.FlowTests
import Tests.ValidationTests
import Tests.DumpRoundTrip
import Tests.RawParseTests
import Tests.SpecExamples
import Tests.SchemaDump
import Tests.ScannerTests
import Tests.ScannerSpecExamples
import Tests.AdversarialGrammarTests
import Tests.MutationSuiteTests
import Tests.PropertyTests
import Tests.ProductionCoverage
import Demo

/-!
# yaml-test-suite Runner

Programmatic test runner that reads yaml-test-suite test files,
parses each test's YAML input with our parser, and reports
pass/fail results staged by feature coverage.

## Usage

```bash
# Console output (default)
.lake/build/bin/suiterunner [stage] [-v|--verbose]

# Generate HTML reports
.lake/build/bin/suiterunner --html docs/

# Generate JSON summary only (faster, no HTML)
.lake/build/bin/suiterunner --json docs/

# JSON with timestamped snapshot
.lake/build/bin/suiterunner --json results/ --snapshot
```

## References

- <https://github.com/yaml/yaml-test-suite>
- <https://yaml.org/spec/1.2.2/>
-/

open Lean4Yaml
open Tests.SuiteRunner

/-! ## Debug Helpers -/

/-- Flush stdout so piped output (e.g., `| tee`) appears immediately. -/
private def flushStdout : IO Unit := do (← IO.getStdout).flush

/-- Log a timestamped debug message to stderr.
    Stderr is line-buffered even when stdout is piped, so these
    always appear immediately. -/
private def dbg (startMs : Nat) (msg : String) : IO Unit := do
  let now ← IO.monoMsNow
  let elapsed := now - startMs
  IO.eprintln s!"[DBG +{elapsed}ms] {msg}"
  (← IO.getStderr).flush

/-! ## Test Execution -/

/-- Tests tagged `1.3-err`/`1.3-mod` whose YAML 1.2.2 behavior we handle correctly.
    These are included despite the 1.3 tag because the test's expected tree reflects
    the 1.2.2 result. See README P10.6d §2.2 — `foldBlockContent` 4-state machine. -/
private def yaml13Include : List String :=
  ["6VJK", "7T8X", "MJS9", "M9B4"]

/-- Result of running a single test case. -/
inductive TestResult where
  | pass (stdout : String := "")
  | fail (reason : String) (stdout : String := "")
  | skip (reason : String)
  deriving Repr

/-- Run a single test case against our parser (pure computation). -/
def runTestCore (tc : TestCase) : TestResult :=
  let yaml := unescapeTestYaml tc.yaml
  if yaml.isEmpty then .skip "empty yaml input"
  -- Tests tagged 1.3-err or 1.3-mod are YAML 1.3 specific (unless allowlisted)
  else if tc.tags.any (fun t => t == "1.3-err" || t == "1.3-mod")
      && !yaml13Include.contains tc.id then
    .skip "YAML 1.3 specific"
  else if tc.expectFail then .skip "error test (run with 'error' stage)"
  else
    match Lean4Yaml.TokenParser.parseYaml yaml with
    | Except.ok _docs => .pass
    | Except.error e => .fail s!"parse error: {e}"

/-- Run a single test case using OS-level process isolation.
    Writes YAML to a temp file, runs `tryparse` via `timeout(1)`,
    and checks exit code: 0 = pass, 1 = parse error, 124 = timeout. -/
def runTest (tc : TestCase) (timeoutSec : Nat := 2) : IO TestResult := do
  let yaml := unescapeTestYaml tc.yaml
  if yaml.isEmpty then return .skip "empty yaml input"
  if tc.tags.any (fun t => t == "1.3-err" || t == "1.3-mod")
      && !yaml13Include.contains tc.id then
    return .skip "YAML 1.3 specific"
  -- Write yaml to temp file (use project-local tmp/ per workspace rules)
  IO.FS.createDirAll "tmp"
  let tmpPath := s!"tmp/yaml_suite_test_{tc.id}.yaml"
  IO.FS.writeFile tmpPath yaml
  -- Run tryparse with OS-level timeout
  let result ← IO.Process.output {
    cmd := "timeout"
    args := #[s!"{timeoutSec}", ".lake/build/bin/tryparse", tmpPath]
  }
  -- Clean up temp file
  try IO.FS.removeFile tmpPath catch _ => pure ()
  -- Capture stdout for parser output (used in JSON reports for UP/fail analysis)
  let stdout := result.stdout.trimAscii.toString
  -- Interpret exit code
  if result.exitCode == 0 then
    if tc.expectFail then return .fail "expected parse failure but succeeded" stdout
    else return .pass stdout
  else if result.exitCode == 124 then
    return .fail "timeout (possible infinite loop)"
  else
    if tc.expectFail then return .pass stdout
    else return .fail s!"parse error: {result.stderr.trimAscii.toString}" stdout

/-- Summary statistics for a test run. -/
structure TestStats where
  total : Nat := 0
  passed : Nat := 0
  failed : Nat := 0
  skipped : Nat := 0
  failures : Array (String × String) := #[]  -- (testId, reason)
  deriving Repr

instance : ToString TestStats where
  toString s :=
    s!"{s.passed} passed, {s.failed} failed, {s.skipped} skipped ({s.total} total)"

/-! ## File System Operations -/

/-- Read all `.yaml` files from the test suite `src/` directory. -/
def readTestFiles (suiteDir : String) : IO (Array (String × String)) := do
  let srcDir := suiteDir ++ "/src"
  let entries ← System.FilePath.readDir srcDir
  let mut files : Array (String × String) := #[]
  for entry in entries do
    let path := entry.path
    if path.extension == some "yaml" then
      let content ← IO.FS.readFile path
      -- Extract test ID from filename (e.g., "229Q" from "229Q.yaml")
      let testId := path.fileStem.getD "unknown"
      files := files.push (testId, content)
  return files.insertionSort (fun a b => a.1 < b.1)

/-! ## Main Runner -/

/-- Run all tests in a given stage and print results. -/
def runStage (stage : Stage) (testCases : Array TestCase)
    (verbose : Bool := false) : IO TestStats := do
  let filtered := testCases.filter (·.inStage stage)
  IO.println s!"Running {filtered.size} tests for stage: {stage}"
  IO.println (String.ofList (List.replicate 60 '-'))
  let mut stats : TestStats := {}
  let mut idx : Nat := 0
  for tc in filtered do
    idx := idx + 1
    stats := { stats with total := stats.total + 1 }
    -- Show progress for every test so user can see we're not stuck
    IO.print s!"  [{idx}/{filtered.size}] {tc.id} "
    flushStdout
    let result ← runTest tc
    match result with
    | .pass .. =>
      stats := { stats with passed := stats.passed + 1 }
      IO.println "✓"
    | .fail reason .. =>
      let failures := stats.failures.push (tc.id, reason)
      stats := { stats with failed := stats.failed + 1 }
      stats := { stats with failures := failures }
      IO.println s!"✗ {reason}"
    | .skip reason =>
      stats := { stats with skipped := stats.skipped + 1 }
      IO.println s!"○ {reason}"
  IO.println (String.ofList (List.replicate 60 '-'))
  IO.println s!"  {stats}"
  if stats.failures.size > 0 && !verbose then
    IO.println s!"\n  Failed tests:"
    for pair in stats.failures do
      IO.println s!"    {pair.1}: {pair.2}"
  IO.println ""
  return stats

/-- Parse command-line stage argument. -/
def parseStageArg (arg : String) : Stage :=
  match arg with
  | "scalar" => .scalar
  | "flow" => .flow
  | "block" => .block
  | "document" => .document
  | "advanced" => .advanced
  | "error" => .error
  | _ => .all

/-- Run all test cases and collect ReportResults for HTML generation. -/
def runAllForReport (testCases : Array TestCase) (stage : Stage)
    (timeoutSec : Nat := 2) (startMs : Nat := 0) : IO (Array ReportResult) := do
  let filtered := if stage == .all then testCases
                  else testCases.filter (fun tc =>
                    tc.stage == stage || (stage != .error && tc.inStage stage))
  dbg startMs s!"runAllForReport: {filtered.size} tests to run"
  let mut results : Array ReportResult := #[]
  let mut idx : Nat := 0
  for tc in filtered do
    idx := idx + 1
    IO.print s!"  [{idx}/{filtered.size}] {tc.id} "
    flushStdout
    let result ← runTest tc timeoutSec
    let reportResult : ReportResult := match result with
      | .pass stdout =>
        let po := if stdout.isEmpty then none else some stdout
        if tc.expectFail then
          { testCase := tc, outcome := .expectedFail, parserOutput := po }
        else
          { testCase := tc, outcome := .pass, parserOutput := po }
      | .fail reason stdout =>
        let po := if stdout.isEmpty then none else some stdout
        if (reason.splitOn "timeout").length > 1 then
          { testCase := tc, outcome := .timeout, errorMsg := some reason }
        else if (reason.splitOn "expected parse failure but succeeded").length > 1 then
          { testCase := tc, outcome := .unexpectedPass, errorMsg := some reason,
            parserOutput := po }
        else if tc.expectFail then
          { testCase := tc, outcome := .expectedFail, errorMsg := some reason,
            parserOutput := po }
        else
          { testCase := tc, outcome := .fail, errorMsg := some reason,
            parserOutput := po }
      | .skip reason =>
        { testCase := tc, outcome := .skip reason }
    -- Console output
    match reportResult.outcome with
    | .pass => IO.println "✓"
    | .fail => IO.println s!"✗ {reportResult.errorMsg.getD ""}"
    | .expectedFail => IO.println "✓ (expected fail)"
    | .unexpectedPass => IO.println s!"⚠ unexpected pass"
    | .skip reason => IO.println s!"○ {reason}"
    | .timeout => IO.println s!"⏱ timeout"
    flushStdout
    -- Periodic stderr progress (every 25 tests)
    if idx % 25 == 0 then
      dbg startMs s!"runAllForReport: completed {idx}/{filtered.size}"
    results := results.push reportResult
  dbg startMs s!"runAllForReport: finished all {filtered.size} tests"
  return results

def main (args : List String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  dbg t0 "suiterunner starting"

  -- Parse arguments
  let mut stageArg := "all"
  let mut verbose := false
  let mut htmlDir : Option String := none
  let mut jsonDir : Option String := none
  let mut snapshot := false
  let mut i : Nat := 0
  let mut skipNext := false
  for arg in args do
    if skipNext then
      skipNext := false
    else if arg == "-v" || arg == "--verbose" then
      verbose := true
    else if arg == "--html" then
      match args.drop (i + 1) with
      | dir :: _ => htmlDir := some dir; skipNext := true
      | [] => IO.eprintln "Error: --html requires a directory argument"; return 1
    else if arg == "--json" then
      match args.drop (i + 1) with
      | dir :: _ => jsonDir := some dir; skipNext := true
      | [] => IO.eprintln "Error: --json requires a directory argument"; return 1
    else if arg == "--snapshot" then
      snapshot := true
    else
      stageArg := arg
    i := i + 1

  let stage := parseStageArg stageArg

  -- Locate yaml-test-suite relative to executable
  let suiteDir := "yaml-test-suite"
  let srcPath : System.FilePath := suiteDir ++ "/src"
  let srcExists ← srcPath.pathExists
  if !srcExists then
    IO.eprintln s!"Error: yaml-test-suite not found at {suiteDir}"
    IO.eprintln "Run: git submodule update --init"
    return 1

  IO.println "══════════════════════════════════════════════════════════"
  IO.println "  yaml-test-suite Runner for lean4-yaml-verified"
  IO.println "══════════════════════════════════════════════════════════"
  IO.println ""
  flushStdout
  dbg t0 "banner printed"

  -- Read and parse all test files
  IO.print "Loading test files... "
  flushStdout
  dbg t0 "reading test files from yaml-test-suite/src"
  let files ← readTestFiles suiteDir
  dbg t0 s!"read {files.size} files, parsing metadata"
  let mut allCases : Array TestCase := #[]
  for pair in files do
    let cases := parseTestFile pair.1 pair.2
    allCases := allCases ++ cases
  dbg t0 s!"parsed {allCases.size} test cases"
  IO.println s!"{allCases.size} test cases from {files.size} files"
  IO.println ""
  flushStdout

  -- Print stage distribution
  IO.println "Test distribution by stage:"
  let stages := #[Stage.scalar, .flow, .block, .document, .advanced, .error]
  for s in stages do
    let count := allCases.filter (·.stage == s) |>.size
    IO.println s!"  {s}: {count}"
  IO.println ""
  flushStdout
  dbg t0 "distribution printed, entering main test loop"

  -- Shared helper: run all verified test suites and print progress
  let runVerifiedSuites : IO (Array Tests.VerifiedSuiteResult) := do
    IO.println "\nRunning verified test suites..."
    flushStdout
    dbg t0 "starting verified test suites"
    let collectors : Array (IO Tests.VerifiedSuiteResult) := #[
      Tests.collectTests,
      Tests.ExplicitKey.collectTests,
      Tests.Flow.collectTests,
      Tests.Validation.collectTests,
      Tests.DumpRoundTrip.collectTests,
      Tests.RawParse.collectTests,
      Tests.SpecExamples.collectTests,
      Tests.SchemaDump.collectTests,
      Tests.ScannerTests.collectTests,
      Tests.ScannerSpecExamples.collectTests,
      Tests.AdversarialGrammar.collectTests,
      Tests.MutationSuite.collectTests,
      Tests.PropertyTests.collectTests,
      Tests.ProdCoverage.collectTests,
      Demo.collectTests
    ]
    let mut verifiedSuites : Array Tests.VerifiedSuiteResult := #[]
    for collect in collectors do
      let result ← collect
      let icon := if result.allPass then "✓" else "✗"
      IO.println s!"  {result.label}: {icon} {result.passed}/{result.total}"
      flushStdout
      dbg t0 s!"verified suite: {result.label} {result.passed}/{result.total}"
      verifiedSuites := verifiedSuites.push result
    let totalVPassed := verifiedSuites.foldl (fun acc s => acc + s.passed) 0
    let totalVTests := verifiedSuites.foldl (fun acc s => acc + s.total) 0
    IO.println s!"\nVerified: {totalVPassed}/{totalVTests}"
    flushStdout
    return verifiedSuites

  -- Shared helper: run all suite tests and collect results
  let runAllSuiteTests : IO (Array ReportResult) := do
    IO.println s!"Running all tests..."
    IO.println (String.ofList (List.replicate 60 '-'))
    flushStdout
    let results ← runAllForReport allCases .all (startMs := t0)
    IO.println (String.ofList (List.replicate 60 '-'))
    flushStdout
    dbg t0 "computing coverage stats"
    let stats := CoverageStats.fromResults results
    IO.println s!"\nCorrect: {stats.correctCount}/{stats.total} ({stats.successRate.floor}%)"
    flushStdout
    return results

  -- JSON-only mode: run all tests + verified suites, write JSON
  match jsonDir with
  | some dir =>
    let results ← runAllSuiteTests
    let verifiedSuites ← runVerifiedSuites
    dbg t0 "generating JSON"
    IO.println s!"\nGenerating JSON..."
    flushStdout
    writeJsonOnly results dir
      (verifiedSuites := some verifiedSuites)
      (snapshot := snapshot)
    dbg t0 "done"
    return 0
  | none => pure ()

  -- HTML report mode: run all tests and generate reports
  match htmlDir with
  | some dir =>
    let results ← runAllSuiteTests
    let verifiedSuites ← runVerifiedSuites

    dbg t0 "generating HTML reports"
    IO.println s!"\nGenerating HTML reports..."
    flushStdout
    writeReports results dir
      (verifiedSuites := some verifiedSuites)
    dbg t0 "done"
    return 0
  | none => pure ()

  -- Console mode: run the requested stage(s)
  if stage == .all then
    let mut totalStats : TestStats := {}
    for s in stages do
      if s != .error then  -- Skip error tests in "all" mode for now
        let stats ← runStage s allCases verbose
        totalStats := {
          total := totalStats.total + stats.total
          passed := totalStats.passed + stats.passed
          failed := totalStats.failed + stats.failed
          skipped := totalStats.skipped + stats.skipped
          failures := totalStats.failures ++ stats.failures
        }
    IO.println "══════════════════════════════════════════════════════════"
    IO.println s!"  TOTAL: {totalStats}"
    IO.println "══════════════════════════════════════════════════════════"
    return if totalStats.failed == 0 then 0 else 1
  else
    let stats ← runStage stage allCases verbose
    return if stats.failed == 0 then 0 else 1
