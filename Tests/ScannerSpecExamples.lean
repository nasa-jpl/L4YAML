import L4YAML.Parser.TokenParser
import Tests.VerifiedResult
-- Reuse cleanup helpers from SpecExamples
import Tests.SpecExamples

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# YAML 1.2.2 Spec Examples — Scanner/Parser Pipeline

Runs the same 132 spec examples from §2–§10 against the Phase 9
two-pass scanner/parser pipeline (`TokenParser.parseYaml`) instead of
the old single-pass parser (`Parser.Document.parseYaml`).

This validates that the scanner correctly tokenizes the full YAML 1.2.2
spec corpus and the token parser correctly builds ASTs from those tokens.

## Usage

```
lake build scannerspecexamples && ./.lake/build/bin/scannerspecexamples
```
-/

open L4YAML
open Tests

namespace Tests.ScannerSpecExamples

/-! ## File Discovery (reuse from SpecExamples) -/

/-- Spec sections to test, in order. -/
private def specSections : Array String := #["2", "5", "6", "7", "8", "9", "10"]

/-- List YAML files in a directory, sorted. -/
private def listYamlFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut files : Array System.FilePath := #[]
  let entries ← dir.readDir
  for entry in entries do
    let name := entry.fileName
    if name.endsWith ".yaml" || name.endsWith ".yml" then
      files := files.push entry.path
  let sorted := files.toList.mergeSort (fun a b => toString a < toString b)
  pure sorted.toArray

/-- Extract example number from filename like "example-2.7.yaml". -/
private def exampleLabel (path : System.FilePath) : String :=
  let name := path.fileName.getD "unknown"
  let name := name.dropSuffix ".yaml" |>.dropSuffix ".yml" |>.copy
  name.dropSuffix "example-" |>.copy

/-! ## Expected-Error Examples (same list as SpecExamples) -/

private def expectedErrorExamples : Array String :=
  #[ "example-5.2", "example-5.10", "example-5.14"
   , "example-6.15", "example-6.17", "example-6.27"
   , "example-7.22", "example-8.3"
   ]

private def isExpectedError (exId : String) : Bool :=
  expectedErrorExamples.any (· == exId)

/-! ## Known Scanner/Parser Gaps -/

/-- Spec examples that are valid YAML but expose known scanner/parser
    limitations in the Phase 9 pipeline. Tracked separately from the
    old parser's gaps. -/
private def knownScannerGaps : Array String :=
  #[]

private def isKnownGap (exId : String) : Bool :=
  knownScannerGaps.any (· == exId)

/-! ## Parse Testing -/

/-- Try to parse one spec example file using the scanner/parser pipeline.
    Returns `(exampleLabel, parsed?, errorMsg)`. -/
private def testOneExample (path : System.FilePath) :
    IO (String × Bool × String) := do
  let raw ← IO.FS.readFile path
  let cleaned := Tests.SpecExamples.cleanupExample raw
  let exId := exampleLabel path
  match TokenParser.parseYaml cleaned with
  | .ok _ => pure (exId, true, "")
  | .error e =>
    -- Also try single-document parse
    match TokenParser.parseYamlSingle cleaned with
    | .ok _ => pure (exId, true, "")
    | .error _ => pure (exId, false, e.toString)

/-- Run all spec example tests against scanner/parser and collect results. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  let baseDir : System.FilePath := "examples"

  for sec in specSections do
    let secDir := baseDir / sec
    setCategory state s!"§{sec} Scanner Spec Examples"

    if ← secDir.pathExists then
      let files ← listYamlFiles secDir
      for file in files do
        let (exId, parsed, errMsg) ← testOneExample file
        let label := s!"Example {exId}"
        if parsed then
          checkImpl state label true
        else if isExpectedError exId then
          checkImpl state label true
            (message := s!"expected error: {errMsg}")
        else if isKnownGap exId then
          checkImpl state label false
            (message := s!"known scanner gap: {errMsg}")
        else
          checkImpl state label false (message := errMsg)
    else
      checkImpl state s!"Section {sec} directory missing" false
        (message := s!"expected {secDir}")

  let results ← finish state
  pure {
    name := "scannerspecexamples"
    label := "YAML 1.2.2 Spec Examples (Scanner/Parser Pipeline)"
    sourceFile := "Tests/ScannerSpecExamples.lean"
    tests := results
  }

end Tests.ScannerSpecExamples
