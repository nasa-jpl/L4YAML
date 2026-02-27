import Lean4Yaml
import Lean4Yaml.TokenParser
import Tests.SuiteRunner.Meta

/-!
# Parser Comparison Tool (P10.1)

Runs both the old parser (`Parse.parseYaml`) and the new tokenized parser
(`TokenParser.parseYaml`) on the yaml-test-suite corpus and reports
behavioral differences.

## Purpose

Phase 10 requires the tokenized parser to be a drop-in replacement for
the old parser. This tool validates that both parsers produce identical
results (success/failure) and, where both succeed, identical `YamlValue`
output.

## Usage

```
lake build parsercompare && .lake/build/bin/parsercompare [--verbose]
```
-/

open Lean4Yaml
open Tests.SuiteRunner

/-- Comparison outcome for a single test. -/
inductive CompareResult where
  | bothOk (contentEq : Bool)
      (oldRepr : String) (newRepr : String)
  | bothFail
  | oldOkNewFail (newErr : String)
  | oldFailNewOk (oldErr : String)
  | skipped (reason : String)

/-- Simple structural equality for YamlDocument arrays.
    We compare the `Repr` output to avoid needing `DecidableEq` for
    the complex nested types with arrays. -/
private def docsEqual (a b : Array YamlDocument) : Bool :=
  toString (repr a) == toString (repr b)

/-- Run both parsers on a single input and compare results. -/
def compareOne (yaml : String) : CompareResult :=
  let oldResult := Parse.parseYaml yaml
  let newResult := TokenParser.parseYaml yaml
  match oldResult, newResult with
  | .ok oldDocs, .ok newDocs =>
    let oldR := toString (repr oldDocs)
    let newR := toString (repr newDocs)
    .bothOk (oldR == newR) oldR newR
  | .error _, .error _ => .bothFail
  | .ok _, .error e => .oldOkNewFail e
  | .error e, .ok _ => .oldFailNewOk e

def main (args : List String) : IO UInt32 := do
  let verbose := args.any (fun a => a == "--verbose" || a == "-v")

  -- Read yaml-test-suite files (inline logic from SuiteRunner)
  let srcDir : System.FilePath := "yaml-test-suite" / "src"
  if !(← srcDir.pathExists) then
    IO.eprintln s!"yaml-test-suite/src directory not found (expected at {srcDir})"
    return 1

  let entries ← srcDir.readDir
  let mut files : Array (String × String) := #[]
  for entry in entries do
    let path := entry.path
    if path.extension == some "yaml" then
      let content ← IO.FS.readFile path
      let testId := path.fileStem.getD "unknown"
      files := files.push (testId, content)
  let sortedFiles := files.insertionSort (fun a b => a.1 < b.1)
  IO.println s!"Read {sortedFiles.size} test files from yaml-test-suite/src/"

  -- Parse all test files into test cases
  let mut allCases : Array TestCase := #[]
  for pair in sortedFiles do
    let cases := parseTestFile pair.1 pair.2
    allCases := allCases ++ cases

  IO.println s!"Parsed {allCases.size} test cases"

  let mut totalTests : Nat := 0
  let mut bothOkMatch : Nat := 0
  let mut bothOkDiffer : Nat := 0
  let mut bothFail : Nat := 0
  let mut oldOkNewFail : Nat := 0
  let mut oldFailNewOk : Nat := 0
  let mut skipped : Nat := 0
  let mut differences : Array String := #[]
  let mut diffSamples : Array (String × String × String) := #[]  -- (label, old, new)

  for tc in allCases do
    let yaml := unescapeTestYaml tc.yaml

    -- Skip empty, YAML 1.3 specific, and error tests
    if yaml.isEmpty then
      skipped := skipped + 1
      continue
    if tc.tags.any (fun t => t == "1.3-err" || t == "1.3-mod") then
      skipped := skipped + 1
      continue

    totalTests := totalTests + 1

    let label := if tc.variant > 0 then s!"{tc.id}[{tc.variant}]" else tc.id

    match compareOne yaml with
    | .bothOk true _ _ =>
      bothOkMatch := bothOkMatch + 1
      if verbose then IO.println s!"  ✓ {label}"
    | .bothOk false oldR newR =>
      bothOkDiffer := bothOkDiffer + 1
      differences := differences.push s!"CONTENT DIFFERS: {label}"
      if diffSamples.size < 3 then
        diffSamples := diffSamples.push (label, oldR, newR)
      IO.println s!"  ≠ {label} — content differs"
    | .bothFail =>
      bothFail := bothFail + 1
      if verbose then IO.println s!"  ✗✗ {label} — both fail"
    | .oldOkNewFail e =>
      oldOkNewFail := oldOkNewFail + 1
      differences := differences.push s!"OLD OK, NEW FAIL: {label} — {e}"
      IO.println s!"  ⚠ {label} — OLD OK, NEW FAIL: {e}"
    | .oldFailNewOk e =>
      oldFailNewOk := oldFailNewOk + 1
      differences := differences.push s!"OLD FAIL, NEW OK: {label} — {e}"
      if verbose then IO.println s!"  ◉ {label} — OLD FAIL, NEW OK: {e}"
    | .skipped reason =>
      skipped := skipped + 1
      if verbose then IO.println s!"  ○ {label} — {reason}"

  let bothOk := bothOkMatch + bothOkDiffer

  IO.println ""
  IO.println "╔══════════════════════════════════════════════════════════╗"
  IO.println "║         Parser Comparison: Old vs Tokenized             ║"
  IO.println "╠══════════════════════════════════════════════════════════╣"
  IO.println s!"║  Total tests:          {totalTests}"
  IO.println s!"║  Both OK (match):      {bothOkMatch}"
  IO.println s!"║  Both OK (differ):     {bothOkDiffer}"
  IO.println s!"║  Both FAIL:            {bothFail}"
  IO.println s!"║  OLD OK, NEW FAIL:     {oldOkNewFail}"
  IO.println s!"║  OLD FAIL, NEW OK:     {oldFailNewOk}"
  IO.println s!"║  Skipped:              {skipped}"
  IO.println s!"║  Both OK total:        {bothOk}"
  IO.println "╚══════════════════════════════════════════════════════════╝"

  if differences.size > 0 then
    IO.println ""
    IO.println s!"══ {differences.size} differences ══"

  -- Show detailed diff samples
  if diffSamples.size > 0 then
    IO.println ""
    IO.println s!"══ First {diffSamples.size} content diff samples ══"
    for sample in diffSamples do
      let label := sample.1
      let oldR := sample.2.1
      let newR := sample.2.2
      IO.println s!"\n── {label} ──"
      IO.println s!"OLD: {oldR.take 2000}"
      IO.println s!"NEW: {newR.take 2000}"

  if oldOkNewFail > 0 then
    IO.println ""
    IO.println "⚠ NEW PARSER REGRESSIONS DETECTED"
    return 1

  if bothOkDiffer > 0 then
    IO.println ""
    IO.println "⚠ CONTENT DIFFERENCES DETECTED (both parsers succeed but produce different ASTs)"
    return 1

  IO.println ""
  IO.println "✓ No regressions. Tokenized parser is a safe replacement."
  return 0
