import L4YAML
import Tests.SuiteRunner.Meta

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Error Stage Diagnostic

Small tests that replicate the yaml-test-suite error-stage pipeline end to end:

1. Read a real `.yaml` test file from the yaml-test-suite.
2. Parse it with `parseTestFile` (same as the suite runner).
3. Unescape with `unescapeTestYaml` (same as the suite runner).
4. Feed the result to `Parse.parseYaml`.
5. Check that the parser rejects the input (exit 1 in subprocess mode).

This catches two bug classes:
- **Pipeline bugs**: `parseTestFile` / `unescapeTestYaml` transforms the YAML
  incorrectly so the parser sees different input than expected.
- **Mapping bugs**: the suite runner's `runAllForReport` misclassifies the
  outcome (e.g., mapping `.pass` from `runTest` to `.unexpectedPass` instead
  of `.expectedFail`).

The five test IDs below are the error tests fixed by Step 10a validation
rules.  All five should be rejected by `Parse.parseYaml`.
-/

open L4YAML
open Tests.SuiteRunner

namespace Tests.ErrorStageDiag

/-- Load a yaml-test-suite file and extract the first test case's YAML. -/
def loadTestYaml (testId : String) : IO String := do
  let path := s!"yaml-test-suite/src/{testId}.yaml"
  let content ← IO.FS.readFile path
  let cases := parseTestFile testId content
  if h : cases.size > 0 then
    let tc := cases[0]
    let yaml := unescapeTestYaml tc.yaml
    return yaml
  else
    throw (IO.Error.userError s!"No test cases found in {path}")

/-- Expect `parseYaml` to reject the input. -/
def expectReject (label : String) (input : String) : IO Bool := do
  match TokenParser.parseYaml input with
  | .ok _ =>
    IO.println s!"  ✗ {label} — unexpectedly ACCEPTED"
    return false
  | .error _ =>
    IO.println s!"  ✓ {label} — correctly rejected"
    return true

/-- Run a single test: load from suite file, unescape, parse, expect rejection. -/
def runSuiteErrorTest (testId : String) (desc : String) : IO Bool := do
  let yaml ← loadTestYaml testId
  expectReject s!"{testId}: {desc}" yaml

/-- Also test with inline strings (same as ValidationTests / FlowRegressionCheck)
    to confirm the parser logic is correct independent of the suite file pipeline. -/
def runInlineErrorTest (testId : String) (desc : String) (input : String) :
    IO Bool :=
  expectReject s!"{testId} (inline): {desc}" input

def runTests : IO Unit := do
  IO.println "--- Error Stage Diagnostic ---"

  IO.println "\n  == Suite-file pipeline (parseTestFile → unescapeTestYaml → parseYaml) =="
  let mut suitePass : Nat := 0
  let mut suiteFail : Nat := 0

  let ids : Array (String × String) := #[
    ("CVW2", "Invalid comment after comma"),
    ("9JBA", "Invalid comment after end of flow sequence"),
    ("KS4U", "Invalid item after end of flow sequence"),
    ("DK4H", "Implicit key followed by newline"),
    ("ZXT5", "Implicit key followed by newline and adjacent value")
  ]

  for (testId, desc) in ids do
    if (← runSuiteErrorTest testId desc) then
      suitePass := suitePass + 1
    else
      suiteFail := suiteFail + 1

  IO.println s!"\n  Suite pipeline: {suitePass}/{suitePass + suiteFail} correctly rejected"

  IO.println "\n  == Inline strings (same as ValidationTests) =="
  let mut inlinePass : Nat := 0
  let mut inlineFail : Nat := 0

  let inlineTests : Array (String × String × String) := #[
    ("CVW2", "# without space after ,", "---\n[ a, b, c,#invalid\n]\n"),
    ("9JBA", "# without space after ]", "---\n[ a, b, c, ]#invalid\n"),
    ("KS4U", "content after closed flow", "---\n[\nsequence item\n]\ninvalid item\n"),
    ("DK4H", "key : on separate lines", "---\n[ key\n  : value ]\n"),
    ("ZXT5", "quoted key colon next line", "[ \"key\"\n  :value ]\n")
  ]

  for (testId, desc, input) in inlineTests do
    if (← runInlineErrorTest testId desc input) then
      inlinePass := inlinePass + 1
    else
      inlineFail := inlineFail + 1

  IO.println s!"\n  Inline: {inlinePass}/{inlinePass + inlineFail} correctly rejected"

  -- Compare: if suite pipeline accepts but inline rejects, it's a pipeline bug
  IO.println "\n  == Comparison =="
  for (testId, desc) in ids do
    let suiteYaml ← loadTestYaml testId
    -- Find the matching inline input
    let inlineInput := match testId with
      | "CVW2" => "---\n[ a, b, c,#invalid\n]\n"
      | "9JBA" => "---\n[ a, b, c, ]#invalid\n"
      | "KS4U" => "---\n[\nsequence item\n]\ninvalid item\n"
      | "DK4H" => "---\n[ key\n  : value ]\n"
      | "ZXT5" => "[ \"key\"\n  :value ]\n"
      | _ => ""
    if suiteYaml == inlineInput then
      IO.println s!"  = {testId}: suite YAML matches inline string"
    else
      IO.println s!"  ≠ {testId}: MISMATCH — suite-file vs inline differ!"
      IO.println s!"    suite  ({suiteYaml.length} chars): {repr suiteYaml}"
      IO.println s!"    inline ({inlineInput.length} chars): {repr inlineInput}"
    -- Also show first test case metadata
    let content ← IO.FS.readFile s!"yaml-test-suite/src/{testId}.yaml"
    let cases := parseTestFile testId content
    if h : cases.size > 0 then
      let tc := cases[0]
      IO.println s!"    expectFail={tc.expectFail}, tags={tc.tags}"

  IO.println ""

  let totalFail := suiteFail + inlineFail
  if totalFail > 0 then
    IO.println s!"  ⚠ {totalFail} test(s) unexpectedly accepted — investigation needed"
  else
    IO.println s!"  All tests correctly rejected in both pipelines."
    IO.println s!"  If HTML report still shows 0/74, the bug is in runAllForReport mapping."

end Tests.ErrorStageDiag

def main : IO Unit := Tests.ErrorStageDiag.runTests
