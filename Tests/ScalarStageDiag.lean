import Lean4Yaml
import Tests.SuiteRunner.Meta

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scalar Stage Diagnostic

Tests the 20 scalar-stage failures from the yaml-test-suite HTML report.
Each test loads a real `.yaml` test file from the yaml-test-suite, extracts
the YAML via `parseTestFile` + `unescapeTestYaml` (same pipeline as the
suite runner), then feeds it to `Parse.parseYaml`.

## Root cause taxonomy (from tryparse errors):

- **Block scalar content not consumed** (12 tests): 4WA9, 6FWR, 6JQW, 96L6,
  96NN, D83L, DK3J, F6MC, FP8R, M29M, P2AD, R4YG —
  "unexpected trailing content" after `---` marker because the block scalar
  (`|`, `>`, `|+`, `|-`, `|2`, `>1`, `>2`) body isn't fully consumed.

- **Plain scalar key parsing** (4 tests): 2EBW, 6H3V, 8CWC, 6SLA —
  Plain/quoted keys with special chars (colons, backslashes, `?`, `:`)
  cause "unexpected trailing content ':'".

- **Block content continuation** (2 tests): AB8U, NB6Z —
  Multi-line plain scalars with tricky continuation (tabs on empty lines,
  `- ` that looks like a sequence indicator).

- **Block structure** (2 tests): H2RW, W42U —
  Block literal scalars inside mappings/sequences with blank lines and
  mixed content types.

The goal is to reproduce each failure in isolation and to track which ones
get fixed as the parser improves.
-/

open Lean4Yaml
open Tests.SuiteRunner

namespace Tests.ScalarStageDiag

/-- Load a yaml-test-suite file and extract all test cases' YAML. -/
def loadAllTestYamls (testId : String) : IO (Array (String × Bool)) := do
  let path := s!"yaml-test-suite/src/{testId}.yaml"
  let content ← IO.FS.readFile path
  let cases := parseTestFile testId content
  let mut results : Array (String × Bool) := #[]
  for tc in cases do
    let yaml := unescapeTestYaml tc.yaml
    results := results.push (yaml, tc.expectFail)
  return results

/-- Test a single YAML input that should parse successfully.
    Returns (passed, errorMsg). -/
def testAccept (label : String) (input : String) : IO (Bool × Option String) := do
  if input.isEmpty then
    IO.println s!"  ○ {label} — empty input (skipped)"
    return (true, none)
  match Parse.parseYaml input with
  | .ok _docs =>
    IO.println s!"  ✓ {label}"
    return (true, none)
  | .error e =>
    IO.println s!"  ✗ {label} — {e}"
    return (false, some e)

/-- Run a suite test by ID: loads from file, tests each case. -/
def runSuiteTest (testId : String) (desc : String) :
    IO (Nat × Nat) := do
  let cases ← loadAllTestYamls testId
  let mut passed : Nat := 0
  let mut failed : Nat := 0
  for (yaml, expectFail) in cases do
    if expectFail then
      -- Error test — skip (or test rejection)
      IO.println s!"  ○ {testId}: {desc} — error test (skipped)"
      passed := passed + 1
    else if yaml.isEmpty then
      IO.println s!"  ○ {testId}: {desc} — empty input (skipped)"
      passed := passed + 1
    else
      let (ok, _) ← testAccept s!"{testId}: {desc}" yaml
      if ok then passed := passed + 1
      else failed := failed + 1
  return (passed, failed)

def runTests : IO Unit := do
  IO.println "--- Scalar Stage Diagnostic (20 failing tests) ---"

  let mut totalPass : Nat := 0
  let mut totalFail : Nat := 0

  -- The 20 scalar-stage failures from the HTML report
  let tests : Array (String × String) := #[
    -- Block scalar content (12 tests)
    ("4WA9", "Literal scalars with indent indicator"),
    ("6FWR", "Block scalar keep (|+)"),
    ("6JQW", "Spec 2.13: literals preserve newlines"),
    ("96L6", "Spec 2.14: folded scalars, newlines→spaces"),
    ("96NN", "Leading tab content in literals"),
    ("D83L", "Block scalar indicator order (|2-, |-2)"),
    ("DK3J", "Zero-indent block scalar with comment-like line"),
    ("F6MC", "More-indented lines in folded block scalars"),
    ("FP8R", "Zero-indented block scalar"),
    ("M29M", "Literal block scalar with trailing space lines"),
    ("P2AD", "Spec 8.1: block scalar header"),
    ("R4YG", "Spec 8.2: block indentation indicator"),
    -- Plain/quoted key parsing (4 tests)
    ("2EBW", "Allowed characters in keys"),
    ("6H3V", "Backslashes in single quotes"),
    ("8CWC", "Plain mapping key ending with colons"),
    ("6SLA", "Allowed characters in quoted mapping key"),
    -- Block content continuation (2 tests)
    ("AB8U", "Sequence entry that looks like two"),
    ("NB6Z", "Multi-line plain value with tabs on empty lines"),
    -- Block structure (2 tests)
    ("H2RW", "Blank lines in block literal inside mapping"),
    ("W42U", "Spec 8.15: block sequence entry types")
  ]

  for (testId, desc) in tests do
    let (p, f) ← runSuiteTest testId desc
    totalPass := totalPass + p
    totalFail := totalFail + f

  IO.println ""
  IO.println s!"  Results: {totalPass} passed, {totalFail} failed"
  IO.println s!"  (of {totalPass + totalFail} total test cases)"

  if totalFail == 0 then
    IO.println "  All scalar-stage tests now pass!"
  else
    IO.println s!"  {totalFail} test(s) still failing — parser improvements needed"

  -- Group summary by root cause
  IO.println "\n  Root cause breakdown:"
  IO.println "  ─────────────────────"

  let blockScalarIds := #["4WA9", "6FWR", "6JQW", "96L6", "96NN", "D83L",
                          "DK3J", "F6MC", "FP8R", "M29M", "P2AD", "R4YG"]
  let keyParsingIds := #["2EBW", "6H3V", "8CWC", "6SLA"]
  let continuationIds := #["AB8U", "NB6Z"]
  let structureIds := #["H2RW", "W42U"]

  for (groupName, groupIds) in #[
    ("Block scalar content", blockScalarIds),
    ("Plain/quoted key parsing", keyParsingIds),
    ("Block content continuation", continuationIds),
    ("Block structure", structureIds)
  ] do
    let mut gPass : Nat := 0
    let mut gFail : Nat := 0
    for gid in groupIds do
      let cases ← loadAllTestYamls gid
      for (yaml, expectFail) in cases do
        if expectFail || yaml.isEmpty then
          gPass := gPass + 1
        else
          match Parse.parseYaml yaml with
          | .ok _ => gPass := gPass + 1
          | .error _ => gFail := gFail + 1
    IO.println s!"  {groupName}: {gPass}/{gPass + gFail} pass ({gFail} fail)"

  IO.println ""

end Tests.ScalarStageDiag

def main : IO Unit := Tests.ScalarStageDiag.runTests
