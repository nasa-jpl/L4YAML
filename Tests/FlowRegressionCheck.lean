import Lean4Yaml

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Flow Regression Check

Diagnostic tests to verify that flow stage yaml-test-suite cases that
previously passed still parse correctly after Step 10a validation changes.

These inputs come from the yaml-test-suite `--stage flow` failures observed
after adding flow structure error validation (§10 in ValidationTests).
The goal is to distinguish pre-existing failures from regressions.

**Result**: baseline (`git stash`) shows 74 pass / 26 fail, same as after
changes.  87E4 and 2EBW were pre-existing failures.  Error stage improved
44→52/74 (+8) with zero flow-stage regressions.
-/

open Lean4Yaml

namespace Tests.FlowRegressionCheck

/-- Test a YAML input that should parse successfully. -/
def expectAccept (label : String) (input : String) : IO Unit := do
  match Parse.parseYaml input with
  | .ok _ => IO.println s!"  ✓ accept: {label}"
  | .error e => IO.println s!"  ✗ accept: {label} — {e}"

/-- Test a YAML input that should be rejected. -/
def expectReject (label : String) (input : String) : IO Unit := do
  match Parse.parseYaml input with
  | .ok _ => IO.println s!"  ✗ reject: {label} — unexpectedly accepted"
  | .error _ => IO.println s!"  ✓ reject: {label}"

def runTests : IO Unit := do
  IO.println "--- Flow Regression Check ---"

  -- 87E4: Spec Example 7.8 — Single Quoted Implicit Keys
  -- Input: 'implicit block key' : [\n  'implicit flow key' : value,\n ]
  expectAccept "87E4: single-quoted implicit keys"
    "'implicit block key' : [\n  'implicit flow key' : value,\n ]\n"

  -- 2EBW: Allowed characters in keys (scalar stage, included in flow)
  expectAccept "2EBW: allowed chars in keys"
    "a!\"#$%&'()*+,-./09:;<=>?@AZ[\\]^_`az{|}~: safe\n?foo: safe question mark\n:foo: safe colon\n-foo: safe dash\nthis is#not: a comment\n"

  -- LQZ7: Spec Example 7.15 — Flow Mappings
  expectAccept "LQZ7: flow mapping in block"
    "- { y: z }\n- {\n  }\n"

  -- 96NN: Tab-indented top-level flow
  expectAccept "96NN: block mapping multi-value"
    "a: b\nc: d\n"

  -- F6MC: Flow sequence with nested mappings
  expectAccept "F6MC: more indented mapping"
    "a:\n  b: c\n  d: e\nf: g\n"

  -- H2RW: multi-document
  expectAccept "H2RW: multi-doc with ---"
    "---\nfoo\n---\nbar\n"

  -- KS4U: content after closed flow is rejected
  expectReject "KS4U: invalid item after flow seq"
    "---\n[\nsequence item\n]\ninvalid item\n"

  -- 9JBA: comment without space after ]
  expectReject "9JBA: # without space after ]"
    "---\n[ a, b, c, ]#invalid\n"

  -- CVW2: comment without space after ,
  expectReject "CVW2: # without space after ,"
    "---\n[ a, b, c,#invalid\n]\n"

  -- DK4H: implicit key colon on next line
  expectReject "DK4H: key : on separate lines"
    "---\n[ key\n  : value ]\n"

  -- ZXT5: quoted key + :value on next line
  expectReject "ZXT5: quoted key colon next line"
    "[ \"key\"\n  :value ]\n"

  IO.println ""

end Tests.FlowRegressionCheck

def main : IO Unit := Tests.FlowRegressionCheck.runTests
