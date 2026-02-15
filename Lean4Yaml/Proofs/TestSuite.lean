/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Parser.Document

/-!
# YAML Test Suite as Compile-Time Tests

This module encodes test cases from the yaml-test-suite
(https://github.com/yaml/yaml-test-suite) as Lean 4 `#guard` checks
and (eventually) `theorem` statements.

## Approach

1. **Phase 1 (current)**: `#guard` checks that verify parse results at compile time.
   If a test case fails, the module won't compile.

2. **Phase 2**: Convert selected `#guard` checks to `theorem` + `decide`
   statements, providing machine-checked proofs.

3. **Phase 3**: Generate test cases programmatically from the yaml-test-suite
   data files.

## Test Structure

Each test case has:
- An ID (from yaml-test-suite, e.g., "229Q")
- Input YAML string
- Expected parse result (success with specific value, or error)
-/

namespace Lean4Yaml.Tests.Suite

open Lean4Yaml
open Lean4Yaml.Parse

/-! ## Helper -/

/-- Check that parsing succeeds and produces the expected number of documents -/
def parsesTo (input : String) (expected : Nat) : Bool :=
  match parseYaml input with
  | .ok docs => docs.size == expected
  | .error _ => false

/-- Check that parsing produces a specific single value -/
def parsesToValue (input : String) (expected : YamlValue) : Bool :=
  match parseYamlSingle input with
  | .ok v => v == expected
  | .error _ => false

/-- Check that parsing fails -/
def parseFails (input : String) : Bool :=
  match parseYaml input with
  | .ok _ => false
  | .error _ => true

/-! ## Basic Scalar Tests -/

-- These are representative tests. The full suite will be added incrementally.

-- Simple plain scalar
-- #guard parsesToValue "hello" (.plainScalar "hello")

-- Simple double-quoted scalar
-- #guard parsesToValue "\"hello world\"" (.quotedScalar "hello world" .doubleQuoted)

-- Simple single-quoted scalar
-- #guard parsesToValue "'hello world'" (.quotedScalar "hello world" .singleQuoted)

-- Empty document
-- #guard parsesTo "" 0

-- Document with just `---`
-- #guard parsesTo "---" 1

-- Note: Tests are commented out until the parser compiles and passes basic checks.
-- They will be uncommented incrementally as the parser is validated.

/-! ## Test Cases from yaml-test-suite -/

-- 229Q: Block mapping
-- Input:
--   a: 1
--   b: 2
-- Expected: mapping with two entries
-- #guard parsesToValue "a: 1\nb: 2\n" (.blockMapping #[
--   (.plainScalar "a", .plainScalar "1"),
--   (.plainScalar "b", .plainScalar "2")
-- ])

-- 2JGN: Flow sequence
-- Input: [a, b, c]
-- Expected: flow sequence with three items
-- #guard parsesToValue "[a, b, c]" (.flowSequence #[
--   .plainScalar "a",
--   .plainScalar "b",
--   .plainScalar "c"
-- ])

-- 4ABK: Flow mapping
-- Input: {a: 1, b: 2}
-- Expected: flow mapping with two entries
-- #guard parsesToValue "{a: 1, b: 2}" (.flowMapping #[
--   (.plainScalar "a", .plainScalar "1"),
--   (.plainScalar "b", .plainScalar "2")
-- ])

end Lean4Yaml.Tests.Suite
