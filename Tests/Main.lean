import Lean4Yaml.Types
import Lean4Yaml.Stream

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Test Runner

Basic test runner for the verified YAML parser.
Tests are structured as simple assertions that print pass/fail.

Eventually, these will migrate to `#guard` statements and `theorem`s
in the Proofs module, but a runtime test suite is useful for rapid
iteration during development.
-/

open Lean4Yaml

namespace Tests

/-! ## Types tests -/

def testScalarStyles : IO Unit := do
  IO.println "--- ScalarStyle ---"
  let styles : List ScalarStyle :=
    [.plain, .singleQuoted, .doubleQuoted, .literal, .folded]
  if styles.length == 5 then
    IO.println "  ✓ All 5 scalar styles defined"
  else
    IO.println "  ✗ Expected 5 scalar styles"
  if ScalarStyle.plain != ScalarStyle.literal then
    IO.println "  ✓ BEq distinguishes styles"
  else
    IO.println "  ✗ BEq failed to distinguish"

def testYamlValueConstruction : IO Unit := do
  IO.println "--- YamlValue construction ---"
  let s := YamlValue.scalar { content := "hello", style := .plain }
  match s with
  | .scalar sc =>
    if sc.content == "hello" then
      IO.println "  ✓ Scalar content preserved"
    else
      IO.println "  ✗ Scalar content mismatch"
  | _ => IO.println "  ✗ Expected scalar"

  let seq := YamlValue.sequence .block #[
    YamlValue.plainScalar "a",
    YamlValue.plainScalar "b"
  ]
  match seq with
  | .sequence _ items =>
    if items.size == 2 then
      IO.println "  ✓ Sequence has 2 items"
    else
      IO.println s!"  ✗ Expected 2 items, got {items.size}"
  | _ => IO.println "  ✗ Expected sequence"

  let m := YamlValue.mapping .block #[
    (YamlValue.plainScalar "key", YamlValue.plainScalar "val")
  ]
  match m with
  | .mapping _ pairs =>
    if pairs.size == 1 then
      IO.println "  ✓ Mapping has 1 pair"
    else
      IO.println s!"  ✗ Expected 1 pair, got {pairs.size}"
  | _ => IO.println "  ✗ Expected mapping"

  match YamlValue.null with
  | .null => IO.println "  ✓ Null value constructed"
  | _ => IO.println "  ✗ Expected null"

def testYamlDocument : IO Unit := do
  IO.println "--- YamlDocument ---"
  let doc : YamlDocument := {
    value := YamlValue.plainScalar "test"
    directives := #[Directive.yaml "1.2"]
  }
  if doc.directives.size == 1 then
    IO.println "  ✓ Document has 1 directive"
  else
    IO.println "  ✗ Directive count mismatch"
  let dir0 := doc.directives[0]?
  match dir0 with
  | some (Directive.yaml ver) =>
    if ver == "1.2" then
      IO.println "  ✓ YAML directive version correct"
    else
      IO.println s!"  ✗ Expected version 1.2, got {ver}"
  | _ => IO.println "  ✗ Expected YAML directive"

/-! ## Stream tests -/

def testYamlStream : IO Unit := do
  IO.println "--- YamlStream ---"
  let stream := YamlStream.ofString "ab\ncd"

  -- Test initial state
  if stream.line == 0 && stream.col == 0 then
    IO.println "  ✓ Initial position (0,0)"
  else
    IO.println s!"  ✗ Expected (0,0), got ({stream.line},{stream.col})"

  -- Test next?
  match stream.next? with
  | some ('a', s1) =>
    IO.println "  ✓ First char is 'a'"
    if s1.col == 1 then
      IO.println "  ✓ Column advances to 1"
    else
      IO.println s!"  ✗ Expected col 1, got {s1.col}"
    match s1.next? with
    | some ('b', s2) =>
      match s2.next? with
      | some ('\n', s3) =>
        if s3.line == 1 && s3.col == 0 then
          IO.println "  ✓ Newline resets col to 0, increments line to 1"
        else
          IO.println s!"  ✗ After newline: expected (1,0), got ({s3.line},{s3.col})"
        match s3.next? with
        | some ('c', s4) =>
          if s4.line == 1 && s4.col == 1 then
            IO.println "  ✓ After 'c': position (1,1)"
          else
            IO.println s!"  ✗ Expected (1,1), got ({s4.line},{s4.col})"
        | _ => IO.println "  ✗ Expected 'c'"
      | _ => IO.println "  ✗ Expected newline"
    | _ => IO.println "  ✗ Expected 'b'"
  | _ => IO.println "  ✗ Expected 'a'"

  -- Test peek?
  match stream.peek? with
  | some 'a' => IO.println "  ✓ peek? returns 'a' without advancing"
  | _ => IO.println "  ✗ peek? failed"

  -- Test ofString on empty
  let empty := YamlStream.ofString ""
  if !empty.hasNext then
    IO.println "  ✓ Empty stream has no next"
  else
    IO.println "  ✗ Empty stream should have no next"

def testYamlPos : IO Unit := do
  IO.println "--- YamlPos ---"
  let p1 : YamlPos := { offset := 0, line := 0, col := 0 }
  let p2 : YamlPos := { offset := 5, line := 1, col := 2 }
  if p1 == p1 then
    IO.println "  ✓ YamlPos BEq reflexive"
  else
    IO.println "  ✗ YamlPos BEq failed"
  if p1 != p2 then
    IO.println "  ✓ YamlPos BEq distinguishes"
  else
    IO.println "  ✗ YamlPos BEq failed to distinguish"

def runTests : IO Unit := do
  IO.println "=== lean4-yaml-verified test suite ===\n"
  testScalarStyles
  testYamlValueConstruction
  testYamlDocument
  testYamlStream
  testYamlPos
  IO.println "\nAll tests complete."

end Tests

def main : IO Unit := Tests.runTests
