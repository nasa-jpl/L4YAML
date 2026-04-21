import L4YAML.Spec.Types
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Unit Tests

Basic unit tests for the verified YAML parser types and stream.
Produces a `VerifiedSuiteResult` for structured reporting.
-/

open L4YAML

namespace Tests

/-! ## Types tests -/

def testScalarStyles (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "ScalarStyle"
  let styles : List ScalarStyle :=
    [.plain, .singleQuoted, .doubleQuoted, .literal, .folded]
  check state "All 5 scalar styles defined" (styles.length == 5)
  check state "BEq distinguishes styles" (ScalarStyle.plain != ScalarStyle.literal)

def testYamlValueConstruction (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlValue construction"
  let s := YamlValue.scalar { content := "hello", style := .plain }
  match s with
  | .scalar sc => check state "Scalar content preserved" (sc.content == "hello")
  | _ => check state "Scalar content preserved" false

  let seq := YamlValue.sequence .block #[
    YamlValue.plainScalar "a",
    YamlValue.plainScalar "b"
  ]
  match seq with
  | .sequence _ items => check state "Sequence has 2 items" (items.size == 2)
  | _ => check state "Sequence has 2 items" false

  let m := YamlValue.mapping .block #[
    (YamlValue.plainScalar "key", YamlValue.plainScalar "val")
  ]
  match m with
  | .mapping _ pairs => check state "Mapping has 1 pair" (pairs.size == 1)
  | _ => check state "Mapping has 1 pair" false

  match YamlValue.null with
  | .null => check state "Null value constructed" true
  | _ => check state "Null value constructed" false

def testYamlDocument (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlDocument"
  let doc : YamlDocument := {
    value := YamlValue.plainScalar "test"
    directives := #[Directive.yaml "1.2"]
  }
  check state "Document has 1 directive" (doc.directives.size == 1)
  let dir0 := doc.directives[0]?
  match dir0 with
  | some (Directive.yaml ver) =>
    check state "YAML directive version correct" (ver == "1.2")
  | _ => check state "YAML directive version correct" false

def testYamlPos (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlPos"
  let p1 : YamlPos := { offset := 0, line := 0, col := 0 }
  let p2 : YamlPos := { offset := 5, line := 1, col := 2 }
  check state "YamlPos BEq reflexive" (p1 == p1)
  check state "YamlPos BEq distinguishes" (p1 != p2)

/-- Collect all unit test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testScalarStyles state
  testYamlValueConstruction state
  testYamlDocument state
  testYamlPos state
  let results ← finish state
  return { name := "tests", label := "Unit Tests", sourceFile := "Tests/Main.lean", tests := results }

end Tests
