import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Document
import Tests.VerifiedResult

/-!
# Parser Integration Tests

Focused tests for each parser component, used to isolate infinite loops
and incorrect parse results during Phase 2 validation.
Produces a `VerifiedSuiteResult` for structured reporting.
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser
open Tests

namespace Tests.Parse

/-! ## Helpers -/

def runParser {α : Type} (p : YamlParser α) (input : String) : Except String α :=
  let stream := YamlStream.ofString input
  match Parser.run p stream with
  | .ok _ v => .ok v
  | .error _ err => .error (toString err)

def checkParser (state : IO.Ref TestCollector) (label : String)
    (p : YamlParser YamlValue) (input : String) : IO Unit := do
  match runParser p input with
  | .ok _ => check state label true
  | .error e => checkM state label false e

def checkParseYaml (state : IO.Ref TestCollector) (label : String)
    (input : String) : IO Unit := do
  match parseYaml input with
  | .ok _ => check state label true
  | .error e => checkM state label false e

def checkParseSingle (state : IO.Ref TestCollector) (label : String)
    (input : String) : IO Unit := do
  match parseYamlSingle input with
  | .ok _ => check state label true
  | .error e => checkM state label false e

/-! ## Tests -/

def testDoubleQuotedScalar (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Double-quoted scalars"
  checkParser state "simple" doubleQuotedScalar "\"hello\""
  checkParser state "with space" doubleQuotedScalar "\"hello world\""
  checkParser state "with escape" doubleQuotedScalar "\"hello\\nworld\""
  checkParser state "empty" doubleQuotedScalar "\"\""

def testSingleQuotedScalar (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Single-quoted scalars"
  checkParser state "simple" singleQuotedScalar "'hello'"
  checkParser state "with space" singleQuotedScalar "'hello world'"
  checkParser state "escaped quote" singleQuotedScalar "'it''s'"
  checkParser state "empty" singleQuotedScalar "''"

def testPlainScalar (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Plain scalars"
  checkParser state "word" (plainScalar (inFlow := false)) "hello"
  checkParser state "multi-word" (plainScalar (inFlow := false)) "hello world"

def testFlowSequence (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow sequences"
  checkParser state "simple" flowSequence "[a, b, c]"
  checkParser state "nested" flowSequence "[[1, 2], [3]]"
  checkParser state "empty" flowSequence "[]"

def testFlowMapping (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow mappings"
  checkParser state "simple" flowMapping "{a: 1, b: 2}"
  checkParser state "empty" flowMapping "{}"

def testBlockSequence (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Block sequences"
  checkParser state "simple" (blockSequence 0) "- a\n- b\n"
  checkParser state "items" (blockSequence 0) "- one\n- two\n- three\n"

def testBlockMapping (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Block mappings"
  checkParser state "simple" (blockMapping 0) "a: 1\nb: 2\n"

def testDocumentParsing (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Document parsing"
  checkParseYaml state "empty" ""
  checkParseSingle state "just scalar" "hello"
  checkParseYaml state "explicit doc" "---\nhello\n"
  checkParseYaml state "multi doc" "---\nfirst\n---\nsecond\n"

def testNestedBlock (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Nested block"
  checkParseSingle state "map with seq value" "items:\n  - a\n  - b\n"
  checkParseSingle state "nested map" "outer:\n  inner: value\n"
  checkParseSingle state "seq of maps" "- a: 1\n- b: 2\n"

/-- Collect all parser integration test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testDoubleQuotedScalar state
  testSingleQuotedScalar state
  testPlainScalar state
  testFlowSequence state
  testFlowMapping state
  testBlockSequence state
  testBlockMapping state
  testDocumentParsing state
  testNestedBlock state
  let results ← finish state
  return { name := "parsetest", label := "Parser Integration Tests", sourceFile := "Tests/ParseTest.lean", tests := results }

end Tests.Parse
