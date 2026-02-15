import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Document

/-!
# Parser Integration Tests

Focused tests for each parser component, used to isolate infinite loops
and incorrect parse results during Phase 2 validation.
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser

namespace Tests.Parse

/-! ## Helpers -/

def testParseYaml (label : String) (input : String) : IO Unit := do
  IO.print s!"  {label}: "
  match parseYaml input with
  | .ok docs => IO.println s!"OK ({docs.size} docs)"
  | .error e => IO.println s!"ERR: {e}"

def testParseSingle (label : String) (input : String) : IO Unit := do
  IO.print s!"  {label}: "
  match parseYamlSingle input with
  | .ok v => IO.println s!"OK → {repr v}"
  | .error e => IO.println s!"ERR: {e}"

/-! ## Individual parser tests via Parser.run -/

def runParser {α : Type} (p : YamlParser α) (input : String) : Except String α :=
  let stream := YamlStream.ofString input
  match Parser.run p stream with
  | .ok _ v => .ok v
  | .error _ err => .error (toString err)

def testScalarParser (label : String) (p : YamlParser YamlValue) (input : String) : IO Unit := do
  IO.print s!"  {label}: "
  match runParser p input with
  | .ok v => IO.println s!"OK → {repr v}"
  | .error e => IO.println s!"ERR: {e}"

/-! ## Tests -/

def testDoubleQuotedScalar : IO Unit := do
  IO.println "--- Double-quoted scalars ---"
  testScalarParser "simple" doubleQuotedScalar "\"hello\""
  testScalarParser "with space" doubleQuotedScalar "\"hello world\""
  testScalarParser "with escape" doubleQuotedScalar "\"hello\\nworld\""
  testScalarParser "empty" doubleQuotedScalar "\"\""

def testSingleQuotedScalar : IO Unit := do
  IO.println "--- Single-quoted scalars ---"
  testScalarParser "simple" singleQuotedScalar "'hello'"
  testScalarParser "with space" singleQuotedScalar "'hello world'"
  testScalarParser "escaped quote" singleQuotedScalar "'it''s'"
  testScalarParser "empty" singleQuotedScalar "''"

def testPlainScalar : IO Unit := do
  IO.println "--- Plain scalars ---"
  testScalarParser "word" (plainScalar (inFlow := false)) "hello"
  testScalarParser "multi-word" (plainScalar (inFlow := false)) "hello world"

def testFlowSequence : IO Unit := do
  IO.println "--- Flow sequences ---"
  testScalarParser "simple" flowSequence "[a, b, c]"
  testScalarParser "nested" flowSequence "[[1, 2], [3]]"
  testScalarParser "empty" flowSequence "[]"

def testFlowMapping : IO Unit := do
  IO.println "--- Flow mappings ---"
  testScalarParser "simple" flowMapping "{a: 1, b: 2}"
  testScalarParser "empty" flowMapping "{}"

def testBlockSequence : IO Unit := do
  IO.println "--- Block sequences ---"
  testScalarParser "simple" (blockSequence 0) "- a\n- b\n"
  testScalarParser "items" (blockSequence 0) "- one\n- two\n- three\n"

def testBlockMapping : IO Unit := do
  IO.println "--- Block mappings ---"
  testScalarParser "simple" (blockMapping 0) "a: 1\nb: 2\n"

def testDocumentParsing : IO Unit := do
  IO.println "--- Document parsing ---"
  testParseYaml "empty" ""
  testParseSingle "just scalar" "hello"
  testParseYaml "explicit doc" "---\nhello\n"
  testParseYaml "multi doc" "---\nfirst\n---\nsecond\n"

def testNestedBlock : IO Unit := do
  IO.println "--- Nested block ---"
  testParseSingle "map with seq value" "items:\n  - a\n  - b\n"
  testParseSingle "nested map" "outer:\n  inner: value\n"
  testParseSingle "seq of maps" "- a: 1\n- b: 2\n"

end Tests.Parse

def main : IO Unit := do
  IO.println "=== Parser Integration Tests ===\n"
  Tests.Parse.testDoubleQuotedScalar
  IO.println ""
  Tests.Parse.testSingleQuotedScalar
  IO.println ""
  Tests.Parse.testPlainScalar
  IO.println ""
  Tests.Parse.testFlowSequence
  IO.println ""
  Tests.Parse.testFlowMapping
  IO.println ""
  Tests.Parse.testBlockSequence
  IO.println ""
  Tests.Parse.testBlockMapping
  IO.println ""
  Tests.Parse.testDocumentParsing
  IO.println ""
  Tests.Parse.testNestedBlock
  IO.println "\n=== Done ==="
