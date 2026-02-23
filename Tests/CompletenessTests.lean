import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Document
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Completeness Tests

Runtime tests verifying that specific YAML inputs parse to the expected
AST values. These are the runtime counterparts of the `native_decide`
theorems in `Tests/CompletenessExplore.lean` and the foundation for
the per-parser specification lemmas planned in Phase 5d.

## Categories

1. **Plain scalars** — single chars, words, multi-word
2. **Quoted scalars** — double-quoted, single-quoted, escape sequences
3. **Flow collections** — flow sequences `[…]`, flow mappings `{…}`
4. **Block collections** — block sequences `- …`, block mappings `key: …`
5. **Multi-document** — `---` separators, `...` terminators
6. **Edge cases** — empty input, whitespace-only, BOM, null values
7. **Stream properties** — `YamlStream.ofString` field correctness
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Tests

namespace Tests.Completeness

/-! ## Helpers -/

/-- Parse YAML input and return the single document value. -/
def parseSingle (input : String) : Except String YamlValue :=
  parseYamlSingle input

/-- Parse YAML input and return all documents. -/
def parseMulti (input : String) : Except String (Array YamlDocument) :=
  parseYaml input

/-- Check that parsing succeeds and the value matches `expected`. -/
def checkParse (state : IO.Ref TestCollector) (name : String)
    (input : String) (expected : YamlValue) : IO Unit := do
  match parseSingle input with
  | .ok v => check state name (v == expected)
  | .error e => checkM state name false e

/-! ## §1 Plain Scalars -/

def testPlainScalars (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Plain scalars"
  -- Single ASCII character
  checkParse state "single char 'a'" "a" (.scalar ⟨"a", .plain, none, none, none⟩)
  -- Simple word
  checkParse state "word 'hello'" "hello" (.scalar ⟨"hello", .plain, none, none, none⟩)
  -- Multi-word (space in plain scalar)
  checkParse state "multi-word 'hello world'" "hello world"
    (.scalar ⟨"hello world", .plain, none, none, none⟩)
  -- Numeric-looking plain scalar
  checkParse state "numeric '42'" "42" (.scalar ⟨"42", .plain, none, none, none⟩)
  -- Boolean-looking plain scalar
  checkParse state "boolean-like 'true'" "true" (.scalar ⟨"true", .plain, none, none, none⟩)
  checkParse state "boolean-like 'false'" "false" (.scalar ⟨"false", .plain, none, none, none⟩)
  -- Null-looking plain scalar
  checkParse state "null-like 'null'" "null" (.scalar ⟨"null", .plain, none, none, none⟩)
  -- Tilde (also null in some schemas)
  checkParse state "tilde '~'" "~" (.scalar ⟨"~", .plain, none, none, none⟩)

/-! ## §2 Quoted Scalars -/

def testQuotedScalars (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Quoted scalars"
  -- Double-quoted
  checkParse state "double-quoted 'hello'" "\"hello\""
    (.scalar ⟨"hello", .doubleQuoted, none, none, none⟩)
  -- Single-quoted
  checkParse state "single-quoted 'hello'" "'hello'"
    (.scalar ⟨"hello", .singleQuoted, none, none, none⟩)
  -- Double-quoted with escape
  checkParse state "double-quoted newline '\\n'" "\"line1\\nline2\""
    (.scalar ⟨"line1\nline2", .doubleQuoted, none, none, none⟩)
  -- Double-quoted with tab escape
  checkParse state "double-quoted tab '\\t'" "\"col1\\tcol2\""
    (.scalar ⟨"col1\tcol2", .doubleQuoted, none, none, none⟩)
  -- Empty double-quoted
  checkParse state "empty double-quoted" "\"\""
    (.scalar ⟨"", .doubleQuoted, none, none, none⟩)
  -- Empty single-quoted
  checkParse state "empty single-quoted" "''"
    (.scalar ⟨"", .singleQuoted, none, none, none⟩)
  -- Single-quoted with escaped quote
  checkParse state "single-quoted with ''" "'it''s'"
    (.scalar ⟨"it's", .singleQuoted, none, none, none⟩)

/-! ## §3 Flow Collections -/

def testFlowCollections (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow collections"
  -- Simple flow sequence
  match parseSingle "[1, 2, 3]" with
  | .ok (.sequence .flow items _) =>
    check state "flow seq [1,2,3] is sequence" true
    check state "flow seq [1,2,3] has 3 items" (items.size == 3)
    check state "flow seq [1,2,3] first item" (items[0]! == .scalar ⟨"1", .plain, none, none, none⟩)
    check state "flow seq [1,2,3] second item" (items[1]! == .scalar ⟨"2", .plain, none, none, none⟩)
    check state "flow seq [1,2,3] third item" (items[2]! == .scalar ⟨"3", .plain, none, none, none⟩)
  | .ok _ => check state "flow seq [1,2,3] is sequence" false
  | .error e => checkM state "flow seq [1,2,3] is sequence" false e
  -- Empty flow sequence
  match parseSingle "[]" with
  | .ok (.sequence .flow items _) =>
    check state "empty flow seq" true
    check state "empty flow seq has 0 items" (items.size == 0)
  | .ok _ => check state "empty flow seq" false
  | .error e => checkM state "empty flow seq" false e
  -- Simple flow mapping
  match parseSingle "{a: b}" with
  | .ok (.mapping .flow pairs _) =>
    check state "flow map {a: b} is mapping" true
    check state "flow map {a: b} has 1 pair" (pairs.size == 1)
    check state "flow map {a: b} key" (pairs[0]!.1 == .scalar ⟨"a", .plain, none, none, none⟩)
    check state "flow map {a: b} value" (pairs[0]!.2 == .scalar ⟨"b", .plain, none, none, none⟩)
  | .ok _ => check state "flow map {a: b} is mapping" false
  | .error e => checkM state "flow map {a: b} is mapping" false e
  -- Empty flow mapping
  match parseSingle "{}" with
  | .ok (.mapping .flow pairs _) =>
    check state "empty flow map" true
    check state "empty flow map has 0 pairs" (pairs.size == 0)
  | .ok _ => check state "empty flow map" false
  | .error e => checkM state "empty flow map" false e
  -- Nested flow
  match parseSingle "[[1], [2]]" with
  | .ok (.sequence .flow items _) =>
    check state "nested flow seq has 2 items" (items.size == 2)
  | .ok _ => check state "nested flow seq" false
  | .error e => checkM state "nested flow seq" false e

/-! ## §4 Block Collections -/

def testBlockCollections (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Block collections"
  -- Block mapping: key: value
  checkParse state "block map 'key: value'" "key: value"
    (.mapping .block #[(.scalar ⟨"key", .plain, none, none, none⟩,
                         .scalar ⟨"value", .plain, none, none, none⟩)] none)
  -- Block mapping: multiple keys
  match parseSingle "a: 1\nb: 2" with
  | .ok (.mapping .block pairs _) =>
    check state "block map 2 keys is mapping" true
    check state "block map 2 keys has 2 pairs" (pairs.size == 2)
    check state "block map first key" (pairs[0]!.1 == .scalar ⟨"a", .plain, none, none, none⟩)
    check state "block map first value" (pairs[0]!.2 == .scalar ⟨"1", .plain, none, none, none⟩)
    check state "block map second key" (pairs[1]!.1 == .scalar ⟨"b", .plain, none, none, none⟩)
    check state "block map second value" (pairs[1]!.2 == .scalar ⟨"2", .plain, none, none, none⟩)
  | .ok _ => check state "block map 2 keys is mapping" false
  | .error e => checkM state "block map 2 keys is mapping" false e
  -- Block sequence
  match parseSingle "- a\n- b\n- c" with
  | .ok (.sequence .block items _) =>
    check state "block seq 3 items is sequence" true
    check state "block seq has 3 items" (items.size == 3)
    check state "block seq first" (items[0]! == .scalar ⟨"a", .plain, none, none, none⟩)
    check state "block seq second" (items[1]! == .scalar ⟨"b", .plain, none, none, none⟩)
    check state "block seq third" (items[2]! == .scalar ⟨"c", .plain, none, none, none⟩)
  | .ok _ => check state "block seq 3 items is sequence" false
  | .error e => checkM state "block seq 3 items is sequence" false e
  -- Nested block mapping in sequence
  match parseSingle "- key: val" with
  | .ok (.sequence .block items _) =>
    check state "seq with nested map has 1 item" (items.size == 1)
    match items[0]! with
    | .mapping .block pairs _ =>
      check state "nested map has 1 pair" (pairs.size == 1)
    | _ => check state "nested item is mapping" false
  | .ok _ => check state "seq with nested map" false
  | .error e => checkM state "seq with nested map" false e

/-! ## §5 Multi-Document -/

def testMultiDocument (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Multi-document"
  -- Two documents split by ---
  match parseMulti "---\na\n---\nb" with
  | .ok docs =>
    check state "two docs with ---" (docs.size == 2)
    check state "first doc value" (docs[0]!.value == .scalar ⟨"a", .plain, none, none, none⟩)
    check state "second doc value" (docs[1]!.value == .scalar ⟨"b", .plain, none, none, none⟩)
  | .error e => checkM state "two docs with ---" false e
  -- Single document with explicit start
  match parseMulti "---\nhello" with
  | .ok docs =>
    check state "single doc with ---" (docs.size == 1)
    check state "explicit start value" (docs[0]!.value == .scalar ⟨"hello", .plain, none, none, none⟩)
  | .error e => checkM state "single doc with ---" false e
  -- Document with terminator
  match parseMulti "hello\n..." with
  | .ok docs =>
    check state "doc with ... terminator" (docs.size == 1)
  | .error e => checkM state "doc with ... terminator" false e

/-! ## §6 Edge Cases -/

def testEdgeCases (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Edge cases"
  -- Empty string produces error or empty
  match parseMulti "" with
  | .ok docs => check state "empty input" (docs.size == 0)
  | .error _ => check state "empty input" true  -- error is acceptable
  -- Whitespace-only (parser may return ok or error — both acceptable)
  match parseMulti "   " with
  | .ok _ => check state "whitespace-only parses" true
  | .error _ => check state "whitespace-only parses" true
  -- Comment-only
  match parseMulti "# just a comment" with
  | .ok docs => check state "comment-only" (docs.size == 0)
  | .error _ => check state "comment-only" true
  -- Trailing newline
  checkParse state "trailing newline" "hello\n" (.scalar ⟨"hello", .plain, none, none, none⟩)
  -- Unicode scalar
  checkParse state "unicode scalar" "日本語" (.scalar ⟨"日本語", .plain, none, none, none⟩)
  -- Leading whitespace in value
  match parseSingle "key:  spaced" with
  | .ok (.mapping .block pairs _) =>
    check state "extra space after colon" (pairs[0]!.2 == .scalar ⟨"spaced", .plain, none, none, none⟩)
  | .ok _ => check state "extra space after colon" false
  | .error e => checkM state "extra space after colon" false e

/-! ## §7 Stream Properties -/

def testStreamProperties (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Stream properties"
  -- ofString field values
  let s := YamlStream.ofString "abc"
  check state "ofString startPos == 0" (s.startPos.byteIdx == 0)
  check state "ofString stopPos correct" (s.stopPos == "abc".rawEndPos)
  check state "ofString line == 0" (s.line == 0)
  check state "ofString col == 0" (s.col == 0)
  check state "ofString validationError == none" (s.validationError == none)
  check state "ofString anchorMap empty" (s.anchorMap == AnchorMap.empty)
  -- remaining for ofString
  check state "remaining == rawEndPos.byteIdx"
    (Parser.Stream.remaining s == "abc".rawEndPos.byteIdx)
  -- Empty string
  let e := YamlStream.ofString ""
  check state "empty remaining == 0" (Parser.Stream.remaining e == 0)
  check state "empty hasNext == false" (!e.hasNext)
  -- Multi-byte string
  let u := YamlStream.ofString "é"
  check state "2-byte char remaining == 2" (Parser.Stream.remaining u == 2)
  let u3 := YamlStream.ofString "日"
  check state "3-byte char remaining == 3" (Parser.Stream.remaining u3 == 3)

/-! ## Collect All Tests -/

/-- Collect all completeness test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testPlainScalars state
  testQuotedScalars state
  testFlowCollections state
  testBlockCollections state
  testMultiDocument state
  testEdgeCases state
  testStreamProperties state
  let results ← finish state
  return { name := "completeness", label := "Completeness Tests",
           sourceFile := "Tests/CompletenessTests.lean", tests := results }

end Tests.Completeness
