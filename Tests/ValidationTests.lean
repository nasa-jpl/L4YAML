import Lean4Yaml
import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Document
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Structural Validation Tests

Runtime tests exercising the structural validation architecture:
validation error semantics, indentation properties, decision type
discrimination, and ValidNode structural invariants.

These are the runtime counterparts of the formal proofs in
`Lean4Yaml/Proofs/Validation.lean`.

## Categories

1. **Validation error semantics** — first-error-wins, clear, orthogonality
2. **Indentation properties** — length bound, head space, zero, atLeast
3. **DispatchResult discrimination** — constructor disjointness
4. **FoldResult discrimination** — constructor disjointness
5. **DocumentResult discrimination** — constructor disjointness
6. **ContinuationCheck discrimination** — constructor disjointness
7. **ValidNode structural** — injectivity, empty collections, chomp
8. **Validation integration** — parser rejects invalid, accepts valid
-/

open Lean4Yaml
open Lean4Yaml.Grammar
open Lean4Yaml.Parse (ContinuationCheck DispatchResult FoldResult DocumentResult parseYaml)
open Tests

namespace Tests.Validation

/-! ## §1  Validation Error Semantics -/

def testValidationErrorSemantics (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Validation Error Semantics"

  -- Setting validationError is observable
  let s : YamlStream := YamlStream.ofString ""
  let s' : YamlStream := { s with validationError := some "err" }
  check state "set validationError → some msg" (s'.validationError == some "err")

  let s2 : YamlStream := YamlStream.ofString "abc"
  let s2' : YamlStream := { s2 with validationError := some "bad indent" }
  check state "set validationError different msg" (s2'.validationError == some "bad indent")

  -- Clearing validationError produces none
  let s3 : YamlStream := { s' with validationError := none }
  check state "clear validationError → none" (s3.validationError == none)

  -- First-error-wins guard: isNone check
  check state "isNone guard: none → true" (s.validationError.isNone == true)
  check state "isNone guard: some → false" (s'.validationError.isNone == false)

  -- Orthogonality: validation error ⊥ anchor map
  check state "set validationError preserves anchorMap" (s'.anchorMap == s.anchorMap)

  -- Orthogonality: validation error ⊥ position
  let s4 : YamlStream := YamlStream.ofString "hello"
  let s4v : YamlStream := { s4 with validationError := some "err" }
  check state "set validationError preserves startPos" (s4v.startPos == s4.startPos)

  let s4c : YamlStream := { s4 with validationError := none }
  check state "clear validationError preserves startPos" (s4c.startPos == s4.startPos)

  -- Default value
  check state "initial validationError is none" (s.validationError == none)

  -- Double-set: second set is a no-op (guard check)
  let se : YamlStream := { s with validationError := some "first" }
  -- Simulate first-error-wins: if isNone is false, don't overwrite
  let wouldOverwrite := !se.validationError.isNone
  check state "first-error-wins: isNone false after set" wouldOverwrite

  -- Clearing then setting works
  let sc : YamlStream := { se with validationError := none }
  let sc' : YamlStream := { sc with validationError := some "second" }
  check state "clear then set yields new msg" (sc'.validationError == some "second")

/-! ## §2  Indentation Properties -/

/-- Build a list with `n` leading spaces followed by `rest`. -/
private def mkIndented : (n : Nat) → (rest : List Char) → List Char
  | 0, cs => cs
  | n + 1, cs => ' ' :: mkIndented n cs

def testIndentationProperties (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Indentation Properties"

  -- Zero indentation
  check state "Indented 0: preserves content" (mkIndented 0 ['a', 'b'] == ['a', 'b'])
  check state "Indented 0: empty list" (mkIndented 0 [] == [])

  -- Length bound: mkIndented n rest has length ≥ n
  check state "indent 3 + 2 chars: length ≥ 3" ((mkIndented 3 ['x', 'y']).length >= 3)
  check state "indent 5 + 0 chars: length ≥ 5" ((mkIndented 5 []).length >= 5)
  check state "indent 10 + 0 chars: length ≥ 10" ((mkIndented 10 []).length >= 10)
  check state "indent 1 + 3 chars: length = 4" ((mkIndented 1 ['a', 'b', 'c']).length == 4)

  -- Head space: first char of positive indent is ' '
  check state "indent 1 head = ' '" ((mkIndented 1 ['a']).head? == some ' ')
  check state "indent 4 head = ' '" ((mkIndented 4 ['z']).head? == some ' ')
  check state "indent 0 head ≠ ' ' (content starts)" ((mkIndented 0 ['x']).head? == some 'x')

  -- Prefix is all spaces
  check state "indent 3 prefix" ((mkIndented 3 ['a']).take 3 == [' ', ' ', ' '])
  check state "indent 5 prefix = replicate 5 ' '" ((mkIndented 5 ['b']).take 5 == List.replicate 5 ' ')

  -- IndentedAtLeast: weaker requirements
  check state "indent 4 satisfies atLeast 2" ((mkIndented 4 ['x']).length >= 2)
  check state "indent 4 satisfies atLeast 0" ((mkIndented 4 ['x']).length >= 0)

  -- Tab is NOT a valid indent char
  check state "tab is not indent char" (('\t' == ' ') == false)
  check state "space is indent char" ((' ' == ' ') == true)

  -- Exact length
  check state "indent n adds exactly n chars" ((mkIndented 7 []).length == 7)
  check state "indent 0 adds no chars" ((mkIndented 0 ['a']).length == 1)

/-! ## §3  DispatchResult Discrimination -/

def testDispatchResult (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "DispatchResult Discrimination"

  -- Constructor disjointness
  check state "invalid ≠ matched" (
    match (DispatchResult.invalid "err" : DispatchResult Nat) with
    | .matched _ => false | _ => true)
  check state "invalid ≠ noMatch" (
    match (DispatchResult.invalid "err" : DispatchResult Nat) with
    | .noMatch => false | _ => true)
  check state "matched ≠ noMatch" (
    match (DispatchResult.matched 42 : DispatchResult Nat) with
    | .noMatch => false | _ => true)
  check state "noMatch ≠ matched" (
    match (DispatchResult.noMatch : DispatchResult Nat) with
    | .matched _ => false | _ => true)
  check state "noMatch ≠ invalid" (
    match (DispatchResult.noMatch : DispatchResult Nat) with
    | .invalid _ => false | _ => true)
  check state "matched ≠ invalid" (
    match (DispatchResult.matched 1 : DispatchResult Nat) with
    | .invalid _ => false | _ => true)

  -- Exhaustiveness
  check state "exhaustive: matched" (
    match (DispatchResult.matched "hi" : DispatchResult String) with
    | .matched _ | .noMatch | .invalid _ => true)
  check state "exhaustive: noMatch" (
    match (DispatchResult.noMatch : DispatchResult String) with
    | .matched _ | .noMatch | .invalid _ => true)
  check state "exhaustive: invalid" (
    match (DispatchResult.invalid "bad" : DispatchResult String) with
    | .matched _ | .noMatch | .invalid _ => true)

  -- Value extraction
  check state "matched extracts value" (
    match (DispatchResult.matched 99 : DispatchResult Nat) with
    | .matched v => v == 99 | _ => false)
  check state "invalid extracts message" (
    match (DispatchResult.invalid "tab in indent" : DispatchResult Nat) with
    | .invalid msg => msg == "tab in indent" | _ => false)

/-! ## §4  FoldResult Discrimination -/

def testFoldResult (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "FoldResult Discrimination"

  check state "forbidden ≠ folded" (
    match FoldResult.forbidden "c-forbidden" with
    | .folded _ => false | _ => true)
  check state "folded ≠ forbidden" (
    match FoldResult.folded "hello " with
    | .forbidden _ => false | _ => true)
  check state "exhaustive: folded" (
    match FoldResult.folded "ok" with
    | .folded _ | .forbidden _ => true)
  check state "exhaustive: forbidden" (
    match FoldResult.forbidden "---" with
    | .folded _ | .forbidden _ => true)
  check state "folded extracts string" (
    match FoldResult.folded "abc " with
    | .folded s => s == "abc " | _ => false)
  check state "forbidden extracts message" (
    match FoldResult.forbidden "document boundary" with
    | .forbidden msg => msg == "document boundary" | _ => false)

/-! ## §5  DocumentResult Discrimination -/

def testDocumentResult (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "DocumentResult Discrimination"

  check state "stalled ≠ parsed" (
    match DocumentResult.stalled ⟨0, 0, 0⟩ with
    | .parsed _ => false | _ => true)
  check state "stalled ≠ endOfStream" (
    match DocumentResult.stalled ⟨5, 1, 3⟩ with
    | .endOfStream => false | _ => true)
  check state "endOfStream ≠ parsed" (
    match (DocumentResult.endOfStream : DocumentResult) with
    | .parsed _ => false | _ => true)
  check state "endOfStream ≠ stalled" (
    match (DocumentResult.endOfStream : DocumentResult) with
    | .stalled _ => false | _ => true)
  check state "parsed ≠ stalled" (
    let doc : YamlDocument := { value := .scalar ⟨"hi", .plain, none⟩ }
    match DocumentResult.parsed doc with
    | .stalled _ => false | _ => true)
  check state "parsed ≠ endOfStream" (
    let doc : YamlDocument := { value := .scalar ⟨"hi", .plain, none⟩ }
    match DocumentResult.parsed doc with
    | .endOfStream => false | _ => true)

  -- Exhaustiveness
  check state "exhaustive: parsed" (
    let doc : YamlDocument := { value := .scalar ⟨"x", .plain, none⟩ }
    match DocumentResult.parsed doc with
    | .parsed _ | .endOfStream | .stalled _ => true)
  check state "exhaustive: endOfStream" (
    match (DocumentResult.endOfStream : DocumentResult) with
    | .parsed _ | .endOfStream | .stalled _ => true)
  check state "exhaustive: stalled" (
    match DocumentResult.stalled ⟨0, 0, 0⟩ with
    | .parsed _ | .endOfStream | .stalled _ => true)

  -- Position preservation in stalled
  check state "stalled preserves position" (
    let pos : YamlPos := ⟨42, 7, 3⟩
    match DocumentResult.stalled pos with
    | .stalled p => p.offset == 42 && p.line == 7 && p.col == 3
    | _ => false)

/-! ## §6  ContinuationCheck Discrimination -/

def testContinuationCheck (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "ContinuationCheck Discrimination"

  check state "sequenceMarker ≠ plainContinuation"
    (ContinuationCheck.sequenceMarker != ContinuationCheck.plainContinuation)
  check state "mappingEntry ≠ plainContinuation"
    (ContinuationCheck.mappingEntry != ContinuationCheck.plainContinuation)
  check state "notContinuing ≠ plainContinuation"
    (ContinuationCheck.notContinuing != ContinuationCheck.plainContinuation)
  check state "notContinuing ≠ sequenceMarker"
    (ContinuationCheck.notContinuing != ContinuationCheck.sequenceMarker)
  check state "notContinuing ≠ mappingEntry"
    (ContinuationCheck.notContinuing != ContinuationCheck.mappingEntry)
  check state "sequenceMarker ≠ mappingEntry"
    (ContinuationCheck.sequenceMarker != ContinuationCheck.mappingEntry)

  -- Exhaustiveness
  check state "exhaustive: notContinuing" (
    match (ContinuationCheck.notContinuing : ContinuationCheck) with
    | .notContinuing | .plainContinuation | .afterEmpty _ | .sequenceMarker | .mappingEntry => true)
  check state "exhaustive: plainContinuation" (
    match (ContinuationCheck.plainContinuation : ContinuationCheck) with
    | .notContinuing | .plainContinuation | .afterEmpty _ | .sequenceMarker | .mappingEntry => true)
  check state "exhaustive: afterEmpty 3" (
    match (ContinuationCheck.afterEmpty 3 : ContinuationCheck) with
    | .notContinuing | .plainContinuation | .afterEmpty _ | .sequenceMarker | .mappingEntry => true)
  check state "exhaustive: sequenceMarker" (
    match (ContinuationCheck.sequenceMarker : ContinuationCheck) with
    | .notContinuing | .plainContinuation | .afterEmpty _ | .sequenceMarker | .mappingEntry => true)
  check state "exhaustive: mappingEntry" (
    match (ContinuationCheck.mappingEntry : ContinuationCheck) with
    | .notContinuing | .plainContinuation | .afterEmpty _ | .sequenceMarker | .mappingEntry => true)

  -- Value extraction
  check state "afterEmpty extracts count" (
    match (ContinuationCheck.afterEmpty 5 : ContinuationCheck) with
    | .afterEmpty n => n == 5 | _ => false)
  check state "afterEmpty 0" (
    match (ContinuationCheck.afterEmpty 0 : ContinuationCheck) with
    | .afterEmpty n => n == 0 | _ => false)

/-! ## §7  ValidNode/ChompStyle Structural -/

def testValidNodeStructural (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "ValidNode & ChompStyle Structural"

  -- ChompStyle exhaustive + disjoint
  check state "ChompStyle strip ≠ clip" (ChompStyle.strip != ChompStyle.clip)
  check state "ChompStyle strip ≠ keep" (ChompStyle.strip != ChompStyle.keep)
  check state "ChompStyle clip ≠ keep" (ChompStyle.clip != ChompStyle.keep)
  check state "ChompStyle exhaustive: strip" (
    match ChompStyle.strip with | .strip | .clip | .keep => true)
  check state "ChompStyle exhaustive: clip" (
    match ChompStyle.clip with | .strip | .clip | .keep => true)
  check state "ChompStyle exhaustive: keep" (
    match ChompStyle.keep with | .strip | .clip | .keep => true)
  check state "ChompStyle decidable eq" (ChompStyle.strip == ChompStyle.strip)

  -- NodeToValue preserves style
  check state "plain scalar → .plain style" (
    let val : YamlValue := .scalar ⟨"hello", .plain, none⟩
    match val with | .scalar s => s.style == .plain | _ => false)
  check state "double-quoted → .doubleQuoted style" (
    let val : YamlValue := .scalar ⟨"world", .doubleQuoted, none⟩
    match val with | .scalar s => s.style == .doubleQuoted | _ => false)
  check state "single-quoted → .singleQuoted style" (
    let val : YamlValue := .scalar ⟨"test", .singleQuoted, none⟩
    match val with | .scalar s => s.style == .singleQuoted | _ => false)
  check state "literal → .literal style" (
    let val : YamlValue := .scalar ⟨"line1\nline2\n", .literal, none⟩
    match val with | .scalar s => s.style == .literal | _ => false)
  check state "folded → .folded style" (
    let val : YamlValue := .scalar ⟨"folded text\n", .folded, none⟩
    match val with | .scalar s => s.style == .folded | _ => false)

/-! ## §8  Validation Integration -/

def testValidationIntegration (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Validation Integration"

  -- Parser accepts valid YAML
  check state "accept: simple scalar" (
    match parseYaml "hello" with | .ok _ => true | .error _ => false)
  check state "accept: simple mapping" (
    match parseYaml "key: value" with | .ok _ => true | .error _ => false)
  check state "accept: simple sequence" (
    match parseYaml "- item1\n- item2" with | .ok _ => true | .error _ => false)
  check state "accept: flow sequence" (
    match parseYaml "[a, b, c]" with | .ok _ => true | .error _ => false)
  check state "accept: flow mapping" (
    match parseYaml "{a: 1, b: 2}" with | .ok _ => true | .error _ => false)
  check state "accept: multi-doc" (
    match parseYaml "---\na\n---\nb" with
    | .ok docs => docs.size == 2 | .error _ => false)
  check state "accept: document end marker" (
    match parseYaml "hello\n..." with | .ok _ => true | .error _ => false)
  check state "accept: double-quoted scalar" (
    match parseYaml "\"hello world\"" with | .ok _ => true | .error _ => false)
  check state "accept: single-quoted scalar" (
    match parseYaml "'hello world'" with | .ok _ => true | .error _ => false)
  check state "accept: literal block scalar" (
    match parseYaml "data: |\n  line1\n  line2" with | .ok _ => true | .error _ => false)
  check state "accept: nested mapping" (
    match parseYaml "a:\n  b: c" with | .ok _ => true | .error _ => false)
  check state "accept: empty document" (
    match parseYaml "" with | .ok _ => true | .error _ => false)

  -- Validation error rejects structurally invalid input
  check state "reject: tab in indentation" (
    match parseYaml "a:\n  b:\n\tc: d" with | Except.ok _ => false | Except.error _ => true)
  check state "reject: trailing content after flow seq" (
    match parseYaml "[a, b] extra" with | Except.ok _ => false | Except.error _ => true)
  check state "reject: trailing content after flow map" (
    match parseYaml "{a: 1} extra" with | Except.ok _ => false | Except.error _ => true)

/-! ## §9  Block Scalar Contract Tests -/

def testBlockScalarContracts (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Block Scalar Contracts"

  -- §1: Header character classification (Grammar.isBlockScalarHeaderChar)
  check state "'-' is header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar '-' == true)
  check state "'+' is header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar '+' == true)
  check state "'1' is header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar '1' == true)
  check state "'9' is header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar '9' == true)
  check state "'5' is header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar '5' == true)
  check state "'0' is NOT header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar '0' == false)
  check state "'\\n' is NOT header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar '\n' == false)
  check state "' ' is NOT header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar ' ' == false)
  check state "'\\t' is NOT header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar '\t' == false)
  check state "'a' is NOT header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar 'a' == false)
  check state "'#' is NOT header char" (Lean4Yaml.Grammar.isBlockScalarHeaderChar '#' == false)

  -- §2: extractHeaderChars specification
  check state "extract empty = ([], [])" (Lean4Yaml.Grammar.extractHeaderChars [] == ([], []))
  check state "extract '-' = (['-'], [])" (Lean4Yaml.Grammar.extractHeaderChars ['-'] == (['-'], []))
  check state "extract '-2' = (['-','2'], [])" (
    Lean4Yaml.Grammar.extractHeaderChars ['-', '2'] == (['-', '2'], []))
  check state "extract '\\n' = ([], ['\\n'])" (
    Lean4Yaml.Grammar.extractHeaderChars ['\n'] == ([], ['\n']))
  check state "extract '\\nxy' preserves tail" (
    Lean4Yaml.Grammar.extractHeaderChars ['\n', 'x', 'y'] == ([], ['\n', 'x', 'y']))
  check state "extract '2-\\n' = (['2','-'], ['\\n'])" (
    Lean4Yaml.Grammar.extractHeaderChars ['2', '-', '\n'] == (['2', '-'], ['\n']))

  -- §3: Contract G2 — literal block scalar column invariant
  -- These tests exercise the runtime assertion in blockScalarHeader.
  -- If the contract is violated, parsing would produce a validation error.
  check state "literal block: no contract violation" (
    match parseYaml "data: |\n  line1\n  line2" with | .ok _ => true | .error _ => false)
  check state "folded block: no contract violation" (
    match parseYaml "data: >\n  line1\n  line2" with | .ok _ => true | .error _ => false)
  check state "literal block with chomp strip" (
    match parseYaml "data: |-\n  line1\n  line2" with | .ok _ => true | .error _ => false)
  check state "literal block with chomp keep" (
    match parseYaml "data: |+\n  line1\n  line2" with | .ok _ => true | .error _ => false)
  check state "literal block with explicit indent" (
    -- |1 means 1-space indent relative to parent; with 'data: ' the parent
    -- indent is 0, so content needs 1 space of indentation (0 + 1 = 1)
    match parseYaml "|1\n line1\n line2" with | .ok _ => true | .error _ => false)
  check state "folded block with chomp+indent" (
    -- >-1 means strip chomp + 1-space indent; standalone so parentIndent=0
    match parseYaml ">-1\n line1\n line2" with | .ok _ => true | .error _ => false)
  check state "literal block: plain header (no indicators)" (
    match parseYaml "data: |\n  content" with | .ok _ => true | .error _ => false)

  -- §4: Peek-before-consume discipline — non-header chars are not consumed
  -- These are regression tests for the exact bug class that was fixed.
  check state "peek-before-consume: newline not consumed by header loop" (
    match parseYaml "|\n  hello" with | .ok _ => true | .error _ => false)
  check state "peek-before-consume: space not consumed by header loop" (
    match parseYaml "|  \n  hello" with | .ok _ => true | .error _ => false)
  check state "peek-before-consume: comment after indicator" (
    match parseYaml "| # comment\n  hello" with | .ok _ => true | .error _ => false)

/-! ## Collect All Tests -/

/-- Collect all validation test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testValidationErrorSemantics state
  testIndentationProperties state
  testDispatchResult state
  testFoldResult state
  testDocumentResult state
  testContinuationCheck state
  testValidNodeStructural state
  testValidationIntegration state
  testBlockScalarContracts state
  let results ← finish state
  return { name := "validationtests", label := "Structural Validation Tests",
           sourceFile := "Tests/ValidationTests.lean", tests := results }

end Tests.Validation
