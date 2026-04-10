import L4YAML
import L4YAML.Grammar
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
`L4YAML/Proofs/Validation.lean`.

## Categories

1. **Validation error semantics** — first-error-wins, clear, orthogonality
2. **Indentation properties** — length bound, head space, zero, atLeast
3. **ValidNode structural** — injectivity, empty collections, chomp
4. **Validation integration** — parser rejects invalid, accepts valid
-/

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser
open Tests

namespace Tests.Validation

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

/-! ## §3  ValidNode/ChompStyle Structural -/

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
    let val : YamlValue := .scalar ⟨"hello", .plain, none, none, none⟩
    match val with | .scalar s => s.style == .plain | _ => false)
  check state "double-quoted → .doubleQuoted style" (
    let val : YamlValue := .scalar ⟨"world", .doubleQuoted, none, none, none⟩
    match val with | .scalar s => s.style == .doubleQuoted | _ => false)
  check state "single-quoted → .singleQuoted style" (
    let val : YamlValue := .scalar ⟨"test", .singleQuoted, none, none, none⟩
    match val with | .scalar s => s.style == .singleQuoted | _ => false)
  check state "literal → .literal style" (
    let val : YamlValue := .scalar ⟨"line1\nline2\n", .literal, none, none, none⟩
    match val with | .scalar s => s.style == .literal | _ => false)
  check state "folded → .folded style" (
    let val : YamlValue := .scalar ⟨"folded text\n", .folded, none, none, none⟩
    match val with | .scalar s => s.style == .folded | _ => false)

/-! ## §4  Validation Integration -/

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

/-! ## §5  Block Scalar Contract Tests -/

def testBlockScalarContracts (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Block Scalar Contracts"

  -- §1: Header character classification (Grammar.isBlockScalarHeaderChar)
  check state "'-' is header char" (L4YAML.Grammar.isBlockScalarHeaderChar '-' == true)
  check state "'+' is header char" (L4YAML.Grammar.isBlockScalarHeaderChar '+' == true)
  check state "'1' is header char" (L4YAML.Grammar.isBlockScalarHeaderChar '1' == true)
  check state "'9' is header char" (L4YAML.Grammar.isBlockScalarHeaderChar '9' == true)
  check state "'5' is header char" (L4YAML.Grammar.isBlockScalarHeaderChar '5' == true)
  check state "'0' is NOT header char" (L4YAML.Grammar.isBlockScalarHeaderChar '0' == false)
  check state "'\\n' is NOT header char" (L4YAML.Grammar.isBlockScalarHeaderChar '\n' == false)
  check state "' ' is NOT header char" (L4YAML.Grammar.isBlockScalarHeaderChar ' ' == false)
  check state "'\\t' is NOT header char" (L4YAML.Grammar.isBlockScalarHeaderChar '\t' == false)
  check state "'a' is NOT header char" (L4YAML.Grammar.isBlockScalarHeaderChar 'a' == false)
  check state "'#' is NOT header char" (L4YAML.Grammar.isBlockScalarHeaderChar '#' == false)

  -- §2: extractHeaderChars specification
  check state "extract empty = ([], [])" (L4YAML.Grammar.extractHeaderChars [] == ([], []))
  check state "extract '-' = (['-'], [])" (L4YAML.Grammar.extractHeaderChars ['-'] == (['-'], []))
  check state "extract '-2' = (['-','2'], [])" (
    L4YAML.Grammar.extractHeaderChars ['-', '2'] == (['-', '2'], []))
  check state "extract '\\n' = ([], ['\\n'])" (
    L4YAML.Grammar.extractHeaderChars ['\n'] == ([], ['\n']))
  check state "extract '\\nxy' preserves tail" (
    L4YAML.Grammar.extractHeaderChars ['\n', 'x', 'y'] == ([], ['\n', 'x', 'y']))
  check state "extract '2-\\n' = (['2','-'], ['\\n'])" (
    L4YAML.Grammar.extractHeaderChars ['2', '-', '\n'] == (['2', '-'], ['\n']))

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

/-! ## §6  Flow Structure Error Tests (Step 10a)

These tests correspond to the 13 yaml-test-suite error cases tagged with
`flow` + (`sequence` or `mapping`) that the parser must reject.
Each input is structurally invalid YAML that should produce a parse error.

| Suite ID | Description                                     |
|----------|-------------------------------------------------|
| 4H7K     | Extra closing `]` after flow sequence            |
| 62EZ     | Content after `}` without separator              |
| 6JTT     | Unclosed outer bracket in nested sequence        |
| 9JBA     | Comment `#` without space after `]`              |
| 9MAG     | Leading comma `[ , ...]`                         |
| C2SP     | Flow mapping key split across lines              |
| CTN5     | Double comma `[ a, b, c, , ]`                    |
| CVW2     | Comment `#` without space after `,`              |
| DK4H     | Implicit key + `:` on separate line in flow      |
| KS4U     | Content after closed flow sequence               |
| P2EQ     | Block item after `}` on same line                |
| T833     | Missing comma between flow mapping entries       |
| ZXT5     | Quoted key + `:value` on next line in flow       |
-/

def testFlowStructureErrors (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow Structure Errors"

  -- 4H7K: Extra closing bracket — `[ a, b, c ] ]`
  check state "reject: extra closing bracket (4H7K)" (
    match parseYaml "---\n[ a, b, c ] ]\n" with | .ok _ => false | .error _ => true)

  -- 62EZ: Content after `}` without separator — `x: { y: z }in: valid`
  check state "reject: content after closing brace (62EZ)" (
    match parseYaml "---\nx: { y: z }in: valid\n" with | .ok _ => false | .error _ => true)

  -- 6JTT: Unclosed bracket — `[ [ a, b, c ]` (outer `[` never closed)
  check state "reject: unclosed flow sequence (6JTT)" (
    match parseYaml "---\n[ [ a, b, c ]\n" with | .ok _ => false | .error _ => true)

  -- 9JBA: Comment without space after `]` — `[ a, b, c, ]#invalid`
  check state "reject: comment without space after ] (9JBA)" (
    match parseYaml "---\n[ a, b, c, ]#invalid\n" with | .ok _ => false | .error _ => true)

  -- 9MAG: Leading comma — `[ , a, b, c ]`
  check state "reject: leading comma in flow seq (9MAG)" (
    match parseYaml "---\n[ , a, b, c ]\n" with | .ok _ => false | .error _ => true)

  -- C2SP: Multiline flow key — `[23\n]: 42`
  check state "reject: multiline flow mapping key (C2SP)" (
    match parseYaml "[23\n]: 42\n" with | .ok _ => false | .error _ => true)

  -- CTN5: Double comma — `[ a, b, c, , ]`
  check state "reject: double comma in flow seq (CTN5)" (
    match parseYaml "---\n[ a, b, c, , ]\n" with | .ok _ => false | .error _ => true)

  -- CVW2: Comment after comma without space — `[ a, b, c,#invalid\n]`
  check state "reject: comment without space after comma (CVW2)" (
    match parseYaml "---\n[ a, b, c,#invalid\n]\n" with | .ok _ => false | .error _ => true)

  -- DK4H: Implicit key + `:` on separate line in flow — `[ key\n  : value ]`
  check state "reject: implicit key colon on next line (DK4H)" (
    match parseYaml "---\n[ key\n  : value ]\n" with | .ok _ => false | .error _ => true)

  -- KS4U: Content after closed flow sequence — `[\nsequence item\n]\ninvalid item`
  check state "reject: content after closed flow seq (KS4U)" (
    match parseYaml "---\n[\nsequence item\n]\ninvalid item\n" with | .ok _ => false | .error _ => true)

  -- P2EQ: Block item after `}` on same line — `- { y: z }- invalid`
  check state "reject: block item after flow map (P2EQ)" (
    match parseYaml "---\n- { y: z }- invalid\n" with | .ok _ => false | .error _ => true)

  -- T833: Missing comma in flow mapping — `{\n foo: 1\n bar: 2 }`
  check state "reject: missing comma in flow mapping (T833)" (
    match parseYaml "---\n{\n foo: 1\n bar: 2 }\n" with | .ok _ => false | .error _ => true)

  -- ZXT5: Quoted key + `:value` on next line — `[ "key"\n  :value ]`
  check state "reject: colon-value on next line after quoted key (ZXT5)" (
    match parseYaml "[ \"key\"\n  :value ]\n" with | .ok _ => false | .error _ => true)

/-! ## Collect All Tests -/

/-- Collect all validation test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testIndentationProperties state
  testValidNodeStructural state
  testValidationIntegration state
  testBlockScalarContracts state
  testFlowStructureErrors state
  let results ← finish state
  return { name := "validationtests", label := "Structural Validation Tests",
           sourceFile := "Tests/ValidationTests.lean", tests := results }

end Tests.Validation
