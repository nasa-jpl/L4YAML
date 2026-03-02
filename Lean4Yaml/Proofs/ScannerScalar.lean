import Lean4Yaml.Scanner
import Lean4Yaml.Proofs.ScannerLoopInvariant
import Lean4Yaml.Proofs.ScannerContracts
import Lean4Yaml.Proofs.ScannerWhitespace

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scanner Scalar WellFormed Preservation (P10.10d)

Machine-checked proofs that the scanner's scalar scanning functions
preserve the `WellFormed` invariant.

## Scope

Four scalar scanner functions are covered:
- `scanDoubleQuoted` — double-quoted scalar `"..."` (§7.3.1)
- `scanSingleQuoted` — single-quoted scalar `'...'` (§7.3.2)
- `scanPlainScalar` — plain (unquoted) scalar (§7.3.3)
- `scanBlockScalar` — block literal `|` / folded `>` scalar (§8.1)

Helper functions with universal WellFormed proofs:
- `emitAt` — emit a token at a saved position (only modifies `tokens`)

## Key Insight

**All four scalar scanners only modify two categories of WellFormed fields:**

1. **`offset`** — via `advance`, `consumeNewline`, `skipSpaces`, `skipWhitespace`,
   `skipToEndOfLine` in looped content scanning.
2. **`tokens`** — via a single `emitAt` call at the end.

They **never** modify `indents`, `flowLevel`, `flowStack`, or `simpleKeyStack`.
Therefore:
- **C1** (`indents.size ≥ 1`): trivially preserved
- **C2** (`flowLevel = flowStack.size`): trivially preserved
- **C3** (`simpleKeyStack.size = flowStack.size`): trivially preserved
- **C4** (`offset ≤ inputEnd`): the substantive conjunct — requires reasoning
  about loops bounded by `inputEnd - offset` fuel.

Universal theorems are provided for `emitAt` and record update patterns.
For the four top-level scanner functions, comprehensive `#guard` checks
verify WellFormed preservation and correct token output on concrete states.
Full universal C4 proofs for the looped scanners are a future proof target
(requires `Nat.fold` invariant infrastructure).

## Zero Axioms

All theorems are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.ScannerScalar

open Lean4Yaml.Scanner
open Lean4Yaml.Proofs.ScannerLoopInvariant
open Lean4Yaml.Proofs.ScannerContracts

/-! ## §1  emitAt — WellFormed Preservation (universal)

```
def ScannerState.emitAt (s : ScannerState) (pos : YamlPos) (tok : YamlToken) : ScannerState :=
  { s with tokens := s.tokens.push { pos := pos, val := tok } }
```

Structurally identical to `emit` — only modifies `tokens`.
-/

/-- `emitAt` preserves `indents`. -/
theorem emitAt_indents (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).indents = s.indents := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `flowLevel`. -/
theorem emitAt_flowLevel (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).flowLevel = s.flowLevel := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `flowStack`. -/
theorem emitAt_flowStack (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).flowStack = s.flowStack := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `simpleKeyStack`. -/
theorem emitAt_simpleKeyStack (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).simpleKeyStack = s.simpleKeyStack := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `offset`. -/
theorem emitAt_offset (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).offset = s.offset := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `inputEnd`. -/
theorem emitAt_inputEnd (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).inputEnd = s.inputEnd := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `WellFormed` (all 4 conjuncts). -/
theorem emitAt_preserves_wellFormed (s : ScannerState) (pos : YamlPos) (tok : YamlToken)
    (hwf : s.WellFormed) : (s.emitAt pos tok).WellFormed := by
  obtain ⟨hind, hflow, hsk, hoff⟩ := hwf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [emitAt_indents]; exact hind
  · rw [emitAt_flowLevel, emitAt_flowStack]; exact hflow
  · rw [emitAt_simpleKeyStack, emitAt_flowStack]; exact hsk
  · rw [emitAt_offset, emitAt_inputEnd]; exact hoff

/-! ## §2  Record Update Patterns — WellFormed Preservation (universal)

All four scalar scanners return states constructed via:
  `{ s'.emitAt startPos (.scalar content style) with simpleKeyAllowed := ..., ... }`

Since `emitAt` only modifies `tokens`, and the `with` clause only modifies
`simpleKeyAllowed`/`simpleKey`, C1–C3 fields (indents, flowLevel, flowStack,
simpleKeyStack) in the result depend only on the loop-body state `s'`.

The loop body only calls `advance`, `consumeNewline`, `skipSpaces`,
`skipWhitespace`, `skipToEndOfLine`, `processEscape`, `foldQuotedNewlines` —
none of which modify C1–C3 fields.
-/

/-- A record update touching only `simpleKeyAllowed` preserves all WellFormed fields. -/
theorem with_simpleKeyAllowed_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed) (b : Bool) :
    ({ s with simpleKeyAllowed := b } : ScannerState).WellFormed := hwf

/-- A record update touching only `simpleKeyAllowed` and `simpleKey` preserves WellFormed. -/
theorem with_simpleKeyAllowed_simpleKey_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed) (b : Bool) (sk : SimpleKeyState) :
    ({ s with simpleKeyAllowed := b, simpleKey := sk } : ScannerState).WellFormed := hwf

/-- The final return pattern of `scanDoubleQuoted`/`scanSingleQuoted`:
    `{ s'.emitAt pos tok with simpleKeyAllowed := false }` preserves WellFormed. -/
theorem emitAt_then_setFlags_preserves_wellFormed (s : ScannerState)
    (pos : YamlPos) (tok : YamlToken) (hwf : s.WellFormed) :
    ({ s.emitAt pos tok with simpleKeyAllowed := false } : ScannerState).WellFormed :=
  emitAt_preserves_wellFormed s pos tok hwf

/-- The final return pattern of `scanBlockScalar`:
    `{ s'.emitAt pos tok with simpleKeyAllowed := true, simpleKey := ... }`
    preserves WellFormed. -/
theorem emitAt_then_blockFlags_preserves_wellFormed (s : ScannerState)
    (pos : YamlPos) (tok : YamlToken) (hwf : s.WellFormed) :
    ({ s.emitAt pos tok with
       simpleKeyAllowed := true
       simpleKey := ⟨false, 0, default, 0⟩ } : ScannerState).WellFormed :=
  emitAt_preserves_wellFormed s pos tok hwf

/-! ## §3  Validation Guards — emitAt -/

-- emitAt preserves WellFormed fields (concrete)
#guard ((ScannerState.mk' "test").emitAt default .key).indents.size ≥ 1
#guard ((ScannerState.mk' "test").emitAt default .key).flowLevel ==
       ((ScannerState.mk' "test").emitAt default .key).flowStack.size
#guard ((ScannerState.mk' "test").emitAt default .key).simpleKeyStack.size ==
       ((ScannerState.mk' "test").emitAt default .key).flowStack.size
#guard ((ScannerState.mk' "test").emitAt default .key).offset ≤
       ((ScannerState.mk' "test").emitAt default .key).inputEnd

-- emitAt produces one token
#guard ((ScannerState.mk' "test").emitAt default .key).tokens.size == 1

-- emitAt on state with existing tokens
#guard (((ScannerState.mk' "t").emit .streamStart).emitAt default .key).tokens.size == 2

/-! ## §4  Validation Guards — processEscape -/

-- Helper: check that processEscape result preserves WellFormed
private def checkEscapeWF (input : String) : Bool :=
  match processEscape (ScannerState.mk' input) with
  | .ok (_, s) => s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
                   && s.simpleKeyStack.size == s.flowStack.size
                   && s.offset ≤ s.inputEnd
  | .error _ => true  -- error paths don't need WellFormed

-- All named escapes preserve WellFormed
#guard checkEscapeWF "0"      -- \0 null
#guard checkEscapeWF "a"      -- \a bell
#guard checkEscapeWF "b"      -- \b backspace
#guard checkEscapeWF "t"      -- \t tab
#guard checkEscapeWF "n"      -- \n newline
#guard checkEscapeWF "v"      -- \v vertical tab
#guard checkEscapeWF "f"      -- \f form feed
#guard checkEscapeWF "r"      -- \r carriage return
#guard checkEscapeWF "e"      -- \e escape
#guard checkEscapeWF " "      -- \space
#guard checkEscapeWF "\""     -- \"
#guard checkEscapeWF "/"      -- \/
#guard checkEscapeWF "\\"     -- \\
#guard checkEscapeWF "N"      -- \N next line
#guard checkEscapeWF "_"      -- \_ non-breaking space
#guard checkEscapeWF "L"      -- \L line separator
#guard checkEscapeWF "P"      -- \P paragraph separator

-- Hex escapes preserve WellFormed
#guard checkEscapeWF "x41"        -- \x41 = 'A'
#guard checkEscapeWF "u0041"      -- \u0041 = 'A'
#guard checkEscapeWF "U00000041"  -- \U00000041 = 'A'

-- Unknown escape: error (no WellFormed needed)
#guard (processEscape (ScannerState.mk' "q")).isOk == false

-- C1-C3 field preservation for processEscape (concrete)
private def escState := ScannerState.mk' "n rest"
private def escResult : Option ScannerState :=
  match processEscape escState with
  | .ok (_, s) => some s
  | .error _ => none

#guard escResult.isSome == true
#guard (escResult.get!).indents.size ≥ 1
#guard (escResult.get!).flowLevel == (escResult.get!).flowStack.size
#guard (escResult.get!).simpleKeyStack.size == (escResult.get!).flowStack.size
#guard (escResult.get!).offset ≤ (escResult.get!).inputEnd

/-! ## §5  Validation Guards — foldQuotedNewlines -/

-- Helper: check foldQuotedNewlines WellFormed preservation
private def checkFoldWF (input : String) : Bool :=
  match foldQuotedNewlines (ScannerState.mk' input) with
  | .ok (_, s) => s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
                   && s.simpleKeyStack.size == s.flowStack.size
                   && s.offset ≤ s.inputEnd
  | .error _ => true

#guard checkFoldWF "\n  a"
#guard checkFoldWF "\n\n  a"
#guard checkFoldWF "\n\n\n  a"
#guard checkFoldWF "\r\n  a"
#guard checkFoldWF "\r  a"

-- foldQuotedNewlines: single newline → space
private def foldResult1 : Option String :=
  match foldQuotedNewlines (ScannerState.mk' "\n  content") with
  | .ok (content, _) => some content
  | .error _ => none
#guard foldResult1 == some " "

-- foldQuotedNewlines: two newlines → "\n"
private def foldResult2 : Option String :=
  match foldQuotedNewlines (ScannerState.mk' "\n\n  content") with
  | .ok (content, _) => some content
  | .error _ => none
#guard foldResult2 == some "\n"

-- foldQuotedNewlines: three newlines → "\n\n"
private def foldResult3 : Option String :=
  match foldQuotedNewlines (ScannerState.mk' "\n\n\n  content") with
  | .ok (content, _) => some content
  | .error _ => none
#guard foldResult3 == some "\n\n"

/-! ## §6  Validation Guards — scanDoubleQuoted -/

-- Helper: check WellFormed after any scalar scan
private def checkScanWF (f : ScannerState → Except ScanError ScannerState) (input : String) : Bool :=
  match f (ScannerState.mk' input) with
  | .ok s => s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
             && s.simpleKeyStack.size == s.flowStack.size
             && s.offset ≤ s.inputEnd
  | .error _ => true  -- error paths don't need WellFormed

-- Empty double-quoted scalar
#guard checkScanWF scanDoubleQuoted "\"\" rest"
-- Simple content
#guard checkScanWF scanDoubleQuoted "\"hello\" rest"
-- Content with escape
#guard checkScanWF scanDoubleQuoted "\"hello\\nworld\" rest"
-- Content with all named escapes
#guard checkScanWF scanDoubleQuoted "\"\\0\\a\\b\\t\\n\\v\\f\\r\\e\\\"\\\\\\/\" rest"
-- Unicode escapes
#guard checkScanWF scanDoubleQuoted "\"\\x41\\u0042\\U00000043\" rest"
-- Multi-line double-quoted
#guard checkScanWF scanDoubleQuoted "\"line1\n  line2\" rest"
-- Line fold: single newline → space
#guard checkScanWF scanDoubleQuoted "\"fold\n  here\" rest"
-- Line fold: multiple newlines
#guard checkScanWF scanDoubleQuoted "\"multi\n\n  line\" rest"
-- Backslash-newline (escaped line break = line continuation)
#guard checkScanWF scanDoubleQuoted "\"cont\\\n  inued\" rest"

-- Helper: extract last token from Except-returning scanner
private def lastToken (f : ScannerState → Except ScanError ScannerState)
    (input : String) : Option YamlToken :=
  match f (ScannerState.mk' input) with
  | .ok s => match s.tokens.back? with
    | some tok => some tok.val
    | none => none
  | .error _ => none

-- Verify correct token type (double-quoted)
#guard lastToken scanDoubleQuoted "\"hello\"" == some (.scalar "hello" .doubleQuoted)
#guard lastToken scanDoubleQuoted "\"\"" == some (.scalar "" .doubleQuoted)

-- Content extraction with escapes
#guard lastToken scanDoubleQuoted "\"a\\nb\"" == some (.scalar "a\nb" .doubleQuoted)
#guard lastToken scanDoubleQuoted "\"a\\tb\"" == some (.scalar "a\tb" .doubleQuoted)
#guard lastToken scanDoubleQuoted "\"a\\\\b\"" == some (.scalar "a\\b" .doubleQuoted)
#guard lastToken scanDoubleQuoted "\"a\\\"b\"" == some (.scalar "a\"b" .doubleQuoted)

-- simpleKeyAllowed is set to false after quoted scalar
private def afterDQ : Option Bool :=
  match scanDoubleQuoted (ScannerState.mk' "\"hello\"") with
  | .ok s => some s.simpleKeyAllowed
  | .error _ => none
#guard afterDQ == some false

-- Error cases
#guard (scanDoubleQuoted (ScannerState.mk' "\"unterminated")).isOk == false
#guard (scanDoubleQuoted (ScannerState.mk' "\"bad\\q\"")).isOk == false

/-! ## §7  Validation Guards — scanSingleQuoted -/

-- WellFormed preservation
#guard checkScanWF scanSingleQuoted "'' rest"
#guard checkScanWF scanSingleQuoted "'hello' rest"
#guard checkScanWF scanSingleQuoted "'it''s' rest"
#guard checkScanWF scanSingleQuoted "'line1\n  line2' rest"
#guard checkScanWF scanSingleQuoted "'a''b''c' rest"

-- Content extraction
#guard lastToken scanSingleQuoted "'hello'" == some (.scalar "hello" .singleQuoted)
#guard lastToken scanSingleQuoted "''" == some (.scalar "" .singleQuoted)
#guard lastToken scanSingleQuoted "'it''s'" == some (.scalar "it's" .singleQuoted)

-- simpleKeyAllowed set to false
private def afterSQ : Option Bool :=
  match scanSingleQuoted (ScannerState.mk' "'hello'") with
  | .ok s => some s.simpleKeyAllowed
  | .error _ => none
#guard afterSQ == some false

-- Error cases
#guard (scanSingleQuoted (ScannerState.mk' "'unterminated")).isOk == false

/-! ## §8  Validation Guards — scanPlainScalar -/

-- WellFormed preservation
#guard checkScanWF scanPlainScalar "hello rest"
#guard checkScanWF scanPlainScalar "key: value"
#guard checkScanWF scanPlainScalar "value # comment"
#guard checkScanWF scanPlainScalar "a:b rest"
#guard checkScanWF scanPlainScalar "just_value"

-- Content extraction
#guard lastToken scanPlainScalar "hello" == some (.scalar "hello" .plain)
#guard lastToken scanPlainScalar "hello world" == some (.scalar "hello world" .plain)
#guard lastToken scanPlainScalar "a:b" == some (.scalar "a:b" .plain)
#guard lastToken scanPlainScalar "value # comment" == some (.scalar "value" .plain)

-- simpleKeyAllowed set to false
private def afterPlain : Option Bool :=
  match scanPlainScalar (ScannerState.mk' "hello") with
  | .ok s => some s.simpleKeyAllowed
  | .error _ => none
#guard afterPlain == some false

-- Flow context: flow indicators terminate plain scalar
private def flowPlainToken (input : String) : Option YamlToken :=
  let fs := scanFlowSequenceStart (ScannerState.mk' ("[" ++ input))
  match scanPlainScalar fs with
  | .ok s => match s.tokens.back? with
    | some tok => some tok.val
    | none => none
  | .error _ => none

#guard flowPlainToken "hello]" == some (.scalar "hello" .plain)
#guard flowPlainToken "hello, world]" == some (.scalar "hello" .plain)

-- Flow context WellFormed
private def checkFlowPlainWF (input : String) : Bool :=
  let fs := scanFlowSequenceStart (ScannerState.mk' ("[" ++ input))
  match scanPlainScalar fs with
  | .ok s => s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
             && s.simpleKeyStack.size == s.flowStack.size
             && s.offset ≤ s.inputEnd
  | .error _ => true

#guard checkFlowPlainWF "hello]"
#guard checkFlowPlainWF "hello, world]"
#guard checkFlowPlainWF "a:b]"

/-! ## §9  Validation Guards — scanBlockScalar -/

-- WellFormed preservation
#guard checkScanWF scanBlockScalar "|\n  hello\n"
#guard checkScanWF scanBlockScalar ">\n  hello\n  world\n"
#guard checkScanWF scanBlockScalar "|2\n  hello\n"
#guard checkScanWF scanBlockScalar "|-\n  hello\n"
#guard checkScanWF scanBlockScalar "|+\n  hello\n\n"
#guard checkScanWF scanBlockScalar "|\n  hello\n\n"
#guard checkScanWF scanBlockScalar ">\n  a\n  b\n  c\n"
#guard checkScanWF scanBlockScalar "|\n\n  hello\n"
#guard checkScanWF scanBlockScalar "| # comment\n  hello\n"

-- Content extraction — literal style
#guard lastToken scanBlockScalar "|\n  hello\n" == some (.scalar "hello\n" .literal)
#guard lastToken scanBlockScalar "|-\n  stripped\n" == some (.scalar "stripped" .literal)
#guard lastToken scanBlockScalar "|+\n  kept\n\n" == some (.scalar "kept\n\n" .literal)

-- Content extraction — folded style
#guard lastToken scanBlockScalar ">\n  hello\n  world\n" == some (.scalar "hello world" .folded)

-- Block scalar flags
private def afterBlock : Option (Bool × Bool) :=
  match scanBlockScalar (ScannerState.mk' "|\n  hello\n") with
  | .ok s => some (s.simpleKeyAllowed, s.simpleKey.possible)
  | .error _ => none
#guard afterBlock == some (true, false)

-- Error: missing newline after block header
#guard (scanBlockScalar (ScannerState.mk' "|hello")).isOk == false

/-! ## §10  End-to-end Pipeline Guards — Scalar in Context -/

-- Helper: extract token values from full scan
private def scanTokens (input : String) : Option (List YamlToken) :=
  match scan input with
  | .ok tokens => some (tokens.toList.map Positioned.val)
  | .error _ => none

-- Double-quoted in mapping value
#guard scanTokens "key: \"value\"" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .doubleQuoted, .blockEnd, .streamEnd]

-- Single-quoted in mapping value
#guard scanTokens "key: 'value'" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .singleQuoted, .blockEnd, .streamEnd]

-- Plain scalar in mapping
#guard scanTokens "key: value" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- Block literal in mapping value
#guard scanTokens "key: |\n  block content\n" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "block content\n" .literal, .blockEnd, .streamEnd]

-- Block folded in mapping value
#guard scanTokens "key: >\n  folded\n  content\n" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "folded content" .folded, .blockEnd, .streamEnd]

-- Double-quoted with escapes in mapping
#guard scanTokens "key: \"line1\\nline2\"" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "line1\nline2" .doubleQuoted, .blockEnd, .streamEnd]

-- Single-quoted with escape in mapping
#guard scanTokens "key: 'it''s'" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "it's" .singleQuoted, .blockEnd, .streamEnd]

-- Flow sequence with mixed scalar types
#guard scanTokens "[\"dq\", 'sq', plain]" == some [
  .streamStart, .flowSequenceStart,
  .scalar "dq" .doubleQuoted, .flowEntry,
  .scalar "sq" .singleQuoted, .flowEntry,
  .scalar "plain" .plain,
  .flowSequenceEnd, .streamEnd]

-- Quoted scalar as mapping key
#guard scanTokens "\"key\": value" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .doubleQuoted, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- Block scalar: strip chomp in pipeline
#guard scanTokens "key: |-\n  stripped\n" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "stripped" .literal, .blockEnd, .streamEnd]

-- Block scalar: keep chomp in pipeline
#guard scanTokens "key: |+\n  kept\n\n" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "kept\n\n" .literal, .blockEnd, .streamEnd]

-- Multiple scalars of different types
#guard scanTokens "a: \"dq\"\nb: 'sq'\nc: plain" == some [
  .streamStart, .blockMappingStart,
  .key, .scalar "a" .plain, .value, .scalar "dq" .doubleQuoted,
  .key, .scalar "b" .plain, .value, .scalar "sq" .singleQuoted,
  .key, .scalar "c" .plain, .value, .scalar "plain" .plain,
  .blockEnd, .streamEnd]

-- Sequence of block scalars
#guard scanTokens "- |\n  lit1\n- >\n  fold1\n" == some [
  .streamStart, .blockSequenceStart,
  .blockEntry, .scalar "lit1\n" .literal,
  .blockEntry, .scalar "fold1" .folded,
  .blockEnd, .streamEnd]

-- UTF-8 in double-quoted
#guard scanTokens "key: \"αβγ\"" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "αβγ" .doubleQuoted, .blockEnd, .streamEnd]

-- UTF-8 in single-quoted
#guard scanTokens "key: 'αβγ'" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "αβγ" .singleQuoted, .blockEnd, .streamEnd]

-- UTF-8 in plain scalar
#guard scanTokens "key: αβγ" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "αβγ" .plain, .blockEnd, .streamEnd]

-- Empty double-quoted
#guard scanTokens "key: \"\"" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "" .doubleQuoted, .blockEnd, .streamEnd]

-- Empty single-quoted
#guard scanTokens "key: ''" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "" .singleQuoted, .blockEnd, .streamEnd]

-- Folded multi-line
#guard scanTokens "key: >\n  hello\n  world\n" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "hello world" .folded, .blockEnd, .streamEnd]

-- Literal multi-line
#guard scanTokens "key: |\n  hello\n  world\n" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "hello\nworld\n" .literal, .blockEnd, .streamEnd]

end Lean4Yaml.Proofs.ScannerScalar
