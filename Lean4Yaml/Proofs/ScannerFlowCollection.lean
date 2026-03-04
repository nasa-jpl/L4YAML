import Lean4Yaml.Scanner
import Lean4Yaml.Emitter
import Lean4Yaml.Proofs.ScannerLoopInvariant
import Lean4Yaml.Proofs.ScannerContracts

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Flow Collection Scanner Correctness (P10.8f.3)

Machine-checked proof that the scanner's `scanFlowSequenceStart/End`,
`scanFlowMappingStart/End`, and `scanFlowEntry` correctly tokenize the
`[`, `]`, `{`, `}`, `,` delimiters produced by the emitter.

## Key Results

### Universal Theorems (15)

**advance field preservation:**

1. **`advance_tokens`**: `ScannerState.advance` preserves the `tokens` array.

**Token count — each flow function emits exactly one token:**

2. **`scanFlowSequenceStart_tokens_size`**: Token count increases by 1.
3. **`scanFlowMappingStart_tokens_size`**: Token count increases by 1.
4. **`scanFlowSequenceEnd_tokens_size`**: Token count increases by 1.
5. **`scanFlowMappingEnd_tokens_size`**: Token count increases by 1.

**Flow end decrements flowLevel:**

6. **`scanFlowSequenceEnd_flowLevel_pos`**: When `flowLevel > 0`,
   `scanFlowSequenceEnd` decrements it by 1.
7. **`scanFlowMappingEnd_flowLevel_pos`**: Same for mapping end.

**Flow end preserves flowLevel/flowStack synchronization:**

8. **`scanFlowSequenceEnd_flow_sync`**: If `flowLevel = flowStack.size`
   before, the invariant holds after `scanFlowSequenceEnd`.
9. **`scanFlowMappingEnd_flow_sync`**: Same for mapping end.

**Flow start enters flow context:**

10. **`scanFlowSequenceStart_inFlow`**: After `scanFlowSequenceStart`,
    the scanner enters flow context (`inFlow = true`).
11. **`scanFlowMappingStart_inFlow`**: Same for mapping start.

**Flow start pushes correct stack marker:**

12. **`scanFlowSequenceStart_pushes_true`**: Sequences push `true` on
    the flow stack.
13. **`scanFlowMappingStart_pushes_false`**: Mappings push `false`.

**scanFlowEntry (comma) correctness:**

14. **`scanFlowEntry_preserves_flowLevel`**: A successful comma scan
    preserves the flow level.
15. **`scanFlowEntry_tokens_size`**: A successful comma scan adds
    exactly one token.

### Compile-Time Verification (37 `#guard` checks)

End-to-end verification covering:
- Correct token types emitted by each flow function
- Leading-comma rejection after flow-open tokens
- Comma acceptance after scalar tokens
- Full `scan` pipeline for `[]`, `{}`, `[a]`, `[a,b]`, `{k:v}`,
  nested sequences/mappings, and mixed nesting
- `emit → scan` round-trip for empty/single/multi-element flow
  sequences and mappings
- Escaped content (`\n`, `\t`) in flow collections
- UTF-8 content (Greek, CJK) in flow collections

## Architecture

The flow collection delimiters (`[`, `]`, `{`, `}`, `,`) are
single-character dispatches with minimal state interaction.  Each
function calls `emit` (appending one token) and `advance` (moving
past the delimiter character).  The start functions additionally
increment `flowLevel` and push onto `flowStack`; the end functions
decrement and pop.

The proofs decompose each function into its constituent operations
(`emit`, `advance`, field updates) using `simp` with the established
lemmas from `ScannerLoopInvariant` (`advance_flowLevel`, etc.) and
`ScannerContracts` (`emit_flowLevel`, etc.).

For `scanFlowEntry`, which uses `do`-notation with an error-throwing
guard, the proofs reduce the monadic structure via `dsimp [letFun]`
and `simp [Bind.bind, Except.bind, ...]` before splitting on the
guard condition.

All theorems are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.ScannerFlowCollection

open Lean4Yaml
open Lean4Yaml.Scanner
open Lean4Yaml.Emit
open Lean4Yaml.Proofs.ScannerLoopInvariant

/-! ## advance preserves tokens -/

/-- `ScannerState.advance` preserves the `tokens` array.
    Complement to `advance_flowLevel`, `advance_flowStack`, etc.
    from `ScannerLoopInvariant`. -/
theorem advance_tokens (s : ScannerState) :
    s.advance.tokens = s.tokens := by
  unfold ScannerState.advance; split <;> simp_all; split <;> rfl

/-! ## Token count: each flow function adds exactly one token -/

/-- `scanFlowSequenceStart` adds exactly one token. -/
theorem scanFlowSequenceStart_tokens_size (s : ScannerState) :
    (scanFlowSequenceStart s).tokens.size = s.tokens.size + 1 := by
  simp [scanFlowSequenceStart, advance_tokens, ScannerState.emit, Array.size_push]

/-- `scanFlowMappingStart` adds exactly one token. -/
theorem scanFlowMappingStart_tokens_size (s : ScannerState) :
    (scanFlowMappingStart s).tokens.size = s.tokens.size + 1 := by
  simp [scanFlowMappingStart, advance_tokens, ScannerState.emit, Array.size_push]

/-- `scanFlowSequenceEnd` adds exactly one token. -/
theorem scanFlowSequenceEnd_tokens_size (s : ScannerState) :
    (scanFlowSequenceEnd s).tokens.size = s.tokens.size + 1 := by
  simp [scanFlowSequenceEnd, advance_tokens, ScannerState.emit, Array.size_push]

/-- `scanFlowMappingEnd` adds exactly one token. -/
theorem scanFlowMappingEnd_tokens_size (s : ScannerState) :
    (scanFlowMappingEnd s).tokens.size = s.tokens.size + 1 := by
  simp [scanFlowMappingEnd, advance_tokens, ScannerState.emit, Array.size_push]

/-! ## Flow end decrements flowLevel when > 0 -/

/-- Helper: emit preserves flowLevel. -/
theorem emit_preserves_flowLevel (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).flowLevel = s.flowLevel := by
  unfold ScannerState.emit
  rfl

/-- Helper: advance preserves flowLevel. -/
theorem advance_preserves_flowLevel (s : ScannerState) :
    s.advance.flowLevel = s.flowLevel := by
  unfold ScannerState.advance
  split
  · simp only []
    split <;> rfl
  · rfl

/-- When `flowLevel > 0`, `scanFlowSequenceEnd` decrements it by 1. -/
theorem scanFlowSequenceEnd_flowLevel_pos (s : ScannerState) (h : s.flowLevel > 0) :
    (scanFlowSequenceEnd s).flowLevel = s.flowLevel - 1 := by
  unfold scanFlowSequenceEnd
  simp only [emit_preserves_flowLevel, advance_preserves_flowLevel]
  split <;> omega

/-- When `flowLevel > 0`, `scanFlowMappingEnd` decrements it by 1. -/
theorem scanFlowMappingEnd_flowLevel_pos (s : ScannerState) (h : s.flowLevel > 0) :
    (scanFlowMappingEnd s).flowLevel = s.flowLevel - 1 := by
  unfold scanFlowMappingEnd
  simp only [emit_preserves_flowLevel, advance_preserves_flowLevel]
  split <;> omega

/-! ## Flow end preserves flow_sync when > 0 -/

/-- Helper: emit preserves flowStack. -/
theorem emit_preserves_flowStack (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).flowStack = s.flowStack := by
  unfold ScannerState.emit
  rfl

/-- Helper: advance preserves flowStack. -/
theorem advance_preserves_flowStack (s : ScannerState) :
    s.advance.flowStack = s.flowStack := by
  unfold ScannerState.advance
  split
  · simp only []
    split <;> rfl
  · rfl

/-- `scanFlowSequenceEnd` preserves `flowLevel = flowStack.size` when `flowLevel > 0`. -/
theorem scanFlowSequenceEnd_flow_sync (s : ScannerState)
    (h : s.flowLevel = s.flowStack.size) (hpos : s.flowLevel > 0) :
    (scanFlowSequenceEnd s).flowLevel = (scanFlowSequenceEnd s).flowStack.size := by
  unfold scanFlowSequenceEnd
  simp only [emit_preserves_flowLevel, emit_preserves_flowStack,
             advance_preserves_flowLevel, advance_preserves_flowStack,
             Array.size_pop]
  split <;> omega

/-- `scanFlowMappingEnd` preserves `flowLevel = flowStack.size` when `flowLevel > 0`. -/
theorem scanFlowMappingEnd_flow_sync (s : ScannerState)
    (h : s.flowLevel = s.flowStack.size) (hpos : s.flowLevel > 0) :
    (scanFlowMappingEnd s).flowLevel = (scanFlowMappingEnd s).flowStack.size := by
  unfold scanFlowMappingEnd
  simp only [emit_preserves_flowLevel, emit_preserves_flowStack,
             advance_preserves_flowLevel, advance_preserves_flowStack,
             Array.size_pop]
  split <;> omega

/-! ## Flow start → inFlow -/

/-- After `scanFlowSequenceStart`, `inFlow = true`. -/
theorem scanFlowSequenceStart_inFlow (s : ScannerState) :
    (scanFlowSequenceStart s).inFlow = true := by
  simp [scanFlowSequenceStart, ScannerState.inFlow, ScannerState.emit]

/-- After `scanFlowMappingStart`, `inFlow = true`. -/
theorem scanFlowMappingStart_inFlow (s : ScannerState) :
    (scanFlowMappingStart s).inFlow = true := by
  simp [scanFlowMappingStart, ScannerState.inFlow, ScannerState.emit]

/-! ## Flow start pushes correct stack marker -/

/-- `scanFlowSequenceStart` pushes `true` (sequence marker) on `flowStack`. -/
theorem scanFlowSequenceStart_pushes_true (s : ScannerState) :
    (scanFlowSequenceStart s).flowStack = s.flowStack.push true := by
  unfold scanFlowSequenceStart
  simp only [emit_preserves_flowStack, advance_preserves_flowStack]

/-- `scanFlowMappingStart` pushes `false` (mapping marker) on `flowStack`. -/
theorem scanFlowMappingStart_pushes_false (s : ScannerState) :
    (scanFlowMappingStart s).flowStack = s.flowStack.push false := by
  unfold scanFlowMappingStart
  simp only [emit_preserves_flowStack, advance_preserves_flowStack]

/-! ## scanFlowEntry correctness -/

/-- A successful `scanFlowEntry` preserves `flowLevel`. -/
theorem scanFlowEntry_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanFlowEntry s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanFlowEntry at h
  split at h
  · dsimp only [letFun] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; rw [← h]; simp [ScannerState.emit, advance_flowLevel]
  · injection h with h; rw [← h]; simp [ScannerState.emit, advance_flowLevel]

/-- A successful `scanFlowEntry` adds exactly one token. -/
theorem scanFlowEntry_tokens_size (s : ScannerState) (s' : ScannerState)
    (h : scanFlowEntry s = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanFlowEntry at h
  split at h
  · dsimp only [letFun] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    split at h
    · exact absurd h (by simp)
    · injection h with h; rw [← h]; simp [ScannerState.emit, advance_tokens, Array.size_push]
  · injection h with h; rw [← h]; simp [ScannerState.emit, advance_tokens, Array.size_push]

/-! ## Concrete token type `#guard` checks -/

#guard (scanFlowSequenceStart (ScannerState.mk' "[")).tokens.back!.val == .flowSequenceStart
#guard (scanFlowMappingStart (ScannerState.mk' "{")).tokens.back!.val == .flowMappingStart
#guard (scanFlowSequenceEnd (ScannerState.mk' "]")).tokens.back!.val == .flowSequenceEnd
#guard (scanFlowMappingEnd (ScannerState.mk' "}")).tokens.back!.val == .flowMappingEnd

-- Leading comma rejected after flow open
private def stateAfterSeqOpen : ScannerState := scanFlowSequenceStart (ScannerState.mk' "[,")
#guard stateAfterSeqOpen.tokens.back!.val == .flowSequenceStart
#guard (scanFlowEntry stateAfterSeqOpen).isOk == false

private def stateAfterMapOpen : ScannerState := scanFlowMappingStart (ScannerState.mk' "{,")
#guard stateAfterMapOpen.tokens.back!.val == .flowMappingStart
#guard (scanFlowEntry stateAfterMapOpen).isOk == false

-- Comma succeeds after a scalar token
private def stateInSeq : ScannerState :=
  let s := scanFlowSequenceStart (ScannerState.mk' "[\"a\",")
  s.emit (.scalar "a" .doubleQuoted)
#guard (scanFlowEntry stateInSeq).isOk == true

/-! ## End-to-end scan `#guard` checks -/

private def scanTokenTypes (input : String) : Option (List YamlToken) :=
  match scan input with
  | .ok tokens => some (tokens.toList.map (·.val))
  | .error _ => none

-- Empty flow sequence
#guard scanTokenTypes "[]" == some [.streamStart, .flowSequenceStart, .flowSequenceEnd, .streamEnd]
-- Empty flow mapping
#guard scanTokenTypes "{}" == some [.streamStart, .flowMappingStart, .flowMappingEnd, .streamEnd]
-- Sequence with one DQ scalar
#guard scanTokenTypes "[\"a\"]" == some [.streamStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowSequenceEnd, .streamEnd]
-- Sequence with two DQ scalars
#guard scanTokenTypes "[\"a\", \"b\"]" == some [.streamStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowEntry, .scalar "b" .doubleQuoted, .flowSequenceEnd, .streamEnd]
-- Mapping with one pair
#guard scanTokenTypes "{\"k\": \"v\"}" == some [.streamStart, .flowMappingStart, .key, .scalar "k" .doubleQuoted, .value, .scalar "v" .doubleQuoted, .flowMappingEnd, .streamEnd]
-- Nested: sequence in mapping
#guard scanTokenTypes "{\"k\": [\"a\"]}" == some [.streamStart, .flowMappingStart, .key, .scalar "k" .doubleQuoted, .value, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowSequenceEnd, .flowMappingEnd, .streamEnd]
-- Nested: mapping in sequence
#guard scanTokenTypes "[{\"k\": \"v\"}]" == some [.streamStart, .flowSequenceStart, .flowMappingStart, .key, .scalar "k" .doubleQuoted, .value, .scalar "v" .doubleQuoted, .flowMappingEnd, .flowSequenceEnd, .streamEnd]

/-! ## emit → scan end-to-end -/

private def mkScalar (s : String) : YamlValue := .scalar { content := s, style := .doubleQuoted }
private def emptySeq : YamlValue := .sequence .flow #[]
private def emptyMap : YamlValue := .mapping .flow #[]

#guard emit emptySeq == "[]"
#guard scanTokenTypes (emit emptySeq) == some [.streamStart, .flowSequenceStart, .flowSequenceEnd, .streamEnd]
#guard emit emptyMap == "{}"
#guard scanTokenTypes (emit emptyMap) == some [.streamStart, .flowMappingStart, .flowMappingEnd, .streamEnd]

-- Single-element sequence
private def singleSeq : YamlValue := .sequence .flow #[mkScalar "hello"]
#guard emit singleSeq == "[\"hello\"]"
#guard scanTokenTypes (emit singleSeq) == some [.streamStart, .flowSequenceStart, .scalar "hello" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- Two-element sequence
private def twoSeq : YamlValue := .sequence .flow #[mkScalar "a", mkScalar "b"]
#guard emit twoSeq == "[\"a\", \"b\"]"
#guard scanTokenTypes (emit twoSeq) == some [.streamStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowEntry, .scalar "b" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- Three-element sequence
private def threeSeq : YamlValue := .sequence .flow #[mkScalar "a", mkScalar "b", mkScalar "c"]
#guard emit threeSeq == "[\"a\", \"b\", \"c\"]"
#guard scanTokenTypes (emit threeSeq) == some [.streamStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowEntry, .scalar "b" .doubleQuoted, .flowEntry, .scalar "c" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- Single-pair mapping
private def singleMap : YamlValue := .mapping .flow #[(mkScalar "k", mkScalar "v")]
#guard emit singleMap == "{\"k\": \"v\"}"
#guard scanTokenTypes (emit singleMap) == some [.streamStart, .flowMappingStart, .key, .scalar "k" .doubleQuoted, .value, .scalar "v" .doubleQuoted, .flowMappingEnd, .streamEnd]

-- Two-pair mapping
private def twoMap : YamlValue := .mapping .flow #[(mkScalar "a", mkScalar "1"), (mkScalar "b", mkScalar "2")]
#guard emit twoMap == "{\"a\": \"1\", \"b\": \"2\"}"
#guard scanTokenTypes (emit twoMap) == some [.streamStart, .flowMappingStart, .key, .scalar "a" .doubleQuoted, .value, .scalar "1" .doubleQuoted, .flowEntry, .key, .scalar "b" .doubleQuoted, .value, .scalar "2" .doubleQuoted, .flowMappingEnd, .streamEnd]

-- Nested: seq with seqs
private def nestedSeq : YamlValue := .sequence .flow #[.sequence .flow #[mkScalar "a"], .sequence .flow #[mkScalar "b"]]
#guard emit nestedSeq == "[[\"a\"], [\"b\"]]"
#guard scanTokenTypes (emit nestedSeq) == some [.streamStart, .flowSequenceStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowSequenceEnd, .flowEntry, .flowSequenceStart, .scalar "b" .doubleQuoted, .flowSequenceEnd, .flowSequenceEnd, .streamEnd]

-- Map containing sequence value
private def mapWithSeq : YamlValue := .mapping .flow #[(mkScalar "items", .sequence .flow #[mkScalar "x", mkScalar "y"])]
#guard scanTokenTypes (emit mapWithSeq) == some [.streamStart, .flowMappingStart, .key, .scalar "items" .doubleQuoted, .value, .flowSequenceStart, .scalar "x" .doubleQuoted, .flowEntry, .scalar "y" .doubleQuoted, .flowSequenceEnd, .flowMappingEnd, .streamEnd]

-- Deeply nested
private def deepNest : YamlValue := .sequence .flow #[.mapping .flow #[(mkScalar "a", .sequence .flow #[mkScalar "b", mkScalar "c"])]]
#guard scanTokenTypes (emit deepNest) == some [.streamStart, .flowSequenceStart, .flowMappingStart, .key, .scalar "a" .doubleQuoted, .value, .flowSequenceStart, .scalar "b" .doubleQuoted, .flowEntry, .scalar "c" .doubleQuoted, .flowSequenceEnd, .flowMappingEnd, .flowSequenceEnd, .streamEnd]

-- Escaped content in flow collections
private def seqWithEscapes : YamlValue := .sequence .flow #[mkScalar "line1\nline2", mkScalar "tab\there"]
#guard scanTokenTypes (emit seqWithEscapes) == some [.streamStart, .flowSequenceStart, .scalar "line1\nline2" .doubleQuoted, .flowEntry, .scalar "tab\there" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- UTF-8 content in flow collections
private def seqWithUtf8 : YamlValue := .sequence .flow #[mkScalar "αβ", mkScalar "日本"]
#guard scanTokenTypes (emit seqWithUtf8) == some [.streamStart, .flowSequenceStart, .scalar "αβ" .doubleQuoted, .flowEntry, .scalar "日本" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- Mapping with escape chars in keys and values
private def mapWithEscapes : YamlValue := .mapping .flow #[(mkScalar "key\n1", mkScalar "val\t1")]
#guard scanTokenTypes (emit mapWithEscapes) == some [.streamStart, .flowMappingStart, .key, .scalar "key\n1" .doubleQuoted, .value, .scalar "val\t1" .doubleQuoted, .flowMappingEnd, .streamEnd]

end Lean4Yaml.Proofs.ScannerFlowCollection
