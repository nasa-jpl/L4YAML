/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.IndexedDispatch

/-! # `IndexedDispatch` — Phase 3 dispatcher-layer proofs (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6).

## Scope (Step 5b.1b.i)

State-helper cursor-preservation + offset-monotonicity infrastructure
for the dispatcher monotonicity lemmas in `5b.1b.ii`–`5b.1b.iv`.

The dispatcher functions in `Scanner/IndexedDispatch.lean` thread the
cursor through helpers that fall into two families:

- **Cursor-preserving** (`emit`, `emitAt`, `emitAtCursor`,
  `overwriteAtCursor`, `pushSequenceIndentIx`, `pushMappingIndentIx`,
  `unwindIndentsLoopIx`, `unwindIndentsIx`, `saveSimpleKeyIx`,
  `scanValuePrepareIx`) — the output `.cursor` is definitionally
  `s.cursor`.
- **Cursor-monotonic** (`advance`, `advanceN`, `skipSpacesS`,
  `skipWhitespaceS`, `skipToContentS`) — the output cursor's
  byte offset is `≥` the input's.

The cursor-level monotonicity lemmas (`consumeLineBreak_offset_monotonic`,
`skipCommentText_offset_monotonic`, `skipToContent_offset_monotonic`,
`skipWhitespace_offset_monotonic`, `skipSpaces_offset_monotonic`)
already exist in `Proofs/Scanner/IndexedWhitespace.lean` and
`Proofs/Scanner/IndexedIndent.lean`; this file lifts them to the
`ScannerStateIx` layer and adds the cursor-preservation lemmas above.

The one new cursor-level lemma is `IxCursor.advanceN_offset_monotonic`
(the multi-step advance was not needed by the whitespace / indent
proofs).

## Layout

1. `IxCursor.advanceN_offset_monotonic`.
2. `ScannerStateIx` cursor-preservation lemmas (token emission,
   indent-stack updates, simple-key save, value-prepare).
3. `ScannerStateIx` state-level offset-monotonicity lemmas for the
   skip-helpers (`skipSpacesS`, `skipWhitespaceS`, `skipToContentS`).

## What's not here (`5b.1b.ii`–`5b.1b.iv`)

- Per-dispatcher monotonicity (`scanBlockEntryIx_offset_monotonic`,
  etc.). These compose the lemmas above through the dispatcher
  shapes.
-/

namespace L4YAML.Indexed.IxCursor

/-- `advanceN` is monotonic on the byte offset. Chained
    `advance_offset_monotonic` via induction on `n`. -/
theorem advanceN_offset_monotonic {input : String} (c : IxCursor input) (n : Nat) :
    c.pos.offset ≤ (c.advanceN n).pos.offset := by
  induction n generalizing c with
  | zero => unfold advanceN; exact Nat.le_refl _
  | succ n' ih =>
    unfold advanceN
    exact Nat.le_trans (advance_offset_monotonic c) (ih c.advance)

end L4YAML.Indexed.IxCursor

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.Indexed

/-! ## `ScannerStateIx` — cursor-preservation lemmas

Token-emission and indent-stack updates do not move the cursor. The
proofs are `rfl` (structure update preserves unspecified fields) or
one-line `split`s. -/

namespace ScannerStateIx

@[simp] theorem emit_cursor {input : String} (s : ScannerStateIx input) (tok : YamlToken) :
    (s.emit tok).cursor = s.cursor := rfl

@[simp] theorem emitAt_cursor {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (h : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok h).cursor = s.cursor := rfl

@[simp] theorem emitAtCursor_cursor {input : String} (s : ScannerStateIx input)
    (sk : IxCursor input) (tok : YamlToken) :
    (s.emitAtCursor sk tok).cursor = s.cursor := rfl

@[simp] theorem overwriteAtCursor_cursor {input : String} (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken) :
    (s.overwriteAtCursor i sk tok).cursor = s.cursor := rfl

@[simp] theorem advance_cursor {input : String} (s : ScannerStateIx input) :
    s.advance.cursor = s.cursor.advance := rfl

theorem advance_offset_monotonic {input : String} (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ s.advance.cursor.pos.offset :=
  IxCursor.advance_offset_monotonic s.cursor

@[simp] theorem advanceN_cursor {input : String} (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).cursor = s.cursor.advanceN n := rfl

theorem advanceN_offset_monotonic {input : String} (s : ScannerStateIx input) (n : Nat) :
    s.cursor.pos.offset ≤ (s.advanceN n).cursor.pos.offset := by
  rw [advanceN_cursor]
  exact IxCursor.advanceN_offset_monotonic s.cursor n

@[simp] theorem pushSequenceIndentIx_cursor {input : String} (s : ScannerStateIx input)
    (col : Int) :
    (pushSequenceIndentIx s col).cursor = s.cursor := by
  unfold pushSequenceIndentIx
  split <;> rfl

@[simp] theorem pushMappingIndentIx_cursor {input : String} (s : ScannerStateIx input)
    (col : Int) :
    (pushMappingIndentIx s col).cursor = s.cursor := by
  unfold pushMappingIndentIx
  split <;> rfl

@[simp] theorem unwindIndentsLoopIx_cursor {input : String} (s : ScannerStateIx input)
    (col : Int) (fuel : Nat) :
    (unwindIndentsLoopIx s col fuel).cursor = s.cursor := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoopIx; rfl
  | succ fuel ih =>
    unfold unwindIndentsLoopIx
    split
    · exact ih _
    · rfl

@[simp] theorem unwindIndentsIx_cursor {input : String} (s : ScannerStateIx input)
    (col : Int) :
    (unwindIndentsIx s col).cursor = s.cursor :=
  unwindIndentsLoopIx_cursor s col s.indents.size

@[simp] theorem saveSimpleKeyIx_cursor {input : String} (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).cursor = s.cursor := by
  unfold saveSimpleKeyIx
  split
  · rfl
  · split <;> rfl

@[simp] theorem scanValuePrepareIx_cursor {input : String} (s : ScannerStateIx input) :
    (scanValuePrepareIx s).cursor = s.cursor := by
  unfold scanValuePrepareIx
  split
  · -- s.simpleKey.possible
    split
    · -- !s.inFlow
      split <;> rfl
    · -- inFlow
      rfl
  · split
    · -- s.explicitKeyLine.isSome
      rfl
    · -- else: pushMappingIndentIx s ... or s
      split
      · exact pushMappingIndentIx_cursor s s.cursor.pos.col
      · rfl

/-! ## `ScannerStateIx` — state-level offset monotonicity for skip-helpers

`skipSpacesS`, `skipWhitespaceS`, `skipToContentS` thread the cursor
through `skipSpaces` / `skipWhitespace` / `skipToContent`. Their
state-level monotonicity follows directly. -/

@[simp] theorem skipSpacesS_cursor {input : String} (s : ScannerStateIx input) :
    s.skipSpacesS.1.cursor = (L4YAML.Scanner.Indexed.skipSpaces s.cursor).1 := rfl

theorem skipSpacesS_offset_monotonic {input : String} (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ s.skipSpacesS.1.cursor.pos.offset := by
  rw [skipSpacesS_cursor]
  exact skipSpaces_offset_monotonic s.cursor

@[simp] theorem skipWhitespaceS_cursor {input : String} (s : ScannerStateIx input) :
    s.skipWhitespaceS.cursor = L4YAML.Scanner.Indexed.skipWhitespace s.cursor := rfl

theorem skipWhitespaceS_offset_monotonic {input : String} (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ s.skipWhitespaceS.cursor.pos.offset := by
  rw [skipWhitespaceS_cursor]
  exact skipWhitespace_offset_monotonic s.cursor

@[simp] theorem skipToContentS_cursor {input : String} (s : ScannerStateIx input) :
    s.skipToContentS.cursor = L4YAML.Scanner.Indexed.skipToContent s.cursor := rfl

theorem skipToContentS_offset_monotonic {input : String} (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ s.skipToContentS.cursor.pos.offset := by
  rw [skipToContentS_cursor]
  exact skipToContent_offset_monotonic s.cursor

end ScannerStateIx

end L4YAML.Scanner.Indexed
