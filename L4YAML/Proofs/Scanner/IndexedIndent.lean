/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedWhitespace

/-! # `IndexedIndent` — Phase 3 indentation / line-break dispatch proofs (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6).

This file extends `IndexedWhitespace.lean` to cover the four
Step 3 productions listed in the blueprint:

- **`s-indent(n)`** (§6.1 [63]) — measured by `skipSpaces`. The
  bidirectional bridge is *already* in `IndexedWhitespace` as
  `skipSpaces_col_eq_count` (Step 2/3 hand-off): the count
  returned equals the column delta, so the indent at the *start*
  of a line is `(skipSpaces c).2` when `c.pos.col = 0`.

- **`b-break`** (§5.4 [28]) — `consumeLineBreak`, already
  covered by case lemmas in `IndexedWhitespace.lean`.

- **`b-non-content`** (§5.4 [30]) — definitionally `b-break`
  (the YAML 1.2.2 grammar gives it the same right-hand side,
  with a different non-terminal label for non-content contexts
  such as inside `c-l-folded` headers). Lemmas about
  `consumeLineBreak` apply unchanged.

- **`s-l-comments`** (§6.7 [79]) — composite of
  `skipWhitespace`, optional `'#'`-introduced
  `c-nb-comment-text`, and a `b-break`. Proven below in two
  pieces: `skipCommentText_*` (the comment body) and
  `skipToContent_*` (the multi-line loop).

## What's *not* here

- Indent-stack data structure and invariants (handled in Step 4
  alongside scalar lexing — block scalars read the indent
  directly).
- Tab-as-indentation error reporting (§6.1) — moves with the
  indent-stack in Step 4.
- The legacy `needIndentCheck` flag has no analogue: `skipSpaces`
  is called explicitly at the points where indent measurement is
  needed, rather than tracked via mutable state.
-/

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.CharPredicates L4YAML.Indexed

/-! ## `skipCommentTextLoop` — offset monotonicity & termination -/

theorem skipCommentTextLoop_offset_monotonic {input : String} (c : IxCursor input)
    (fuel : Nat) :
    c.pos.offset ≤ (skipCommentTextLoop c fuel).pos.offset := by
  induction fuel generalizing c with
  | zero =>
    unfold skipCommentTextLoop; exact Nat.le_refl _
  | succ fuel ih =>
    unfold skipCommentTextLoop
    split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance)

theorem skipCommentText_offset_monotonic {input : String} (c : IxCursor input) :
    c.pos.offset ≤ (skipCommentText c).pos.offset :=
  skipCommentTextLoop_offset_monotonic c _

/-- `skipCommentText` consumes until either (a) the cursor reaches
    a line-break character or (b) end-of-input. The fuel bound
    matches `skipWhitespaceLoop_terminates` — each advancing
    iteration strictly increases the byte offset. -/
theorem skipCommentTextLoop_terminates {input : String} (c : IxCursor input)
    (fuel : Nat) (hFuel : input.utf8ByteSize - c.pos.offset ≤ fuel) :
    peekIsLineBreak (skipCommentTextLoop c fuel) = true ∨
        (skipCommentTextLoop c fuel).peek? = none := by
  induction fuel generalizing c with
  | zero =>
    have hLe : input.utf8ByteSize ≤ c.pos.offset := by omega
    have hpe : c.peek? = none := (IxCursor.peek?_eq_none_iff c).mpr hLe
    unfold skipCommentTextLoop
    exact Or.inr hpe
  | succ fuel ih =>
    unfold skipCommentTextLoop
    split
    · rename_i hLB
      exact Or.inl hLB
    · split
      · rename_i hpe
        exact Or.inr hpe
      · rename_i ch hpe
        -- ch is the current character; we advance and recurse.
        have hMore : c.pos.offset < input.utf8ByteSize := by
          if h' : c.pos.offset < input.utf8ByteSize then
            exact h'
          else
            have hNone : c.peek? = none :=
              (IxCursor.peek?_eq_none_iff c).mpr (Nat.le_of_not_lt h')
            rw [hNone] at hpe
            contradiction
        have hAdv : c.pos.offset < c.advance.pos.offset :=
          IxCursor.advance_offset_lt_of_hasMore c hMore
        have hFuel' : input.utf8ByteSize - c.advance.pos.offset ≤ fuel := by omega
        exact ih c.advance hFuel'

theorem skipCommentText_terminates {input : String} (c : IxCursor input) :
    peekIsLineBreak (skipCommentText c) = true ∨ (skipCommentText c).peek? = none := by
  unfold skipCommentText
  exact skipCommentTextLoop_terminates c _ (Nat.sub_le _ _)

/-! ## `skipToContentLoop` — offset monotonicity & termination -/

theorem skipToContentLoop_offset_monotonic {input : String} (c : IxCursor input)
    (fuel : Nat) :
    c.pos.offset ≤ (skipToContentLoop c fuel).pos.offset := by
  induction fuel generalizing c with
  | zero =>
    unfold skipToContentLoop; exact Nat.le_refl _
  | succ fuel ih =>
    unfold skipToContentLoop
    -- After skipWhitespace, then case on peek?.
    have hSW : c.pos.offset ≤ (skipWhitespace c).pos.offset :=
      skipWhitespace_offset_monotonic c
    split
    · -- peek? = none, return c1 = skipWhitespace c
      exact hSW
    · split
      · -- '#' — recurse
        rename_i ch _ hHash
        have hCT : (skipWhitespace c).advance.pos.offset ≤
            (skipCommentText (skipWhitespace c).advance).pos.offset :=
          skipCommentText_offset_monotonic (skipWhitespace c).advance
        have hAdv :
            (skipWhitespace c).pos.offset ≤ (skipWhitespace c).advance.pos.offset :=
          IxCursor.advance_offset_monotonic _
        have hLB :
            (skipCommentText (skipWhitespace c).advance).pos.offset ≤
            (consumeLineBreak (skipCommentText (skipWhitespace c).advance)).pos.offset :=
          consumeLineBreak_offset_monotonic _
        have hRec :
            (consumeLineBreak (skipCommentText (skipWhitespace c).advance)).pos.offset ≤
            (skipToContentLoop
              (consumeLineBreak (skipCommentText (skipWhitespace c).advance))
              fuel).pos.offset :=
          ih _
        omega
      · split
        · -- line break — recurse
          have hLB : (skipWhitespace c).pos.offset ≤
              (consumeLineBreak (skipWhitespace c)).pos.offset :=
            consumeLineBreak_offset_monotonic _
          have hRec :
              (consumeLineBreak (skipWhitespace c)).pos.offset ≤
              (skipToContentLoop (consumeLineBreak (skipWhitespace c)) fuel).pos.offset :=
            ih _
          omega
        · -- content — stop at c1
          exact hSW

theorem skipToContent_offset_monotonic {input : String} (c : IxCursor input) :
    c.pos.offset ≤ (skipToContent c).pos.offset :=
  skipToContentLoop_offset_monotonic c _

/-! ## `skipToContent` — bidirectional spec at the cursor

The "settles at content or EOF" claim (a strict-fuel termination
result) is most naturally stated at the cursor *entry point* level
in Step 4, where it composes with the dispatch-loop indent
invariant. Here we land two single-step bidirectional lemmas that
characterise `skipToContent`'s behaviour locally:

- **`skipToContent_at_content`** (idempotence on content):
  when the cursor already sits at a content character (not
  whitespace, not line-break, not `'#'`), `skipToContent` is the
  identity. This is the *completeness* direction for the
  "settled" predicate.

- **`skipToContent_atEnd`**: when the cursor is at EOF,
  `skipToContent` is the identity.

Together with `skipCommentText_terminates`,
`consumeLineBreak_*`, and `skipToContent_offset_monotonic`, this
provides the cursor-local invariants Step 4 will consume; the
*global* termination of `skipToContent` (cursor settles at
content / EOF in finitely many iterations) is exactly the strict-
fuel argument and folds in with the dispatch-loop measure of
Step 4. -/

/-- `skipToContent` is a no-op at end-of-input. -/
theorem skipToContent_atEnd {input : String} (c : IxCursor input)
    (h : c.peek? = none) : skipToContent c = c := by
  unfold skipToContent skipToContentLoop
  -- Need to show: after fuel+1, with peek? = none, the result is c.
  -- First: skipWhitespace c = c when peek? = none.
  have hSW : skipWhitespace c = c := by
    unfold skipWhitespace skipWhitespaceLoop
    -- For any fuel, skipWhitespaceLoop c fuel = c when peekIsWhiteSpace c = false.
    have hpw : peekIsWhiteSpace c = false := peekIsWhiteSpace_atEnd c h
    cases input.utf8ByteSize with
    | zero => rfl
    | succ n => simp [hpw]
  rw [hSW]
  rw [h]

/-- `skipToContent` is a no-op when the cursor sits at a content
    character — a `Char` that is not whitespace, not a line break,
    and not `'#'`. This is the *completeness* direction: the
    scanner consumes nothing when there is nothing to consume. -/
theorem skipToContent_at_content {input : String} (c : IxCursor input)
    {ch : Char} (hpe : c.peek? = some ch)
    (hWS : isWhiteSpaceBool ch = false)
    (hLB : isLineBreakBool ch = false)
    (hHash : ch ≠ '#') :
    skipToContent c = c := by
  -- First: skipWhitespace c = c (peek is not whitespace).
  have hSW : skipWhitespace c = c := by
    unfold skipWhitespace skipWhitespaceLoop
    have hpw : peekIsWhiteSpace c = false := by
      unfold peekIsWhiteSpace; rw [hpe]; exact hWS
    cases input.utf8ByteSize with
    | zero => rfl
    | succ n => simp [hpw]
  unfold skipToContent skipToContentLoop
  rw [hSW, hpe]
  have hHashBool : (ch == '#') = false := by
    simp [hHash]
  simp [hHashBool, hLB]

end L4YAML.Scanner.Indexed
