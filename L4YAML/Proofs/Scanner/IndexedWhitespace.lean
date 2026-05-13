/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.IndexedScanner
import L4YAML.Proofs.Foundation.CharClass

/-! # `IndexedWhitespace` — Phase 3 character/whitespace spec proofs (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6).

This file lands the *bidirectional* proofs that bridge the runtime
recognisers in `Scanner.Indexed` to the YAML 1.2.2 spec predicates in
`Spec.CharPredicates`:

- **`peekIsX_iff`**: `peekIsX c = true ↔ (∃ ch, c.peek? = some ch ∧
  isXProp ch)` — soundness + completeness in one direction.

- **Monotonicity**: `skipSpaces` / `skipWhitespace` only advance the
  byte offset forward. Used in Step 3's indentation logic and in the
  loop-progress proofs of the dispatch layer.

- **`consumeLineBreak` case lemmas**: explicit characterisation of
  the three break forms (LF, CR-without-LF, CRLF) and the no-op
  default.

- **Termination correctness** (deferred from Step 2, closed here in
  Step 3): when the fuel parameter is at least `utf8ByteSize -
  offset`, both `skipSpacesLoop` and `skipWhitespaceLoop` return a
  cursor at a non-matching character or at end-of-input. Combined
  with `skipSpaces`/`skipWhitespace`'s entry-point fuel of
  `input.utf8ByteSize`, this gives the unconditional termination
  guarantee on `IxCursor input`.

- **Count = column delta** (Step 3): since `isIndentCharBool c =
  (c == ' ')` and `' '` is not a line-break character, advancing
  past an indent-char only bumps `col` (never `line`). Therefore
  `(skipSpaces c).1.pos.col = c.pos.col + (skipSpaces c).2` and
  `(skipSpaces c).1.pos.line = c.pos.line` — the count returned by
  `skipSpaces` is exactly the column delta. This is the form the
  Step 3 indent-stack invariant consumes.
-/

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.CharPredicates L4YAML.Indexed

/-! ## `peekIs*` ↔ spec bridge -/

theorem peekIsLineBreak_iff {input : String} (c : IxCursor input) :
    peekIsLineBreak c = true ↔ ∃ ch, c.peek? = some ch ∧ isLineBreakProp ch := by
  unfold peekIsLineBreak
  cases h : c.peek? with
  | none    => simp
  | some ch => simp [isLineBreak_iff]

theorem peekIsWhiteSpace_iff {input : String} (c : IxCursor input) :
    peekIsWhiteSpace c = true ↔ ∃ ch, c.peek? = some ch ∧ isWhiteSpaceProp ch := by
  unfold peekIsWhiteSpace
  cases h : c.peek? with
  | none    => simp
  | some ch => simp [isWhiteSpace_iff]

theorem peekIsBlank_iff {input : String} (c : IxCursor input) :
    peekIsBlank c = true ↔ ∃ ch, c.peek? = some ch ∧ isBlankProp ch := by
  unfold peekIsBlank
  cases h : c.peek? with
  | none    => simp
  | some ch => simp [isBlank_iff]

theorem peekIsIndentChar_iff {input : String} (c : IxCursor input) :
    peekIsIndentChar c = true ↔ ∃ ch, c.peek? = some ch ∧ isIndentCharProp ch := by
  unfold peekIsIndentChar
  cases h : c.peek? with
  | none    => simp
  | some ch => simp [isIndentChar_iff]

/-! ## `peekIs*` at end-of-input -/

theorem peekIsLineBreak_atEnd {input : String} (c : IxCursor input)
    (h : c.peek? = none) : peekIsLineBreak c = false := by
  unfold peekIsLineBreak; rw [h]

theorem peekIsWhiteSpace_atEnd {input : String} (c : IxCursor input)
    (h : c.peek? = none) : peekIsWhiteSpace c = false := by
  unfold peekIsWhiteSpace; rw [h]

theorem peekIsBlank_atEnd {input : String} (c : IxCursor input)
    (h : c.peek? = none) : peekIsBlank c = false := by
  unfold peekIsBlank; rw [h]

theorem peekIsIndentChar_atEnd {input : String} (c : IxCursor input)
    (h : c.peek? = none) : peekIsIndentChar c = false := by
  unfold peekIsIndentChar; rw [h]

/-! ## `peekIs*` implies cursor `hasMore` -/

theorem peekIsIndentChar_implies_hasMore {input : String} (c : IxCursor input)
    (h : peekIsIndentChar c = true) : c.pos.offset < input.utf8ByteSize := by
  unfold peekIsIndentChar at h
  if h' : c.pos.offset < input.utf8ByteSize then
    exact h'
  else
    have hpe : c.peek? = none :=
      (IxCursor.peek?_eq_none_iff c).mpr (Nat.le_of_not_lt h')
    rw [hpe] at h; exact absurd h (by decide)

theorem peekIsWhiteSpace_implies_hasMore {input : String} (c : IxCursor input)
    (h : peekIsWhiteSpace c = true) : c.pos.offset < input.utf8ByteSize := by
  unfold peekIsWhiteSpace at h
  if h' : c.pos.offset < input.utf8ByteSize then
    exact h'
  else
    have hpe : c.peek? = none :=
      (IxCursor.peek?_eq_none_iff c).mpr (Nat.le_of_not_lt h')
    rw [hpe] at h; exact absurd h (by decide)

/-! ## `skipSpaces` / `skipWhitespace` — offset monotonicity -/

theorem skipSpacesLoop_offset_monotonic {input : String} (c : IxCursor input)
    (fuel : Nat) :
    c.pos.offset ≤ (skipSpacesLoop c fuel).1.pos.offset := by
  induction fuel generalizing c with
  | zero =>
    unfold skipSpacesLoop; exact Nat.le_refl _
  | succ fuel ih =>
    unfold skipSpacesLoop
    split
    · -- indent-char branch: advance + recurse
      simp only
      exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance)
    · -- non-indent branch: cursor unchanged
      exact Nat.le_refl _

theorem skipSpaces_offset_monotonic {input : String} (c : IxCursor input) :
    c.pos.offset ≤ (skipSpaces c).1.pos.offset :=
  skipSpacesLoop_offset_monotonic c _

theorem skipWhitespaceLoop_offset_monotonic {input : String} (c : IxCursor input)
    (fuel : Nat) :
    c.pos.offset ≤ (skipWhitespaceLoop c fuel).pos.offset := by
  induction fuel generalizing c with
  | zero =>
    unfold skipWhitespaceLoop; exact Nat.le_refl _
  | succ fuel ih =>
    unfold skipWhitespaceLoop
    split
    · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance)
    · exact Nat.le_refl _

theorem skipWhitespace_offset_monotonic {input : String} (c : IxCursor input) :
    c.pos.offset ≤ (skipWhitespace c).pos.offset :=
  skipWhitespaceLoop_offset_monotonic c _

/-! ## `skipSpaces` — count and run boundary -/

/-- Zero-step base: at `fuel = 0`, `skipSpaces` returns the input
    cursor with count 0. -/
@[simp] theorem skipSpacesLoop_zero {input : String} (c : IxCursor input) :
    skipSpacesLoop c 0 = (c, 0) := by
  unfold skipSpacesLoop; rfl

/-- Non-indent shortcut: when the current char is not a space the loop
    returns `(c, 0)` immediately, regardless of remaining fuel. -/
theorem skipSpacesLoop_no_indent {input : String} (c : IxCursor input)
    (fuel : Nat) (h : peekIsIndentChar c = false) :
    skipSpacesLoop c (fuel + 1) = (c, 0) := by
  unfold skipSpacesLoop; simp [h]

/-! ## Termination — closes the Step 2 deferred obligation

When the fuel parameter is at least `utf8ByteSize - offset`, the
loop is guaranteed to exit with the cursor at a non-matching
character (or at end-of-input). The bound is tight: each iteration
that advances strictly increases `offset` by at least one
(`advance_offset_lt_of_hasMore`), so after at most
`utf8ByteSize - offset` iterations the cursor reaches end-of-input
and the next peek fails. -/

theorem skipSpacesLoop_terminates {input : String} (c : IxCursor input)
    (fuel : Nat) (hFuel : input.utf8ByteSize - c.pos.offset ≤ fuel) :
    peekIsIndentChar (skipSpacesLoop c fuel).1 = false := by
  induction fuel generalizing c with
  | zero =>
    have hLe : input.utf8ByteSize ≤ c.pos.offset := by omega
    have hpe : c.peek? = none := (IxCursor.peek?_eq_none_iff c).mpr hLe
    rw [skipSpacesLoop_zero]
    exact peekIsIndentChar_atEnd c hpe
  | succ fuel ih =>
    unfold skipSpacesLoop
    split
    · rename_i hPeek
      simp only
      have hMore : c.pos.offset < input.utf8ByteSize :=
        peekIsIndentChar_implies_hasMore c hPeek
      have hAdv : c.pos.offset < c.advance.pos.offset :=
        IxCursor.advance_offset_lt_of_hasMore c hMore
      have hFuel' : input.utf8ByteSize - c.advance.pos.offset ≤ fuel := by omega
      exact ih c.advance hFuel'
    · rename_i hPeek
      simp only
      match h' : peekIsIndentChar c with
      | false => rfl
      | true  => exact absurd h' hPeek

theorem skipSpaces_terminates {input : String} (c : IxCursor input) :
    peekIsIndentChar (skipSpaces c).1 = false := by
  unfold skipSpaces
  exact skipSpacesLoop_terminates c _ (Nat.sub_le _ _)

theorem skipWhitespaceLoop_terminates {input : String} (c : IxCursor input)
    (fuel : Nat) (hFuel : input.utf8ByteSize - c.pos.offset ≤ fuel) :
    peekIsWhiteSpace (skipWhitespaceLoop c fuel) = false := by
  induction fuel generalizing c with
  | zero =>
    have hLe : input.utf8ByteSize ≤ c.pos.offset := by omega
    have hpe : c.peek? = none := (IxCursor.peek?_eq_none_iff c).mpr hLe
    unfold skipWhitespaceLoop
    exact peekIsWhiteSpace_atEnd c hpe
  | succ fuel ih =>
    unfold skipWhitespaceLoop
    split
    · rename_i hPeek
      have hMore : c.pos.offset < input.utf8ByteSize :=
        peekIsWhiteSpace_implies_hasMore c hPeek
      have hAdv : c.pos.offset < c.advance.pos.offset :=
        IxCursor.advance_offset_lt_of_hasMore c hMore
      have hFuel' : input.utf8ByteSize - c.advance.pos.offset ≤ fuel := by omega
      exact ih c.advance hFuel'
    · rename_i hPeek
      match h' : peekIsWhiteSpace c with
      | false => rfl
      | true  => exact absurd h' hPeek

theorem skipWhitespace_terminates {input : String} (c : IxCursor input) :
    peekIsWhiteSpace (skipWhitespace c) = false := by
  unfold skipWhitespace
  exact skipWhitespaceLoop_terminates c _ (Nat.sub_le _ _)

/-! ## Count = column delta — used by Step 3's indent-stack invariant

An indent character is exactly `' '` (per `isIndentCharBool`), which
is *not* a line-break. So advancing across a space leaves `line`
unchanged and bumps `col` by one. The count returned by `skipSpaces`
is therefore exactly the column delta. -/

/-- Advancing past an indent-char bumps `col` by 1 and leaves `line`
    unchanged. Builds on `IxCursor.advance`'s line/col update rule. -/
theorem advance_indent_col_succ {input : String} (c : IxCursor input)
    (h : peekIsIndentChar c = true) :
    c.advance.pos.col = c.pos.col + 1 ∧ c.advance.pos.line = c.pos.line := by
  have hMore : c.pos.offset < input.utf8ByteSize :=
    peekIsIndentChar_implies_hasMore c h
  have hCh : String.Pos.Raw.get input ⟨c.pos.offset⟩ = ' ' := by
    unfold peekIsIndentChar IxCursor.peek? at h
    rw [if_pos hMore] at h
    simpa [isIndentCharBool] using h
  unfold IxCursor.advance
  simp [dif_pos hMore, hCh]

theorem skipSpacesLoop_col_eq_count {input : String} (c : IxCursor input)
    (fuel : Nat) :
    (skipSpacesLoop c fuel).1.pos.col =
        c.pos.col + (skipSpacesLoop c fuel).2 ∧
    (skipSpacesLoop c fuel).1.pos.line = c.pos.line := by
  induction fuel generalizing c with
  | zero =>
    rw [skipSpacesLoop_zero]
    refine ⟨?_, rfl⟩
    show c.pos.col = c.pos.col + 0
    omega
  | succ fuel ih =>
    unfold skipSpacesLoop
    split
    · rename_i hPeek
      simp only
      have ⟨hCol, hLine⟩ := advance_indent_col_succ c hPeek
      have ⟨ihCol, ihLine⟩ := ih c.advance
      refine ⟨?_, ?_⟩
      · rw [ihCol, hCol]; omega
      · rw [ihLine, hLine]
    · -- false branch: result is (c, 0)
      refine ⟨?_, rfl⟩
      show c.pos.col = c.pos.col + 0
      omega

theorem skipSpaces_col_eq_count {input : String} (c : IxCursor input) :
    (skipSpaces c).1.pos.col = c.pos.col + (skipSpaces c).2 ∧
    (skipSpaces c).1.pos.line = c.pos.line :=
  skipSpacesLoop_col_eq_count c _

/-! ## `consumeLineBreak` — case lemmas -/

theorem consumeLineBreak_LF {input : String} (c : IxCursor input)
    (h : c.peek? = some '\n') : consumeLineBreak c = c.advance := by
  simp [consumeLineBreak, h]

theorem consumeLineBreak_CR_no_LF {input : String} (c : IxCursor input)
    (hCR : c.peek? = some '\r') (hNotLF : c.peekAt? 1 ≠ some '\n') :
    consumeLineBreak c = c.advance := by
  simp [consumeLineBreak, hCR, hNotLF]

theorem consumeLineBreak_CRLF_offset {input : String} (c : IxCursor input)
    (hCR : c.peek? = some '\r') (hLF : c.peekAt? 1 = some '\n') :
    (consumeLineBreak c).pos.offset = c.advance.advance.pos.offset := by
  simp [consumeLineBreak, hCR, hLF]

theorem consumeLineBreak_CRLF_line {input : String} (c : IxCursor input)
    (hCR : c.peek? = some '\r') (hLF : c.peekAt? 1 = some '\n') :
    (consumeLineBreak c).pos.line = c.advance.pos.line := by
  simp [consumeLineBreak, hCR, hLF]

theorem consumeLineBreak_CRLF_col {input : String} (c : IxCursor input)
    (hCR : c.peek? = some '\r') (hLF : c.peekAt? 1 = some '\n') :
    (consumeLineBreak c).pos.col = 0 := by
  simp [consumeLineBreak, hCR, hLF]

theorem consumeLineBreak_atEnd {input : String} (c : IxCursor input)
    (h : c.peek? = none) : consumeLineBreak c = c := by
  simp [consumeLineBreak, h]

/-- `consumeLineBreak` is a no-op when the current character is neither
    LF nor CR. Common case lemma used by the dispatch layer. -/
theorem consumeLineBreak_other_char {input : String} (c : IxCursor input)
    {ch : Char} (hp : c.peek? = some ch) (hLF : ch ≠ '\n') (hCR : ch ≠ '\r') :
    consumeLineBreak c = c := by
  unfold consumeLineBreak; rw [hp]
  have hb1 : (ch == '\n') = false := by simp [hLF]
  have hb2 : (ch == '\r') = false := by simp [hCR]
  simp [hb1, hb2]

theorem consumeLineBreak_no_op {input : String} (c : IxCursor input)
    (hCh : ∀ ch, c.peek? = some ch → ch ≠ '\n' ∧ ch ≠ '\r') :
    consumeLineBreak c = c := by
  cases hp : c.peek? with
  | none    => exact consumeLineBreak_atEnd c hp
  | some ch =>
    have ⟨hne1, hne2⟩ := hCh ch hp
    exact consumeLineBreak_other_char c hp hne1 hne2

/-! ## Offset monotonicity for `consumeLineBreak` -/

theorem consumeLineBreak_offset_monotonic {input : String} (c : IxCursor input) :
    c.pos.offset ≤ (consumeLineBreak c).pos.offset := by
  cases hp : c.peek? with
  | none =>
    rw [consumeLineBreak_atEnd c hp]; exact Nat.le_refl _
  | some ch =>
    by_cases hLF : ch = '\n'
    · subst hLF
      rw [consumeLineBreak_LF c hp]
      exact IxCursor.advance_offset_monotonic c
    by_cases hCR : ch = '\r'
    · subst hCR
      by_cases hCRLF : c.peekAt? 1 = some '\n'
      · have hOff : (consumeLineBreak c).pos.offset = c.advance.advance.pos.offset :=
          consumeLineBreak_CRLF_offset c hp hCRLF
        rw [hOff]
        exact Nat.le_trans (IxCursor.advance_offset_monotonic c)
          (IxCursor.advance_offset_monotonic c.advance)
      · rw [consumeLineBreak_CR_no_LF c hp hCRLF]
        exact IxCursor.advance_offset_monotonic c
    · rw [consumeLineBreak_other_char c hp hLF hCR]; exact Nat.le_refl _

end L4YAML.Scanner.Indexed
