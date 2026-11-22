/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.Whitespace


public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-! # `line` across preprocessing (DOCS item 9k)

Item 9k's three §6.9 tests read `s.line` and compare it with the line a token
was emitted on.  To *use* one of them in a proof you need the fact that a run of
`skipToContentLoop` which crossed no break left the line alone — and "crossed no
break" is not a hypothesis anyone was carrying.

It does not have to be.  The scanner already records it: `consumeNewline` sets
`needIndentCheck := true` on every break it consumes, and **nothing inside
`skipToContentLoop` ever clears it** — the clearing happens one level up, in
`scanNextToken_preprocess`, after the loop has returned.  So the flag on the
loop's own output is a witness that a break was crossed, and

    skipToContentLoop s fuel = .ok s'  →  s'.needIndentCheck = false
                                      →  s'.line = s.line

is provable with no character-level reasoning at all.  §1 and §2 are the
`_preserves_line` / `_preserves_needIndentCheck` families the induction needs,
cloned from the `_preserves_flowStack` family in
`ScannerFlowStackPreservation.lean`; §3 is the pair of results.

**Why the whitespace helpers preserve the line.**  `skipSpacesLoop` advances only
on `' '` and `skipWhitespaceLoop` only on `isWhiteSpaceBool`, neither of which is
`b-char` ([26] is `\n` or `\r`), and `collectCommentTextLoop` stops *at* a break
rather than consuming it.  `advance` moves the line only on those two
characters, so all three are line-transparent and `consumeNewline` is the loop's
single line-mover. -/

namespace L4YAML.Scanner

open L4YAML
open L4YAML.CharPredicates

/-! ## §1  `line` transparency of the non-break helpers -/

/-- `advance` moves the line only on `\n`/`\r`. -/
lemma advance_preserves_line_of_ne_break (s : ScannerState) (c : Char)
    (hp : s.peek? = some c) (hn : c ≠ '\n') (hr : c ≠ '\r') :
    s.advance.line = s.line := by
  have hlt : s.offset < s.inputEnd := by
    unfold ScannerState.peek? at hp
    split at hp
    · assumption
    · exact absurd hp (by simp)
  have hc : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
    unfold ScannerState.peek? at hp; rw [ite_eq_left hlt] at hp; injection hp
  unfold ScannerState.advance
  rw [ite_eq_left hlt]
  dsimp only []
  rw [hc, ite_eq_right (by simpa using hn), ite_eq_right (by simpa using hr)]

lemma skipSpacesLoop_preserves_line (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).line = s.line := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop
    split
    · rename_i hp
      rw [ih, advance_preserves_line_of_ne_break s ' ' hp (by decide) (by decide)]
    · rfl

lemma skipSpaces_preserves_line (s : ScannerState) :
    (skipSpaces s).line = s.line := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_line s _

lemma skipWhitespaceLoop_preserves_line (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).line = s.line := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop
    split
    · rename_i c hp
      split
      · rename_i hw
        -- `s-white` is space or tab; neither is `b-char`.
        have hn : c ≠ '\n' := by intro h; rw [h] at hw; exact absurd hw (by decide)
        have hr : c ≠ '\r' := by intro h; rw [h] at hw; exact absurd hw (by decide)
        rw [ih, advance_preserves_line_of_ne_break s c hp hn hr]
      · rfl
    · rfl

lemma skipWhitespace_preserves_line (s : ScannerState) :
    (skipWhitespace s).line = s.line := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_line s _

lemma collectCommentTextLoop_preserves_line (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.line = s.line := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ _ ih =>
    unfold collectCommentTextLoop
    split
    · rename_i c hp
      split
      · rfl
      · rename_i hb
        have hn : c ≠ '\n' := by intro h; rw [h] at hb; exact absurd hb (by decide)
        have hr : c ≠ '\r' := by intro h; rw [h] at hb; exact absurd hb (by decide)
        rw [ih, advance_preserves_line_of_ne_break s c hp hn hr]
    · rfl

lemma skipToContentComment_preserves_line (s : ScannerState) :
    (skipToContentComment s).line = s.line := by
  unfold skipToContentComment
  split
  · rename_i hp
    simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_line,
            advance_preserves_line_of_ne_break s '#' hp (by decide) (by decide)]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_line,
            advance_preserves_line_of_ne_break s '#' hp (by decide) (by decide)]
      · rfl
  · rfl

lemma skipToContentWs_preserves_line (s s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.line = s.line := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_preserves_line, skipSpaces_preserves_line]
        · split at h
          · simp at h; rw [← h, skipWhitespace_preserves_line, skipSpaces_preserves_line]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_line, skipSpaces_preserves_line]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_preserves_line, skipSpaces_preserves_line]
      · simp at h; rw [← h, skipSpaces_preserves_line]
    · simp at h; rw [← h, skipWhitespace_preserves_line, skipSpaces_preserves_line]
  · simp at h; rw [← h, skipWhitespace_preserves_line]

/-! ## §2  `needIndentCheck` is set by `consumeNewline` and cleared by nothing

    The helpers of §1 all reach the state through `advance`, which is a record
    update on `offset`/`line`/`col` alone. -/

lemma advance_preserves_needIndentCheck (s : ScannerState) :
    s.advance.needIndentCheck = s.needIndentCheck := by
  unfold ScannerState.advance; dsimp only []
  split <;> (try split) <;> (try split) <;> rfl

lemma skipSpacesLoop_preserves_needIndentCheck (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).needIndentCheck = s.needIndentCheck := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih => unfold skipSpacesLoop; split
                 · rw [ih, advance_preserves_needIndentCheck]
                 · rfl

lemma skipSpaces_preserves_needIndentCheck (s : ScannerState) :
    (skipSpaces s).needIndentCheck = s.needIndentCheck := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_needIndentCheck s _

lemma skipWhitespaceLoop_preserves_needIndentCheck (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).needIndentCheck = s.needIndentCheck := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih => unfold skipWhitespaceLoop; split
                 · split
                   · rw [ih, advance_preserves_needIndentCheck]
                   · rfl
                 · rfl

lemma skipWhitespace_preserves_needIndentCheck (s : ScannerState) :
    (skipWhitespace s).needIndentCheck = s.needIndentCheck := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_needIndentCheck s _

lemma collectCommentTextLoop_preserves_needIndentCheck (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.needIndentCheck = s.needIndentCheck := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ _ ih => unfold collectCommentTextLoop; split
                 · split
                   · rfl
                   · rw [ih, advance_preserves_needIndentCheck]
                 · rfl

lemma skipToContentComment_preserves_needIndentCheck (s : ScannerState) :
    (skipToContentComment s).needIndentCheck = s.needIndentCheck := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_needIndentCheck,
            advance_preserves_needIndentCheck]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_needIndentCheck,
            advance_preserves_needIndentCheck]
      · rfl
  · rfl

lemma skipToContentWs_preserves_needIndentCheck (s s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.needIndentCheck = s.needIndentCheck := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h
          rw [← h, skipWhitespace_preserves_needIndentCheck,
              skipSpaces_preserves_needIndentCheck]
        · split at h
          · simp at h
            rw [← h, skipWhitespace_preserves_needIndentCheck,
                skipSpaces_preserves_needIndentCheck]
          · split at h
            · simp at h
              rw [← h, skipWhitespace_preserves_needIndentCheck,
                  skipSpaces_preserves_needIndentCheck]
            · simp at h
        · simp at h
          rw [← h, skipWhitespace_preserves_needIndentCheck,
              skipSpaces_preserves_needIndentCheck]
      · simp at h; rw [← h, skipSpaces_preserves_needIndentCheck]
    · simp at h
      rw [← h, skipWhitespace_preserves_needIndentCheck,
          skipSpaces_preserves_needIndentCheck]
  · simp at h; rw [← h, skipWhitespace_preserves_needIndentCheck]

/-- The loop's single line-mover raises the flag.  `consumeNewline`'s
    fall-through arm (`| _ => s`) is unreachable here because the caller has
    already tested `isLineBreakBool` on the peeked character. -/
lemma consumeNewline_needIndentCheck_of_break (s : ScannerState) (c : Char)
    (hp : s.peek? = some c) (hb : isLineBreakBool c = true) :
    (consumeNewline s).needIndentCheck = true := by
  have hlf : c = '\n' ∨ c = '\r' := by
    simpa only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
      Bool.or_eq_true, beq_iff_eq] using hb
  unfold consumeNewline
  rcases hlf with h | h <;> subst h <;> rw [hp]
  · -- LF: the arm's own record update raises the flag.
    split
    · rfl
    · rename_i heq; exact absurd heq (by simp)
    · rename_i hne _; exact absurd rfl hne
  · -- CR: both arms of the CRLF test raise it.
    split
    · rename_i heq; exact absurd heq (by simp)
    · dsimp only []; split <;> rfl
    · rename_i _ hne; exact absurd rfl hne

/-! ## §3  The two results -/

/-- Once raised, the flag survives the rest of the loop. -/
lemma skipToContentLoop_needIndentCheck_mono (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') (hs : s.needIndentCheck = true) :
    s'.needIndentCheck = true := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]; exact hs
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      have h1 : s1.needIndentCheck = true := by
        rw [skipToContentWs_preserves_needIndentCheck s s1 hws]; exact hs
      simp only [] at h
      split at h
      · split at h
        · split at h
          · exact ih _ h (by simp; exact consumeNewline_preserves_needIndentCheck_true h1)
          · exact ih _ h (consumeNewline_preserves_needIndentCheck_true h1)
        · simp at h; rw [← h, skipToContentComment_preserves_needIndentCheck]; exact h1
      · simp at h; rw [← h, skipToContentComment_preserves_needIndentCheck]; exact h1
where
  /-- `consumeNewline` only ever sets the flag, so `true` in gives `true` out. -/
  consumeNewline_preserves_needIndentCheck_true {t : ScannerState}
      (ht : t.needIndentCheck = true) :
      (consumeNewline (skipToContentComment t)).needIndentCheck = true := by
    unfold consumeNewline
    split
    · rfl
    · simp only []; split <;> rfl
    · rw [skipToContentComment_preserves_needIndentCheck]; exact ht

/-- …and so does the walk the scanner actually calls. -/
lemma skipToContent_needIndentCheck_mono {s s' : ScannerState}
    (h : skipToContent s = .ok s') (hs : s.needIndentCheck = true) :
    s'.needIndentCheck = true := by
  unfold skipToContent at h
  exact skipToContentLoop_needIndentCheck_mono s s' _ h hs

/-- **The transport (item 9k).**  A run of `skipToContentLoop` that leaves
    `needIndentCheck` clear consumed no `b-break`, and so left the line alone.

    This is the fact a same-line property test needs at its consumption site:
    the run held in the accumulation was emitted at some line, preprocessing ran,
    and the guard reads `s.line` — the two agree exactly when the flag is
    still down. -/
@[yaml_spec "6.7" 79 "s-l-comments", yaml_spec "5.4" 28 "b-break"]
lemma skipToContentLoop_line_eq_of_needIndentCheck (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') (hnic : s'.needIndentCheck = false) :
    s'.line = s.line := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · rename_i c hpk
        split at h
        · -- a break WAS consumed: the flag is up in `s'`, contradicting `hnic`
          rename_i hb
          exfalso
          have hup : (consumeNewline (skipToContentComment s1)).needIndentCheck = true :=
            consumeNewline_needIndentCheck_of_break _ c hpk hb
          split at h
          · have := skipToContentLoop_needIndentCheck_mono _ _ _ h (by simpa using hup)
            rw [this] at hnic; exact Bool.noConfusion hnic
          · have := skipToContentLoop_needIndentCheck_mono _ _ _ h hup
            rw [this] at hnic; exact Bool.noConfusion hnic
        · simp at h; rw [← h, skipToContentComment_preserves_line]
          exact skipToContentWs_preserves_line s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_line]
        exact skipToContentWs_preserves_line s s1 hws

/-- `skipToContent`'s form of the transport. -/
lemma skipToContent_line_eq_of_needIndentCheck (s s' : ScannerState)
    (h : skipToContent s = .ok s') (hnic : s'.needIndentCheck = false) :
    s'.line = s.line := by
  unfold skipToContent at h
  exact skipToContentLoop_line_eq_of_needIndentCheck s s' _ h hnic

end L4YAML.Scanner

end Blanket
