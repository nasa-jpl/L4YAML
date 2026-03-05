import Lean4Yaml.Scanner

open Lean4Yaml.Scanner

-- All 4 helper theorems are already proven in ScannerCorrectness.
-- Let's re-prove them locally to keep this self-contained test file.

theorem advance_preserves_tokens' (s : ScannerState) :
    s.advance.tokens = s.tokens := by
  unfold ScannerState.advance
  simp only [↓reduceIte]
  split <;> (split <;> rfl)

theorem consumeNewline_preserves_tokens' (s : ScannerState) :
    (consumeNewline s).tokens = s.tokens := by
  unfold consumeNewline
  split
  · exact advance_preserves_tokens' s
  · dsimp only []
    split
    · rw [advance_preserves_tokens', advance_preserves_tokens']
    · exact advance_preserves_tokens' s
  · rfl

theorem skipSpaces_preserves_tokens' (s : ScannerState) :
    (skipSpaces s).tokens = s.tokens := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop
    split
    · rw [IH, advance_preserves_tokens']
    · rfl

theorem skipWhitespace_preserves_tokens' (s : ScannerState) :
    (skipWhitespace s).tokens = s.tokens := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop
    split
    · split
      · rw [IH, advance_preserves_tokens']
      · rfl
    · rfl

theorem skipToEndOfLine_preserves_tokens' (s : ScannerState) :
    (skipToEndOfLine s).tokens = s.tokens := by
  unfold skipToEndOfLine
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ fuel' IH =>
    unfold skipToEndOfLineLoop
    split
    · split
      · rfl
      · rw [IH, advance_preserves_tokens']
    · rfl

-- Now the main theorem
theorem skipToContentLoop_preserves_tokens (s : ScannerState) (s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.tokens = s.tokens := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h
    rw [h]
  | succ fuel' IH =>
    unfold skipToContentLoop at h
    simp only [Nat.add_eq, Nat.add_zero] at h
    -- The body is a do-block. After unfolding, h is a complex hypothesis.
    -- The key insight: every operation in the body preserves tokens.
    -- Let's try to simplify step by step.
    sorry

#check @skipToContentLoop_preserves_tokens
