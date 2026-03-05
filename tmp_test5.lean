import Lean4Yaml.Scanner

open Lean4Yaml.Scanner

-- Helper lemmas (reproduced for this test file)
theorem advance_preserves_tokens' (s : ScannerState) :
    s.advance.tokens = s.tokens := by
  unfold ScannerState.advance; simp only [↓reduceIte]; split <;> (split <;> rfl)

theorem consumeNewline_preserves_tokens' (s : ScannerState) :
    (consumeNewline s).tokens = s.tokens := by
  unfold consumeNewline; split
  · exact advance_preserves_tokens' s
  · dsimp only []; split
    · rw [advance_preserves_tokens', advance_preserves_tokens']
    · exact advance_preserves_tokens' s
  · rfl

theorem skipSpaces_preserves_tokens' (s : ScannerState) :
    (skipSpaces s).tokens = s.tokens := by
  unfold skipSpaces; generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ IH => unfold skipSpacesLoop; split; · rw [IH, advance_preserves_tokens']; · rfl

theorem skipWhitespace_preserves_tokens' (s : ScannerState) :
    (skipWhitespace s).tokens = s.tokens := by
  unfold skipWhitespace; generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ IH =>
    unfold skipWhitespaceLoop; split
    · split; · rw [IH, advance_preserves_tokens']; · rfl
    · rfl

theorem skipToEndOfLine_preserves_tokens' (s : ScannerState) :
    (skipToEndOfLine s).tokens = s.tokens := by
  unfold skipToEndOfLine; generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ IH =>
    unfold skipToEndOfLineLoop; split
    · split; · rfl; · rw [IH, advance_preserves_tokens']
    · rfl

-- Main: try the match-based formulation with simp to close branches
set_option maxHeartbeats 2000000 in
theorem skipToContentLoop_preserves_tokens (s : ScannerState) (fuel : Nat) :
    match skipToContentLoop s fuel with
    | .ok s' => s'.tokens = s.tokens
    | .error _ => True := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop
    simp
  | succ fuel' IH =>
    unfold skipToContentLoop
    simp only []
    -- Try splitting on the first branch
    split
    · -- needIndentCheck = true
      simp only [skipSpaces_preserves_tokens', skipWhitespace_preserves_tokens',
                  skipToEndOfLine_preserves_tokens', consumeNewline_preserves_tokens']
      split  -- col ≤ currentIndent
      · split  -- peek = tab?
        · -- tab case
          simp only [skipWhitespace_preserves_tokens']
          split -- probe peek
          all_goals (try { split <;> simp_all [skipWhitespace_preserves_tokens', skipToEndOfLine_preserves_tokens', consumeNewline_preserves_tokens', IH] })
        · -- non-tab: fall through to comment
          sorry
        · sorry
      · sorry
    · -- needIndentCheck = false
      sorry

