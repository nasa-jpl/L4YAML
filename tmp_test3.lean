import Lean4Yaml.Scanner

open Lean4Yaml.Scanner

-- Reuse proven facts
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

-- The real question: what does the hypothesis look like after unfold?
-- Let me print it.
set_option maxHeartbeats 400000 in
theorem skipToContentLoop_preserves_tokens (s : ScannerState) (s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.tokens = s.tokens := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [h]
  | succ fuel' IH =>
    unfold skipToContentLoop at h
    -- Instead of trying to decompose the do-block in h,
    -- let's think about what function the body computes on tokens.
    -- The body: if needIndentCheck then ... else ...; match peek; etc.
    -- All paths either:
    --   (a) return .ok s'' where s''.tokens = s.tokens (content found)
    --   (b) throw error (not .ok, contradiction with h)
    --   (c) call skipToContentLoop with fuel' → use IH
    --
    -- Key: none of the intermediate operations change tokens.
    -- skipSpaces, skipWhitespace, skipToEndOfLine: proven to preserve tokens
    -- consumeNewline: proven to preserve tokens
    -- { s' with simpleKeyAllowed := ..., needIndentCheck := ... }: no tokens change
    --
    -- The do-block for Except compiles to a sequence of Except.bind/match.
    -- Let's try simp to normalize it.
    simp only [Except.bind_ok, Except.ok.injEq] at h
    -- Try to split on all the branches
    split at h
    · -- needIndentCheck = true
      -- After skipSpaces, various tab checks
      simp only [skipSpaces_preserves_tokens', skipWhitespace_preserves_tokens',
                  skipToEndOfLine_preserves_tokens', consumeNewline_preserves_tokens'] at h
      split at h  -- col ≤ currentIndent?
      · split at h  -- peek? match for tab check
        · -- some '\t'
          split at h  -- probe.peek?
          · -- some '#' (comment after tab)
            split at h  -- peek? for '#' after whitespace
            · split at h -- '#' comment check
              · -- commentOk = true
                split at h -- peek? for line break
                · split at h -- isLineBreak
                  · -- line break: consume + recurse
                    sorry
                  · -- not line break: content
                    sorry
                · -- none: EOF
                  sorry
              · -- commentOk = false
                sorry
            · sorry
            · sorry
          · sorry
          · sorry
          · sorry
        · sorry
        · sorry
      · sorry
    · -- needIndentCheck = false
      sorry

