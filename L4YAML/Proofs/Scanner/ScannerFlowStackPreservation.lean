/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-! # `flowStack` preservation suite (scanner leaves)

`ScannerState.flowStack` is written only by the four flow-collection functions
(`scanFlowSequenceStart`/`scanFlowMappingStart` push a kind marker,
`scanFlowSequenceEnd`/`scanFlowMappingEnd` pop one).  Every other scanner
function copies the field through record updates.  This file discharges that
"every other function" half: a `_preserves_flowStack` lemma for each scanner
leaf reachable from `scanNextToken` outside those four, up to the three
non-flow per-character dispatchers.

The proofs are mechanical clones of the `_preserves_simpleKeyStack` suite in
`ScannerCorrectness.lean` (lines 3528-5752) with the field renamed: the
originals are field-agnostic structural walks (unfold + split + fuel induction
bottoming out in `emit`/`advance` preservation), so the same scripts transfer
verbatim.

The suite lives at the scanner-proof layer because both the emitter-scannability
chain results (`Proofs/Output/EmitterScannability/FlowStackChain.lean`, which
lifts these to `FlowMonoChain`) and the production-side accumulation invariant
(`Proofs/Production/StreamAccum.lean`, which couples `flowStack` to the open
flow frames) consume it.
-/

set_option maxHeartbeats 1000000

namespace L4YAML.Proofs.ScannerFlowStack

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.FlowAdjacency

/-! ## §1  `flowStack` preservation suite (scanner leaves)

Clones of the `_preserves_simpleKeyStack` suite in
`Proofs/Scanner/ScannerCorrectness.lean` with `simpleKeyStack` renamed to
`flowStack`: the original proofs are field-agnostic structural walks
(unfold + split + fuel induction bottoming out in `emit`/`advance`
preservation), so they transfer verbatim. -/

-- Cloned from `ScannerCorrectness` lines 3528-3530 (`_preserves_flowStack` twin).
lemma advance_preserves_flowStack (s : ScannerState) :
    s.advance.flowStack = s.flowStack := by
  unfold ScannerState.advance; dsimp only []; split <;> (try split) <;> (try split) <;> rfl

-- Cloned from `ScannerCorrectness` lines 3532-3534 (`_preserves_flowStack` twin).
lemma emit_preserves_flowStack (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).flowStack = s.flowStack := by
  unfold ScannerState.emit; rfl

-- Cloned from `ScannerCorrectness` lines 3536-3543 (`_preserves_flowStack` twin).
lemma skipSpacesLoop_preserves_flowStack (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).flowStack = s.flowStack := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · exact (ih _).trans (advance_preserves_flowStack _)
    · rfl

-- Cloned from `ScannerCorrectness` lines 3545-3554 (`_preserves_flowStack` twin).
lemma skipWhitespaceLoop_preserves_flowStack (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).flowStack = s.flowStack := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact (ih _).trans (advance_preserves_flowStack _)
      · rfl
    · rfl

-- Cloned from `ScannerCorrectness` lines 3556-3565 (`_preserves_flowStack` twin).
lemma skipToEndOfLineLoop_preserves_flowStack (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).flowStack = s.flowStack := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · exact (ih _).trans (advance_preserves_flowStack _)
    · rfl

-- Cloned from `ScannerCorrectness` lines 3567-3569 (`_preserves_flowStack` twin).
lemma skipSpaces_preserves_flowStack (s : ScannerState) :
    (skipSpaces s).flowStack = s.flowStack := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_flowStack s _

-- Cloned from `ScannerCorrectness` lines 3571-3573 (`_preserves_flowStack` twin).
lemma skipWhitespace_preserves_flowStack (s : ScannerState) :
    (skipWhitespace s).flowStack = s.flowStack := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_flowStack s _

-- Cloned from `ScannerCorrectness` lines 3575-3577 (`_preserves_flowStack` twin).
lemma skipToEndOfLine_preserves_flowStack (s : ScannerState) :
    (skipToEndOfLine s).flowStack = s.flowStack := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_flowStack s _

-- Cloned from `ScannerCorrectness` lines 3580-3590 (`_preserves_flowStack` twin).
lemma collectCommentTextLoop_preserves_flowStack (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.flowStack = s.flowStack := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_flowStack]
    · rfl

-- Cloned from `ScannerCorrectness` lines 3592-3609 (`_preserves_flowStack` twin).
lemma skipToContentWs_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.flowStack = s.flowStack := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_preserves_flowStack, skipSpaces_preserves_flowStack]
        · split at h
          · simp at h; rw [← h, skipWhitespace_preserves_flowStack, skipSpaces_preserves_flowStack]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_flowStack, skipSpaces_preserves_flowStack]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_preserves_flowStack, skipSpaces_preserves_flowStack]
      · simp at h; rw [← h, skipSpaces_preserves_flowStack]
    · simp at h; rw [← h, skipWhitespace_preserves_flowStack, skipSpaces_preserves_flowStack]
  · simp at h; rw [← h, skipWhitespace_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 3611-3628 (`_preserves_flowStack` twin).
lemma skipToContentComment_preserves_flowStack (s : ScannerState) :
    (skipToContentComment s).flowStack = s.flowStack := by
  unfold skipToContentComment
  split
  · -- peek? = some '#'
    simp only []
    split  -- peekBack?
    · -- peekBack? = some c
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_flowStack, advance_preserves_flowStack]
      · rfl
    · -- peekBack? = none
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_flowStack, advance_preserves_flowStack]
      · rfl
  · rfl

-- Cloned from `ScannerCorrectness` lines 3630-3638 (`_preserves_flowStack` twin).
lemma consumeNewline_preserves_flowStack (s : ScannerState) :
    (consumeNewline s).flowStack = s.flowStack := by
  unfold consumeNewline
  split
  · exact advance_preserves_flowStack s
  · simp only []; split
    · exact advance_preserves_flowStack _
    · exact advance_preserves_flowStack _
  · rfl

-- Cloned from `ScannerCorrectness` lines 3640-3660 (`_preserves_flowStack` twin).
lemma skipToContentLoop_preserves_flowStack (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') : s'.flowStack = s.flowStack := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · split at h
          · have := ih _ h; rw [this, consumeNewline_preserves_flowStack,
              skipToContentComment_preserves_flowStack]; exact skipToContentWs_preserves_flowStack s s1 hws
          · have := ih _ h; rw [this, consumeNewline_preserves_flowStack,
              skipToContentComment_preserves_flowStack]; exact skipToContentWs_preserves_flowStack s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_flowStack]
          exact skipToContentWs_preserves_flowStack s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_flowStack]
        exact skipToContentWs_preserves_flowStack s s1 hws

-- Cloned from `ScannerCorrectness` lines 3662-3664 (`_preserves_flowStack` twin).
lemma skipToContent_preserves_flowStack (s s' : ScannerState)
    (h : skipToContent s = .ok s') : s'.flowStack = s.flowStack := by
  unfold skipToContent at h; exact skipToContentLoop_preserves_flowStack s s' _ h

-- Cloned from `ScannerCorrectness` lines 3666-3674 (`_preserves_flowStack` twin).
lemma unwindIndentsLoop_preserves_flowStack (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).flowStack = s.flowStack := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ _ ih =>
    unfold unwindIndentsLoop; split
    · have := ih { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop, pendingKeys := (s.emit .blockEnd).pendingKeys.pop }
      simp [emit_preserves_flowStack] at this; exact this
    · rfl

-- Cloned from `ScannerCorrectness` lines 3676-3678 (`_preserves_flowStack` twin).
lemma unwindIndents_preserves_flowStack (s : ScannerState) (col : Int) :
    (unwindIndents s col).flowStack = s.flowStack := by
  unfold unwindIndents; exact unwindIndentsLoop_preserves_flowStack s col _

-- Cloned from `ScannerCorrectness` lines 3680-3685 (`_preserves_flowStack` twin).
lemma saveSimpleKey_preserves_flowStack (st : ScannerState) :
    (saveSimpleKey st).flowStack = st.flowStack := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl

-- Cloned from `ScannerCorrectness` lines 3690-3703 (`_preserves_flowStack` twin).
lemma collectHexDigitsLoop_preserves_flowStack (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.flowStack = s.flowStack := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_flowStack s
        rw [ih, h_adv]
      · rfl

-- Cloned from `ScannerCorrectness` lines 3706-3715 (`_preserves_flowStack` twin).
lemma parseHexEscape_preserves_flowStack (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.flowStack = s.flowStack := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_flowStack s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]

-- Cloned from `ScannerCorrectness` lines 3718-3734 (`_preserves_flowStack` twin).
lemma processEscape_preserves_flowStack (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.flowStack = s.flowStack := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  -- Split on each character case
  repeat (split at h)
  -- Handle all goals
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_flowStack s)
    | (have h_adv := advance_preserves_flowStack s
       have h_hex := parseHexEscape_preserves_flowStack s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )

-- Cloned from `ScannerCorrectness` lines 3737-3753 (`_preserves_flowStack` twin).
lemma skipBlankLinesLoop_preserves_flowStack (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.flowStack = s.flowStack := by
  induction fuel generalizing s cnt with
  | zero => unfold skipBlankLinesLoop; rfl
  | succ fuel' ih =>
    unfold skipBlankLinesLoop
    cases h_peek : (skipWhitespace s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipWhitespace_preserves_flowStack s
        have h_cn := consumeNewline_preserves_flowStack (skipWhitespace s)
        -- item 100: the gate's arm keeps the state untouched
        split
        · rfl
        · rw [ih, h_cn, h_sp]

-- Cloned from `ScannerCorrectness` lines 3756-3772 (`_preserves_flowStack` twin).
lemma foldQuotedNewlinesLoop_preserves_flowStack (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.flowStack = s.flowStack := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    cases h_peek : (skipWhitespace s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipWhitespace_preserves_flowStack s
        have h_cn := consumeNewline_preserves_flowStack (skipWhitespace s)
        split
        · rfl
        · rw [ih, h_cn, h_sp]

-- Cloned from `ScannerCorrectness` lines 3775-3790 (`_preserves_flowStack` twin).
lemma foldQuotedNewlines_preserves_flowStack (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.flowStack = s.flowStack := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_flowStack s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_flowStack (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_flowStack (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_flowStack (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  -- 4.32.0 reshaped the do-notation match tree; split fully, then close every
  -- leaf uniformly (error leaves by contradiction, ok leaves by the fold chain).
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn])

-- Cloned from `ScannerCorrectness` lines 3793-3876 (`_preserves_flowStack` twin).
lemma collectPlainScalarLoop_preserves_flowStack (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.flowStack = s.flowStack := by
  intro result h
  induction fuel generalizing s content lastLine with
  | zero =>
    unfold collectPlainScalarLoop at h
    injection h with h_eq; cases h_eq; rfl
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · -- peek = none
      injection h with h_eq; cases h_eq; rfl
    · -- peek = some c
      rename_i c
      split at h
      · -- collectPlainScalar_terminates? = some → state = s
        rename_i hterm
        injection h with h_eq; cases h_eq
        rw [ScannerCorrectness.ScanHelpers.collectPlainScalar_terminates?_state _ _ _ _ _ _ hterm]
      · -- collectPlainScalar_terminates? = none → continue
        split at h
        · -- isLineBreak c
          split at h
          · -- inFlow
            simp only [bind, Except.bind] at h
            split at h <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk content_fold s_fold =>
              have h_fold := foldQuotedNewlines_preserves_flowStack s s_fold content_fold heq
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · -- item 50: the flow floor's throw contradicts `.ok`
                split at h
                · contradiction
                dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s_fold (content ++ content_fold) "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih s_fold (content ++ content_fold) "" h_loop, h_fold]
                | error e => simp at h
          · -- !inFlow: block line break
            split at h
            · -- _handleBlockLineBreak = none → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- _handleBlockLineBreak = some → recurse
              rename_i content' s' hblk
              have hprop : s'.flowStack = s.flowStack := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipWhitespace_preserves_flowStack,
                    skipSpaces_preserves_flowStack,
                    skipBlankLinesLoop_preserves_flowStack,
                    consumeNewline_preserves_flowStack]
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih _ _ _ h_loop, hprop]
                | error e => simp at h
        · split at h
          · -- isWhiteSpace c
            have h_adv := advance_preserves_flowStack s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · -- regular content
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- plainSafe → recurse
              simp only [] at h
              have h_adv := advance_preserves_flowStack s
              rw [ih s.advance _ "" h, h_adv]

-- Cloned from `ScannerCorrectness` lines 3879-3935 (`_preserves_flowStack` twin).
lemma collectDoubleQuotedLoop_preserves_flowStack (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.flowStack = s.flowStack := by
  -- protectedLen (default 0) is generalised so the IH covers the fold
  -- boundary the recursive call shifts (B2).
  suffices H : ∀ (p : Nat) (s : ScannerState) (content : String) (result : String × ScannerState),
      collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd p = .ok result →
      result.snd.flowStack = s.flowStack by
    intro result h; exact H 0 s content result h
  intro p s content result h
  induction fuel generalizing s content p with
  | zero =>
    unfold collectDoubleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '"' case (closing quote)
      injection h with h_eq; cases h_eq
      exact advance_preserves_flowStack s
    · -- some '\\' case (escape sequence)
      simp only [] at h
      split at h <;> try contradiction
      -- some c after backslash
      split at h
      · -- isLineBreak c (escaped line break — the landing is a fold, item 87)
        have h_adv := advance_preserves_flowStack s
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_flowStack s.advance s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold, h_adv])
      · -- regular escape sequence
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_flowStack s.advance ch s_after_escape heq
          have h_adv := advance_preserves_flowStack s
          rw [ih _ _ _ h, h_proc, h_adv]
    · -- some c case (regular character)
      split at h
      · -- isLineBreak c
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_flowStack s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold])
      · -- regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_flowStack s
        rw [ih _ _ _ h, h_adv]

-- Cloned from `ScannerCorrectness` lines 3938-3976 (`_preserves_flowStack` twin).
lemma collectSingleQuotedLoop_preserves_flowStack (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.flowStack = s.flowStack := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectSingleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '\'' case
      simp only [] at h
      split at h
      · -- escaped quote: '\''\''
        have h_adv1 := advance_preserves_flowStack s
        have h_adv2 := advance_preserves_flowStack s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · -- closing quote
        injection h with h_eq; cases h_eq
        exact advance_preserves_flowStack s
    · -- some c case (not quote)
      split at h
      · -- isLineBreak c = true
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_flowStack s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih s_fold _ h, h_fold])
      · -- isLineBreak c = false, regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_flowStack s
        rw [ih s.advance _ h, h_adv]

-- Cloned from `ScannerCorrectness` lines 3979-3996 (`_preserves_flowStack` twin).
lemma collectAnchorNameLoop_preserves_flowStack (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.flowStack = s.flowStack := by
  induction fuel generalizing s acc with
  | zero =>
    unfold collectAnchorNameLoop
    rfl
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · -- some c
      split
      · -- condition true: recurse with advance
        rw [ih]
        exact advance_preserves_flowStack s
      · -- condition false: return
        rfl
    · -- none
      rfl

-- Cloned from `ScannerCorrectness` lines 3999-4008 (`_preserves_flowStack` twin).
lemma collectDirectiveNameLoop_preserves_flowStack (s : ScannerState) (name : String) (fuel : Nat) :
    (collectDirectiveNameLoop s name fuel).snd.flowStack = s.flowStack := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ fuel' ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact advance_preserves_flowStack s
      · rfl
    · rfl

-- Cloned from `ScannerCorrectness` lines 4011-4021 (`_preserves_flowStack` twin).
lemma collectVersionMajorLoop_preserves_flowStack (s : ScannerState) (major : String) (fuel : Nat) :
    (collectVersionMajorLoop s major fuel).snd.flowStack = s.flowStack := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMajorLoop; split
    · exact advance_preserves_flowStack s
    · split
      · rw [ih]; exact advance_preserves_flowStack s
      · rfl
    · rfl

-- Cloned from `ScannerCorrectness` lines 4024-4033 (`_preserves_flowStack` twin).
lemma collectVersionMinorLoop_preserves_flowStack (s : ScannerState) (minor : String) (fuel : Nat) :
    (collectVersionMinorLoop s minor fuel).snd.flowStack = s.flowStack := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact advance_preserves_flowStack s
      · rfl
    · rfl

-- Cloned from `ScannerCorrectness` lines 4036-4045 (`_preserves_flowStack` twin).
lemma collectTagHandleDirectiveLoop_preserves_flowStack (s : ScannerState) (handle : String) (fuel : Nat) :
    (collectTagHandleDirectiveLoop s handle fuel).snd.flowStack = s.flowStack := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact advance_preserves_flowStack s
      · rfl
    · rfl

-- Cloned from `ScannerCorrectness` lines 4048-4057 (`_preserves_flowStack` twin).
lemma collectTagPrefixLoop_preserves_flowStack (s : ScannerState) (pfx : String) (fuel : Nat) :
    (collectTagPrefixLoop s pfx fuel).snd.flowStack = s.flowStack := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact advance_preserves_flowStack s
      · rfl
    · rfl

-- Cloned from `ScannerCorrectness` lines 4060-4071 (`_preserves_flowStack` twin).
lemma collectVerbatimTagLoop_preserves_flowStack (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.flowStack = s.flowStack := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_flowStack s  -- found '>', return (uri, s.advance)
    · split  -- isUriCharBool
      · rw [ih]; exact advance_preserves_flowStack s  -- uri char, recurse
      · rfl  -- not uri char, return (uri, s)
    · simp only []  -- none, return (uri, s)

-- Cloned from `ScannerCorrectness` lines 4074-4084 (`_preserves_flowStack` twin).
lemma collectTagSuffixLoop_preserves_flowStack (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.flowStack = s.flowStack := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_flowStack s  -- tag char, recurse
      · simp only []  -- not tag char, return
    · simp only []  -- none, return

-- Cloned from `ScannerCorrectness` lines 4087-4098 (`_preserves_flowStack` twin).
lemma collectTagHandleLoop_preserves_flowStack (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.flowStack = s.flowStack := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_flowStack s  -- found '!', return (chars, true, s.advance)
    · split  -- split on the if condition
      · rw [ih]; exact advance_preserves_flowStack s  -- word char, recurse
      · simp only []  -- not word char, return
    · simp only []  -- none, return

-- Cloned from `ScannerCorrectness` lines 4101-4113 (`_preserves_flowStack` twin).
lemma parseBlockHeaderLoop_preserves_flowStack (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.flowStack = s.flowStack := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_flowStack s
    · rw [ih]; exact advance_preserves_flowStack s
    · split
      · rw [ih]; exact advance_preserves_flowStack s
      · rfl
    · rfl

-- Cloned from `ScannerCorrectness` lines 4116-4123 (`_preserves_flowStack` twin).
lemma consumeExactSpaces_preserves_flowStack (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.flowStack = s.flowStack := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_flowStack s
    · rfl

-- Cloned from `ScannerCorrectness` lines 4126-4136 (`_preserves_flowStack` twin).
lemma collectLineContentLoop_preserves_flowStack (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.flowStack = s.flowStack := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_flowStack s
    · rfl

-- Cloned from `ScannerCorrectness` lines 4139-4161 (`_preserves_flowStack` twin).
lemma collectBlockScalarLoop_preserves_flowStack (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.flowStack = s.flowStack := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_flowStack s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_flowStack, consumeExactSpaces_preserves_flowStack]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_flowStack,
                    collectLineContentLoop_preserves_flowStack, consumeExactSpaces_preserves_flowStack]
              · split
                · rfl
                · rw [collectLineContentLoop_preserves_flowStack, consumeExactSpaces_preserves_flowStack]
            · rw [collectLineContentLoop_preserves_flowStack, consumeExactSpaces_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4164-4174 (`_preserves_flowStack` twin).
lemma skipDocEndWhitespace_preserves_flowStack (s : ScannerState) (fuel : Nat) :
    (skipDocEndWhitespace s fuel).flowStack = s.flowStack := by
  induction fuel generalizing s with
  | zero => unfold skipDocEndWhitespace; rfl
  | succ fuel' ih =>
    unfold skipDocEndWhitespace
    split
    · split
      · rw [ih]; exact advance_preserves_flowStack s
      · rfl
    · rfl

-- Cloned from `ScannerCorrectness` lines 4178-4206 (`_preserves_flowStack` twin).
lemma preprocess_preserves_flowStack (s : ScannerState) (s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    s1.flowStack = s.flowStack := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_stack_skip := skipToContent_preserves_flowStack s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [closeStaleExplicitKey_flowStack, saveSimpleKey_preserves_flowStack]
            show (unwindIndents s_skip s_skip.col).flowStack = s.flowStack
            rw [unwindIndents_preserves_flowStack]; exact h_stack_skip
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [closeStaleExplicitKey_flowStack, saveSimpleKey_preserves_flowStack]; exact h_stack_skip

-- Cloned from `ScannerCorrectness` lines 4302-4308 (`_preserves_flowStack` twin).
lemma advanceNLoop_preserves_flowStack (s : ScannerState) (n : Nat) :
    (s.advanceNLoop n).flowStack = s.flowStack := by
  induction n generalizing s with
  | zero => unfold ScannerState.advanceNLoop; rfl
  | succ _ ih =>
    unfold ScannerState.advanceNLoop
    exact (ih s.advance).trans (advance_preserves_flowStack s)

-- Cloned from `ScannerCorrectness` lines 4314-4316 (`_preserves_flowStack` twin).
lemma advanceN_preserves_flowStack (s : ScannerState) (n : Nat) :
    (s.advanceN n).flowStack = s.flowStack := by
  unfold ScannerState.advanceN; exact advanceNLoop_preserves_flowStack s n

-- Cloned from `ScannerCorrectness` lines 4397-4399 (`_preserves_flowStack` twin).
lemma emitAt_preserves_flowStack (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).flowStack = s.flowStack := by
  unfold ScannerState.emitAt; rfl

-- Cloned from `ScannerCorrectness` lines 4409-4413 (`_preserves_flowStack` twin).
lemma pushSequenceIndent_preserves_flowStack (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).flowStack = s.flowStack := by
  unfold pushSequenceIndent; split
  · simp [emit_preserves_flowStack]
  · rfl

-- Cloned from `ScannerCorrectness` lines 4421-4425 (`_preserves_flowStack` twin).
lemma pushMappingIndent_preserves_flowStack (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).flowStack = s.flowStack := by
  unfold pushMappingIndent; split
  · simp [emit_preserves_flowStack]
  · rfl

-- Cloned from `ScannerCorrectness` lines 4447-4451 (`_preserves_flowStack` twin).
lemma scanDocumentStart_preserves_flowStack (s : ScannerState) :
    (scanDocumentStart s).flowStack = s.flowStack := by
  unfold scanDocumentStart
  simp [advanceN_preserves_flowStack, emit_preserves_flowStack,
        unwindIndents_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4467-4475 (`_preserves_flowStack` twin).
lemma scanDocumentEnd_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanDocumentEnd s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanDocumentEnd at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advanceN_preserves_flowStack, emit_preserves_flowStack,
        unwindIndents_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4495-4503 (`_preserves_flowStack` twin).
lemma scanKey_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanKey s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanKey at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_flowStack, emit_preserves_flowStack,
                  pushMappingIndent_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4533-4544 (`_preserves_flowStack` twin).
lemma scanValuePrepare_preserves_flowStack (s : ScannerState) :
    (scanValuePrepare s).flowStack = s.flowStack := by
  unfold scanValuePrepare
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · exact pushMappingIndent_preserves_flowStack s s.col
      · rfl

-- Cloned from `ScannerCorrectness` lines 4569-4582 (`_preserves_flowStack` twin).
lemma scanValue_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanValue s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  -- Three guards since item 31: validate, indent-tab check, tab check
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  simp [advance_preserves_flowStack, emit_preserves_flowStack,
        scanValuePrepare_preserves_flowStack]
  unfold scanValueClearKey; split
  · split
    · rfl
    · split <;> rfl
  · rfl

-- Cloned from `ScannerCorrectness` lines 4600-4614 (`_preserves_flowStack` twin).
lemma scanBlockScalarSkipComment_preserves_flowStack (s : ScannerState) :
    (scanBlockScalarSkipComment s).flowStack = s.flowStack := by
  unfold scanBlockScalarSkipComment
  split
  · -- some '#'
    split
    · -- peekBack? = some c
      dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_flowStack, advance_preserves_flowStack]
      · rfl
    · -- peekBack? = none
      rfl
  · rfl

-- Cloned from `ScannerCorrectness` lines 4617-4626 (`_preserves_flowStack` twin).
lemma scanBlockScalarConsumeNewline_preserves_flowStack (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_flowStack s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

-- Cloned from `ScannerCorrectness` lines 4640-4650 (`_preserves_flowStack` twin).
lemma scanBlockScalarBody_preserves_flowStack (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos) (s' : ScannerState)
    (h_sk : s_nl.flowStack = s_orig.flowStack)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.flowStack = s_orig.flowStack := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_preserves_flowStack, collectBlockScalarLoop_preserves_flowStack, h_sk]

-- Cloned from `ScannerCorrectness` lines 4660-4671 (`_preserves_flowStack` twin).
lemma scanBlockScalar_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_flowStack s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_flowStack _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_flowStack,
              skipWhitespace_preserves_flowStack,
              parseBlockHeaderLoop_preserves_flowStack,
              advance_preserves_flowStack]) h

-- Cloned from `ScannerCorrectness` lines 4721-4764 (`_preserves_flowStack` twin).
lemma scanDirective_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanDirective s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · -- YAML directive (match wrapper)
      split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_preserves_flowStack]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals (try simp [emitAt_preserves_flowStack, skipWhitespace_preserves_flowStack,
              collectVersionMinorLoop_preserves_flowStack,
              collectVersionMajorLoop_preserves_flowStack])
        all_goals (rw [collectDirectiveNameLoop_preserves_flowStack, advance_preserves_flowStack])
      · contradiction
    · split at h
      · -- TAG directive (match wrapper)
        split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_preserves_flowStack]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner
          · contradiction  -- [89]: a malformed `%TAG` handle is refused
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
          all_goals simp [emitAt_preserves_flowStack, collectTagPrefixLoop_preserves_flowStack,
                skipWhitespace_preserves_flowStack,
                collectTagHandleDirectiveLoop_preserves_flowStack,
                collectDirectiveNameLoop_preserves_flowStack,
                advance_preserves_flowStack]
        · contradiction
      · simp only [Except.ok.injEq] at h; subst h
        simp [skipToEndOfLine_preserves_flowStack, skipWhitespace_preserves_flowStack,
              collectDirectiveNameLoop_preserves_flowStack, advance_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4820-4827 (`_preserves_flowStack` twin).
lemma scanFlowEntry_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanFlowEntry s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_flowStack, emit_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4839-4847 (`_preserves_flowStack` twin).
lemma scanBlockEntry_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanBlockEntry s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_flowStack, emit_preserves_flowStack,
                  pushSequenceIndent_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4869-4877 (`_preserves_flowStack` twin).
lemma scanAnchorOrAlias_preserves_flowStack (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.flowStack = s.flowStack := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [emitAt_preserves_flowStack, collectAnchorNameLoop_preserves_flowStack,
          advance_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4901-4911 (`_preserves_flowStack` twin).
lemma scanVerbatimTag_preserves_flowStack (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    s'.flowStack = s.flowStack := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp [emitAt_preserves_flowStack, collectVerbatimTagLoop_preserves_flowStack,
            advance_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4919-4923 (`_preserves_flowStack` twin).
lemma scanSecondaryTag_preserves_flowStack (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).flowStack = s.flowStack := by
  unfold scanSecondaryTag
  simp [emitAt_preserves_flowStack, collectTagSuffixLoop_preserves_flowStack,
        advance_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4934-4941 (`_preserves_flowStack` twin).
lemma scanNamedTag_preserves_flowStack (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).flowStack = s.flowStack := by
  unfold scanNamedTag
  simp only []
  split
  · simp [emitAt_preserves_flowStack, collectTagSuffixLoop_preserves_flowStack,
          collectTagHandleLoop_preserves_flowStack]
  · simp [emitAt_preserves_flowStack, collectTagSuffixLoop_preserves_flowStack,
          collectTagHandleLoop_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 4961-4977 (`_preserves_flowStack` twin).
lemma scanTag_preserves_flowStack (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.flowStack = s.flowStack := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have h := Except.ok.inj hok; subst h; dsimp only []
      simp [scanVerbatimTag_preserves_flowStack s.advance s.currentPos s_verb hv,
            advance_preserves_flowStack]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanSecondaryTag_preserves_flowStack, advance_preserves_flowStack]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanNamedTag_preserves_flowStack, advance_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 5074-5082 (`_preserves_flowStack` twin).
lemma scanPlainScalar_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h; subst h
  simp [emitAt_preserves_flowStack]
  exact collectPlainScalarLoop_preserves_flowStack s "" "" _ _ _ _ result heq

-- Cloned from `ScannerCorrectness` lines 5490-5505 (`_preserves_flowStack` twin).
lemma scanDoubleQuoted_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_flowStack]
    have := collectDoubleQuotedLoop_preserves_flowStack s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_flowStack]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_flowStack]
    have := collectDoubleQuotedLoop_preserves_flowStack s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 5541-5556 (`_preserves_flowStack` twin).
lemma scanSingleQuoted_preserves_flowStack (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') : s'.flowStack = s.flowStack := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_flowStack]
    have := collectSingleQuotedLoop_preserves_flowStack s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_flowStack]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_flowStack]
    have := collectSingleQuotedLoop_preserves_flowStack s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_flowStack]

-- Cloned from `ScannerCorrectness` lines 5608-5624 (`_preserves_flowStack` twin).
lemma dispatchStructural_preserves_flowStack (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    s'.flowStack = s.flowStack := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_preserves_flowStack s
    | exact scanDocumentEnd_preserves_flowStack _ _ (by assumption)
    | exact scanDirective_preserves_flowStack _ _ (by assumption)
    | (simp_all [scanDocumentStart_preserves_flowStack,
        scanDocumentEnd_preserves_flowStack, scanDirective_preserves_flowStack]; done)

-- Cloned from `ScannerCorrectness` lines 5644-5660 (`_preserves_flowStack` twin).
lemma dispatchBlockIndicators_preserves_flowStack (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    s'.flowStack = s.flowStack := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanBlockEntry_preserves_flowStack _ _ (by assumption)
    | exact scanKey_preserves_flowStack _ _ (by assumption)
    | exact scanValue_preserves_flowStack _ _ (by assumption)
    | (simp_all [scanBlockEntry_preserves_flowStack,
        scanKey_preserves_flowStack, scanValue_preserves_flowStack]; done)

-- Cloned from `ScannerCorrectness` lines 5708-5752 (`_preserves_flowStack` twin).
lemma dispatchContent_preserves_flowStack (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    s'.flowStack = s.flowStack := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · -- '&': item-9e property-run guard, then the scanAnchorOrAlias bind
    split at h
    · simp at h
    generalize h_fn : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h; dsimp only []
      exact scanAnchorOrAlias_preserves_flowStack s true s_a h_fn
  · split at h
    · -- '*': alias, under the item-9e property-run guard
      split at h
      · simp at h
      split at h
      · simp at h
      · -- item 9h: peel `validateAliasClose`, then the alias bind.
        replace h := aliasArm_scan_ok h
        generalize h_fn : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanAnchorOrAlias_preserves_flowStack s false s_a h_fn
    · split at h
      · -- '!': item-9e property-run guard, then the scanTag bind
        split at h
        · simp at h
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanTag_preserves_flowStack s s_t h_fn
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_flowStack _ _ (by assumption)
          | exact scanDoubleQuoted_preserves_flowStack _ _ (by assumption)
          | exact scanSingleQuoted_preserves_flowStack _ _ (by assumption)
          | exact scanPlainScalar_preserves_flowStack _ _ (by assumption)
          | (simp_all; done)

end L4YAML.Proofs.ScannerFlowStack

end Blanket
