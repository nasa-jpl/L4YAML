/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Scanner.ScannerLinePreservation
public import L4YAML.Proofs.Scanner.PreprocessIndentStable
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-! # The explicit-key coupling's scanner half (DOCS item 124)

**Where `explicitKeyLine` and `explicitKeyCol` go, function by function.**
The two fields are written by `scanKey`, `scanValue` and the four flow
brackets, and by nothing else: every skip, every content scan, every props
scan and the whole block-scalar walk carry them unchanged.  This file is the
transport ladder for both fields (the `implicitValueLine` ladder of item 101,
transposed twice), plus the epilogue facts for the writers — including the
LINE-FREE `scanValue` discriminators that decide, from the pre-state's
`explicitKeyLine`/`explicitKeyCol` and the indicator's own column alone,
whether the `:` stamped `implicitValueLine` or consumed the pending `?`.

The consumer is the park-face coupling (U2 in the under-indent map): a park
that cannot refute `explicitKeyLine` owes the `?` frame's face, and the
producers pay or refute through exactly these lemmas. -/

set_option autoImplicit false

namespace L4YAML.Proofs.ExplicitKeyCoupling

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.ScannerCorrectness

/-! ## §1  `explicitKeyLine`: the basic chain -/

/-! ## explicitKeyLine preservation through the skipToContent chain (item 48)

`explicitKeyLine` is written by `scanValue` alone; the whole preprocessing
chain carries it unchanged.  The clones below mirror the `flowLevel` ladder
lemma-for-lemma — same functions, same branch structure. -/

lemma advance_preserves_explicitKeyLine (s : ScannerState) :
    s.advance.explicitKeyLine = s.explicitKeyLine := by
  unfold ScannerState.advance
  split
  · simp only []
    split
    · rfl
    · split <;> rfl
  · rfl

lemma emit_preserves_explicitKeyLine (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).explicitKeyLine = s.explicitKeyLine := by
  unfold ScannerState.emit
  rfl

lemma unwindIndentsLoop_preserves_explicitKeyLine (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · rw [ih]; exact emit_preserves_explicitKeyLine s .blockEnd
    · rfl

lemma unwindIndents_preserves_explicitKeyLine (s : ScannerState) (col : Int) :
    (unwindIndents s col).explicitKeyLine = s.explicitKeyLine := by
  unfold unwindIndents
  exact unwindIndentsLoop_preserves_explicitKeyLine s col s.indents.size

lemma saveSimpleKey_preserves_explicitKeyLine (s : ScannerState) :
    (saveSimpleKey s).explicitKeyLine = s.explicitKeyLine := by
  unfold saveSimpleKey
  split <;> (try rfl)
  split <;> rfl

lemma consumeNewline_preserves_explicitKeyLine (s : ScannerState) :
    (consumeNewline s).explicitKeyLine = s.explicitKeyLine := by
  unfold consumeNewline
  split
  · exact advance_preserves_explicitKeyLine s
  · dsimp only []
    split
    · exact advance_preserves_explicitKeyLine s
    · exact advance_preserves_explicitKeyLine s
  · rfl

lemma skipSpaces_preserves_explicitKeyLine (s : ScannerState) :
    (skipSpaces s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop; split
    · rw [IH, advance_preserves_explicitKeyLine]
    · rfl

lemma skipWhitespace_preserves_explicitKeyLine (s : ScannerState) :
    (skipWhitespace s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [IH, advance_preserves_explicitKeyLine]
      · rfl
    · rfl

lemma collectCommentTextLoop_preserves_explicitKeyLine (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_explicitKeyLine]
    · rfl

lemma skipToContentWs_preserves_explicitKeyLine (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine,
            skipSpaces_preserves_explicitKeyLine]
        · split at h
          · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine,
              skipSpaces_preserves_explicitKeyLine]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine,
                skipSpaces_preserves_explicitKeyLine]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine,
            skipSpaces_preserves_explicitKeyLine]
      · simp at h; rw [← h, skipSpaces_preserves_explicitKeyLine]
    · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine,
        skipSpaces_preserves_explicitKeyLine]
  · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine]

lemma skipToContentComment_preserves_explicitKeyLine (s : ScannerState) :
    (skipToContentComment s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_explicitKeyLine, advance_preserves_explicitKeyLine]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_explicitKeyLine, advance_preserves_explicitKeyLine]
      · rfl
  · rfl

lemma skipToContentLoop_preserves_explicitKeyLine (s : ScannerState) (s' : ScannerState)
    (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [← h]
  | succ fuel' IH =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · rename_i c hpeek
        split at h
        · split at h
          · have ih := IH _ h
            rw [ih, consumeNewline_preserves_explicitKeyLine,
                skipToContentComment_preserves_explicitKeyLine]
            exact skipToContentWs_preserves_explicitKeyLine s s1 hws
          · have ih := IH _ h
            rw [ih, consumeNewline_preserves_explicitKeyLine,
                skipToContentComment_preserves_explicitKeyLine]
            exact skipToContentWs_preserves_explicitKeyLine s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_explicitKeyLine]
          exact skipToContentWs_preserves_explicitKeyLine s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_explicitKeyLine]
        exact skipToContentWs_preserves_explicitKeyLine s s1 hws

lemma skipToContent_preserves_explicitKeyLine (s : ScannerState) (s' : ScannerState) :
    skipToContent s = .ok s' →
    s'.explicitKeyLine = s.explicitKeyLine := by
  intro h
  unfold skipToContent at h
  exact skipToContentLoop_preserves_explicitKeyLine s s' _ h


/-! ## §2  `explicitKeyLine`: the content, props and block-scalar scans -/


/-! ## `explicitKeyLine` through the CONTENT scans (item 101)

Item 48 carried the stamp through the preprocessing chain, which is where a
block dispatch reads it.  A CONTENT dispatch reads it one step further on: the
`[189]` implicit value's own content parks a pending, and the `:` that meets
that park is refused by `scanValueValidate` for the same reason the one at the
value indicator was.  `scanValue` is still the field's only writer, so the four
value-completing scans carry it unchanged — the ladder below mirrors the
`simpleKey` one lemma-for-lemma, same functions, same branch structure. -/

lemma collectHexDigitsLoop_preserves_explicitKeyLine (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.explicitKeyLine = s.explicitKeyLine := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_explicitKeyLine s
        rw [ih, h_adv]
      · rfl


lemma parseHexEscape_preserves_explicitKeyLine (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_explicitKeyLine s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]


lemma processEscape_preserves_explicitKeyLine (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  -- Split on each character case
  repeat' (split at h)
  -- Handle all goals
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_explicitKeyLine s)
    | (have h_adv := advance_preserves_explicitKeyLine s
       have h_hex := parseHexEscape_preserves_explicitKeyLine s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )


lemma skipBlankLinesLoop_preserves_explicitKeyLine (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.explicitKeyLine = s.explicitKeyLine := by
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
        have h_sp := skipWhitespace_preserves_explicitKeyLine s
        have h_cn := consumeNewline_preserves_explicitKeyLine (skipWhitespace s)
        -- item 100: the gate's arm keeps the state untouched
        split
        · rfl
        · rw [ih, h_cn, h_sp]


lemma foldQuotedNewlinesLoop_preserves_explicitKeyLine (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.explicitKeyLine = s.explicitKeyLine := by
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
        have h_sp := skipWhitespace_preserves_explicitKeyLine s
        have h_cn := consumeNewline_preserves_explicitKeyLine (skipWhitespace s)
        split
        · rfl
        · rw [ih, h_cn, h_sp]


lemma foldQuotedNewlines_preserves_explicitKeyLine (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_explicitKeyLine s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_explicitKeyLine (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_explicitKeyLine (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_explicitKeyLine (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  -- 4.32.0 reshaped the do-notation match tree; split fully, then close every
  -- leaf uniformly (error leaves by contradiction, ok leaves by the fold chain).
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn])


lemma collectPlainScalarLoop_preserves_explicitKeyLine (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.explicitKeyLine = s.explicitKeyLine := by
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
        rw [ScanHelpers.collectPlainScalar_terminates?_state _ _ _ _ _ _ hterm]
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
              have h_fold := foldQuotedNewlines_preserves_explicitKeyLine s s_fold content_fold heq
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · -- recurse with content-length check
                -- item 50: the flow floor's throw contradicts `.ok`
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
              have hprop : s'.explicitKeyLine = s.explicitKeyLine := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipWhitespace_preserves_explicitKeyLine, skipSpaces_preserves_explicitKeyLine,
                    skipBlankLinesLoop_preserves_explicitKeyLine, consumeNewline_preserves_explicitKeyLine]
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
            have h_adv := advance_preserves_explicitKeyLine s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · -- regular content
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- plainSafe → recurse
              simp only [] at h
              have h_adv := advance_preserves_explicitKeyLine s
              rw [ih s.advance _ "" h, h_adv]


lemma collectDoubleQuotedLoop_preserves_explicitKeyLine (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.explicitKeyLine = s.explicitKeyLine := by
  -- protectedLen (default 0) is generalised so the IH covers the fold
  -- boundary the recursive call shifts (B2).
  suffices H : ∀ (p : Nat) (s : ScannerState) (content : String) (result : String × ScannerState),
      collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd p = .ok result →
      result.snd.explicitKeyLine = s.explicitKeyLine by
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
      exact advance_preserves_explicitKeyLine s
    · -- some '\\' case (escape sequence)
      simp only [] at h
      split at h <;> try contradiction
      -- some c after backslash
      split at h
      · -- isLineBreak c (escaped line break; item 53 splits the branch)
        have h_adv := advance_preserves_explicitKeyLine s
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_explicitKeyLine s.advance s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold, h_adv])
      · -- regular escape sequence
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_explicitKeyLine s.advance ch s_after_escape heq
          have h_adv := advance_preserves_explicitKeyLine s
          rw [ih _ _ _ h, h_proc, h_adv]
    · -- some c case (regular character)
      split at h
      · -- isLineBreak c
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_explicitKeyLine s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold])
      · -- regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_explicitKeyLine s
        rw [ih _ _ _ h, h_adv]


lemma collectSingleQuotedLoop_preserves_explicitKeyLine (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.explicitKeyLine = s.explicitKeyLine := by
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
        have h_adv1 := advance_preserves_explicitKeyLine s
        have h_adv2 := advance_preserves_explicitKeyLine s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · -- closing quote
        injection h with h_eq; cases h_eq
        exact advance_preserves_explicitKeyLine s
    · -- some c case (not quote)
      split at h
      · -- isLineBreak c = true
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_explicitKeyLine s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih s_fold _ h, h_fold])
      · -- isLineBreak c = false, regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_explicitKeyLine s
        rw [ih s.advance _ h, h_adv]


lemma collectAnchorNameLoop_preserves_explicitKeyLine (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.explicitKeyLine = s.explicitKeyLine := by
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
        exact advance_preserves_explicitKeyLine s
      · -- condition false: return
        rfl
    · -- none
      rfl

lemma emitAt_preserves_explicitKeyLine (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).explicitKeyLine = s.explicitKeyLine := by
  unfold ScannerState.emitAt; rfl

lemma scanAnchorOrAlias_preserves_explicitKeyLine (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [emitAt_preserves_explicitKeyLine, collectAnchorNameLoop_preserves_explicitKeyLine,
          advance_preserves_explicitKeyLine]

lemma scanPlainScalar_preserves_explicitKeyLine (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') : s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h; subst h
  simp [emitAt_preserves_explicitKeyLine]
  exact collectPlainScalarLoop_preserves_explicitKeyLine s "" "" _ _ _ _ result heq

lemma scanDoubleQuoted_preserves_explicitKeyLine (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') : s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_explicitKeyLine]
    have := collectDoubleQuotedLoop_preserves_explicitKeyLine s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_explicitKeyLine]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_explicitKeyLine]
    have := collectDoubleQuotedLoop_preserves_explicitKeyLine s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_explicitKeyLine]

lemma scanSingleQuoted_preserves_explicitKeyLine (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') : s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_explicitKeyLine]
    have := collectSingleQuotedLoop_preserves_explicitKeyLine s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_explicitKeyLine]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_explicitKeyLine]
    have := collectSingleQuotedLoop_preserves_explicitKeyLine s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_explicitKeyLine]

/-! ### … and through the TAG scan (item 102)

The props run's own head is `&`/`!`, which the content ladder above excludes:
`dispatchContent_explicitKeyLine` reads a value-completing character.  A
`[96]` run parks before its content, so the stamp has to survive the property
scan itself before the run's content can carry it — the anchor half is
`scanAnchorOrAlias_preserves_explicitKeyLine` above, and this is the tag
half, mirroring the `simpleKey` ladder lemma-for-lemma. -/

lemma collectVerbatimTagLoop_preserves_explicitKeyLine (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_explicitKeyLine s  -- found '>', return (uri, s.advance)
    · split  -- isUriCharBool
      · rw [ih]; exact advance_preserves_explicitKeyLine s  -- uri char, recurse
      · rfl  -- not uri char, return (uri, s)
    · simp only []  -- none, return (uri, s)

lemma collectTagSuffixLoop_preserves_explicitKeyLine (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_explicitKeyLine s  -- tag char, recurse
      · simp only []  -- not tag char, return
    · simp only []  -- none, return

lemma collectTagHandleLoop_preserves_explicitKeyLine (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_explicitKeyLine s  -- found '!', return (chars, true, s.advance)
    · split  -- split on the if condition
      · rw [ih]; exact advance_preserves_explicitKeyLine s  -- word char, recurse
      · simp only []  -- not word char, return
    · simp only []  -- none, return

lemma scanVerbatimTag_preserves_explicitKeyLine (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp [emitAt_preserves_explicitKeyLine, collectVerbatimTagLoop_preserves_explicitKeyLine,
            advance_preserves_explicitKeyLine]

lemma scanSecondaryTag_preserves_explicitKeyLine (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).explicitKeyLine = s.explicitKeyLine := by
  unfold scanSecondaryTag
  simp [emitAt_preserves_explicitKeyLine, collectTagSuffixLoop_preserves_explicitKeyLine,
        advance_preserves_explicitKeyLine]

lemma scanNamedTag_preserves_explicitKeyLine (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).explicitKeyLine = s.explicitKeyLine := by
  unfold scanNamedTag
  simp only []
  split
  · simp [emitAt_preserves_explicitKeyLine, collectTagSuffixLoop_preserves_explicitKeyLine,
          collectTagHandleLoop_preserves_explicitKeyLine]
  · simp [emitAt_preserves_explicitKeyLine, collectTagSuffixLoop_preserves_explicitKeyLine,
          collectTagHandleLoop_preserves_explicitKeyLine]

lemma scanTag_preserves_explicitKeyLine (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have h := Except.ok.inj hok; subst h; dsimp only []
      simp [scanVerbatimTag_preserves_explicitKeyLine s.advance s.currentPos s_verb hv,
            advance_preserves_explicitKeyLine]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanSecondaryTag_preserves_explicitKeyLine, advance_preserves_explicitKeyLine]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanNamedTag_preserves_explicitKeyLine, advance_preserves_explicitKeyLine]


/-! ### … and through the BLOCK SCALAR, which totalizes the walk (item 103)

The stamp ladder above stops at the tag: items 101/102 needed the heads a
content dispatch reads as a KEY, and `|`/`>` is not one.  The flow interior
reads every head, so the last arm has to be walked too — and once it is, the
dispatch lemma is TOTAL and the three head-restricted readings above collapse
into it.  These are `ContentAllowDirectives.lean`'s walks with the field
renamed, for the reason stated there: both proofs bottom out in
`advance`/`emitAt`, which touch no field but their own. -/

lemma consumeExactSpaces_preserves_explicitKeyLine (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.explicitKeyLine = s.explicitKeyLine := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_explicitKeyLine s
    · rfl

lemma parseBlockHeaderLoop_preserves_explicitKeyLine (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_explicitKeyLine s
    · rw [ih]; exact advance_preserves_explicitKeyLine s
    · split
      · rw [ih]; exact advance_preserves_explicitKeyLine s
      · rfl
    · rfl

lemma collectLineContentLoop_preserves_explicitKeyLine (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_explicitKeyLine s
    · rfl

lemma collectBlockScalarLoop_preserves_explicitKeyLine (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_explicitKeyLine s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_explicitKeyLine, consumeExactSpaces_preserves_explicitKeyLine]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_explicitKeyLine,
                    collectLineContentLoop_preserves_explicitKeyLine, consumeExactSpaces_preserves_explicitKeyLine]
              · split
                · rfl
                · rw [collectLineContentLoop_preserves_explicitKeyLine, consumeExactSpaces_preserves_explicitKeyLine]
            · rw [collectLineContentLoop_preserves_explicitKeyLine, consumeExactSpaces_preserves_explicitKeyLine]

lemma scanBlockScalarSkipComment_preserves_explicitKeyLine (s : ScannerState) :
    (scanBlockScalarSkipComment s).explicitKeyLine = s.explicitKeyLine := by
  unfold scanBlockScalarSkipComment
  split
  · -- some '#'
    split
    · -- peekBack? = some c
      dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_explicitKeyLine, advance_preserves_explicitKeyLine]
      · rfl
    · -- peekBack? = none
      rfl
  · rfl

lemma scanBlockScalarConsumeNewline_preserves_explicitKeyLine (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_explicitKeyLine s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

lemma scanBlockScalarBody_preserves_explicitKeyLine (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos) (s' : ScannerState)
    (h_fl : s_nl.explicitKeyLine = s_orig.explicitKeyLine)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.explicitKeyLine = s_orig.explicitKeyLine := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_preserves_explicitKeyLine, collectBlockScalarLoop_preserves_explicitKeyLine, h_fl]

lemma scanBlockScalar_preserves_explicitKeyLine (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') : s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_explicitKeyLine s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_explicitKeyLine _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_explicitKeyLine,
              skipWhitespace_preserves_explicitKeyLine,
              parseBlockHeaderLoop_preserves_explicitKeyLine,
              advance_preserves_explicitKeyLine]) h

lemma dispatchContent_preserves_explicitKeyLine (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · -- '&': scanAnchorOrAlias bind
    split at h   -- item 9e: the property-run guard
    · simp at h
    generalize h_fn : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h; dsimp only []
      exact scanAnchorOrAlias_preserves_explicitKeyLine s true s_a h_fn
  · split at h
    · -- '*': alias
      split at h   -- item 9e: the property-run guard
      · simp at h
      split at h
      · simp at h
      · -- item 9h: peel `validateAliasClose`; the alias facts are unchanged.
        exact scanAnchorOrAlias_preserves_explicitKeyLine s false _ (aliasArm_scan_ok h)
    · split at h
      · -- '!': tag
        split at h   -- item 9e: the property-run guard
        · simp at h
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanTag_preserves_explicitKeyLine s s_t h_fn
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_explicitKeyLine _ _ (by assumption)
          | exact scanDoubleQuoted_preserves_explicitKeyLine _ _ (by assumption)
          | exact scanSingleQuoted_preserves_explicitKeyLine _ _ (by assumption)
          | exact scanPlainScalar_preserves_explicitKeyLine _ _ (by assumption)
          | (simp_all; done)


/-! ### … and through the FLOW indicators (item 103)

The stamp has to cross a whole flow COLLECTION to reach the close that may
read it as a key (`k: [1]: 2`), so the five indicators and the `?` are walked
here too.  None of them writes the field — `scanValue` is still its only
writer, and inside a flow even that one preserves it. -/

lemma pushMappingIndent_preserves_explicitKeyLine (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).explicitKeyLine = s.explicitKeyLine := by
  unfold pushMappingIndent; split
  · simp [emit_preserves_explicitKeyLine]
  · rfl

/-- The `,` ENDS the explicit-key entry (item 9l): `scanFlowEntry` clears the
    field outright rather than preserving it. -/
lemma scanFlowEntry_explicitKeyLine_none (s : ScannerState) (s' : ScannerState)
    (h : scanFlowEntry s = .ok s') : s'.explicitKeyLine = none := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals rfl

lemma scanValueClearKey_preserves_explicitKeyLine (s : ScannerState) :
    (scanValueClearKey s).explicitKeyLine = s.explicitKeyLine := by
  unfold scanValueClearKey
  split
  · split
    · rfl
    · split <;> rfl
  · rfl



/-! ## §3  `explicitKeyCol`: the basic chain -/

/-! ## explicitKeyCol preservation through the skipToContent chain (item 48)

`explicitKeyCol` is written by `scanValue` alone; the whole preprocessing
chain carries it unchanged.  The clones below mirror the `flowLevel` ladder
lemma-for-lemma — same functions, same branch structure. -/

lemma advance_preserves_explicitKeyCol (s : ScannerState) :
    s.advance.explicitKeyCol = s.explicitKeyCol := by
  unfold ScannerState.advance
  split
  · simp only []
    split
    · rfl
    · split <;> rfl
  · rfl

lemma emit_preserves_explicitKeyCol (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).explicitKeyCol = s.explicitKeyCol := by
  unfold ScannerState.emit
  rfl

lemma unwindIndentsLoop_preserves_explicitKeyCol (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · rw [ih]; exact emit_preserves_explicitKeyCol s .blockEnd
    · rfl

lemma unwindIndents_preserves_explicitKeyCol (s : ScannerState) (col : Int) :
    (unwindIndents s col).explicitKeyCol = s.explicitKeyCol := by
  unfold unwindIndents
  exact unwindIndentsLoop_preserves_explicitKeyCol s col s.indents.size

lemma saveSimpleKey_preserves_explicitKeyCol (s : ScannerState) :
    (saveSimpleKey s).explicitKeyCol = s.explicitKeyCol := by
  unfold saveSimpleKey
  split <;> (try rfl)
  split <;> rfl

lemma consumeNewline_preserves_explicitKeyCol (s : ScannerState) :
    (consumeNewline s).explicitKeyCol = s.explicitKeyCol := by
  unfold consumeNewline
  split
  · exact advance_preserves_explicitKeyCol s
  · dsimp only []
    split
    · exact advance_preserves_explicitKeyCol s
    · exact advance_preserves_explicitKeyCol s
  · rfl

lemma skipSpaces_preserves_explicitKeyCol (s : ScannerState) :
    (skipSpaces s).explicitKeyCol = s.explicitKeyCol := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop; split
    · rw [IH, advance_preserves_explicitKeyCol]
    · rfl

lemma skipWhitespace_preserves_explicitKeyCol (s : ScannerState) :
    (skipWhitespace s).explicitKeyCol = s.explicitKeyCol := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [IH, advance_preserves_explicitKeyCol]
      · rfl
    · rfl

lemma collectCommentTextLoop_preserves_explicitKeyCol (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_explicitKeyCol]
    · rfl

lemma skipToContentWs_preserves_explicitKeyCol (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') :
    s'.explicitKeyCol = s.explicitKeyCol := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyCol,
            skipSpaces_preserves_explicitKeyCol]
        · split at h
          · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyCol,
              skipSpaces_preserves_explicitKeyCol]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyCol,
                skipSpaces_preserves_explicitKeyCol]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyCol,
            skipSpaces_preserves_explicitKeyCol]
      · simp at h; rw [← h, skipSpaces_preserves_explicitKeyCol]
    · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyCol,
        skipSpaces_preserves_explicitKeyCol]
  · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyCol]

lemma skipToContentComment_preserves_explicitKeyCol (s : ScannerState) :
    (skipToContentComment s).explicitKeyCol = s.explicitKeyCol := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_explicitKeyCol, advance_preserves_explicitKeyCol]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_explicitKeyCol, advance_preserves_explicitKeyCol]
      · rfl
  · rfl

lemma skipToContentLoop_preserves_explicitKeyCol (s : ScannerState) (s' : ScannerState)
    (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [← h]
  | succ fuel' IH =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · rename_i c hpeek
        split at h
        · split at h
          · have ih := IH _ h
            rw [ih, consumeNewline_preserves_explicitKeyCol,
                skipToContentComment_preserves_explicitKeyCol]
            exact skipToContentWs_preserves_explicitKeyCol s s1 hws
          · have ih := IH _ h
            rw [ih, consumeNewline_preserves_explicitKeyCol,
                skipToContentComment_preserves_explicitKeyCol]
            exact skipToContentWs_preserves_explicitKeyCol s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_explicitKeyCol]
          exact skipToContentWs_preserves_explicitKeyCol s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_explicitKeyCol]
        exact skipToContentWs_preserves_explicitKeyCol s s1 hws

lemma skipToContent_preserves_explicitKeyCol (s : ScannerState) (s' : ScannerState) :
    skipToContent s = .ok s' →
    s'.explicitKeyCol = s.explicitKeyCol := by
  intro h
  unfold skipToContent at h
  exact skipToContentLoop_preserves_explicitKeyCol s s' _ h


/-! ## §4  `explicitKeyCol`: the content, props and block-scalar scans -/


/-! ## `explicitKeyCol` through the CONTENT scans (item 101)

Item 48 carried the stamp through the preprocessing chain, which is where a
block dispatch reads it.  A CONTENT dispatch reads it one step further on: the
`[189]` implicit value's own content parks a pending, and the `:` that meets
that park is refused by `scanValueValidate` for the same reason the one at the
value indicator was.  `scanValue` is still the field's only writer, so the four
value-completing scans carry it unchanged — the ladder below mirrors the
`simpleKey` one lemma-for-lemma, same functions, same branch structure. -/

lemma collectHexDigitsLoop_preserves_explicitKeyCol (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.explicitKeyCol = s.explicitKeyCol := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_explicitKeyCol s
        rw [ih, h_adv]
      · rfl


lemma parseHexEscape_preserves_explicitKeyCol (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.explicitKeyCol = s.explicitKeyCol := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_explicitKeyCol s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]


lemma processEscape_preserves_explicitKeyCol (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.explicitKeyCol = s.explicitKeyCol := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  -- Split on each character case
  repeat' (split at h)
  -- Handle all goals
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_explicitKeyCol s)
    | (have h_adv := advance_preserves_explicitKeyCol s
       have h_hex := parseHexEscape_preserves_explicitKeyCol s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )


lemma skipBlankLinesLoop_preserves_explicitKeyCol (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.explicitKeyCol = s.explicitKeyCol := by
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
        have h_sp := skipWhitespace_preserves_explicitKeyCol s
        have h_cn := consumeNewline_preserves_explicitKeyCol (skipWhitespace s)
        -- item 100: the gate's arm keeps the state untouched
        split
        · rfl
        · rw [ih, h_cn, h_sp]


lemma foldQuotedNewlinesLoop_preserves_explicitKeyCol (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.explicitKeyCol = s.explicitKeyCol := by
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
        have h_sp := skipWhitespace_preserves_explicitKeyCol s
        have h_cn := consumeNewline_preserves_explicitKeyCol (skipWhitespace s)
        split
        · rfl
        · rw [ih, h_cn, h_sp]


lemma foldQuotedNewlines_preserves_explicitKeyCol (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.explicitKeyCol = s.explicitKeyCol := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_explicitKeyCol s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_explicitKeyCol (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_explicitKeyCol (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_explicitKeyCol (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  -- 4.32.0 reshaped the do-notation match tree; split fully, then close every
  -- leaf uniformly (error leaves by contradiction, ok leaves by the fold chain).
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn])


lemma collectPlainScalarLoop_preserves_explicitKeyCol (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.explicitKeyCol = s.explicitKeyCol := by
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
        rw [ScanHelpers.collectPlainScalar_terminates?_state _ _ _ _ _ _ hterm]
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
              have h_fold := foldQuotedNewlines_preserves_explicitKeyCol s s_fold content_fold heq
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · -- recurse with content-length check
                -- item 50: the flow floor's throw contradicts `.ok`
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
              have hprop : s'.explicitKeyCol = s.explicitKeyCol := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipWhitespace_preserves_explicitKeyCol, skipSpaces_preserves_explicitKeyCol,
                    skipBlankLinesLoop_preserves_explicitKeyCol, consumeNewline_preserves_explicitKeyCol]
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
            have h_adv := advance_preserves_explicitKeyCol s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · -- regular content
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- plainSafe → recurse
              simp only [] at h
              have h_adv := advance_preserves_explicitKeyCol s
              rw [ih s.advance _ "" h, h_adv]


lemma collectDoubleQuotedLoop_preserves_explicitKeyCol (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.explicitKeyCol = s.explicitKeyCol := by
  -- protectedLen (default 0) is generalised so the IH covers the fold
  -- boundary the recursive call shifts (B2).
  suffices H : ∀ (p : Nat) (s : ScannerState) (content : String) (result : String × ScannerState),
      collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd p = .ok result →
      result.snd.explicitKeyCol = s.explicitKeyCol by
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
      exact advance_preserves_explicitKeyCol s
    · -- some '\\' case (escape sequence)
      simp only [] at h
      split at h <;> try contradiction
      -- some c after backslash
      split at h
      · -- isLineBreak c (escaped line break; item 53 splits the branch)
        have h_adv := advance_preserves_explicitKeyCol s
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_explicitKeyCol s.advance s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold, h_adv])
      · -- regular escape sequence
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_explicitKeyCol s.advance ch s_after_escape heq
          have h_adv := advance_preserves_explicitKeyCol s
          rw [ih _ _ _ h, h_proc, h_adv]
    · -- some c case (regular character)
      split at h
      · -- isLineBreak c
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_explicitKeyCol s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold])
      · -- regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_explicitKeyCol s
        rw [ih _ _ _ h, h_adv]


lemma collectSingleQuotedLoop_preserves_explicitKeyCol (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.explicitKeyCol = s.explicitKeyCol := by
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
        have h_adv1 := advance_preserves_explicitKeyCol s
        have h_adv2 := advance_preserves_explicitKeyCol s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · -- closing quote
        injection h with h_eq; cases h_eq
        exact advance_preserves_explicitKeyCol s
    · -- some c case (not quote)
      split at h
      · -- isLineBreak c = true
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_explicitKeyCol s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih s_fold _ h, h_fold])
      · -- isLineBreak c = false, regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_explicitKeyCol s
        rw [ih s.advance _ h, h_adv]


lemma collectAnchorNameLoop_preserves_explicitKeyCol (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.explicitKeyCol = s.explicitKeyCol := by
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
        exact advance_preserves_explicitKeyCol s
      · -- condition false: return
        rfl
    · -- none
      rfl

lemma emitAt_preserves_explicitKeyCol (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).explicitKeyCol = s.explicitKeyCol := by
  unfold ScannerState.emitAt; rfl

lemma scanAnchorOrAlias_preserves_explicitKeyCol (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [emitAt_preserves_explicitKeyCol, collectAnchorNameLoop_preserves_explicitKeyCol,
          advance_preserves_explicitKeyCol]

lemma scanPlainScalar_preserves_explicitKeyCol (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') : s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h; subst h
  simp [emitAt_preserves_explicitKeyCol]
  exact collectPlainScalarLoop_preserves_explicitKeyCol s "" "" _ _ _ _ result heq

lemma scanDoubleQuoted_preserves_explicitKeyCol (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') : s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_explicitKeyCol]
    have := collectDoubleQuotedLoop_preserves_explicitKeyCol s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_explicitKeyCol]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_explicitKeyCol]
    have := collectDoubleQuotedLoop_preserves_explicitKeyCol s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_explicitKeyCol]

lemma scanSingleQuoted_preserves_explicitKeyCol (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') : s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_explicitKeyCol]
    have := collectSingleQuotedLoop_preserves_explicitKeyCol s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_explicitKeyCol]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_explicitKeyCol]
    have := collectSingleQuotedLoop_preserves_explicitKeyCol s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_explicitKeyCol]

/-! ### … and through the TAG scan (item 102)

The props run's own head is `&`/`!`, which the content ladder above excludes:
`dispatchContent_explicitKeyCol` reads a value-completing character.  A
`[96]` run parks before its content, so the stamp has to survive the property
scan itself before the run's content can carry it — the anchor half is
`scanAnchorOrAlias_preserves_explicitKeyCol` above, and this is the tag
half, mirroring the `simpleKey` ladder lemma-for-lemma. -/

lemma collectVerbatimTagLoop_preserves_explicitKeyCol (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_explicitKeyCol s  -- found '>', return (uri, s.advance)
    · split  -- isUriCharBool
      · rw [ih]; exact advance_preserves_explicitKeyCol s  -- uri char, recurse
      · rfl  -- not uri char, return (uri, s)
    · simp only []  -- none, return (uri, s)

lemma collectTagSuffixLoop_preserves_explicitKeyCol (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_explicitKeyCol s  -- tag char, recurse
      · simp only []  -- not tag char, return
    · simp only []  -- none, return

lemma collectTagHandleLoop_preserves_explicitKeyCol (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_explicitKeyCol s  -- found '!', return (chars, true, s.advance)
    · split  -- split on the if condition
      · rw [ih]; exact advance_preserves_explicitKeyCol s  -- word char, recurse
      · simp only []  -- not word char, return
    · simp only []  -- none, return

lemma scanVerbatimTag_preserves_explicitKeyCol (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp [emitAt_preserves_explicitKeyCol, collectVerbatimTagLoop_preserves_explicitKeyCol,
            advance_preserves_explicitKeyCol]

lemma scanSecondaryTag_preserves_explicitKeyCol (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).explicitKeyCol = s.explicitKeyCol := by
  unfold scanSecondaryTag
  simp [emitAt_preserves_explicitKeyCol, collectTagSuffixLoop_preserves_explicitKeyCol,
        advance_preserves_explicitKeyCol]

lemma scanNamedTag_preserves_explicitKeyCol (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).explicitKeyCol = s.explicitKeyCol := by
  unfold scanNamedTag
  simp only []
  split
  · simp [emitAt_preserves_explicitKeyCol, collectTagSuffixLoop_preserves_explicitKeyCol,
          collectTagHandleLoop_preserves_explicitKeyCol]
  · simp [emitAt_preserves_explicitKeyCol, collectTagSuffixLoop_preserves_explicitKeyCol,
          collectTagHandleLoop_preserves_explicitKeyCol]

lemma scanTag_preserves_explicitKeyCol (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have h := Except.ok.inj hok; subst h; dsimp only []
      simp [scanVerbatimTag_preserves_explicitKeyCol s.advance s.currentPos s_verb hv,
            advance_preserves_explicitKeyCol]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanSecondaryTag_preserves_explicitKeyCol, advance_preserves_explicitKeyCol]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanNamedTag_preserves_explicitKeyCol, advance_preserves_explicitKeyCol]


/-! ### … and through the BLOCK SCALAR, which totalizes the walk (item 103)

The stamp ladder above stops at the tag: items 101/102 needed the heads a
content dispatch reads as a KEY, and `|`/`>` is not one.  The flow interior
reads every head, so the last arm has to be walked too — and once it is, the
dispatch lemma is TOTAL and the three head-restricted readings above collapse
into it.  These are `ContentAllowDirectives.lean`'s walks with the field
renamed, for the reason stated there: both proofs bottom out in
`advance`/`emitAt`, which touch no field but their own. -/

lemma consumeExactSpaces_preserves_explicitKeyCol (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.explicitKeyCol = s.explicitKeyCol := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_explicitKeyCol s
    · rfl

lemma parseBlockHeaderLoop_preserves_explicitKeyCol (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_explicitKeyCol s
    · rw [ih]; exact advance_preserves_explicitKeyCol s
    · split
      · rw [ih]; exact advance_preserves_explicitKeyCol s
      · rfl
    · rfl

lemma collectLineContentLoop_preserves_explicitKeyCol (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_explicitKeyCol s
    · rfl

lemma collectBlockScalarLoop_preserves_explicitKeyCol (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.explicitKeyCol = s.explicitKeyCol := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_explicitKeyCol s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_explicitKeyCol, consumeExactSpaces_preserves_explicitKeyCol]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_explicitKeyCol,
                    collectLineContentLoop_preserves_explicitKeyCol, consumeExactSpaces_preserves_explicitKeyCol]
              · split
                · rfl
                · rw [collectLineContentLoop_preserves_explicitKeyCol, consumeExactSpaces_preserves_explicitKeyCol]
            · rw [collectLineContentLoop_preserves_explicitKeyCol, consumeExactSpaces_preserves_explicitKeyCol]

lemma scanBlockScalarSkipComment_preserves_explicitKeyCol (s : ScannerState) :
    (scanBlockScalarSkipComment s).explicitKeyCol = s.explicitKeyCol := by
  unfold scanBlockScalarSkipComment
  split
  · -- some '#'
    split
    · -- peekBack? = some c
      dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_explicitKeyCol, advance_preserves_explicitKeyCol]
      · rfl
    · -- peekBack? = none
      rfl
  · rfl

lemma scanBlockScalarConsumeNewline_preserves_explicitKeyCol (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_explicitKeyCol s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

lemma scanBlockScalarBody_preserves_explicitKeyCol (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos) (s' : ScannerState)
    (h_fl : s_nl.explicitKeyCol = s_orig.explicitKeyCol)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.explicitKeyCol = s_orig.explicitKeyCol := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_preserves_explicitKeyCol, collectBlockScalarLoop_preserves_explicitKeyCol, h_fl]

lemma scanBlockScalar_preserves_explicitKeyCol (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') : s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_explicitKeyCol s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_explicitKeyCol _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_explicitKeyCol,
              skipWhitespace_preserves_explicitKeyCol,
              parseBlockHeaderLoop_preserves_explicitKeyCol,
              advance_preserves_explicitKeyCol]) h

lemma dispatchContent_preserves_explicitKeyCol (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · -- '&': scanAnchorOrAlias bind
    split at h   -- item 9e: the property-run guard
    · simp at h
    generalize h_fn : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h; dsimp only []
      exact scanAnchorOrAlias_preserves_explicitKeyCol s true s_a h_fn
  · split at h
    · -- '*': alias
      split at h   -- item 9e: the property-run guard
      · simp at h
      split at h
      · simp at h
      · -- item 9h: peel `validateAliasClose`; the alias facts are unchanged.
        exact scanAnchorOrAlias_preserves_explicitKeyCol s false _ (aliasArm_scan_ok h)
    · split at h
      · -- '!': tag
        split at h   -- item 9e: the property-run guard
        · simp at h
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanTag_preserves_explicitKeyCol s s_t h_fn
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_explicitKeyCol _ _ (by assumption)
          | exact scanDoubleQuoted_preserves_explicitKeyCol _ _ (by assumption)
          | exact scanSingleQuoted_preserves_explicitKeyCol _ _ (by assumption)
          | exact scanPlainScalar_preserves_explicitKeyCol _ _ (by assumption)
          | (simp_all; done)


/-! ### … and through the FLOW indicators (item 103)

The stamp has to cross a whole flow COLLECTION to reach the close that may
read it as a key (`k: [1]: 2`), so the five indicators and the `?` are walked
here too.  None of them writes the field — `scanValue` is still its only
writer, and inside a flow even that one preserves it. -/

lemma pushMappingIndent_preserves_explicitKeyCol (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).explicitKeyCol = s.explicitKeyCol := by
  unfold pushMappingIndent; split
  · simp [emit_preserves_explicitKeyCol]
  · rfl

lemma scanFlowEntry_preserves_explicitKeyCol (s : ScannerState) (s' : ScannerState)
    (h : scanFlowEntry s = .ok s') : s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_explicitKeyCol, emit_preserves_explicitKeyCol]

lemma scanValueClearKey_preserves_explicitKeyCol (s : ScannerState) :
    (scanValueClearKey s).explicitKeyCol = s.explicitKeyCol := by
  unfold scanValueClearKey
  split
  · split
    · rfl
    · split <;> rfl
  · rfl



/-! ## §5  The writers: `scanKey`, `scanBlockEntry`, the flow brackets, the
preprocessing, and the `scanValue` DISCRIMINATORS

`explicitValue` in `scanValue`'s epilogue is
`s_kc.explicitKeyLine.isSome && !s_kc.simpleKey.possible &&
(s.inFlow || (s.col : Int) == s_kc.explicitKeyCol)` — three conjuncts, each
refutable from the pre-state without reading any line: the field itself, the
resolved key, and the indicator's own column against the frame's.  Every one
of the lemmas below is stated line-free for exactly that reason: the
landed-`:` consumer decides the branch from coordinates it already holds. -/

lemma pushSequenceIndent_preserves_explicitKeyLine (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).explicitKeyLine = s.explicitKeyLine := by
  unfold pushSequenceIndent; split
  · simp [emit_preserves_explicitKeyLine]
  · rfl

lemma pushSequenceIndent_preserves_explicitKeyCol (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).explicitKeyCol = s.explicitKeyCol := by
  unfold pushSequenceIndent; split
  · simp [emit_preserves_explicitKeyCol]
  · rfl

/-- `scanBlockEntry` writes `indents`, `tokens` and the arm — never the
    explicit-key registers. -/
lemma scanBlockEntry_preserves_explicitKey {s s' : ScannerState}
    (h : scanBlockEntry s = .ok s') :
    s'.explicitKeyLine = s.explicitKeyLine ∧ s'.explicitKeyCol = s.explicitKeyCol := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals constructor
  all_goals simp [advance_preserves_explicitKeyLine, emit_preserves_explicitKeyLine,
    advance_preserves_explicitKeyCol, emit_preserves_explicitKeyCol,
    pushSequenceIndent_preserves_explicitKeyLine, pushSequenceIndent_preserves_explicitKeyCol]

/-- `scanKey` SETS the pair: the `?`'s own line and column. -/
lemma scanKey_ok_explicitKey {s s' : ScannerState} (h : scanKey s = .ok s') :
    s'.explicitKeyLine = some s.line ∧ s'.explicitKeyCol = (s.col : Int) := by
  unfold scanKey at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals exact ⟨rfl, rfl⟩

/-- The flow opens clear the column register with the line (item 98's park). -/
lemma scanFlowSequenceStart_explicitKeyCol (s : ScannerState) :
    (scanFlowSequenceStart s).explicitKeyCol = -1 := rfl

lemma scanFlowMappingStart_explicitKeyCol (s : ScannerState) :
    (scanFlowMappingStart s).explicitKeyCol = -1 := rfl

/-- The flow ends restore the column register beside the line
    (`ScannerCorrectness.scanFlowSequenceEnd_ek_restored`'s second half). -/
lemma scanFlowSequenceEnd_explicitKeyCol (s : ScannerState) :
    (scanFlowSequenceEnd s).explicitKeyCol
      = (s.explicitKeyStack.back?.getD (none, -1)).2 := by
  unfold scanFlowSequenceEnd
  simp [emit_preserves_explicitKeyStack]

lemma scanFlowMappingEnd_explicitKeyCol (s : ScannerState) :
    (scanFlowMappingEnd s).explicitKeyCol
      = (s.explicitKeyStack.back?.getD (none, -1)).2 := by
  unfold scanFlowMappingEnd
  simp [emit_preserves_explicitKeyStack]

/-- Preprocessing either carries both registers — the skip chain, the unwind and
    the save write none of them — or ends them together (item 333: a sibling
    entry at or left of the `?`'s column closes the stale key). -/
lemma preprocess_explicitKey_cases (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    (s1.explicitKeyLine = s.explicitKeyLine ∧ s1.explicitKeyCol = s.explicitKeyCol) ∨
    (s.explicitKeyLine ≠ none ∧
      ∃ (t : ScannerState) (c' : Char), t.peek? = some c' ∧ s1 = (t.closeStaleAt c').readPendingKey) := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_l_skip := skipToContent_preserves_explicitKeyLine s s_skip h_skip
    have h_c_skip := skipToContent_preserves_explicitKeyCol s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            by_cases h_dead : s.explicitKeyLine = none
            · have h_dead' : (saveSimpleKey
                  { unwindIndents s_skip s_skip.col with needIndentCheck := false }).explicitKeyLine
                  = none := by
                rw [saveSimpleKey_preserves_explicitKeyLine]
                show (unwindIndents s_skip s_skip.col).explicitKeyLine = none
                rw [unwindIndents_preserves_explicitKeyLine, h_l_skip, h_dead]
              rw [closeStaleExplicitKey_of_ek_none _ h_dead']
              left
              rw [saveSimpleKey_preserves_explicitKeyLine, saveSimpleKey_preserves_explicitKeyCol]
              constructor
              · show (unwindIndents s_skip s_skip.col).explicitKeyLine = s.explicitKeyLine
                rw [unwindIndents_preserves_explicitKeyLine]; exact h_l_skip
              · show (unwindIndents s_skip s_skip.col).explicitKeyCol = s.explicitKeyCol
                rw [unwindIndents_preserves_explicitKeyCol]; exact h_c_skip
            · rcases closeStaleExplicitKey_cases
                  (saveSimpleKey { unwindIndents s_skip s_skip.col with needIndentCheck := false })
                with h_eq | ⟨_, hc, h_eq⟩ <;> rw [h_eq]
              · left
                rw [saveSimpleKey_preserves_explicitKeyLine, saveSimpleKey_preserves_explicitKeyCol]
                constructor
                · show (unwindIndents s_skip s_skip.col).explicitKeyLine = s.explicitKeyLine
                  rw [unwindIndents_preserves_explicitKeyLine]; exact h_l_skip
                · show (unwindIndents s_skip s_skip.col).explicitKeyCol = s.explicitKeyCol
                  rw [unwindIndents_preserves_explicitKeyCol]; exact h_c_skip
              · right; exact ⟨h_dead, _, _, hc, rfl⟩
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            by_cases h_dead : s.explicitKeyLine = none
            · have h_dead' : (saveSimpleKey s_skip).explicitKeyLine = none := by
                rw [saveSimpleKey_preserves_explicitKeyLine, h_l_skip, h_dead]
              rw [closeStaleExplicitKey_of_ek_none _ h_dead']
              left
              rw [saveSimpleKey_preserves_explicitKeyLine, saveSimpleKey_preserves_explicitKeyCol]
              exact ⟨h_l_skip, h_c_skip⟩
            · rcases closeStaleExplicitKey_cases (saveSimpleKey s_skip) with h_eq | ⟨_, hc, h_eq⟩ <;> rw [h_eq]
              · left
                rw [saveSimpleKey_preserves_explicitKeyLine, saveSimpleKey_preserves_explicitKeyCol]
                exact ⟨h_l_skip, h_c_skip⟩
              · right; exact ⟨h_dead, _, _, hc, rfl⟩

/-- A dead register stays dead through preprocessing: both arms of
    `preprocess_explicitKey_cases` end at `none`. -/
lemma preprocess_explicitKeyLine_none (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (h0 : s.explicitKeyLine = none) : s1.explicitKeyLine = none := by
  rcases preprocess_explicitKey_cases s s1 c h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h1.trans h0
  · exact absurd h0 h1

/-! ### `scanValueClearKey`: what survives the phantom clear -/

/-- The clear writes `simpleKey` alone, so both scans read the same cursor. -/
lemma scanValueClearKey_cursor (s : ScannerState) :
    (scanValueClearKey s).offset = s.offset ∧
    (scanValueClearKey s).input = s.input ∧
    (scanValueClearKey s).inputEnd = s.inputEnd := by
  unfold scanValueClearKey
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- `scanValuePrepare` writes tokens, key state and indents — same cursor. -/
lemma scanValuePrepare_cursor (s : ScannerState) :
    (scanValuePrepare s).offset = s.offset ∧
    (scanValuePrepare s).input = s.input ∧
    (scanValuePrepare s).inputEnd = s.inputEnd ∧
    (scanValuePrepare s).line = s.line := by
  unfold scanValuePrepare pushMappingIndent
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- A key saved strictly behind the cursor on the cursor's own line survives
    the clear: branch (1) needs the save AT the indicator, branch (2) needs it
    on the `?`'s line while the cursor is off it. -/
lemma scanValueClearKey_keeps_key {s : ScannerState}
    (_h_poss : s.simpleKey.possible = true)
    (h_off : s.simpleKey.pos.offset ≠ s.offset)
    (h_kline : s.simpleKey.pos.line = s.line) :
    (scanValueClearKey s).simpleKey = s.simpleKey := by
  unfold scanValueClearKey
  split
  · rename_i ekLine hek
    split
    · rename_i hcl
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcl
      exact absurd hcl.1.2 h_off
    · split
      · rename_i _ hcl2
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcl2
        exact absurd (h_kline ▸ hcl2.1.1.2) hcl2.1.2
      · rfl
  · rfl

/-! ### The `scanValue` discriminators, line-free -/

/-- `peek?` reads only the cursor triple. -/
private lemma peek?_congr' {s₁ s₂ : ScannerState}
    (ho : s₁.offset = s₂.offset) (hi : s₁.input = s₂.input)
    (he : s₁.inputEnd = s₂.inputEnd) :
    s₁.peek? = s₂.peek? := by
  unfold ScannerState.peek?
  rw [ho, hi, he]

/-- The epilogue's advance stays on the `:`'s own line. -/
private lemma scanValue_epilogue_line {s : ScannerState}
    (h_peek : s.peek? = some ':') :
    (((scanValuePrepare (scanValueClearKey s)).emit .value).advance).line = s.line := by
  obtain ⟨hck_off, hck_in, hck_end⟩ := scanValueClearKey_cursor s
  obtain ⟨hp_off, hp_in, hp_end, hp_line⟩ := scanValuePrepare_cursor (scanValueClearKey s)
  have h_peek_prep : ((scanValuePrepare (scanValueClearKey s)).emit .value).peek?
      = some ':' := by
    rw [peek?_congr' (s₂ := s)
      (by rw [show ((scanValuePrepare (scanValueClearKey s)).emit .value).offset
            = (scanValuePrepare (scanValueClearKey s)).offset from rfl, hp_off, hck_off])
      (by rw [show ((scanValuePrepare (scanValueClearKey s)).emit .value).input
            = (scanValuePrepare (scanValueClearKey s)).input from rfl, hp_in, hck_in])
      (by rw [show ((scanValuePrepare (scanValueClearKey s)).emit .value).inputEnd
            = (scanValuePrepare (scanValueClearKey s)).inputEnd from rfl, hp_end, hck_end])]
    exact h_peek
  rw [advance_preserves_line_of_ne_break _ ':'
        h_peek_prep (by decide) (by decide),
      show ((scanValuePrepare (scanValueClearKey s)).emit .value).line
        = (scanValuePrepare (scanValueClearKey s)).line from rfl,
      hp_line, (L4YAML.Proofs.PreprocessIndentStable.scanValueClearKey_fields s).2.2.2.2.2.1]

/-- **No pending `?`: the `:` STAMPS and leaves the field down.**  The first
    conjunct of `explicitValue` is refuted by the field itself. -/
lemma scanValue_ok_of_ekl_none {s s' : ScannerState}
    (h : scanValue s = .ok s') (h_noflow : s.inFlow = false)
    (h_peek : s.peek? = some ':')
    (h_ek : s.explicitKeyLine = none) :
    s'.implicitValueLine = some s'.line ∧ s'.explicitKeyLine = none := by
  have h_ek_kc : (scanValueClearKey s).explicitKeyLine = none :=
    (scanValueClearKey_preserves_explicitKeyLine s).trans h_ek
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · have h' := Except.ok.inj h
        subst h'
        constructor
        · show (if s.inFlow || _ then _ else some s.line) = _
          rw [h_noflow, h_ek_kc]
          simp only [Option.isSome_none, Bool.false_and, Bool.false_or, ite_eq_right
            (by simp : ¬((false : Bool) = true))]
          rw [scanValue_epilogue_line h_peek]
        · show (if s.inFlow = true then _
              else if _ then (_, (scanValueClearKey s).explicitKeyLine, _)
              else PendingKeys.close _ _ _).2.1 = none
          rw [ite_eq_right (by rw [h_noflow]; exact Bool.false_ne_true), h_ek_kc]
          simp [scanValueKeySurvives, h_noflow, h_ek_kc]

/-- **Live `?`, the `:` OFF the frame's column: the `:` STAMPS.**  The third
    conjunct of `explicitValue` is refuted by the two columns alone. -/
lemma scanValue_stamp_of_col_ne {s s' : ScannerState}
    (h : scanValue s = .ok s') (h_noflow : s.inFlow = false)
    (h_peek : s.peek? = some ':')
    (h_ne : (s.col : Int) ≠ s.explicitKeyCol) :
    s'.implicitValueLine = some s'.line := by
  have h_kc : (scanValueClearKey s).explicitKeyCol = s.explicitKeyCol :=
    scanValueClearKey_preserves_explicitKeyCol s
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · have h' := Except.ok.inj h
        subst h'
        show (if s.inFlow || _ then _ else some s.line) = _
        rw [h_noflow, h_kc]
        simp only [Bool.false_or, beq_eq_false_iff_ne.mpr h_ne, Bool.and_false,
          ite_eq_right (by simp : ¬((false : Bool) = true))]
        rw [scanValue_epilogue_line h_peek]

/-- **A live key resolves: the `:` STAMPS.**  The second conjunct of
    `explicitValue` is refuted by the key that survives the clear. -/
lemma scanValue_stamp_of_key {s s' : ScannerState}
    (h : scanValue s = .ok s') (h_noflow : s.inFlow = false)
    (h_peek : s.peek? = some ':')
    (h_poss : s.simpleKey.possible = true)
    (h_off : s.simpleKey.pos.offset ≠ s.offset)
    (h_kline : s.simpleKey.pos.line = s.line) :
    s'.implicitValueLine = some s'.line := by
  have h_keep : (scanValueClearKey s).simpleKey = s.simpleKey :=
    scanValueClearKey_keeps_key h_poss h_off h_kline
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · have h' := Except.ok.inj h
        subst h'
        show (if s.inFlow || _ then _ else some s.line) = _
        rw [h_noflow, h_keep, h_poss]
        simp only [Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_or,
          ite_eq_right (by simp : ¬((false : Bool) = true))]
        rw [scanValue_epilogue_line h_peek]

/-- **A key that SURVIVES the clear: the `:` STAMPS** (item 185).

    `scanValue_stamp_of_key` above asks for the key's three coordinates
    because it reconstructs the survival from them
    (`scanValueClearKey_keeps_key`).  The field `explicitValue` actually reads
    is the CLEARED state's, and that is decidable on the dispatch state like
    the other two conjuncts — so this is the same discriminator with its
    premise taken where the definition takes it, and it is what makes item
    125's split TOTAL rather than two thirds of one. -/
lemma scanValue_stamp_of_cleared_key {s s' : ScannerState}
    (h : scanValue s = .ok s') (h_noflow : s.inFlow = false)
    (h_peek : s.peek? = some ':')
    (h_poss : (scanValueClearKey s).simpleKey.possible = true) :
    s'.implicitValueLine = some s'.line := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · have h' := Except.ok.inj h
        subst h'
        show (if s.inFlow || _ then _ else some s.line) = _
        rw [h_noflow, h_poss]
        simp only [Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_or,
          ite_eq_right (by simp : ¬((false : Bool) = true))]
        rw [scanValue_epilogue_line h_peek]

/-- **§8.2.2 [197] read BACKWARDS** (item 185): a block `:` that the validate
    ADMITS with a live `?` register and no surviving key stands at the
    mapping's own indent and off the `?`'s line.

    The two throws are the spec's own `l-block-map-explicit-value(n) =
    s-indent(n) ':' …`: the `l-` prefix puts the `:` on a line of its own, and
    `s-indent(n)` is exact.  A consumer that has just refuted all three
    `explicitValue` alternatives knows this `:` IS the explicit value, so it
    also knows the two coordinates the scanner already tested for it. -/
lemma scanValueValidate_explicit_at_indent {s : ScannerState} {ekLine : Nat}
    (h : scanValueValidate s = .ok ())
    (h_noflow : s.inFlow = false)
    (h_ek : s.explicitKeyLine = some ekLine)
    (h_poss : s.simpleKey.possible = false) :
    s.line ≠ ekLine ∧ (s.col : Int) = s.currentIndent := by
  unfold scanValueValidate at h
  simp only [bind, Except.bind, h_ek, h_poss, h_noflow, Bool.false_and,
    Bool.not_false, Bool.and_true, Bool.and_self,
    ite_eq_right (by simp : ¬((false : Bool) = true))] at h
  rw [ite_eq_left trivial] at h
  have hline : s.line ≠ ekLine := by
    intro hl
    rw [ite_eq_left (by simp [hl])] at h
    simp at h
  rw [ite_eq_right (by simp [hline])] at h
  refine ⟨hline, ?_⟩
  by_cases hne : (s.col : Int) = s.currentIndent
  · exact hne
  · rw [ite_eq_left (by simp [hne])] at h
    simp at h

/-- The same, read off a `:` dispatch that SUCCEEDED (item 185). -/
lemma scanValue_explicit_at_indent {s s' : ScannerState} {ekLine : Nat}
    (h : scanValue s = .ok s') (h_noflow : s.inFlow = false)
    (h_ek : s.explicitKeyLine = some ekLine)
    (h_poss : (scanValueClearKey s).simpleKey.possible = false) :
    s.line ≠ ekLine ∧ (s.col : Int) = s.currentIndent := by
  have h_val : scanValueValidate (scanValueClearKey s) = .ok () := by
    unfold scanValue at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i u hv
      cases u
      exact hv
  obtain ⟨hcol, hind, hflow, _, hekl, hline, _⟩ :=
    L4YAML.Proofs.PreprocessIndentStable.scanValueClearKey_fields s
  have h_ci : (scanValueClearKey s).currentIndent = s.currentIndent :=
    L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq hind
  have := scanValueValidate_explicit_at_indent (ekLine := ekLine) h_val
    (by rw [hflow]; exact h_noflow) (by rw [hekl]; exact h_ek) h_poss
  rw [hline, hcol, h_ci] at this
  exact this

/-- **The `:` whose coordinate does not exceed the frame's column CLOSES the
    frame's level** (step 4, item 335): in flow the register dies; in block a dead
    register stays dead, and a live one is re-read off the pending-key stack with
    the level at `s.explicitKeyCol` closed — so an outer `?` survives. -/
lemma scanValue_ekl_none_of_col_le {s s' : ScannerState}
    (h : scanValue s = .ok s')
    (h_kcol : s.simpleKey.possible = true → (s.simpleKey.pos.col : Int) ≤ s.explicitKeyCol)
    (h_col : (s.col : Int) ≤ s.explicitKeyCol) :
    s'.explicitKeyLine = none ∨
    ∃ cols pks, s'.explicitKeyLine = (PendingKeys.close cols pks s.explicitKeyCol).2.1 ∧
      s'.explicitKeyCol = (PendingKeys.close cols pks s.explicitKeyCol).2.2 := by
  have h_kc : (scanValueClearKey s).explicitKeyCol = s.explicitKeyCol :=
    scanValueClearKey_preserves_explicitKeyCol s
  have h_sk := L4YAML.Proofs.PreprocessIndentStable.scanValueClearKey_simpleKey s
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · have h' := Except.ok.inj h
        subst h'
        show (if s.inFlow = true then _
            else if _ then (_, (scanValueClearKey s).explicitKeyLine, _)
            else PendingKeys.close _ _ (scanValueClearKey s).explicitKeyCol).2.1 = none ∨ _
        by_cases hf : s.inFlow = true
        · rw [ite_eq_left hf]; exact Or.inl rfl
        · rw [ite_eq_right hf]
          by_cases hsv : scanValueKeySurvives s (scanValueClearKey s) = true
          · rw [ite_eq_left hsv]
            left
            unfold scanValueKeySurvives at hsv
            simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hsv
            rcases hsv with ⟨-, h0 | ⟨-, hgt⟩⟩
            · simpa using h0
            · exfalso
              rw [h_kc] at hgt
              split at hgt
              · rename_i h_poss_kc
                rcases h_sk with h_eq | h_false
                · rw [h_eq] at hgt h_poss_kc
                  exact absurd hgt (Int.not_lt.mpr (h_kcol h_poss_kc))
                · rw [h_false] at h_poss_kc; cases h_poss_kc
              · exact absurd hgt (Int.not_lt.mpr h_col)
          · rw [ite_eq_right hsv, h_kc]
            exact Or.inr ⟨_, _, rfl, rfl⟩

/-- **When the field survives the `:`, it survived from a live pre-state with
    the column register unchanged — or it is the re-read of the pending-key
    stack with the pre-state's level closed** (step 4, item 335): the second arm
    is the outer `?` an inner one's value uncovers. -/
lemma scanValue_ekl_some_source {s s' : ScannerState}
    (h : scanValue s = .ok s')
    (h_some : s'.explicitKeyLine.isSome = true) :
    (s'.explicitKeyLine = s.explicitKeyLine ∧ s'.explicitKeyCol = s.explicitKeyCol ∧
      s.explicitKeyLine.isSome = true) ∨
    ∃ cols pks, s'.explicitKeyLine = (PendingKeys.close cols pks s.explicitKeyCol).2.1 ∧
      s'.explicitKeyCol = (PendingKeys.close cols pks s.explicitKeyCol).2.2 := by
  have h_l : (scanValueClearKey s).explicitKeyLine = s.explicitKeyLine :=
    scanValueClearKey_preserves_explicitKeyLine s
  have h_c : (scanValueClearKey s).explicitKeyCol = s.explicitKeyCol :=
    scanValueClearKey_preserves_explicitKeyCol s
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · have h' := Except.ok.inj h
        subst h'
        revert h_some
        show ((if s.inFlow = true then _
            else if _ then (_, (scanValueClearKey s).explicitKeyLine,
              if (scanValueClearKey s).explicitKeyLine.isSome then (scanValueClearKey s).explicitKeyCol
              else -1)
            else PendingKeys.close _ _ (scanValueClearKey s).explicitKeyCol).2.1).isSome = true → _
        by_cases hf : s.inFlow = true
        · rw [ite_eq_left hf]; intro hh; simp at hh
        · rw [ite_eq_right hf]
          by_cases hsv : scanValueKeySurvives s (scanValueClearKey s) = true
          · rw [ite_eq_left hsv]
            intro hh
            left
            refine ⟨h_l, ?_, by rw [← h_l]; exact hh⟩
            show (if (scanValueClearKey s).explicitKeyLine.isSome = true
                then (scanValueClearKey s).explicitKeyCol else -1) = s.explicitKeyCol
            rw [ite_eq_left hh]; exact h_c
          · rw [ite_eq_right hsv, h_c]
            intro _
            exact Or.inr ⟨_, _, rfl, rfl⟩

/-! ## §6  The seeds -/

lemma mk'_explicitKeyLine (input : String) :
    (ScannerState.mk' input).explicitKeyLine = none := rfl

lemma mk'_explicitKeyCol (input : String) :
    (ScannerState.mk' input).explicitKeyCol = -1 := rfl

lemma consumeBOM_preserves_explicitKey (s : ScannerState) :
    s.consumeBOM.explicitKeyLine = s.explicitKeyLine ∧
    s.consumeBOM.explicitKeyCol = s.explicitKeyCol := by
  unfold ScannerState.consumeBOM
  constructor
  · simpa using advance_preserves_explicitKeyLine s
  · simpa using advance_preserves_explicitKeyCol s


/-! ### The document markers end the register (item 320)

`scanDocumentStart` and `scanDocumentEnd` write `explicitKeyLine := none` in their final update
(item 317: a marker ends every open node, the `?` frame among them).  These two lemmas are what a
marker park's dead-register field is paid with. -/

/-- The `---` scan's register, dead: the final update writes it. -/
lemma scanDocumentStart_explicitKeyLine (s : ScannerState) :
    (scanDocumentStart s).explicitKeyLine = none := by
  unfold scanDocumentStart
  rfl

/-- The `...` scan's register, dead on every arm of the scan that returns. -/
lemma scanDocumentEnd_explicitKeyLine {s s' : ScannerState}
    (hok : scanDocumentEnd s = .ok s') : s'.explicitKeyLine = none := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok; rfl)


end L4YAML.Proofs.ExplicitKeyCoupling

end Blanket
