/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScannerAllowDirectives

@[expose] public section Blanket

/-! # `allowDirectives` across CONTENT dispatch (β.3)

    The companion to `ScannerAllowDirectives.lean`, which walks the
    *preprocessing* prefix.  This file walks the other half:
    `scanNextToken_dispatchContent` and every scanner it can call.

    **Why it is needed.**  The accumulation's flow-interior invariant carries
    `sc.allowDirectives = false` (an open flow collection is always dispatched
    after `scanNextToken` cleared the flag), and every accum step has to
    re-establish it for the post-state.  `accum_step_flow` gets that from the
    five indicator scanners; `accum_step_content` needs it from the seven
    content ones, which is what `dispatchContent_preserves_allowDirectives`
    below provides.  It is the LAST hypothesis of the flow-interior content
    step that is not about the grammar.

    **Why the proofs look copied.**  They are: these are the
    `_preserves_flowLevel` walks of `ScannerCorrectness.lean` with the field
    renamed.  Both proofs are field-agnostic — unfold, split, fuel-induct, and
    bottom out in `advance`/`emitAt`, neither of which touches any field but its
    own — so the scripts transfer verbatim.  The two places the transfer FAILS
    are the two functions whose job is this field: `scanDocumentStart` and
    `scanDocumentEnd` re-open directives at a `---`/`...`, so their
    `_preserves_flowLevel` twins have no `allowDirectives` counterpart and are
    deliberately absent here.  Neither is reachable from content dispatch.

    Only the transitive closure of `dispatchContent_preserves_allowDirectives`
    is cloned; the rest of the `flowLevel` chain has no consumer. -/

namespace L4YAML.Proofs.ScannerAllowDirectives

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.CharPredicates

lemma emitAt_preserves_allowDirectives (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).allowDirectives = s.allowDirectives := by
  unfold ScannerState.emitAt; rfl

lemma collectAnchorNameLoop_preserves_allowDirectives (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.allowDirectives = s.allowDirectives := by
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
        exact advance_preserves_allowDirectives s
      · -- condition false: return
        rfl
    · -- none
      rfl

lemma scanAnchorOrAlias_preserves_allowDirectives (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.allowDirectives = s.allowDirectives := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [emitAt_preserves_allowDirectives, collectAnchorNameLoop_preserves_allowDirectives,
          advance_preserves_allowDirectives]

lemma collectVerbatimTagLoop_preserves_allowDirectives (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_allowDirectives s
    · split
      · rw [ih]; exact advance_preserves_allowDirectives s
      · rfl
    · simp only []

lemma collectTagSuffixLoop_preserves_allowDirectives (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_allowDirectives s
      · simp only []
    · simp only []

lemma collectTagHandleLoop_preserves_allowDirectives (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_allowDirectives s
    · split
      · rw [ih]; exact advance_preserves_allowDirectives s
      · simp only []
    · simp only []

lemma scanVerbatimTag_preserves_allowDirectives (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    s'.allowDirectives = s.allowDirectives := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp [emitAt_preserves_allowDirectives, collectVerbatimTagLoop_preserves_allowDirectives,
            advance_preserves_allowDirectives]

lemma scanSecondaryTag_preserves_allowDirectives (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).allowDirectives = s.allowDirectives := by
  unfold scanSecondaryTag
  simp [emitAt_preserves_allowDirectives, collectTagSuffixLoop_preserves_allowDirectives,
        advance_preserves_allowDirectives]

lemma scanNamedTag_preserves_allowDirectives (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).allowDirectives = s.allowDirectives := by
  unfold scanNamedTag
  simp only []
  split
  · simp [emitAt_preserves_allowDirectives, collectTagSuffixLoop_preserves_allowDirectives,
          collectTagHandleLoop_preserves_allowDirectives]
  · simp [emitAt_preserves_allowDirectives, collectTagSuffixLoop_preserves_allowDirectives,
          collectTagHandleLoop_preserves_allowDirectives]

lemma scanTag_preserves_allowDirectives (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.allowDirectives = s.allowDirectives := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have h := Except.ok.inj hok; subst h; dsimp only []
      simp [scanVerbatimTag_preserves_allowDirectives s.advance s.currentPos s_verb hv,
            advance_preserves_allowDirectives]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanSecondaryTag_preserves_allowDirectives, advance_preserves_allowDirectives]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanNamedTag_preserves_allowDirectives, advance_preserves_allowDirectives]

lemma skipBlankLinesLoop_preserves_allowDirectives (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.allowDirectives = s.allowDirectives := by
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
        have h_sp := skipWhitespace_preserves_allowDirectives s
        have h_cn := consumeNewline_preserves_allowDirectives (skipWhitespace s)
        -- item 100: the gate's arm keeps the state untouched
        split
        · rfl
        · rw [ih, h_cn, h_sp]

lemma foldQuotedNewlinesLoop_preserves_allowDirectives (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.allowDirectives = s.allowDirectives := by
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
        have h_sp := skipWhitespace_preserves_allowDirectives s
        have h_cn := consumeNewline_preserves_allowDirectives (skipWhitespace s)
        split
        · rfl
        · rw [ih, h_cn, h_sp]

lemma foldQuotedNewlines_preserves_allowDirectives (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.allowDirectives = s.allowDirectives := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_allowDirectives s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_allowDirectives (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_allowDirectives (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_allowDirectives (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  -- 4.32.0 reshaped the do-notation match tree; split fully, then close every
  -- leaf uniformly (error leaves by contradiction, ok leaves by the fold chain).
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn])

lemma collectHexDigitsLoop_preserves_allowDirectives (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.allowDirectives = s.allowDirectives := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_allowDirectives s
        rw [ih, h_adv]
      · rfl

lemma parseHexEscape_preserves_allowDirectives (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.allowDirectives = s.allowDirectives := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_allowDirectives s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]

lemma processEscape_preserves_allowDirectives (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.allowDirectives = s.allowDirectives := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  repeat (split at h)
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_allowDirectives s)
    | (have h_adv := advance_preserves_allowDirectives s
       have h_hex := parseHexEscape_preserves_allowDirectives s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )

lemma collectPlainScalarLoop_preserves_allowDirectives (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.allowDirectives = s.allowDirectives := by
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
              have h_fold := foldQuotedNewlines_preserves_allowDirectives s s_fold content_fold heq
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
              have hprop : s'.allowDirectives = s.allowDirectives := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipWhitespace_preserves_allowDirectives, skipSpaces_preserves_allowDirectives,
                    skipBlankLinesLoop_preserves_allowDirectives, consumeNewline_preserves_allowDirectives]
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
            have h_adv := advance_preserves_allowDirectives s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · -- regular content
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- plainSafe → recurse
              simp only [] at h
              have h_adv := advance_preserves_allowDirectives s
              rw [ih s.advance _ "" h, h_adv]

lemma collectDoubleQuotedLoop_preserves_allowDirectives (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.allowDirectives = s.allowDirectives := by
  -- protectedLen (default 0) is generalised so the IH covers the fold
  -- boundary the recursive call shifts (B2).
  suffices H : ∀ (p : Nat) (s : ScannerState) (content : String) (result : String × ScannerState),
      collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd p = .ok result →
      result.snd.allowDirectives = s.allowDirectives by
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
      exact advance_preserves_allowDirectives s
    · -- some '\\' case (escape sequence)
      simp only [] at h
      split at h <;> try contradiction
      -- some c after backslash
      split at h
      · -- isLineBreak c (escaped line break — the landing is a fold, item 87)
        have h_adv := advance_preserves_allowDirectives s
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_allowDirectives s.advance s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold, h_adv])
      · -- regular escape sequence
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_allowDirectives s.advance ch s_after_escape heq
          have h_adv := advance_preserves_allowDirectives s
          rw [ih _ _ _ h, h_proc, h_adv]
    · -- some c case (regular character)
      split at h
      · -- isLineBreak c
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_allowDirectives s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold])
      · -- regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_allowDirectives s
        rw [ih _ _ _ h, h_adv]

lemma collectSingleQuotedLoop_preserves_allowDirectives (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.allowDirectives = s.allowDirectives := by
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
        have h_adv1 := advance_preserves_allowDirectives s
        have h_adv2 := advance_preserves_allowDirectives s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · -- closing quote
        injection h with h_eq; cases h_eq
        exact advance_preserves_allowDirectives s
    · -- some c case (not quote)
      split at h
      · -- isLineBreak c = true
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_allowDirectives s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih s_fold _ h, h_fold])
      · -- isLineBreak c = false, regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_allowDirectives s
        rw [ih s.advance _ h, h_adv]

lemma consumeExactSpaces_preserves_allowDirectives (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.allowDirectives = s.allowDirectives := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_allowDirectives s
    · rfl

lemma parseBlockHeaderLoop_preserves_allowDirectives (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_allowDirectives s
    · rw [ih]; exact advance_preserves_allowDirectives s
    · split
      · rw [ih]; exact advance_preserves_allowDirectives s
      · rfl
    · rfl

lemma collectLineContentLoop_preserves_allowDirectives (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_allowDirectives s
    · rfl

lemma collectBlockScalarLoop_preserves_allowDirectives (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_allowDirectives s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_allowDirectives, consumeExactSpaces_preserves_allowDirectives]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_allowDirectives,
                    collectLineContentLoop_preserves_allowDirectives, consumeExactSpaces_preserves_allowDirectives]
              · split
                · rfl
                · rw [collectLineContentLoop_preserves_allowDirectives, consumeExactSpaces_preserves_allowDirectives]
            · rw [collectLineContentLoop_preserves_allowDirectives, consumeExactSpaces_preserves_allowDirectives]

lemma scanBlockScalarSkipComment_preserves_allowDirectives (s : ScannerState) :
    (scanBlockScalarSkipComment s).allowDirectives = s.allowDirectives := by
  unfold scanBlockScalarSkipComment
  split
  · -- some '#'
    split
    · -- peekBack? = some c
      dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_allowDirectives, advance_preserves_allowDirectives]
      · rfl
    · -- peekBack? = none
      rfl
  · rfl

lemma scanBlockScalarConsumeNewline_preserves_allowDirectives (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_allowDirectives s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

lemma scanBlockScalarBody_preserves_allowDirectives (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos) (s' : ScannerState)
    (h_fl : s_nl.allowDirectives = s_orig.allowDirectives)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.allowDirectives = s_orig.allowDirectives := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_preserves_allowDirectives, collectBlockScalarLoop_preserves_allowDirectives, h_fl]

lemma scanPlainScalar_preserves_allowDirectives (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h; subst h
  simp [emitAt_preserves_allowDirectives]
  exact collectPlainScalarLoop_preserves_allowDirectives s "" "" _ _ _ _ result heq

lemma scanDoubleQuoted_preserves_allowDirectives (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_allowDirectives]
    have := collectDoubleQuotedLoop_preserves_allowDirectives s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_allowDirectives]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_allowDirectives]
    have := collectDoubleQuotedLoop_preserves_allowDirectives s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_allowDirectives]

lemma scanSingleQuoted_preserves_allowDirectives (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_allowDirectives]
    have := collectSingleQuotedLoop_preserves_allowDirectives s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_allowDirectives]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_allowDirectives]
    have := collectSingleQuotedLoop_preserves_allowDirectives s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_allowDirectives]

lemma scanBlockScalar_preserves_allowDirectives (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_allowDirectives s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_allowDirectives _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_allowDirectives,
              skipWhitespace_preserves_allowDirectives,
              parseBlockHeaderLoop_preserves_allowDirectives,
              advance_preserves_allowDirectives]) h

lemma dispatchContent_preserves_allowDirectives (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    s'.allowDirectives = s.allowDirectives := by
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
      exact scanAnchorOrAlias_preserves_allowDirectives s true s_a h_fn
  · split at h
    · -- '*': alias
      split at h   -- item 9e: the property-run guard
      · simp at h
      split at h
      · simp at h
      · -- item 9h: peel `validateAliasClose`; the alias facts are unchanged.
        exact scanAnchorOrAlias_preserves_allowDirectives s false _ (aliasArm_scan_ok h)
    · split at h
      · -- '!': tag
        split at h   -- item 9e: the property-run guard
        · simp at h
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanTag_preserves_allowDirectives s s_t h_fn
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_allowDirectives _ _ (by assumption)
          | exact scanDoubleQuoted_preserves_allowDirectives _ _ (by assumption)
          | exact scanSingleQuoted_preserves_allowDirectives _ _ (by assumption)
          | exact scanPlainScalar_preserves_allowDirectives _ _ (by assumption)
          | (simp_all; done)

end L4YAML.Proofs.ScannerAllowDirectives

end Blanket
