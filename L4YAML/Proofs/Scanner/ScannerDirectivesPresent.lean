/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-! # `directivesPresent` across preprocessing and the three non-structural dispatches

    Only `Scanner/Document.lean` writes `directivesPresent` (`scanDirective`
    sets it, `scanDocumentStart`/`scanDocumentEnd` clear it).  This file walks
    `scanNextToken_preprocess`, `scanNextToken_dispatchFlowIndicators`,
    `scanNextToken_dispatchBlockIndicators` and `scanNextToken_dispatchContent`
    with every scanner they can call, so the directive-run invariant of
    `Proofs/Scanner/DirectiveRuns.lean` can carry the flag across a step.

    The scripts are the `directivesPresent` walks of `ScannerDirectivesPresent.lean`
    and `ContentDirectivesPresent.lean` with the field renamed: both are
    field-agnostic (unfold + split + fuel induction bottoming out in
    `emit`/`advance`), so they transfer verbatim.  The two `directivesPresent`-
    specific facts there (`dispatchStructural_inFlow_no_success`,
    `scanDirective_allowDirectives`) have no `directivesPresent` twin and are
    deliberately absent. -/

namespace L4YAML.Proofs.ScannerDirectivesPresent

open L4YAML.Proofs.CloseStaleExplicitKey
open L4YAML L4YAML.Scanner
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.CharPredicates


lemma advance_preserves_directivesPresent (s : ScannerState) :
    s.advance.directivesPresent = s.directivesPresent := by
  unfold ScannerState.advance; dsimp only []; split <;> (try split) <;> (try split) <;> rfl

lemma emit_preserves_directivesPresent (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).directivesPresent = s.directivesPresent := by
  unfold ScannerState.emit; rfl

lemma skipSpacesLoop_preserves_directivesPresent (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · exact (ih _).trans (advance_preserves_directivesPresent _)
    · rfl

lemma skipWhitespaceLoop_preserves_directivesPresent (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact (ih _).trans (advance_preserves_directivesPresent _)
      · rfl
    · rfl

lemma skipToEndOfLineLoop_preserves_directivesPresent (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · exact (ih _).trans (advance_preserves_directivesPresent _)
    · rfl

lemma skipSpaces_preserves_directivesPresent (s : ScannerState) :
    (skipSpaces s).directivesPresent = s.directivesPresent := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_directivesPresent s _

lemma skipWhitespace_preserves_directivesPresent (s : ScannerState) :
    (skipWhitespace s).directivesPresent = s.directivesPresent := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_directivesPresent s _

lemma skipToEndOfLine_preserves_directivesPresent (s : ScannerState) :
    (skipToEndOfLine s).directivesPresent = s.directivesPresent := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_directivesPresent s _

lemma collectCommentTextLoop_preserves_directivesPresent (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_directivesPresent]
    · rfl

lemma skipToContentWs_preserves_directivesPresent (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_preserves_directivesPresent, skipSpaces_preserves_directivesPresent]
        · split at h
          · simp at h; rw [← h, skipWhitespace_preserves_directivesPresent, skipSpaces_preserves_directivesPresent]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_directivesPresent, skipSpaces_preserves_directivesPresent]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_preserves_directivesPresent, skipSpaces_preserves_directivesPresent]
      · simp at h; rw [← h, skipSpaces_preserves_directivesPresent]
    · simp at h; rw [← h, skipWhitespace_preserves_directivesPresent, skipSpaces_preserves_directivesPresent]
  · simp at h; rw [← h, skipWhitespace_preserves_directivesPresent]

lemma skipToContentComment_preserves_directivesPresent (s : ScannerState) :
    (skipToContentComment s).directivesPresent = s.directivesPresent := by
  unfold skipToContentComment
  split
  · -- peek? = some '#'
    simp only []
    split  -- peekBack?
    · -- peekBack? = some c
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_directivesPresent, advance_preserves_directivesPresent]
      · rfl
    · -- peekBack? = none
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_directivesPresent, advance_preserves_directivesPresent]
      · rfl
  · rfl

lemma consumeNewline_preserves_directivesPresent (s : ScannerState) :
    (consumeNewline s).directivesPresent = s.directivesPresent := by
  unfold consumeNewline
  split
  · exact advance_preserves_directivesPresent s
  · simp only []; split
    · exact advance_preserves_directivesPresent _
    · exact advance_preserves_directivesPresent _
  · rfl

lemma skipToContentLoop_preserves_directivesPresent (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') : s'.directivesPresent = s.directivesPresent := by
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
          · have := ih _ h; rw [this, consumeNewline_preserves_directivesPresent,
              skipToContentComment_preserves_directivesPresent]; exact skipToContentWs_preserves_directivesPresent s s1 hws
          · have := ih _ h; rw [this, consumeNewline_preserves_directivesPresent,
              skipToContentComment_preserves_directivesPresent]; exact skipToContentWs_preserves_directivesPresent s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_directivesPresent]
          exact skipToContentWs_preserves_directivesPresent s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_directivesPresent]
        exact skipToContentWs_preserves_directivesPresent s s1 hws

lemma skipToContent_preserves_directivesPresent (s s' : ScannerState)
    (h : skipToContent s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold skipToContent at h; exact skipToContentLoop_preserves_directivesPresent s s' _ h

lemma unwindIndentsLoop_preserves_directivesPresent (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ _ ih =>
    unfold unwindIndentsLoop; split
    · have := ih { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop, pendingKeys := (s.emit .blockEnd).pendingKeys.pop }
      simp [emit_preserves_directivesPresent] at this; exact this
    · rfl

lemma unwindIndents_preserves_directivesPresent (s : ScannerState) (col : Int) :
    (unwindIndents s col).directivesPresent = s.directivesPresent := by
  unfold unwindIndents; exact unwindIndentsLoop_preserves_directivesPresent s col _

lemma saveSimpleKey_preserves_directivesPresent (st : ScannerState) :
    (saveSimpleKey st).directivesPresent = st.directivesPresent := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl
/-- `scanNextToken_preprocess` preserves `directivesPresent`: it is
    `skipToContent` → optional `unwindIndents` → `saveSimpleKey`, and none of
    the three touches the flag. -/
lemma preprocess_preserves_directivesPresent (s : ScannerState) (s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    s1.directivesPresent = s.directivesPresent := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_ad_skip := skipToContent_preserves_directivesPresent s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [closeStaleExplicitKey_directivesPresent, saveSimpleKey_preserves_directivesPresent]
            show (unwindIndents s_skip s_skip.col).directivesPresent = s.directivesPresent
            rw [unwindIndents_preserves_directivesPresent]; exact h_ad_skip
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [closeStaleExplicitKey_directivesPresent, saveSimpleKey_preserves_directivesPresent]; exact h_ad_skip

/-! ## No structural token succeeds inside an open flow (β.3)

    `scanNextToken_dispatchStructural` returns `.ok (some _)` from exactly three
    arms, and inside a flow collection all three are dead:

    * the `---` and `...` accept arms sit BELOW the §5.4 `documentMarkerInFlow`
      guard, which fires on precisely their trigger once `inFlow` holds;
    * the `%` arm reaches `scanDirective`, which rejects on `!directivesPresent`.

    The flag is false inside a flow because `scanNextToken` clears it before any
    flow indicator is dispatched, so the `[`/`{` that opened the collection
    cleared it. The accumulation carries that fact; this lemma consumes it. -/


lemma pushSequenceIndent_preserves_directivesPresent (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).directivesPresent = s.directivesPresent := by
  unfold pushSequenceIndent; split <;> rfl

lemma pushMappingIndent_preserves_directivesPresent (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).directivesPresent = s.directivesPresent := by
  unfold pushMappingIndent; split <;> rfl

/-- The `-` indicator's conditional push, at the shape the unfolded
    `scanBlockEntry` presents it in. -/
lemma ite_pushSequenceIndent_directivesPresent (s : ScannerState) :
    (if !s.inFlow then pushSequenceIndent s (s.col : Int) else s).directivesPresent
      = s.directivesPresent := by
  split
  · exact pushSequenceIndent_preserves_directivesPresent _ _
  · rfl

/-- The `?` indicator's conditional push, likewise. -/
lemma ite_pushMappingIndent_directivesPresent (s : ScannerState) :
    (if !s.inFlow then pushMappingIndent s (s.col : Int) else s).directivesPresent
      = s.directivesPresent := by
  split
  · exact pushMappingIndent_preserves_directivesPresent _ _
  · rfl

lemma scanBlockEntry_preserves_directivesPresent {s s' : ScannerState}
    (h : scanBlockEntry s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    first
      | (subst h
         simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent,
           ite_pushSequenceIndent_directivesPresent,
           pushSequenceIndent_preserves_directivesPresent])
      | (injection h with h
         subst h
         simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent,
           pushSequenceIndent_preserves_directivesPresent])
      | (exfalso; simp_all; done)

lemma scanKey_preserves_directivesPresent {s s' : ScannerState}
    (h : scanKey s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold scanKey at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    first
      | (subst h
         simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent,
           ite_pushMappingIndent_directivesPresent,
           pushMappingIndent_preserves_directivesPresent])
      | (injection h with h
         subst h
         simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent,
           pushMappingIndent_preserves_directivesPresent])
      | (exfalso; simp_all; done)

lemma scanValueClearKey_preserves_directivesPresent (s : ScannerState) :
    (scanValueClearKey s).directivesPresent = s.directivesPresent := by
  unfold scanValueClearKey
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

lemma scanValuePrepare_preserves_directivesPresent (s : ScannerState) :
    (scanValuePrepare s).directivesPresent = s.directivesPresent := by
  unfold scanValuePrepare
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · exact pushMappingIndent_preserves_directivesPresent _ _
      · rfl

lemma scanValue_preserves_directivesPresent {s s' : ScannerState}
    (h : scanValue s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    first
      | (subst h
         simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent,
           scanValuePrepare_preserves_directivesPresent,
           scanValueClearKey_preserves_directivesPresent])
      | (injection h with h
         subst h
         simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent,
           scanValuePrepare_preserves_directivesPresent,
           scanValueClearKey_preserves_directivesPresent])
      | (exfalso; simp_all; done)

/-- The block-indicator dispatcher never writes `directivesPresent`. -/
lemma dispatchBlockIndicators_preserves_directivesPresent {s s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    s'.directivesPresent = s.directivesPresent := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · simp at h
    · rename_i s_be h_be
      injection Except.ok.inj h with h
      subst h
      exact scanBlockEntry_preserves_directivesPresent h_be
  · split at h
    · split at h
      · simp at h
      · rename_i s_k h_k
        injection Except.ok.inj h with h
        subst h
        exact scanKey_preserves_directivesPresent h_k
    · split at h
      · split at h
        · simp at h
        · rename_i s_v h_v
          injection Except.ok.inj h with h
          subst h
          exact scanValue_preserves_directivesPresent h_v
      · exact absurd (Except.ok.inj h) nofun

lemma scanFlowSequenceStart_preserves_directivesPresent (s : ScannerState) :
    (scanFlowSequenceStart s).directivesPresent = s.directivesPresent := by
  unfold scanFlowSequenceStart
  simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent]

lemma scanFlowSequenceEnd_preserves_directivesPresent (s : ScannerState) :
    (scanFlowSequenceEnd s).directivesPresent = s.directivesPresent := by
  unfold scanFlowSequenceEnd
  simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent]

lemma scanFlowMappingStart_preserves_directivesPresent (s : ScannerState) :
    (scanFlowMappingStart s).directivesPresent = s.directivesPresent := by
  unfold scanFlowMappingStart
  simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent]

lemma scanFlowMappingEnd_preserves_directivesPresent (s : ScannerState) :
    (scanFlowMappingEnd s).directivesPresent = s.directivesPresent := by
  unfold scanFlowMappingEnd
  simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent]

lemma scanFlowEntry_preserves_directivesPresent {s s' : ScannerState}
    (h : scanFlowEntry s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;>
    first
      | (subst h
         simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent])
      | (injection h with h
         subst h
         simp only [advance_preserves_directivesPresent, emit_preserves_directivesPresent])
      | (exfalso; simp_all; done)

/-- The flow-indicator dispatcher never writes `directivesPresent` either. -/
lemma dispatchFlowIndicators_preserves_directivesPresent {s s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    s'.directivesPresent = s.directivesPresent := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    (try split at h) <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    first
      | (exfalso; simp_all; done)
      | (injection h with h
         injection h with h
         subst h
         simp only [scanFlowSequenceStart_preserves_directivesPresent,
           scanFlowSequenceEnd_preserves_directivesPresent,
           scanFlowMappingStart_preserves_directivesPresent,
           scanFlowMappingEnd_preserves_directivesPresent])
      | (rename_i h_fe
         injection h with h
         injection h with h
         subst h
         exact scanFlowEntry_preserves_directivesPresent h_fe)


lemma emitAt_preserves_directivesPresent (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).directivesPresent = s.directivesPresent := by
  unfold ScannerState.emitAt; rfl

lemma collectAnchorNameLoop_preserves_directivesPresent (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.directivesPresent = s.directivesPresent := by
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
        exact advance_preserves_directivesPresent s
      · -- condition false: return
        rfl
    · -- none
      rfl

lemma scanAnchorOrAlias_preserves_directivesPresent (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [emitAt_preserves_directivesPresent, collectAnchorNameLoop_preserves_directivesPresent,
          advance_preserves_directivesPresent]

lemma collectVerbatimTagLoop_preserves_directivesPresent (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_directivesPresent s
    · split
      · rw [ih]; exact advance_preserves_directivesPresent s
      · rfl
    · simp only []

lemma collectTagSuffixLoop_preserves_directivesPresent (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_directivesPresent s
      · simp only []
    · simp only []

lemma collectTagHandleLoop_preserves_directivesPresent (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_directivesPresent s
    · split
      · rw [ih]; exact advance_preserves_directivesPresent s
      · simp only []
    · simp only []

lemma scanVerbatimTag_preserves_directivesPresent (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp [emitAt_preserves_directivesPresent, collectVerbatimTagLoop_preserves_directivesPresent,
            advance_preserves_directivesPresent]

lemma scanSecondaryTag_preserves_directivesPresent (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).directivesPresent = s.directivesPresent := by
  unfold scanSecondaryTag
  simp [emitAt_preserves_directivesPresent, collectTagSuffixLoop_preserves_directivesPresent,
        advance_preserves_directivesPresent]

lemma scanNamedTag_preserves_directivesPresent (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).directivesPresent = s.directivesPresent := by
  unfold scanNamedTag
  simp only []
  split
  · simp [emitAt_preserves_directivesPresent, collectTagSuffixLoop_preserves_directivesPresent,
          collectTagHandleLoop_preserves_directivesPresent]
  · simp [emitAt_preserves_directivesPresent, collectTagSuffixLoop_preserves_directivesPresent,
          collectTagHandleLoop_preserves_directivesPresent]

lemma scanTag_preserves_directivesPresent (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have h := Except.ok.inj hok; subst h; dsimp only []
      simp [scanVerbatimTag_preserves_directivesPresent s.advance s.currentPos s_verb hv,
            advance_preserves_directivesPresent]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanSecondaryTag_preserves_directivesPresent, advance_preserves_directivesPresent]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanNamedTag_preserves_directivesPresent, advance_preserves_directivesPresent]

lemma skipBlankLinesLoop_preserves_directivesPresent (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.directivesPresent = s.directivesPresent := by
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
        have h_sp := skipWhitespace_preserves_directivesPresent s
        have h_cn := consumeNewline_preserves_directivesPresent (skipWhitespace s)
        -- item 100: the gate's arm keeps the state untouched
        split
        · rfl
        · rw [ih, h_cn, h_sp]

lemma foldQuotedNewlinesLoop_preserves_directivesPresent (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.directivesPresent = s.directivesPresent := by
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
        have h_sp := skipWhitespace_preserves_directivesPresent s
        have h_cn := consumeNewline_preserves_directivesPresent (skipWhitespace s)
        split
        · rfl
        · rw [ih, h_cn, h_sp]

lemma foldQuotedNewlines_preserves_directivesPresent (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.directivesPresent = s.directivesPresent := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_directivesPresent s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_directivesPresent (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_directivesPresent (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_directivesPresent (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  -- 4.32.0 reshaped the do-notation match tree; split fully, then close every
  -- leaf uniformly (error leaves by contradiction, ok leaves by the fold chain).
  repeat' split at h
  all_goals first
    | contradiction
    | (injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn])

lemma collectHexDigitsLoop_preserves_directivesPresent (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.directivesPresent = s.directivesPresent := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_directivesPresent s
        rw [ih, h_adv]
      · rfl

lemma parseHexEscape_preserves_directivesPresent (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.directivesPresent = s.directivesPresent := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_directivesPresent s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]

lemma processEscape_preserves_directivesPresent (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.directivesPresent = s.directivesPresent := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  repeat (split at h)
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_directivesPresent s)
    | (have h_adv := advance_preserves_directivesPresent s
       have h_hex := parseHexEscape_preserves_directivesPresent s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )

lemma collectPlainScalarLoop_preserves_directivesPresent (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.directivesPresent = s.directivesPresent := by
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
              have h_fold := foldQuotedNewlines_preserves_directivesPresent s s_fold content_fold heq
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
              have hprop : s'.directivesPresent = s.directivesPresent := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipWhitespace_preserves_directivesPresent, skipSpaces_preserves_directivesPresent,
                    skipBlankLinesLoop_preserves_directivesPresent, consumeNewline_preserves_directivesPresent]
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
            have h_adv := advance_preserves_directivesPresent s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · -- regular content
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- plainSafe → recurse
              simp only [] at h
              have h_adv := advance_preserves_directivesPresent s
              rw [ih s.advance _ "" h, h_adv]

lemma collectDoubleQuotedLoop_preserves_directivesPresent (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.directivesPresent = s.directivesPresent := by
  -- protectedLen (default 0) is generalised so the IH covers the fold
  -- boundary the recursive call shifts (B2).
  suffices H : ∀ (p : Nat) (s : ScannerState) (content : String) (result : String × ScannerState),
      collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd p = .ok result →
      result.snd.directivesPresent = s.directivesPresent by
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
      exact advance_preserves_directivesPresent s
    · -- some '\\' case (escape sequence)
      simp only [] at h
      split at h <;> try contradiction
      -- some c after backslash
      split at h
      · -- isLineBreak c (escaped line break — the landing is a fold, item 87)
        have h_adv := advance_preserves_directivesPresent s
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_directivesPresent s.advance s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold, h_adv])
      · -- regular escape sequence
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_directivesPresent s.advance ch s_after_escape heq
          have h_adv := advance_preserves_directivesPresent s
          rw [ih _ _ _ h, h_proc, h_adv]
    · -- some c case (regular character)
      split at h
      · -- isLineBreak c
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_directivesPresent s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih _ _ _ h, h_fold])
      · -- regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_directivesPresent s
        rw [ih _ _ _ h, h_adv]

lemma collectSingleQuotedLoop_preserves_directivesPresent (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.directivesPresent = s.directivesPresent := by
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
        have h_adv1 := advance_preserves_directivesPresent s
        have h_adv2 := advance_preserves_directivesPresent s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · -- closing quote
        injection h with h_eq; cases h_eq
        exact advance_preserves_directivesPresent s
    · -- some c case (not quote)
      split at h
      · -- isLineBreak c = true
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_directivesPresent s s_fold folded heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih s_fold _ h, h_fold])
      · -- isLineBreak c = false, regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_directivesPresent s
        rw [ih s.advance _ h, h_adv]

lemma consumeExactSpaces_preserves_directivesPresent (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.directivesPresent = s.directivesPresent := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_directivesPresent s
    · rfl

lemma parseBlockHeaderLoop_preserves_directivesPresent (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_directivesPresent s
    · rw [ih]; exact advance_preserves_directivesPresent s
    · split
      · rw [ih]; exact advance_preserves_directivesPresent s
      · rfl
    · rfl

lemma collectLineContentLoop_preserves_directivesPresent (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_directivesPresent s
    · rfl

lemma collectBlockScalarLoop_preserves_directivesPresent (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_directivesPresent s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_directivesPresent, consumeExactSpaces_preserves_directivesPresent]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_directivesPresent,
                    collectLineContentLoop_preserves_directivesPresent, consumeExactSpaces_preserves_directivesPresent]
              · split
                · rfl
                · rw [collectLineContentLoop_preserves_directivesPresent, consumeExactSpaces_preserves_directivesPresent]
            · rw [collectLineContentLoop_preserves_directivesPresent, consumeExactSpaces_preserves_directivesPresent]

lemma scanBlockScalarSkipComment_preserves_directivesPresent (s : ScannerState) :
    (scanBlockScalarSkipComment s).directivesPresent = s.directivesPresent := by
  unfold scanBlockScalarSkipComment
  split
  · -- some '#'
    split
    · -- peekBack? = some c
      dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_directivesPresent, advance_preserves_directivesPresent]
      · rfl
    · -- peekBack? = none
      rfl
  · rfl

lemma scanBlockScalarConsumeNewline_preserves_directivesPresent (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_directivesPresent s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

lemma scanBlockScalarBody_preserves_directivesPresent (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos) (s' : ScannerState)
    (h_fl : s_nl.directivesPresent = s_orig.directivesPresent)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.directivesPresent = s_orig.directivesPresent := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_preserves_directivesPresent, collectBlockScalarLoop_preserves_directivesPresent, h_fl]

lemma scanPlainScalar_preserves_directivesPresent (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h; subst h
  simp [emitAt_preserves_directivesPresent]
  exact collectPlainScalarLoop_preserves_directivesPresent s "" "" _ _ _ _ result heq

lemma scanDoubleQuoted_preserves_directivesPresent (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_directivesPresent]
    have := collectDoubleQuotedLoop_preserves_directivesPresent s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_directivesPresent]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_directivesPresent]
    have := collectDoubleQuotedLoop_preserves_directivesPresent s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_directivesPresent]

lemma scanSingleQuoted_preserves_directivesPresent (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_directivesPresent]
    have := collectSingleQuotedLoop_preserves_directivesPresent s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_directivesPresent]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_directivesPresent]
    have := collectSingleQuotedLoop_preserves_directivesPresent s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_directivesPresent]

lemma scanBlockScalar_preserves_directivesPresent (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') : s'.directivesPresent = s.directivesPresent := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_directivesPresent s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_directivesPresent _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_directivesPresent,
              skipWhitespace_preserves_directivesPresent,
              parseBlockHeaderLoop_preserves_directivesPresent,
              advance_preserves_directivesPresent]) h

lemma dispatchContent_preserves_directivesPresent (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
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
      exact scanAnchorOrAlias_preserves_directivesPresent s true s_a h_fn
  · split at h
    · -- '*': alias
      split at h   -- item 9e: the property-run guard
      · simp at h
      split at h
      · simp at h
      · -- item 9h: peel `validateAliasClose`; the alias facts are unchanged.
        exact scanAnchorOrAlias_preserves_directivesPresent s false _ (aliasArm_scan_ok h)
    · split at h
      · -- '!': tag
        split at h   -- item 9e: the property-run guard
        · simp at h
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanTag_preserves_directivesPresent s s_t h_fn
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_directivesPresent _ _ (by assumption)
          | exact scanDoubleQuoted_preserves_directivesPresent _ _ (by assumption)
          | exact scanSingleQuoted_preserves_directivesPresent _ _ (by assumption)
          | exact scanPlainScalar_preserves_directivesPresent _ _ (by assumption)
          | (simp_all; done)


end L4YAML.Proofs.ScannerDirectivesPresent

end Blanket
