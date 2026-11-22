/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-! # `allowDirectives` across preprocessing (β.3)

    `scanNextToken_preprocess` runs `skipToContent`, `unwindIndents` and
    `saveSimpleKey`, none of which touches `allowDirectives`.  This file walks
    that chain so `preprocess_preserves_allowDirectives` is available to the
    accumulation.

    **Why it is needed.**  `scanNextToken` clears `allowDirectives` on the first
    non-structural token, and every flow indicator is dispatched *after* that
    clear — so an open flow collection implies the flag is already false.  The
    accumulation carries that as part of its flow-interior invariant, and
    `accum_step_structural` consumes it: `scanNextToken_dispatchStructural`'s
    only success arm inside a flow is the `%` directive, and `scanDirective`
    rejects outright when `allowDirectives` is false.  Without this transport the
    invariant would be stated on `sc` and needed on `s_prep`.

    Structurally these are the `_preserves_flowStack` walks of
    `Proofs/Scanner/ScannerFlowStackPreservation.lean` with the field renamed:
    the proofs are field-agnostic (unfold + split + fuel induction bottoming out
    in `emit`/`advance`), so they transfer verbatim.  Only the preprocessing
    prefix is cloned — the scan-body collectors are not on this path. -/

namespace L4YAML.Proofs.ScannerAllowDirectives

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML.Scanner

lemma advance_preserves_allowDirectives (s : ScannerState) :
    s.advance.allowDirectives = s.allowDirectives := by
  unfold ScannerState.advance; dsimp only []; split <;> (try split) <;> (try split) <;> rfl

lemma emit_preserves_allowDirectives (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).allowDirectives = s.allowDirectives := by
  unfold ScannerState.emit; rfl

lemma skipSpacesLoop_preserves_allowDirectives (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).allowDirectives = s.allowDirectives := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · exact (ih _).trans (advance_preserves_allowDirectives _)
    · rfl

lemma skipWhitespaceLoop_preserves_allowDirectives (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).allowDirectives = s.allowDirectives := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact (ih _).trans (advance_preserves_allowDirectives _)
      · rfl
    · rfl

lemma skipToEndOfLineLoop_preserves_allowDirectives (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).allowDirectives = s.allowDirectives := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · exact (ih _).trans (advance_preserves_allowDirectives _)
    · rfl

lemma skipSpaces_preserves_allowDirectives (s : ScannerState) :
    (skipSpaces s).allowDirectives = s.allowDirectives := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_allowDirectives s _

lemma skipWhitespace_preserves_allowDirectives (s : ScannerState) :
    (skipWhitespace s).allowDirectives = s.allowDirectives := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_allowDirectives s _

lemma skipToEndOfLine_preserves_allowDirectives (s : ScannerState) :
    (skipToEndOfLine s).allowDirectives = s.allowDirectives := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_allowDirectives s _

lemma collectCommentTextLoop_preserves_allowDirectives (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.allowDirectives = s.allowDirectives := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_allowDirectives]
    · rfl

lemma skipToContentWs_preserves_allowDirectives (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_preserves_allowDirectives, skipSpaces_preserves_allowDirectives]
        · split at h
          · simp at h; rw [← h, skipWhitespace_preserves_allowDirectives, skipSpaces_preserves_allowDirectives]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_allowDirectives, skipSpaces_preserves_allowDirectives]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_preserves_allowDirectives, skipSpaces_preserves_allowDirectives]
      · simp at h; rw [← h, skipSpaces_preserves_allowDirectives]
    · simp at h; rw [← h, skipWhitespace_preserves_allowDirectives, skipSpaces_preserves_allowDirectives]
  · simp at h; rw [← h, skipWhitespace_preserves_allowDirectives]

lemma skipToContentComment_preserves_allowDirectives (s : ScannerState) :
    (skipToContentComment s).allowDirectives = s.allowDirectives := by
  unfold skipToContentComment
  split
  · -- peek? = some '#'
    simp only []
    split  -- peekBack?
    · -- peekBack? = some c
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_allowDirectives, advance_preserves_allowDirectives]
      · rfl
    · -- peekBack? = none
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_allowDirectives, advance_preserves_allowDirectives]
      · rfl
  · rfl

lemma consumeNewline_preserves_allowDirectives (s : ScannerState) :
    (consumeNewline s).allowDirectives = s.allowDirectives := by
  unfold consumeNewline
  split
  · exact advance_preserves_allowDirectives s
  · simp only []; split
    · exact advance_preserves_allowDirectives _
    · exact advance_preserves_allowDirectives _
  · rfl

lemma skipToContentLoop_preserves_allowDirectives (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') : s'.allowDirectives = s.allowDirectives := by
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
          · have := ih _ h; rw [this, consumeNewline_preserves_allowDirectives,
              skipToContentComment_preserves_allowDirectives]; exact skipToContentWs_preserves_allowDirectives s s1 hws
          · have := ih _ h; rw [this, consumeNewline_preserves_allowDirectives,
              skipToContentComment_preserves_allowDirectives]; exact skipToContentWs_preserves_allowDirectives s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_allowDirectives]
          exact skipToContentWs_preserves_allowDirectives s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_allowDirectives]
        exact skipToContentWs_preserves_allowDirectives s s1 hws

lemma skipToContent_preserves_allowDirectives (s s' : ScannerState)
    (h : skipToContent s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold skipToContent at h; exact skipToContentLoop_preserves_allowDirectives s s' _ h

lemma unwindIndentsLoop_preserves_allowDirectives (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).allowDirectives = s.allowDirectives := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ _ ih =>
    unfold unwindIndentsLoop; split
    · have := ih { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop, pendingKeys := (s.emit .blockEnd).pendingKeys.pop }
      simp [emit_preserves_allowDirectives] at this; exact this
    · rfl

lemma unwindIndents_preserves_allowDirectives (s : ScannerState) (col : Int) :
    (unwindIndents s col).allowDirectives = s.allowDirectives := by
  unfold unwindIndents; exact unwindIndentsLoop_preserves_allowDirectives s col _

lemma saveSimpleKey_preserves_allowDirectives (st : ScannerState) :
    (saveSimpleKey st).allowDirectives = st.allowDirectives := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl

/-- `scanNextToken_preprocess` preserves `allowDirectives`: it is
    `skipToContent` → optional `unwindIndents` → `saveSimpleKey`, and none of
    the three touches the flag. -/
lemma preprocess_preserves_allowDirectives (s : ScannerState) (s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    s1.allowDirectives = s.allowDirectives := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_ad_skip := skipToContent_preserves_allowDirectives s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [closeStaleExplicitKey_allowDirectives, saveSimpleKey_preserves_allowDirectives]
            show (unwindIndents s_skip s_skip.col).allowDirectives = s.allowDirectives
            rw [unwindIndents_preserves_allowDirectives]; exact h_ad_skip
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [closeStaleExplicitKey_allowDirectives, saveSimpleKey_preserves_allowDirectives]; exact h_ad_skip

/-! ## No structural token succeeds inside an open flow (β.3)

    `scanNextToken_dispatchStructural` returns `.ok (some _)` from exactly three
    arms, and inside a flow collection all three are dead:

    * the `---` and `...` accept arms sit BELOW the §5.4 `documentMarkerInFlow`
      guard, which fires on precisely their trigger once `inFlow` holds;
    * the `%` arm reaches `scanDirective`, which rejects on `!allowDirectives`.

    The flag is false inside a flow because `scanNextToken` clears it before any
    flow indicator is dispatched, so the `[`/`{` that opened the collection
    cleared it. The accumulation carries that fact; this lemma consumes it. -/

lemma dispatchStructural_inFlow_no_success (s s' : ScannerState) (c : Char)
    (h_inflow : s.inFlow = true) (h_ad : s.allowDirectives = false) :
    scanNextToken_dispatchStructural s c ≠ .ok (some s') := by
  intro h
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, Except.bind, pure, Except.pure, h_inflow, Bool.and_true, Bool.true_and] at h
  -- The under-indent guard either errors (non-bracket `c`) or falls through;
  -- both continuations are the same document-marker/directive chain.
  have chain : ∀ r : Except ScanError (Option ScannerState),
      r = (if (s.col == 0 && (atDocumentStart s || atDocumentEnd s)) = true then
              Except.error (ScanError.documentMarkerInFlow s.line)
            else if (s.col == 0 && atDocumentStart s) = true then
              Except.ok (some (scanDocumentStart s))
            else if (s.col == 0 && atDocumentEnd s) = true then
              (scanDocumentEnd s).map some
            else if (c == '%' && s.col == 0) = true then
              (scanDirective s).map some
            else Except.ok none) →
      r ≠ .ok (some s') := by
    intro r hr hok
    subst hr
    split at hok
    · simp at hok
    · rename_i h_no_marker
      split at hok
      · rename_i h_ds; simp_all
      · split at hok
        · rename_i h_de; simp_all
        · split at hok
          · -- `%` at col 0 → `scanDirective`, which needs `allowDirectives`.
            unfold scanDirective at hok
            rw [ite_eq_left (by simp [h_ad])] at hok
            simp [Except.map] at hok
          · simp at hok
  split at h
  · -- item 50: the floor refuses outright (the `]`/`}` exemption is gone)
    simp at h
  · exact chain _ rfl h

/-! ## The two indicator dispatchers (item 138)

    `scanNextToken` clears `allowDirectives` before either indicator dispatcher
    runs, and neither dispatcher's scans touch the flag again.  Walking them is
    what turns that clear into a park FIELD: every `PendingNode` produced past
    the structural dispatch carries `sc.allowDirectives = false`, which is how a
    later `%` — the one arm `scanDirective` admits — knows the park it closed
    was the stream's own seed or a `...`.

    The proofs are the file's own shape: unfold, split on the guards, and bottom
    out in `emit`/`advance`, neither of which writes the field. -/

lemma pushSequenceIndent_preserves_allowDirectives (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).allowDirectives = s.allowDirectives := by
  unfold pushSequenceIndent; split <;> rfl

lemma pushMappingIndent_preserves_allowDirectives (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).allowDirectives = s.allowDirectives := by
  unfold pushMappingIndent; split <;> rfl

/-- The `-` indicator's conditional push, at the shape the unfolded
    `scanBlockEntry` presents it in. -/
lemma ite_pushSequenceIndent_allowDirectives (s : ScannerState) :
    (if !s.inFlow then pushSequenceIndent s (s.col : Int) else s).allowDirectives
      = s.allowDirectives := by
  split
  · exact pushSequenceIndent_preserves_allowDirectives _ _
  · rfl

/-- The `?` indicator's conditional push, likewise. -/
lemma ite_pushMappingIndent_allowDirectives (s : ScannerState) :
    (if !s.inFlow then pushMappingIndent s (s.col : Int) else s).allowDirectives
      = s.allowDirectives := by
  split
  · exact pushMappingIndent_preserves_allowDirectives _ _
  · rfl

lemma scanBlockEntry_preserves_allowDirectives {s s' : ScannerState}
    (h : scanBlockEntry s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    first
      | (subst h
         simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives,
           ite_pushSequenceIndent_allowDirectives,
           pushSequenceIndent_preserves_allowDirectives])
      | (injection h with h
         subst h
         simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives,
           pushSequenceIndent_preserves_allowDirectives])
      | (exfalso; simp_all; done)

lemma scanKey_preserves_allowDirectives {s s' : ScannerState}
    (h : scanKey s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold scanKey at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    first
      | (subst h
         simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives,
           ite_pushMappingIndent_allowDirectives,
           pushMappingIndent_preserves_allowDirectives])
      | (injection h with h
         subst h
         simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives,
           pushMappingIndent_preserves_allowDirectives])
      | (exfalso; simp_all; done)

lemma scanValueClearKey_preserves_allowDirectives (s : ScannerState) :
    (scanValueClearKey s).allowDirectives = s.allowDirectives := by
  unfold scanValueClearKey
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

lemma scanValuePrepare_preserves_allowDirectives (s : ScannerState) :
    (scanValuePrepare s).allowDirectives = s.allowDirectives := by
  unfold scanValuePrepare
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · exact pushMappingIndent_preserves_allowDirectives _ _
      · rfl

lemma scanValue_preserves_allowDirectives {s s' : ScannerState}
    (h : scanValue s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    first
      | (subst h
         simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives,
           scanValuePrepare_preserves_allowDirectives,
           scanValueClearKey_preserves_allowDirectives])
      | (injection h with h
         subst h
         simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives,
           scanValuePrepare_preserves_allowDirectives,
           scanValueClearKey_preserves_allowDirectives])
      | (exfalso; simp_all; done)

/-- The block-indicator dispatcher never writes `allowDirectives`. -/
lemma dispatchBlockIndicators_preserves_allowDirectives {s s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    s'.allowDirectives = s.allowDirectives := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · simp at h
    · rename_i s_be h_be
      injection Except.ok.inj h with h
      subst h
      exact scanBlockEntry_preserves_allowDirectives h_be
  · split at h
    · split at h
      · simp at h
      · rename_i s_k h_k
        injection Except.ok.inj h with h
        subst h
        exact scanKey_preserves_allowDirectives h_k
    · split at h
      · split at h
        · simp at h
        · rename_i s_v h_v
          injection Except.ok.inj h with h
          subst h
          exact scanValue_preserves_allowDirectives h_v
      · exact absurd (Except.ok.inj h) nofun

lemma scanFlowSequenceStart_preserves_allowDirectives (s : ScannerState) :
    (scanFlowSequenceStart s).allowDirectives = s.allowDirectives := by
  unfold scanFlowSequenceStart
  simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives]

lemma scanFlowSequenceEnd_preserves_allowDirectives (s : ScannerState) :
    (scanFlowSequenceEnd s).allowDirectives = s.allowDirectives := by
  unfold scanFlowSequenceEnd
  simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives]

lemma scanFlowMappingStart_preserves_allowDirectives (s : ScannerState) :
    (scanFlowMappingStart s).allowDirectives = s.allowDirectives := by
  unfold scanFlowMappingStart
  simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives]

lemma scanFlowMappingEnd_preserves_allowDirectives (s : ScannerState) :
    (scanFlowMappingEnd s).allowDirectives = s.allowDirectives := by
  unfold scanFlowMappingEnd
  simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives]

lemma scanFlowEntry_preserves_allowDirectives {s s' : ScannerState}
    (h : scanFlowEntry s = .ok s') : s'.allowDirectives = s.allowDirectives := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind] at h
  split at h <;> (try split at h) <;>
    first
      | (subst h
         simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives])
      | (injection h with h
         subst h
         simp only [advance_preserves_allowDirectives, emit_preserves_allowDirectives])
      | (exfalso; simp_all; done)

/-- The flow-indicator dispatcher never writes `allowDirectives` either. -/
lemma dispatchFlowIndicators_preserves_allowDirectives {s s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    s'.allowDirectives = s.allowDirectives := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    (try split at h) <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    first
      | (exfalso; simp_all; done)
      | (injection h with h
         injection h with h
         subst h
         simp only [scanFlowSequenceStart_preserves_allowDirectives,
           scanFlowSequenceEnd_preserves_allowDirectives,
           scanFlowMappingStart_preserves_allowDirectives,
           scanFlowMappingEnd_preserves_allowDirectives])
      | (rename_i h_fe
         injection h with h
         injection h with h
         subst h
         exact scanFlowEntry_preserves_allowDirectives h_fe)

/-- **A directive scan says the flag was up** (item 138): `scanDirective`'s
    first test is `!s.allowDirectives`, and it throws there.  This is the
    premise `PendingNode.dirRoute` consumes — it is what narrows the park that
    a `%` closed to the two the accumulation can give an arm to. -/
lemma scanDirective_allowDirectives {s s' : ScannerState}
    (h : scanDirective s = .ok s') : s.allowDirectives = true := by
  cases had : s.allowDirectives with
  | true => rfl
  | false =>
    exfalso
    unfold scanDirective at h
    rw [ite_eq_left (by simp [had])] at h
    simp at h

end L4YAML.Proofs.ScannerAllowDirectives

end Blanket
