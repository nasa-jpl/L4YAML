/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.DirectiveRuns
public import L4YAML.Proofs.Scanner.FlowIndentStable
public import L4YAML.Proofs.Scanner.ScannerFlowStackPreservation
public import L4YAML.Proofs.Scanner.ScannerFlowCollection
public import L4YAML.Proofs.Scanner.ScannerContracts
public import L4YAML.Proofs.Scanner.EntryBoundaryLayout
public import L4YAML.Proofs.Scanner.FlowAdjacency

@[expose] public section Blanket

/-! # Flow-stack synchrony over the scanner loop (capstone 7.7, stream S3, obligation β2a)

The three scanner facts the `Shape` loop invariant of `DocStartLive` needs and
that the tree had only at the primitive level:

* `FlowSync s := s.flowLevel = s.flowStack.size ∧ s.simpleKeyStack.size = s.flowStack.size`
  — the two synchrony clauses of `ScannerState.WellFormed` — holds at `mk'` and
  is preserved by every `scanNextToken` step (`FlowSync_scanNextToken`) and so
  by `scanLoopFull` (`FlowSync_scanLoopFull`);
* a step taken in flow context leaves `indents` unchanged
  (`scanNextToken_indents_of_inFlow`);
* `skipToContent` never clears `simpleKeyAllowed` (`skipToContent_simpleKeyAllowed_mono`):
  its only write is `:= true` at a line break in block context.

Adversarial grid: Priority 93. -/

namespace L4YAML.Proofs.FlowSync

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.DirectiveRuns
open L4YAML.Proofs.CloseStaleExplicitKey L4YAML.Proofs.EntryBoundaryLayout
  L4YAML.Proofs.FlowAdjacency L4YAML.Proofs.FlowIndentStable L4YAML.Proofs.IndentStackBase
  L4YAML.Proofs.ScannerAllowDirectives L4YAML.Proofs.ScannerContracts
  L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.ScannerFlowCollection
  L4YAML.Proofs.ScannerFlowStack

/-- The two stack-synchrony clauses of `ScannerState.WellFormed`. -/
def FlowSync (s : ScannerState) : Prop :=
  s.flowLevel = s.flowStack.size ∧ s.simpleKeyStack.size = s.flowStack.size

lemma FlowSync_mk' (input : String) : FlowSync (ScannerState.mk' input) := ⟨rfl, rfl⟩

lemma FlowSync.emit (s : ScannerState) (t : YamlToken) (h : FlowSync s) : FlowSync (s.emit t) := by
  unfold FlowSync at *
  rw [ScannerCorrectness.emit_preserves_flowLevel, ScannerCorrectness.emit_preserves_flowStack,
    ScannerCorrectness.emit_preserves_simpleKeyStack]; exact h

lemma FlowSync.consumeBOM (s : ScannerState) (h : FlowSync s) : FlowSync s.consumeBOM := by
  unfold FlowSync at *
  rw [consumeBOM_preserves_flowLevel, consumeBOM_preserves_flowStack,
    consumeBOM_preserves_simpleKeyStack]; exact h

lemma FlowSync.unwindIndents (s : ScannerState) (col : Int) (h : FlowSync s) :
    FlowSync (unwindIndents s col) := by
  unfold FlowSync at *
  rw [unwindIndents_preserves_flowLevel, unwindIndents_preserves_flowStack,
    unwindIndents_preserves_simpleKeyStack]; exact h

/-- Twin of `preprocess_preserves_flowStack`. -/
lemma preprocess_preserves_flowLevel (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) : s1.flowLevel = s.flowLevel := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have hk := skipToContent_preserves_flowLevel s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [closeStaleExplicitKey_flowLevel, saveSimpleKey_preserves_flowLevel]
            show (unwindIndents s_skip s_skip.col).flowLevel = s.flowLevel
            rw [unwindIndents_preserves_flowLevel]; exact hk
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [closeStaleExplicitKey_flowLevel, saveSimpleKey_preserves_flowLevel]; exact hk

lemma FlowSync_preprocess (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) (hF : FlowSync s) : FlowSync s1 := by
  unfold FlowSync at *
  rw [preprocess_preserves_flowLevel s s1 c h, preprocess_preserves_flowStack s s1 c h,
    preprocess_preserves_simpleKeyStack s s1 c h]; exact hF

lemma FlowSync_dispatchStructural (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) (hF : FlowSync s) : FlowSync s' := by
  unfold FlowSync at *
  rw [dispatchStructural_preserves_flowLevel s c s' h, dispatchStructural_preserves_flowStack s c s' h,
    dispatchStructural_preserves_simpleKeyStack s c s' h]; exact hF

lemma FlowSync_dispatchBlock (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) (hF : FlowSync s) :
    FlowSync s' := by
  unfold FlowSync at *
  rw [dispatchBlockIndicators_preserves_flowLevel s c s' h,
    dispatchBlockIndicators_preserves_flowStack s c s' h,
    dispatchBlockIndicators_preserves_simpleKeyStack s c s' h]; exact hF

lemma FlowSync_dispatchContent (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') (hF : FlowSync s) : FlowSync s' := by
  unfold FlowSync at *
  rw [dispatchContent_preserves_flowLevel s c s' h, dispatchContent_preserves_flowStack s c s' h,
    dispatchContent_preserves_simpleKeyStack s c s' h]; exact hF

lemma FlowSync_flowSequenceStart (s : ScannerState) (hF : FlowSync s) :
    FlowSync (scanFlowSequenceStart s) :=
  ⟨scanFlowSequenceStart_flow_sync s hF.1, scanFlowSequenceStart_simpleKeyStack_sync s hF.2⟩

lemma FlowSync_flowMappingStart (s : ScannerState) (hF : FlowSync s) :
    FlowSync (scanFlowMappingStart s) :=
  ⟨scanFlowMappingStart_flow_sync s hF.1, scanFlowMappingStart_simpleKeyStack_sync s hF.2⟩

lemma FlowSync_flowSequenceEnd (s : ScannerState) (hF : FlowSync s) (hpos : 0 < s.flowLevel) :
    FlowSync (scanFlowSequenceEnd s) := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨scanFlowSequenceEnd_flow_sync s h1 hpos, ?_⟩
  have h3 := scanFlowSequenceEnd_flow_sync s h1 hpos
  rw [scanFlowSequenceEnd_flowLevel_pos s hpos] at h3
  rw [scanFlowSequenceEnd_stack_popped, Array.size_pop]
  omega

lemma FlowSync_flowMappingEnd (s : ScannerState) (hF : FlowSync s) (hpos : 0 < s.flowLevel) :
    FlowSync (scanFlowMappingEnd s) := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨scanFlowMappingEnd_flow_sync s h1 hpos, ?_⟩
  have h3 := scanFlowMappingEnd_flow_sync s h1 hpos
  rw [scanFlowMappingEnd_flowLevel_pos s hpos] at h3
  rw [scanFlowMappingEnd_stack_popped, Array.size_pop]
  omega

lemma FlowSync_dispatchFlow (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) (hF : FlowSync s) :
    FlowSync s' := by
  unfold scanNextToken_dispatchFlowIndicators at h
  replace h := peel_flowAdj h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact FlowSync_flowSequenceStart s hF
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · have hpos : 0 < s.flowLevel := Nat.pos_of_ne_zero (by simp_all)
            simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
            exact FlowSync_flowSequenceEnd s hF hpos
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact FlowSync_flowMappingStart s hF
      · split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · have hpos : 0 < s.flowLevel := Nat.pos_of_ne_zero (by simp_all)
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                exact FlowSync_flowMappingEnd s hF hpos
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i _ _ _ h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                unfold FlowSync at *
                rw [L4YAML.Proofs.ScannerFlowCollection.scanFlowEntry_preserves_flowLevel s _ h_entry,
                  L4YAML.Proofs.ScannerFlowCollection.scanFlowEntry_preserves_flowStack s _ h_entry,
                  scanFlowEntry_preserves_simpleKeyStack s _ h_entry]; exact hF
          · simp at h

/-- One scanner step keeps the flow stacks in sync. -/
lemma FlowSync_scanNextToken (s s' : ScannerState) (hF : FlowSync s)
    (h : scanNextToken s = .ok (some s')) : FlowSync s' := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  rename_i s2 c h_pre
  have hF2 := FlowSync_preprocess s s2 c h_pre hF
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact FlowSync_dispatchStructural s2 c _ (by assumption) hF2
  · split at h <;> (try (simp at h; done))
    split at h <;> (try (simp at h; done))
    have hF3 : FlowSync (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2) := by
      split <;> exact hF2
    split at h <;> (try (simp at h; done))
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      exact FlowSync_dispatchFlow _ c _ (by assumption) hF3
    · split at h <;> (try (simp at h; done))
      split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact FlowSync_dispatchBlock _ c _ (by assumption) hF3
      · split at h <;> (try (simp at h; done))
        split at h <;> (try (simp at h; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact FlowSync_dispatchContent _ c _ (by assumption) hF3

/-- The loop keeps it, through the terminal `skipToContent` / `unwindIndents` / `.streamEnd`. -/
lemma FlowSync_scanLoopFull (fuel : Nat) : ∀ (s s' : ScannerState), FlowSync s →
    scanLoopFull s fuel = .ok s' → FlowSync s' := by
  induction fuel with
  | zero => intro s s' _ h; unfold scanLoopFull at h; simp at h
  | succ n ih =>
    intro s s' hF h
    unfold scanLoopFull at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Except.ok.injEq] at h; subst h
              refine FlowSync.emit _ _ (FlowSync.unwindIndents _ _ ?_)
              split
              · rename_i sk hsk
                unfold FlowSync at *
                rw [skipToContent_preserves_flowLevel s sk hsk,
                  skipToContent_preserves_flowStack s sk hsk,
                  skipToContent_preserves_simpleKeyStack s sk hsk]; exact hF
              · exact hF
    · exact ih _ _ (FlowSync_scanNextToken s _ hF (by assumption)) h

/-! ## Indents are frozen in flow context -/

lemma dispatchStructural_indents_of_inFlow (s : ScannerState) (c : Char) (s' : ScannerState)
    (hin : s.inFlow = true) (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    s'.indents = s.indents := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, Except.bind, pure, Except.pure, hin, Bool.and_true, Bool.true_and] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h_no_marker
      split at h
      · rename_i h_ds; simp_all
      · split at h
        · rename_i h_de; simp_all
        · split at h
          · cases hd : scanDirective s with
            | ok sd =>
              rw [hd] at h
              simp only [Except.ok.injEq, Option.some.injEq] at h
              subst h
              exact scanDirective_preserves_indents hd
            | error e => rw [hd] at h; simp at h
          · simp at h

/-- A step taken in flow context does not touch the indent stack. -/
lemma scanNextToken_indents_of_inFlow (s s' : ScannerState) (hin : s.inFlow = true)
    (h : scanNextToken s = .ok (some s')) : s'.indents = s.indents := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  rename_i s2 c h_pre
  have hi2 : s2.indents = s.indents := preprocess_indents_of_inFlow hin h_pre
  have hin2 : s2.inFlow = true := by
    unfold ScannerState.inFlow at *
    rw [preprocess_preserves_flowLevel s s2 c h_pre]; exact hin
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    rw [dispatchStructural_indents_of_inFlow s2 c _ hin2 (by assumption)]; exact hi2
  · split at h <;> (try (simp at h; done))
    split at h <;> (try (simp at h; done))
    have hin3 : (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2).inFlow = true := by
      split <;> exact hin2
    have hi3 : (if s2.allowDirectives = true then
        { s2 with allowDirectives := false, documentEverStarted := true } else s2).indents
          = s.indents := by
      split <;> exact hi2
    split at h <;> (try (simp at h; done))
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      rw [dispatchFlowIndicators_preserves_indents (by assumption)]; exact hi3
    · split at h <;> (try (simp at h; done))
      split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        rw [dispatchBlockIndicators_preserves_indents hin3 (by assumption)]; exact hi3
      · split at h <;> (try (simp at h; done))
        split at h <;> (try (simp at h; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        rw [dispatchContent_preserves_indents hin3 (by assumption)]; exact hi3

/-! ## `skipToContent` never clears `simpleKeyAllowed` -/

lemma skipToContentLoop_simpleKeyAllowed_mono (s s' : ScannerState) (fuel : Nat)
    (ha : s.simpleKeyAllowed = true) (h : skipToContentLoop s fuel = .ok s') :
    s'.simpleKeyAllowed = true := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]; exact ha
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · split at h
          · exact ih _ rfl h
          · refine ih _ ?_ h
            rw [consumeNewline_preserves_simpleKeyAllowed,
              skipToContentComment_preserves_simpleKeyAllowed,
              skipToContentWs_preserves_simpleKeyAllowed s s1 hws]; exact ha
        · simp at h; rw [← h, skipToContentComment_preserves_simpleKeyAllowed,
            skipToContentWs_preserves_simpleKeyAllowed s s1 hws]; exact ha
      · simp at h; rw [← h, skipToContentComment_preserves_simpleKeyAllowed,
          skipToContentWs_preserves_simpleKeyAllowed s s1 hws]; exact ha

lemma skipToContent_simpleKeyAllowed_mono (s s' : ScannerState) (ha : s.simpleKeyAllowed = true)
    (h : skipToContent s = .ok s') : s'.simpleKeyAllowed = true := by
  unfold skipToContent at h
  exact skipToContentLoop_simpleKeyAllowed_mono s s' _ ha h

end L4YAML.Proofs.FlowSync
