/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Production.ScannerPlainScalarValid
public import L4YAML.Proofs.Output.EmitterScannability.ScannerAcceptance
public import L4YAML.Proofs.Scanner.ScannerFlowStackPreservation
public import L4YAML.Proofs.Scanner.ScannerEkStackPreservation

@[expose] public section Blanket

/-! # FlowStackChain — `flowStack` moves in lockstep with `flowLevel`

`ScannerState.flowStack` is written only by the four flow-collection
functions (`scanFlowSequenceStart`/`scanFlowMappingStart` push a kind marker
and increment `flowLevel`; `scanFlowSequenceEnd`/`scanFlowMappingEnd` pop it
and decrement `flowLevel`).  Every other scanner function copies the field
through record updates.  This file makes that lockstep precise across a full
`scanNextToken` step and lifts it to balanced scan chains:

* **§1** — `flowStack` preservation suite for every scanner leaf reached by
  `scanNextToken` outside the four flow open/close functions.  Mechanical
  clones of the `_preserves_simpleKeyStack` suite in
  `Proofs/Scanner/ScannerCorrectness.lean` (lines 3528–5752): the originals
  are field-agnostic structural walks, so the same scripts prove the
  `flowStack` twins verbatim.
* **§2** — flow open/close `flowLevel`/`flowStack` component facts.
* **§3** — `dispatchFlowIndicators_flowStack_step`: the 5-arm fact for the
  flow-indicator dispatcher (preserve / push `true` / push `false` / pop).
* **§4** — `scanNextToken_flowStack_step`: the per-step trichotomy — one
  scanner step either preserves `flowStack` (and `flowLevel`), pushes one
  kind marker (incrementing `flowLevel`), or pops one (decrementing it).
* **§5** — `FlowMonoChain.flowStack_invariant` / `FlowMonoChain.flowStack_eq`:
  a balanced scan chain (`FlowMonoChain`, flow level never below the floor)
  never disturbs the `flowStack` entries below the floor; a chain that starts
  and ends at the floor preserves `flowStack` exactly.
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.FlowAdjacency
open L4YAML.Proofs.ScannerFlowStack

namespace FlowStackChain

/-! ## §1 (moved) — the scanner-leaf `flowStack` preservation suite now lives at
    the scanner-proof layer, in `Proofs/Scanner/ScannerFlowStackPreservation.lean`
    (`L4YAML.Proofs.ScannerFlowStack`), so the production-side accumulation
    invariant can consume it without importing this emitter-side module. It is
    `open`ed at the top of this file, so §2-§5 below still name its lemmas
    unqualified. -/

/-! ## §2  Flow open/close component facts -/

/-- `scanFlowSequenceStart` increments `flowLevel`. -/
lemma scanFlowSequenceStart_flowLevel (s : ScannerState) :
    (scanFlowSequenceStart s).flowLevel = s.flowLevel + 1 := by
  unfold scanFlowSequenceStart
  simp only [ScannerCorrectness.emit_preserves_flowLevel,
             ScannerCorrectness.advance_preserves_flowLevel]

/-- `scanFlowMappingStart` increments `flowLevel`. -/
lemma scanFlowMappingStart_flowLevel (s : ScannerState) :
    (scanFlowMappingStart s).flowLevel = s.flowLevel + 1 := by
  unfold scanFlowMappingStart
  simp only [ScannerCorrectness.emit_preserves_flowLevel,
             ScannerCorrectness.advance_preserves_flowLevel]

/-! ## §3  Flow-indicator dispatcher step fact -/

set_option maxHeartbeats 800000 in
/-- The 5-arm `flowLevel`/`flowStack` fact for the flow-indicator dispatcher:
    `[` pushes `true`, `{` pushes `false`, `]`/`}` pop (with `flowLevel > 0`
    from the level guard), and `,` preserves both fields. -/
lemma dispatchFlowIndicators_flowStack_step (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    (s'.flowLevel = s.flowLevel ∧ s'.flowStack = s.flowStack) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧ s'.flowStack = s.flowStack.push true) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧ s'.flowStack = s.flowStack.push false) ∨
    (s.flowLevel > 0 ∧ s'.flowLevel + 1 = s.flowLevel ∧
      s'.flowStack = s.flowStack.pop) := by
  unfold scanNextToken_dispatchFlowIndicators at h
  replace h := peel_flowAdj h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- c == '['
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact Or.inr (Or.inl ⟨scanFlowSequenceStart_flowLevel s,
      ScannerFlowCollection.scanFlowSequenceStart_pushes_true s⟩)
  -- c == ']'
  · split at h
    · split at h
      · simp at h  -- flowLevel == 0 → error
      · rename_i h_lvl
        split at h
        · simp at h  -- flowStack kind mismatch → error
        · split at h
          · simp at h  -- validateFlowClose error
          · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
            have h_pos : s.flowLevel > 0 := by
              simp only [beq_iff_eq] at h_lvl; omega
            refine Or.inr (Or.inr (Or.inr
              ⟨h_pos, ?_, ScannerFlowCollection.scanFlowSequenceEnd_pops s⟩))
            rw [ScannerFlowCollection.scanFlowSequenceEnd_flowLevel_pos s h_pos]
            omega
    -- c == '{'
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact Or.inr (Or.inr (Or.inl ⟨scanFlowMappingStart_flowLevel s,
          ScannerFlowCollection.scanFlowMappingStart_pushes_false s⟩))
      -- c == '}'
      · split at h
        · split at h
          · simp at h  -- flowLevel == 0 → error
          · rename_i h_lvl
            split at h
            · simp at h  -- flowStack kind mismatch → error
            · split at h
              · simp at h  -- validateFlowClose error
              · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                have h_pos : s.flowLevel > 0 := by
                  simp only [beq_iff_eq] at h_lvl; omega
                refine Or.inr (Or.inr (Or.inr
                  ⟨h_pos, ?_, ScannerFlowCollection.scanFlowMappingEnd_pops s⟩))
                rw [ScannerFlowCollection.scanFlowMappingEnd_flowLevel_pos s h_pos]
                omega
        -- c == ','
        · split at h
          · split at h
            · simp at h  -- flowLevel == 0 → error
            · split at h
              · simp at h  -- scanFlowEntry error
              · rename_i h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                exact Or.inl
                  ⟨ScannerCorrectness.scanFlowEntry_preserves_flowLevel _ _ h_entry,
                   scanFlowEntry_preserves_flowStack _ _ h_entry⟩
          -- fallthrough: not a flow indicator
          · simp at h

end FlowStackChain

/-! ## §4  Per-step trichotomy -/

set_option maxHeartbeats 1600000 in
/-- One `scanNextToken` step moves `flowStack` in lockstep with `flowLevel`:
    it either preserves both, pushes one kind marker (`true` for `[`,
    `false` for `{`) while incrementing `flowLevel`, or pops one while
    decrementing `flowLevel` (which was positive). -/
lemma scanNextToken_flowStack_step {s s' : ScannerState}
    (h : scanNextToken s = .ok (some s')) :
    (s'.flowLevel = s.flowLevel ∧ s'.flowStack = s.flowStack) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧ s'.flowStack = s.flowStack.push true) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧ s'.flowStack = s.flowStack.push false) ∨
    (s.flowLevel > 0 ∧ s'.flowLevel + 1 = s.flowLevel ∧
      s'.flowStack = s.flowStack.pop) := by
  unfold scanNextToken at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h <;> (try (simp at h; done))  -- preprocess Except
  split at h <;> (try (simp at h; done))  -- preprocess Option
  rename_i s1 c1 h_pre
  have h_pre_st := ScannerFlowStack.preprocess_preserves_flowStack s _ _ h_pre
  have h_pre_fl := preprocess_preserves_flowLevel s _ _ h_pre
  -- §9.2 dangling-node check (item 133)
  split at h <;> (try (simp at h; done))
  -- §8.1 flow-value floor (item 172)
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))  -- structural Except
  split at h
  · -- structural some
    simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    refine Or.inl ⟨?_, ?_⟩
    · rw [ScannerCorrectness.dispatchStructural_preserves_flowLevel s1 c1 _
        (by assumption), h_pre_fl]
    · rw [ScannerFlowStack.dispatchStructural_preserves_flowStack s1 c1 _
        (by assumption), h_pre_st]
  · -- structural none → directives check → allowDirectives ite → flow/block/content
    have h_allow_st : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).flowStack = st.flowStack := by intro st; split <;> rfl
    have h_allow_fl : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).flowLevel = st.flowLevel := by intro st; split <;> rfl
    split at h <;> (try (simp at h; done))  -- checkNoPendingDirectives
    split at h <;> (try (simp at h; done))  -- checkBareDocument (item 132)
    split at h <;> (try (simp at h; done))  -- flow Except
    split at h
    · -- flow some
      simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      have h_step := FlowStackChain.dispatchFlowIndicators_flowStack_step _ _ c1
        (by assumption)
      rcases h_step with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h0, h1, h2⟩
      · rw [h_allow_fl, h_pre_fl] at h1; rw [h_allow_st, h_pre_st] at h2
        exact Or.inl ⟨h1, h2⟩
      · rw [h_allow_fl, h_pre_fl] at h1; rw [h_allow_st, h_pre_st] at h2
        exact Or.inr (Or.inl ⟨h1, h2⟩)
      · rw [h_allow_fl, h_pre_fl] at h1; rw [h_allow_st, h_pre_st] at h2
        exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
      · rw [h_allow_fl, h_pre_fl] at h0 h1; rw [h_allow_st, h_pre_st] at h2
        exact Or.inr (Or.inr (Or.inr ⟨h0, h1, h2⟩))
    · -- flow none → block
      split at h <;> (try (simp at h; done))  -- block Except
      split at h
      · -- block some
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        refine Or.inl ⟨?_, ?_⟩
        · rw [ScannerCorrectness.dispatchBlockIndicators_preserves_flowLevel _ c1 _
            (by assumption), h_allow_fl, h_pre_fl]
        · rw [ScannerFlowStack.dispatchBlockIndicators_preserves_flowStack _ c1 _
            (by assumption), h_allow_st, h_pre_st]
      · -- block none → content
        split at h <;> (try (simp at h; done))  -- adjacent-value check (item 47)
        split at h <;> (try (simp at h; done))  -- content Except
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        refine Or.inl ⟨?_, ?_⟩
        · rw [ScannerCorrectness.dispatchContent_preserves_flowLevel _ c1 _
            (by assumption), h_allow_fl, h_pre_fl]
        · rw [ScannerFlowStack.dispatchContent_preserves_flowStack _ c1 _
            (by assumption), h_allow_st, h_pre_st]

/-! ## §5  Chain theorems over `FlowMonoChain` -/

/-- Through a `FlowMonoChain` with floor `fl₀`, the `flowStack` entries below
    the floor are never disturbed: if the start state's stack splits as
    `base ++ extra` with `extra` tracking the excess flow depth
    (`extra.size = flowLevel - fl₀`), the end state's stack is `base ++ extra'`
    with `extra'` tracking the end state's excess depth.  Pops always stay
    inside `extra` because the chain keeps `flowLevel ≥ fl₀`. -/
lemma FlowMonoChain.flowStack_invariant {fl₀ : Nat} {t s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ t n s') :
    ∀ base extra : Array Bool, t.flowStack = base ++ extra →
      extra.size = t.flowLevel - fl₀ → t.flowLevel ≥ fl₀ →
      ∃ extra', s'.flowStack = base ++ extra' ∧
        extra'.size = s'.flowLevel - fl₀ := by
  induction h with
  | zero _h_fl =>
    intro _base extra h_eq h_size _h_ge
    exact ⟨extra, h_eq, h_size⟩
  | @step s s_mid s'' m _h_fl h_snt h_rest ih =>
    intro base extra h_eq h_size h_ge
    have h_mid_ge : s_mid.flowLevel ≥ fl₀ := h_rest.flowLevel_ge_start
    rcases scanNextToken_flowStack_step h_snt with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h0, h1, h2⟩
    · -- preserve
      exact ih base extra (h2.trans h_eq) (by omega) (by omega)
    · -- push true
      refine ih base (extra.push true) ?_ ?_ (by omega)
      · rw [h2, h_eq, Array.push_append]
      · rw [Array.size_push]; omega
    · -- push false
      refine ih base (extra.push false) ?_ ?_ (by omega)
      · rw [h2, h_eq, Array.push_append]
      · rw [Array.size_push]; omega
    · -- pop: the chain floor keeps the pop inside `extra`
      have h_extra : 0 < extra.size := by omega
      refine ih base extra.pop ?_ ?_ (by omega)
      · rw [h2, h_eq, Array.pop_append, ite_eq_right]
        simp only [Array.isEmpty_iff]
        intro hh; subst hh; simp at h_extra
      · rw [Array.size_pop]; omega

/-- A balanced `FlowMonoChain` — starting and ending at the floor flow level —
    preserves `flowStack` exactly. -/
lemma FlowMonoChain.flowStack_eq {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s')
    (h_s : s.flowLevel = fl₀) (h_s' : s'.flowLevel = fl₀) :
    s'.flowStack = s.flowStack := by
  obtain ⟨extra', h_eq, h_size⟩ :=
    h.flowStack_invariant s.flowStack #[] (by simp) (by simp [h_s]) (by omega)
  have h_zero : extra'.size = 0 := by omega
  rw [h_eq, Array.eq_empty_of_size_eq_zero h_zero, Array.append_empty]

/-! ## §6  `explicitKeyStack` twins (item 98)

`explicitKeyStack` moves in the same lockstep as `flowStack` — pushed by the
two flow opens (the outer explicit-key stamp), popped by the two closes,
copied everywhere else (`Proofs/Scanner/ScannerEkStackPreservation.lean`).
The chain theorems below are the `flowStack` §3–§5 clones; the pushed VALUE
is existential because the chain lemmas never read it. -/

set_option maxHeartbeats 800000 in
/-- The flow-indicator dispatcher's `explicitKeyStack` step fact: `[`/`{`
    push one entry (incrementing `flowLevel`), `]`/`}` pop (with
    `flowLevel > 0`), and `,` preserves both fields. -/
lemma FlowStackChain.dispatchFlowIndicators_ekStack_step (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    (s'.flowLevel = s.flowLevel ∧ s'.explicitKeyStack = s.explicitKeyStack) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧
      ∃ e, s'.explicitKeyStack = s.explicitKeyStack.push e) ∨
    (s.flowLevel > 0 ∧ s'.flowLevel + 1 = s.flowLevel ∧
      s'.explicitKeyStack = s.explicitKeyStack.pop) := by
  unfold scanNextToken_dispatchFlowIndicators at h
  replace h := peel_flowAdj h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- c == '['
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact Or.inr (Or.inl ⟨FlowStackChain.scanFlowSequenceStart_flowLevel s,
      _, ScannerCorrectness.scanFlowSequenceStart_ek_pushed s⟩)
  -- c == ']'
  · split at h
    · split at h
      · simp at h
      · rename_i h_lvl
        split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
            have h_pos : s.flowLevel > 0 := by
              simp only [beq_iff_eq] at h_lvl; omega
            refine Or.inr (Or.inr
              ⟨h_pos, ?_, ScannerCorrectness.scanFlowSequenceEnd_ekstack_popped s⟩)
            rw [ScannerFlowCollection.scanFlowSequenceEnd_flowLevel_pos s h_pos]
            omega
    -- c == '{'
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact Or.inr (Or.inl ⟨FlowStackChain.scanFlowMappingStart_flowLevel s,
          _, ScannerCorrectness.scanFlowMappingStart_ek_pushed s⟩)
      -- c == '}'
      · split at h
        · split at h
          · simp at h
          · rename_i h_lvl
            split at h
            · simp at h
            · split at h
              · simp at h
              · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                have h_pos : s.flowLevel > 0 := by
                  simp only [beq_iff_eq] at h_lvl; omega
                refine Or.inr (Or.inr
                  ⟨h_pos, ?_, ScannerCorrectness.scanFlowMappingEnd_ekstack_popped s⟩)
                rw [ScannerFlowCollection.scanFlowMappingEnd_flowLevel_pos s h_pos]
                omega
        -- c == ','
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                exact Or.inl
                  ⟨ScannerCorrectness.scanFlowEntry_preserves_flowLevel _ _ h_entry,
                   ScannerEkStack.scanFlowEntry_preserves_explicitKeyStack _ _ h_entry⟩
          · simp at h

set_option maxHeartbeats 1600000 in
/-- One `scanNextToken` step moves `explicitKeyStack` in lockstep with
    `flowLevel`: preserve both, push one entry (a flow open), or pop one
    (a flow close). -/
lemma scanNextToken_ekStack_step {s s' : ScannerState}
    (h : scanNextToken s = .ok (some s')) :
    (s'.flowLevel = s.flowLevel ∧ s'.explicitKeyStack = s.explicitKeyStack) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧
      ∃ e, s'.explicitKeyStack = s.explicitKeyStack.push e) ∨
    (s.flowLevel > 0 ∧ s'.flowLevel + 1 = s.flowLevel ∧
      s'.explicitKeyStack = s.explicitKeyStack.pop) := by
  unfold scanNextToken at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  rename_i s1 c1 h_pre
  have h_pre_st := ScannerEkStack.preprocess_preserves_explicitKeyStack s _ _ h_pre
  have h_pre_fl := preprocess_preserves_flowLevel s _ _ h_pre
  -- §9.2 dangling-node check (item 133), then the §8.1 flow-value floor (item 172)
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h <;> (try (simp at h; done))
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    refine Or.inl ⟨?_, ?_⟩
    · rw [ScannerCorrectness.dispatchStructural_preserves_flowLevel s1 c1 _
        (by assumption), h_pre_fl]
    · rw [ScannerEkStack.dispatchStructural_preserves_explicitKeyStack s1 c1 _
        (by assumption), h_pre_st]
  · have h_allow_st : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).explicitKeyStack = st.explicitKeyStack := by intro st; split <;> rfl
    have h_allow_fl : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).flowLevel = st.flowLevel := by intro st; split <;> rfl
    split at h <;> (try (simp at h; done))  -- checkBareDocument (item 132)
    split at h <;> (try (simp at h; done))
    split at h <;> (try (simp at h; done))
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      have h_step := FlowStackChain.dispatchFlowIndicators_ekStack_step _ _ c1
        (by assumption)
      rcases h_step with ⟨h1, h2⟩ | ⟨h1, e, h2⟩ | ⟨h0, h1, h2⟩
      · rw [h_allow_fl, h_pre_fl] at h1; rw [h_allow_st, h_pre_st] at h2
        exact Or.inl ⟨h1, h2⟩
      · rw [h_allow_fl, h_pre_fl] at h1; rw [h_allow_st, h_pre_st] at h2
        exact Or.inr (Or.inl ⟨h1, e, h2⟩)
      · rw [h_allow_fl, h_pre_fl] at h0 h1; rw [h_allow_st, h_pre_st] at h2
        exact Or.inr (Or.inr ⟨h0, h1, h2⟩)
    · split at h <;> (try (simp at h; done))
      split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        refine Or.inl ⟨?_, ?_⟩
        · rw [ScannerCorrectness.dispatchBlockIndicators_preserves_flowLevel _ c1 _
            (by assumption), h_allow_fl, h_pre_fl]
        · rw [ScannerEkStack.dispatchBlockIndicators_preserves_explicitKeyStack _ c1 _
            (by assumption), h_allow_st, h_pre_st]
      · split at h <;> (try (simp at h; done))
        split at h <;> (try (simp at h; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        refine Or.inl ⟨?_, ?_⟩
        · rw [ScannerCorrectness.dispatchContent_preserves_flowLevel _ c1 _
            (by assumption), h_allow_fl, h_pre_fl]
        · rw [ScannerEkStack.dispatchContent_preserves_explicitKeyStack _ c1 _
            (by assumption), h_allow_st, h_pre_st]

/-- The `explicitKeyStack` chain invariant — `flowStack_invariant`'s twin. -/
lemma FlowMonoChain.ekStack_invariant {fl₀ : Nat} {t s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ t n s') :
    ∀ base extra : Array (Option Nat × Int), t.explicitKeyStack = base ++ extra →
      extra.size = t.flowLevel - fl₀ → t.flowLevel ≥ fl₀ →
      ∃ extra', s'.explicitKeyStack = base ++ extra' ∧
        extra'.size = s'.flowLevel - fl₀ := by
  induction h with
  | zero _h_fl =>
    intro _base extra h_eq h_size _h_ge
    exact ⟨extra, h_eq, h_size⟩
  | @step s s_mid s'' m _h_fl h_snt h_rest ih =>
    intro base extra h_eq h_size h_ge
    have h_mid_ge : s_mid.flowLevel ≥ fl₀ := h_rest.flowLevel_ge_start
    rcases scanNextToken_ekStack_step h_snt with
      ⟨h1, h2⟩ | ⟨h1, e, h2⟩ | ⟨h0, h1, h2⟩
    · exact ih base extra (h2.trans h_eq) (by omega) (by omega)
    · refine ih base (extra.push e) ?_ ?_ (by omega)
      · rw [h2, h_eq, Array.push_append]
      · rw [Array.size_push]; omega
    · have h_extra : 0 < extra.size := by omega
      refine ih base extra.pop ?_ ?_ (by omega)
      · rw [h2, h_eq, Array.pop_append, ite_eq_right]
        simp only [Array.isEmpty_iff]
        intro hh; subst hh; simp at h_extra
      · rw [Array.size_pop]; omega

/-- A balanced `FlowMonoChain` preserves `explicitKeyStack` exactly —
    `flowStack_eq`'s twin (item 98). -/
lemma FlowMonoChain.ekStack_eq {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s')
    (h_s : s.flowLevel = fl₀) (h_s' : s'.flowLevel = fl₀) :
    s'.explicitKeyStack = s.explicitKeyStack := by
  obtain ⟨extra', h_eq, h_size⟩ :=
    h.ekStack_invariant s.explicitKeyStack #[] (by simp) (by simp [h_s]) (by omega)
  have h_zero : extra'.size = 0 := by omega
  rw [h_eq, Array.eq_empty_of_size_eq_zero h_zero, Array.append_empty]

/-- The open→body→close composites' `explicitKeyLine` step: the open pushed
    the outer stamp, the balanced body left the stack alone, so the value the
    close restores is the stamp the open saved (item 98). -/
lemma ek_restore_of_push_body {s₁ s₂ : ScannerState} {ek : Option Nat}
    {ekc : Int} {base : Array (Option Nat × Int)}
    (h_push : s₁.explicitKeyStack = base.push (ek, ekc))
    (h_body : s₂.explicitKeyStack = s₁.explicitKeyStack) :
    (s₂.explicitKeyStack.back?.getD (none, -1)).1 = ek := by
  rw [h_body, h_push, Array.back?_push, Option.getD_some]

end L4YAML.Proofs.EmitterScannability

end Blanket
