import L4YAML.Scanner
import L4YAML.Proofs.ScannerLoopInvariant
import L4YAML.Proofs.ScannerProgress

/-!
# Scanner Bound Preservation (Phase 4.2.A)

Proof that `scanNextToken` preserves the offset/inputEnd/input
bound invariant:
  `s'.offset ≤ s'.inputEnd ∧ s'.inputEnd = s.inputEnd ∧ s'.input = s.input`

Additionally threads `IsValid` (UTF-8 position validity) through
the scanner pipeline.

## Structure

1. Building-block lemmas for advance, emit, pushIndent, saveSimpleKey
2. Per-loop preservation lemmas (inputEnd, input, offset bound, IsValid)
3. Per-dispatch preservation theorems
4. Composition into `scanNextToken_preserves_bound`
-/

namespace L4YAML.Proofs.ScannerBound

open L4YAML.Scanner
open L4YAML.Proofs.ScannerLoopInvariant
open L4YAML.Proofs.ScannerProgress

/-! ## §1  Bound Invariant Bundle

For threading through the scanner, we track four properties relative
to an original state `s₀`:
1. offset ≤ inputEnd
2. inputEnd = s₀.inputEnd
3. input = s₀.input
4. IsValid at the current position
-/

/-- Bundle of properties preserved through scanner operations. -/
structure BoundInv (s₀ s : ScannerState) : Prop where
  offset_le : s.offset ≤ s.inputEnd
  inputEnd_eq : s.inputEnd = s₀.inputEnd
  input_eq : s.input = s₀.input
  isValid : String.Pos.Raw.IsValid s.input ⟨s.offset⟩

/-- Reflexive: BoundInv holds for the initial state. -/
theorem BoundInv.refl (s : ScannerState)
    (h_le : s.offset ≤ s.inputEnd)
    (h_iv : String.Pos.Raw.IsValid s.input ⟨s.offset⟩) :
    BoundInv s s :=
  ⟨h_le, rfl, rfl, h_iv⟩

/-- BoundInv is transitive through intermediate states. -/
theorem BoundInv.trans {s₀ s₁ s₂ : ScannerState}
    (h₁ : BoundInv s₀ s₁) (h₂ : BoundInv s₁ s₂) :
    BoundInv s₀ s₂ :=
  ⟨h₂.offset_le,
   by rw [h₂.inputEnd_eq, h₁.inputEnd_eq],
   by rw [h₂.input_eq, h₁.input_eq],
   h₂.isValid⟩

/-! ## §2  Building-Block BoundInv Preservation -/

/-- `advance` preserves BoundInv. -/
theorem advance_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ s.advance := by
  have hie : s.inputEnd = s.input.utf8ByteSize := by
    rw [h.inputEnd_eq, h.input_eq]; exact hend
  exact ⟨
    by rw [advance_inputEnd]; exact advance_offset_le s h.isValid h.offset_le hie,
    by rw [advance_inputEnd, h.inputEnd_eq],
    by rw [advance_input, h.input_eq],
    advance_isValid s h.isValid hie
  ⟩

/-- `emit` preserves BoundInv. -/
theorem emit_BoundInv {s₀ : ScannerState} (s : ScannerState) (tok : YamlToken)
    (h : BoundInv s₀ s) :
    BoundInv s₀ (s.emit tok) :=
  ⟨by rw [emit_offset, emit_inputEnd]; exact h.offset_le,
   by rw [emit_inputEnd]; exact h.inputEnd_eq,
   by rw [emit_input]; exact h.input_eq,
   by rw [emit_input]; rw [show (s.emit tok).offset = s.offset from rfl]; exact h.isValid⟩

/-- `emitAt` preserves BoundInv. -/
theorem emitAt_BoundInv {s₀ : ScannerState} (s : ScannerState) (pos : YamlPos) (tok : YamlToken)
    (h : BoundInv s₀ s) :
    BoundInv s₀ (s.emitAt pos tok) :=
  -- emitAt is just another emit with position; doesn't touch offset/inputEnd/input
  ⟨by unfold ScannerState.emitAt; exact h.offset_le,
   by unfold ScannerState.emitAt; exact h.inputEnd_eq,
   by unfold ScannerState.emitAt; exact h.input_eq,
   by unfold ScannerState.emitAt; exact h.isValid⟩

/-- `pushSequenceIndent` preserves BoundInv. -/
theorem pushSequenceIndent_BoundInv {s₀ : ScannerState} (s : ScannerState) (col : Int)
    (h : BoundInv s₀ s) :
    BoundInv s₀ (pushSequenceIndent s col) :=
  ⟨by rw [pushSequenceIndent_offset, pushSequenceIndent_inputEnd]; exact h.offset_le,
   by rw [pushSequenceIndent_inputEnd]; exact h.inputEnd_eq,
   by rw [pushSequenceIndent_input]; exact h.input_eq,
   by rw [pushSequenceIndent_input]; rw [pushSequenceIndent_offset]; exact h.isValid⟩

/-- `pushMappingIndent` preserves BoundInv. -/
theorem pushMappingIndent_BoundInv {s₀ : ScannerState} (s : ScannerState) (col : Int)
    (h : BoundInv s₀ s) :
    BoundInv s₀ (pushMappingIndent s col) :=
  ⟨by rw [pushMappingIndent_offset, pushMappingIndent_inputEnd]; exact h.offset_le,
   by rw [pushMappingIndent_inputEnd]; exact h.inputEnd_eq,
   by rw [pushMappingIndent_input]; exact h.input_eq,
   by rw [pushMappingIndent_input]; rw [pushMappingIndent_offset]; exact h.isValid⟩

/-- `saveSimpleKey` preserves BoundInv. -/
theorem saveSimpleKey_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (h : BoundInv s₀ s) :
    BoundInv s₀ (saveSimpleKey s) :=
  ⟨by rw [saveSimpleKey_offset, saveSimpleKey_inputEnd]; exact h.offset_le,
   by rw [saveSimpleKey_inputEnd]; exact h.inputEnd_eq,
   by rw [saveSimpleKey_input]; exact h.input_eq,
   by rw [saveSimpleKey_input]; rw [saveSimpleKey_offset]; exact h.isValid⟩

/-- Field updates not touching offset/inputEnd/input preserve BoundInv. -/
theorem fieldUpdate_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (s' : ScannerState)
    (h : BoundInv s₀ s)
    (hoff : s'.offset = s.offset)
    (hie : s'.inputEnd = s.inputEnd)
    (hinp : s'.input = s.input) :
    BoundInv s₀ s' :=
  ⟨by rw [hoff, hie]; exact h.offset_le,
   by rw [hie]; exact h.inputEnd_eq,
   by rw [hinp]; exact h.input_eq,
   by rw [hinp, hoff]; exact h.isValid⟩

/-! ## §3  Flow Indicator Scanners — BoundInv Preservation

These are the simplest: each is `pushIndent.saveKey.emit.advance`
or `flowPop.emit.advance`, with no loops. -/

-- Helper: the result of a flow open/close function has the same
-- offset/inputEnd/input as advance applied to an intermediate state
-- that preserves BoundInv.

theorem scanFlowSequenceStart_BoundInv (s : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize) :
    BoundInv s (scanFlowSequenceStart s) := by
  -- scanFlowSequenceStart s = { s_adv with flowLevel, flowStack, ... }
  -- where s_adv = ({ s with simpleKey := ... }.emit .flowSequenceStart).advance
  -- The result has the same offset/inputEnd/input as s_adv.
  let s_kd : ScannerState := { s with simpleKey := { possible := false } }
  let s_em := s_kd.emit .flowSequenceStart
  let s_adv := s_em.advance
  have h1 : BoundInv s s_kd := fieldUpdate_BoundInv _ _ h rfl rfl rfl
  have h2 : BoundInv s s_em := emit_BoundInv _ _ h1
  have h3 : BoundInv s s_adv := advance_BoundInv _ h2 hend
  exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩

theorem scanFlowMappingStart_BoundInv (s : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize) :
    BoundInv s (scanFlowMappingStart s) := by
  let s_kd : ScannerState := { s with simpleKey := { possible := false } }
  let s_em := s_kd.emit .flowMappingStart
  let s_adv := s_em.advance
  have h1 : BoundInv s s_kd := fieldUpdate_BoundInv _ _ h rfl rfl rfl
  have h2 : BoundInv s s_em := emit_BoundInv _ _ h1
  have h3 : BoundInv s s_adv := advance_BoundInv _ h2 hend
  exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩

theorem scanFlowSequenceEnd_BoundInv (s : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize) :
    BoundInv s (scanFlowSequenceEnd s) := by
  let s_em := s.emit .flowSequenceEnd
  let s_adv := s_em.advance
  have h2 : BoundInv s s_em := emit_BoundInv _ _ h
  have h3 : BoundInv s s_adv := advance_BoundInv _ h2 hend
  exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩

theorem scanFlowMappingEnd_BoundInv (s : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize) :
    BoundInv s (scanFlowMappingEnd s) := by
  let s_em := s.emit .flowMappingEnd
  let s_adv := s_em.advance
  have h2 : BoundInv s s_em := emit_BoundInv _ _ h
  have h3 : BoundInv s s_adv := advance_BoundInv _ h2 hend
  exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩

theorem scanFlowEntry_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanFlowEntry s = .ok s') :
    BoundInv s s' := by
  unfold scanFlowEntry at hok
  simp only [bind, Except.bind] at hok
  -- Both paths produce { (s.emit .flowEntry).advance with simpleKeyAllowed := true }
  let s_em := s.emit .flowEntry
  let s_adv := s_em.advance
  have h_adv : BoundInv s s_adv := advance_BoundInv _ (emit_BoundInv _ _ h) hend
  split at hok
  · split at hok <;> (try contradiction)
    injection hok with hok; subst hok
    exact ⟨h_adv.offset_le, h_adv.inputEnd_eq, h_adv.input_eq, h_adv.isValid⟩
  · injection hok with hok; subst hok
    exact ⟨h_adv.offset_le, h_adv.inputEnd_eq, h_adv.input_eq, h_adv.isValid⟩

/-! ## §4  Block Indicator Scanners — BoundInv Preservation -/

theorem scanBlockEntry_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanBlockEntry s = .ok s') :
    BoundInv s s' := by
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind] at hok
  split at hok  -- !s.inFlow
  · -- block: tab check + pushSequenceIndent
    split at hok <;> try contradiction
    injection hok with hok; subst hok
    let s_pi := pushSequenceIndent s s.col
    let s_em := s_pi.emit .blockEntry
    let s_adv := s_em.advance
    have h1 : BoundInv s s_pi := pushSequenceIndent_BoundInv _ _ h
    have h2 : BoundInv s s_em := emit_BoundInv _ _ h1
    have h3 : BoundInv s s_adv := advance_BoundInv _ h2 hend
    exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩
  · -- flow: no pushSequenceIndent
    injection hok with hok; subst hok
    let s_em := s.emit .blockEntry
    let s_adv := s_em.advance
    have h2 : BoundInv s s_em := emit_BoundInv _ _ h
    have h3 : BoundInv s s_adv := advance_BoundInv _ h2 hend
    exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩

theorem scanKey_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanKey s = .ok s') :
    BoundInv s s' := by
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  -- The structure: pushMappingIndent conditionally, emit .key, advance, tab check, ok
  -- After simp, splits on the conditions
  split at hok  -- !s.inFlow (pushMappingIndent)
  · -- block: pushMappingIndent
    let s_pi := pushMappingIndent s s.col
    let s_em := s_pi.emit .key
    let s_adv := s_em.advance
    have h1 : BoundInv s s_pi := pushMappingIndent_BoundInv _ _ h
    have h2 : BoundInv s s_em := emit_BoundInv _ _ h1
    have h3 : BoundInv s s_adv := advance_BoundInv _ h2 hend
    -- Tab check after advance may error — split on it
    split at hok
    · split at hok <;> try contradiction
      injection hok with hok; subst hok
      exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩
    · injection hok with hok; subst hok
      exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩
  · -- flow: no pushMappingIndent
    let s_em := s.emit .key
    let s_adv := s_em.advance
    have h2 : BoundInv s s_em := emit_BoundInv _ _ h
    have h3 : BoundInv s s_adv := advance_BoundInv _ h2 hend
    split at hok
    · split at hok <;> try contradiction
      injection hok with hok; subst hok
      exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩
    · injection hok with hok; subst hok
      exact ⟨h3.offset_le, h3.inputEnd_eq, h3.input_eq, h3.isValid⟩

/-! ## §5  Per-Dispatch BoundInv Preservation

These compose the leaf-level lemmas from §3-§4. -/

/-- `dispatchFlowIndicators` preserves BoundInv.
    Fully proven — all 5 flow indicator functions are loop-free. -/
theorem dispatchFlowIndicators_preserves_bound (s s' : ScannerState) (c : Char)
    (h_bi : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    BoundInv s s' := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok  -- c == '['
  · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
    exact scanFlowSequenceStart_BoundInv s h_bi hend
  · split at hok  -- c == ']'
    · split at hok  -- flowLevel == 0
      · cases hok
      · split at hok  -- validateFlowClose
        · cases hok
        · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
          exact scanFlowSequenceEnd_BoundInv s h_bi hend
    · split at hok  -- c == '{'
      · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
        exact scanFlowMappingStart_BoundInv s h_bi hend
      · split at hok  -- c == '}'
        · split at hok
          · cases hok
          · split at hok
            · cases hok
            · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
              exact scanFlowMappingEnd_BoundInv s h_bi hend
        · split at hok  -- c == ','
          · split at hok
            · cases hok
            · -- Generalize to preserve scanFlowEntry connection
              generalize h_fe : scanFlowEntry s = fe_result at hok
              cases fe_result with
              | error e => simp at hok
              | ok r =>
                simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                exact scanFlowEntry_BoundInv s _ h_bi hend h_fe
          · nomatch hok

-- scanValue BoundInv: complex control flow but no loops.
-- All paths end with (emit .value).advance on a state derived from s
-- by offset-preserving operations.
theorem scanValue_BoundInv (s s' : ScannerState)
    (h_bi : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanValue s = .ok s') :
    BoundInv s s' := by
  unfold scanValue at hok
  dsimp only [] at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · contradiction  -- scanValueValidate = .error
  · split at hok
    · contradiction  -- scanValueTabCheck = .error
    · injection hok with hok; subst hok
      -- Chain BoundInv: scanValueClearKey → scanValuePrepare → emit .value → advance
      have h_off : (scanValuePrepare (scanValueClearKey s)).offset = s.offset := by
        have h_ck : (scanValueClearKey s).offset = s.offset := by
          simp only [scanValueClearKey]
          split
          · split <;> (try split) <;> rfl
          · rfl
        have h_vp : ∀ kc : ScannerState, (scanValuePrepare kc).offset = kc.offset := by
          intro kc; simp only [scanValuePrepare]
          split
          · split <;> (try split) <;> rfl
          · split
            · rfl
            · split
              · unfold pushMappingIndent ScannerState.emit; split <;> rfl
              · rfl
        rw [h_vp, h_ck]
      have h_ie : (scanValuePrepare (scanValueClearKey s)).inputEnd = s.inputEnd := by
        have h_ck : (scanValueClearKey s).inputEnd = s.inputEnd := by
          simp only [scanValueClearKey]
          split
          · split <;> (try split) <;> rfl
          · rfl
        have h_vp : ∀ kc : ScannerState, (scanValuePrepare kc).inputEnd = kc.inputEnd := by
          intro kc; simp only [scanValuePrepare]
          split
          · split <;> (try split) <;> rfl
          · split
            · rfl
            · split
              · unfold pushMappingIndent ScannerState.emit; split <;> rfl
              · rfl
        rw [h_vp, h_ck]
      have h_inp : (scanValuePrepare (scanValueClearKey s)).input = s.input := by
        have h_ck : (scanValueClearKey s).input = s.input := by
          simp only [scanValueClearKey]
          split
          · split <;> (try split) <;> rfl
          · rfl
        have h_vp : ∀ kc : ScannerState, (scanValuePrepare kc).input = kc.input := by
          intro kc; simp only [scanValuePrepare]
          split
          · split <;> (try split) <;> rfl
          · split
            · rfl
            · split
              · unfold pushMappingIndent ScannerState.emit; split <;> rfl
              · rfl
        rw [h_vp, h_ck]
      have h_iv : String.Pos.Raw.IsValid (scanValuePrepare (scanValueClearKey s)).input
          ⟨(scanValuePrepare (scanValueClearKey s)).offset⟩ := by
        rw [h_inp, h_off]; exact h_bi.isValid
      have h_prep : BoundInv s (scanValuePrepare (scanValueClearKey s)) :=
        ⟨by rw [h_off, h_ie]; exact h_bi.offset_le,
         by rw [h_ie],
         by rw [h_inp],
         h_iv⟩
      have h_em := emit_BoundInv _ .value h_prep
      have h_adv := advance_BoundInv _ h_em hend
      exact ⟨h_adv.offset_le, h_adv.inputEnd_eq, h_adv.input_eq, h_adv.isValid⟩

/-- `dispatchBlockIndicators` preserves BoundInv.
    Fully proven — scanBlockEntry, scanKey use no loops. scanValue
    uses no loops either (just field updates + advance). -/
theorem dispatchBlockIndicators_preserves_bound (s s' : ScannerState) (c : Char)
    (h_bi : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    BoundInv s s' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok  -- c == '-' && ...
  · split at hok
    · cases hok
    · injection hok with hok; injection hok with hok; subst hok
      exact scanBlockEntry_BoundInv s _ h_bi hend ‹_›
  · split at hok  -- c == '?' && ...
    · split at hok
      · cases hok
      · injection hok with hok; injection hok with hok; subst hok
        exact scanKey_BoundInv s _ h_bi hend ‹_›
    · split at hok  -- c == ':' && ...
      · split at hok
        · cases hok
        · injection hok with hok; injection hok with hok; subst hok
          exact scanValue_BoundInv s _ h_bi hend ‹_›
      · nomatch hok

/-! ## §6  Sorry-based Dispatch Lemmas

These dispatch-level lemmas are stated with `sorry`; they represent
the remaining proof obligations for full `scanNextToken_preserves_bound`. -/

-- Preprocess preserves BoundInv.
-- Proof requires: skipToContent (loop), unwindIndents (loop), saveSimpleKey
theorem preprocess_preserves_bound (s : ScannerState) (sp : ScannerState) (c : Char)
    (h_bi : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanNextToken_preprocess s = .ok (some (sp, c))) :
    BoundInv s sp := by
  sorry

-- Structural dispatch preserves BoundInv.
-- Proof requires: scanDocumentStart (advanceN 3), scanDocumentEnd (advanceN 3),
-- scanDirective (many loops)
theorem dispatchStructural_preserves_bound (s sp s' : ScannerState) (c : Char)
    (h_bi : BoundInv s sp) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanNextToken_dispatchStructural sp c = .ok (some s')) :
    BoundInv s s' := by
  sorry

-- Content dispatch preserves BoundInv.
-- Proof requires: all scalar scanners (loops), anchor/alias/tag (loops)
theorem dispatchContent_preserves_bound (s sp s' : ScannerState) (c : Char)
    (h_bi : BoundInv s sp) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanNextToken_dispatchContent sp c = .ok s') :
    BoundInv s s' := by
  sorry

/-! ## §7  scanNextToken_preserves_bound — Capstone Composition -/

-- Helper: allowDirectives toggle doesn't affect BoundInv
theorem allowDirectives_toggle_BoundInv {s₀ sp : ScannerState}
    (h : BoundInv s₀ sp) :
    BoundInv s₀ { sp with allowDirectives := false, documentEverStarted := true } :=
  fieldUpdate_BoundInv _ _ h rfl rfl rfl

/-- Main composition: `scanNextToken` preserves BoundInv.

This mirrors the per-dispatch structure of `scanNextToken_progress`
but tracks the full BoundInv bundle (offset ≤ inputEnd, inputEnd/input
preserved, IsValid) instead of just offset increase.

The proof dispatches to per-dispatch preservation lemmas from §3-§6,
some of which currently use `sorry` for sub-scanner loops. -/
theorem scanNextToken_preserves_bound_full (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s'))
    (h_bi : BoundInv s s)
    (hend : s.inputEnd = s.input.utf8ByteSize) :
    BoundInv s s' := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at h
  -- Split on preprocess result
  split at h
  · cases h  -- error
  · split at h
    · simp at h  -- none ≠ some
    · rename_i sp c h_pre
      have h_bi_sp := preprocess_preserves_bound s sp c h_bi hend h_pre
      -- Helpers for dispatchers that use reflexive BoundInv
      have h_bi_sp_refl : BoundInv sp sp :=
        BoundInv.refl sp h_bi_sp.offset_le h_bi_sp.isValid
      have h_hend_sp : sp.inputEnd = sp.input.utf8ByteSize := by
        rw [h_bi_sp.inputEnd_eq, h_bi_sp.input_eq]; exact hend
      -- Split on dispatchStructural
      split at h
      · cases h  -- error
      · split at h
        · -- some s1 (structural handled it)
          simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          exact dispatchStructural_preserves_bound s sp _ c h_bi_sp hend ‹_›
        · -- none (structural passed, continue to flow/block/content)
          -- Outermost match is checkBlockFlowIndent (wrapping the if-expression)
          split at h
          · cases h  -- indent error
          · -- Case-split on allowDirectives to resolve the if-expression
            rcases h_ad : sp.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at h
            · -- false case: dispatchers use sp directly
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp c = fi at h
              cases fi with
              | error => cases h
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                  exact BoundInv.trans h_bi_sp
                    (dispatchFlowIndicators_preserves_bound sp _ c h_bi_sp_refl h_hend_sp h_fi)
                | none =>
                  generalize h_bk : scanNextToken_dispatchBlockIndicators sp c = bk at h
                  cases bk with
                  | error => cases h
                  | ok bk_opt =>
                    cases bk_opt with
                    | some s_bk =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                      exact BoundInv.trans h_bi_sp
                        (dispatchBlockIndicators_preserves_bound sp _ c h_bi_sp_refl h_hend_sp h_bk)
                    | none =>
                      generalize h_dc : scanNextToken_dispatchContent sp c = dc at h
                      cases dc with
                      | error => cases h
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                        exact dispatchContent_preserves_bound s sp _ c h_bi_sp hend h_dc
            · -- true case: dispatchers use { sp with allowDirectives := false, ... }
              -- After simp reduces the if, h contains dispatchers applied
              -- to the struct. Since the struct has the same offset/inputEnd/input
              -- as sp, all BoundInv results follow from the false case structure.
              -- We split directly on the dispatch matches in h.
              have h_bi_sp2 : BoundInv s
                  { sp with allowDirectives := false, documentEverStarted := true } :=
                allowDirectives_toggle_BoundInv h_bi_sp
              -- The dispatchers in h are applied to the expanded struct.
              -- Split on them directly.
              split at h  -- flow dispatcher result
              · cases h  -- error
              · split at h  -- flow some/none
                · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                  exact BoundInv.trans h_bi_sp2
                    (dispatchFlowIndicators_preserves_bound _ _ c
                      (BoundInv.refl _ h_bi_sp2.offset_le h_bi_sp2.isValid)
                      (by rw [h_bi_sp2.inputEnd_eq, h_bi_sp2.input_eq]; exact hend) ‹_›)
                · split at h  -- block dispatcher result
                  · cases h
                  · split at h  -- block some/none
                    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                      exact BoundInv.trans h_bi_sp2
                        (dispatchBlockIndicators_preserves_bound _ _ c
                          (BoundInv.refl _ h_bi_sp2.offset_le h_bi_sp2.isValid)
                          (by rw [h_bi_sp2.inputEnd_eq, h_bi_sp2.input_eq]; exact hend) ‹_›)
                    · split at h  -- content dispatcher result
                      · cases h
                      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                        exact dispatchContent_preserves_bound s _ _ c h_bi_sp2 hend ‹_›

/-- Wrapper matching the signature used in EmitterScannability. -/
theorem scanNextToken_preserves_bound (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s'))
    (h_le : s.offset ≤ s.inputEnd)
    (h_ie : s.inputEnd = s.input.utf8ByteSize)
    (h_iv : String.Pos.Raw.IsValid s.input ⟨s.offset⟩) :
    s'.offset ≤ s'.inputEnd ∧ s'.inputEnd = s.inputEnd ∧ s'.input = s.input
    ∧ String.Pos.Raw.IsValid s'.input ⟨s'.offset⟩ := by
  have h_bi := scanNextToken_preserves_bound_full s s' h (BoundInv.refl s h_le h_iv) h_ie
  exact ⟨h_bi.offset_le, h_bi.inputEnd_eq, h_bi.input_eq, h_bi.isValid⟩

end L4YAML.Proofs.ScannerBound
