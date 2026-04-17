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

/-! ## §5b  Loop-Level BoundInv Preservation

Building blocks for scanner loops. Each follows the same pattern:
induction on fuel, with `advance_BoundInv` at each step.

Note: Functions using `termination_by fuel` (WF recursion) do NOT reduce
`f s 0 = s` definitionally.  We must `simp only [f]` in the zero case. -/

/-- `advanceNLoop` preserves BoundInv. -/
theorem advanceNLoop_BoundInv {s₀ : ScannerState} (s : ScannerState) (n : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (ScannerState.advanceNLoop s n) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih => exact ih _ (advance_BoundInv s h hend)

/-- `advanceN` preserves BoundInv. -/
theorem advanceN_BoundInv {s₀ : ScannerState} (s : ScannerState) (n : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (s.advanceN n) :=
  advanceNLoop_BoundInv s n h hend

/-- `skipWhitespaceLoop` preserves BoundInv. -/
theorem skipWhitespaceLoop_BoundInv {s₀ : ScannerState} (s : ScannerState) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipWhitespaceLoop s fuel) := by
  induction fuel generalizing s with
  | zero => simp only [skipWhitespaceLoop]; exact h
  | succ n ih =>
    simp only [skipWhitespaceLoop]
    split  -- peek?
    · split  -- isWhiteSpaceBool
      · exact ih _ (advance_BoundInv s h hend)
      · exact h
    · exact h

/-- `skipWhitespace` preserves BoundInv. -/
theorem skipWhitespace_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipWhitespace s) :=
  skipWhitespaceLoop_BoundInv s _ h hend

/-- `skipSpacesLoop` preserves BoundInv. -/
theorem skipSpacesLoop_BoundInv {s₀ : ScannerState} (s : ScannerState) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipSpacesLoop s fuel) := by
  induction fuel generalizing s with
  | zero => simp only [skipSpacesLoop]; exact h
  | succ n ih =>
    simp only [skipSpacesLoop]
    split  -- peek? = some ' '
    · exact ih _ (advance_BoundInv s h hend)
    · exact h

/-- `skipSpaces` preserves BoundInv. -/
theorem skipSpaces_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipSpaces s) :=
  skipSpacesLoop_BoundInv s _ h hend

/-- `collectCommentTextLoop` preserves BoundInv (in second component). -/
theorem collectCommentTextLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (text : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectCommentTextLoop s text fuel).2 := by
  induction fuel generalizing s text with
  | zero => simp only [collectCommentTextLoop]; exact h
  | succ n ih =>
    simp only [collectCommentTextLoop]
    split  -- peek? = some c
    · split  -- isLineBreakBool c
      · exact h
      · exact ih _ _ (advance_BoundInv s h hend)
    · exact h

/-- `skipToContentComment` preserves BoundInv.
    Handles the `#` → advance → `collectCommentTextLoop` → field update path. -/
theorem skipToContentComment_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipToContentComment s) := by
  unfold skipToContentComment
  simp only []
  split  -- peek? = some '#'
  · -- some '#': comment path
    split  -- peekBack? or next inner match
    <;> (split <;> first
      | (exact fieldUpdate_BoundInv _ _
          (collectCommentTextLoop_BoundInv s.advance "" _ (advance_BoundInv s h hend) hend)
          rfl rfl rfl)
      | exact h)
  · exact h

/-- `consumeNewline` preserves BoundInv.
    Handles `\n` (one advance) and `\r` + optional `\n` (one or two advances). -/
theorem consumeNewline_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (consumeNewline s) := by
  unfold consumeNewline
  split
  · -- '\n': { s.advance with needIndentCheck := true }
    exact fieldUpdate_BoundInv _ _ (advance_BoundInv s h hend) rfl rfl rfl
  · -- '\r'
    simp only []
    split
    · -- CRLF
      have h_adv := advance_BoundInv s h hend
      have h_ie : s.advance.inputEnd = s.advance.input.utf8ByteSize := by
        rw [h_adv.inputEnd_eq, h_adv.input_eq]; exact hend
      -- peek? returned some '\n', so offset < inputEnd
      have h_lt : s.advance.offset < s.advance.inputEnd := by
        rename_i h_peek
        simp only [ScannerState.peek?] at h_peek
        split at h_peek
        · assumption
        · cases h_peek
      refine ⟨?_, h_adv.inputEnd_eq, h_adv.input_eq, ?_⟩
      · -- offset_le
        rw [h_ie]
        exact raw_next_le_utf8ByteSize s.advance.input ⟨s.advance.offset⟩
          h_adv.isValid (show s.advance.offset < s.advance.input.utf8ByteSize by omega)
      · -- isValid
        exact next_isValid s.advance.input ⟨s.advance.offset⟩ h_adv.isValid
          (show s.advance.offset < s.advance.input.utf8ByteSize by omega)
    · -- CR only: { s.advance with needIndentCheck := true }
      exact fieldUpdate_BoundInv _ _ (advance_BoundInv s h hend) rfl rfl rfl
  · -- other: s
    exact h

/-- `skipToContentWs` preserves BoundInv. -/
theorem skipToContentWs_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : skipToContentWs s = .ok s') :
    BoundInv s₀ s' := by
  -- All .ok paths return skipSpaces s, skipWhitespace (skipSpaces s), or skipWhitespace s.
  unfold skipToContentWs at hok
  have h_ss := skipSpaces_BoundInv s h hend
  have h_wsss := skipWhitespace_BoundInv _ h_ss hend
  have h_ws := skipWhitespace_BoundInv s h hend
  simp only [] at hok
  -- Exhaust all branches. Every .ok path produces h_ss, h_wsss, or h_ws.
  repeat (first | cases hok; (first | exact h_wsss | exact h_ss | exact h_ws) | split at hok | cases hok)

/-- `skipToContentLoop` preserves BoundInv. -/
theorem skipToContentLoop_BoundInv {s₀ : ScannerState} (s s' : ScannerState) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : skipToContentLoop s fuel = .ok s') :
    BoundInv s₀ s' := by
  induction fuel generalizing s with
  | zero => simp only [skipToContentLoop] at hok; cases hok; exact h
  | succ n ih =>
    simp only [skipToContentLoop] at hok
    -- hok : (match skipToContentWs s with .error => .error | .ok s1 => ...) = .ok s'
    split at hok
    · cases hok  -- skipToContentWs error → contradiction
    · -- skipToContentWs returned .ok s1
      -- Extract the BoundInv for s1 from the split hypothesis
      rename_i s1 h_ws
      have h_s1 := skipToContentWs_BoundInv s s1 h hend h_ws
      -- s2 = skipToContentComment s1
      have h_cmt := skipToContentComment_BoundInv s1 h_s1 hend
      -- Split on (skipToContentComment s1).peek?
      split at hok
      · -- peek? = some c
        split at hok
        · -- isLineBreakBool c → consumeNewline → recurse
          have h_nl := consumeNewline_BoundInv _ h_cmt hend
          split at hok
          · -- !isInFlowSequence → { s3 with simpleKeyAllowed := true }
            refine ih _ ?_ hok
            exact fieldUpdate_BoundInv _ _ h_nl rfl rfl rfl
          · -- isInFlowSequence → s3
            exact ih _ h_nl hok
        · -- ¬ isLineBreakBool c → .ok s2
          cases hok; exact h_cmt
      · -- peek? = none → .ok s2
        cases hok; exact h_cmt

/-- `skipToContent` preserves BoundInv. -/
theorem skipToContent_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : skipToContent s = .ok s') :
    BoundInv s₀ s' :=
  skipToContentLoop_BoundInv s s' _ h hend hok

/-- `unwindIndentsLoop` preserves BoundInv.
    Each step emits `.blockEnd` and pops `indents`, neither touching offset/inputEnd/input. -/
theorem unwindIndentsLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (col : Int) (fuel : Nat)
    (h : BoundInv s₀ s) :
    BoundInv s₀ (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => simp only [unwindIndentsLoop]; exact h
  | succ n ih =>
    simp only [unwindIndentsLoop]
    split  -- currentIndent > col && indents.size > 1
    · exact ih _ (fieldUpdate_BoundInv _ _ (emit_BoundInv _ .blockEnd h) rfl rfl rfl)
    · exact h

/-- `unwindIndents` preserves BoundInv. -/
theorem unwindIndents_BoundInv {s₀ : ScannerState} (s : ScannerState) (col : Int)
    (h : BoundInv s₀ s) :
    BoundInv s₀ (unwindIndents s col) :=
  unwindIndentsLoop_BoundInv s col _ h

/-! ## §5c  Sub-Scanner BoundInv Preservation

BoundInv lemmas for individual scanner functions called by the structural
and content dispatchers.  All proofs complete — no sorry. -/

-- Simple fuel-based loops (provable)

theorem skipToEndOfLineLoop_BoundInv {s₀ : ScannerState} (s : ScannerState) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipToEndOfLineLoop s fuel) := by
  induction fuel generalizing s with
  | zero => simp only [skipToEndOfLineLoop]; exact h
  | succ n ih =>
    simp only [skipToEndOfLineLoop]
    split  -- peek?
    · split  -- isLineBreakBool
      · exact h
      · exact ih _ (advance_BoundInv s h hend)
    · exact h

theorem skipToEndOfLine_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipToEndOfLine s) :=
  skipToEndOfLineLoop_BoundInv s _ h hend

theorem skipDocEndWhitespace_BoundInv {s₀ : ScannerState} (s : ScannerState) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipDocEndWhitespace s fuel) := by
  induction fuel generalizing s with
  | zero => simp only [skipDocEndWhitespace]; exact h
  | succ n ih =>
    simp only [skipDocEndWhitespace]
    split  -- peek?
    · split  -- c == ' ' || c == '\t'
      · exact ih _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectDirectiveNameLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (name : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectDirectiveNameLoop s name fuel).2 := by
  induction fuel generalizing s name with
  | zero => exact h
  | succ n ih =>
    simp only [collectDirectiveNameLoop]
    split  -- peek?
    · split  -- !isWhiteSpaceBool && !isLineBreakBool
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

-- Additional simple loop BoundInv lemmas

theorem collectAnchorNameLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (name : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectAnchorNameLoop s name fuel).2 := by
  induction fuel generalizing s name with
  | zero => exact h
  | succ n ih =>
    simp only [collectAnchorNameLoop]
    split  -- peek?
    · split  -- condition
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectVersionMajorLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (major : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectVersionMajorLoop s major fuel).2 := by
  induction fuel generalizing s major with
  | zero => simp only [collectVersionMajorLoop]; exact h
  | succ n ih =>
    simp only [collectVersionMajorLoop]
    split  -- some '.'
    · exact advance_BoundInv s h hend
    · split  -- c.isDigit
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectVersionMinorLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (minor : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectVersionMinorLoop s minor fuel).2 := by
  induction fuel generalizing s minor with
  | zero => simp only [collectVersionMinorLoop]; exact h
  | succ n ih =>
    simp only [collectVersionMinorLoop]
    split
    · split
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectTagHandleDirectiveLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (handle : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectTagHandleDirectiveLoop s handle fuel).2 := by
  induction fuel generalizing s handle with
  | zero => simp only [collectTagHandleDirectiveLoop]; exact h
  | succ n ih =>
    simp only [collectTagHandleDirectiveLoop]
    split
    · split
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectTagPrefixLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (pfx : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectTagPrefixLoop s pfx fuel).2 := by
  induction fuel generalizing s pfx with
  | zero => simp only [collectTagPrefixLoop]; exact h
  | succ n ih =>
    simp only [collectTagPrefixLoop]
    split
    · split
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectVerbatimTagLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (uri : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectVerbatimTagLoop s uri fuel).2.2 := by
  induction fuel generalizing s uri with
  | zero => simp only [collectVerbatimTagLoop]; exact h
  | succ n ih =>
    simp only [collectVerbatimTagLoop]
    split  -- some '>'
    · exact advance_BoundInv s h hend
    · split  -- isUriCharBool
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectTagSuffixLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (suffix : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectTagSuffixLoop s suffix fuel).2 := by
  induction fuel generalizing s suffix with
  | zero => simp only [collectTagSuffixLoop]; exact h
  | succ n ih =>
    simp only [collectTagSuffixLoop]
    split
    · split
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectTagHandleLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (chars : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectTagHandleLoop s chars fuel).2.2 := by
  induction fuel generalizing s chars with
  | zero => simp only [collectTagHandleLoop]; exact h
  | succ n ih =>
    simp only [collectTagHandleLoop]
    split  -- some '!'
    · exact advance_BoundInv s h hend
    · split
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectHexDigitsLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (hex : String) (n : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectHexDigitsLoop s hex n).2 := by
  induction n generalizing s hex with
  | zero => simp only [collectHexDigitsLoop]; exact h
  | succ k ih =>
    simp only [collectHexDigitsLoop]
    split
    · split
      · exact ih _ _ (advance_BoundInv s h hend)
      · exact h
    · exact h

theorem collectLineContentLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (content : String) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectLineContentLoop s content fuel).2 := by
  induction fuel generalizing s content with
  | zero => simp only [collectLineContentLoop]; exact h
  | succ n ih =>
    simp only [collectLineContentLoop]
    split
    · split  -- isLineBreakBool
      · exact h
      · exact ih _ _ (advance_BoundInv s h hend)
    · exact h

theorem consumeExactSpaces_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (count : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (consumeExactSpaces s count).2 := by
  induction count generalizing s with
  | zero => simp only [consumeExactSpaces]; exact h
  | succ n ih =>
    simp only [consumeExactSpaces]
    split  -- peek? = some ' '
    · exact ih _ (advance_BoundInv s h hend)
    · exact h

theorem parseBlockHeaderLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (chomp : ChompStyle) (explicitOffset : Option Nat) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (parseBlockHeaderLoop s chomp explicitOffset fuel).2.2 := by
  -- Use suffices to avoid .2.2 blocking split
  suffices ∀ c' eo' s', parseBlockHeaderLoop s chomp explicitOffset fuel = (c', eo', s') →
      BoundInv s₀ s' by
    exact this _ _ _ rfl
  induction fuel generalizing s chomp explicitOffset with
  | zero =>
    intro c' eo' s' h_eq; simp only [parseBlockHeaderLoop] at h_eq
    simp only [Prod.mk.injEq] at h_eq; obtain ⟨_, _, rfl⟩ := h_eq; exact h
  | succ n ih =>
    intro c' eo' s' h_eq; simp only [parseBlockHeaderLoop] at h_eq
    split at h_eq
    · exact ih _ _ _ (advance_BoundInv s h hend) _ _ _ h_eq
    · exact ih _ _ _ (advance_BoundInv s h hend) _ _ _ h_eq
    · split at h_eq
      · exact ih _ _ _ (advance_BoundInv s h hend) _ _ _ h_eq
      · simp only [Prod.mk.injEq] at h_eq; obtain ⟨_, _, rfl⟩ := h_eq; exact h
    · simp only [Prod.mk.injEq] at h_eq; obtain ⟨_, _, rfl⟩ := h_eq; exact h

theorem skipBlankLinesLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (cnt : Nat) (fuel : Nat) (inputEnd : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipBlankLinesLoop s cnt fuel inputEnd).2 := by
  induction fuel generalizing s cnt with
  | zero => simp only [skipBlankLinesLoop]; exact h
  | succ n ih =>
    simp only [skipBlankLinesLoop]
    split  -- (skipSpaces s).peek? = some c
    · split  -- isLineBreakBool
      · exact ih _ _ (consumeNewline_BoundInv _ (skipSpaces_BoundInv s h hend) hend)
      · exact h
    · exact h

theorem skipTrailingSpaces_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (skipTrailingSpaces s fuel) := by
  induction fuel generalizing s with
  | zero => simp only [skipTrailingSpaces]; exact h
  | succ n ih =>
    simp only [skipTrailingSpaces]
    split
    · split
      · exact ih _ (advance_BoundInv s h hend)
      · exact h
    · exact h

-- Sub-scanner helper BoundInv lemmas

theorem scanBlockScalarSkipComment_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (scanBlockScalarSkipComment s) := by
  unfold scanBlockScalarSkipComment
  simp only []
  split  -- peek? = some '#'
  · split  -- peekBack? match
    <;> (split <;> first
      | (exact fieldUpdate_BoundInv _ _
          (collectCommentTextLoop_BoundInv s.advance "" _ (advance_BoundInv s h hend) hend)
          rfl rfl rfl)
      | exact h)
  · exact h

theorem scanBlockScalarConsumeNewline_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : scanBlockScalarConsumeNewline s = .ok s') :
    BoundInv s₀ s' := by
  unfold scanBlockScalarConsumeNewline at hok
  split at hok
  · split at hok
    · injection hok with hok; subst hok
      exact consumeNewline_BoundInv s h hend
    · split at hok
      · injection hok with hok; subst hok; exact h
      · cases hok
  · injection hok with hok; subst hok; exact h

theorem parseHexEscape_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (n : Nat) (ch : Char)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : parseHexEscape s n = .ok (ch, s')) :
    BoundInv s₀ s' := by
  simp only [parseHexEscape, bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok
  · cases hok
  · split at hok
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨_, rfl⟩ := hok
      exact collectHexDigitsLoop_BoundInv s "" n h hend
    · cases hok

set_option maxHeartbeats 6400000 in
theorem processEscape_BoundInv {s₀ : ScannerState} (s s' : ScannerState) (ch : Char)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : processEscape s = .ok (ch, s')) :
    BoundInv s₀ s' := by
  simp only [processEscape] at hok
  have h_adv := advance_BoundInv s h hend
  split at hok
  · cases hok
  · try dsimp only [] at hok
    repeat split at hok
    all_goals first
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
         obtain ⟨_, rfl⟩ := hok; exact h_adv)
      | exact parseHexEscape_BoundInv _ _ _ _ h_adv hend hok
      | contradiction

theorem foldQuotedNewlinesLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (emptyCount : Nat) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (foldQuotedNewlinesLoop s emptyCount fuel).1 := by
  induction fuel generalizing s emptyCount with
  | zero => simp only [foldQuotedNewlinesLoop]; exact h
  | succ n ih =>
    simp only [foldQuotedNewlinesLoop]
    split
    · split  -- isLineBreakBool
      · exact ih _ _ (consumeNewline_BoundInv _ (skipSpaces_BoundInv s h hend) hend)
      · exact h
    · exact h

set_option maxHeartbeats 3200000 in
theorem foldQuotedNewlines_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (content : String)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : foldQuotedNewlines s = .ok (content, s')) :
    BoundInv s₀ s' := by
  -- The final state is always skipWhitespace(skipSpaces(loop(consumeNewline s).1))
  let s₁ := consumeNewline s
  let p := foldQuotedNewlinesLoop s₁ 0 (s.inputEnd - s₁.offset + 1)
  let s₂ := skipSpaces p.1
  let s₃ := skipWhitespace s₂
  have h₁ := consumeNewline_BoundInv s h hend
  have h₂ := foldQuotedNewlinesLoop_BoundInv s₁ 0
    (s.inputEnd - s₁.offset + 1) h₁ hend
  have h₃ := skipSpaces_BoundInv _ h₂ hend
  have h₄ : BoundInv s₀ s₃ := skipWhitespace_BoundInv _ h₃ hend
  suffices s' = s₃ by rw [this]; exact h₄
  unfold foldQuotedNewlines at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  try dsimp only [] at hok
  repeat split at hok
  all_goals (try dsimp only [] at hok)
  all_goals first
    | contradiction
    | (injection hok with hok; exact (Prod.mk.inj hok).2)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at hok; exact hok.2)
    | (split at hok <;>
       (simp only [Except.ok.injEq, Prod.mk.injEq] at hok; obtain ⟨_, rfl⟩ := hok; rfl))

-- Structural scanner BoundInv lemmas

set_option maxHeartbeats 1600000 in
theorem scanDocumentStart_BoundInv (s : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize) :
    BoundInv s (scanDocumentStart s) := by
  have h_unw := unwindIndents_BoundInv s (-1) h
  have h_kd : BoundInv s { unwindIndents s (-1) with simpleKey := { possible := false } } :=
    fieldUpdate_BoundInv _ _ h_unw rfl rfl rfl
  have h_em := emit_BoundInv _ .documentStart h_kd
  have h_adv := advanceN_BoundInv _ 3 h_em hend
  exact fieldUpdate_BoundInv _ _ h_adv rfl rfl rfl

set_option maxHeartbeats 3200000 in
theorem scanDocumentEnd_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanDocumentEnd s = .ok s') :
    BoundInv s s' := by
  -- scanDocumentEnd always returns `.ok result` where result is a fixed chain.
  -- The trailing validation doesn't affect the returned state.
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  -- After resolving do-notation, hok has guard + validation splits
  -- but the returned state is always the same
  have h_unw := unwindIndents_BoundInv s (-1) h
  have h_kd : BoundInv s { unwindIndents s (-1) with simpleKey := { possible := false } } :=
    fieldUpdate_BoundInv _ _ h_unw rfl rfl rfl
  have h_em := emit_BoundInv _ .documentEnd h_kd
  have h_adv := advanceN_BoundInv _ 3 h_em hend
  have h_res : BoundInv s { (unwindIndents s (-1) |> fun s => { s with simpleKey := { possible := false } }
    |>.emit .documentEnd |>.advanceN 3) with
    simpleKeyAllowed := true, allowDirectives := true,
    directivesPresent := false, definedAnchors := #[] } :=
    fieldUpdate_BoundInv _ _ h_adv rfl rfl rfl
  repeat split at hok
  all_goals (try dsimp only [] at hok)
  all_goals first
    | contradiction
    | (injection hok with hok; subst hok; exact h_res)
    | (simp only [Except.ok.injEq] at hok; subst hok; exact h_res)
    | (split at hok <;> first
       | contradiction
       | (injection hok with hok; subst hok; exact h_res)
       | (simp only [Except.ok.injEq] at hok; subst hok; exact h_res)
       | (split at hok <;> first
          | contradiction
          | (injection hok with hok; subst hok; exact h_res)))

set_option maxHeartbeats 3200000 in
theorem scanYamlDirective_BoundInv {s₀ : ScannerState} (s s_ws s' : ScannerState)
    (startPos : YamlPos)
    (h : BoundInv s₀ s_ws) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : scanYamlDirective s s_ws startPos = .ok s') :
    BoundInv s₀ s' := by
  -- scanYamlDirective returns { emitAt (skipWhitespace (collectVersionMinorLoop ...)) ... with ... }
  -- The validation (match peek?) doesn't affect the returned state.
  unfold scanYamlDirective at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  let s_maj := (collectVersionMajorLoop s_ws "" (s.inputEnd - s_ws.offset)).2
  let s_min := (collectVersionMinorLoop s_maj "" (s.inputEnd - s_maj.offset)).2
  let s_val := skipWhitespace s_min
  have h_maj := collectVersionMajorLoop_BoundInv s_ws ""
    (s.inputEnd - s_ws.offset) h hend
  have h_min := collectVersionMinorLoop_BoundInv s_maj ""
    (s.inputEnd - s_maj.offset) h_maj hend
  have h_sw := skipWhitespace_BoundInv _ h_min hend
  have h_res : BoundInv s₀ { s_val.emitAt startPos (.versionDirective (collectVersionMajorLoop s_ws "" (s.inputEnd - s_ws.offset)).1.toNat! (collectVersionMinorLoop s_maj "" (s.inputEnd - s_maj.offset)).1.toNat!) with
    seenYamlDirective := true, directivesPresent := true } :=
    ⟨h_sw.offset_le, h_sw.inputEnd_eq, h_sw.input_eq, h_sw.isValid⟩
  repeat split at hok
  all_goals (try dsimp only [] at hok)
  all_goals first
    | contradiction
    | (injection hok with hok; subst hok; exact h_res)
    | (simp only [Except.ok.injEq] at hok; subst hok; exact h_res)
    | (split at hok <;> first
       | contradiction
       | (injection hok with hok; subst hok; exact h_res)
       | (simp only [Except.ok.injEq] at hok; subst hok; exact h_res)
       | (split at hok <;> first
          | contradiction
          | (injection hok with hok; subst hok; exact h_res)))

set_option maxHeartbeats 3200000 in
theorem scanTagDirective_BoundInv {s₀ : ScannerState} (s s_ws s' : ScannerState)
    (startPos : YamlPos)
    (h : BoundInv s₀ s_ws) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : scanTagDirective s s_ws startPos = .ok s') :
    BoundInv s₀ s' := by
  -- scanTagDirective returns { emitAt (skipWhitespace (collectTagPrefixLoop ...)) ... with ... }
  unfold scanTagDirective at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  let s_hnd := (collectTagHandleDirectiveLoop s_ws "" (s.inputEnd - s_ws.offset)).2
  let s_ws2 := skipWhitespace s_hnd
  let s_pfx := (collectTagPrefixLoop s_ws2 "" (s.inputEnd - s_ws2.offset)).2
  let s_val := skipWhitespace s_pfx
  have h_hnd := collectTagHandleDirectiveLoop_BoundInv s_ws ""
    (s.inputEnd - s_ws.offset) h hend
  have h_ws2 := skipWhitespace_BoundInv _ h_hnd hend
  have h_pfx := collectTagPrefixLoop_BoundInv s_ws2 ""
    (s.inputEnd - s_ws2.offset) h_ws2 hend
  have h_sw := skipWhitespace_BoundInv _ h_pfx hend
  have h_res : BoundInv s₀ { s_val.emitAt startPos (.tagDirective (collectTagHandleDirectiveLoop s_ws "" (s.inputEnd - s_ws.offset)).1 (collectTagPrefixLoop s_ws2 "" (s.inputEnd - s_ws2.offset)).1) with directivesPresent := true } :=
    ⟨h_sw.offset_le, h_sw.inputEnd_eq, h_sw.input_eq, h_sw.isValid⟩
  repeat split at hok
  all_goals (try dsimp only [] at hok)
  all_goals first
    | contradiction
    | (injection hok with hok; subst hok; exact h_res)
    | (simp only [Except.ok.injEq] at hok; subst hok; exact h_res)
    | (split at hok <;> first
       | contradiction
       | (injection hok with hok; subst hok; exact h_res)
       | (simp only [Except.ok.injEq] at hok; subst hok; exact h_res)
       | (split at hok <;> first
          | contradiction
          | (injection hok with hok; subst hok; exact h_res)))

set_option maxHeartbeats 3200000 in
theorem scanDirective_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanDirective s = .ok s') :
    BoundInv s s' := by
  -- scanDirective: if YAML → scanYamlDirective → skipToEndOfLine, if TAG → scanTagDirective → skipToEndOfLine
  unfold scanDirective at hok
  split at hok  -- !allowDirectives
  · cases hok
  · dsimp only [] at hok
    have h_adv := advance_BoundInv s h hend
    have h_name := collectDirectiveNameLoop_BoundInv s.advance ""
      (s.inputEnd - s.advance.offset) h_adv hend
    have h_ws := skipWhitespace_BoundInv _ h_name hend
    split at hok  -- name == "YAML"
    · split at hok  -- match scanYamlDirective
      · next s'' heq =>
        have h_yaml := scanYamlDirective_BoundInv s _ _ _ h_ws hend heq
        cases hok
        exact skipToEndOfLine_BoundInv _ h_yaml hend
      · cases hok
    · split at hok  -- name == "TAG"
      · split at hok  -- match scanTagDirective
        · next s'' heq =>
          have h_tag := scanTagDirective_BoundInv s _ _ _ h_ws hend heq
          cases hok
          exact skipToEndOfLine_BoundInv _ h_tag hend
        · cases hok
      · cases hok; exact skipToEndOfLine_BoundInv _ h_ws hend

-- Content scanner BoundInv lemmas (all proven — complex loops)

theorem scanAnchorOrAlias_BoundInv (s s' : ScannerState) (isAnchor : Bool)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    BoundInv s s' := by
  unfold scanAnchorOrAlias at hok
  dsimp only [] at hok  -- inline let bindings
  split at hok  -- name.isEmpty
  · cases hok  -- error
  · simp only [Except.ok.injEq] at hok; subst hok
    have h_adv := advance_BoundInv s h hend
    have h_name := collectAnchorNameLoop_BoundInv s.advance ""
      (s.inputEnd - s.advance.offset) h_adv hend
    exact ⟨h_name.offset_le, h_name.inputEnd_eq, h_name.input_eq, h_name.isValid⟩

-- Tag sub-scanner helpers

theorem scanVerbatimTag_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (startPos : YamlPos)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : scanVerbatimTag s startPos = .ok s') :
    BoundInv s₀ s' := by
  simp only [scanVerbatimTag] at hok
  split at hok  -- !foundClose
  · cases hok
  · split at hok  -- uri.isEmpty
    · cases hok
    · simp only [Except.ok.injEq] at hok; subst hok
      exact emitAt_BoundInv _ _ _
        (collectVerbatimTagLoop_BoundInv _ "" _ (advance_BoundInv s h hend) hend)

theorem scanSecondaryTag_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (startPos : YamlPos)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (scanSecondaryTag s startPos) := by
  unfold scanSecondaryTag
  exact emitAt_BoundInv _ _ _
    (collectTagSuffixLoop_BoundInv _ "" _ (advance_BoundInv s h hend) hend)

theorem scanNamedTag_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (startPos : YamlPos) (inputEnd : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (scanNamedTag s startPos inputEnd) := by
  simp only [scanNamedTag]
  split  -- if foundBang
  · -- foundBang = true: collectTagHandleLoop → collectTagSuffixLoop → emitAt
    exact emitAt_BoundInv _ _ _
      (collectTagSuffixLoop_BoundInv _ "" _
        (collectTagHandleLoop_BoundInv _ "" _ h hend) hend)
  · -- foundBang = false: emitAt on collectTagHandleLoop state
    exact emitAt_BoundInv _ _ _
      (collectTagHandleLoop_BoundInv _ "" _ h hend)

theorem scanTag_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanTag s = .ok s') :
    BoundInv s s' := by
  unfold scanTag at hok
  simp only [bind, Except.bind, pure, Pure.pure, Bind.bind, Except.pure] at hok
  have h_adv := advance_BoundInv s h hend
  split at hok  -- peek? match
  · -- some '<' → scanVerbatimTag
    split at hok  -- bind on scanVerbatimTag
    · cases hok
    · next v heq =>
      simp only [Except.ok.injEq] at hok; subst hok
      exact fieldUpdate_BoundInv _ _
        (scanVerbatimTag_BoundInv s.advance v s.currentPos h_adv hend heq) rfl rfl rfl
  · -- some '!' → scanSecondaryTag
    simp only [Except.ok.injEq] at hok; subst hok
    exact fieldUpdate_BoundInv _ _
      (scanSecondaryTag_BoundInv s.advance s.currentPos h_adv hend) rfl rfl rfl
  · -- _ → scanNamedTag
    simp only [Except.ok.injEq] at hok; subst hok
    exact fieldUpdate_BoundInv _ _
      (scanNamedTag_BoundInv s.advance s.currentPos s.inputEnd h_adv hend) rfl rfl rfl

-- Block scalar loop BoundInv

set_option maxHeartbeats 6400000 in
theorem collectBlockScalarLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (rawContent : String) (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).2 := by
  induction fuel generalizing s rawContent with
  | zero => simp only [collectBlockScalarLoop]; exact h
  | succ n ih =>
    simp only [collectBlockScalarLoop]
    split  -- atDocumentBoundary
    · exact h
    · have h_ces := consumeExactSpaces_BoundInv s contentIndent h hend
      split  -- peek? of s_after_spaces
      · exact h_ces
      · split  -- isLineBreakBool
        · exact ih _ _ (consumeNewline_BoundInv _ h_ces hend)
        · split  -- spacesConsumed < contentIndent
          · exact h
          · have h_lcl := collectLineContentLoop_BoundInv _ ""
              (inputEnd - (consumeExactSpaces s contentIndent).2.offset + 1) h_ces hend
            split  -- peek? of s_after_line
            · split  -- isLineBreakBool
              · exact ih _ _ (consumeNewline_BoundInv _ h_lcl hend)
              · exact ih _ _ h_lcl
            · exact h_lcl

set_option maxHeartbeats 6400000 in
theorem scanBlockScalarBody_BoundInv {s₀ : ScannerState} (s_orig s_after_newline s' : ScannerState)
    (chomp : ChompStyle) (explicitOffset : Option Nat) (isLiteral : Bool) (startPos : YamlPos)
    (h : BoundInv s₀ s_after_newline) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : scanBlockScalarBody s_orig s_after_newline chomp explicitOffset isLiteral startPos = .ok s') :
    BoundInv s₀ s' := by
  unfold scanBlockScalarBody at hok
  cases explicitOffset with
  | some m =>
    dsimp only [] at hok
    simp only [Except.ok.injEq] at hok; subst hok
    exact ⟨(collectBlockScalarLoop_BoundInv s_after_newline "" _ _ _ h hend).offset_le,
           (collectBlockScalarLoop_BoundInv s_after_newline "" _ _ _ h hend).inputEnd_eq,
           (collectBlockScalarLoop_BoundInv s_after_newline "" _ _ _ h hend).input_eq,
           (collectBlockScalarLoop_BoundInv s_after_newline "" _ _ _ h hend).isValid⟩
  | none =>
    dsimp only [] at hok
    split at hok  -- match autoDetectErr?
    · cases hok  -- error
    · simp only [Except.ok.injEq] at hok; subst hok
      exact ⟨(collectBlockScalarLoop_BoundInv s_after_newline "" _ _ _ h hend).offset_le,
             (collectBlockScalarLoop_BoundInv s_after_newline "" _ _ _ h hend).inputEnd_eq,
             (collectBlockScalarLoop_BoundInv s_after_newline "" _ _ _ h hend).input_eq,
             (collectBlockScalarLoop_BoundInv s_after_newline "" _ _ _ h hend).isValid⟩

set_option maxHeartbeats 3200000 in
theorem scanBlockScalar_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanBlockScalar s = .ok s') :
    BoundInv s s' := by
  unfold scanBlockScalar at hok
  dsimp only [] at hok
  split at hok  -- match scanBlockScalarConsumeNewline
  · cases hok
  · next s_an heq =>
    have h_adv := advance_BoundInv s h hend
    have h_hdr := parseBlockHeaderLoop_BoundInv s.advance .clip none 2 h_adv hend
    have h_ws := skipWhitespace_BoundInv _ h_hdr hend
    have h_sc := scanBlockScalarSkipComment_BoundInv _ h_ws hend
    have h_cn := scanBlockScalarConsumeNewline_BoundInv _ s_an h_sc hend heq
    exact scanBlockScalarBody_BoundInv s s_an _ _ _ _ _ h_cn hend hok

-- Complex loop BoundInv lemmas

set_option maxHeartbeats 6400000 in
theorem collectDoubleQuotedLoop_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (content resultContent : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
    (currentIndent : Int) (inputEnd : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd
           = .ok (resultContent, s')) :
    BoundInv s₀ s' := by
  induction fuel generalizing s content with
  | zero => simp only [collectDoubleQuotedLoop] at hok; cases hok
  | succ n ih =>
    simp only [collectDoubleQuotedLoop] at hok
    split at hok  -- peek?
    · cases hok  -- none
    · -- some '"': closing quote
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨_, rfl⟩ := hok
      exact advance_BoundInv s h hend
    · -- some '\\': escape
      try dsimp only [] at hok
      split at hok  -- s.advance.peek?
      · -- some c
        split at hok  -- isLineBreakBool
        · -- escaped line break: no bind, just let + recurse
          try dsimp only [] at hok
          exact ih _ _ (skipWhitespace_BoundInv _
            (consumeNewline_BoundInv _ (advance_BoundInv s h hend) hend) hend) hok
        · -- regular escape: do with processEscape ←
          simp only [bind, Except.bind, pure, Pure.pure, Bind.bind, Except.pure] at hok
          split at hok  -- processEscape result
          · cases hok
          · next p heq =>
            try dsimp only [] at hok
            exact ih _ _ (processEscape_BoundInv _ _ p.1
              (advance_BoundInv s h hend) hend heq) hok
      · cases hok  -- none: error
    · -- some c (not '"', not '\\')
      split at hok  -- isLineBreakBool
      · -- line break: do with foldQuotedNewlines ←
        simp only [bind, Except.bind, pure, Pure.pure, Bind.bind, Except.pure] at hok
        split at hok  -- foldQuotedNewlines result
        · cases hok
        · next p heq =>
          try dsimp only [] at hok
          split at hok  -- atDocumentStart/End
          · cases hok
          · split at hok  -- underIndented
            · cases hok
            · try dsimp only [] at hok
              exact ih _ _ (foldQuotedNewlines_BoundInv _ p.2 _ h hend heq) hok
      · split at hok  -- !isNbJsonBool
        · cases hok
        · try dsimp only [] at hok
          exact ih _ _ (advance_BoundInv s h hend) hok

set_option maxHeartbeats 6400000 in
theorem collectSingleQuotedLoop_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (content resultContent : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
    (currentIndent : Int) (inputEnd : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd
           = .ok (resultContent, s')) :
    BoundInv s₀ s' := by
  induction fuel generalizing s content with
  | zero => simp only [collectSingleQuotedLoop] at hok; cases hok
  | succ n ih =>
    simp only [collectSingleQuotedLoop] at hok
    split at hok  -- peek?
    · cases hok  -- none
    · -- some '\''
      try dsimp only [] at hok
      split at hok  -- s.advance.peek?
      · -- some '\'' (escaped quote)
        try dsimp only [] at hok
        exact ih _ _ (advance_BoundInv _ (advance_BoundInv s h hend) hend) hok
      · -- closing quote
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨_, rfl⟩ := hok
        exact advance_BoundInv s h hend
    · -- some c (not '\'')
      split at hok  -- isLineBreakBool
      · -- line break: do with foldQuotedNewlines ←
        simp only [bind, Except.bind, pure, Pure.pure, Bind.bind, Except.pure] at hok
        split at hok  -- foldQuotedNewlines result
        · cases hok
        · next p heq =>
          try dsimp only [] at hok
          split at hok  -- atDocumentStart/End
          · cases hok
          · split at hok  -- underIndented
            · cases hok
            · try dsimp only [] at hok
              exact ih _ _ (foldQuotedNewlines_BoundInv _ p.2 _ h hend heq) hok
      · split at hok  -- !isNbJsonBool
        · cases hok
        · try dsimp only [] at hok
          exact ih _ _ (advance_BoundInv s h hend) hok

set_option maxHeartbeats 3200000 in
theorem scanDoubleQuoted_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanDoubleQuoted s = .ok s') :
    BoundInv s s' := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind, pure, Pure.pure, Bind.bind, Except.pure] at hok
  have h_adv := advance_BoundInv s h hend
  split at hok  -- bind on collectDoubleQuotedLoop
  · cases hok
  · rename_i p heq
    have h_dq := collectDoubleQuotedLoop_BoundInv _ _ _ _ _ _ _ _ _ h_adv hend heq
    split at hok  -- if s.inFlow = false
    · -- validation needed
      revert hok
      generalize validateTrailingContent p.2 s.inputEnd = val
      intro hok
      cases val with
      | error e => simp at hok
      | ok u =>
        simp only [Except.ok.injEq] at hok; subst hok
        exact ⟨h_dq.offset_le, h_dq.inputEnd_eq, h_dq.input_eq, h_dq.isValid⟩
    · -- no validation
      simp only [Except.ok.injEq] at hok; subst hok
      exact ⟨h_dq.offset_le, h_dq.inputEnd_eq, h_dq.input_eq, h_dq.isValid⟩

set_option maxHeartbeats 3200000 in
theorem scanSingleQuoted_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanSingleQuoted s = .ok s') :
    BoundInv s s' := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind, pure, Pure.pure, Bind.bind, Except.pure] at hok
  have h_adv := advance_BoundInv s h hend
  split at hok  -- bind on collectSingleQuotedLoop
  · cases hok
  · rename_i p heq
    have h_sq := collectSingleQuotedLoop_BoundInv _ _ _ _ _ _ _ _ _ h_adv hend heq
    split at hok
    · revert hok
      generalize validateTrailingContent p.2 s.inputEnd = val
      intro hok
      cases val with
      | error e => simp at hok
      | ok u =>
        simp only [Except.ok.injEq] at hok; subst hok
        exact ⟨h_sq.offset_le, h_sq.inputEnd_eq, h_sq.input_eq, h_sq.isValid⟩
    · simp only [Except.ok.injEq] at hok; subst hok
      exact ⟨h_sq.offset_le, h_sq.inputEnd_eq, h_sq.input_eq, h_sq.isValid⟩

-- Plain scalar loop BoundInv

theorem collectPlainScalar_handleBlockLineBreak_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (content content' : String) (contentIndent : Nat) (inputEnd : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd = some (content', s')) :
    BoundInv s₀ s' := by
  unfold collectPlainScalar_handleBlockLineBreak at hok
  try dsimp only [] at hok
  have h_cn := consumeNewline_BoundInv s h hend
  have h_bl := skipBlankLinesLoop_BoundInv (consumeNewline s) 0
    (inputEnd - (consumeNewline s).offset + 1) inputEnd h_cn hend
  have h_sp := skipSpaces_BoundInv _ h_bl hend
  split at hok
  · cases hok
  · split at hok
    · cases hok
    · simp only [Option.some.injEq, Prod.mk.injEq] at hok
      obtain ⟨_, rfl⟩ := hok
      exact h_sp

theorem terminates?_state_eq (c : Char) (s : ScannerState)
    (content spaces : String) (inFlow : Bool) (result : PlainScalarResult)
    (h : collectPlainScalar_terminates? c s content spaces inFlow = some result) :
    result.state = s := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · injection h with h; cases h; rfl
  · split at h
    · simp only [] at h
      split at h
      · split at h
        · injection h with h; cases h; rfl
        · contradiction
      · split at h
        · injection h with h; cases h; rfl
        · contradiction
    · split at h
      · injection h with h; cases h; rfl
      · split at h
        · injection h with h; cases h; rfl
        · contradiction

set_option maxHeartbeats 12800000 in
theorem collectPlainScalarLoop_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (content spaces : String) (fuel : Nat) (inFlow : Bool) (contentIndent : Nat) (inputEnd : Nat)
    (r : PlainScalarResult)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd = .ok r) :
    BoundInv s₀ r.state := by
  induction fuel generalizing s content spaces r with
  | zero =>
    simp only [collectPlainScalarLoop] at hok
    simp only [Except.ok.injEq] at hok; subst hok; exact h
  | succ n ih =>
    simp only [collectPlainScalarLoop] at hok
    split at hok  -- peek?
    · -- none
      simp only [Except.ok.injEq] at hok; subst hok; exact h
    · -- some c
      split at hok  -- collectPlainScalar_terminates?
      · -- some result: terminates
        next result heq_term =>
        simp only [Except.ok.injEq] at hok; subst hok
        rw [terminates?_state_eq _ _ _ _ _ _ heq_term]; exact h
      · -- none: continue scanning
        split at hok  -- isLineBreakBool
        · -- line break
          split at hok  -- inFlow
          · -- inFlow = true: do with foldQuotedNewlines ←
            simp only [bind, Except.bind, pure, Pure.pure, Bind.bind, Except.pure] at hok
            split at hok  -- foldQuotedNewlines result
            · cases hok
            · rename_i fld s_fld heq_fold
              try dsimp only [] at hok
              split at hok  -- peek? = some '#'
              · simp only [Except.ok.injEq] at hok; subst hok; exact h
              · try dsimp only [] at hok
                split at hok  -- match recursive call
                · next r' heq_rec =>
                  try dsimp only [] at hok
                  split at hok
                  · simp only [Except.ok.injEq] at hok; subst hok; exact h
                  · simp only [Except.ok.injEq] at hok; subst hok
                    exact ih _ _ _ _ (foldQuotedNewlines_BoundInv _ s_fld.2 _ h hend heq_fold) heq_rec
                · cases hok
          · -- inFlow = false: handleBlockLineBreak
            try dsimp only [] at hok
            split at hok  -- handleBlockLineBreak
            · -- none: terminate
              simp only [Except.ok.injEq] at hok; subst hok; exact h
            · -- some (content', s')
              rename_i c_blk s_blk heq_blk
              try dsimp only [] at hok
              split at hok  -- peek? = some '#'
              · simp only [Except.ok.injEq] at hok; subst hok; exact h
              · try dsimp only [] at hok
                split at hok  -- match recursive call
                · next r' heq_rec =>
                  try dsimp only [] at hok
                  split at hok
                  · simp only [Except.ok.injEq] at hok; subst hok; exact h
                  · simp only [Except.ok.injEq] at hok; subst hok
                    exact ih _ _ _ _
                      (collectPlainScalar_handleBlockLineBreak_BoundInv _ _ _ _ _ _ h hend heq_blk)
                      heq_rec
                · cases hok
        · split at hok  -- isWhiteSpaceBool
          · exact ih _ _ _ _ (advance_BoundInv s h hend) hok
          · split at hok  -- !isPlainSafeBool
            · simp only [Except.ok.injEq] at hok; subst hok; exact h
            · try dsimp only [] at hok
              exact ih _ _ _ _ (advance_BoundInv s h hend) hok

set_option maxHeartbeats 3200000 in
theorem scanPlainScalar_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanPlainScalar s = .ok s') :
    BoundInv s s' := by
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind, pure, Pure.pure, Bind.bind, Except.pure] at hok
  split at hok  -- bind on collectPlainScalarLoop
  · cases hok
  · next r heq =>
    try dsimp only [] at hok
    simp only [Except.ok.injEq] at hok; subst hok
    exact ⟨(collectPlainScalarLoop_BoundInv _ _ _ _ _ _ _ _ h hend heq).offset_le,
           (collectPlainScalarLoop_BoundInv _ _ _ _ _ _ _ _ h hend heq).inputEnd_eq,
           (collectPlainScalarLoop_BoundInv _ _ _ _ _ _ _ _ h hend heq).input_eq,
           (collectPlainScalarLoop_BoundInv _ _ _ _ _ _ _ _ h hend heq).isValid⟩

/-! ## §6  Dispatch-Level BoundInv Preservation -/

-- Preprocess preserves BoundInv.
-- Chains: skipToContent → maybe unwindIndents → saveSimpleKey → peek?
-- All sub-operations preserve BoundInv (proven in §5b).
-- The do-notation desugaring creates join points that require careful handling.
theorem preprocess_preserves_bound (s : ScannerState) (sp : ScannerState) (c : Char)
    (h_bi : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanNextToken_preprocess s = .ok (some (sp, c))) :
    BoundInv s sp := by
  simp only [scanNextToken_preprocess, bind, Except.bind, pure, Pure.pure,
    Bind.bind, Except.pure] at hok
  -- Split on skipToContent result
  split at hok
  · cases hok  -- error
  · rename_i s1 h_stc
    have h_bi1 := skipToContent_BoundInv s s1 h_bi hend h_stc
    -- After skipToContent:
    --   if !hasMore → none, conditional unwind → error check → saveSimpleKey → peek?
    -- Split on !hasMore
    split at hok
    · cases hok  -- none ≠ some
    · -- hasMore, split on unwind condition (!inFlow && needIndentCheck)
      split at hok
      · -- unwind branch: s2 = { unwindIndents s1 col with needIndentCheck := false }
        have h_uw := unwindIndents_BoundInv s1 s1.col h_bi1
        have h_bi2 : BoundInv s { unwindIndents s1 s1.col with needIndentCheck := false } :=
          ⟨h_uw.offset_le, h_uw.inputEnd_eq, h_uw.input_eq, h_uw.isValid⟩
        -- Split on error check (indents.size < savedIndentSize && ...)
        split at hok
        · cases hok  -- error
        · -- saveSimpleKey + peek?
          split at hok
          · cases hok  -- none ≠ some
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact saveSimpleKey_BoundInv _ h_bi2
      · -- no-unwind branch: s2 = s1
        split at hok
        · cases hok  -- error
        · split at hok
          · cases hok  -- none ≠ some
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact saveSimpleKey_BoundInv _ h_bi1

-- Structural dispatch preserves BoundInv.
-- Dispatches to scanDocumentStart, scanDocumentEnd, or scanDirective.
theorem dispatchStructural_preserves_bound (s sp s' : ScannerState) (c : Char)
    (h_bi : BoundInv s sp) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanNextToken_dispatchStructural sp c = .ok (some s')) :
    BoundInv s s' := by
  have h_refl := BoundInv.refl sp h_bi.offset_le h_bi.isValid
  have h_hend : sp.inputEnd = sp.input.utf8ByteSize := by
    rw [h_bi.inputEnd_eq, h_bi.input_eq]; exact hend
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure, Bind.bind] at hok
  -- Step through each if/match in sequence
  -- 1. if s.inFlow && s.currentIndent >= 0 && col <= currentIndent
  split at hok
  · -- flow indent check true → if c != ']' && c != '}'
    split at hok
    · cases hok  -- error
    · -- c is ']' or '}', fall through
      -- 2. if col == 0 && inFlow && (docStart || docEnd)
      split at hok
      · cases hok  -- error
      · -- 3. if col == 0 && atDocumentStart
        split at hok
        · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
          exact BoundInv.trans h_bi (scanDocumentStart_BoundInv sp h_refl h_hend)
        · -- 4. if col == 0 && atDocumentEnd
          split at hok
          · -- scanDocumentEnd bind
            split at hok
            · cases hok  -- error from scanDocumentEnd
            · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
              exact BoundInv.trans h_bi (scanDocumentEnd_BoundInv sp _ h_refl h_hend ‹_›)
          · -- 5. if c == '%' && col == 0
            split at hok
            · split at hok
              · cases hok  -- error from scanDirective
              · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                exact BoundInv.trans h_bi (scanDirective_BoundInv sp _ h_refl h_hend ‹_›)
            · cases hok  -- return none
  · -- flow indent check false
    split at hok
    · cases hok  -- error
    · split at hok
      · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
        exact BoundInv.trans h_bi (scanDocumentStart_BoundInv sp h_refl h_hend)
      · split at hok
        · split at hok
          · cases hok
          · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
            exact BoundInv.trans h_bi (scanDocumentEnd_BoundInv sp _ h_refl h_hend ‹_›)
        · split at hok
          · split at hok
            · cases hok
            · simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
              exact BoundInv.trans h_bi (scanDirective_BoundInv sp _ h_refl h_hend ‹_›)
          · cases hok  -- return none

-- Content dispatch preserves BoundInv.
-- Dispatches to scanAnchorOrAlias, scanTag, scanBlockScalar,
-- scanDoubleQuoted, scanSingleQuoted, scanPlainScalar.
theorem dispatchContent_preserves_bound (s sp s' : ScannerState) (c : Char)
    (h_bi : BoundInv s sp) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanNextToken_dispatchContent sp c = .ok s') :
    BoundInv s s' := by
  have h_refl := BoundInv.refl sp h_bi.offset_le h_bi.isValid
  have h_hend : sp.inputEnd = sp.input.utf8ByteSize := by
    rw [h_bi.inputEnd_eq, h_bi.input_eq]; exact hend
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Pure.pure, Bind.bind, Except.pure] at hok
  -- Step through each if-branch for the character dispatch
  -- 1. c == '&' (anchor)
  split at hok
  · split at hok  -- bind on scanAnchorOrAlias
    · cases hok
    · rename_i s_a heq
      simp only [Except.ok.injEq] at hok; subst hok
      have h_aa := scanAnchorOrAlias_BoundInv sp _ true h_refl h_hend heq
      exact BoundInv.trans h_bi ⟨h_aa.offset_le, h_aa.inputEnd_eq, h_aa.input_eq, h_aa.isValid⟩
  -- 2. c == '*' (alias)
  · split at hok
    · split at hok  -- !definedAnchors check
      · cases hok  -- error: undefined alias
      · split at hok  -- bind on scanAnchorOrAlias
        · cases hok
        · rename_i s_a heq
          simp only [Except.ok.injEq] at hok; subst hok
          exact BoundInv.trans h_bi (scanAnchorOrAlias_BoundInv sp _ false h_refl h_hend heq)
    -- 3. c == '!' (tag)
    · split at hok
      · split at hok  -- bind on scanTag
        · cases hok
        · rename_i s_t heq
          simp only [Except.ok.injEq] at hok; subst hok
          exact BoundInv.trans h_bi (scanTag_BoundInv sp _ h_refl h_hend heq)
      -- 4. c == '|' || c == '>' (block scalar)
      · split at hok
        · split at hok  -- bind on scanBlockScalar
          · cases hok
          · rename_i s_bs heq
            simp only [Except.ok.injEq] at hok; subst hok
            exact BoundInv.trans h_bi (scanBlockScalar_BoundInv sp _ h_refl h_hend heq)
        -- 5. c == '"' (double quoted)
        · split at hok
          · split at hok  -- bind on scanDoubleQuoted
            · cases hok
            · rename_i s_dq heq
              -- simpleKey update: if s'.simpleKey.possible then { s' with ... } else s'
              split at hok
              · simp only [Except.ok.injEq] at hok; subst hok
                have h_dq := scanDoubleQuoted_BoundInv sp _ h_refl h_hend heq
                exact BoundInv.trans h_bi ⟨h_dq.offset_le, h_dq.inputEnd_eq, h_dq.input_eq, h_dq.isValid⟩
              · simp only [Except.ok.injEq] at hok; subst hok
                exact BoundInv.trans h_bi (scanDoubleQuoted_BoundInv sp _ h_refl h_hend heq)
          -- 6. c == '\'' (single quoted)
          · split at hok
            · split at hok  -- bind on scanSingleQuoted
              · cases hok
              · rename_i s_sq heq
                split at hok
                · simp only [Except.ok.injEq] at hok; subst hok
                  have h_sq := scanSingleQuoted_BoundInv sp _ h_refl h_hend heq
                  exact BoundInv.trans h_bi ⟨h_sq.offset_le, h_sq.inputEnd_eq, h_sq.input_eq, h_sq.isValid⟩
                · simp only [Except.ok.injEq] at hok; subst hok
                  exact BoundInv.trans h_bi (scanSingleQuoted_BoundInv sp _ h_refl h_hend heq)
            -- 7. canStartPlainScalar (plain scalar)
            · split at hok
              · split at hok  -- bind on scanPlainScalar
                · cases hok
                · rename_i s_ps heq
                  simp only [Except.ok.injEq] at hok; subst hok
                  exact BoundInv.trans h_bi (scanPlainScalar_BoundInv sp _ h_refl h_hend heq)
              -- 8. else: error (.unexpectedChar)
              · cases hok

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

The proof dispatches to per-dispatch preservation lemmas from §3-§6. -/
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
