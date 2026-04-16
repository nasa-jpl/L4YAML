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
  split  -- peek? = some '#'
  · -- some '#': comment path
    -- All paths return either s or { collectResult with comments := ... }
    -- Both preserve BoundInv (advance/collect only move forward, field update preserves bound fields)
    sorry
  · exact h

/-- `consumeNewline` preserves BoundInv.
    Handles `\n` (one advance) and `\r` + optional `\n` (one or two advances). -/
theorem consumeNewline_BoundInv {s₀ : ScannerState} (s : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize) :
    BoundInv s₀ (consumeNewline s) := by
  -- consumeNewline does at most 2 advance steps (CR+LF) and field updates (line/col/needIndentCheck).
  -- None of these modify input/inputEnd. advance_BoundInv handles each step.
  sorry

/-- `skipToContentWs` preserves BoundInv. -/
theorem skipToContentWs_BoundInv {s₀ : ScannerState} (s s' : ScannerState)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : skipToContentWs s = .ok s') :
    BoundInv s₀ s' := by
  -- All ok-result paths return skipSpaces s, skipWhitespace (skipSpaces s), or skipWhitespace s
  -- Each preserves BoundInv by composition of skipSpaces_BoundInv and skipWhitespace_BoundInv
  sorry

/-- `skipToContentLoop` preserves BoundInv. -/
theorem skipToContentLoop_BoundInv {s₀ : ScannerState} (s s' : ScannerState) (fuel : Nat)
    (h : BoundInv s₀ s) (hend : s₀.inputEnd = s₀.input.utf8ByteSize)
    (hok : skipToContentLoop s fuel = .ok s') :
    BoundInv s₀ s' := by
  -- Induction on fuel; each step chains skipToContentWs, skipToContentComment,
  -- consumeNewline, and (possibly) simpleKeyAllowed field update.
  -- All sub-steps preserve BoundInv.
  sorry

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
and content dispatchers.  Simple fuel-based loops are proven; complex
scanners with many sub-operations are sorry'd for now. -/

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

-- Structural scanner BoundInv lemmas

set_option maxHeartbeats 1600000 in
theorem scanDocumentStart_BoundInv (s : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize) :
    BoundInv s (scanDocumentStart s) := by
  -- scanDocumentStart is pure: unwindIndents → {simpleKey} → emit → advanceN 3 → {with ...}
  -- Chain BoundInv through each step with explicit type annotations
  -- to ensure fieldUpdate_BoundInv infers the correct intermediate states.
  have h_unw := unwindIndents_BoundInv s (-1) h
  have h_kd : BoundInv s { unwindIndents s (-1) with simpleKey := { possible := false } } :=
    fieldUpdate_BoundInv _ _ h_unw rfl rfl rfl
  have h_em := emit_BoundInv _ .documentStart h_kd
  have h_adv := advanceN_BoundInv _ 3 h_em hend
  exact fieldUpdate_BoundInv _ _ h_adv rfl rfl rfl

set_option maxHeartbeats 1600000 in
theorem scanDocumentEnd_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanDocumentEnd s = .ok s') :
    BoundInv s s' := by
  -- scanDocumentEnd returns `result` (same chain as scanDocumentStart).
  -- The match/if validation only gates error/ok, not the returned state.
  -- The do-notation creates join points that block split/simp only.
  -- We use full simp to reduce them, then manual splitting.
  simp only [scanDocumentEnd, bind, Except.bind, pure, Pure.pure, Except.pure,
    Bind.bind] at hok
  -- Use split to decompose the if/match structure
  split at hok
  · cases hok  -- throw → error
  · -- The do-notation join points (letFun/have) may block further splitting.
    -- Try using full simp to reduce everything, then omega for contradiction.
    -- Since the ok paths all return 'result' with the same bound chain,
    -- we extract s' = result by exhaustive case analysis.
    sorry

theorem scanDirective_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanDirective s = .ok s') :
    BoundInv s s' := by
  sorry

-- Content scanner BoundInv lemmas (all sorry'd — complex loops)

theorem scanAnchorOrAlias_BoundInv (s s' : ScannerState) (isAnchor : Bool)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    BoundInv s s' := by
  sorry

theorem scanTag_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanTag s = .ok s') :
    BoundInv s s' := by
  sorry

theorem scanBlockScalar_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanBlockScalar s = .ok s') :
    BoundInv s s' := by
  sorry

theorem scanDoubleQuoted_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanDoubleQuoted s = .ok s') :
    BoundInv s s' := by
  sorry

theorem scanSingleQuoted_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanSingleQuoted s = .ok s') :
    BoundInv s s' := by
  sorry

theorem scanPlainScalar_BoundInv (s s' : ScannerState)
    (h : BoundInv s s) (hend : s.inputEnd = s.input.utf8ByteSize)
    (hok : scanPlainScalar s = .ok s') :
    BoundInv s s' := by
  sorry

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
    -- The rest is pure: if !hasMore → none, else conditional unwind → error check → saveSimpleKey → peek?
    -- All paths either error (eliminated by hok : ... = .ok (some ...)) or return (saveSimpleKey s2, c)
    -- where s2 has BoundInv s s2 (via unwindIndents_BoundInv + fieldUpdate_BoundInv)
    sorry

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
  -- Macro: close branches that give scanDocumentStart/End/Directive or error/none
  -- Uses sorry fallback for any remaining branches from unresolved join points.
  repeat split at hok
  -- After exhaustive splitting, each goal's hok is one of:
  -- .error e = .ok (some s')    → cases hok
  -- .ok none = .ok (some s')    → cases hok (injection: none ≠ some)
  -- .ok (some X) = .ok (some s') → simp; subst; apply sub-scanner BoundInv
  all_goals first
    | cases hok
    | contradiction
    | (simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
       exact BoundInv.trans h_bi (scanDocumentStart_BoundInv sp h_refl h_hend))
    | (simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
       first
       | exact BoundInv.trans h_bi (scanDocumentEnd_BoundInv sp _ h_refl h_hend ‹_›)
       | exact BoundInv.trans h_bi (scanDirective_BoundInv sp _ h_refl h_hend ‹_›))
    | (-- Fallback for join-point residues: try simp to reduce, then subst
       simp at hok
       first
       | (obtain rfl := hok
          first
          | exact BoundInv.trans h_bi (scanDocumentStart_BoundInv sp h_refl h_hend)
          | exact BoundInv.trans h_bi (scanDocumentEnd_BoundInv sp _ h_refl h_hend ‹_›)
          | exact BoundInv.trans h_bi (scanDirective_BoundInv sp _ h_refl h_hend ‹_›))
       | (obtain ⟨rfl, rfl⟩ := hok
          first
          | exact BoundInv.trans h_bi (scanDocumentEnd_BoundInv sp _ h_refl h_hend ‹_›)
          | exact BoundInv.trans h_bi (scanDirective_BoundInv sp _ h_refl h_hend ‹_›))
       | sorry)

-- Content dispatch preserves BoundInv.
-- Dispatches to scanAnchorOrAlias, scanTag, scanBlockScalar,
-- scanDoubleQuoted, scanSingleQuoted, scanPlainScalar.
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
