/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.RoundTrip
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.ParserWellBehaved
open L4YAML.Proofs.ScalarCoupling

-- ═══ Scanner → Parser bridge: token structure for non-empty flow collections ═══

/-! ### Infrastructure for filtered token tracking (Sub-phase 4.4.G) -/

/-- `unwindIndents` is identity when the indent stack has at most 1 entry.
    This covers emitter output where `indents = #[]` (the default from `ScannerState.mk'`).
    `unwindIndentsLoop` checks `s.indents.size > 1` before unwinding; with size ≤ 1,
    the condition fails immediately and the state is returned unchanged. -/
theorem unwindIndents_noop_short_stack (s : ScannerState)
    (h_stack : s.indents.size ≤ 1) :
    unwindIndents s (-1) = s := by
  unfold unwindIndents
  unfold unwindIndentsLoop
  split
  · -- fuel = 0 case is impossible since fuel = s.indents.size ≤ 1
    rfl
  · -- fuel = fuel' + 1
    split
    · -- s.currentIndent > -1 && s.indents.size > 1
      exfalso
      rename_i h_cond
      simp only [Bool.and_eq_true, decide_eq_true_iff] at h_cond
      omega
    · rfl

/-- When a ScanChain starts from s₀ via scanFiltered, the token array equation.
    Combines `scanFiltered_of_chain_eq` with `unwindIndents` identity for emitter states. -/
theorem scanFiltered_tokens_eq_of_chain_short_stack
    (input : String) (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF')
    (h_chain : ScanChain s₀ n s_final)
    (h_eof : scanNextToken s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4)
    (h_stack : s_final.indents.size ≤ 1) :
    Scanner.scanFiltered input =
      .ok ((s_final.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder)) := by
  have h_eq := scanFiltered_of_chain_eq input s₀ s_final n h_s0 h_no_bom h_chain h_eof h_fl h_dp h_fuel
  rwa [unwindIndents_noop_short_stack s_final h_stack] at h_eq

/-- `ScanChain` token array monotonicity: tokens array size grows (non-strictly)
    through any scan chain. -/
theorem ScanChain_tokens_mono {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s') : s'.tokens.size ≥ s.tokens.size := by
  induction h_chain with
  | zero => exact Nat.le_refl _
  | step h_snt _h_rest ih => exact Nat.le_trans (ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt) ih

/-- Combined per-step prefix preservation and simpleKey invariant maintenance.

    **Precondition**: `n ≤ s.tokens.size` and the simpleKey condition
    `s.simpleKey.possible → s.simpleKey.tokenIndex ≥ n`, which says that
    the prefix index doesn't overlap the simpleKey placeholder position.
    Without this, `scanNextToken` may overwrite `tokens[tokenIndex]`
    (replacing `.placeholder` with `.key`), violating prefix preservation.

    **Precondition**: Uses `SimpleKeyAbove` to track both the current simpleKey
    and all stacked simpleKeys. This is necessary because flow close operations
    (`]`/`}`) restore a simpleKey from the stack, and without stack bounds,
    the restored `tokenIndex` could fall below `n`.

    **Conclusion**: Returns both prefix preservation and `SimpleKeyAbove s' n`,
    enabling straightforward induction in `ScanChain_preserves_raw_prefix`. -/
theorem scanNextToken_prefix_and_sk_inv (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : ScannerCorrectness.SimpleKeyAbove s n) :
    (∀ (i : Nat) (hi : i < n),
      s'.tokens[i]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
      s.tokens[i]'(by omega)) ∧
    ScannerCorrectness.SimpleKeyAbove s' n :=
  ⟨fun i hi => ScannerCorrectness.scanNextToken_preserves_prefix s s' h_next n h_n h_inv i hi,
   ScannerCorrectness.scanNextToken_maintains_simpleKeyAbove s s' h_next n h_n h_inv⟩

/-- Through a ScanChain, all raw token positions below `n₀` are preserved,
    provided `n₀ ≤ s.tokens.size` and `SimpleKeyAbove s n₀` holds (tracking
    both the current simpleKey and all stacked simpleKeys).

    The `SimpleKeyAbove` invariant is maintained through each step by
    `scanNextToken_prefix_and_sk_inv`, making the induction straightforward. -/
theorem ScanChain_preserves_raw_prefix {s s' : ScannerState} {k : Nat}
    (h_chain : ScanChain s k s')
    (n₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : ScannerCorrectness.SimpleKeyAbove s n₀)
    (i : Nat) (hi : i < n₀) :
    s'.tokens[i]'(by have := ScanChain_tokens_mono h_chain; omega) =
    s.tokens[i]'(by omega) := by
  induction h_chain with
  | zero => rfl
  | step h_snt h_rest ih =>
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt
    have ⟨h_pres, h_inv'⟩ := scanNextToken_prefix_and_sk_inv _ _ h_snt n₀ h_n₀ h_inv
    exact (ih (Nat.le_trans h_n₀ h_adds) h_inv').trans (h_pres i hi)

/-! #### Filtered growth through a scan chain — see the strict-variant track

The unconditional per-step lemma `scanNextToken_filtered_grows` (and its `ScanChain`
corollary `ScanChain_filtered_grows`) were **removed**: they are *false as stated*.  A
YAML 1.2.2 §6.8.3 reserved directive (`%FOO …`, not `%YAML`/`%TAG`) is scanned by
`scanDirective` into `skipToEndOfLine` and emits **no** token, so that `scanNextToken`
step returns `some s'` while adding zero filtered tokens — the `≥ +1` bound cannot hold
for every input.  The old proof papered over exactly this case with a `sorry` on the
reserved-directive branch of the structural dispatch.

The honest replacement is the **strict-variant track** in `ScanChainGrowth.lean`:
`ScanChainGrew p` augments a `ScanChain` with a per-step *witness* that the filtered
count strictly grows, and `ScanChainGrew_filtered_grows` then yields the `+ n` bound with
no sorry.  The emitter-body producers (`emitList_scans_safebody` /
`emitPairList_scans_safebody`) construct that witnessed chain directly, so the
non-empty-structure theorems read the growth bound off the chain they already build (the
mapping body's `old_sz + 3 ≤ …` and the sequence body's `old_sz < …` conjuncts of the
`*_body_filtered_characterization` lemmas) rather than re-deriving it from a (false)
universal per-step lemma. -/

/-- Through a FlowMonoChain, the filtered token array of the final state has the
    filtered array of the initial state as a prefix.

    Uses `FlowMonoChain_preserves_raw_prefix` (which maintains `SimpleKeyAboveFloor`
    through the chain using the flow-level floor) composed with
    `Array_filter_prefix_of_raw_prefix` to lift raw index preservation to
    filtered-array prefix preservation.

    **Preconditions**:
    - `FlowMonoChain fl₀ s n s'`: flow-monotone chain with floor `fl₀`
    - `h_sk`: `s.simpleKey.possible = false` (no in-flight placeholder reservation)
    - `h_sync`: `s.simpleKeyStack.size ≥ s.flowLevel` (stack/flow synchronized)
    - `h_stack_floor`: stack entries at index ≥ `fl₀` have `tokenIndex ≥ s.tokens.size`

    Both call sites have `fl₀ = s₁.flowLevel = 1` with `s₁.simpleKeyStack.size = 1`,
    making `h_stack_floor` vacuously true (no `j` satisfies `1 ≤ j < 1`). -/
theorem ScanChain_filtered_prefix {s s' : ScannerState} {n fl₀ : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s')
    (h_sk : s.simpleKey.possible = false)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_stack_floor : ∀ j, fl₀ ≤ j → (hj : j < s.simpleKeyStack.size) →
      s.simpleKeyStack[j].possible = true → s.simpleKeyStack[j].tokenIndex ≥ s.tokens.size) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ∃ suffix, (s'.tokens.filter p).toList = (s.tokens.filter p).toList ++ suffix := by
  exact Array_filter_prefix_of_raw_prefix s.tokens s'.tokens _
    (FlowMonoChain.tokens_mono h_fmc)
    (fun i hi => FlowMonoChain_preserves_raw_prefix h_fmc s.tokens.size (by omega)
      ⟨fun h => absurd h (by simp [h_sk]), h_stack_floor, by have := h_fmc.flowLevel_ge_start; omega⟩
      h_sync i hi)

/-- `emitPairList` for non-empty pairs produces a non-empty string. -/
theorem emitPairList_toList_ne_nil (p : YamlValue × YamlValue)
    (ps : List (YamlValue × YamlValue)) :
    (emit.emitPairList (p :: ps)).toList ≠ [] := by
  obtain ⟨c, rest', h_eq, _, _, _⟩ := emitPairList_first_char p ps
  rw [h_eq]; exact List.cons_ne_nil _ _

/-- `scanFlowSequenceEnd` token array equation: pushes exactly one `.flowSequenceEnd` token. -/
theorem scanFlowSequenceEnd_tokens_eq (s : ScannerState) :
    (scanFlowSequenceEnd s).tokens = s.tokens.push { pos := s.currentPos, val := .flowSequenceEnd } := by
  unfold scanFlowSequenceEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowSequenceEnd)]
  unfold ScannerState.emit; rfl

/-- `scanFlowMappingEnd` token array equation: pushes exactly one `.flowMappingEnd` token. -/
theorem scanFlowMappingEnd_tokens_eq (s : ScannerState) :
    (scanFlowMappingEnd s).tokens = s.tokens.push { pos := s.currentPos, val := .flowMappingEnd } := by
  unfold scanFlowMappingEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowMappingEnd)]
  unfold ScannerState.emit; rfl

/-- The close-bracket step for outermost `]`: filtered token array is the input
    filtered array with `.flowSequenceEnd` appended.

    Traces through `saveSimpleKey` (adds only placeholders, filtered out) →
    `allowDirectives` (no token change) → `scanFlowSequenceEnd` (appends
    `.flowSequenceEnd` which passes the placeholder filter). -/
theorem scanNextToken_flow_close_seq_outermost_ext (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨[']'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ s'.indents = s.indents
      ∧ (∃ tok, tok.val = .flowSequenceEnd ∧
          s'.tokens.filter p = (s.tokens.filter p).push tok) := by
  -- Replay the close bracket proof to get the intermediate state s_ad
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ']')) :=
    scanNextToken_preprocess_flow s ']' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_bracket s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨[']'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_flow_disp := dispatchFlowIndicators_close_bracket_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- s' = scanFlowSequenceEnd s_ad
  let s' := scanFlowSequenceEnd s_ad
  have h_result_fl : s'.flowLevel = 0 := by
    show (scanFlowSequenceEnd s_ad).flowLevel = 0
    rw [scanFlowSequenceEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : s'.directivesPresent = false := by
    show (scanFlowSequenceEnd s_ad).directivesPresent = false
    rw [scanFlowSequenceEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : s'.peek? = none := by
    show (scanFlowSequenceEnd s_ad).peek? = none
    rw [scanFlowSequenceEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad ']' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowSequenceEnd) ']' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowSequenceEnd).offset < (s_ad.emit .flowSequenceEnd).inputEnd from h_lt)
        (by decide) (by decide))
  -- Indents preservation: s'.indents = s.indents
  have h_result_indents : s'.indents = s.indents := by
    show (scanFlowSequenceEnd s_ad).indents = s.indents
    rw [scanFlowSequenceEnd_preserves_indents]
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  -- Filtered tokens: s'.tokens.filter p = (s.tokens.filter p).push tok
  have h_ad_tokens_filter : s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]
    split <;> exact saveSimpleKey_filter_placeholder s
  have h_result_tokens : ∃ tok, tok.val = .flowSequenceEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder) =
      (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
    have h_fse_tokens : (scanFlowSequenceEnd s_ad).tokens =
        s_ad.tokens.push { pos := s_ad.currentPos, val := .flowSequenceEnd } :=
      scanFlowSequenceEnd_tokens_eq s_ad
    have h_filter_push : (s_ad.tokens.push { pos := s_ad.currentPos, val := .flowSequenceEnd }).filter
        (fun t => t.val != .placeholder) =
        (s_ad.tokens.filter (fun t => t.val != .placeholder)).push
          { pos := s_ad.currentPos, val := .flowSequenceEnd } := by
      rw [Array.filter_push]; rfl
    exact ⟨{ pos := s_ad.currentPos, val := .flowSequenceEnd }, rfl,
      by rw [show s' = scanFlowSequenceEnd s_ad from rfl,
             h_fse_tokens, h_filter_push, h_ad_tokens_filter]⟩
  exact ⟨s', h_snt, h_result_fl, h_result_dp, h_result_eof, h_result_indents, h_result_tokens⟩

/-- The close-brace step for outermost `}`: filtered token array is the input
    filtered array with `.flowMappingEnd` appended. -/
theorem scanNextToken_flow_close_mapping_outermost_ext (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨['}'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ s'.indents = s.indents
      ∧ (∃ tok, tok.val = .flowMappingEnd ∧
          s'.tokens.filter p = (s.tokens.filter p).push tok) := by
  -- Replay the close brace proof to get the intermediate state s_ad
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '}')) :=
    scanNextToken_preprocess_flow s '}' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_brace s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨['}'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_flow_disp := dispatchFlowIndicators_close_brace_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- s' = scanFlowMappingEnd s_ad
  let s' := scanFlowMappingEnd s_ad
  have h_result_fl : s'.flowLevel = 0 := by
    show (scanFlowMappingEnd s_ad).flowLevel = 0
    rw [scanFlowMappingEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : s'.directivesPresent = false := by
    show (scanFlowMappingEnd s_ad).directivesPresent = false
    rw [scanFlowMappingEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : s'.peek? = none := by
    show (scanFlowMappingEnd s_ad).peek? = none
    rw [scanFlowMappingEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad '}' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowMappingEnd) '}' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowMappingEnd).offset < (s_ad.emit .flowMappingEnd).inputEnd from h_lt)
        (by decide) (by decide))
  -- Indents preservation: s'.indents = s.indents
  have h_result_indents : s'.indents = s.indents := by
    show (scanFlowMappingEnd s_ad).indents = s.indents
    rw [scanFlowMappingEnd_preserves_indents]
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  -- Filtered tokens: s'.tokens.filter p = (s.tokens.filter p).push tok
  have h_ad_tokens_filter : s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]
    split <;> exact saveSimpleKey_filter_placeholder s
  have h_result_tokens : ∃ tok, tok.val = .flowMappingEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder) =
      (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
    have h_fme_tokens : (scanFlowMappingEnd s_ad).tokens =
        s_ad.tokens.push { pos := s_ad.currentPos, val := .flowMappingEnd } :=
      scanFlowMappingEnd_tokens_eq s_ad
    have h_filter_push : (s_ad.tokens.push { pos := s_ad.currentPos, val := .flowMappingEnd }).filter
        (fun t => t.val != .placeholder) =
        (s_ad.tokens.filter (fun t => t.val != .placeholder)).push
          { pos := s_ad.currentPos, val := .flowMappingEnd } := by
      rw [Array.filter_push]; rfl
    exact ⟨{ pos := s_ad.currentPos, val := .flowMappingEnd }, rfl,
      by rw [show s' = scanFlowMappingEnd s_ad from rfl,
             h_fme_tokens, h_filter_push, h_ad_tokens_filter]⟩
  exact ⟨s', h_snt, h_result_fl, h_result_dp, h_result_eof, h_result_indents, h_result_tokens⟩

-- Every `scanFiltered` result has streamStart first, streamEnd last, size ≥ 2.
-- Mirrors the proof of `scanFiltered_produces_valid_tokens` but returns a
-- plain conjunction (avoiding the `ValidTokenStream` struct indirection).
theorem scanFiltered_boundary_tokens (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    tokens.size ≥ 2 ∧
    tokens[0]!.val = .streamStart ∧
    tokens[tokens.size - 1]!.val = .streamEnd := by
  unfold Scanner.scanFiltered at h
  -- Case split on the underlying scan result
  generalize h_scan : Scanner.scan input = result at h
  match result with
  | .error _ => simp at h
  | .ok raw =>
  -- h : .ok (raw.filter (fun t => t.val != .placeholder)) = .ok tokens
  injection h with h_eq
  -- h_eq : raw.filter ... = tokens — keep tokens in goal, transport via ← h_eq
  let p : Positioned YamlToken → Bool := fun t => t.val != .placeholder
  let l := raw.toList
  -- Raw scan properties
  have h_raw_sz := ScannerCorrectness.scan_produces_at_least_two input raw h_scan
  have h_raw_first := ScannerCorrectness.scan_first_is_streamStart input raw h_scan (by omega)
  have h_raw_last := ScannerCorrectness.scan_last_is_streamEnd input raw h_scan (by omega)
  -- List-level reasoning: head/last pass filter, preserved in filtered list
  have h_l_ne : l ≠ [] := by
    intro h0
    have : raw.size = 0 := by show l.length = 0; simp [h0]
    omega
  have h_p_first : p (l.head h_l_ne) = true := by
    show ((l.head h_l_ne).val != .placeholder) = true
    have : (l.head h_l_ne).val = .streamStart := by
      rw [List.head_eq_getElem]; exact h_raw_first
    rw [this]; decide
  have h_p_last : p (l.getLast h_l_ne) = true := by
    show ((l.getLast h_l_ne).val != .placeholder) = true
    have : (l.getLast h_l_ne).val = .streamEnd := by
      rw [List.getLast_eq_getElem]; exact h_raw_last
    rw [this]; decide
  have h_flt_ne : l.filter p ≠ [] := by
    rw [show l = l.head h_l_ne :: l.tail from (List.cons_head_tail h_l_ne).symm,
        List.filter_cons_of_pos h_p_first]
    exact List.cons_ne_nil _ _
  have h_find : l.find? p = some (l.head h_l_ne) := by
    conv => lhs; rw [show l = l.head h_l_ne :: l.tail from (List.cons_head_tail h_l_ne).symm]
    exact List.find?_cons_of_pos h_p_first
  have h_head_filt : (l.filter p).head h_flt_ne = l.head h_l_ne := by
    rw [List.head_filter]; simp [h_find]
  have h_rev_ne : l.reverse ≠ [] := by simp [h_l_ne]
  have h_rfind : l.reverse.find? p = some (l.getLast h_l_ne) := by
    conv => lhs; rw [show l.reverse = l.reverse.head h_rev_ne :: l.reverse.tail
                        from (List.cons_head_tail h_rev_ne).symm,
                      show l.reverse.head h_rev_ne = l.getLast h_l_ne
                        from List.head_reverse ..]
    exact List.find?_cons_of_pos h_p_last
  have h_last_filt : (l.filter p).getLast h_flt_ne = l.getLast h_l_ne := by
    rw [List.getLast_filter]; simp [h_rfind]
  -- Filtered size ≥ 2
  have h_filt_sz_list : (l.filter p).length ≥ 2 := by
    have h_pos : (l.filter p).length > 0 := List.length_pos_iff.mpr h_flt_ne
    have h_ne_1 : (l.filter p).length ≠ 1 := by
      intro h1
      obtain ⟨a, h_eq'⟩ := List.length_eq_one_iff.mp h1
      have : l.head h_l_ne = l.getLast h_l_ne := by
        rw [← h_head_filt, ← h_last_filt]; simp [h_eq']
      have := congrArg Positioned.val this
      rw [show (l.head h_l_ne).val = .streamStart
            from by rw [List.head_eq_getElem]; exact h_raw_first,
          show (l.getLast h_l_ne).val = .streamEnd
            from by rw [List.getLast_eq_getElem]; exact h_raw_last] at this
      cases this
    omega
  have h_filt_sz : (raw.filter p).size ≥ 2 := by
    show (raw.filter p).toList.length ≥ 2
    rw [Array.toList_filter]; exact h_filt_sz_list
  -- Bridge Array.size ↔ List.length for omega
  have h_filt_len : (raw.filter p).toList.length ≥ 2 := by
    rw [Array.toList_filter]; exact h_filt_sz_list
  -- Transport to tokens via ← h_eq
  have h_tsz : tokens.size ≥ 2 := h_eq ▸ h_filt_sz
  refine ⟨h_tsz, ?_, ?_⟩
  · -- tokens[0]!.val = .streamStart
    suffices h : (raw.filter p)[0]!.val = .streamStart by rwa [h_eq] at h
    rw [getElem!_pos _ 0 (by omega)]
    have h_first_val : ((l.filter p).head h_flt_ne).val = .streamStart := by
      rw [h_head_filt, List.head_eq_getElem]; exact h_raw_first
    rw [List.head_eq_getElem] at h_first_val
    show ((raw.filter p).toList[0]'(show 0 < (raw.filter p).size from by omega)).val
      = .streamStart
    simp only [Array.toList_filter]; exact h_first_val
  · -- tokens[N-1]!.val = .streamEnd
    suffices h : (raw.filter p)[(raw.filter p).size - 1]!.val = .streamEnd by rwa [h_eq] at h
    rw [getElem!_pos _ _ (by omega)]
    have h_last_val : ((l.filter p).getLast h_flt_ne).val = .streamEnd := by
      rw [h_last_filt, List.getLast_eq_getElem]; exact h_raw_last
    rw [List.getLast_eq_getElem] at h_last_val
    have h_sz_eq : (raw.filter p).size = (l.filter p).length := by
      have : (raw.filter p).toList = l.filter p := Array.toList_filter
      show (raw.filter p).toList.length = (l.filter p).length; rw [this]
    show ((raw.filter p).toList[(raw.filter p).size - 1]'(show (raw.filter p).size - 1 < (raw.filter p).size from by omega)).val
      = .streamEnd
    simp only [Array.toList_filter, h_sz_eq]; exact h_last_val

-- These characterize the filtered token array produced by scanning emitter output,
-- providing the properties needed by the parser flow loop fuel sufficiency theorems.

-- Flow bracket nesting utilities (flowBracketDelta, flowBracketBalance) are defined
-- in ParserGrammableBase.lean and available via the ParserGrammable import.
open L4YAML.Proofs.ParserGrammable (flowBracketDelta flowBracketBalance
  flowBracketBalance_compose flowBracketBalance_push)


end L4YAML.Proofs.EmitterScannability
