import L4YAML.Proofs.Output.EmitterScannability.Block

/-!
# `Grammable` producers for the block-tracking predicates

Extracted from / building on `EmitterScannability.Block` (2026-05-31).  Ships the
monolithic `Grammable` producers for the two block-tracking predicates:

  * `emit_scans_in_flow_block            : Grammable v inFlow → EmitScansInFlowBlock v`
  * `emit_scans_in_flow_saved_key_block  : Grammable v inFlow → EmitScansInFlowSavedKeyBlock v`

proven as **one combined induction** `EmitScansInFlowBlock v ∧ EmitScansInFlowSavedKeyBlock v`
(genuinely mutual: the block-mapping case needs the saved-key-block of the *keys* while the
saved-key producer's body needs the block of *items/values*; the IH yields both projections
for every sub-value, and the two `.1`/`.2` wrappers expose the public names).

Each case mirrors the proven non-block templates `emit_scans_in_flow` and
`emit_scans_in_flow_saved_key` (`ScanChainGrowth`), adding the block conjuncts via the
dispatch-push lemmas (`scanNextToken_flow_*_filtered_push`), the body producers
(`emitList_scans_block_nonempty` / `emitPairList_scans_block_nonempty`), and the bracket
framers (`wrap_seq_block` / `wrap_map_block`).  The one genuinely novel sub-proof is the
saved-key-block `take`-side equation, captured by the pure helper
`block_take_eq_of_getElem?`.

These declarations stay in the original `L4YAML.Proofs.EmitterScannability` namespace, so
their fully-qualified names are unchanged.
-/

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

open L4YAML.Proofs.ParserGrammable (flowBracketDelta flowBracketBalance
  flowBracketBalance_compose flowBracketBalance_push)

/-! ### Take-side filter helper

    The saved-key-block predicate carries a *take-side* filter equation
    `(s'.tokens.toList.take (N+1)).filter p = (s.tokens.filter p).toList` (`N = s.tokens.size`).
    Given the first-`N` raw prefix matches `s.tokens` (`h_pref` pointwise) and slot `N` is
    filtered out (`h_ph`), the take-of-`N+1` filter is exactly `s.tokens`' filter: the first
    `N` tokens contribute `s.tokens`' filter and the placeholder at slot `N` filters away. -/
private theorem block_take_eq_of_getElem?
    (arr base : Array (Positioned YamlToken)) (N : Nat)
    (p : Positioned YamlToken → Bool)
    (h_base : base.size = N)
    (h_N1 : N < arr.size)
    (h_pref : ∀ j, j < N → arr[j]? = base[j]?)
    (h_ph : p (arr[N]'h_N1) = false) :
    (arr.toList.take (N + 1)).filter p = (base.filter p).toList := by
  have h_take : arr.toList.take N = base.toList := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < N
    · rw [if_pos hj, Array.getElem?_toList, Array.getElem?_toList, h_pref j hj]
    · rw [if_neg hj,
        List.getElem?_eq_none_iff.mpr (by rw [Array.length_toList, h_base]; omega)]
  have h_lenN : N < arr.toList.length := by rwa [Array.length_toList]
  have h_getN : arr.toList[N]? = some (arr[N]'h_N1) := by
    rw [List.getElem?_eq_getElem h_lenN, Array.getElem_toList]
  rw [List.take_add_one, h_take, h_getN, Option.toList_some, List.filter_append,
      List.filter_cons]
  simp only [h_ph, Bool.false_eq_true, if_false, List.filter_nil, List.append_nil]
  exact (Array.toList_filter).symm

/-! ### Open-`{` exposes `simpleKeyAllowed = true`

    Companion to `scanNextToken_flow_open_mapping_nested`: a `{` in flow context leaves
    `simpleKeyAllowed = true` (a simple key can start immediately inside the mapping).  Needed
    because the mapping-body producer `emitPairList_scans_block_nonempty` requires it (the first
    pair's key is reserved via `saveSimpleKey`). -/
theorem scanNextToken_flow_open_mapping_ska (s s' : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_snt : scanNextToken s = .ok (some s')) :
    s'.simpleKeyAllowed = true := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '{')) :=
    scanNextToken_preprocess_flow s '{' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '{' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true } else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_brace s_ad
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowMappingStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowMappingStart s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  rw [h_s']; rfl

/-! ### Combined `Grammable` producer

    One induction over `Grammable v inFlow` producing `EmitScansInFlowBlock v ∧
    EmitScansInFlowSavedKeyBlock v`.  Each constructor's pair is assembled from the
    corresponding non-block template plus the block conjuncts. -/
set_option maxHeartbeats 1600000 in
theorem emit_scans_block_combined (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) :
    EmitScansInFlowBlock v ∧ EmitScansInFlowSavedKeyBlock v := by
  induction hg with
  | scalar sc _ h =>
    refine ⟨?block, ?savedkey⟩
    case block =>
      intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline _h_sync
      have h_chars : (emit (.scalar sc)).toList ++ rest =
          ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest := by
        simp only [emit, emitScalar, String.toList_append]; rfl
      have hcorr' : ScannerSurfCorr s_state
          ⟨['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest, s_state.col⟩ := by
        rwa [← h_chars]
      have hcorr_q : ScannerSurfCorr s_state
          ⟨'"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest), s_state.col⟩ := by
        have : ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest =
            '"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr'
      obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_tok', h_ska', _h_line', h_atol', h_endline', h_stack'⟩ :=
        scanNextToken_flow_scanDoubleQuoted s_state sc.content rest hcorr' h_flow h_indent h_col
          h_atol h_endline
      have h_grew : (s'.tokens.filter (fun t => t.val != .placeholder)).size >
                    (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s_state s' '"'
          ((escapeString sc.content).toList ++ ['"'] ++ rest) hcorr_q
          h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt
      obtain ⟨tok, str, st, h_tok_val, h_push⟩ :=
        scanNextToken_flow_scalar_filtered_push s_state ((escapeString sc.content).toList ++ ['"'] ++ rest)
          hcorr_q h_flow h_indent h_col h_snt
      refine ⟨1, s', [tok], ScanChainGrew.single h_snt h_grew, h_corr', h_fl', h_dp', h_ids', h_ek',
        h_col', ?_, ?_, _h_line', h_ska', h_tok', h_atol', h_endline', h_stack',
        FlowMonoChain.single h_snt (Nat.le.refl) (by omega), ?_, ?_, ?_, ?_⟩
      · unfold ScannerState.inFlow; rw [h_fl']
        unfold ScannerState.inFlow at h_flow; exact h_flow
      · unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent
      · rw [h_push, Array.toList_push]
      · exact WellBracketed_singleton_delta_zero tok (by rw [h_tok_val]; exact flowBracketDelta_scalar str st)
      · exact EntrySafe_scalar tok str st h_tok_val
      · exact ⟨List.cons_ne_nil _ _, Or.inl ⟨str, st, by rw [List.head_cons]; exact h_tok_val⟩⟩
    case savedkey =>
      intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska _h_sync
      have h_chars : (emit (.scalar sc)).toList ++ rest =
          ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest := by
        simp only [emit, emitScalar, String.toList_append]; rfl
      have hcorr' : ScannerSurfCorr s_state
          ⟨['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest, s_state.col⟩ := by
        rwa [← h_chars]
      have hcorr_q : ScannerSurfCorr s_state
          ⟨'"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest), s_state.col⟩ := by
        have : ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest =
            '"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr'
      obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', _h_tok', h_ska', _h_line', h_atol', h_endline', h_stack'⟩ :=
        scanNextToken_flow_scanDoubleQuoted s_state sc.content rest hcorr' h_flow h_indent h_col
          h_atol h_endline
      obtain ⟨s'', h_snt'', h_poss'', h_tidx'', h_size'', h_ph'', h_ph1''⟩ :=
        scanNextToken_flow_scalar_savedKey s_state sc.content rest hcorr' h_flow h_indent h_col h_ek h_ska
      have h_eq : s'' = s' := Option.some.inj (Except.ok.inj (h_snt''.symm.trans h_snt))
      subst h_eq
      have h_grew : (s''.tokens.filter (fun t => t.val != .placeholder)).size >
                    (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s_state s'' '"'
          ((escapeString sc.content).toList ++ ['"'] ++ rest) hcorr_q
          h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt''
      obtain ⟨tok, str, st, h_tok_val, h_push⟩ :=
        scanNextToken_flow_scalar_filtered_push s_state ((escapeString sc.content).toList ++ ['"'] ++ rest)
          hcorr_q h_flow h_indent h_col h_snt''
      have h_N1 : s_state.tokens.size < s''.tokens.size := by omega
      have h_nc : ∀ t c', scanNextToken_preprocess s_state = .ok (some (t, c')) → c' ≠ ':' :=
        no_colon_of_preprocess_flow s_state '"' ((escapeString sc.content).toList ++ ['"'] ++ rest)
          s_state.col hcorr_q h_flow (by decide) (by decide) (by decide) (by decide)
      have h_pref : ∀ j, j < s_state.tokens.size → s''.tokens[j]? = s_state.tokens[j]? := by
        intro j hj
        have h_pt := scanNextToken_at_non_colon_preserves_positions s_state s'' h_snt'' h_nc j hj
        rw [Array.getElem?_eq_getElem (by
              have := ScannerCorrectness.scanNextToken_adds_tokens s_state s'' h_snt''; omega),
            Array.getElem?_eq_getElem hj, h_pt]
      have h_ph_false :
          (fun (t : Positioned YamlToken) => t.val != .placeholder) (s''.tokens[s_state.tokens.size]'h_N1) = false := by
        have h := h_ph'' h_N1; simp [h]
      have h_take :
          (s''.tokens.toList.take (s_state.tokens.size + 1)).filter (fun t => t.val != .placeholder)
            = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList :=
        block_take_eq_of_getElem? s''.tokens s_state.tokens s_state.tokens.size
          (fun t => t.val != .placeholder) rfl h_N1 h_pref h_ph_false
      refine ⟨1, s'', [tok], ScanChainGrew.single h_snt'' h_grew, h_corr', h_fl', h_dp', h_ids', h_ek',
        h_col', ?_, ?_, _h_line', h_atol', h_endline', h_stack',
        FlowMonoChain.single h_snt'' (Nat.le.refl) (by omega),
        h_ska', h_poss'', h_tidx'', h_size'', h_ph'', h_ph1'', ?_, h_take, ?_⟩
      · unfold ScannerState.inFlow; rw [h_fl']
        unfold ScannerState.inFlow at h_flow; exact h_flow
      · unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent
      · rw [h_push, Array.toList_push]
      · exact WellBracketed_singleton_delta_zero tok (by rw [h_tok_val]; exact flowBracketDelta_scalar str st)
  | sequence style items tag anchor _ h ih =>
    refine ⟨?block, ?savedkey⟩
    case block =>
      intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      have h_chars : (emit (.sequence style items tag anchor)).toList ++ rest =
          ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest := by
        simp only [emit, String.toList_append]; rfl
      have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest), s_state.col⟩ := by
        have : ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest =
            '[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, _h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
        scanNextToken_flow_open_nested s_state
          ((emit.emitList items.toList).toList ++ [']'] ++ rest) hcorr₀ h_flow h_indent h_col
          h_atol h_endline
      have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
      have h_s1_inflow : s₁.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
      have h_s1_indent : s₁.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
      have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
      have h_s1_sync : s₁.simpleKeyStack.size = s₁.flowLevel := by
        rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
      obtain ⟨fssTok, h_fss_val, h_open_push⟩ :=
        scanNextToken_flow_open_seq_filtered_push s_state
          ((emit.emitList items.toList).toList ++ [']'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_snt₁
      have h_list_scan : EmitListScansInFlowBlock items.toList := by
        match h_list : items.toList with
        | [] => exact emitList_scans_block_empty
        | _ :: _ =>
          exact emitList_scans_block_nonempty _ (by simp) (fun w hw => by
            have hw' : w ∈ items.toList := h_list ▸ hw
            have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw'
            have h_sz : i < items.size := by rwa [Array.length_toList] at hi
            exact h_eq ▸ (ih ⟨i, h_sz⟩).1)
      have h_corr₁_assoc : ScannerSurfCorr s₁
          ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
        rw [List.append_assoc] at h_corr₁; exact h_corr₁
      obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_body_append, h_body_wb⟩ :=
        h_list_scan s₁ ([']'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_s1_sync
      have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
      have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
        unfold StackEndLineOnLine at h_stack_endline₁ ⊢
        rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
      obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, _, _⟩ :=
        scanNextToken_flow_close_seq_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
          h_atol₂ h_stack_endline₂
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨']' :: rest, s₂.col⟩ := by
        have : [']'] ++ rest = ']' :: rest := by simp
        rwa [this] at h_corr₂
      obtain ⟨fseTok, h_fse_val, h_close_push⟩ :=
        scanNextToken_flow_close_seq_filtered_push s₂ rest h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
          h_fl₂_ge2 h_snt₃
      have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
      have h_fmc_all :=
        (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
          (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
      have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s_state s₁ '['
          ((emit.emitList items.toList).toList ++ [']'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
      have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s₂ s₃ ']' rest
          h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
      have h_block_eq : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (fssTok :: (bodyBlock ++ [fseTok])) := by
        have h1 : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fssTok] := by
          rw [h_open_push, Array.toList_push]
        have h3 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fseTok] := by
          rw [h_close_push, Array.toList_push]
        rw [h3, h_body_append, h1]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have h_wrap := wrap_seq_block fssTok fseTok bodyBlock h_fss_val h_fse_val h_body_wb
      refine ⟨(1 + n₂) + 1, s₃, fssTok :: (bodyBlock ++ [fseTok]),
        (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
        h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all,
        h_block_eq, h_wrap.1, h_wrap.2, ?_⟩
      · rw [h_fl₃, h_fl₂, h_fl₁]; omega
      · rw [h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek₃, h_ek₂, h_ek₁]
      · rw [h_col₃]; omega
      · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
      · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
      · rw [_h_line₃, _h_line₂, _h_line₁]
      · exact h_atol₃
      · exact h_endline₃
      · rw [h_stack₃, h_stack₂, h_stack_pop₁]
      · exact ⟨List.cons_ne_nil _ _, Or.inr (Or.inl (by rw [List.head_cons]; exact h_fss_val))⟩
    case savedkey =>
      intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
      have h_chars : (emit (.sequence style items tag anchor)).toList ++ rest =
          ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest := by
        simp only [emit, String.toList_append]; rfl
      have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest), s_state.col⟩ := by
        have : ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest =
            '[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
        scanNextToken_flow_open_nested s_state
          ((emit.emitList items.toList).toList ++ [']'] ++ rest) hcorr₀ h_flow h_indent h_col
          h_atol h_endline
      obtain ⟨h_s1_size, h_s1_rawN, h_s1_rawN1⟩ :=
        scanNextToken_flow_open_seq_savedKey s_state s₁ ((emit.emitList items.toList).toList ++ [']'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_ek h_ska h_snt₁
      have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
      have h_s1_inflow : s₁.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
      have h_s1_indent : s₁.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
      have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
      have h_stack_size₁ : s₁.simpleKeyStack.size = s₁.flowLevel := by
        rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
      obtain ⟨fssTok, h_fss_val, h_open_push⟩ :=
        scanNextToken_flow_open_seq_filtered_push s_state
          ((emit.emitList items.toList).toList ++ [']'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_snt₁
      have h_list_scan : EmitListScansInFlowBlock items.toList := by
        match h_list : items.toList with
        | [] => exact emitList_scans_block_empty
        | _ :: _ =>
          exact emitList_scans_block_nonempty _ (by simp) (fun w hw => by
            have hw' : w ∈ items.toList := h_list ▸ hw
            have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw'
            have h_sz : i < items.size := by rwa [Array.length_toList] at hi
            exact h_eq ▸ (ih ⟨i, h_sz⟩).1)
      have h_corr₁_assoc : ScannerSurfCorr s₁
          ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
        rw [List.append_assoc] at h_corr₁; exact h_corr₁
      obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_body_append, h_body_wb⟩ :=
        h_list_scan s₁ ([']'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_stack_size₁
      have h_skaf_N : SimpleKeyAboveFloor s₁ s_state.tokens.size s₁.flowLevel := by
        refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
          fun j hj hjb _ => by exfalso; omega, by omega⟩
      have h_skaf₁ : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 1) s₁.flowLevel := by
        refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
          fun j hj hjb _ => by exfalso; omega, by omega⟩
      have h_body_rawN : s₂.tokens[s_state.tokens.size]? = s₁.tokens[s_state.tokens.size]? := by
        have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 1)
          (by omega) h_skaf₁ (by omega) s_state.tokens.size (by omega)
        rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
            Array.getElem?_eq_getElem (by omega), h_eq]
      have h_skaf₁' : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 2) s₁.flowLevel := by
        refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
          fun j hj hjb _ => by exfalso; omega, by omega⟩
      have h_body_rawN1 : s₂.tokens[s_state.tokens.size + 1]? = s₁.tokens[s_state.tokens.size + 1]? := by
        have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 2)
          (by omega) h_skaf₁' (by omega) (s_state.tokens.size + 1) (by omega)
        rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
            Array.getElem?_eq_getElem (by omega), h_eq]
      have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
      have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
        unfold StackEndLineOnLine at h_stack_endline₁ ⊢
        rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
      obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, h_skrestore₃, h_prefix₃⟩ :=
        scanNextToken_flow_close_seq_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
          h_atol₂ h_stack_endline₂
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨']' :: rest, s₂.col⟩ := by
        have : [']'] ++ rest = ']' :: rest := by simp
        rwa [this] at h_corr₂
      obtain ⟨fseTok, h_fse_val, h_close_push⟩ :=
        scanNextToken_flow_close_seq_filtered_push s₂ rest h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
          h_fl₂_ge2 h_snt₃
      have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
      have h_fmc_all :=
        (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
          (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
      have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s_state s₁ '['
          ((emit.emitList items.toList).toList ++ [']'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
      have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s₂ s₃ ']' rest
          h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
      have h_skey_eq : s₃.simpleKey = (saveSimpleKey s_state).simpleKey := by
        rw [h_skrestore₃, h_stack₂, h_stack_push₁]; simp [Array.back?_push]
      obtain ⟨_h_skp, _h_skt, _, _⟩ := saveSimpleKey_eval s_state h_ek h_ska
      have h_close_mono : s₂.tokens.size ≤ s₃.tokens.size := by
        have := ScannerCorrectness.scanNextToken_adds_tokens s₂ s₃ h_snt₃; omega
      have h_body_mono : s₁.tokens.size ≤ s₂.tokens.size := h_fmc₂.tokens_mono
      have h_s3_rawN? : s₃.tokens[s_state.tokens.size]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
        rw [h_prefix₃ s_state.tokens.size (by omega), h_body_rawN, h_s1_rawN]
      have h_s3_rawN1? : s₃.tokens[s_state.tokens.size + 1]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
        rw [h_prefix₃ (s_state.tokens.size + 1) (by omega), h_body_rawN1, h_s1_rawN1]
      have h_block_eq : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (fssTok :: (bodyBlock ++ [fseTok])) := by
        have h1 : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fssTok] := by
          rw [h_open_push, Array.toList_push]
        have h3 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fseTok] := by
          rw [h_close_push, Array.toList_push]
        rw [h3, h_body_append, h1]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have h_N1 : s_state.tokens.size < s₃.tokens.size := by omega
      have h_pref : ∀ j, j < s_state.tokens.size → s₃.tokens[j]? = s_state.tokens[j]? := by
        intro j hj
        have hj2 : j < s₂.tokens.size := by omega
        have h_nc_open : ∀ t c', scanNextToken_preprocess s_state = .ok (some (t, c')) → c' ≠ ':' :=
          no_colon_of_preprocess_flow s_state '[' ((emit.emitList items.toList).toList ++ [']'] ++ rest)
            s_state.col h_corr_state_cons h_flow (by decide) (by decide) (by decide) (by decide)
        have ho := scanNextToken_at_non_colon_preserves_positions s_state s₁ h_snt₁ h_nc_open j hj
        have hb := FlowMonoChain_preserves_raw_prefix h_fmc₂ s_state.tokens.size (by omega)
          h_skaf_N (by omega) j hj
        have hc := h_prefix₃ j hj2
        rw [hc, Array.getElem?_eq_getElem hj2, hb, ho, Array.getElem?_eq_getElem hj]
      have h_ph_false :
          (fun (t : Positioned YamlToken) => t.val != .placeholder) (s₃.tokens[s_state.tokens.size]'h_N1) = false := by
        have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'h_N1) :=
          Array.getElem?_eq_getElem h_N1
        have heq := Option.some.inj (h_some.symm.trans h_s3_rawN?)
        rw [heq]; rfl
      have h_take :
          (s₃.tokens.toList.take (s_state.tokens.size + 1)).filter (fun t => t.val != .placeholder)
            = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList :=
        block_take_eq_of_getElem? s₃.tokens s_state.tokens s_state.tokens.size
          (fun t => t.val != .placeholder) rfl h_N1 h_pref h_ph_false
      have h_wrap := wrap_seq_block fssTok fseTok bodyBlock h_fss_val h_fse_val h_body_wb
      refine ⟨(1 + n₂) + 1, s₃, fssTok :: (bodyBlock ++ [fseTok]),
        (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
        h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_atol₃, h_endline₃, ?_, h_fmc_all,
        h_ska₃, ?_, ?_, ?_, ?_, ?_, h_block_eq, h_take, h_wrap.1⟩
      · rw [h_fl₃, h_fl₂, h_fl₁]; omega
      · rw [h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek₃, h_ek₂, h_ek₁]
      · rw [h_col₃]; omega
      · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
      · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
      · rw [_h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack₃, h_stack₂, h_stack_pop₁]
      · rw [h_skey_eq]; exact _h_skp
      · rw [h_skey_eq]; exact _h_skt
      · omega
      · intro hh
        have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'hh) :=
          Array.getElem?_eq_getElem hh
        have := Option.some.inj (h_some.symm.trans h_s3_rawN?); rw [this]
      · intro hh
        have h_some : s₃.tokens[s_state.tokens.size + 1]? = some (s₃.tokens[s_state.tokens.size + 1]'hh) :=
          Array.getElem?_eq_getElem hh
        have := Option.some.inj (h_some.symm.trans h_s3_rawN1?); rw [this]
  | mapping style pairs tag anchor _ hk hv ihk ihv =>
    refine ⟨?block, ?savedkey⟩
    case block =>
      intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      have h_chars : (emit (.mapping style pairs tag anchor)).toList ++ rest =
          ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest := by
        simp only [emit, String.toList_append]; rfl
      have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest), s_state.col⟩ := by
        have : ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest =
            '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, _h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
        scanNextToken_flow_open_mapping_nested s_state
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) hcorr₀ h_flow h_indent h_col
          h_atol h_endline
      have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
      have h_s1_inflow : s₁.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
      have h_s1_indent : s₁.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
      have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
      have h_s1_ska : s₁.simpleKeyAllowed = true :=
        scanNextToken_flow_open_mapping_ska s_state s₁
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_snt₁
      have h_s1_sync : s₁.simpleKeyStack.size = s₁.flowLevel := by
        rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
      obtain ⟨fmsTok, h_fms_val, h_open_push⟩ :=
        scanNextToken_flow_open_map_filtered_push s_state
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_snt₁
      have h_pair_scan : EmitPairListScansInFlowBlock pairs.toList := by
        match h_list : pairs.toList with
        | [] => exact emitPairList_scans_block_empty
        | _ :: _ =>
          exact emitPairList_scans_block_nonempty _ (by simp) (fun p hp => by
            have hp' : p ∈ pairs.toList := h_list ▸ hp
            have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
            have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
            exact h_eq ▸ (ihk ⟨i, h_sz⟩).2) (fun p hp => by
            have hp' : p ∈ pairs.toList := h_list ▸ hp
            have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
            have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
            exact h_eq ▸ (ihv ⟨i, h_sz⟩).1)
      have h_corr₁_assoc : ScannerSurfCorr s₁
          ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
        rw [List.append_assoc] at h_corr₁; exact h_corr₁
      obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_body_append, h_body_wb⟩ :=
        h_pair_scan s₁ (['}'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_s1_ska h_s1_sync
      have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
      have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
        unfold StackEndLineOnLine at h_stack_endline₁ ⊢
        rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
      obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, _, _⟩ :=
        scanNextToken_flow_close_mapping_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
          h_atol₂ h_stack_endline₂
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨'}' :: rest, s₂.col⟩ := by
        have : ['}'] ++ rest = '}' :: rest := by simp
        rwa [this] at h_corr₂
      obtain ⟨fmeTok, h_fme_val, h_close_push⟩ :=
        scanNextToken_flow_close_map_filtered_push s₂ rest h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
          h_fl₂_ge2 h_snt₃
      have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
      have h_fmc_all :=
        (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
          (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
      have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s_state s₁ '{'
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
      have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s₂ s₃ '}' rest
          h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
      have h_block_eq : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (fmsTok :: (bodyBlock ++ [fmeTok])) := by
        have h1 : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fmsTok] := by
          rw [h_open_push, Array.toList_push]
        have h3 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fmeTok] := by
          rw [h_close_push, Array.toList_push]
        rw [h3, h_body_append, h1]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have h_wrap := wrap_map_block fmsTok fmeTok bodyBlock h_fms_val h_fme_val h_body_wb
      refine ⟨(1 + n₂) + 1, s₃, fmsTok :: (bodyBlock ++ [fmeTok]),
        (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
        h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all,
        h_block_eq, h_wrap.1, h_wrap.2, ?_⟩
      · rw [h_fl₃, h_fl₂, h_fl₁]; omega
      · rw [h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek₃, h_ek₂, h_ek₁]
      · rw [h_col₃]; omega
      · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
      · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
      · rw [_h_line₃, _h_line₂, _h_line₁]
      · exact h_atol₃
      · exact h_endline₃
      · rw [h_stack₃, h_stack₂, h_stack_pop₁]
      · exact ⟨List.cons_ne_nil _ _, Or.inr (Or.inr (by rw [List.head_cons]; exact h_fms_val))⟩
    case savedkey =>
      intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
      have h_chars : (emit (.mapping style pairs tag anchor)).toList ++ rest =
          ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest := by
        simp only [emit, String.toList_append]; rfl
      have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest), s_state.col⟩ := by
        have : ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest =
            '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
        scanNextToken_flow_open_mapping_nested s_state
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) hcorr₀ h_flow h_indent h_col
          h_atol h_endline
      obtain ⟨h_s1_size, h_s1_rawN, h_s1_rawN1⟩ :=
        scanNextToken_flow_open_mapping_savedKey s_state s₁ ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_ek h_ska h_snt₁
      have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
      have h_s1_inflow : s₁.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
      have h_s1_indent : s₁.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
      have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
      have h_stack_size₁ : s₁.simpleKeyStack.size = s₁.flowLevel := by
        rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
      have h_s1_ska : s₁.simpleKeyAllowed = true :=
        scanNextToken_flow_open_mapping_ska s_state s₁
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_snt₁
      obtain ⟨fmsTok, h_fms_val, h_open_push⟩ :=
        scanNextToken_flow_open_map_filtered_push s_state
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col h_snt₁
      have h_pair_scan : EmitPairListScansInFlowBlock pairs.toList := by
        match h_list : pairs.toList with
        | [] => exact emitPairList_scans_block_empty
        | _ :: _ =>
          exact emitPairList_scans_block_nonempty _ (by simp) (fun p hp => by
            have hp' : p ∈ pairs.toList := h_list ▸ hp
            have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
            have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
            exact h_eq ▸ (ihk ⟨i, h_sz⟩).2) (fun p hp => by
            have hp' : p ∈ pairs.toList := h_list ▸ hp
            have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
            have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
            exact h_eq ▸ (ihv ⟨i, h_sz⟩).1)
      have h_corr₁_assoc : ScannerSurfCorr s₁
          ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
        rw [List.append_assoc] at h_corr₁; exact h_corr₁
      obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_body_append, h_body_wb⟩ :=
        h_pair_scan s₁ (['}'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_s1_ska h_stack_size₁
      have h_skaf_N : SimpleKeyAboveFloor s₁ s_state.tokens.size s₁.flowLevel := by
        refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
          fun j hj hjb _ => by exfalso; omega, by omega⟩
      have h_skaf₁ : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 1) s₁.flowLevel := by
        refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
          fun j hj hjb _ => by exfalso; omega, by omega⟩
      have h_body_rawN : s₂.tokens[s_state.tokens.size]? = s₁.tokens[s_state.tokens.size]? := by
        have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 1)
          (by omega) h_skaf₁ (by omega) s_state.tokens.size (by omega)
        rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
            Array.getElem?_eq_getElem (by omega), h_eq]
      have h_skaf₁' : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 2) s₁.flowLevel := by
        refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
          fun j hj hjb _ => by exfalso; omega, by omega⟩
      have h_body_rawN1 : s₂.tokens[s_state.tokens.size + 1]? = s₁.tokens[s_state.tokens.size + 1]? := by
        have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 2)
          (by omega) h_skaf₁' (by omega) (s_state.tokens.size + 1) (by omega)
        rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
            Array.getElem?_eq_getElem (by omega), h_eq]
      have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
      have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
        unfold StackEndLineOnLine at h_stack_endline₁ ⊢
        rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
      obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, h_skrestore₃, h_prefix₃⟩ :=
        scanNextToken_flow_close_mapping_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
          h_atol₂ h_stack_endline₂
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨'}' :: rest, s₂.col⟩ := by
        have : ['}'] ++ rest = '}' :: rest := by simp
        rwa [this] at h_corr₂
      obtain ⟨fmeTok, h_fme_val, h_close_push⟩ :=
        scanNextToken_flow_close_map_filtered_push s₂ rest h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
          h_fl₂_ge2 h_snt₃
      have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
      have h_fmc_all :=
        (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
          (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
      have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s_state s₁ '{'
          ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
          h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
      have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s₂ s₃ '}' rest
          h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
      have h_skey_eq : s₃.simpleKey = (saveSimpleKey s_state).simpleKey := by
        rw [h_skrestore₃, h_stack₂, h_stack_push₁]; simp [Array.back?_push]
      obtain ⟨_h_skp, _h_skt, _, _⟩ := saveSimpleKey_eval s_state h_ek h_ska
      have h_close_mono : s₂.tokens.size ≤ s₃.tokens.size := by
        have := ScannerCorrectness.scanNextToken_adds_tokens s₂ s₃ h_snt₃; omega
      have h_body_mono : s₁.tokens.size ≤ s₂.tokens.size := h_fmc₂.tokens_mono
      have h_s3_rawN? : s₃.tokens[s_state.tokens.size]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
        rw [h_prefix₃ s_state.tokens.size (by omega), h_body_rawN, h_s1_rawN]
      have h_s3_rawN1? : s₃.tokens[s_state.tokens.size + 1]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
        rw [h_prefix₃ (s_state.tokens.size + 1) (by omega), h_body_rawN1, h_s1_rawN1]
      have h_block_eq : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (fmsTok :: (bodyBlock ++ [fmeTok])) := by
        have h1 : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fmsTok] := by
          rw [h_open_push, Array.toList_push]
        have h3 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList ++ [fmeTok] := by
          rw [h_close_push, Array.toList_push]
        rw [h3, h_body_append, h1]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have h_N1 : s_state.tokens.size < s₃.tokens.size := by omega
      have h_pref : ∀ j, j < s_state.tokens.size → s₃.tokens[j]? = s_state.tokens[j]? := by
        intro j hj
        have hj2 : j < s₂.tokens.size := by omega
        have h_nc_open : ∀ t c', scanNextToken_preprocess s_state = .ok (some (t, c')) → c' ≠ ':' :=
          no_colon_of_preprocess_flow s_state '{' ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
            s_state.col h_corr_state_cons h_flow (by decide) (by decide) (by decide) (by decide)
        have ho := scanNextToken_at_non_colon_preserves_positions s_state s₁ h_snt₁ h_nc_open j hj
        have hb := FlowMonoChain_preserves_raw_prefix h_fmc₂ s_state.tokens.size (by omega)
          h_skaf_N (by omega) j hj
        have hc := h_prefix₃ j hj2
        rw [hc, Array.getElem?_eq_getElem hj2, hb, ho, Array.getElem?_eq_getElem hj]
      have h_ph_false :
          (fun (t : Positioned YamlToken) => t.val != .placeholder) (s₃.tokens[s_state.tokens.size]'h_N1) = false := by
        have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'h_N1) :=
          Array.getElem?_eq_getElem h_N1
        have heq := Option.some.inj (h_some.symm.trans h_s3_rawN?)
        rw [heq]; rfl
      have h_take :
          (s₃.tokens.toList.take (s_state.tokens.size + 1)).filter (fun t => t.val != .placeholder)
            = (s_state.tokens.filter (fun t => t.val != .placeholder)).toList :=
        block_take_eq_of_getElem? s₃.tokens s_state.tokens s_state.tokens.size
          (fun t => t.val != .placeholder) rfl h_N1 h_pref h_ph_false
      have h_wrap := wrap_map_block fmsTok fmeTok bodyBlock h_fms_val h_fme_val h_body_wb
      refine ⟨(1 + n₂) + 1, s₃, fmsTok :: (bodyBlock ++ [fmeTok]),
        (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
        h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_atol₃, h_endline₃, ?_, h_fmc_all,
        h_ska₃, ?_, ?_, ?_, ?_, ?_, h_block_eq, h_take, h_wrap.1⟩
      · rw [h_fl₃, h_fl₂, h_fl₁]; omega
      · rw [h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek₃, h_ek₂, h_ek₁]
      · rw [h_col₃]; omega
      · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
      · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
      · rw [_h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack₃, h_stack₂, h_stack_pop₁]
      · rw [h_skey_eq]; exact _h_skp
      · rw [h_skey_eq]; exact _h_skt
      · omega
      · intro hh
        have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'hh) :=
          Array.getElem?_eq_getElem hh
        have := Option.some.inj (h_some.symm.trans h_s3_rawN?); rw [this]
      · intro hh
        have h_some : s₃.tokens[s_state.tokens.size + 1]? = some (s₃.tokens[s_state.tokens.size + 1]'hh) :=
          Array.getElem?_eq_getElem hh
        have := Option.some.inj (h_some.symm.trans h_s3_rawN1?); rw [this]

theorem emit_scans_in_flow_block (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : EmitScansInFlowBlock v :=
  (emit_scans_block_combined v hg).1

theorem emit_scans_in_flow_saved_key_block (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : EmitScansInFlowSavedKeyBlock v :=
  (emit_scans_block_combined v hg).2

/-! ### §G.balance.bridge.assemble — sequence-body `SafeBody` producer

The `.assemble` bridge for flow **sequences**: scanning `emitList items` (the comma-
separated body between `[` and `]`) produces a filtered-LIST `block` that is not just
`WellBracketed` but a full `SafeBody ContentStartTok` — nonempty `EntrySafe` entries
(each item's `emit v` block) with content-start heads, separated by single delta-`0`
`.flowEntry` tokens.  `SafeBody` is exactly what `SafeBody_array_flowEntry` (and
`SafeBody.head_Q`) consume to discharge both halves of the flow-sequence body-token
characterization (first new filtered token is a content start; the token after every
outer-level balance-`0` `.flowEntry` is a content start) — so this producer lets
`emitList_body_filtered_characterization` be proven directly off the block layer with
no `SavedKeyDoesntResolve` substrate and no two-chain reconciliation.

The proof mirrors `emitList_scans_block_nonempty` (same per-item / comma / preprocess /
recurse decomposition) but additionally accumulates the `SafeBody`: each item's
`EmitScansInFlowBlock` already exposes `EntrySafe block` and a content-start head, and
the comma contributes the `.flowEntry` separator — exactly the `SafeBody.single` /
`SafeBody.cons` inputs. -/
theorem emitList_scans_safebody (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlowBlock v) :
    ∀ (s : ScannerState) (rest_chars : List Char),
      ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest_chars, s.col⟩ →
      s.inFlow = true →
      s.flowLevel > 0 →
      s.currentIndent < 0 →
      s.col > 0 →
      s.explicitKeyLine = none →
      AllTokensOnLine s s.line →
      EndLineOnLine s →
      s.simpleKeyStack.size = s.flowLevel →
      ∃ n s' block,
        ScanChainGrew (fun t => t.val != .placeholder) s n s'
        ∧ ScannerSurfCorr s' ⟨rest_chars, s'.col⟩
        ∧ s'.flowLevel = s.flowLevel
        ∧ s'.directivesPresent = s.directivesPresent
        ∧ s'.indents = s.indents
        ∧ s'.explicitKeyLine = s.explicitKeyLine
        ∧ s'.col > 0
        ∧ s'.inFlow = true
        ∧ s'.currentIndent < 0
        ∧ s'.line = s.line
        ∧ AllTokensOnLine s' s'.line
        ∧ EndLineOnLine s'
        ∧ s'.simpleKeyStack = s.simpleKeyStack
        ∧ FlowMonoChain s.flowLevel s n s'
        ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
        ∧ WellBracketed block
        ∧ SafeBody ContentStartTok block := by
  induction items with
  | nil => contradiction
  | cons v tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
    match tail, ih with
    | [], _ =>
      have h_eq : (emit.emitList [v]).toList = (emit v).toList := by
        simp only [emit.emitList]
      rw [h_eq] at hcorr
      obtain ⟨n, s', block, h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow',
              h_indent', h_line_v, _h_ska, _h_last, h_atol', h_endline', h_stack', h_fmc',
              h_block_eq, h_wb, h_es, h_cs⟩ :=
        h_all v (.head _) s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      obtain ⟨h_cs_ne, h_cs_val⟩ := h_cs
      exact ⟨n, s', block, h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow',
        h_indent', h_line_v, h_atol', h_endline', h_stack', h_fmc', h_block_eq, h_wb,
        SafeBody.single block h_cs_ne h_es h_cs_val⟩
    | v' :: vs, ih =>
      have h_eq : (emit.emitList (v :: v' :: vs)).toList ++ rest_chars =
          (emit v).toList ++ ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
        simp [emit.emitList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan emit v via EmitScansInFlowBlock (item block `block₁`, with EntrySafe + head)
      have h_ev : EmitScansInFlowBlock v := h_all v (.head _)
      obtain ⟨n₁, s₁, block₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_flow₁,
              h_indent₁, _h_line₁, _h_ska₁, h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_block_eq₁, h_wb₁, h_es₁, h_cs₁⟩ :=
        h_ev s ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      obtain ⟨h_cs₁_ne, h_cs₁_val⟩ := h_cs₁
      -- Step 2: Scan ',' via scanNextToken_flow_comma (state) + push lemma (block)
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂⟩ :=
        scanNextToken_flow_comma s₁
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁
          h_last₁ h_atol₁ h_endline₁
      obtain ⟨feTok, h_feTok_val, h_comma_eq⟩ :=
        scanNextToken_flow_comma_filtered_push s₁
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ h_last₁ h_snt₂
      -- Step 3: Handle leading space via preprocessing equality
      obtain ⟨c, rest', h_first, h_nws, h_nlb, h_nc⟩ := emitList_first_char v' vs
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c :: (rest' ++ rest_chars), s₂.col⟩ := by
        have : ' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars =
            ' ' :: c :: (rest' ++ rest_chars) := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₂]; omega)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₂]; exact h_indent₁
      have h_s2_col : s₂.col > 0 := by rw [h_col₂]; omega
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c (rest' ++ rest_chars) h_corr₂_ws
          h_s2_flow h_nws h_nlb h_nc h_s2_indent
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit.emitList (v' :: vs)).toList ++ rest_chars, s₃.col⟩ := by
        have : c :: (rest' ++ rest_chars) = (emit.emitList (v' :: vs)).toList ++ rest_chars := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: Recursive scan of emitList (v' :: vs) from s₃ (tail block `block_rest`, with SafeBody)
      have h_tail_all : ∀ w ∈ v' :: vs, EmitScansInFlowBlock w :=
        fun w hw => h_all w (.tail _ hw)
      obtain ⟨n₃, s_end, block_rest, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc₃, h_block_eq_end, h_wb_rest, h_sb_rest⟩ :=
        ih (by simp) h_tail_all s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂, h_ek₁]; exact h_ek)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_stack_pp₃, h_stack₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
      -- Step 5: Lift chain for s₂ via preprocessing equality
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit.emitList (v' :: vs)).toList = [] := by
            match h_list : (emit.emitList (v' :: vs)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          exact absurd h_nil (emitList_toList_ne_nil v' vs)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain₃
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars), s₁.col⟩ := by
          have : [',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars =
              ',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ','
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      have h_fmc₃' : FlowMonoChain s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      -- Block accumulation: block = block₁ ++ [feTok] ++ block_rest
      have h_block_eq₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ (block₁ ++ [feTok]) := by
        have h_s3_s2 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp₃]
        rw [h_s3_s2, congrArg Array.toList h_comma_eq, Array.toList_push, h_block_eq₁,
            List.append_assoc]
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, block₁ ++ [feTok] ++ block_rest,
        h_arith ▸ h_chain_all, h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end,
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, ?_, ?_, ?_⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂, h_ek₁]
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack₂, h_stack₁]
      · -- block equation: s_end = s₃ ++ block_rest = s ++ (block₁ ++ [feTok]) ++ block_rest
        rw [h_block_eq_end, h_block_eq₃, List.append_assoc]
      · -- WellBracketed (block₁ ++ [feTok] ++ block_rest)
        exact WellBracketed_append _ _
          (WellBracketed_append _ _ h_wb₁
            (WellBracketed_singleton_delta_zero feTok (by rw [h_feTok_val]; exact flowBracketDelta_flowEntry)))
          h_wb_rest
      · -- SafeBody ContentStartTok (block₁ ++ [feTok] ++ block_rest)
        have h_reassoc : block₁ ++ [feTok] ++ block_rest = block₁ ++ feTok :: block_rest := by
          rw [List.append_assoc]; rfl
        rw [h_reassoc]
        exact SafeBody.cons block₁ feTok block_rest h_cs₁_ne h_es₁ h_cs₁_val h_feTok_val h_sb_rest

end L4YAML.Proofs.EmitterScannability
