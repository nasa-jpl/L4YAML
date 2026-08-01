/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Output.EmitterScannability.NonemptyStructure
import L4YAML.Proofs.Output.EmitterScannability.TokVals

/-!
# Value-determined scanner content pin (`emitTokVals`)

The PARALLEL value-determined mirror of the deep chain producers in
`NonemptyStructure.lean`: same chains, same state conjuncts, but the structural
conjuncts (`WellBracketed`/`WellTyped`/`EntrySafe`/`EntryUnit`/`RecEntryDeep`/
`ContentStartTok`/`OpenerAdj`/`SepAdj` — and for the body lemmas
`RecSeqBodyDeep`/`RecMapBodyDeep`) are REPLACED by the single conjunct
`block.map (·.val) = emitTokVals v` (resp. `emitTokVals.seqTokVals` /
`emitTokVals.mapTokVals` for the bodies).

The one brick swap relative to the structural model: the scalar leaf uses
`scanNextToken_flow_scalar_filtered_push_content` (WellBracketed.lean), whose
scalar `.val` is pinned to `.scalar content .doubleQuoted`, instead of the
existential `scanNextToken_flow_scalar_filtered_push`.

Whole-array wrappers replay open_init → body → close →
`scanFiltered_tokens_eq_of_chain_short_stack` (the R597/R607 replay), yielding
`tokens.toList.map (·.val) = .streamStart :: (emitTokVals v ++ [.streamEnd])`
for any `Grammable v`.
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

/-! ## Pair-generic unfolding helpers for `mapTokVals`

The body lemmas below manipulate pairs `p : YamlValue × YamlValue` without
destructuring them (mirroring the structural model, which uses `p.1`/`p.2`
throughout); these two rfl-by-eta lemmas restate the `mapTokVals` unfolding
equations in `p.1`/`p.2` form. -/

lemma mapTokVals_pair_singleton (p : YamlValue × YamlValue) :
    emitTokVals.mapTokVals [p]
      = .key :: (emitTokVals p.1 ++ (.value :: emitTokVals p.2)) := by
  obtain ⟨k, v⟩ := p; rfl

lemma mapTokVals_pair_cons (p q : YamlValue × YamlValue)
    (rest : List (YamlValue × YamlValue)) :
    emitTokVals.mapTokVals (p :: q :: rest)
      = (.key :: (emitTokVals p.1 ++ (.value :: emitTokVals p.2)))
          ++ (.flowEntry :: emitTokVals.mapTokVals (q :: rest)) := by
  obtain ⟨k, v⟩ := p; rfl

/-! ## A/B. The value-determined per-entry predicates

`EmitScansInFlowRecEntryDeep` / `EmitScansInFlowSavedKeyRecEntryDeep` with the
structural conjuncts replaced by `block.map (·.val) = emitTokVals v`. -/

/-- Value-determined mirror of `EmitScansInFlowRecEntryDeep`: every scan-state
    conjunct verbatim, structural conjuncts replaced by the content pin. -/
def EmitScansTokVals (v : YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit v).toList ++ rest, s.col⟩ →
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
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ s'.simpleKeyAllowed = false
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
      ∧ block.map (·.val) = emitTokVals v

/-- Value-determined mirror of `EmitScansInFlowSavedKeyRecEntryDeep`: every
    placeholder/simpleKey bookkeeping conjunct verbatim (they are load-bearing
    for the colon step), structural conjuncts replaced by the content pin. -/
def EmitScansSavedKeyTokVals (v : YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit v).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    s.simpleKeyAllowed = true →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s' block,
      ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
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
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.simpleKey.possible = true
      ∧ s'.simpleKey.tokenIndex = s.tokens.size
      ∧ s.tokens.size + 1 < s'.tokens.size
      ∧ (∀ (h : s.tokens.size < s'.tokens.size),
          (s'.tokens[s.tokens.size]'h).val = .placeholder)
      ∧ (∀ (h : s.tokens.size + 1 < s'.tokens.size),
          (s'.tokens[s.tokens.size + 1]'h).val = .placeholder)
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
      ∧ (s'.tokens.toList.take (s.tokens.size + 1)).filter (fun t => t.val != .placeholder)
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
      ∧ block.map (·.val) = emitTokVals v

/-! ## C. Sequence-body assembler (mirror of `emitList_scans_recseqbodyDeep`) -/

/-- Value-determined mirror of `emitList_scans_recseqbodyDeep`: the
    comma-separated body block of `emitList items` maps to
    `emitTokVals.seqTokVals items`. -/
lemma emitList_scans_tokvals (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansTokVals v) :
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
        ∧ block.map (·.val) = emitTokVals.seqTokVals items := by
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
              h_block_eq, h_pin⟩ :=
        h_all v (.head _) s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      exact ⟨n, s', block, h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow',
        h_indent', h_line_v, h_atol', h_endline', h_stack', h_fmc', h_block_eq,
        by rw [seqTokVals_singleton]; exact h_pin⟩
    | v' :: vs, ih =>
      have h_eq : (emit.emitList (v :: v' :: vs)).toList ++ rest_chars =
          (emit v).toList ++ ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
        simp [emit.emitList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan emit v via EmitScansTokVals (item block `block₁`, with the content pin)
      have h_ev : EmitScansTokVals v := h_all v (.head _)
      obtain ⟨n₁, s₁, block₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_flow₁,
              h_indent₁, _h_line₁, _h_ska₁, h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_block_eq₁, h_pin₁⟩ :=
        h_ev s ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
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
      -- Step 4: Recursive scan of emitList (v' :: vs) from s₃ (tail block `block_rest`)
      have h_tail_all : ∀ w ∈ v' :: vs, EmitScansTokVals w :=
        fun w hw => h_all w (.tail _ hw)
      obtain ⟨n₃, s_end, block_rest, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc₃, h_block_eq_end, h_pin_rest⟩ :=
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
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, ?_, ?_⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂, h_ek₁]
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack₂, h_stack₁]
      · -- block equation: s_end = s₃ ++ block_rest = s ++ (block₁ ++ [feTok]) ++ block_rest
        rw [h_block_eq_end, h_block_eq₃, List.append_assoc]
      · -- value pin: (block₁ ++ [feTok] ++ block_rest).map (·.val) = seqTokVals (v :: v' :: vs)
        rw [seqTokVals_cons_cons]
        simp only [List.map_append, List.map_cons, h_pin₁, h_feTok_val,
                   h_pin_rest, List.append_assoc, List.cons_append, List.nil_append]

/-! ## D. Mapping-body assembler (mirror of `emitPairList_scans_recmapbodyDeep`) -/

/-- Value-determined mirror of `emitPairList_scans_recmapbodyDeep`: the
    `", "`-separated key/value body block of `emitPairList pairs` maps to
    `emitTokVals.mapTokVals pairs`. -/
lemma emitPairList_scans_tokvals (pairs : List (YamlValue × YamlValue))
    (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansSavedKeyTokVals p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansTokVals p.2) :
    ∀ (s : ScannerState) (rest : List Char),
      ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩ →
      s.inFlow = true →
      s.flowLevel > 0 →
      s.currentIndent < 0 →
      s.col > 0 →
      s.explicitKeyLine = none →
      AllTokensOnLine s s.line →
      EndLineOnLine s →
      s.simpleKeyAllowed = true →
      s.simpleKeyStack.size = s.flowLevel →
      ∃ n s' block,
        ScanChainGrew (fun t => t.val != .placeholder) s n s'
        ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
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
        ∧ block.map (·.val) = emitTokVals.mapTokVals pairs
        ∧ 3 ≤ n := by
  induction pairs with
  | nil => contradiction
  | cons p tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
    match tail, ih with
    | [], _ =>
      have h_eq : (emit.emitPairList [p]).toList ++ rest_chars =
          (emit p.1).toList ++ ([':', ' '] ++ (emit p.2).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      have h_ek_key : EmitScansSavedKeyTokVals p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, block_k, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_ska₁, h_poss₁, h_tidx₁, h_szlt₁, _h_ph0₁, h_ph1₁, h_blockeq_k, h_take_k, h_pin_k⟩ :=
        h_ek_key s ([':', ' '] ++ (emit p.2).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
      have h_n₁_pos : 1 ≤ n₁ := by
        rcases Nat.eq_zero_or_pos n₁ with h0 | hpos
        · subst h0; rw [ScanChainGrew.eq_of_zero h_chain₁] at h_szlt₁; omega
        · exact hpos
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁ ((emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      have h_lt_k : s₁.simpleKey.tokenIndex + 1 < s₁.tokens.size := by rw [h_tidx₁]; exact h_szlt₁
      have h_ph_k : (s₁.tokens[s₁.simpleKey.tokenIndex + 1]'h_lt_k).val = .placeholder := by
        simp only [h_tidx₁]; exact h_ph1₁ h_szlt₁
      obtain ⟨s₂', pos_v, h_snt₂', h_block_colon⟩ :=
        scanNextToken_flow_value_block s₁ ((emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁ h_ska₁ h_poss₁ h_lt_k h_ph_k
      have h_s2_eq : s₂' = s₂ := Option.some.inj (Except.ok.inj (h_snt₂'.symm.trans h_snt₂))
      rw [h_s2_eq] at h_block_colon
      have h_hk : s.tokens.size + 1 < s₁.tokens.toList.length := by
        rw [Array.length_toList]; exact h_szlt₁
      have h_old : (fun t : Positioned YamlToken => t.val != .placeholder)
          (s₁.tokens.toList[s.tokens.size + 1]'h_hk) = false := by
        have hph := h_ph1₁ h_szlt₁
        simp only [Array.getElem_toList, hph]; rfl
      have h_full : s₁.tokens.toList.filter (fun t => t.val != .placeholder)
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block_k := by
        rw [← Array.toList_filter]; exact h_blockeq_k
      have h_drop : (s₁.tokens.toList.drop (s.tokens.size + 2)).filter
            (fun t => t.val != .placeholder) = block_k :=
        List_filter_drop_succ_of_take s₁.tokens.toList (s.tokens.size + 1)
          (fun t => t.val != .placeholder) h_hk h_old _ block_k h_take_k h_full
      rw [h_tidx₁, h_take_k, h_drop] at h_block_colon
      have h_block_kc : (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                (block_k ++ [⟨pos_v, .value, pos_v⟩])) := by
        rw [h_block_colon]; simp only [List.append_assoc, List.cons_append]
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c_v :: (rest_v ++ rest_chars), s₂.col⟩ := by
        have h_eq_chars : (' ' :: (emit p.2).toList ++ rest_chars) =
            (' ' :: c_v :: (rest_v ++ rest_chars)) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₂
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_v (rest_v ++ rest_chars) h_corr₂_ws
          h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++ rest_chars, s₃.col⟩ := by
        have h_eq_chars : (c_v :: (rest_v ++ rest_chars)) =
            ((emit p.2).toList ++ rest_chars) := by
          rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₃
      have h_ev : EmitScansTokVals p.2 := h_all_v p (.head _)
      obtain ⟨n_v, s_end, block_v, h_chain_v, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, _h_ska_v, _h_last_v,
              h_atol_end, h_endline_end, h_stack_end, h_fmc_v, h_blockeq_v, h_pin_v⟩ :=
        h_ev s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_stack_pp₃, h_stack_v₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n_v_pos : n_v ≥ 1 := by
        match n_v, h_chain_v with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.2).toList = [] := by
            match h_list : (emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n_v' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain_v
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (emit p.2).toList ++ rest_chars), s₁.col⟩ := by
          have : [':', ' '] ++ (emit p.2).toList ++ rest_chars =
              ':' :: (' ' :: (emit p.2).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (emit p.2).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      have h_fmc_v' : FlowMonoChain s.flowLevel s₃ (n_v' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc_v
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n_v' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc_v'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n_v' + 1)) = n₁ + 1 + (n_v' + 1) := by omega
      have h_block_end : (s_end.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ ((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) := by
        have h_s3_s2 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp₃]
        rw [h_blockeq_v, h_s3_s2, h_block_kc, List.append_assoc]
      refine ⟨n₁ + 1 + (n_v' + 1), s_end,
        (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ :: (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v,
        h_arith ▸ h_chain_all, h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end,
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, h_block_end, ?_, by omega⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack_v₂, h_stack₁]
      · -- value pin: ((.key :: (block_k ++ [.value])) ++ block_v).map = mapTokVals [p]
        rw [mapTokVals_pair_singleton]
        simp only [List.map_append, List.map_cons, h_pin_k, h_pin_v,
                   List.append_assoc, List.cons_append, List.nil_append]
    | p' :: ps, ih =>
      have h_eq : (emit.emitPairList (p :: p' :: ps)).toList ++ rest_chars =
          (emit p.1).toList ++ ([':', ' '] ++ (emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      have h_ek_key : EmitScansSavedKeyTokVals p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, block_k, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_ska₁, h_poss₁, h_tidx₁, h_szlt₁, _h_ph0₁, h_ph1₁, h_blockeq_k, h_take_k, h_pin_k⟩ :=
        h_ek_key s ([':', ' '] ++ (emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁
          ((emit p.2).toList ++ [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      have h_lt_k : s₁.simpleKey.tokenIndex + 1 < s₁.tokens.size := by rw [h_tidx₁]; exact h_szlt₁
      have h_ph_k : (s₁.tokens[s₁.simpleKey.tokenIndex + 1]'h_lt_k).val = .placeholder := by
        simp only [h_tidx₁]; exact h_ph1₁ h_szlt₁
      obtain ⟨s₂', pos_v, h_snt₂', h_block_colon⟩ :=
        scanNextToken_flow_value_block s₁
          ((emit p.2).toList ++ [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁ h_ska₁ h_poss₁ h_lt_k h_ph_k
      have h_s2_eq : s₂' = s₂ := Option.some.inj (Except.ok.inj (h_snt₂'.symm.trans h_snt₂))
      rw [h_s2_eq] at h_block_colon
      have h_hk : s.tokens.size + 1 < s₁.tokens.toList.length := by
        rw [Array.length_toList]; exact h_szlt₁
      have h_old : (fun t : Positioned YamlToken => t.val != .placeholder)
          (s₁.tokens.toList[s.tokens.size + 1]'h_hk) = false := by
        have hph := h_ph1₁ h_szlt₁
        simp only [Array.getElem_toList, hph]; rfl
      have h_full : s₁.tokens.toList.filter (fun t => t.val != .placeholder)
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block_k := by
        rw [← Array.toList_filter]; exact h_blockeq_k
      have h_drop : (s₁.tokens.toList.drop (s.tokens.size + 2)).filter
            (fun t => t.val != .placeholder) = block_k :=
        List_filter_drop_succ_of_take s₁.tokens.toList (s.tokens.size + 1)
          (fun t => t.val != .placeholder) h_hk h_old _ block_k h_take_k h_full
      rw [h_tidx₁, h_take_k, h_drop] at h_block_colon
      have h_block_kc : (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                (block_k ++ [⟨pos_v, .value, pos_v⟩])) := by
        rw [h_block_colon]; simp only [List.append_assoc, List.cons_append]
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₂.col⟩ := by
        have h_eq_chars : (' ' :: (emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) =
            (' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₂
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_v
          (rest_v ++ [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₂_ws h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars, s₃.col⟩ := by
        have h_eq_chars : (c_v :: (rest_v ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) =
            ((emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
          rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₃
      have h_ev : EmitScansTokVals p.2 := h_all_v p (.head _)
      have h_corr₃_assoc : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++ ([',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₃.col⟩ := by
        simp only [List.append_assoc] at h_corr₃' ⊢; exact h_corr₃'
      obtain ⟨n_v, s_v, block_v, h_chain_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v,
              h_ek_v, h_col_v, h_flow_v, h_indent_v, _h_line_v, _h_ska_v, h_last_v,
              h_atol_v, h_endline_v, h_stack_v, h_fmc_v, h_blockeq_v, h_pin_v⟩ :=
        h_ev s₃ ([',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₃_assoc
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_stack_pp₃, h_stack_v₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
      have h_snt_eq_v : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n_v_pos : n_v ≥ 1 := by
        match n_v, h_chain_v with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_v.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.2).toList = [] := by
            match h_list : (emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
      have h_filt_le_v : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                         (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws_v : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n_v' + 1) s_v :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_v h_filt_le_v h_chain_v
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₁.col⟩ := by
          have : [':', ' '] ++ (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      obtain ⟨s_c, h_snt_c, h_corr_c, h_fl_c, h_dp_c, h_ids_c, h_ek_c, h_col_c, _h_line_c, h_atol_c, h_endline_c, h_stack_c⟩ :=
        scanNextToken_flow_comma s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_atol_v h_endline_v
      obtain ⟨feTok, h_feTok_val, h_comma_eq⟩ :=
        scanNextToken_flow_comma_filtered_push s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_snt_c
      obtain ⟨h_ska_c_true, _h_sk_c_eq⟩ :=
        scanNextToken_flow_comma_simpleKey s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_snt_c
      obtain ⟨c_p, rest_p, h_first_p, h_nws_p, h_nlb_p, h_nc_p⟩ :=
        emitPairList_first_char p' ps
      have h_corr_c_ws : ScannerSurfCorr s_c
          ⟨' ' :: c_p :: (rest_p ++ rest_chars), s_c.col⟩ := by
        have : ' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
            ' ' :: c_p :: (rest_p ++ rest_chars) := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_c
      have h_sc_flow : s_c.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_c]; omega)
      have h_sc_indent : s_c.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids_c]; exact h_indent_v
      obtain ⟨s_pp, h_corr_pp, h_flow_pp, h_fl_pp, h_indent_pp, h_col_pp,
              h_dp_pp, h_ids_pp, h_ek_pp, _h_line_pp, h_pp_eq_r, h_atol_transfer_pp, h_endline_transfer_pp, h_stack_pp, h_toks_pp, h_sk_pp, h_ska_pp⟩ :=
        scanNextToken_preprocess_flow_ws1 s_c c_p (rest_p ++ rest_chars) h_corr_c_ws
          h_sc_flow h_nws_p h_nlb_p h_nc_p h_sc_indent
      have h_corr_pp' : ScannerSurfCorr s_pp
          ⟨(emit.emitPairList (p' :: ps)).toList ++ rest_chars, s_pp.col⟩ := by
        have : c_p :: (rest_p ++ rest_chars) =
            (emit.emitPairList (p' :: ps)).toList ++ rest_chars := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_pp
      have h_tail_all_k : ∀ q ∈ p' :: ps, EmitScansSavedKeyTokVals q.1 :=
        fun q hq => h_all_k q (.tail _ hq)
      have h_tail_all_v : ∀ q ∈ p' :: ps, EmitScansTokVals q.2 :=
        fun q hq => h_all_v q (.tail _ hq)
      obtain ⟨n_r, s_end, block_rest, h_chain_r, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc_r, h_blockeq_rest, h_pin_rest, h_n_r_ge3⟩ :=
        ih (by simp) h_tail_all_k h_tail_all_v s_pp rest_chars h_corr_pp'
          h_flow_pp
          (by rw [h_fl_pp, h_fl_c]; rw [h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent_pp]; exact h_sc_indent)
          (by rw [h_col_pp]; omega)
          (by rw [h_ek_pp, h_ek_c, h_ek_v, h_ek₃]; exact h_ek₂)
          (h_atol_transfer_pp h_atol_c)
          (h_endline_transfer_pp h_endline_c)
          (by rw [h_ska_pp]; exact h_ska_c_true)
          (by rw [h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁,
              h_sync, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁])
      have h_snt_eq_r : scanNextToken s_c = scanNextToken s_pp :=
        scanNextToken_eq_of_preprocess s_c s_pp h_pp_eq_r
      have h_n_r_pos : n_r ≥ 1 := by omega
      obtain ⟨n_r', rfl⟩ : ∃ k, n_r = k + 1 := ⟨n_r - 1, by omega⟩
      have h_filt_le_r : (s_c.tokens.filter (fun t => t.val != .placeholder)).size ≤
                         (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp]; exact Nat.le_refl _
      have h_chain_ws_r : ScanChainGrew (fun t => t.val != .placeholder)
            s_c (n_r' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_r h_filt_le_r h_chain_r
      have h_grew_c : (s_c.tokens.filter (fun t => t.val != .placeholder)).size >
                      (s_v.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr_v_cons : ScannerSurfCorr s_v
            ⟨',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s_v.col⟩ := by
          have : [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr_v
        exact scanNextToken_filtered_grows_in_flow s_v s_c ','
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v_cons h_flow_v h_indent_v h_col_v
          (by decide) (by decide) (by decide) h_snt_c
      have h_fmc_v' : FlowMonoChain s.flowLevel s₃ (n_v' + 1) s_v :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc_v
      have h_fmc_ws_v : FlowMonoChain s.flowLevel s₂ (n_v' + 1) s_v :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_v (by omega) h_fmc_v'
      have h_fmc_r' : FlowMonoChain s.flowLevel s_pp (n_r' + 1) s_end :=
        (show s.flowLevel = s_pp.flowLevel from by omega) ▸ h_fmc_r
      have h_fmc_ws_r : FlowMonoChain s.flowLevel s_c (n_r' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_r (by omega) h_fmc_r'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans
          (h_fmc_ws_v.trans
            ((FlowMonoChain.single h_snt_c (by omega) (by omega)).trans h_fmc_ws_r)))
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans
          (h_chain_ws_v.trans
            ((ScanChainGrew.single h_snt_c h_grew_c).trans h_chain_ws_r)))
      have h_arith : n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) =
          n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1) := by omega
      have h_block_end : (s_end.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ ((((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) ++ block_rest) := by
        have h_s3_s2 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp₃]
        have h_block_v_end : (s_v.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s.tokens.filter (fun t => t.val != .placeholder)).toList
              ++ ((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) := by
          rw [h_blockeq_v, h_s3_s2, h_block_kc, List.append_assoc]
        have h_block_c_end : (s_c.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s.tokens.filter (fun t => t.val != .placeholder)).toList
              ++ (((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) := by
          rw [congrArg Array.toList h_comma_eq, Array.toList_push, h_block_v_end, List.append_assoc]
        have h_s_pp_c : (s_pp.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s_c.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp]
        rw [h_blockeq_rest, h_s_pp_c, h_block_c_end, List.append_assoc]
      refine ⟨n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1), s_end,
        (((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ :: (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) ++ block_rest,
        h_arith ▸ h_chain_all, h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end,
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, h_block_end, ?_, by omega⟩
      · rw [h_fl_end, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids_pp, h_ids_c, h_ids_v, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek_pp, h_ek_c, h_ek_v, h_ek₃]; exact h_ek₂.trans h_ek.symm
      · rw [h_line_end, _h_line_pp, _h_line_c, _h_line_v, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁]
      · -- value pin: ((entry ++ [feTok]) ++ block_rest).map = mapTokVals (p :: p' :: ps)
        rw [mapTokVals_pair_cons]
        simp only [List.map_append, List.map_cons, h_pin_k, h_pin_v, h_feTok_val,
                   h_pin_rest, List.append_assoc, List.cons_append, List.nil_append]

/-! ## E. The value-determined per-entry producer (mirror of
`emit_scans_in_flow_rec_entry_both_deep`) -/

/-- Value-determined per-entry producer: for any `Grammable v`, scanning
    `emit v` from any admissible in-flow scanner state appends a block whose
    `.val`-run is exactly `emitTokVals v` (both the plain and the saved-key
    chain shapes). Same `Grammable` induction as the structural producer, with
    the scalar leaf swapped to the content-pinned
    `scanNextToken_flow_scalar_filtered_push_content`. -/
lemma emit_scans_tokvals_both (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) :
    EmitScansTokVals v ∧ EmitScansSavedKeyTokVals v := by
  induction hg with
  | scalar sc _ h =>
      refine ⟨?_, ?_⟩
      · intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline _h_sync
        have h_chars : (emit (.scalar sc)).toList ++ rest =
            ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest := by
          simp only [emit, emitScalar, String.toList_append]; rfl
        have hcorr' : ScannerSurfCorr s_state
            ⟨['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest, s_state.col⟩ := by
          rwa [← h_chars]
        obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_tok', h_ska', _h_line', h_atol', h_endline', h_stack'⟩ :=
          scanNextToken_flow_scanDoubleQuoted s_state sc.content rest hcorr' h_flow h_indent h_col
            h_atol h_endline
        obtain ⟨tok, h_tok_val, h_push⟩ :=
          scanNextToken_flow_scalar_filtered_push_content s_state sc.content rest
            hcorr' h_flow h_indent h_col h_snt
        have h_grew : (s'.tokens.filter (fun t => t.val != .placeholder)).size >
                      (s_state.tokens.filter (fun t => t.val != .placeholder)).size := by
          rw [h_push]; simp [Array.size_push]
        refine ⟨1, s', [tok], ScanChainGrew.single h_snt h_grew, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', ?_, ?_, _h_line', h_ska', h_tok', h_atol', h_endline', h_stack',
          FlowMonoChain.single h_snt (Nat.le.refl) (by omega), ?_, ?_⟩
        · unfold ScannerState.inFlow; rw [h_fl']
          unfold ScannerState.inFlow at h_flow; exact h_flow
        · unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent
        · rw [h_push, Array.toList_push]
        · simp only [List.map_cons, List.map_nil, h_tok_val]
          rfl
      · intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska _h_sync
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
        obtain ⟨tok, h_tok_val, h_push⟩ :=
          scanNextToken_flow_scalar_filtered_push_content s_state sc.content rest
            hcorr' h_flow h_indent h_col h_snt''
        have h_grew : (s''.tokens.filter (fun t => t.val != .placeholder)).size >
                      (s_state.tokens.filter (fun t => t.val != .placeholder)).size := by
          rw [h_push]; simp [Array.size_push]
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
        · simp only [List.map_cons, List.map_nil, h_tok_val]
          rfl
  | sequence style items tag anchor _ h ih =>
      refine ⟨?_, ?_⟩
      · intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
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
        have h_corr₁_assoc : ScannerSurfCorr s₁
            ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
          rw [List.append_assoc] at h_corr₁; exact h_corr₁
        obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                h_body_append, h_body_pin⟩ :
            (∃ n₂ s₂ bodyBlock,
              ScanChainGrew (fun t => t.val != .placeholder) s₁ n₂ s₂
              ∧ ScannerSurfCorr s₂ ⟨[']'] ++ rest, s₂.col⟩
              ∧ s₂.flowLevel = s₁.flowLevel
              ∧ s₂.directivesPresent = s₁.directivesPresent
              ∧ s₂.indents = s₁.indents
              ∧ s₂.explicitKeyLine = s₁.explicitKeyLine
              ∧ s₂.col > 0
              ∧ s₂.inFlow = true
              ∧ s₂.currentIndent < 0
              ∧ s₂.line = s₁.line
              ∧ AllTokensOnLine s₂ s₂.line
              ∧ EndLineOnLine s₂
              ∧ s₂.simpleKeyStack = s₁.simpleKeyStack
              ∧ FlowMonoChain s₁.flowLevel s₁ n₂ s₂
              ∧ (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
                  = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList ++ bodyBlock
              ∧ bodyBlock.map (·.val) = emitTokVals.seqTokVals items.toList) := by
          match h_list : items.toList with
          | [] =>
            refine ⟨0, s₁, [], .zero, ?_, rfl, rfl, rfl, rfl, h_s1_col, h_s1_inflow, h_s1_indent, rfl,
                    h_atol₁, h_endline₁, rfl, .zero (Nat.le.refl), ?_, ?_⟩
            · have h_e : (emit.emitList items.toList).toList ++ ([']'] ++ rest) = [']'] ++ rest := by
                rw [h_list]; simp only [emit.emitList]; rfl
              rw [h_e] at h_corr₁_assoc; exact h_corr₁_assoc
            · simp
            · simp
          | w :: ws =>
            have h_all_rec : ∀ u ∈ (w :: ws), EmitScansTokVals u := fun u hu => by
              have hu' : u ∈ items.toList := h_list ▸ hu
              have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hu'
              have h_sz : i < items.size := by rwa [Array.length_toList] at hi
              exact h_eq ▸ (ih ⟨i, h_sz⟩).1
            obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                    h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                    h_body_append, h_body_pin⟩ :=
              emitList_scans_tokvals (w :: ws) (by simp) h_all_rec s₁ ([']'] ++ rest)
                (h_list ▸ h_corr₁_assoc) h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
                (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_s1_sync
            exact ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                   h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                   h_body_append, h_body_pin⟩
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
        refine ⟨(1 + n₂) + 1, s₃, fssTok :: (bodyBlock ++ [fseTok]),
          (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
          h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all,
          h_block_eq, ?_⟩
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
        · -- value pin: the wrapped block maps to emitTokVals (.sequence …)
          simp only [List.map_cons, List.map_append, List.map_nil, h_fss_val, h_fse_val,
                     h_body_pin, emitTokVals]
      · intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
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
        have h_corr₁_assoc : ScannerSurfCorr s₁
            ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
          rw [List.append_assoc] at h_corr₁; exact h_corr₁
        obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                h_body_append, h_body_pin⟩ :
            (∃ n₂ s₂ bodyBlock,
              ScanChainGrew (fun t => t.val != .placeholder) s₁ n₂ s₂
              ∧ ScannerSurfCorr s₂ ⟨[']'] ++ rest, s₂.col⟩
              ∧ s₂.flowLevel = s₁.flowLevel
              ∧ s₂.directivesPresent = s₁.directivesPresent
              ∧ s₂.indents = s₁.indents
              ∧ s₂.explicitKeyLine = s₁.explicitKeyLine
              ∧ s₂.col > 0
              ∧ s₂.inFlow = true
              ∧ s₂.currentIndent < 0
              ∧ s₂.line = s₁.line
              ∧ AllTokensOnLine s₂ s₂.line
              ∧ EndLineOnLine s₂
              ∧ s₂.simpleKeyStack = s₁.simpleKeyStack
              ∧ FlowMonoChain s₁.flowLevel s₁ n₂ s₂
              ∧ (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
                  = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList ++ bodyBlock
              ∧ bodyBlock.map (·.val) = emitTokVals.seqTokVals items.toList) := by
          match h_list : items.toList with
          | [] =>
            refine ⟨0, s₁, [], .zero, ?_, rfl, rfl, rfl, rfl, h_s1_col, h_s1_inflow, h_s1_indent, rfl,
                    h_atol₁, h_endline₁, rfl, .zero (Nat.le.refl), ?_, ?_⟩
            · have h_e : (emit.emitList items.toList).toList ++ ([']'] ++ rest) = [']'] ++ rest := by
                rw [h_list]; simp only [emit.emitList]; rfl
              rw [h_e] at h_corr₁_assoc; exact h_corr₁_assoc
            · simp
            · simp
          | w :: ws =>
            have h_all_rec : ∀ u ∈ (w :: ws), EmitScansTokVals u := fun u hu => by
              have hu' : u ∈ items.toList := h_list ▸ hu
              have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hu'
              have h_sz : i < items.size := by rwa [Array.length_toList] at hi
              exact h_eq ▸ (ih ⟨i, h_sz⟩).1
            obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                    h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                    h_body_append, h_body_pin⟩ :=
              emitList_scans_tokvals (w :: ws) (by simp) h_all_rec s₁ ([']'] ++ rest)
                (h_list ▸ h_corr₁_assoc) h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
                (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_stack_size₁
            exact ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                   h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                   h_body_append, h_body_pin⟩
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
        refine ⟨(1 + n₂) + 1, s₃, fssTok :: (bodyBlock ++ [fseTok]),
          (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
          h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_atol₃, h_endline₃, ?_, h_fmc_all,
          h_ska₃, ?_, ?_, ?_, ?_, ?_, h_block_eq, h_take, ?_⟩
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
        · -- value pin: the wrapped block maps to emitTokVals (.sequence …)
          simp only [List.map_cons, List.map_append, List.map_nil, h_fss_val, h_fse_val,
                     h_body_pin, emitTokVals]
  | mapping style pairs tag anchor _ _hk _hv ihk ihv =>
      refine ⟨?_, ?_⟩
      · intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
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
        have h_corr₁_assoc : ScannerSurfCorr s₁
            ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
          rw [List.append_assoc] at h_corr₁; exact h_corr₁
        obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                h_body_append, h_body_pin⟩ :
            (∃ n₂ s₂ bodyBlock,
              ScanChainGrew (fun t => t.val != .placeholder) s₁ n₂ s₂
              ∧ ScannerSurfCorr s₂ ⟨['}'] ++ rest, s₂.col⟩
              ∧ s₂.flowLevel = s₁.flowLevel
              ∧ s₂.directivesPresent = s₁.directivesPresent
              ∧ s₂.indents = s₁.indents
              ∧ s₂.explicitKeyLine = s₁.explicitKeyLine
              ∧ s₂.col > 0
              ∧ s₂.inFlow = true
              ∧ s₂.currentIndent < 0
              ∧ s₂.line = s₁.line
              ∧ AllTokensOnLine s₂ s₂.line
              ∧ EndLineOnLine s₂
              ∧ s₂.simpleKeyStack = s₁.simpleKeyStack
              ∧ FlowMonoChain s₁.flowLevel s₁ n₂ s₂
              ∧ (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
                  = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList ++ bodyBlock
              ∧ bodyBlock.map (·.val) = emitTokVals.mapTokVals pairs.toList) := by
          match h_list : pairs.toList with
          | [] =>
            refine ⟨0, s₁, [], .zero, ?_, rfl, rfl, rfl, rfl, h_s1_col, h_s1_inflow, h_s1_indent, rfl,
                    h_atol₁, h_endline₁, rfl, .zero (Nat.le.refl), ?_, ?_⟩
            · have h_e : (emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest) = ['}'] ++ rest := by
                rw [h_list]; simp only [emit.emitPairList]; rfl
              rw [h_e] at h_corr₁_assoc; exact h_corr₁_assoc
            · simp
            · simp
          | p :: ps =>
            have h_all_k : ∀ q ∈ (p :: ps), EmitScansSavedKeyTokVals q.1 := fun q hq => by
              have hq' : q ∈ pairs.toList := h_list ▸ hq
              have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hq'
              have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
              exact h_eq ▸ (ihk ⟨i, h_sz⟩).2
            have h_all_v : ∀ q ∈ (p :: ps), EmitScansTokVals q.2 := fun q hq => by
              have hq' : q ∈ pairs.toList := h_list ▸ hq
              have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hq'
              have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
              exact h_eq ▸ (ihv ⟨i, h_sz⟩).1
            obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                    h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                    h_body_append, h_body_pin, _h_n_ge3⟩ :=
              emitPairList_scans_tokvals (p :: ps) (by simp) h_all_k h_all_v s₁ (['}'] ++ rest)
                (h_list ▸ h_corr₁_assoc) h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
                (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_s1_ska h_s1_sync
            exact ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                   h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                   h_body_append, h_body_pin⟩
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
        refine ⟨(1 + n₂) + 1, s₃, fmsTok :: (bodyBlock ++ [fmeTok]),
          (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
          h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all,
          h_block_eq, ?_⟩
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
        · -- value pin: the wrapped block maps to emitTokVals (.mapping …)
          simp only [List.map_cons, List.map_append, List.map_nil, h_fms_val, h_fme_val,
                     h_body_pin, emitTokVals]
      · intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
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
        have h_corr₁_assoc : ScannerSurfCorr s₁
            ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
          rw [List.append_assoc] at h_corr₁; exact h_corr₁
        obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                h_body_append, h_body_pin⟩ :
            (∃ n₂ s₂ bodyBlock,
              ScanChainGrew (fun t => t.val != .placeholder) s₁ n₂ s₂
              ∧ ScannerSurfCorr s₂ ⟨['}'] ++ rest, s₂.col⟩
              ∧ s₂.flowLevel = s₁.flowLevel
              ∧ s₂.directivesPresent = s₁.directivesPresent
              ∧ s₂.indents = s₁.indents
              ∧ s₂.explicitKeyLine = s₁.explicitKeyLine
              ∧ s₂.col > 0
              ∧ s₂.inFlow = true
              ∧ s₂.currentIndent < 0
              ∧ s₂.line = s₁.line
              ∧ AllTokensOnLine s₂ s₂.line
              ∧ EndLineOnLine s₂
              ∧ s₂.simpleKeyStack = s₁.simpleKeyStack
              ∧ FlowMonoChain s₁.flowLevel s₁ n₂ s₂
              ∧ (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
                  = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList ++ bodyBlock
              ∧ bodyBlock.map (·.val) = emitTokVals.mapTokVals pairs.toList) := by
          match h_list : pairs.toList with
          | [] =>
            refine ⟨0, s₁, [], .zero, ?_, rfl, rfl, rfl, rfl, h_s1_col, h_s1_inflow, h_s1_indent, rfl,
                    h_atol₁, h_endline₁, rfl, .zero (Nat.le.refl), ?_, ?_⟩
            · have h_e : (emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest) = ['}'] ++ rest := by
                rw [h_list]; simp only [emit.emitPairList]; rfl
              rw [h_e] at h_corr₁_assoc; exact h_corr₁_assoc
            · simp
            · simp
          | p :: ps =>
            have h_all_k : ∀ q ∈ (p :: ps), EmitScansSavedKeyTokVals q.1 := fun q hq => by
              have hq' : q ∈ pairs.toList := h_list ▸ hq
              have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hq'
              have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
              exact h_eq ▸ (ihk ⟨i, h_sz⟩).2
            have h_all_v : ∀ q ∈ (p :: ps), EmitScansTokVals q.2 := fun q hq => by
              have hq' : q ∈ pairs.toList := h_list ▸ hq
              have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hq'
              have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
              exact h_eq ▸ (ihv ⟨i, h_sz⟩).1
            obtain ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                    h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                    h_body_append, h_body_pin, _h_n_ge3⟩ :=
              emitPairList_scans_tokvals (p :: ps) (by simp) h_all_k h_all_v s₁ (['}'] ++ rest)
                (h_list ▸ h_corr₁_assoc) h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
                (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁ h_s1_ska h_stack_size₁
            exact ⟨n₂, s₂, bodyBlock, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂,
                   h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂,
                   h_body_append, h_body_pin⟩
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
        refine ⟨(1 + n₂) + 1, s₃, fmsTok :: (bodyBlock ++ [fmeTok]),
          (ScanChainGrew.single h_snt₁ h_grew₁).trans (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
          h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_atol₃, h_endline₃, ?_, h_fmc_all,
          h_ska₃, ?_, ?_, ?_, ?_, ?_, h_block_eq, h_take, ?_⟩
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
        · -- value pin: the wrapped block maps to emitTokVals (.mapping …)
          simp only [List.map_cons, List.map_append, List.map_nil, h_fms_val, h_fme_val,
                     h_body_pin, emitTokVals]

/-- Value-side projection of the combined producer. -/
lemma emit_scans_tokvals (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : EmitScansTokVals v :=
  (emit_scans_tokvals_both v hg).1

/-- Saved-key-side projection of the combined producer. -/
lemma emit_scans_saved_key_tokvals (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : EmitScansSavedKeyTokVals v :=
  (emit_scans_tokvals_both v hg).2

/-! ## F. Whole-array wrappers

Chain replays open_init → body → outermost close →
`scanFiltered_tokens_eq_of_chain_short_stack` (the R597/R607 replay shape),
pinning the ENTIRE filtered `.val`-run of a standalone emission. -/

/-- Whole-array `.val`-run pin for a standalone non-empty flow sequence. -/
lemma scanFiltered_emitSeq_tokvals
    (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansTokVals v)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items ++ "]") = .ok tokens) :
    tokens.toList.map (·.val)
      = .streamStart :: (.flowSequenceStart ::
          (emitTokVals.seqTokVals items ++ [.flowSequenceEnd, .streamEnd])) := by
  let input := "[" ++ emit.emitList items ++ "]"
  have h_toList : input.toList = '[' :: (emit.emitList items).toList ++ [']'] := by
    simp only [input, String.toList_append]; rfl
  -- ═══ Step 1: open bracket → s₁ ═══
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, _h_sk₁, h_filt₁,
          h_sync₁, _h_ska₁, _h_ssv₁⟩ :=
    scanNextToken_flow_open_init input ((emit.emitList items).toList ++ [']']) h_toList
  -- ═══ Step 2: body scan via emitList_scans_tokvals → s₂ and body block ═══
  obtain ⟨_n₂, s₂, block, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, _h_ek₂, h_col₂, h_inflow₂,
          h_indent₂, _h_line₂, _h_atol₂, _h_endline₂, _h_stack₂, _h_fmc₂, h_block_eq₂, h_pin⟩ :=
    emitList_scans_tokvals items h_ne h_all s₁ [']']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_sync₁
  -- ═══ Step 3: close bracket → s₃ ═══
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fse, h_tok_fse_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_seq_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
      (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
  -- ═══ Step 4: chain composition + token equation ═══
  have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
  have h_chain_all := (ScanChain.single h_snt₁).trans
    (h_chain₂.toScanChain.trans (ScanChain.single h_snt₃))
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '﻿' := by
    have h_chars := chars_from_zero_toList input
    rw [h_toList] at h_chars
    have h_corr0 := initial_corr input _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '[' ((emit.emitList items).toList ++ [']']) 0 h_corr0
    rw [h_pk]; decide
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder)) :=
    scanFiltered_tokens_eq_of_chain_short_stack input _ s₃ _ rfl h_no_bom
      h_chain_all h_eof h_fl₃ h_dp₃
      (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
      h_indents_small
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) := by
    have h_scan' : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at h_scan'; exact (Except.ok.inj h_scan').symm
  -- ═══ Step 5: decompose token array and assemble the `.val` run ═══
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) =
      (s₃.tokens.filter (fun t => t.val != .placeholder)).push
        { pos := s₃.currentPos, val := .streamEnd } := by
    rw [show (s₃.emit .streamEnd).tokens
          = s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } from rfl,
        Array.filter_push]
    rfl
  have h_tokens_decomp : tokens = ((s₂.tokens.filter (fun t => t.val != .placeholder)).push tok_fse).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  have h_s1_vals : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
      = [.streamStart, .flowSequenceStart] := by
    rw [← Array.toList_map, h_filt₁]
  have h_tlist : tokens.toList
      = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
        ++ (block ++ [tok_fse, { pos := s₃.currentPos, val := .streamEnd }]) := by
    rw [h_tokens_decomp]
    simp only [Array.toList_push, h_block_eq₂, List.append_assoc, List.cons_append,
               List.nil_append]
  calc tokens.toList.map (·.val)
      = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
        ++ (block.map (·.val) ++ [tok_fse.val, YamlToken.streamEnd]) := by
        rw [h_tlist]; simp only [List.map_append, List.map_cons, List.map_nil]
    _ = [.streamStart, .flowSequenceStart]
        ++ (emitTokVals.seqTokVals items ++ [.flowSequenceEnd, .streamEnd]) := by
        rw [h_s1_vals, h_pin, h_tok_fse_val]
    _ = .streamStart :: (.flowSequenceStart ::
          (emitTokVals.seqTokVals items ++ [.flowSequenceEnd, .streamEnd])) := rfl

/-- Whole-array `.val`-run pin for a standalone non-empty flow mapping. -/
lemma scanFiltered_emitMap_tokvals
    (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansSavedKeyTokVals p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansTokVals p.2)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs ++ "}") = .ok tokens) :
    tokens.toList.map (·.val)
      = .streamStart :: (.flowMappingStart ::
          (emitTokVals.mapTokVals pairs ++ [.flowMappingEnd, .streamEnd])) := by
  let input := "{" ++ emit.emitPairList pairs ++ "}"
  have h_toList : input.toList = '{' :: (emit.emitPairList pairs).toList ++ ['}'] := by
    simp only [input, String.toList_append]; rfl
  -- ═══ Step 1: open brace → s₁ ═══
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, _h_sk₁, h_filt₁,
          h_sync₁, h_ska₁, _h_ssv₁⟩ :=
    scanNextToken_flow_open_mapping_init input ((emit.emitPairList pairs).toList ++ ['}']) h_toList
  -- ═══ Step 2: body scan via emitPairList_scans_tokvals → s₂ and body block ═══
  obtain ⟨_n₂, s₂, block, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, _h_ek₂, h_col₂, h_inflow₂,
          h_indent₂, _h_line₂, _h_atol₂, _h_endline₂, _h_stack₂, _h_fmc₂, h_block_eq₂, h_pin, _h_n3⟩ :=
    emitPairList_scans_tokvals pairs h_ne h_all_k h_all_v s₁ ['}']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_ska₁ h_sync₁
  -- ═══ Step 3: close brace → s₃ ═══
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fme, h_tok_fme_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_mapping_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
      (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
  -- ═══ Step 4: chain composition + token equation ═══
  have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
  have h_chain_all := (ScanChain.single h_snt₁).trans
    (h_chain₂.toScanChain.trans (ScanChain.single h_snt₃))
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '﻿' := by
    have h_chars := chars_from_zero_toList input
    rw [h_toList] at h_chars
    have h_corr0 := initial_corr input _ h_chars
    have ⟨h_pk, _⟩ :=
      peek_of_chars_cons _ '{' ((emit.emitPairList pairs).toList ++ ['}']) 0 h_corr0
    rw [h_pk]; decide
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder)) :=
    scanFiltered_tokens_eq_of_chain_short_stack input _ s₃ _ rfl h_no_bom
      h_chain_all h_eof h_fl₃ h_dp₃
      (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
      h_indents_small
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) := by
    have h_scan' : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at h_scan'; exact (Except.ok.inj h_scan').symm
  -- ═══ Step 5: decompose token array and assemble the `.val` run ═══
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) =
      (s₃.tokens.filter (fun t => t.val != .placeholder)).push
        { pos := s₃.currentPos, val := .streamEnd } := by
    rw [show (s₃.emit .streamEnd).tokens
          = s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } from rfl,
        Array.filter_push]
    rfl
  have h_tokens_decomp : tokens = ((s₂.tokens.filter (fun t => t.val != .placeholder)).push tok_fme).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  have h_s1_vals : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
      = [.streamStart, .flowMappingStart] := by
    rw [← Array.toList_map, h_filt₁]
  have h_tlist : tokens.toList
      = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
        ++ (block ++ [tok_fme, { pos := s₃.currentPos, val := .streamEnd }]) := by
    rw [h_tokens_decomp]
    simp only [Array.toList_push, h_block_eq₂, List.append_assoc, List.cons_append,
               List.nil_append]
  calc tokens.toList.map (·.val)
      = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
        ++ (block.map (·.val) ++ [tok_fme.val, YamlToken.streamEnd]) := by
        rw [h_tlist]; simp only [List.map_append, List.map_cons, List.map_nil]
    _ = [.streamStart, .flowMappingStart]
        ++ (emitTokVals.mapTokVals pairs ++ [.flowMappingEnd, .streamEnd]) := by
        rw [h_s1_vals, h_pin, h_tok_fme_val]
    _ = .streamStart :: (.flowMappingStart ::
          (emitTokVals.mapTokVals pairs ++ [.flowMappingEnd, .streamEnd])) := rfl

/-- **Whole-array value-determined pin.**  For any `Grammable v`, the filtered
    token `.val`-run of the standalone emission `emit v` is exactly
    `.streamStart :: (emitTokVals v ++ [.streamEnd])`. -/
lemma scanFiltered_emit_tokvals (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered (emit v) = .ok tokens) :
    tokens.toList.map (·.val) = .streamStart :: (emitTokVals v ++ [.streamEnd]) := by
  cases hg with
  | scalar sc iF hsc =>
    -- Standalone scalar: single scanDoubleQuoted step, then EOF; the init lemma
    -- already pins the filtered prefix to [streamStart, scalar content dq].
    obtain ⟨s₁, h_snt₁, h_peek₁, h_flow₁, h_dp₁, _h_tokmem, h_ids₁, h_filt₁⟩ :=
      scanNextToken_emitScalar_init sc.content
    have h_eof : scanNextToken s₁ = .ok none := scanNextToken_eof s₁ h_peek₁
    have h_chain : ScanChain ((ScannerState.mk' (emitScalar sc.content)).emit .streamStart) 1 s₁ :=
      ScanChain.single h_snt₁
    have h_no_bom : (ScannerState.mk' (emitScalar sc.content)).peek? ≠ some '﻿' := by
      have h_chars := chars_from_zero_toList (emitScalar sc.content)
      rw [emitScalar_toList] at h_chars
      have h_corr0 := initial_corr (emitScalar sc.content) _ h_chars
      have ⟨h_pk, _⟩ :=
        peek_of_chars_cons _ '"' ((escapeString sc.content).toList ++ ['"']) 0 h_corr0
      rw [h_pk]; decide
    have h_indents_small : s₁.indents.size ≤ 1 := by
      rw [h_ids₁]; decide
    have h_tok_eq : Scanner.scanFiltered (emitScalar sc.content) =
        .ok ((s₁.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder)) :=
      scanFiltered_tokens_eq_of_chain_short_stack (emitScalar sc.content) _ s₁ _ rfl h_no_bom
        h_chain h_eof h_flow₁ h_dp₁
        (ScanChain.fuel_bound _ _ _ _ rfl h_chain h_eof)
        h_indents_small
    have h_tokens_eq : tokens
        = (s₁.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) := by
      have h_scan' : Scanner.scanFiltered (emitScalar sc.content) = .ok tokens := h_scan
      rw [h_tok_eq] at h_scan'; exact (Except.ok.inj h_scan').symm
    have h_final_filter : (s₁.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) =
        (s₁.tokens.filter (fun t => t.val != .placeholder)).push
          { pos := s₁.currentPos, val := .streamEnd } := by
      rw [show (s₁.emit .streamEnd).tokens
            = s₁.tokens.push { pos := s₁.currentPos, val := .streamEnd } from rfl,
          Array.filter_push]
      rfl
    have h_s1_vals : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
        = [.streamStart, .scalar sc.content .doubleQuoted] := by
      rw [← Array.toList_map, h_filt₁]
    have h_tlist : tokens.toList
        = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
          ++ [{ pos := s₁.currentPos, val := .streamEnd }] := by
      rw [h_tokens_eq, h_final_filter, Array.toList_push]
    calc tokens.toList.map (·.val)
        = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
          ++ [YamlToken.streamEnd] := by
          rw [h_tlist]; simp only [List.map_append, List.map_cons, List.map_nil]
      _ = .streamStart :: (emitTokVals (.scalar sc) ++ [.streamEnd]) := by
          rw [h_s1_vals]; rfl
  | sequence style items tag anchor iF h =>
    match h_list : items.toList with
    | [] =>
      -- Empty flow sequence: `emit` is "[]"; replay open_init → outermost close.
      have h_chars : (emit (.sequence style items tag anchor)).toList =
          '[' :: ((emit.emitList items.toList).toList ++ [']']) := by
        simp only [emit, String.toList_append]; rfl
      have h_toList : (emit (.sequence style items tag anchor)).toList = '[' :: [']'] := by
        rw [h_chars, h_list]; rfl
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
              _h_inflow₁, _h_indent₁, _h_ek₁, _h_line₁, _h_atol₁, _h_endline₁, _h_sk₁, h_filt₁,
              _h_sync₁, _h_ska₁, _h_ssv₁⟩ :=
        scanNextToken_flow_open_init (emit (.sequence style items tag anchor)) [']'] h_toList
      obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fse, h_tok_fse_val, h_filt₃⟩⟩ :=
        scanNextToken_flow_close_seq_outermost_ext s₁ h_corr₁ _h_inflow₁ _h_indent₁
          (by rw [h_col₁]; omega) h_fl₁ h_dp₁
      have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
      have h_chain_all := (ScanChain.single h_snt₁).trans (ScanChain.single h_snt₃)
      have h_no_bom : (ScannerState.mk' (emit (.sequence style items tag anchor))).peek?
          ≠ some '﻿' := by
        have h_chars0 := chars_from_zero_toList (emit (.sequence style items tag anchor))
        rw [h_toList] at h_chars0
        have h_corr0 := initial_corr (emit (.sequence style items tag anchor)) _ h_chars0
        have ⟨h_pk, _⟩ := peek_of_chars_cons _ '[' [']'] 0 h_corr0
        rw [h_pk]; decide
      have h_indents_small : s₃.indents.size ≤ 1 := by
        rw [h_ids₃, h_ids₁]
        unfold ScannerState.emit ScannerState.mk'
        dsimp only []
        decide
      have h_tok_eq : Scanner.scanFiltered (emit (.sequence style items tag anchor)) =
          .ok ((s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder)) :=
        scanFiltered_tokens_eq_of_chain_short_stack (emit (.sequence style items tag anchor))
          _ s₃ _ rfl h_no_bom h_chain_all h_eof h_fl₃ h_dp₃
          (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
          h_indents_small
      have h_tokens_eq : tokens
          = (s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) := by
        have h_scan' := h_scan
        rw [h_tok_eq] at h_scan'; exact (Except.ok.inj h_scan').symm
      have h_final_filter : (s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) =
          (s₃.tokens.filter (fun t => t.val != .placeholder)).push
            { pos := s₃.currentPos, val := .streamEnd } := by
        rw [show (s₃.emit .streamEnd).tokens
              = s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } from rfl,
            Array.filter_push]
        rfl
      have h_tokens_decomp : tokens
          = ((s₁.tokens.filter (fun t => t.val != .placeholder)).push tok_fse).push
              { pos := s₃.currentPos, val := .streamEnd } := by
        rw [h_tokens_eq, h_final_filter, h_filt₃]
      have h_s1_vals : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
          = [.streamStart, .flowSequenceStart] := by
        rw [← Array.toList_map, h_filt₁]
      have h_tlist : tokens.toList
          = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ [tok_fse, { pos := s₃.currentPos, val := .streamEnd }] := by
        rw [h_tokens_decomp]
        simp only [Array.toList_push, List.append_assoc, List.cons_append, List.nil_append]
      calc tokens.toList.map (·.val)
          = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
            ++ [tok_fse.val, YamlToken.streamEnd] := by
            rw [h_tlist]; simp only [List.map_append, List.map_cons, List.map_nil]
        _ = [.streamStart, .flowSequenceStart] ++ [.flowSequenceEnd, .streamEnd] := by
            rw [h_s1_vals, h_tok_fse_val]
        _ = .streamStart :: (emitTokVals (.sequence style items tag anchor) ++ [.streamEnd]) := by
            simp [emitTokVals, h_list]
    | w :: ws =>
      have h_all : ∀ u ∈ items.toList, EmitScansTokVals u := fun u hu => by
        have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hu
        have h_sz : i < items.size := by rwa [Array.length_toList] at hi
        exact h_eq ▸ emit_scans_tokvals _ (h ⟨i, h_sz⟩)
      have h_ne : items.toList ≠ [] := by rw [h_list]; exact List.cons_ne_nil _ _
      have h_scan' : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]")
          = .ok tokens := h_scan
      have h_main := scanFiltered_emitSeq_tokvals items.toList h_ne h_all tokens h_scan'
      rw [h_main]
      simp [emitTokVals]
  | mapping style pairs tag anchor iF hk hv =>
    match h_list : pairs.toList with
    | [] =>
      -- Empty flow mapping: `emit` is "{}"; replay open_mapping_init → outermost close.
      have h_chars : (emit (.mapping style pairs tag anchor)).toList =
          '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}']) := by
        simp only [emit, String.toList_append]; rfl
      have h_toList : (emit (.mapping style pairs tag anchor)).toList = '{' :: ['}'] := by
        rw [h_chars, h_list]; rfl
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
              _h_inflow₁, _h_indent₁, _h_ek₁, _h_line₁, _h_atol₁, _h_endline₁, _h_sk₁, h_filt₁,
              _h_sync₁, _h_ska₁, _h_ssv₁⟩ :=
        scanNextToken_flow_open_mapping_init (emit (.mapping style pairs tag anchor)) ['}'] h_toList
      obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fme, h_tok_fme_val, h_filt₃⟩⟩ :=
        scanNextToken_flow_close_mapping_outermost_ext s₁ h_corr₁ _h_inflow₁ _h_indent₁
          (by rw [h_col₁]; omega) h_fl₁ h_dp₁
      have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
      have h_chain_all := (ScanChain.single h_snt₁).trans (ScanChain.single h_snt₃)
      have h_no_bom : (ScannerState.mk' (emit (.mapping style pairs tag anchor))).peek?
          ≠ some '﻿' := by
        have h_chars0 := chars_from_zero_toList (emit (.mapping style pairs tag anchor))
        rw [h_toList] at h_chars0
        have h_corr0 := initial_corr (emit (.mapping style pairs tag anchor)) _ h_chars0
        have ⟨h_pk, _⟩ := peek_of_chars_cons _ '{' ['}'] 0 h_corr0
        rw [h_pk]; decide
      have h_indents_small : s₃.indents.size ≤ 1 := by
        rw [h_ids₃, h_ids₁]
        unfold ScannerState.emit ScannerState.mk'
        dsimp only []
        decide
      have h_tok_eq : Scanner.scanFiltered (emit (.mapping style pairs tag anchor)) =
          .ok ((s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder)) :=
        scanFiltered_tokens_eq_of_chain_short_stack (emit (.mapping style pairs tag anchor))
          _ s₃ _ rfl h_no_bom h_chain_all h_eof h_fl₃ h_dp₃
          (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
          h_indents_small
      have h_tokens_eq : tokens
          = (s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) := by
        have h_scan' := h_scan
        rw [h_tok_eq] at h_scan'; exact (Except.ok.inj h_scan').symm
      have h_final_filter : (s₃.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder) =
          (s₃.tokens.filter (fun t => t.val != .placeholder)).push
            { pos := s₃.currentPos, val := .streamEnd } := by
        rw [show (s₃.emit .streamEnd).tokens
              = s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } from rfl,
            Array.filter_push]
        rfl
      have h_tokens_decomp : tokens
          = ((s₁.tokens.filter (fun t => t.val != .placeholder)).push tok_fme).push
              { pos := s₃.currentPos, val := .streamEnd } := by
        rw [h_tokens_eq, h_final_filter, h_filt₃]
      have h_s1_vals : (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
          = [.streamStart, .flowMappingStart] := by
        rw [← Array.toList_map, h_filt₁]
      have h_tlist : tokens.toList
          = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ [tok_fme, { pos := s₃.currentPos, val := .streamEnd }] := by
        rw [h_tokens_decomp]
        simp only [Array.toList_push, List.append_assoc, List.cons_append, List.nil_append]
      calc tokens.toList.map (·.val)
          = (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.map (·.val)
            ++ [tok_fme.val, YamlToken.streamEnd] := by
            rw [h_tlist]; simp only [List.map_append, List.map_cons, List.map_nil]
        _ = [.streamStart, .flowMappingStart] ++ [.flowMappingEnd, .streamEnd] := by
            rw [h_s1_vals, h_tok_fme_val]
        _ = .streamStart :: (emitTokVals (.mapping style pairs tag anchor) ++ [.streamEnd]) := by
            simp [emitTokVals, h_list]
    | p :: ps =>
      have h_all_k : ∀ q ∈ pairs.toList, EmitScansSavedKeyTokVals q.1 := fun q hq => by
        have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hq
        have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
        exact h_eq ▸ emit_scans_saved_key_tokvals _ (hk ⟨i, h_sz⟩)
      have h_all_v : ∀ q ∈ pairs.toList, EmitScansTokVals q.2 := fun q hq => by
        have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hq
        have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
        exact h_eq ▸ emit_scans_tokvals _ (hv ⟨i, h_sz⟩)
      have h_ne : pairs.toList ≠ [] := by rw [h_list]; exact List.cons_ne_nil _ _
      have h_scan' : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}")
          = .ok tokens := h_scan
      have h_main := scanFiltered_emitMap_tokvals pairs.toList h_ne h_all_k h_all_v tokens h_scan'
      rw [h_main]
      simp [emitTokVals]

/-! ## Axiom audit -/

/--
info: 'L4YAML.Proofs.EmitterScannability.emit_scans_tokvals_both' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_15,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_18,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_27,
 escapeChar_hex_structure._native.native_decide.ax_1_1,
 escapeChar_hex_structure._native.native_decide.ax_1_2,
 escapeChar_hex_structure._native.native_decide.ax_1_3,
 escapeTag_not_linebreak._native.native_decide.ax_1_10,
 escapeTag_not_linebreak._native.native_decide.ax_1_11,
 escapeTag_not_linebreak._native.native_decide.ax_1_12,
 escapeTag_not_linebreak._native.native_decide.ax_1_2,
 escapeTag_not_linebreak._native.native_decide.ax_1_3,
 escapeTag_not_linebreak._native.native_decide.ax_1_4,
 escapeTag_not_linebreak._native.native_decide.ax_1_5,
 escapeTag_not_linebreak._native.native_decide.ax_1_6,
 escapeTag_not_linebreak._native.native_decide.ax_1_7,
 escapeTag_not_linebreak._native.native_decide.ax_1_8,
 escapeTag_not_linebreak._native.native_decide.ax_1_9,
 hexNibble_is_hex._native.native_decide.ax_1_1,
 hexNibble_lt128._native.native_decide.ax_1_1,
 hex_foldl_roundtrip._native.native_decide.ax_1_1,
 hex_two_foldl_bound._native.native_decide.ax_1_1,
 escapeTag_roundtrip._native.native_decide.ax_1_10,
 escapeTag_roundtrip._native.native_decide.ax_1_11,
 escapeTag_roundtrip._native.native_decide.ax_1_12,
 escapeTag_roundtrip._native.native_decide.ax_1_13,
 escapeTag_roundtrip._native.native_decide.ax_1_14,
 escapeTag_roundtrip._native.native_decide.ax_1_15,
 escapeTag_roundtrip._native.native_decide.ax_1_16,
 escapeTag_roundtrip._native.native_decide.ax_1_17,
 escapeTag_roundtrip._native.native_decide.ax_1_18,
 escapeTag_roundtrip._native.native_decide.ax_1_19,
 escapeTag_roundtrip._native.native_decide.ax_1_2,
 escapeTag_roundtrip._native.native_decide.ax_1_20,
 escapeTag_roundtrip._native.native_decide.ax_1_21,
 escapeTag_roundtrip._native.native_decide.ax_1_22,
 escapeTag_roundtrip._native.native_decide.ax_1_23,
 escapeTag_roundtrip._native.native_decide.ax_1_3,
 escapeTag_roundtrip._native.native_decide.ax_1_4,
 escapeTag_roundtrip._native.native_decide.ax_1_5,
 escapeTag_roundtrip._native.native_decide.ax_1_6,
 escapeTag_roundtrip._native.native_decide.ax_1_7,
 escapeTag_roundtrip._native.native_decide.ax_1_8,
 escapeTag_roundtrip._native.native_decide.ax_1_9]
-/
#guard_msgs in
#print axioms emit_scans_tokvals_both

/--
info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_emitSeq_tokvals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_emitSeq_tokvals

/--
info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_emitMap_tokvals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_emitMap_tokvals

/--
info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_emit_tokvals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_15,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_18,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_27,
 emitScalar_toList._native.native_decide.ax_1_1,
 emitScalar_utf8ByteSize_ge._native.native_decide.ax_1_1,
 escapeChar_hex_structure._native.native_decide.ax_1_1,
 escapeChar_hex_structure._native.native_decide.ax_1_2,
 escapeChar_hex_structure._native.native_decide.ax_1_3,
 escapeTag_not_linebreak._native.native_decide.ax_1_10,
 escapeTag_not_linebreak._native.native_decide.ax_1_11,
 escapeTag_not_linebreak._native.native_decide.ax_1_12,
 escapeTag_not_linebreak._native.native_decide.ax_1_2,
 escapeTag_not_linebreak._native.native_decide.ax_1_3,
 escapeTag_not_linebreak._native.native_decide.ax_1_4,
 escapeTag_not_linebreak._native.native_decide.ax_1_5,
 escapeTag_not_linebreak._native.native_decide.ax_1_6,
 escapeTag_not_linebreak._native.native_decide.ax_1_7,
 escapeTag_not_linebreak._native.native_decide.ax_1_8,
 escapeTag_not_linebreak._native.native_decide.ax_1_9,
 hexNibble_is_hex._native.native_decide.ax_1_1,
 hexNibble_lt128._native.native_decide.ax_1_1,
 hex_foldl_roundtrip._native.native_decide.ax_1_1,
 hex_two_foldl_bound._native.native_decide.ax_1_1,
 escapeTag_roundtrip._native.native_decide.ax_1_10,
 escapeTag_roundtrip._native.native_decide.ax_1_11,
 escapeTag_roundtrip._native.native_decide.ax_1_12,
 escapeTag_roundtrip._native.native_decide.ax_1_13,
 escapeTag_roundtrip._native.native_decide.ax_1_14,
 escapeTag_roundtrip._native.native_decide.ax_1_15,
 escapeTag_roundtrip._native.native_decide.ax_1_16,
 escapeTag_roundtrip._native.native_decide.ax_1_17,
 escapeTag_roundtrip._native.native_decide.ax_1_18,
 escapeTag_roundtrip._native.native_decide.ax_1_19,
 escapeTag_roundtrip._native.native_decide.ax_1_2,
 escapeTag_roundtrip._native.native_decide.ax_1_20,
 escapeTag_roundtrip._native.native_decide.ax_1_21,
 escapeTag_roundtrip._native.native_decide.ax_1_22,
 escapeTag_roundtrip._native.native_decide.ax_1_23,
 escapeTag_roundtrip._native.native_decide.ax_1_3,
 escapeTag_roundtrip._native.native_decide.ax_1_4,
 escapeTag_roundtrip._native.native_decide.ax_1_5,
 escapeTag_roundtrip._native.native_decide.ax_1_6,
 escapeTag_roundtrip._native.native_decide.ax_1_7,
 escapeTag_roundtrip._native.native_decide.ax_1_8,
 escapeTag_roundtrip._native.native_decide.ax_1_9]
-/
#guard_msgs in
#print axioms scanFiltered_emit_tokvals

end L4YAML.Proofs.EmitterScannability
