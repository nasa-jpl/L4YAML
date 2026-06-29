/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Output.EmitterScannability.BlockProducers

/-!
# Scanner-span-locality: body-content scanner fact (R596)

For a non-empty all-scalar flow sequence `emitList items`, the body block produced by scanning
in flow context carries `.scalar sc.content .doubleQuoted` at position `2*j` for element `j`.

This is the SCANNER FACT component of the scanner-span-locality chain that closes the Front-B
sorry at `EmitterScannability.lean:1002`: given `tokens[2 + 2*j]!.val = .scalar sc.content .dq`,
`peek_of_pos_val` converts to `ps.peek? = some (.scalar sc.content .dq)`, and
`parseNode_scalar_produces_scalar` pins the parse result to
`.scalar (Scalar.mk sc.content .doubleQuoted none none none)`.
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge

abbrev filt : Positioned YamlToken → Bool := fun t => t.val != .placeholder

/-- **R596. Body-content scanner fact for all-scalar flow sequences.**

    For a non-empty list of all-scalar values, scanning `emitList items` from a flow-context state
    `s` produces a body block `block` satisfying:
    * `block[2*j]!.val = .scalar items[j].content .doubleQuoted` for each `j < items.length`
    * `block.length = 2 * items.length - 1`

    Proof: direct list induction parallel to `emitList_scans_safebody`, using
    `scanNextToken_flow_scalar_filtered_push_content` (content-pinned) for each scalar head, and
    `scanNextToken_flow_comma_filtered_push` + `scanNextToken_preprocess_flow_ws1` for the `", "`
    separator.  The IH provides the tail's block with the same property, and the indexing step
    uses `List.getElem!_cons_succ` twice to hop over the two prefix tokens.  -/
theorem emitList_allScalar_body_content_at :
    ∀ (items : List YamlValue), items ≠ [] →
    ∀ (_h_all : ∀ v ∈ items, ∃ sc : Scalar, v = .scalar sc),
    ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest, s.col⟩ →
    s.inFlow = true → s.flowLevel > 0 → s.currentIndent < 0 → s.col > 0 →
    s.explicitKeyLine = none → AllTokensOnLine s s.line → EndLineOnLine s →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ (n : Nat) (s' : ScannerState) (block : List (Positioned YamlToken)),
      ScanChainGrew filt s n s' ∧
      ScannerSurfCorr s' ⟨rest, s'.col⟩ ∧
      s'.flowLevel = s.flowLevel ∧
      s'.directivesPresent = s.directivesPresent ∧
      s'.indents = s.indents ∧
      s'.explicitKeyLine = s.explicitKeyLine ∧
      s'.col > 0 ∧
      s'.inFlow = true ∧
      s'.currentIndent < 0 ∧
      s'.line = s.line ∧
      AllTokensOnLine s' s'.line ∧
      EndLineOnLine s' ∧
      s'.simpleKeyStack = s.simpleKeyStack ∧
      (s'.tokens.filter filt).toList = (s.tokens.filter filt).toList ++ block ∧
      block.length = 2 * items.length - 1 ∧
      ∀ j : Nat, j < items.length → ∀ sc : Scalar, items[j]? = some (.scalar sc) →
          2 * j < block.length ∧ block[2 * j]!.val = .scalar sc.content .doubleQuoted := by
  intro items
  induction items with
  | nil => intro h; exact absurd rfl h
  | cons v tail ih =>
    intro h_ne h_all s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
    obtain ⟨sc, rfl⟩ : ∃ sc : Scalar, v = .scalar sc := h_all v (.head _)
    cases tail with
    | nil =>
      -- ── SINGLETON CASE: items = [.scalar sc] ────────────────────────────────
      have h_eq : (emit.emitList [.scalar sc]).toList ++ rest =
          ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest := by
        simp only [emit.emitList, emit, emitScalar, String.toList_append]; rfl
      rw [h_eq] at hcorr
      obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_last', _,
              h_line', h_atol', h_endline', h_stack'⟩ :=
        scanNextToken_flow_scanDoubleQuoted s sc.content rest hcorr h_flow h_indent h_col
          h_atol h_endline
      obtain ⟨tok, h_tok_val, h_push⟩ :=
        scanNextToken_flow_scalar_filtered_push_content s sc.content rest hcorr h_flow h_indent
          h_col h_snt
      have h_grew : (s'.tokens.filter filt).size > (s.tokens.filter filt).size := by
        rw [h_push]; simp [Array.size_push]
      refine ⟨1, s', [tok],
              ScanChainGrew.single h_snt h_grew,
              h_corr', h_fl', h_dp', h_ids', h_ek', h_col',
              by unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl']; omega),
              by unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent,
              h_line', h_atol', h_endline', h_stack', ?_, ?_, ?_⟩
      · rw [h_push, Array.toList_push]
      · simp
      · intro j hj sc' h_item
        simp only [List.length_singleton] at hj
        obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h_item
        obtain rfl : sc = sc' := YamlValue.scalar.inj h_item
        exact ⟨by simp, by simp only [Nat.mul_zero, List.getElem!_cons_zero]; exact h_tok_val⟩
    | cons v' vs =>
      -- ── MULTI-ELEMENT CASE: items = .scalar sc :: v' :: vs ──────────────────
      obtain ⟨sc', rfl⟩ : ∃ sc' : Scalar, v' = .scalar sc' := h_all v' (.tail _ (.head _))
      let rest₁ : List Char := ',' :: ' ' :: (emit.emitList (.scalar sc' :: vs)).toList ++ rest
      have h_chars : (emit.emitList (.scalar sc :: .scalar sc' :: vs)).toList ++ rest =
          ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest₁ := by
        simp only [emit.emitList, emit, emitScalar, String.toList_append, List.append_assoc]; rfl
      have hcorr_h : ScannerSurfCorr s
          ⟨['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest₁, s.col⟩ :=
        h_chars ▸ hcorr
      -- Step 1: scan first scalar
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_last₁, _,
              h_line₁, h_atol₁, h_endline₁, h_stack₁⟩ :=
        scanNextToken_flow_scanDoubleQuoted s sc.content rest₁ hcorr_h h_flow h_indent h_col
          h_atol h_endline
      obtain ⟨tok₁, h_tok₁_val, h_push₁⟩ :=
        scanNextToken_flow_scalar_filtered_push_content s sc.content rest₁ hcorr_h h_flow
          h_indent h_col h_snt₁
      have h_grew₁ : (s₁.tokens.filter filt).size > (s.tokens.filter filt).size := by
        rw [h_push₁]; simp [Array.size_push]
      -- Step 2: scan ',' separator
      have h_s1_flow : s₁.inFlow = true :=
        by unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
      have h_s1_indent : s₁.currentIndent < 0 :=
        by unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_line₂,
              h_atol₂, h_endline₂, h_stack₂⟩ :=
        scanNextToken_flow_comma s₁ (' ' :: (emit.emitList (.scalar sc' :: vs)).toList ++ rest)
          h_corr₁ h_s1_flow h_s1_indent (by omega) h_last₁ h_atol₁ h_endline₁
      obtain ⟨feTok, _h_feTok_val, h_push₂⟩ :=
        scanNextToken_flow_comma_filtered_push s₁
          (' ' :: (emit.emitList (.scalar sc' :: vs)).toList ++ rest)
          h_corr₁ h_s1_flow h_s1_indent (by omega) h_last₁ h_snt₂
      have h_grew₂ : (s₂.tokens.filter filt).size > (s₁.tokens.filter filt).size := by
        rw [h_push₂]; simp [Array.size_push]
      -- Step 3: preprocessing absorbs the ' ' space
      obtain ⟨c_f, rest_f, h_first, h_nws, h_nlb, h_nc⟩ := emitList_first_char (.scalar sc') vs
      have h_s2_flow : s₂.inFlow = true :=
        by unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₂, h_fl₁]; omega)
      have h_s2_indent : s₂.currentIndent < 0 :=
        by unfold ScannerState.currentIndent; rw [h_ids₂, h_ids₁]; exact h_indent
      have h_corr₂_ws : ScannerSurfCorr s₂ ⟨' ' :: c_f :: (rest_f ++ rest), s₂.col⟩ := by
        have : ' ' :: (emit.emitList (.scalar sc' :: vs)).toList ++ rest =
               ' ' :: c_f :: (rest_f ++ rest) := by rw [h_first]; simp [List.cons_append]
        rwa [this] at h_corr₂
      obtain ⟨s₃, h_corr₃, h_s3_flow, h_fl₃, h_s3_indent, h_col₃, h_dp₃, h_ids₃, h_ek₃,
              h_line₃, h_pp_eq, h_atol_tr₃, h_endline_tr₃, h_stack₃, h_toks₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_f (rest_f ++ rest) h_corr₂_ws h_s2_flow
          h_nws h_nlb h_nc h_s2_indent
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit.emitList (.scalar sc' :: vs)).toList ++ rest, s₃.col⟩ := by
        have : c_f :: (rest_f ++ rest) = (emit.emitList (.scalar sc' :: vs)).toList ++ rest := by
          rw [h_first]; simp [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: IH on the tail (.scalar sc' :: vs) from s₃
      have h_tail_ne : .scalar sc' :: vs ≠ [] := List.cons_ne_nil _ _
      have h_tail_all : ∀ w ∈ (.scalar sc' :: vs), ∃ sc_w : Scalar, w = .scalar sc_w :=
        fun w hw => h_all w (.tail _ hw)
      obtain ⟨n₃, s_end, block_rest, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end,
              h_endline_end, h_stack_end, h_block_eq₃, h_len₃, h_pointwise₃⟩ :=
        ih h_tail_ne h_tail_all s₃ rest h_corr₃'
          h_s3_flow (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by omega)
          (by omega)
          (by rw [h_ek₃, h_ek₂, h_ek₁]; exact h_ek)
          (h_atol_tr₃ h_atol₂)
          (h_endline_tr₃ h_endline₂)
          (by rw [h_stack₃, h_stack₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
      -- Lift IH chain through the preprocessing equality
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_filt_le : (s₂.tokens.filter filt).size ≤ (s₃.tokens.filter filt).size := by
        rw [h_toks₃]; omega
      -- n₃ ≥ 1: the tail produces at least one token
      have h_n₃_pos : n₃ ≥ 1 := by
        obtain ⟨h_bound, _⟩ := h_pointwise₃ 0 (by simp) sc' (by simp)
        rcases Nat.eq_zero_or_pos n₃ with rfl | h_pos
        · exfalso
          have h_s_eq : s_end = s₃ := ScanChainGrew.eq_of_zero h_chain₃
          rw [h_s_eq] at h_block_eq₃
          have h_len := congrArg List.length h_block_eq₃
          rw [List.length_append] at h_len
          omega
        · exact h_pos
      obtain ⟨m₃, rfl⟩ : ∃ m, n₃ = m + 1 := ⟨n₃ - 1, by omega⟩
      have h_chain_s₂ : ScanChainGrew filt s₂ (m₃ + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain₃
      -- Build combined filter equation
      have h_filter_end : (s_end.tokens.filter filt).toList =
          (s.tokens.filter filt).toList ++ (tok₁ :: feTok :: block_rest) := by
        rw [h_block_eq₃]
        have h_s3_filt : (s₃.tokens.filter filt).toList = (s₂.tokens.filter filt).toList :=
          by rw [h_toks₃]
        rw [h_s3_filt]
        rw [h_push₂, Array.toList_push]
        rw [h_push₁, Array.toList_push]
        simp [List.append_assoc]
      -- Block length
      have h_len : (tok₁ :: feTok :: block_rest).length =
          2 * (.scalar sc :: .scalar sc' :: vs).length - 1 := by
        simp only [List.length_cons]
        have h_lr := h_len₃
        simp only [List.length_cons] at h_lr
        omega
      -- Chain composition
      have h_chain_all : ScanChainGrew filt s (1 + (1 + (m₃ + 1))) s_end :=
        (ScanChainGrew.single h_snt₁ h_grew₁).trans
          ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_s₂)
      -- Pointwise content property
      have h_pointwise : ∀ j : Nat,
          j < (.scalar sc :: .scalar sc' :: vs).length →
          ∀ sc_j : Scalar,
          (.scalar sc :: .scalar sc' :: vs)[j]? = some (.scalar sc_j) →
          2 * j < (tok₁ :: feTok :: block_rest).length ∧
          (tok₁ :: feTok :: block_rest)[2 * j]!.val = .scalar sc_j.content .doubleQuoted := by
        intro j hj sc_j h_item
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h_item
          obtain rfl : sc = sc_j := YamlValue.scalar.inj h_item
          exact ⟨by simp only [h_len, List.length_cons]; omega,
                 by simp only [Nat.mul_zero, List.getElem!_cons_zero]; exact h_tok₁_val⟩
        | succ j' =>
          simp only [List.length_cons] at hj
          have hj' : j' < (.scalar sc' :: vs).length := by simp only [List.length_cons]; omega
          simp only [List.getElem?_cons_succ] at h_item
          obtain ⟨h_bound_r, h_val_r⟩ := h_pointwise₃ j' hj' sc_j h_item
          refine ⟨?_, ?_⟩
          · simp only [List.length_cons]; omega
          · -- (tok₁ :: feTok :: block_rest)[2*(j'+1)]! = block_rest[2*j']!
            rw [show 2 * (j' + 1) = 2 * j' + 2 from by omega]
            rw [List.getElem!_cons_succ, List.getElem!_cons_succ]
            exact h_val_r
      exact ⟨1 + (1 + (m₃ + 1)), s_end, tok₁ :: feTok :: block_rest,
             h_chain_all, h_corr_end,
             by rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁],
             by rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁],
             by rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁],
             by rw [h_ek_end, h_ek₃, h_ek₂, h_ek₁],
             h_col_end, h_flow_end, h_indent_end,
             by rw [h_line_end, h_line₃, h_line₂, h_line₁],
             h_atol_end, h_endline_end,
             by rw [h_stack_end, h_stack₃, h_stack₂, h_stack₁],
             h_filter_end, h_len, h_pointwise⟩

/-- **R597. All-scalar token-array content pin.**

    If `scanFiltered ("[" ++ emitList items ++ "]") = .ok tokens` with a non-empty all-scalar
    `items`, then `tokens.size = 2 * items.length + 3` and for each `j < items.length`:
    `tokens[2 + 2 * j]!.val = .scalar (items[j] as Scalar).content .doubleQuoted`.

    Proof: chain-replay of `"[" ++ emitList ++ "]"` (same pattern as `seqRoot_recseqbody`):
    1. `scanNextToken_flow_open_init` yields `s₁` with filtered prefix `[streamStart, flowSeqStart]`.
    2. R596 (`emitList_allScalar_body_content_at`) yields `s₂` and body `block` with
       `block[2*j]!.val = .scalar sc.content .doubleQuoted`.
    3. `scanNextToken_flow_close_seq_outermost_ext` yields `s₃`.
    4. `scanFiltered_tokens_eq_of_chain_short_stack` gives `tokens = s₂.filter ++ [tok_fse, streamEnd]`.
    5. Offset-2 index arithmetic connects `tokens[2 + 2*j]` to `block[2*j]`. -/
theorem scanFiltered_emitSeq_allScalar_token_at
    (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, ∃ sc : Scalar, v = .scalar sc)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items ++ "]") = .ok tokens) :
    tokens.size = 2 * items.length + 3 ∧
    tokens[1]!.val = .flowSequenceStart ∧
    ∀ j : Nat, j < items.length → ∀ sc : Scalar, items[j]? = some (.scalar sc) →
        tokens[2 + 2 * j]!.val = .scalar sc.content .doubleQuoted := by
  let input := "[" ++ emit.emitList items ++ "]"
  have h_toList : input.toList = '[' :: (emit.emitList items).toList ++ [']'] := by
    simp only [input, String.toList_append]; rfl
  -- ═══ Step 1: open bracket → s₁ ═══
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, _h_sk₁, h_filt₁,
          h_sync₁, _h_ska₁, _h_ssv₁⟩ :=
    scanNextToken_flow_open_init input ((emit.emitList items).toList ++ [']']) h_toList
  -- ═══ Step 2: body scan via R596 → s₂ and body block ═══
  obtain ⟨_n₂, s₂, block, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_inflow₂,
          h_indent₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_block_eq₂, h_block_len, h_block_content⟩ :=
    emitList_allScalar_body_content_at items h_ne h_all s₁ [']']
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
      .ok ((s₃.emit .streamEnd).tokens.filter filt) :=
    scanFiltered_tokens_eq_of_chain_short_stack input _ s₃ _ rfl h_no_bom
      h_chain_all h_eof h_fl₃ h_dp₃
      (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
      h_indents_small
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter filt := by
    have : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at this; exact (Except.ok.inj this).symm
  -- ═══ Step 5: decompose token array ═══
  have h_emit_se : (s₃.emit .streamEnd).tokens =
      s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } :=
    rfl
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter filt =
      (s₃.tokens.filter filt).push { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_emit_se, Array.filter_push]; rfl
  have h_tokens_decomp : tokens = ((s₂.tokens.filter filt).push tok_fse).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  -- ═══ Step 6: filtered prefix size ═══
  have h_filt₁_sz : (s₁.tokens.filter filt).size = 2 := by
    have : ((s₁.tokens.filter filt).map (·.val)).size = 2 := by rw [h_filt₁]; rfl
    simpa [Array.size_map] using this
  have h_s1_filt_len : (s₁.tokens.filter filt).toList.length = 2 := by
    rw [Array.length_toList]; exact h_filt₁_sz
  -- ═══ Step 7: s₂ filtered size ═══
  have h_s2_filt_sz : (s₂.tokens.filter filt).size = 2 + block.length := by
    have h_len := congrArg List.length h_block_eq₂
    simp only [List.length_append, Array.length_toList] at h_len
    rw [h_filt₁_sz] at h_len; omega
  -- ═══ Step 8: overall token size ═══
  have h_items_len_pos : 1 ≤ items.length := List.length_pos_iff.mpr h_ne
  have h_tokens_sz : tokens.size = 2 * items.length + 3 := by
    rw [h_tokens_decomp]; simp only [Array.size_push]
    rw [h_s2_filt_sz, h_block_len]; omega
  -- ═══ Step 9/10: s₁ filtered-array position 1 = flowSequenceStart ═══
  have h_filt₁_val1 : ((s₁.tokens.filter filt)[1]'(by rw [h_filt₁_sz]; omega)).val =
      .flowSequenceStart := by
    have hmapped : ((s₁.tokens.filter filt).map (·.val))[1]'(by simp [Array.size_map, h_filt₁_sz]) =
        .flowSequenceStart := by
      simp [h_filt₁]
    rwa [Array.getElem_map] at hmapped
  have h_t1 : tokens[1]!.val = .flowSequenceStart := by
    have h1_lt_s2 : 1 < (s₂.tokens.filter filt).size := by rw [h_s2_filt_sz]; omega
    have h1_lt_s1 : 1 < (s₁.tokens.filter filt).size := by rw [h_filt₁_sz]; omega
    rw [h_tokens_decomp, getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h1_lt_s2]
    have h_eq : (s₂.tokens.filter filt)[1]'h1_lt_s2 = (s₁.tokens.filter filt)[1]'h1_lt_s1 := by
      show (s₂.tokens.filter filt).toList[1]'(by rw [Array.length_toList]; exact h1_lt_s2) =
          (s₁.tokens.filter filt).toList[1]'(by rw [Array.length_toList]; exact h1_lt_s1)
      simp only [h_block_eq₂]
      exact List.getElem_append_left (by rw [Array.length_toList]; exact h1_lt_s1)
    calc ((s₂.tokens.filter filt)[1]'h1_lt_s2).val
        = ((s₁.tokens.filter filt)[1]'h1_lt_s1).val := congrArg Positioned.val h_eq
      _ = .flowSequenceStart := h_filt₁_val1
  -- ═══ Step 11: pointwise content pin ═══
  refine ⟨h_tokens_sz, h_t1, fun j hj sc h_item => ?_⟩
  obtain ⟨h_2j_lt_block, h_block_val⟩ := h_block_content j hj sc h_item
  have h_2j_lt_s2 : 2 + 2 * j < (s₂.tokens.filter filt).size := by
    rw [h_s2_filt_sz]; omega
  rw [h_tokens_decomp, getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
  rw [Array.getElem_push_lt (by simp only [Array.size_push]; omega)]
  rw [Array.getElem_push_lt h_2j_lt_s2]
  -- Goal: ((s₂.tokens.filter filt)[2+2*j]'h_2j_lt_s2).val = .scalar sc.content .doubleQuoted
  have h_at_2j : (s₂.tokens.filter filt)[2 + 2 * j]'h_2j_lt_s2 =
      block[2 * j]'h_2j_lt_block := by
    -- Work at the List.getElem? level to avoid dependent proof-bound issues
    have h_lhs_lt : 2 + 2 * j < (s₂.tokens.filter filt).toList.length := by
      rw [Array.length_toList]; exact h_2j_lt_s2
    have h_opt : (s₂.tokens.filter filt).toList[2 + 2 * j]? = block[2 * j]? := by
      rw [h_block_eq₂, List.getElem?_append_right (by rw [h_s1_filt_len]; omega)]
      have h_sub : 2 + 2 * j - (s₁.tokens.filter filt).toList.length = 2 * j := by
        rw [h_s1_filt_len]; omega
      rw [h_sub]
    rw [List.getElem?_eq_getElem h_lhs_lt, List.getElem?_eq_getElem h_2j_lt_block] at h_opt
    have h_list_eq := Option.some.inj h_opt
    rwa [Array.getElem_toList] at h_list_eq
  rw [h_at_2j]
  -- Goal: (block[2*j]'h_2j_lt_block).val = .scalar sc.content .doubleQuoted
  rw [(getElem!_pos block (2 * j) h_2j_lt_block).symm]
  exact h_block_val

end L4YAML.Proofs.EmitterScannability
