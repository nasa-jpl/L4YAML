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
      (∀ j : Nat, j < items.length → ∀ sc : Scalar, items[j]? = some (.scalar sc) →
          2 * j < block.length ∧ block[2 * j]!.val = .scalar sc.content .doubleQuoted) ∧
      ∀ j : Nat, j + 1 < items.length →
          2 * j + 1 < block.length ∧ block[2 * j + 1]!.val = .flowEntry := by
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
              h_line', h_atol', h_endline', h_stack', ?_, ?_, ?_, ?_⟩
      · rw [h_push, Array.toList_push]
      · simp
      · intro j hj sc' h_item
        simp only [List.length_singleton] at hj
        obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h_item
        obtain rfl : sc = sc' := YamlValue.scalar.inj h_item
        exact ⟨by simp, by simp only [Nat.mul_zero, List.getElem!_cons_zero]; exact h_tok_val⟩
      · -- flowEntry: j+1 < [sc].length = 1 → j+1 < 1, impossible
        intro j hj; simp only [List.length_singleton] at hj; omega
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
      obtain ⟨feTok, h_feTok_val, h_push₂⟩ :=
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
              h_endline_end, h_stack_end, h_block_eq₃, h_len₃, h_pointwise₃, h_block_fe_tail⟩ :=
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
      -- flowEntry at odd block positions
      have h_block_fe : ∀ j : Nat, j + 1 < (.scalar sc :: .scalar sc' :: vs).length →
          2 * j + 1 < (tok₁ :: feTok :: block_rest).length ∧
          (tok₁ :: feTok :: block_rest)[2 * j + 1]!.val = .flowEntry := by
        intro j hj
        cases j with
        | zero =>
          refine ⟨by simp only [h_len, List.length_cons]; omega, ?_⟩
          simp only [Nat.mul_zero, Nat.zero_add, List.getElem!_cons_succ,
                     List.getElem!_cons_zero]
          exact h_feTok_val
        | succ j' =>
          simp only [List.length_cons] at hj
          have hj' : j' + 1 < (.scalar sc' :: vs).length := by
            simp only [List.length_cons]; omega
          obtain ⟨h_bound_r, h_val_r⟩ := h_block_fe_tail j' hj'
          refine ⟨by simp only [List.length_cons]; omega, ?_⟩
          rw [show 2 * (j' + 1) + 1 = 2 * j' + 1 + 2 from by omega]
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
             h_filter_end, h_len, h_pointwise, h_block_fe⟩

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
    (∀ j : Nat, j < items.length → ∀ sc : Scalar, items[j]? = some (.scalar sc) →
        tokens[2 + 2 * j]!.val = .scalar sc.content .doubleQuoted) ∧
    (∀ j : Nat, 0 < j → j < items.length → tokens[2 * j + 1]!.val = .flowEntry) ∧
    tokens[2 * items.length + 1]!.val = .flowSequenceEnd := by
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
          h_indent₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_block_eq₂, h_block_len,
          h_block_content, h_block_fe_content⟩ :=
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
  -- ═══ Step 11: all three conclusions ═══
  refine ⟨h_tokens_sz, h_t1, ?_, ?_, ?_⟩
  · -- Scalar pointwise: tokens[2+2*j]!.val = .scalar sc.content .doubleQuoted
    intro j hj sc h_item
    obtain ⟨h_2j_lt_block, h_block_val⟩ := h_block_content j hj sc h_item
    have h_2j_lt_s2 : 2 + 2 * j < (s₂.tokens.filter filt).size := by
      rw [h_s2_filt_sz]; omega
    rw [h_tokens_decomp, getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h_2j_lt_s2]
    have h_at_2j : (s₂.tokens.filter filt)[2 + 2 * j]'h_2j_lt_s2 =
        block[2 * j]'h_2j_lt_block := by
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
    rw [h_at_2j, (getElem!_pos block (2 * j) h_2j_lt_block).symm]
    exact h_block_val
  · -- flowEntry: tokens[2*j+1]!.val = .flowEntry for 0 < j < items.length
    intro j hj_pos hj_lt
    obtain ⟨h_2jm1_lt_block, h_block_fe_val⟩ := h_block_fe_content (j - 1) (by omega)
    have h_2j1_lt_s2 : 2 * j + 1 < (s₂.tokens.filter filt).size := by
      rw [h_s2_filt_sz, h_block_len]; omega
    rw [h_tokens_decomp, getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h_2j1_lt_s2]
    have h_at_fe : (s₂.tokens.filter filt)[2 * j + 1]'h_2j1_lt_s2 =
        block[2 * (j - 1) + 1]'h_2jm1_lt_block := by
      have h_lhs_lt : 2 * j + 1 < (s₂.tokens.filter filt).toList.length := by
        rw [Array.length_toList]; exact h_2j1_lt_s2
      have h_opt : (s₂.tokens.filter filt).toList[2 * j + 1]? = block[2 * (j - 1) + 1]? := by
        rw [h_block_eq₂, List.getElem?_append_right (by rw [h_s1_filt_len]; omega)]
        congr 1; rw [h_s1_filt_len]; omega
      rw [List.getElem?_eq_getElem h_lhs_lt,
          List.getElem?_eq_getElem h_2jm1_lt_block] at h_opt
      have h_list_eq := Option.some.inj h_opt
      rwa [Array.getElem_toList] at h_list_eq
    rw [h_at_fe, (getElem!_pos block _ h_2jm1_lt_block).symm]
    exact h_block_fe_val
  · -- flowSequenceEnd: tokens[2*items.length+1]!.val = .flowSequenceEnd
    have h_idx : (s₂.tokens.filter filt).size = 2 * items.length + 1 := by
      rw [h_s2_filt_sz, h_block_len]; omega
    have h_idx_list : (s₂.tokens.filter filt).toList.length = 2 * items.length + 1 := by
      rw [Array.length_toList]; exact h_idx
    have h_lt : 2 * items.length + 1 < tokens.size := by rw [h_tokens_sz]; omega
    have h_lt2 : 2 * items.length + 1 < tokens.toList.length := by
      rw [Array.length_toList]; exact h_lt
    have h_tlist : tokens.toList = (s₂.tokens.filter filt).toList ++
        [tok_fse, { pos := s₃.currentPos, val := .streamEnd }] := by
      rw [h_tokens_decomp]; simp [Array.toList_push]
    have h_opt : tokens.toList[2 * items.length + 1]? = some tok_fse := by
      rw [h_tlist, List.getElem?_append_right (by rw [h_idx_list]; omega)]
      simp only [h_idx_list, Nat.sub_self, List.getElem?_cons_zero]
    rw [List.getElem?_eq_getElem h_lt2] at h_opt
    have h_elem : tokens.toList[2 * items.length + 1]'h_lt2 = tok_fse :=
      Option.some.inj h_opt
    have h_tok_eq : tokens[2 * items.length + 1]! = tok_fse := by
      rw [getElem!_pos tokens (2 * items.length + 1) h_lt]
      have h_rw := h_elem
      rwa [Array.getElem_toList] at h_rw
    rw [h_tok_eq]; exact h_tok_fse_val


/-- **R606. Body-content scanner fact for all-scalar flow mappings.**

    For a non-empty list of all-scalar pairs, scanning `emitPairList pairs` from a flow-context
    state `s` (with `simpleKeyAllowed = true`) produces a body block `block` satisfying:
    * `block.length = 5 * pairs.length - 1`
    * `block[5*j+1]!.val = .scalar sk.content .doubleQuoted` for each pair j
    * `block[5*j+3]!.val = .scalar sv.content .doubleQuoted` for each pair j
    * `block[5*j+4]!.val = .flowEntry` for j + 1 < pairs.length

    Proof: direct list induction parallel to `emitList_allScalar_body_content_at` (R596), using
    the colon-scan block (`scanNextToken_flow_value_block`) to simultaneously insert `.key` and
    `.value` tokens, with re-anchoring via `block_take_eq_of_getElem?` +
    `List_filter_drop_succ_of_take`.  The IH threading uses `scanNextToken_flow_comma_simpleKey`
    to restore `simpleKeyAllowed = true` for each subsequent pair.  -/
theorem emitPairList_allScalar_body_content_at :
    ∀ (pairs : List (YamlValue × YamlValue)), pairs ≠ [] →
    ∀ (_h_all : ∀ p ∈ pairs, ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv),
    ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩ →
    s.inFlow = true → s.flowLevel > 0 → s.currentIndent < 0 → s.col > 0 →
    s.explicitKeyLine = none → AllTokensOnLine s s.line → EndLineOnLine s →
    s.simpleKeyAllowed = true →
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
      block.length = 5 * pairs.length - 1 ∧
      (∀ j : Nat, j < pairs.length → ∀ sk sv : Scalar, pairs[j]? = some (.scalar sk, .scalar sv) →
          5 * j + 1 < block.length ∧ block[5 * j + 1]!.val = .scalar sk.content .doubleQuoted ∧
          5 * j + 3 < block.length ∧ block[5 * j + 3]!.val = .scalar sv.content .doubleQuoted) ∧
      ∀ j : Nat, j + 1 < pairs.length →
          5 * j + 4 < block.length ∧ block[5 * j + 4]!.val = .flowEntry := by
  intro pairs
  induction pairs with
  | nil => intro h; exact absurd rfl h
  | cons p tail ih =>
    intro _h_ne h_all s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
    obtain ⟨sk, sv, hsk, hsv⟩ : ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv :=
      h_all p (.head _)
    cases tail with
    | nil =>
      -- ── SINGLETON CASE: pairs = [(p.1, p.2)] ─────────────────────────────────
      -- rest_k BEFORE h_eq (R596-exact pattern): everything after closing key quote
      let rest_k : List Char :=
        ':' :: ' ' :: ['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest
      -- h_eq: simp unfolds rest_k via the show-from-rfl lemma so both sides right-associate
      -- to identical terms; rfl closes because ['"'] ++ rest →_def '"' :: rest by computation
      have h_eq : (emit.emitPairList [p]).toList ++ rest =
          ['"'] ++ (escapeString sk.content).toList ++ ['"'] ++ rest_k := by
        simp only [emit.emitPairList, emit, emitScalar, String.toList_append, hsk, hsv,
                   List.append_assoc,
                   show rest_k = ':' :: ' ' :: ['"'] ++
                     (escapeString sv.content).toList ++ ['"'] ++ rest from rfl]
        rfl
      have hcorr_k' : ScannerSurfCorr s
          ⟨['"'] ++ (escapeString sk.content).toList ++ ['"'] ++ rest_k, s.col⟩ :=
        h_eq ▸ hcorr
      -- hcorr_kq: ['"'] ++ esc_k ++ ['"'] ++ rest_k = '"' :: (esc_k ++ ['"'] ++ rest_k) by defn
      have hcorr_kq : ScannerSurfCorr s
          ⟨'"' :: ((escapeString sk.content).toList ++ ['"'] ++ rest_k), s.col⟩ :=
        hcorr_k'
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_last₁, h_ska₁,
              h_line₁, h_atol₁, h_endline₁, h_stack₁⟩ :=
        scanNextToken_flow_scanDoubleQuoted s sk.content rest_k hcorr_k' h_flow h_indent h_col
          h_atol h_endline
      obtain ⟨s₁', h_snt₁', h_poss₁, h_tidx₁, h_szlt₁, h_ph0₁, h_ph1₁⟩ :=
        scanNextToken_flow_scalar_savedKey s sk.content rest_k hcorr_k' h_flow h_indent h_col
          h_ek h_ska
      have h_s1_eq : s₁' = s₁ := Option.some.inj (Except.ok.inj (h_snt₁'.symm.trans h_snt₁))
      rw [h_s1_eq] at h_poss₁ h_tidx₁ h_szlt₁ h_ph0₁ h_ph1₁
      clear h_snt₁' s₁' h_s1_eq
      obtain ⟨tok_k, h_tok_k_val, h_push_k⟩ :=
        scanNextToken_flow_scalar_filtered_push_content s sk.content rest_k hcorr_kq
          h_flow h_indent h_col h_snt₁
      -- Key re-anchoring for colon scan
      have h_nc_k : ∀ t c', scanNextToken_preprocess s = .ok (some (t, c')) → c' ≠ ':' :=
        no_colon_of_preprocess_flow s '"'
          ((escapeString sk.content).toList ++ ['"'] ++ rest_k)
          s.col hcorr_kq h_flow (by decide) (by decide) (by decide) (by decide)
      have h_N1_k : s.tokens.size < s₁.tokens.size := by
        have := ScannerCorrectness.scanNextToken_adds_tokens s s₁ h_snt₁; omega
      have h_pref_k : ∀ j, j < s.tokens.size → s₁.tokens[j]? = s.tokens[j]? := by
        intro j hj
        have h_pt := scanNextToken_at_non_colon_preserves_positions s s₁ h_snt₁ h_nc_k j hj
        rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hj, h_pt]
      have h_ph0_false : filt (s₁.tokens[s.tokens.size]'h_N1_k) = false := by
        have := h_ph0₁ h_N1_k; simp [this, filt]
      have h_take_k : (s₁.tokens.toList.take (s.tokens.size + 1)).filter filt
          = (s.tokens.filter filt).toList :=
        block_take_eq_of_getElem? s₁.tokens s.tokens s.tokens.size filt rfl h_N1_k h_pref_k h_ph0_false
      -- Colon scan
      have h_flow₁ : s₁.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
      have h_indent₁ : s₁.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv_ok : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      have h_corr₁_col : ScannerSurfCorr s₁
          ⟨':' :: ' ' :: (['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest), s₁.col⟩ :=
        h_corr₁
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁
          (['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest)
          h_corr₁_col h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv_ok
          h_atol₁ h_endline₁
      have h_lt_k : s₁.simpleKey.tokenIndex + 1 < s₁.tokens.size := by rw [h_tidx₁]; exact h_szlt₁
      have h_ph_k : (s₁.tokens[s₁.simpleKey.tokenIndex + 1]'h_lt_k).val = .placeholder := by
        simp only [h_tidx₁]; exact h_ph1₁ h_szlt₁
      obtain ⟨s₂', pos_v, h_snt₂', h_block_colon⟩ :=
        scanNextToken_flow_value_block s₁
          (['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest)
          h_corr₁_col h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv_ok
          h_atol₁ h_endline₁ h_ska₁ h_poss₁ h_lt_k h_ph_k
      have h_s2_eq : s₂' = s₂ := Option.some.inj (Except.ok.inj (h_snt₂'.symm.trans h_snt₂))
      rw [h_s2_eq] at h_block_colon
      have h_grew_colon : (s₂.tokens.filter filt).size > (s₁.tokens.filter filt).size := by
        have hcorr_kq' : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest)), s₁.col⟩ :=
          h_corr₁_col
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':' _ hcorr_kq'
          h_flow₁ h_indent₁ h_col₁ (by decide) (by decide) (by decide) h_snt₂
      -- Re-anchor colon output
      have h_hk : s.tokens.size + 1 < s₁.tokens.toList.length := by
        rw [Array.length_toList]; exact h_szlt₁
      have h_ph1_false : filt (s₁.tokens.toList[s.tokens.size + 1]'h_hk) = false := by
        rw [Array.getElem_toList]
        have h := h_ph1₁ h_szlt₁; simp [h, filt]
      have h_full_k : s₁.tokens.toList.filter filt
          = (s.tokens.filter filt).toList ++ [tok_k] := by
        rw [← Array.toList_filter, h_push_k, Array.toList_push]
      have h_drop_k : (s₁.tokens.toList.drop (s.tokens.size + 2)).filter filt = [tok_k] :=
        List_filter_drop_succ_of_take s₁.tokens.toList (s.tokens.size + 1) filt
          h_hk h_ph1_false (s.tokens.filter filt).toList [tok_k] h_take_k h_full_k
      let keyTok : Positioned YamlToken := ⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩
      let valueTok : Positioned YamlToken := ⟨pos_v, .value, pos_v⟩
      rw [h_tidx₁, h_take_k, h_drop_k] at h_block_colon
      have h_block_kc : (s₂.tokens.filter filt).toList =
          (s.tokens.filter filt).toList ++ [keyTok, tok_k, valueTok] := by
        rw [h_block_colon]; simp only [keyTok, valueTok, List.append_assoc,
                                        List.cons_append, List.nil_append]
      -- Preprocessing + value scan
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: '"' :: ((escapeString sv.content).toList ++ ['"'] ++ rest), s₂.col⟩ :=
        h_corr₂
      obtain ⟨s₃, h_corr₃, h_s3_flow, h_fl₃, h_s3_indent, h_col₃, h_dp₃, h_ids₃, h_ek₃,
              _h_line₃, h_pp_eq, h_atol_tr₃, h_endline_tr₃, h_stack₃, h_toks₃, _, h_ska₃⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ '"' ((escapeString sv.content).toList ++ ['"'] ++ rest)
          h_corr₂_ws h_flow₂ (by decide) (by decide) (by decide) h_indent₂
      have hcorr₃' : ScannerSurfCorr s₃
          ⟨['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest, s₃.col⟩ := by
        have : '"' :: ((escapeString sv.content).toList ++ ['"'] ++ rest) =
               ['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest := by
          simp [List.cons_append]
        rw [this] at h_corr₃; exact h_corr₃
      have hcorr₃_q : ScannerSurfCorr s₃
          ⟨'"' :: ((escapeString sv.content).toList ++ ['"'] ++ rest), s₃.col⟩ :=
        h_corr₃
      obtain ⟨s_v, h_snt_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v, h_ek_v, h_col_v, h_last_v,
              _h_ska_v, h_line_v, h_atol_v, h_endline_v, h_stack_v⟩ :=
        scanNextToken_flow_scanDoubleQuoted s₃ sv.content rest hcorr₃'
          h_s3_flow (by unfold ScannerState.currentIndent; rw [h_ids₃]; exact h_indent₂)
          (by omega) (h_atol_tr₃ h_atol₂) (h_endline_tr₃ h_endline₂)
      obtain ⟨tok_v, h_tok_v_val, h_push_v⟩ :=
        scanNextToken_flow_scalar_filtered_push_content s₃ sv.content rest hcorr₃_q
          h_s3_flow (by unfold ScannerState.currentIndent; rw [h_ids₃]; exact h_indent₂)
          (by omega) h_snt_v
      have h_snt_eq_v : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_filt_le_v : (s₂.tokens.filter filt).size ≤ (s₃.tokens.filter filt).size := by
        simp [h_toks₃]
      have h_chain_sv : ScanChainGrew filt s₂ 1 s_v :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_v h_filt_le_v (ScanChainGrew.single h_snt_v
          (by rw [h_push_v]; simp [Array.size_push]))
      have h_s3_filt : (s₃.tokens.filter filt).toList = (s₂.tokens.filter filt).toList := by
        rw [h_toks₃]
      have h_filter_sv : (s_v.tokens.filter filt).toList =
          (s.tokens.filter filt).toList ++ [keyTok, tok_k, valueTok, tok_v] := by
        have h1 : (s_v.tokens.filter filt).toList = (s₃.tokens.filter filt).toList ++ [tok_v] := by
          rw [h_push_v, Array.toList_push]
        rw [h1, h_s3_filt, h_block_kc]; simp [List.append_assoc]
      -- Singleton result
      have h_chain_all : ScanChainGrew filt s (1 + (1 + 1)) s_v :=
        (ScanChainGrew.single h_snt₁ (by rw [h_push_k]; simp [Array.size_push])).trans
          ((ScanChainGrew.single h_snt₂ h_grew_colon).trans h_chain_sv)
      refine ⟨1 + (1 + 1), s_v, [keyTok, tok_k, valueTok, tok_v],
              h_chain_all, h_corr_v,
              by rw [h_fl_v, h_fl₃, h_fl₂, h_fl₁],
              by rw [h_dp_v, h_dp₃, h_dp₂, h_dp₁],
              by rw [h_ids_v, h_ids₃, h_ids₂, h_ids₁],
              by rw [h_ek_v, h_ek₃, h_ek₂]; exact h_ek.symm,
              h_col_v,
              by unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_v]; omega),
              by unfold ScannerState.currentIndent; rw [h_ids_v, h_ids₃]; exact h_indent₂,
              h_line_v.trans (_h_line₃.trans (_h_line₂.trans h_line₁)), h_atol_v, h_endline_v,
              by rw [h_stack_v, h_stack₃, h_stack₂, h_stack₁],
              h_filter_sv, ?_, ?_, ?_⟩
      · rfl  -- block.length = 4 = 5 * 1 - 1
      · intro j hj sk' sv' h_pair
        obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h_pair
        obtain ⟨hsk', hsv'⟩ := Prod.mk.inj h_pair
        obtain rfl : sk = sk' := by rwa [hsk, YamlValue.scalar.injEq] at hsk'
        obtain rfl : sv = sv' := by rwa [hsv, YamlValue.scalar.injEq] at hsv'
        refine ⟨by simp, ?_, by simp, ?_⟩
        · simp only [show (5 : Nat) * 0 + 1 = 1 from rfl,
                     List.getElem!_cons_succ, List.getElem!_cons_zero]; exact h_tok_k_val
        · simp only [show (5 : Nat) * 0 + 3 = 3 from rfl,
                     List.getElem!_cons_succ, List.getElem!_cons_succ,
                     List.getElem!_cons_succ, List.getElem!_cons_zero]; exact h_tok_v_val
      · intro j hj; simp only [List.length_cons, List.length_nil] at hj; omega
    | cons p' tail' =>
      -- ── MULTI-PAIR CASE: pairs = p :: p' :: tail' ────────────────────────────
      obtain ⟨sk', sv', hsk', hsv'⟩ := h_all p' (.tail _ (.head _))
      let rest_inner : List Char :=
        ',' :: ' ' :: (emit.emitPairList (p' :: tail')).toList ++ rest
      -- rest_k: everything after the closing key quote (includes ": sv" + rest_inner)
      let rest_k : List Char :=
        ':' :: ' ' :: ['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest_inner
      -- Surface reduction: emitPairList(p :: p' :: tail') ++ rest = ['"'] ++ esc_k ++ ['"'] ++ rest_k
      have h_eq : (emit.emitPairList (p :: p' :: tail')).toList ++ rest =
          ['"'] ++ (escapeString sk.content).toList ++ ['"'] ++ rest_k := by
        simp only [emit.emitPairList, emit, emitScalar, String.toList_append, hsk, hsv,
                   List.append_assoc,
                   show rest_k = ':' :: ' ' :: ['"'] ++
                     (escapeString sv.content).toList ++ ['"'] ++ rest_inner from rfl]
        rfl
      have hcorr_k' : ScannerSurfCorr s
          ⟨['"'] ++ (escapeString sk.content).toList ++ ['"'] ++ rest_k, s.col⟩ := by
        rw [← h_eq]; exact hcorr
      -- hcorr_kq: ['"'] ++ esc_k ++ ['"'] ++ rest_k = '"' :: (esc_k ++ ['"'] ++ rest_k) by defn
      have hcorr_kq : ScannerSurfCorr s
          ⟨'"' :: ((escapeString sk.content).toList ++ ['"'] ++ rest_k), s.col⟩ :=
        hcorr_k'
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_last₁, h_ska₁,
              h_line₁, h_atol₁, h_endline₁, h_stack₁⟩ :=
        scanNextToken_flow_scanDoubleQuoted s sk.content rest_k hcorr_k' h_flow h_indent h_col
          h_atol h_endline
      obtain ⟨s₁', h_snt₁', h_poss₁, h_tidx₁, h_szlt₁, h_ph0₁, h_ph1₁⟩ :=
        scanNextToken_flow_scalar_savedKey s sk.content rest_k hcorr_k' h_flow h_indent h_col
          h_ek h_ska
      have h_s1_eq : s₁' = s₁ := Option.some.inj (Except.ok.inj (h_snt₁'.symm.trans h_snt₁))
      rw [h_s1_eq] at h_poss₁ h_tidx₁ h_szlt₁ h_ph0₁ h_ph1₁
      clear h_snt₁' s₁' h_s1_eq
      obtain ⟨tok_k, h_tok_k_val, h_push_k⟩ :=
        scanNextToken_flow_scalar_filtered_push_content s sk.content rest_k hcorr_kq
          h_flow h_indent h_col h_snt₁
      -- Key re-anchoring for colon scan
      have h_nc_k : ∀ t c', scanNextToken_preprocess s = .ok (some (t, c')) → c' ≠ ':' :=
        no_colon_of_preprocess_flow s '"'
          ((escapeString sk.content).toList ++ ['"'] ++ rest_k)
          s.col hcorr_kq h_flow (by decide) (by decide) (by decide) (by decide)
      have h_N1_k : s.tokens.size < s₁.tokens.size := by
        have := ScannerCorrectness.scanNextToken_adds_tokens s s₁ h_snt₁; omega
      have h_pref_k : ∀ j, j < s.tokens.size → s₁.tokens[j]? = s.tokens[j]? := by
        intro j hj
        have h_pt := scanNextToken_at_non_colon_preserves_positions s s₁ h_snt₁ h_nc_k j hj
        rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hj, h_pt]
      have h_ph0_false : filt (s₁.tokens[s.tokens.size]'h_N1_k) = false := by
        have := h_ph0₁ h_N1_k; simp [this, filt]
      have h_take_k : (s₁.tokens.toList.take (s.tokens.size + 1)).filter filt
          = (s.tokens.filter filt).toList :=
        block_take_eq_of_getElem? s₁.tokens s.tokens s.tokens.size filt rfl h_N1_k h_pref_k h_ph0_false
      -- Colon scan
      have h_flow₁ : s₁.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
      have h_indent₁ : s₁.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv_ok : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      have h_corr₁_col : ScannerSurfCorr s₁
          ⟨':' :: ' ' :: (['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest_inner), s₁.col⟩ :=
        h_corr₁
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁
          (['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest_inner)
          h_corr₁_col h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv_ok
          h_atol₁ h_endline₁
      have h_lt_k : s₁.simpleKey.tokenIndex + 1 < s₁.tokens.size := by rw [h_tidx₁]; exact h_szlt₁
      have h_ph_k : (s₁.tokens[s₁.simpleKey.tokenIndex + 1]'h_lt_k).val = .placeholder := by
        simp only [h_tidx₁]; exact h_ph1₁ h_szlt₁
      obtain ⟨s₂', pos_v, h_snt₂', h_block_colon⟩ :=
        scanNextToken_flow_value_block s₁
          (['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest_inner)
          h_corr₁_col h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv_ok
          h_atol₁ h_endline₁ h_ska₁ h_poss₁ h_lt_k h_ph_k
      have h_s2_eq : s₂' = s₂ := Option.some.inj (Except.ok.inj (h_snt₂'.symm.trans h_snt₂))
      rw [h_s2_eq] at h_block_colon
      have h_grew_colon : (s₂.tokens.filter filt).size > (s₁.tokens.filter filt).size := by
        have hcorr₁_cons : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest_inner)), s₁.col⟩ :=
          h_corr₁_col
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':' _ hcorr₁_cons
          h_flow₁ h_indent₁ h_col₁ (by decide) (by decide) (by decide) h_snt₂
      -- Re-anchor colon output
      have h_hk : s.tokens.size + 1 < s₁.tokens.toList.length := by
        rw [Array.length_toList]; exact h_szlt₁
      have h_ph1_false : filt (s₁.tokens.toList[s.tokens.size + 1]'h_hk) = false := by
        rw [Array.getElem_toList]
        have h := h_ph1₁ h_szlt₁; simp [h, filt]
      have h_full_k : s₁.tokens.toList.filter filt
          = (s.tokens.filter filt).toList ++ [tok_k] := by
        rw [← Array.toList_filter, h_push_k, Array.toList_push]
      have h_drop_k : (s₁.tokens.toList.drop (s.tokens.size + 2)).filter filt = [tok_k] :=
        List_filter_drop_succ_of_take s₁.tokens.toList (s.tokens.size + 1) filt
          h_hk h_ph1_false (s.tokens.filter filt).toList [tok_k] h_take_k h_full_k
      let keyTok : Positioned YamlToken := ⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩
      let valueTok : Positioned YamlToken := ⟨pos_v, .value, pos_v⟩
      rw [h_tidx₁, h_take_k, h_drop_k] at h_block_colon
      have h_block_kc : (s₂.tokens.filter filt).toList =
          (s.tokens.filter filt).toList ++ [keyTok, tok_k, valueTok] := by
        rw [h_block_colon]; simp only [keyTok, valueTok, List.append_assoc,
                                        List.cons_append, List.nil_append]
      -- Preprocessing + value scan
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: '"' :: ((escapeString sv.content).toList ++ ['"'] ++ rest_inner), s₂.col⟩ :=
        h_corr₂
      obtain ⟨s₃, h_corr₃, h_s3_flow, h_fl₃, h_s3_indent, h_col₃, h_dp₃, h_ids₃, h_ek₃,
              _h_line₃, h_pp_eq, h_atol_tr₃, h_endline_tr₃, h_stack₃, h_toks₃, _, h_ska₃⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ '"' ((escapeString sv.content).toList ++ ['"'] ++ rest_inner)
          h_corr₂_ws h_flow₂ (by decide) (by decide) (by decide) h_indent₂
      have hcorr₃' : ScannerSurfCorr s₃
          ⟨['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest_inner, s₃.col⟩ := by
        have : '"' :: ((escapeString sv.content).toList ++ ['"'] ++ rest_inner) =
               ['"'] ++ (escapeString sv.content).toList ++ ['"'] ++ rest_inner := by
          simp [List.cons_append]
        rw [this] at h_corr₃; exact h_corr₃
      have hcorr₃_q : ScannerSurfCorr s₃
          ⟨'"' :: ((escapeString sv.content).toList ++ ['"'] ++ rest_inner), s₃.col⟩ :=
        h_corr₃
      -- rest for value scan = rest_inner = ',' :: ' ' :: ...
      obtain ⟨s_v, h_snt_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v, h_ek_v, h_col_v, h_last_v,
              _h_ska_v, h_line_v, h_atol_v, h_endline_v, h_stack_v⟩ :=
        scanNextToken_flow_scanDoubleQuoted s₃ sv.content rest_inner hcorr₃'
          h_s3_flow (by unfold ScannerState.currentIndent; rw [h_ids₃]; exact h_indent₂)
          (by omega) (h_atol_tr₃ h_atol₂) (h_endline_tr₃ h_endline₂)
      obtain ⟨tok_v, h_tok_v_val, h_push_v⟩ :=
        scanNextToken_flow_scalar_filtered_push_content s₃ sv.content rest_inner hcorr₃_q
          h_s3_flow (by unfold ScannerState.currentIndent; rw [h_ids₃]; exact h_indent₂)
          (by omega) h_snt_v
      have h_snt_eq_v : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_filt_le_v : (s₂.tokens.filter filt).size ≤ (s₃.tokens.filter filt).size := by
        simp [h_toks₃]
      have h_chain_sv : ScanChainGrew filt s₂ 1 s_v :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_v h_filt_le_v (ScanChainGrew.single h_snt_v
          (by rw [h_push_v]; simp [Array.size_push]))
      have h_s3_filt : (s₃.tokens.filter filt).toList = (s₂.tokens.filter filt).toList := by
        rw [h_toks₃]
      have h_filter_sv : (s_v.tokens.filter filt).toList =
          (s.tokens.filter filt).toList ++ [keyTok, tok_k, valueTok, tok_v] := by
        have h1 : (s_v.tokens.filter filt).toList = (s₃.tokens.filter filt).toList ++ [tok_v] := by
          rw [h_push_v, Array.toList_push]
        rw [h1, h_s3_filt, h_block_kc]; simp [List.append_assoc]
      -- ── COMMA SCAN ──────────────────────────────────────────────────────────
      have h_flow_v : s_v.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_v]; omega)
      have h_indent_v : s_v.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids_v, h_ids₃]; exact h_indent₂
      have h_corr_v_comma : ScannerSurfCorr s_v
          ⟨',' :: ' ' :: (emit.emitPairList (p' :: tail')).toList ++ rest, s_v.col⟩ :=
        h_corr_v
      obtain ⟨s_c, h_snt_c, h_corr_c, h_fl_c, h_dp_c, h_ids_c, h_ek_c, h_col_c,
              h_line_c, h_atol_c, h_endline_c, h_stack_c⟩ :=
        scanNextToken_flow_comma s_v
          (' ' :: (emit.emitPairList (p' :: tail')).toList ++ rest)
          h_corr_v_comma h_flow_v h_indent_v (by omega) h_last_v h_atol_v h_endline_v
      obtain ⟨feTok, h_feTok_val, h_push_c⟩ :=
        scanNextToken_flow_comma_filtered_push s_v
          (' ' :: (emit.emitPairList (p' :: tail')).toList ++ rest)
          h_corr_v_comma h_flow_v h_indent_v (by omega) h_last_v h_snt_c
      have h_grew_c : (s_c.tokens.filter filt).size > (s_v.tokens.filter filt).size := by
        rw [h_push_c]; simp [Array.size_push]
      obtain ⟨h_ska_c, _⟩ :=
        scanNextToken_flow_comma_simpleKey s_v
          (' ' :: (emit.emitPairList (p' :: tail')).toList ++ rest)
          h_corr_v_comma h_flow_v h_indent_v (by omega) h_last_v h_snt_c
      -- ── SPACE PREPROCESS BEFORE NEXT PAIR ───────────────────────────────────
      obtain ⟨c_f, rest_f, h_first_f, h_nws_f, h_nlb_f, h_nc_f⟩ :=
        emitPairList_first_char p' tail'
      have h_flow_c : s_c.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_c, h_fl_v]; omega)
      have h_indent_c : s_c.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids_c, h_ids_v, h_ids₃]; exact h_indent₂
      have h_corr_c_ws : ScannerSurfCorr s_c
          ⟨' ' :: c_f :: (rest_f ++ rest), s_c.col⟩ := by
        have : ' ' :: (emit.emitPairList (p' :: tail')).toList ++ rest =
               ' ' :: c_f :: (rest_f ++ rest) := by rw [h_first_f]; simp [List.cons_append]
        rwa [this] at h_corr_c
      obtain ⟨s_pp, h_corr_pp, h_s_pp_flow, h_fl_pp, h_s_pp_indent, h_col_pp, h_dp_pp, h_ids_pp,
              h_ek_pp, _h_line_pp, h_pp_eq_pp, h_atol_tr_pp, h_endline_tr_pp, h_stack_pp,
              h_toks_pp, _, h_ska_pp⟩ :=
        scanNextToken_preprocess_flow_ws1 s_c c_f (rest_f ++ rest) h_corr_c_ws h_flow_c
          h_nws_f h_nlb_f h_nc_f h_indent_c
      have h_corr_pp' : ScannerSurfCorr s_pp
          ⟨(emit.emitPairList (p' :: tail')).toList ++ rest, s_pp.col⟩ := by
        have : c_f :: (rest_f ++ rest) = (emit.emitPairList (p' :: tail')).toList ++ rest := by
          rw [h_first_f]; simp [List.cons_append]
        rwa [this] at h_corr_pp
      -- ── IH APPLICATION ──────────────────────────────────────────────────────
      have h_tail_ne : p' :: tail' ≠ [] := List.cons_ne_nil _ _
      have h_tail_all : ∀ q ∈ (p' :: tail' : List _),
          ∃ sk_q sv_q : Scalar, q.1 = .scalar sk_q ∧ q.2 = .scalar sv_q :=
        fun q hq => h_all q (.tail _ hq)
      have h_ska_pp_true : s_pp.simpleKeyAllowed = true := by rw [h_ska_pp, h_ska_c]
      have h_sync_pp : s_pp.simpleKeyStack.size = s_pp.flowLevel := by
        rw [h_stack_pp, h_stack_c, h_stack_v, h_stack₃, h_stack₂, h_stack₁,
            h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_sync
      obtain ⟨n_pp, s_end, block_rest, h_chain_pp, h_corr_end,
              h_fl_end, h_dp_end, h_ids_end, h_ek_end, h_col_end,
              h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end,
              h_block_pp, h_len_pp, h_pw_pp, h_fe_pp⟩ :=
        ih h_tail_ne h_tail_all s_pp rest h_corr_pp'
          h_s_pp_flow
          (by rw [h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_s_pp_indent]; exact h_indent_c)
          (by rw [h_col_pp]; omega) (by rw [h_ek_pp, h_ek_c, h_ek_v, h_ek₃]; exact h_ek₂)
          (h_atol_tr_pp h_atol_c)
          (h_endline_tr_pp h_endline_c)
          h_ska_pp_true h_sync_pp
      -- ── LIFT IH CHAIN THROUGH PREPROCESSING ─────────────────────────────────
      have h_n_pp_pos : n_pp ≥ 1 := by
        obtain ⟨sk_h, sv_h, hsk_h, hsv_h⟩ := h_tail_all p' (.head _)
        have h_pair_0 : (p' :: tail')[0]? = some (.scalar sk_h, .scalar sv_h) := by
          simp only [List.getElem?_cons_zero]; exact congrArg some (Prod.ext hsk_h hsv_h)
        obtain ⟨h_bound, _, _, _⟩ := h_pw_pp 0 (by simp) sk_h sv_h h_pair_0
        rcases Nat.eq_zero_or_pos n_pp with rfl | h_pos
        · exfalso
          have h_s_eq := ScanChainGrew.eq_of_zero h_chain_pp
          rw [h_s_eq] at h_block_pp
          have h_len' := congrArg List.length h_block_pp
          rw [List.length_append] at h_len'; omega
        · exact h_pos
      obtain ⟨m_pp, rfl⟩ : ∃ m, n_pp = m + 1 := ⟨n_pp - 1, by omega⟩
      have h_snt_eq_pp : scanNextToken s_c = scanNextToken s_pp :=
        scanNextToken_eq_of_preprocess s_c s_pp h_pp_eq_pp
      have h_filt_le_pp : (s_c.tokens.filter filt).size ≤ (s_pp.tokens.filter filt).size := by
        simp [h_toks_pp]
      have h_chain_c_end : ScanChainGrew filt s_c (m_pp + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_pp h_filt_le_pp h_chain_pp
      -- ── COMBINED FILTER EQUATION ─────────────────────────────────────────────
      have h_s_pp_filt : (s_pp.tokens.filter filt).toList = (s_c.tokens.filter filt).toList := by
        rw [h_toks_pp]
      have h_filter_end : (s_end.tokens.filter filt).toList =
          (s.tokens.filter filt).toList ++
          ([keyTok, tok_k, valueTok, tok_v, feTok] ++ block_rest) := by
        have h3 : (s_c.tokens.filter filt).toList = (s_v.tokens.filter filt).toList ++ [feTok] := by
          rw [h_push_c, Array.toList_push]
        rw [h_block_pp, h_s_pp_filt, h3, h_filter_sv]; simp [List.append_assoc]
      -- ── FULL CHAIN ───────────────────────────────────────────────────────────
      have h_grew_k : (s₁.tokens.filter filt).size > (s.tokens.filter filt).size := by
        rw [h_push_k]; simp [Array.size_push]
      have h_chain_all : ScanChainGrew filt s (1 + (1 + 1) + (1 + (m_pp + 1))) s_end :=
        ((ScanChainGrew.single h_snt₁ h_grew_k).trans
          ((ScanChainGrew.single h_snt₂ h_grew_colon).trans h_chain_sv)).trans
        ((ScanChainGrew.single h_snt_c h_grew_c).trans h_chain_c_end)
      -- ── BLOCK LENGTH ─────────────────────────────────────────────────────────
      have h_len : ([keyTok, tok_k, valueTok, tok_v, feTok] ++ block_rest).length =
          5 * (p :: p' :: tail').length - 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        have := h_len_pp; simp only [List.length_cons] at this; omega
      -- ── POINTWISE CONTENT ────────────────────────────────────────────────────
      have h_pointwise : ∀ j : Nat,
          j < (p :: p' :: tail').length →
          ∀ sk_j sv_j : Scalar,
          (p :: p' :: tail')[j]? = some (.scalar sk_j, .scalar sv_j) →
          5 * j + 1 < ([keyTok, tok_k, valueTok, tok_v, feTok] ++ block_rest).length ∧
          ([keyTok, tok_k, valueTok, tok_v, feTok] ++ block_rest)[5 * j + 1]!.val =
              .scalar sk_j.content .doubleQuoted ∧
          5 * j + 3 < ([keyTok, tok_k, valueTok, tok_v, feTok] ++ block_rest).length ∧
          ([keyTok, tok_k, valueTok, tok_v, feTok] ++ block_rest)[5 * j + 3]!.val =
              .scalar sv_j.content .doubleQuoted := by
        intro j hj sk_j sv_j h_pair
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h_pair
          obtain ⟨hsk_j, hsv_j⟩ := Prod.mk.inj h_pair
          obtain rfl : sk = sk_j := by rwa [hsk, YamlValue.scalar.injEq] at hsk_j
          obtain rfl : sv = sv_j := by rwa [hsv, YamlValue.scalar.injEq] at hsv_j
          refine ⟨by simp, ?_, by simp, ?_⟩
          · simp only [show (5 : Nat) * 0 + 1 = 1 from rfl]; exact h_tok_k_val
          · simp only [show (5 : Nat) * 0 + 3 = 3 from rfl]; exact h_tok_v_val
        | succ j' =>
          simp only [List.length_cons] at hj
          simp only [List.getElem?_cons_succ] at h_pair
          obtain ⟨h_lt_r, h_k_r, h_lt_rv, h_v_r⟩ :=
            h_pw_pp j' (by simp only [List.length_cons]; omega) sk_j sv_j h_pair
          refine ⟨by simp only [List.length_append, List.length_cons]; omega, ?_,
                  by simp only [List.length_append, List.length_cons]; omega, ?_⟩
          · rw [show 5 * (j' + 1) + 1 = 5 * j' + 1 + 5 from by omega]
            simp only [show 5 * j' + 1 + 5 = 5 * j' + 1 + 4 + 1 from by omega,
                       show 5 * j' + 1 + 4 = 5 * j' + 1 + 3 + 1 from by omega,
                       show 5 * j' + 1 + 3 = 5 * j' + 1 + 2 + 1 from by omega,
                       show 5 * j' + 1 + 2 = 5 * j' + 1 + 1 + 1 from by omega,
                       show 5 * j' + 1 + 1 = 5 * j' + 1 + 0 + 1 from by omega]
            exact h_k_r
          · rw [show 5 * (j' + 1) + 3 = 5 * j' + 3 + 5 from by omega]
            simp only [show 5 * j' + 3 + 5 = 5 * j' + 3 + 4 + 1 from by omega,
                       show 5 * j' + 3 + 4 = 5 * j' + 3 + 3 + 1 from by omega,
                       show 5 * j' + 3 + 3 = 5 * j' + 3 + 2 + 1 from by omega,
                       show 5 * j' + 3 + 2 = 5 * j' + 3 + 1 + 1 from by omega,
                       show 5 * j' + 3 + 1 = 5 * j' + 3 + 0 + 1 from by omega]
            exact h_v_r
      -- ── FLOW ENTRY FACTS ─────────────────────────────────────────────────────
      have h_fe : ∀ j : Nat, j + 1 < (p :: p' :: tail').length →
          5 * j + 4 < ([keyTok, tok_k, valueTok, tok_v, feTok] ++ block_rest).length ∧
          ([keyTok, tok_k, valueTok, tok_v, feTok] ++ block_rest)[5 * j + 4]!.val = .flowEntry := by
        intro j hj
        cases j with
        | zero =>
          refine ⟨by simp, ?_⟩
          simp only [show (5 : Nat) * 0 + 4 = 4 from rfl]
          exact h_feTok_val
        | succ j' =>
          simp only [List.length_cons] at hj
          obtain ⟨h_lt_fe, h_fe_val⟩ := h_fe_pp j' (by simp only [List.length_cons]; omega)
          refine ⟨by simp only [List.length_append, List.length_cons]; omega, ?_⟩
          rw [show 5 * (j' + 1) + 4 = 5 * j' + 4 + 5 from by omega]
          simp only [show 5 * j' + 4 + 5 = 5 * j' + 4 + 4 + 1 from by omega,
                     show 5 * j' + 4 + 4 = 5 * j' + 4 + 3 + 1 from by omega,
                     show 5 * j' + 4 + 3 = 5 * j' + 4 + 2 + 1 from by omega,
                     show 5 * j' + 4 + 2 = 5 * j' + 4 + 1 + 1 from by omega,
                     show 5 * j' + 4 + 1 = 5 * j' + 4 + 0 + 1 from by omega]
          exact h_fe_val
      exact ⟨1 + (1 + 1) + (1 + (m_pp + 1)), s_end,
             [keyTok, tok_k, valueTok, tok_v, feTok] ++ block_rest,
             h_chain_all, h_corr_end,
             by rw [h_fl_end, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁],
             by rw [h_dp_end, h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁],
             by rw [h_ids_end, h_ids_pp, h_ids_c, h_ids_v, h_ids₃, h_ids₂, h_ids₁],
             by rw [h_ek_end, h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂]; exact h_ek.symm,
             h_col_end, h_flow_end, h_indent_end,
             h_line_end.trans (_h_line_pp.trans (h_line_c.trans
               (h_line_v.trans (_h_line₃.trans (_h_line₂.trans h_line₁))))),
             h_atol_end, h_endline_end,
             by rw [h_stack_end, h_stack_pp, h_stack_c, h_stack_v, h_stack₃, h_stack₂, h_stack₁],
             h_filter_end, h_len, h_pointwise, h_fe⟩

/-- **R607. All-scalar token-array content pin for flow mappings.**

    If `scanFiltered ("{" ++ emitPairList pairs ++ "}") = .ok tokens` with a non-empty all-scalar
    `pairs`, then `tokens.size = 5 * pairs.length + 3` and for each `j < pairs.length`:
    `tokens[2 + 5 * j + 1]!.val = .scalar sk.content .doubleQuoted` (key) and
    `tokens[2 + 5 * j + 3]!.val = .scalar sv.content .doubleQuoted` (value).

    Proof: chain-replay of `"{" ++ emitPairList ++ "}"` (mapping mirror of R597):
    1. `scanNextToken_flow_open_mapping_init` yields `s₁` with filtered prefix `[streamStart, flowMappingStart]`.
    2. R606 (`emitPairList_allScalar_body_content_at`) yields `s₂` and body `block`.
    3. `scanNextToken_flow_close_mapping_outermost_ext` yields `s₃`.
    4. `scanFiltered_tokens_eq_of_chain_short_stack` gives `tokens = s₂.filter ++ [tok_fme, streamEnd]`.
    5. Offset-2 index arithmetic connects `tokens[2 + 5*j + k]` to `block[5*j + k]`. -/
theorem scanFiltered_emitMap_allScalar_pair_at
    (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all : ∀ p ∈ pairs, ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs ++ "}") = .ok tokens) :
    tokens.size = 5 * pairs.length + 3 ∧
    tokens[1]!.val = .flowMappingStart ∧
    (∀ j : Nat, j < pairs.length → ∀ sk sv : Scalar, pairs[j]? = some (.scalar sk, .scalar sv) →
        tokens[2 + 5 * j + 1]!.val = .scalar sk.content .doubleQuoted ∧
        tokens[2 + 5 * j + 3]!.val = .scalar sv.content .doubleQuoted) ∧
    (∀ j : Nat, j + 1 < pairs.length →
        tokens[2 + 5 * j + 4]!.val = .flowEntry) ∧
    tokens[5 * pairs.length + 1]!.val = .flowMappingEnd := by
  let input := "{" ++ emit.emitPairList pairs ++ "}"
  have h_toList : input.toList = '{' :: (emit.emitPairList pairs).toList ++ ['}'] := by
    simp only [input, String.toList_append]; rfl
  -- ═══ Step 1: open brace → s₁ ═══
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, _h_sk₁, h_filt₁,
          h_sync₁, h_ska₁, _h_ssv₁⟩ :=
    scanNextToken_flow_open_mapping_init input ((emit.emitPairList pairs).toList ++ ['}']) h_toList
  -- ═══ Step 2: body scan via R606 → s₂ and body block ═══
  obtain ⟨_n₂, s₂, block, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_inflow₂,
          h_indent₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_block_eq₂, h_block_len,
          h_block_content, h_block_fe_content⟩ :=
    emitPairList_allScalar_body_content_at pairs h_ne h_all s₁ ['}']
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
  have h_tokens_decomp : tokens = ((s₂.tokens.filter filt).push tok_fme).push
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
  have h_pairs_len_pos : 1 ≤ pairs.length := List.length_pos_iff.mpr h_ne
  have h_tokens_sz : tokens.size = 5 * pairs.length + 3 := by
    rw [h_tokens_decomp]; simp only [Array.size_push]
    rw [h_s2_filt_sz, h_block_len]; omega
  -- ═══ Step 9/10: s₁ filtered-array position 1 = flowMappingStart ═══
  have h_filt₁_val1 : ((s₁.tokens.filter filt)[1]'(by rw [h_filt₁_sz]; omega)).val =
      .flowMappingStart := by
    have hmapped : ((s₁.tokens.filter filt).map (·.val))[1]'
        (by simp [Array.size_map, h_filt₁_sz]) = .flowMappingStart := by
      simp [h_filt₁]
    rwa [Array.getElem_map] at hmapped
  have h_t1 : tokens[1]!.val = .flowMappingStart := by
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
      _ = .flowMappingStart := h_filt₁_val1
  -- ═══ Step 11: all five conclusions ═══
  refine ⟨h_tokens_sz, h_t1, ?_, ?_, ?_⟩
  · -- Key+value scalar pointwise
    intro j hj sk sv h_pair
    obtain ⟨h_k_lt, h_k_val, h_v_lt, h_v_val⟩ := h_block_content j hj sk sv h_pair
    constructor
    · -- key: tokens[2+5*j+1]!.val = .scalar sk.content .doubleQuoted
      have h_klt_s2 : 2 + 5 * j + 1 < (s₂.tokens.filter filt).size := by
        rw [h_s2_filt_sz]; omega
      rw [h_tokens_decomp, getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
      rw [Array.getElem_push_lt (by simp only [Array.size_push]; omega)]
      rw [Array.getElem_push_lt h_klt_s2]
      have h_at_k : (s₂.tokens.filter filt)[2 + 5 * j + 1]'h_klt_s2 =
          block[5 * j + 1]'h_k_lt := by
        have h_lhs_lt : 2 + 5 * j + 1 < (s₂.tokens.filter filt).toList.length := by
          rw [Array.length_toList]; exact h_klt_s2
        have h_opt : (s₂.tokens.filter filt).toList[2 + 5 * j + 1]? = block[5 * j + 1]? := by
          rw [h_block_eq₂, List.getElem?_append_right (by rw [h_s1_filt_len]; omega)]
          congr 1; rw [h_s1_filt_len]; omega
        rw [List.getElem?_eq_getElem h_lhs_lt, List.getElem?_eq_getElem h_k_lt] at h_opt
        have h_list_eq := Option.some.inj h_opt
        rwa [Array.getElem_toList] at h_list_eq
      rw [h_at_k, (getElem!_pos block (5 * j + 1) h_k_lt).symm]
      exact h_k_val
    · -- value: tokens[2+5*j+3]!.val = .scalar sv.content .doubleQuoted
      have h_vlt_s2 : 2 + 5 * j + 3 < (s₂.tokens.filter filt).size := by
        rw [h_s2_filt_sz]; omega
      rw [h_tokens_decomp, getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
      rw [Array.getElem_push_lt (by simp only [Array.size_push]; omega)]
      rw [Array.getElem_push_lt h_vlt_s2]
      have h_at_v : (s₂.tokens.filter filt)[2 + 5 * j + 3]'h_vlt_s2 =
          block[5 * j + 3]'h_v_lt := by
        have h_lhs_lt : 2 + 5 * j + 3 < (s₂.tokens.filter filt).toList.length := by
          rw [Array.length_toList]; exact h_vlt_s2
        have h_opt : (s₂.tokens.filter filt).toList[2 + 5 * j + 3]? = block[5 * j + 3]? := by
          rw [h_block_eq₂, List.getElem?_append_right (by rw [h_s1_filt_len]; omega)]
          congr 1; rw [h_s1_filt_len]; omega
        rw [List.getElem?_eq_getElem h_lhs_lt, List.getElem?_eq_getElem h_v_lt] at h_opt
        have h_list_eq := Option.some.inj h_opt
        rwa [Array.getElem_toList] at h_list_eq
      rw [h_at_v, (getElem!_pos block (5 * j + 3) h_v_lt).symm]
      exact h_v_val
  · -- flowEntry: tokens[2+5*j+4]!.val = .flowEntry for j + 1 < pairs.length
    intro j hj
    obtain ⟨h_fe_lt, h_fe_val⟩ := h_block_fe_content j hj
    have h_felt_s2 : 2 + 5 * j + 4 < (s₂.tokens.filter filt).size := by
      rw [h_s2_filt_sz]; omega
    rw [h_tokens_decomp, getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h_felt_s2]
    have h_at_fe : (s₂.tokens.filter filt)[2 + 5 * j + 4]'h_felt_s2 =
        block[5 * j + 4]'h_fe_lt := by
      have h_lhs_lt : 2 + 5 * j + 4 < (s₂.tokens.filter filt).toList.length := by
        rw [Array.length_toList]; exact h_felt_s2
      have h_opt : (s₂.tokens.filter filt).toList[2 + 5 * j + 4]? = block[5 * j + 4]? := by
        rw [h_block_eq₂, List.getElem?_append_right (by rw [h_s1_filt_len]; omega)]
        congr 1; rw [h_s1_filt_len]; omega
      rw [List.getElem?_eq_getElem h_lhs_lt, List.getElem?_eq_getElem h_fe_lt] at h_opt
      have h_list_eq := Option.some.inj h_opt
      rwa [Array.getElem_toList] at h_list_eq
    rw [h_at_fe, (getElem!_pos block (5 * j + 4) h_fe_lt).symm]
    exact h_fe_val
  · -- flowMappingEnd: tokens[5*pairs.length+1]!.val = .flowMappingEnd
    have h_idx : (s₂.tokens.filter filt).size = 5 * pairs.length + 1 := by
      rw [h_s2_filt_sz, h_block_len]; omega
    have h_idx_list : (s₂.tokens.filter filt).toList.length = 5 * pairs.length + 1 := by
      rw [Array.length_toList]; exact h_idx
    have h_lt : 5 * pairs.length + 1 < tokens.size := by rw [h_tokens_sz]; omega
    have h_lt2 : 5 * pairs.length + 1 < tokens.toList.length := by
      rw [Array.length_toList]; exact h_lt
    have h_tlist : tokens.toList = (s₂.tokens.filter filt).toList ++
        [tok_fme, { pos := s₃.currentPos, val := .streamEnd }] := by
      rw [h_tokens_decomp]; simp [Array.toList_push]
    have h_opt : tokens.toList[5 * pairs.length + 1]? = some tok_fme := by
      rw [h_tlist, List.getElem?_append_right (by rw [h_idx_list]; omega)]
      simp only [h_idx_list, Nat.sub_self, List.getElem?_cons_zero]
    rw [List.getElem?_eq_getElem h_lt2] at h_opt
    have h_elem : tokens.toList[5 * pairs.length + 1]'h_lt2 = tok_fme :=
      Option.some.inj h_opt
    have h_tok_fme_eq : tokens[5 * pairs.length + 1]! = tok_fme := by
      rw [getElem!_pos tokens (5 * pairs.length + 1) h_lt]
      rwa [Array.getElem_toList] at h_elem
    rw [h_tok_fme_eq]; exact h_tok_fme_val

end L4YAML.Proofs.EmitterScannability
