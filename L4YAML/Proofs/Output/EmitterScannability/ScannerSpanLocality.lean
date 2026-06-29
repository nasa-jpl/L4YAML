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
    ∀ (h_all : ∀ v ∈ items, ∃ sc : Scalar, v = .scalar sc),
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
        simp only [List.length_cons, List.length_nil, Nat.add_zero]
        have h_lr := h_len₃
        simp only [List.length_cons, List.length_nil, Nat.add_zero] at h_lr
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
          simp only [List.length_cons, List.length_nil, Nat.add_zero] at hj
          have hj' : j' < (.scalar sc' :: vs).length := by simp only [List.length_cons]; omega
          simp only [List.getElem?_cons_succ] at h_item
          obtain ⟨h_bound_r, h_val_r⟩ := h_pointwise₃ j' hj' sc_j h_item
          refine ⟨?_, ?_⟩
          · simp only [List.length_cons, List.length_nil, Nat.add_zero]; omega
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

end L4YAML.Proofs.EmitterScannability
