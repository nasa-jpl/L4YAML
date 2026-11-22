/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.Preflow
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.FlowStackChainIx

@[expose] public section Blanket

/-! # `FlowMonoChain.Sync.Scenarios.FlowSeqOpen` — Phase 3 Step
`6f.3b3.emitscans.flowpair` (SS2, `[`-opener track)

**Scenario prerequisite for `emit_scans_in_flowIx` (SS3).** The
`.flowmono.sync.scenarios` family ported the `{`-opener
(`scanNextTokenIx_flow_open_mapping_nested`, `FlowClose` §3) but not
its `[` sibling, because the chain lemmas of that family never needed
the sequence opener. The `emit_scans_in_flowIx` induction (sequence
case) *does*, so it is ported here.

This is the direct sequence analog of `FlowClose` §3
(`scanNextTokenIx_flow_open_mapping_nested`), itself the
nested analog of `scanNextToken_flow_open_nested`.
Every step is identical with `'{' ↦ '['`,
`scanFlowMappingStartIx ↦ scanFlowSequenceStartIx`,
`dispatchFlowIndicators_brace ↦ dispatchFlowIndicators_bracket`, and
`YamlToken.flowMappingStart ↦ YamlToken.flowSequenceStart`.

Threads preprocess → `dispatchStructural` (none) → allowDirectives
update → `dispatchFlowIndicators_bracket` → `scanFlowSequenceStartIx`. Yields
`flowLevel + 1`, `simpleKeyStack.pop = s.simpleKeyStack` (push undone
by `.pop`), `StackEndLineOnLineIx s' s'.line` (the pushed key
inherits `EndLineOnLineIx` from the prior state).
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.CharPredicates
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.Basic
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid
open L4YAML.Proofs.FlowAdjacencyIx
open L4YAML.Surface

variable {input : String}

/-! ## `scanNextTokenIx_flow_open_seq_nested`

`[` inside an existing flow context — push onto `simpleKeyStack`,
increment `flowLevel`, yield `StackEndLineOnLineIx s' s'.line`
inheriting the prior `EndLineOnLineIx s`. -/

/-- Full `scanNextTokenIx` for `'['` inside an existing flow context.
    Indexed twin of `scanNextToken_flow_open_nested`.
    Sequence analog of `scanNextTokenIx_flow_open_mapping_nested`. -/
lemma scanNextTokenIx_flow_open_seq_nested (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨'[' :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_endline : EndLineOnLineIx s)
    (h_dp : s.directivesPresent = false)
    (h_last : ∀ t, lastRealTokenValIx? s.tokens = some t → t.completesFlowValue = false) :
    ∃ s', scanNextTokenIx s = .ok (some s')
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = s.flowLevel + 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = none
      ∧ s'.cursor.pos.col = s.cursor.pos.col + 1
      ∧ s'.cursor.pos.line = s.cursor.pos.line
      ∧ AllTokensOnLineIx s' s'.cursor.pos.line
      ∧ EndLineOnLineIx s'
      ∧ StackEndLineOnLineIx s' s'.cursor.pos.line
      ∧ s'.simpleKeyStack.pop = s.simpleKeyStack
      ∧ (∀ t, lastRealTokenValIx? s'.tokens = some t → t.completesFlowValue = false)
      ∧ s'.flowStack = s.flowStack.push true
      -- item 9r exposures: the `[` re-enables saves, caps the raw array
      -- with a non-`.value` token, pushes the (possibly just-saved)
      -- pending key onto the stack, clears the current one, and only
      -- ever pushes tokens (the incoming array is a `getElem?` prefix).
      ∧ s'.simpleKeyAllowed = true
      ∧ LastRawNotValueIx s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack.push (saveSimpleKeyIx s).simpleKey
      ∧ s'.simpleKey.possible = false
      ∧ s.tokens.tokens.size < s'.tokens.tokens.size
      ∧ (∀ i, i < s.tokens.tokens.size → s'.tokens.tokens[i]? = s.tokens.tokens[i]?)
      ∧ s'.explicitKeyStack = s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol) := by
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, '[')) :=
    scanNextTokenIx_preprocess_flow s '[' rest s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) '[' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if (saveSimpleKeyIx s).allowDirectives then
        { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
      else saveSimpleKeyIx s := ⟨_, rfl⟩
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    rw [h_s_ad_def]; split <;> exact h_sk_flow
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_explicitKeyLine s
  have h_ad_cursor : s_ad.cursor = s.cursor := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_cursor s
  have h_ad_tokens : s_ad.tokens = (saveSimpleKeyIx s).tokens := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
    have h1 : (saveSimpleKeyIx s).simpleKeyStack = s.simpleKeyStack :=
      saveSimpleKeyIx_preserves_simpleKeyStack s
    rw [h_s_ad_def]; split <;> exact h1
  have h_ad_simpleKey : s_ad.simpleKey = (saveSimpleKeyIx s).simpleKey := by
    rw [h_s_ad_def]; split <;> rfl
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad '[' =
      .ok (some (scanFlowSequenceStartIx s_ad)) :=
    dispatchFlowIndicators_bracket s_ad
      (checkFlowAdjacencyIx_ok_of_notCompletes (fun t ht =>
        saveSimpleKeyIx_preserves_completesFalse s h_last t (h_ad_tokens ▸ ht)))
  have h_snt := scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
    (scanFlowSequenceStartIx s_ad) '['
    h_pp h_struct h_s_ad_def (scanNextTokenIx_checkFlowValueIndent_ok_of_inFlow _ _ h_flow) h_flow_disp
    ((saveSimpleKeyIx_directivesPresent s).trans h_dp)
    (scanNextTokenIx_checkBareDocument_ok_of_inFlow _
      ((saveSimpleKeyIx_inFlow s).trans h_flow))
    (scanNextTokenIx_checkDanglingNode_ok_of_inFlow _ _ h_flow)
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨'[' :: rest, s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_ad_cursor]; exact hcorr.chars_from
    · rw [h_ad_cursor]; exact hcorr.input_prefix
    · intro i hi h0
      have hi' : i < s.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s.indents[i]'hi' := by congr 1
      rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowSequenceStartIx_detail s_ad rest h_ad_corr
  have h_s'_corr : ScannerSurfCorrIx (scanFlowSequenceStartIx s_ad)
      ⟨rest, (scanFlowSequenceStartIx s_ad).cursor.pos.col⟩ := by
    rw [h_col_f]; exact h_corr_f
  have h_s'_fl : (scanFlowSequenceStartIx s_ad).flowLevel = s.flowLevel + 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_s'_dp : (scanFlowSequenceStartIx s_ad).directivesPresent = s.directivesPresent :=
    h_dp_f.trans h_ad_dp
  have h_s'_ids : (scanFlowSequenceStartIx s_ad).indents = s.indents :=
    h_ids_f.trans h_ad_ids
  have h_s'_ek : (scanFlowSequenceStartIx s_ad).explicitKeyLine = none :=
    scanFlowSequenceStartIx_explicitKeyLine s_ad
  have h_s'_col : (scanFlowSequenceStartIx s_ad).cursor.pos.col = s.cursor.pos.col + 1 := by
    rw [h_col_f, show s_ad.cursor.pos.col = s.cursor.pos.col from by rw [h_ad_cursor]]
  have ⟨h_peek_ad, h_lt_ad⟩ :=
    peek_of_chars_consIx_state s_ad '[' rest s_ad.cursor.pos.col h_ad_corr
  have h_ad_line : s_ad.cursor.pos.line = s.cursor.pos.line := by rw [h_ad_cursor]
  have h_s'_line : (scanFlowSequenceStartIx s_ad).cursor.pos.line = s.cursor.pos.line := by
    show (s_ad.emit YamlToken.flowSequenceStart).advance.cursor.pos.line = s.cursor.pos.line
    rw [advance_cursor, emit_cursor]
    exact (advance_line_of_peekIx s_ad.cursor '[' h_lt_ad h_peek_ad
      (by decide) (by decide)).trans h_ad_line
  have h_s'_atol :
      AllTokensOnLineIx (scanFlowSequenceStartIx s_ad)
        (scanFlowSequenceStartIx s_ad).cursor.pos.line := by
    rw [h_s'_line]
    have h_atol_sk : AllTokensOnLineIx (saveSimpleKeyIx s) s.cursor.pos.line :=
      AllTokensOnLineIx_saveSimpleKeyIx s s.cursor.pos.line h_atol rfl
    have h_atol_ad : AllTokensOnLineIx s_ad s.cursor.pos.line :=
      AllTokensOnLineIx_of_tokens_eq h_ad_tokens h_atol_sk
    exact AllTokensOnLineIx_scanFlowSequenceStartIx s_ad s.cursor.pos.line h_atol_ad h_ad_line
  -- EndLineOnLineIx: scanFlowSequenceStartIx sets simpleKey.possible = false
  have h_s'_endline : EndLineOnLineIx (scanFlowSequenceStartIx s_ad) := by
    intro h_poss
    rw [scanFlowSequenceStartIx_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  -- StackEndLineOnLineIx: pushed simpleKey inherits EndLineOnLineIx from s
  have h_s_ad_endline : EndLineOnLineIx s_ad := by
    have h_sk_endline : EndLineOnLineIx (saveSimpleKeyIx s) :=
      EndLineOnLineIx_saveSimpleKeyIx s h_endline
    intro h_poss
    rw [h_ad_simpleKey] at h_poss
    have ⟨h1, h2⟩ := h_sk_endline h_poss
    refine ⟨?_, ?_⟩
    · rw [h_ad_simpleKey, h1]
      show (saveSimpleKeyIx s).cursor.pos.line = s_ad.cursor.pos.line
      rw [saveSimpleKeyIx_cursor, h_ad_cursor]
    · rw [h_ad_simpleKey, h2]
      show (saveSimpleKeyIx s).cursor.pos.line = s_ad.cursor.pos.line
      rw [saveSimpleKeyIx_cursor, h_ad_cursor]
  have h_s'_stackend : StackEndLineOnLineIx (scanFlowSequenceStartIx s_ad)
      (scanFlowSequenceStartIx s_ad).cursor.pos.line := by
    unfold StackEndLineOnLineIx
    rw [scanFlowSequenceStartIx_stack_pushed, Array.back?_push, h_s'_line]
    intro h_poss
    have ⟨h1, h2⟩ := h_s_ad_endline h_poss
    refine ⟨h1.trans h_ad_line, ?_⟩
    show s_ad.simpleKey.cursor.pos.line = s.cursor.pos.line
    exact h2.trans h_ad_line
  have h_s'_stackpop : (scanFlowSequenceStartIx s_ad).simpleKeyStack.pop = s.simpleKeyStack := by
    rw [scanFlowSequenceStartIx_stack_pushed, Array.pop_push]; exact h_ad_stack
  have h_s'_last : ∀ t, lastRealTokenValIx? (scanFlowSequenceStartIx s_ad).tokens = some t →
      t.completesFlowValue = false := by
    intro t ht
    rw [scanFlowSequenceStartIx_lastRealTokenVal s_ad] at ht
    simp only [Option.some.injEq] at ht; subst ht; rfl
  have h_s'_push : (scanFlowSequenceStartIx s_ad).flowStack = s.flowStack.push true := by
    rw [scanFlowSequenceStartIx_flowStack]
    congr 1
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_flowStack s
  -- item 9r exposures
  have h_s'_tokens_arr : (scanFlowSequenceStartIx s_ad).tokens.tokens
      = s_ad.tokens.tokens.push (IxToken.mk' (input := input) s_ad.cursor.pos
          YamlToken.flowSequenceStart s_ad.cursor.pos (Nat.le_refl _)
          s_ad.cursor.posBound) := rfl
  have h_sz_ad : s.tokens.tokens.size ≤ s_ad.tokens.tokens.size := by
    rw [h_ad_tokens]
    exact saveSimpleKeyIx_tokens_size_ge s
  have h_s'_ska : (scanFlowSequenceStartIx s_ad).simpleKeyAllowed = true := rfl
  have h_s'_lrv : LastRawNotValueIx (scanFlowSequenceStartIx s_ad) := by
    refine lastRawNotValueIx_of_push ?_ h_s'_tokens_arr
    nofun
  have h_s'_stackpush : (scanFlowSequenceStartIx s_ad).simpleKeyStack
      = s.simpleKeyStack.push (saveSimpleKeyIx s).simpleKey := by
    rw [scanFlowSequenceStartIx_stack_pushed, h_ad_stack, h_ad_simpleKey]
  have h_s'_size : s.tokens.tokens.size
      < (scanFlowSequenceStartIx s_ad).tokens.tokens.size := by
    rw [h_s'_tokens_arr]
    simp only [Array.size_push]
    omega
  have h_s'_prefix : ∀ i, i < s.tokens.tokens.size →
      (scanFlowSequenceStartIx s_ad).tokens.tokens[i]? = s.tokens.tokens[i]? := by
    intro i hi
    have hi_ad : i < s_ad.tokens.tokens.size := Nat.lt_of_lt_of_le hi h_sz_ad
    have h1 : (scanFlowSequenceStartIx s_ad).tokens.tokens[i]?
        = s_ad.tokens.tokens[i]? := by
      rw [h_s'_tokens_arr, Array.getElem?_push_lt hi_ad,
          Array.getElem?_eq_getElem hi_ad]
    rw [h1, h_ad_tokens]
    exact saveSimpleKeyIx_tokens_prefix s i hi
  have h_s'_ekpush : (scanFlowSequenceStartIx s_ad).explicitKeyStack
      = s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol) := by
    rw [scanFlowSequenceStartIx_ek_pushed]
    have h1 : s_ad.explicitKeyStack = s.explicitKeyStack := by
      rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_explicitKeyStack s
    have h2 : s_ad.explicitKeyCol = s.explicitKeyCol := by
      rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_explicitKeyCol s
    rw [h1, h2, h_ad_ek]
  refine ⟨_, h_snt, h_s'_corr, h_s'_fl, h_s'_dp, h_s'_ids, h_s'_ek, h_s'_col,
         h_s'_line, h_s'_atol, h_s'_endline, h_s'_stackend, h_s'_stackpop, h_s'_last,
         h_s'_push, h_s'_ska, h_s'_lrv, h_s'_stackpush,
         scanFlowSequenceStartIx_simpleKey_not_possible s_ad, h_s'_size, h_s'_prefix,
         h_s'_ekpush⟩

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

end Blanket
