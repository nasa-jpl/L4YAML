/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.PerDispatch

/-! # `FilteredGrowth.Turn3` — Phase 3 Step `6f.3b3.filteredgrowth.turn3`

**Single session** (legacy `Proofs/Output/EmitterScannability.lean`
lines 6759–6908, ~150 LOC).

Dispatch-level filtered growth (Turn 3 of the EmitterScannability
migration). These compose the per-phase pieces from `.perdispatch`
and `.infra` into a clean "a SUCCESSFUL non-structural dispatch path
strictly grows the filtered token count" witness, then assemble the
in-flow corollary used by the `EmitScansInFlowIx` construction sites.

Ships:

  * **§1 `scanNextTokenIx_via_flow_dispatch_filtered_grows`** —
    `≥ +1` when the flow-indicator dispatcher succeeds (legacy 6769).
  * **§2 `scanNextTokenIx_via_block_dispatch_filtered_grows`** —
    `≥ +1` when the block-indicator dispatcher succeeds (legacy 6787).
  * **§3 `scanNextTokenIx_via_content_dispatch_filtered_grows`** —
    `≥ +1` when the content dispatcher succeeds (legacy 6806).
  * **§4 `scanNextTokenIx_filtered_grows_in_flow`** — in flow context
    (with `currentIndent < 0`, `col > 0`, non-whitespace non-`#`
    next char), every successful `scanNextTokenIx` step strictly grows
    the filtered token count (legacy 6837). The directive branch is
    ruled out by `dispatchStructural_none_flow`, so the conclusion is
    unconditional for emitter outputs.

## Indexed simplification

The three `via_*` lemmas are line-for-line the legacy proofs with the
`.tokens` → `.tokens.tokens` (TokenStream ↔ Array) bridge: each chains
`preprocess_filtered_monoIx` (≥), the `allowDirectives` `if`-split
(=, by `split <;> rfl` since the record update preserves `.tokens`
definitionally), and the matching `dispatch*_filtered_growsIx` (≥ +1).

`scanNextTokenIx_filtered_grows_in_flow` reuses the FlowMonoChain
pipeline lemmas (`scanNextTokenIx_preprocess_flow`,
`dispatchStructural_none_flow`, `checkBlockFlowIndent_ok_flow`) and the
`saveSimpleKeyIx` preservation simp set. The `scanNextTokenIx` body is
structurally identical to legacy `scanNextToken`, so the `unfold` +
`simp only [bind, …, ← hs_ad, …]` reduction and the nested
`match h_*_eq : …` dispatch case analysis transfer verbatim.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth

open L4YAML
open L4YAML.Indexed
open L4YAML.CharPredicates
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain

variable {input : String}

/-! ## §1  `scanNextTokenIx_via_flow_dispatch_filtered_grows` (legacy 6769) -/

lemma scanNextTokenIx_via_flow_dispatch_filtered_grows
    (s s_pp s_ad s_result : ScannerStateIx input) (c : Char)
    (h_pp : scanNextTokenIx_preprocess s = .ok (some (s_pp, c)))
    (_h_struct : scanNextTokenIx_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (_h_check : scanNextTokenIx_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextTokenIx_dispatchFlowIndicators s_ad c = .ok (some s_result)) :
    (s_result.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  have h_pp_mono := preprocess_filtered_monoIx s _ _ h_pp
  have h_ad_eq_filter :
      (s_ad.tokens.tokens.filter (fun t => t.token != .placeholder)).size =
      (s_pp.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
    rw [h_ad_eq]; split <;> rfl
  have h_disp := dispatchFlowIndicators_filtered_growsIx h_flow
  omega

/-! ## §2  `scanNextTokenIx_via_block_dispatch_filtered_grows` (legacy 6787) -/

lemma scanNextTokenIx_via_block_dispatch_filtered_grows
    (s s_pp s_ad s_result : ScannerStateIx input) (c : Char)
    (h_pp : scanNextTokenIx_preprocess s = .ok (some (s_pp, c)))
    (_h_struct : scanNextTokenIx_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (_h_check : scanNextTokenIx_checkBlockFlowIndent s_ad c = .ok ())
    (_h_flow : scanNextTokenIx_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextTokenIx_dispatchBlockIndicators s_ad c = .ok (some s_result)) :
    (s_result.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  have h_pp_mono := preprocess_filtered_monoIx s _ _ h_pp
  have h_ad_eq_filter :
      (s_ad.tokens.tokens.filter (fun t => t.token != .placeholder)).size =
      (s_pp.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
    rw [h_ad_eq]; split <;> rfl
  have h_disp := dispatchBlockIndicators_filtered_growsIx h_block
  omega

/-! ## §3  `scanNextTokenIx_via_content_dispatch_filtered_grows` (legacy 6806) -/

lemma scanNextTokenIx_via_content_dispatch_filtered_grows
    (s s_pp s_ad s_result : ScannerStateIx input) (c : Char)
    (h_pp : scanNextTokenIx_preprocess s = .ok (some (s_pp, c)))
    (_h_struct : scanNextTokenIx_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (_h_check : scanNextTokenIx_checkBlockFlowIndent s_ad c = .ok ())
    (_h_flow : scanNextTokenIx_dispatchFlowIndicators s_ad c = .ok none)
    (_h_block : scanNextTokenIx_dispatchBlockIndicators s_ad c = .ok none)
    (h_content : scanNextTokenIx_dispatchContent s_ad c = .ok s_result) :
    (s_result.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  have h_pp_mono := preprocess_filtered_monoIx s _ _ h_pp
  have h_ad_eq_filter :
      (s_ad.tokens.tokens.filter (fun t => t.token != .placeholder)).size =
      (s_pp.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
    rw [h_ad_eq]; split <;> rfl
  have h_disp := dispatchContent_filtered_growsIx h_content
  omega

/-! ## §4  `scanNextTokenIx_filtered_grows_in_flow` (legacy 6837)

In flow context, every successful `scanNextTokenIx` step strictly
grows the filtered token count. With `s.inFlow = true`,
`s.currentIndent < 0`, `s.cursor.pos.col > 0`, and the next character
being non-whitespace / non-`#`, `dispatchStructural_none_flow` rules
out the directive branch entirely, so the conclusion goes through
unconditionally for emitter outputs. -/

set_option maxHeartbeats 800000 in
lemma scanNextTokenIx_filtered_grows_in_flow
    (s s' : ScannerStateIx input) (c : Char) (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨c :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#')
    (h_snt : scanNextTokenIx s = .ok (some s')) :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size >
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
  -- Step 1: pin down preprocess output.
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, c)) :=
    scanNextTokenIx_preprocess_flow s c rest s.cursor.pos.col hcorr h_flow h_nws h_nlb h_nc
  -- Step 2: structural dispatch returns none (saveSimpleKeyIx preserves
  -- inFlow / currentIndent / col).
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    simp
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) c = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col_pos)
  -- Step 3: post-allowDir state s_ad and its inFlow witness for checkBlockFlowIndent.
  let s_ad : ScannerStateIx input := if (saveSimpleKeyIx s).allowDirectives then
    { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKeyIx s
  have hs_ad : s_ad = if (saveSimpleKeyIx s).allowDirectives then
      { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
    else saveSimpleKeyIx s := rfl
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad c = .ok () :=
    checkBlockFlowIndent_ok_flow _ _ (h_ad_flow ▸ h_flow)
  -- Fix B: pending-directives check passes (dp = false is forced by h_snt's success).
  have h_ndp_ok : scanNextTokenIx_checkNoPendingDirectives (saveSimpleKeyIx s) = .ok () :=
    scanNextTokenIx_checkNoPendingDirectives_ok _
      (scanNextTokenIx_ok_directivesPresent_false h_pp h_struct h_snt)
  -- Step 4: unfold scanNextTokenIx using the pinned dispatch info.
  unfold scanNextTokenIx at h_snt
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind, h_pp, h_struct,
             h_ndp_ok, ← hs_ad, h_check] at h_snt
  -- Step 5: case-analyze on dispatchFlowIndicators result.
  match h_flow_eq : scanNextTokenIx_dispatchFlowIndicators s_ad c with
  | .error _ => rw [h_flow_eq] at h_snt; simp at h_snt
  | .ok (some s_flow) =>
    rw [h_flow_eq] at h_snt; simp only at h_snt
    injection h_snt with h_eq; injection h_eq with h_eq; subst h_eq
    have h_grew := scanNextTokenIx_via_flow_dispatch_filtered_grows
      s _ s_ad s_flow c h_pp h_struct hs_ad h_check h_flow_eq
    omega
  | .ok none =>
    rw [h_flow_eq] at h_snt; simp only at h_snt
    -- Now case-analyze on dispatchBlockIndicators result.
    match h_block_eq : scanNextTokenIx_dispatchBlockIndicators s_ad c with
    | .error _ => rw [h_block_eq] at h_snt; simp at h_snt
    | .ok (some s_block) =>
      rw [h_block_eq] at h_snt; simp only at h_snt
      injection h_snt with h_eq; injection h_eq with h_eq; subst h_eq
      have h_grew := scanNextTokenIx_via_block_dispatch_filtered_grows
        s _ s_ad s_block c h_pp h_struct hs_ad h_check h_flow_eq h_block_eq
      omega
    | .ok none =>
      rw [h_block_eq] at h_snt; simp only at h_snt
      -- Final dispatch: content.
      match h_cont_eq : scanNextTokenIx_dispatchContent s_ad c with
      | .error _ => rw [h_cont_eq] at h_snt; simp at h_snt
      | .ok s_cont =>
        rw [h_cont_eq] at h_snt; simp only at h_snt
        injection h_snt with h_eq; injection h_eq with h_eq; subst h_eq
        have h_grew := scanNextTokenIx_via_content_dispatch_filtered_grows
          s _ s_ad s_cont c h_pp h_struct hs_ad h_check h_flow_eq h_block_eq h_cont_eq
        omega

end L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth
