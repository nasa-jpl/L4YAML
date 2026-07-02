/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.EmitterScannability.ScanSteps

/-!
# Emitter Scannability — Filtered Token Growth Infrastructure

Foundation module extracted 2026-05-31 from `EmitterScannability.lean`. Imports the
previous foundation layer `ScanSteps`; the base imports this transitively.
Namespace reopened; contiguous prefix slice ⇒ no forward references.

Contents: first-filtered-token lemmas for flow-content scanners, the general
filtered token array growth infrastructure, and per-dispatch-layer growth lemmas.
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

/-! ### First-filtered-token lemmas for flow-content scanners (Tier 2 Turn 1)

When `scanNextToken` runs in flow context with a leading content character
(`"`, `[`, or `{`), the *first* new filtered (non-placeholder) token is
fully determined by that leading character.  These three lemmas pin down
that fact and serve as building blocks for body-token characterization in
`emitList_body_filtered_characterization` and
`emitPairList_body_filtered_characterization`. -/

/-- After `scanNextToken` with leading `[` in flow context, the first new
    filtered token is `.flowSequenceStart`. -/
theorem scanFlowSequenceStart_first_filtered_token (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    (s.tokens.filter (fun t => t.val != .placeholder)).size <
      (s'.tokens.filter (fun t => t.val != .placeholder)).size ∧
    (∀ (h : (s.tokens.filter (fun t => t.val != .placeholder)).size <
            (s'.tokens.filter (fun t => t.val != .placeholder)).size),
      ((s'.tokens.filter (fun t => t.val != .placeholder))[
        (s.tokens.filter (fun t => t.val != .placeholder)).size]'h).val
        = .flowSequenceStart) := by
  -- Re-derive dispatch to identify s'
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '[')) :=
    scanNextToken_preprocess_flow s '[' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '[' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '[' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_bracket s_ad
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowSequenceStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowSequenceStart s_ad := by
    have h := h_snt.symm.trans h_snt_eq
    exact Option.some.inj (Except.ok.inj h)
  -- Tokens shape: scanFlowSequenceStart s_ad pushes one .flowSequenceStart token
  have h_fss_tokens : (scanFlowSequenceStart s_ad).tokens
      = s_ad.tokens.push ⟨s_ad.currentPos, .flowSequenceStart, s_ad.currentPos⟩ := by
    show ({ ({ s_ad with simpleKey := _ }.emit .flowSequenceStart).advance with
        flowLevel := _, simpleKeyAllowed := _,
        flowStack := _, simpleKeyStack := _ }).tokens = _
    simp only [ScannerCorrectness.advance_preserves_tokens,
               ScannerState.emit, ScannerState.currentPos]
  have h_ad_tokens_filter :
      s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    have h_pp_filt := saveSimpleKey_filter_placeholder s
    simp only [s_ad]; split <;> exact h_pp_filt
  rw [h_s', h_fss_tokens, Array.filter_push]
  simp only [show ((⟨s_ad.currentPos, .flowSequenceStart, s_ad.currentPos⟩ : Positioned YamlToken).val
                   != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_tokens_filter]
  refine ⟨?_, ?_⟩
  · rw [Array.size_push]; omega
  · intro _; rw [Array.getElem_push_eq]

/-- After `scanNextToken` with leading `{` in flow context, the first new
    filtered token is `.flowMappingStart`. -/
theorem scanFlowMappingStart_first_filtered_token (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    (s.tokens.filter (fun t => t.val != .placeholder)).size <
      (s'.tokens.filter (fun t => t.val != .placeholder)).size ∧
    (∀ (h : (s.tokens.filter (fun t => t.val != .placeholder)).size <
            (s'.tokens.filter (fun t => t.val != .placeholder)).size),
      ((s'.tokens.filter (fun t => t.val != .placeholder))[
        (s.tokens.filter (fun t => t.val != .placeholder)).size]'h).val
        = .flowMappingStart) := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '{')) :=
    scanNextToken_preprocess_flow s '{' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '{' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_brace s_ad
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowMappingStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowMappingStart s_ad := by
    have h := h_snt.symm.trans h_snt_eq
    exact Option.some.inj (Except.ok.inj h)
  have h_fms_tokens : (scanFlowMappingStart s_ad).tokens
      = s_ad.tokens.push ⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩ := by
    show ({ ({ s_ad with simpleKey := _ }.emit .flowMappingStart).advance with
        flowLevel := _, simpleKeyAllowed := _,
        flowStack := _, simpleKeyStack := _ }).tokens = _
    simp only [ScannerCorrectness.advance_preserves_tokens,
               ScannerState.emit, ScannerState.currentPos]
  have h_ad_tokens_filter :
      s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    have h_pp_filt := saveSimpleKey_filter_placeholder s
    simp only [s_ad]; split <;> exact h_pp_filt
  rw [h_s', h_fms_tokens, Array.filter_push]
  simp only [show ((⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩ : Positioned YamlToken).val
                   != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_tokens_filter]
  refine ⟨?_, ?_⟩
  · rw [Array.size_push]; omega
  · intro _; rw [Array.getElem_push_eq]

/-- Extract from a successful `scanDoubleQuoted` call: the result's tokens
    are exactly the input's tokens with one `.scalar _ .doubleQuoted` pushed.
    Used by `scanDoubleQuoted_first_filtered_token` to identify the new
    token without knowing the specific content string. -/
theorem scanDoubleQuoted_tokens_push {s s' : ScannerState}
    (h : scanDoubleQuoted s = .ok s') :
    ∃ c, s'.tokens
      = s.tokens.push ⟨s.currentPos, .scalar c .doubleQuoted, s.currentPos⟩ := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i ev_result heq_loop
  obtain ⟨content, s_after_close⟩ := ev_result
  refine ⟨content, ?_⟩
  have h_collect := ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
    s.advance "" _ _ _ _ _ _ heq_loop
  have h_adv := ScannerCorrectness.advance_preserves_tokens s
  split at h
  · -- !inFlow case: validateTrailingContent check
    split at h <;> try contradiction
    injection h with h_eq; subst h_eq; dsimp only []
    show (s_after_close.emitAt s.currentPos (.scalar content .doubleQuoted)).tokens = _
    unfold ScannerState.emitAt; simp only [Array.push]
    rw [h_collect, h_adv]
  · -- inFlow case: no validation
    injection h with h_eq; subst h_eq; dsimp only []
    show (s_after_close.emitAt s.currentPos (.scalar content .doubleQuoted)).tokens = _
    unfold ScannerState.emitAt; simp only [Array.push]
    rw [h_collect, h_adv]

/-- **Double-quoted scalar push, content pinned (§5.12).** When the scanner input is
    `'"' :: escapeString content ++ '"' :: rest` in flow context, `scanDoubleQuoted`
    produces a token push of exactly `.scalar content .doubleQuoted`.
    Strengthens `scanDoubleQuoted_tokens_push` (which gives only `∃ c`). -/
theorem scanDoubleQuoted_tokens_push_content {s s' : ScannerState}
    (content : String) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h : scanDoubleQuoted s = .ok s') :
    s'.tokens = s.tokens.push ⟨s.currentPos, .scalar content .doubleQuoted, s.currentPos⟩ := by
  have h_last : lastRealTokenVal? s'.tokens = some (.scalar content .doubleQuoted) := by
    obtain ⟨s_ok, h_dq_ok, _, _, _, _, _, _, h_last_ok, _, _⟩ :=
      scanDoubleQuoted_flow_ok s content rest hcorr h_flow
    rwa [Except.ok.inj (h_dq_ok.symm.trans h)] at h_last_ok
  obtain ⟨c, h_tok⟩ := scanDoubleQuoted_tokens_push h
  have h_c_eq : c = content := by
    have h_last_c : lastRealTokenVal? s'.tokens = some (.scalar c .doubleQuoted) := by
      rw [h_tok]
      exact lastRealTokenVal_push_non_ph' s.tokens
        ⟨s.currentPos, .scalar c .doubleQuoted, s.currentPos⟩
        (fun h_abs => YamlToken.noConfusion h_abs)
    exact (YamlToken.scalar.inj (Option.some.inj (h_last_c.symm.trans h_last))).1
  rw [h_tok, h_c_eq]

/-- After `scanNextToken` with leading `"` in flow context, the first new
    filtered token is some `.scalar` token (the doubleQuoted scalar emitted
    by `scanDoubleQuoted`).  Content and subType are existentially
    quantified — the lemma's purpose is dispatch identification. -/
theorem scanDoubleQuoted_first_filtered_token (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'"' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    (s.tokens.filter (fun t => t.val != .placeholder)).size <
      (s'.tokens.filter (fun t => t.val != .placeholder)).size ∧
    (∀ (h : (s.tokens.filter (fun t => t.val != .placeholder)).size <
            (s'.tokens.filter (fun t => t.val != .placeholder)).size),
      ∃ c sc, ((s'.tokens.filter (fun t => t.val != .placeholder))[
        (s.tokens.filter (fun t => t.val != .placeholder)).size]'h).val
        = .scalar c sc) := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
    scanNextToken_preprocess_flow s '"' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_flow_true : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '"' h_ad_flow_true
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  -- From h_snt + dispatch composition, dispatchContent must succeed and yield s'
  have h_dc : scanNextToken_dispatchContent s_ad '"' = Except.ok s' := by
    cases h_dc_eq : scanNextToken_dispatchContent s_ad '"' with
    | error e =>
      exfalso
      have h_snt_err := scanNextToken_via_content_dispatch_error
        _ _ _ _ _ h_pp h_struct rfl h_check h_flow_none h_block_none h_dc_eq
      rw [h_snt_err] at h_snt; exact absurd h_snt (by simp)
    | ok s_dc =>
      have h_snt_eq : scanNextToken s = Except.ok (some s_dc) :=
        scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl h_check
          h_flow_none h_block_none h_dc_eq
      have h_eq2 : s' = s_dc := Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
      subst h_eq2; rfl
  -- Extract scanDoubleQuoted's effect from dispatchContent
  -- For c = '"', dispatchContent: scanDoubleQuoted s_ad ; (optional simpleKey update)
  have h_tokens_push : ∃ c, s'.tokens
      = s_ad.tokens.push ⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩ := by
    -- Reduce h_dc to extract the scanDoubleQuoted result
    cases h_dq_eq : scanDoubleQuoted s_ad with
    | error e =>
      exfalso
      have h_dc_err : scanNextToken_dispatchContent s_ad '"' = Except.error e := by
        unfold scanNextToken_dispatchContent
        simp [bind, Except.bind, pure, Except.pure, h_dq_eq]
      rw [h_dc_err] at h_dc; exact absurd h_dc (by simp)
    | ok s_dq =>
      obtain ⟨c, h_tok⟩ := scanDoubleQuoted_tokens_push h_dq_eq
      refine ⟨c, ?_⟩
      have h_s'_tokens : s'.tokens = s_dq.tokens := by
        unfold scanNextToken_dispatchContent at h_dc
        simp [bind, Except.bind, pure, Except.pure, h_dq_eq] at h_dc
        split at h_dc
        · rw [← h_dc]
        · rw [← h_dc]
      rw [h_s'_tokens, h_tok]
  obtain ⟨c, h_s'_tokens⟩ := h_tokens_push
  -- Now apply filter_push
  have h_ad_tokens_filter :
      s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    have h_pp_filt := saveSimpleKey_filter_placeholder s
    simp only [s_ad]; split <;> exact h_pp_filt
  rw [h_s'_tokens, Array.filter_push]
  simp only [show ((⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩ : Positioned YamlToken).val
                   != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_tokens_filter]
  refine ⟨?_, ?_⟩
  · rw [Array.size_push]; omega
  · intro _; refine ⟨c, .doubleQuoted, ?_⟩; exact congrArg _ Array.getElem_push_eq

/-- Evaluate `saveSimpleKey` on the save branch: when a simple key is allowed
    and the line is not an explicit-key line, `saveSimpleKey` reserves two
    placeholder slots (`tokens.size` grows by 2) and records a pending key
    whose `tokenIndex` is the pre-save `tokens.size`. -/
theorem saveSimpleKey_eval (s : ScannerState)
    (h_ek : s.explicitKeyLine = none) (h_ska : s.simpleKeyAllowed = true) :
    (saveSimpleKey s).simpleKey.possible = true ∧
    (saveSimpleKey s).simpleKey.tokenIndex = s.tokens.size ∧
    (saveSimpleKey s).simpleKeyStack = s.simpleKeyStack ∧
    (saveSimpleKey s).tokens.size = s.tokens.size + 2 := by
  unfold saveSimpleKey
  split
  · rename_i h1; rw [h_ek] at h1; simp at h1
  · exact ⟨rfl, rfl, rfl, by simp [Array.size_push]⟩

/-- Both no-overwrite invariants needed at the residual-chain start follow from
    a uniform characterization of the post-head-step saved keys: the current key
    (if any) and every newly-pushed stack key point at `N` (the head item's
    reserved slot), while pre-existing stack keys reside strictly below `N - 1`
    (their `tokenIndex + 1 < N`, from `SimpleKeyStackValid`). -/
theorem noOverwrite_of_keys_at_or_below (s' : ScannerState) (N : Nat)
    (hP1 : s'.simpleKey.possible = true → s'.simpleKey.tokenIndex = N)
    (hP2 : ∀ (j : Nat) (h : j < s'.simpleKeyStack.size),
        s'.simpleKeyStack[j].possible = true →
        s'.simpleKeyStack[j].tokenIndex = N ∨ s'.simpleKeyStack[j].tokenIndex + 1 < N) :
    NoOverwriteAt s' (N + 2) ∧ FlowNoOverwriteAt s' N := by
  refine ⟨⟨fun hp => ?_, fun j hj hp => ?_⟩, ⟨fun hp => ?_, fun j hj hp => ?_⟩⟩
  · have := hP1 hp; omega
  · rcases hP2 j hj hp with h | h <;> omega
  · have := hP1 hp; omega
  · rcases hP2 j hj hp with h | h <;> omega

/-- The first `scanNextToken` step over an emitList head item (leading char
    `[`/`{`/`"` in flow) reserves the two placeholder slots at raw positions
    `N`, `N+1` (`N = s.tokens.size`) and lands the head content token at `N+2`,
    so `s'.tokens.size = N + 3`.  Every possible saved key in the resulting
    state points at `N` (the head key — kept as the current key for a scalar,
    pushed onto the stack for a sequence/mapping open) or, for pre-existing
    stack keys, strictly below `N - 1` (by `SimpleKeyStackValid`).  Packaged as
    the two no-overwrite invariants consumed by substrate.d (`N+2`) and
    substrate.e (`N`) at the residual-chain start. -/
theorem emitList_head_step_noOverwrite (s s' : ScannerState) (c : Char) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨c :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none) (h_ska : s.simpleKeyAllowed = true)
    (h_ssv : ScannerCorrectness.SimpleKeyStackValid s)
    (h_c : c = '[' ∨ c = '{' ∨ c = '"')
    (h_snt : scanNextToken s = .ok (some s')) :
    s'.tokens.size = s.tokens.size + 3 ∧
    NoOverwriteAt s' (s.tokens.size + 2) ∧
    FlowNoOverwriteAt s' (s.tokens.size) := by
  obtain ⟨h_skp, h_skt, h_sks, h_skz⟩ := saveSimpleKey_eval s h_ek h_ska
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
    else saveSimpleKey s
  have h_ad_sk : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by
    simp only [s_ad]; split <;> rfl
  have h_ad_stack : s_ad.simpleKeyStack = (saveSimpleKey s).simpleKeyStack := by
    simp only [s_ad]; split <;> rfl
  have h_ad_tokens : s_ad.tokens = (saveSimpleKey s).tokens := by
    simp only [s_ad]; split <;> rfl
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
  rcases h_c with rfl | rfl | rfl
  · -- '[' : s' = scanFlowSequenceStart s_ad
    have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '[')) :=
      scanNextToken_preprocess_flow s '[' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
    have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '[' = .ok none :=
      dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
    have h_check := checkBlockFlowIndent_ok_flow s_ad '[' (h_ad_flow ▸ h_flow)
    have h_flow_disp := dispatchFlowIndicators_bracket s_ad
    have h_snt_eq : scanNextToken s = .ok (some (scanFlowSequenceStart s_ad)) :=
      scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
    have h_s' : s' = scanFlowSequenceStart s_ad :=
      Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
    have h_stack_eq : s'.simpleKeyStack = s.simpleKeyStack.push (saveSimpleKey s).simpleKey := by
      rw [h_s', ScannerCorrectness.scanFlowSequenceStart_stack_pushed, h_ad_stack, h_ad_sk, h_sks]
    refine ⟨?_, noOverwrite_of_keys_at_or_below s' s.tokens.size ?_ ?_⟩
    · rw [h_s', ScannerCorrectness.scanFlowSequenceStart_adds_one_token, h_ad_tokens, h_skz]
    · intro hp
      rw [h_s', ScannerCorrectness.scanFlowSequenceStart_simpleKey_cleared] at hp
      exact absurd hp (by decide)
    · intro j hj hp
      simp only [h_stack_eq, Array.size_push] at hj
      simp only [h_stack_eq] at hp ⊢
      rcases Nat.lt_or_ge j s.simpleKeyStack.size with hlt | hge
      · simp only [Array.getElem_push_lt hlt] at hp ⊢
        right; exact (h_ssv j hlt hp).2.1
      · obtain rfl : j = s.simpleKeyStack.size := by omega
        simp only [Array.getElem_push_eq] at hp ⊢
        left; exact h_skt
  · -- '{' : s' = scanFlowMappingStart s_ad
    have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '{')) :=
      scanNextToken_preprocess_flow s '{' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
    have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '{' = .ok none :=
      dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
    have h_check := checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
    have h_flow_disp := dispatchFlowIndicators_brace s_ad
    have h_snt_eq : scanNextToken s = .ok (some (scanFlowMappingStart s_ad)) :=
      scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
    have h_s' : s' = scanFlowMappingStart s_ad :=
      Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
    have h_stack_eq : s'.simpleKeyStack = s.simpleKeyStack.push (saveSimpleKey s).simpleKey := by
      rw [h_s', ScannerCorrectness.scanFlowMappingStart_stack_pushed, h_ad_stack, h_ad_sk, h_sks]
    refine ⟨?_, noOverwrite_of_keys_at_or_below s' s.tokens.size ?_ ?_⟩
    · rw [h_s', ScannerCorrectness.scanFlowMappingStart_adds_one_token, h_ad_tokens, h_skz]
    · intro hp
      rw [h_s', ScannerCorrectness.scanFlowMappingStart_simpleKey_cleared] at hp
      exact absurd hp (by decide)
    · intro j hj hp
      simp only [h_stack_eq, Array.size_push] at hj
      simp only [h_stack_eq] at hp ⊢
      rcases Nat.lt_or_ge j s.simpleKeyStack.size with hlt | hge
      · simp only [Array.getElem_push_lt hlt] at hp ⊢
        right; exact (h_ssv j hlt hp).2.1
      · obtain rfl : j = s.simpleKeyStack.size := by omega
        simp only [Array.getElem_push_eq] at hp ⊢
        left; exact h_skt
  · -- '"' : s' from dispatchContent (scanDoubleQuoted + endLine tweak)
    have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
      scanNextToken_preprocess_flow s '"' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
    have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
      dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
    have h_ad_flow_true : s_ad.inFlow = true := h_ad_flow ▸ h_flow
    have h_check := checkBlockFlowIndent_ok_flow s_ad '"' h_ad_flow_true
    have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
      dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
      dispatchBlockIndicators_none_quote _
    -- identify s' = dispatchContent output
    have h_dc : scanNextToken_dispatchContent s_ad '"' = Except.ok s' := by
      cases h_dc_eq : scanNextToken_dispatchContent s_ad '"' with
      | error e =>
        exfalso
        have h_snt_err := scanNextToken_via_content_dispatch_error
          _ _ _ _ _ h_pp h_struct rfl h_check h_flow_none h_block_none h_dc_eq
        rw [h_snt_err] at h_snt; exact absurd h_snt (by simp)
      | ok s_dc =>
        have h_snt_eq : scanNextToken s = Except.ok (some s_dc) :=
          scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl h_check
            h_flow_none h_block_none h_dc_eq
        have h_eq2 : s' = s_dc := Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
        subst h_eq2; rfl
    -- extract scanDoubleQuoted result and relate s' to it
    cases h_dq_eq : scanDoubleQuoted s_ad with
    | error e =>
      exfalso
      have h_dc_err : scanNextToken_dispatchContent s_ad '"' = Except.error e := by
        unfold scanNextToken_dispatchContent
        simp [bind, Except.bind, pure, Except.pure, h_dq_eq]
      rw [h_dc_err] at h_dc; exact absurd h_dc (by simp)
    | ok s_dq =>
      have h_sdq_sk : s_dq.simpleKey = s_ad.simpleKey :=
        ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s_ad s_dq h_dq_eq
      have h_sdq_stack : s_dq.simpleKeyStack = s_ad.simpleKeyStack :=
        ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s_ad s_dq h_dq_eq
      have h_sdq_poss : s_dq.simpleKey.possible = true := by rw [h_sdq_sk, h_ad_sk]; exact h_skp
      obtain ⟨ct, h_dq_tok⟩ := scanDoubleQuoted_tokens_push h_dq_eq
      -- dispatchContent for '"' applies the endLine tweak (simpleKey.possible = true)
      have h_dc2 := h_dc
      unfold scanNextToken_dispatchContent at h_dc2
      simp [bind, Except.bind, pure, Except.pure, h_dq_eq, h_sdq_poss] at h_dc2
      have h_s'_eq := h_dc2.symm
      refine ⟨?_, noOverwrite_of_keys_at_or_below s' s.tokens.size ?_ ?_⟩
      · -- size = N+3
        rw [h_s'_eq]
        show s_dq.tokens.size = s.tokens.size + 3
        rw [h_dq_tok, Array.size_push, h_ad_tokens, h_skz]
      · -- current key: possible → tokenIndex = N
        intro _
        rw [h_s'_eq]
        show s_dq.simpleKey.tokenIndex = s.tokens.size
        rw [h_sdq_sk, h_ad_sk]; exact h_skt
      · -- stack: old entries below N-1
        intro j hj hp
        have h_s'_stack : s'.simpleKeyStack = s.simpleKeyStack := by
          rw [h_s'_eq]; show s_dq.simpleKeyStack = s.simpleKeyStack
          rw [h_sdq_stack, h_ad_stack, h_sks]
        simp only [h_s'_stack] at hj hp ⊢
        right; exact (h_ssv j hj hp).2.1

-- The first char of `emit v` is always a non-whitespace content char.
-- Used for space-handling in comma-separated lists.
theorem emit_first_char (v : YamlValue) :
    ∃ c rest', (emit v).toList = c :: rest' ∧
      isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ c ≠ '#' := by
  cases v with
  | scalar s =>
    refine ⟨'"', (escapeString s.content).toList ++ ['"'], ?_, by decide, by decide, by decide⟩
    simp only [emit, emitScalar, String.toList_append]; rfl
  | sequence _ items _ _ =>
    refine ⟨'[', (emit.emitList items.toList).toList ++ [']'], ?_, by decide, by decide, by decide⟩
    simp only [emit, String.toList_append]; rfl
  | mapping _ pairs _ _ =>
    refine ⟨'{', (emit.emitPairList pairs.toList).toList ++ ['}'], ?_, by decide, by decide, by decide⟩
    simp only [emit, String.toList_append]; rfl
  | «alias» name =>
    refine ⟨'"', (escapeString ("*" ++ name)).toList ++ ['"'], ?_, by decide, by decide, by decide⟩
    simp only [emit, emitScalar, String.toList_append]; rfl

-- The first char of `emitList (v :: vs)` is the first char of `emit v`.
theorem emitList_first_char (v : YamlValue) (vs : List YamlValue) :
    ∃ c rest', (emit.emitList (v :: vs)).toList = c :: rest' ∧
      isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ c ≠ '#' := by
  obtain ⟨c, ev_rest, h_emit_eq, h_nws, h_nlb, h_nc⟩ := emit_first_char v
  match vs with
  | [] =>
    simp only [emit.emitList]
    exact ⟨c, ev_rest, h_emit_eq, h_nws, h_nlb, h_nc⟩
  | v' :: vs' =>
    have h_el : (emit.emitList (v :: v' :: vs')).toList =
        (emit v).toList ++ (", " ++ emit.emitList (v' :: vs')).toList := by
      simp [emit.emitList, String.toList_append, List.append_assoc]
    rw [h_el, h_emit_eq]
    exact ⟨c, ev_rest ++ (", " ++ emit.emitList (v' :: vs')).toList,
      by simp, h_nws, h_nlb, h_nc⟩

-- The first char of `emit v` is one of the flow content-start indicators
-- `[` / `{` / `"`.  Refines `emit_first_char`'s "non-whitespace" conclusion
-- to the exact dispatch-relevant characters.
theorem emit_first_char_bracket (v : YamlValue) :
    ∃ c rest', (emit v).toList = c :: rest' ∧ (c = '[' ∨ c = '{' ∨ c = '"') := by
  cases v with
  | scalar s =>
    refine ⟨'"', (escapeString s.content).toList ++ ['"'], ?_, Or.inr (Or.inr rfl)⟩
    simp only [emit, emitScalar, String.toList_append]; rfl
  | sequence _ items _ _ =>
    refine ⟨'[', (emit.emitList items.toList).toList ++ [']'], ?_, Or.inl rfl⟩
    simp only [emit, String.toList_append]; rfl
  | mapping _ pairs _ _ =>
    refine ⟨'{', (emit.emitPairList pairs.toList).toList ++ ['}'], ?_, Or.inr (Or.inl rfl)⟩
    simp only [emit, String.toList_append]; rfl
  | «alias» name =>
    refine ⟨'"', (escapeString ("*" ++ name)).toList ++ ['"'], ?_, Or.inr (Or.inr rfl)⟩
    simp only [emit, emitScalar, String.toList_append]; rfl

-- The first char of `emitList (v :: vs)` is one of `[` / `{` / `"`.
theorem emitList_first_char_bracket (v : YamlValue) (vs : List YamlValue) :
    ∃ c rest', (emit.emitList (v :: vs)).toList = c :: rest' ∧ (c = '[' ∨ c = '{' ∨ c = '"') := by
  obtain ⟨c, ev_rest, h_emit_eq, h_c⟩ := emit_first_char_bracket v
  match vs with
  | [] =>
    simp only [emit.emitList]
    exact ⟨c, ev_rest, h_emit_eq, h_c⟩
  | v' :: vs' =>
    have h_el : (emit.emitList (v :: v' :: vs')).toList =
        (emit v).toList ++ (", " ++ emit.emitList (v' :: vs')).toList := by
      simp [emit.emitList, String.toList_append, List.append_assoc]
    rw [h_el, h_emit_eq]
    exact ⟨c, ev_rest ++ (", " ++ emit.emitList (v' :: vs')).toList, by simp, h_c⟩

-- `emitList` is non-empty on non-empty input: its toList is non-nil.
theorem emitList_toList_ne_nil (v : YamlValue) (vs : List YamlValue) :
    (emit.emitList (v :: vs)).toList ≠ [] := by
  obtain ⟨c, rest', h_eq, _, _, _⟩ := emitList_first_char v vs
  rw [h_eq]; exact List.cons_ne_nil _ _

/-- After `emit streamEnd`, the pushed token is the last element of the array.
    Gives: `(s.emit tok).tokens = s.tokens.push ⟨s.currentPos, tok⟩`.
    Forward-declared from its later siblings to support the filtered-growth
    infrastructure that follows. -/
theorem emit_tokens_push (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).tokens = s.tokens.push { pos := s.currentPos, val := tok } := by
  unfold ScannerState.emit; rfl

/-- If `b` extends `a` (same elements at all positions `i < a.size`), then
    `b.filter p` has `a.filter p` as a prefix. -/
theorem Array_filter_prefix_of_raw_prefix {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : a.size ≤ b.size)
    (h_eq : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i]) :
    ∃ suffix, (b.filter p).toList = (a.filter p).toList ++ suffix := by
  have h_take : b.toList.take a.size = a.toList := by
    apply List.ext_getElem
    · simp only [List.length_take, Array.length_toList, Nat.min_eq_left h_sz]
    · intro n hn₁ hn₂
      simp only [List.getElem_take]
      rw [Array.getElem_toList, Array.getElem_toList]
      exact h_eq n (by simpa [Array.length_toList] using hn₂)
  have h_split : b.toList = a.toList ++ b.toList.drop a.size := by
    rw [← h_take, List.take_append_drop]
  rw [Array.toList_filter, Array.toList_filter, h_split, List.filter_append]
  exact ⟨(b.toList.drop a.size).filter p, rfl⟩

/-- Pointwise corollary of `Array_filter_prefix_of_raw_prefix`: at any filtered
    index below `(a.filter p).size`, `b.filter p` agrees with `a.filter p`. -/
theorem Array_filter_getElem_of_raw_prefix {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : a.size ≤ b.size)
    (h_eq : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i])
    (k : Nat) (hk : k < (a.filter p).size)
    (hk' : k < (b.filter p).size) :
    (b.filter p)[k]'hk' = (a.filter p)[k]'hk := by
  obtain ⟨suffix, h_suffix⟩ := Array_filter_prefix_of_raw_prefix a b p h_sz h_eq
  have h_lk : k < (a.filter p).toList.length := by rwa [Array.length_toList]
  have h_lk' : k < (b.filter p).toList.length := by rwa [Array.length_toList]
  have hopt : (b.filter p).toList[k]? = (a.filter p).toList[k]? := by
    rw [h_suffix, List.getElem?_append_left h_lk]
  rw [List.getElem?_eq_getElem h_lk', List.getElem?_eq_getElem h_lk] at hopt
  exact Option.some.inj hopt

/-! ### Filtered token array growth infrastructure

   Every `scanNextToken` step adds at least one non-placeholder token.
   The proof decomposes into:
   1. Preprocessing (skipToContent, unwindIndents, saveSimpleKey) preserves
      or grows filtered count — from existing `preprocess_preserves_prefix`.
   2. Each dispatch branch emits at least one non-placeholder token.
   3. `setIfInBounds` with non-placeholder replacement doesn't decrease
      filtered count (only used in `scanValuePrepare`).
-/

-- List helper: replacing an element that passes a filter doesn't decrease filter count.
theorem List_filter_set_length_mono {α : Type} (l : List α) (i : Nat) (v : α)
    (p : α → Bool) (hv : p v = true) :
    ((l.set i v).filter p).length ≥ (l.filter p).length := by
  induction l generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.filter_cons, hv, ite_true]
      split <;> simp <;> omega
    | succ j =>
      simp only [List.set_cons_succ, List.filter_cons]
      have := ih j
      split <;> simp <;> omega

-- Array.setIfInBounds with a filter-passing replacement preserves or grows
-- the filtered array size.
theorem Array_setIfInBounds_filter_mono {α : Type} (a : Array α) (i : Nat) (v : α)
    (p : α → Bool) (hv : p v = true) :
    ((a.setIfInBounds i v).filter p).size ≥ (a.filter p).size := by
  unfold Array.setIfInBounds
  split
  · -- i < a.size: use List_filter_set_length_mono
    next h_bound =>
    have : ((a.set i v h_bound).filter p).toList.length ≥ (a.filter p).toList.length := by
      rw [Array.toList_filter, Array.toList_filter, Array.toList_set]
      exact List_filter_set_length_mono a.toList i v p hv
    exact this
  · -- i ≥ a.size: identity
    omega

/-- **Filtered-set, dropping a filtered-out slot.** When `l[i]` fails the filter
    `p`, dropping it (splitting around index `i`) leaves `l.filter p` intact.  The
    list-level fact behind "a placeholder slot is invisible to the filtered view". -/
theorem List_filter_eq_of_not_pass {α : Type} (l : List α) (i : Nat) (p : α → Bool)
    (hi : i < l.length) (h_old : p (l[i]'hi) = false) :
    l.filter p = (l.take i).filter p ++ (l.drop (i + 1)).filter p := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero =>
      have h_a : p a = false := h_old
      simp [h_a]
    | succ j =>
      have hj : j < as.length := by simpa using hi
      have h_old' : p (as[j]'hj) = false := by
        have : (a :: as)[j + 1]'hi = as[j]'hj := List.getElem_cons_succ ..
        rwa [this] at h_old
      simp only [List.take_succ_cons, List.drop_succ_cons, List.filter_cons]
      rw [ih j hj h_old']
      split <;> simp [List.cons_append]

/-- **Filtered-set, inserting at a filtered-out slot.** Setting `l[i]` (which fails
    `p`) to a `p`-passing token `v` inserts `v` into `l.filter p` exactly at the rank
    position `((l.take i).filter p).length`.  This is the list-level characterization
    of the colon's retroactive placeholder→`.key` write: it converts an invisible
    slot into a visible `.key`, inserting it at its filtered rank — the general form
    of the special "first new filtered token is `.key`" fact `keyshape_first_token_key`
    proves, lifted to the *entire* filtered block (toward sorries 9646/9552). -/
theorem List_filter_set_of_not_pass {α : Type} (l : List α) (i : Nat) (v : α)
    (p : α → Bool) (hi : i < l.length) (h_old : p (l[i]'hi) = false) (h_new : p v = true) :
    (l.set i v).filter p = (l.take i).filter p ++ v :: (l.drop (i + 1)).filter p := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero =>
      simp [h_new]
    | succ j =>
      have hj : j < as.length := by simpa using hi
      have h_old' : p (as[j]'hj) = false := by
        have : (a :: as)[j + 1]'hi = as[j]'hj := List.getElem_cons_succ ..
        rwa [this] at h_old
      simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.filter_cons]
      rw [ih j hj h_old']
      split <;> simp [List.cons_append]

/-- Array bridge: `setIfInBounds` at a filtered-out slot inserts the new (filtered-in)
    token at its rank in the filtered `toList` — the form the colon producer applies
    (`s₂.tokens = (s₁.tokens.setIfInBounds (N+1) keyTok).push valueTok`). -/
theorem Array_filter_setIfInBounds_of_not_pass {α : Type} (a : Array α) (i : Nat) (v : α)
    (p : α → Bool) (hi : i < a.size) (h_old : p (a[i]'hi) = false) (h_new : p v = true) :
    ((a.setIfInBounds i v).filter p).toList =
      (a.toList.take i).filter p ++ v :: (a.toList.drop (i + 1)).filter p := by
  have hi' : i < a.toList.length := by simpa [Array.length_toList] using hi
  have h_old' : p (a.toList[i]'hi') = false := by
    rw [Array.getElem_toList]; exact h_old
  rw [Array.setIfInBounds, dif_pos hi, Array.toList_filter, Array.toList_set]
  exact List_filter_set_of_not_pass a.toList i v p hi' h_old' h_new

/-- **Colon block-suffix identity.** If the filtered prefix `(l.take k).filter p`
    equals `baseFilt` and the whole filtered list is `baseFilt ++ block_k`, and slot
    `k` is filtered out, then the filtered suffix *after* the filtered-out slot equals
    exactly `block_k`.  This is the algebraic core the mapping-body producer uses to
    re-anchor `scanNextToken_flow_value_block`'s mid-key insertion to the pair start:
    the colon writes `.key` at the rank of slot `N+1` (a placeholder), and this lemma
    pins the *content after* that slot to the key block `block_k`, so the colon delta
    becomes a clean front-insert `.key :: block_k` relative to the pair-start prefix
    (toward sorries 9646/9552). -/
theorem List_filter_drop_succ_of_take {α : Type} (l : List α) (k : Nat) (p : α → Bool)
    (hk : k < l.length) (h_old : p (l[k]'hk) = false)
    (baseFilt block_k : List α)
    (h_take : (l.take k).filter p = baseFilt)
    (h_full : l.filter p = baseFilt ++ block_k) :
    (l.drop (k + 1)).filter p = block_k := by
  have h_split := List_filter_eq_of_not_pass l k p hk h_old
  rw [h_take, h_full] at h_split
  exact (List.append_cancel_left h_split).symm

-- Preprocessing monotonicity: the filtered token count doesn't decrease
-- through `scanNextToken_preprocess`.
theorem preprocess_filtered_mono (s : ScannerState) (s₁ : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s₁, c))) :
    (s₁.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size := by
  have h_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s s₁ c h
  have h_pres := ScannerCorrectness.ScanHelpers.preprocess_preserves_prefix s s₁ c h
  obtain ⟨suffix, h_eq⟩ := Array_filter_prefix_of_raw_prefix s.tokens s₁.tokens
    (fun t => t.val != .placeholder) h_mono h_pres
  show (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.length ≥
       (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
  rw [h_eq, List.length_append]; omega

-- `allowDirectives` if-then-else preserves filtered token count (tokens unchanged).
theorem allowDir_ite_filter (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ((if s.allowDirectives = true then
        { s with allowDirectives := false, documentEverStarted := true }
      else s).tokens.filter p).size = (s.tokens.filter p).size := by
  split <;> rfl

/-! #### General filtered growth helper -/

-- If a non-empty list's first element passes filter `p`, filter has length ≥ 1.
theorem List_filter_length_ge_one {α : Type} (l : List α) (p : α → Bool)
    (h_len : l.length ≥ 1) (h_head : p (l[0]'(by omega)) = true) :
    (l.filter p).length ≥ 1 := by
  match l with
  | [] => simp at h_len
  | hd :: tl =>
    have h_hd : p hd = true := h_head
    rw [List.filter_cons_of_pos h_hd, List.length_cons]; omega

-- If array `b` extends array `a` (same elements at positions `< a.size`), has at
-- least one more element, and that element at position `a.size` passes filter `p`,
-- then `(b.filter p).size ≥ (a.filter p).size + 1`.
theorem filtered_grows_of_extended_prefix {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : b.size ≥ a.size + 1)
    (h_pres : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i])
    (h_new : p (b[a.size]'(by omega)) = true) :
    (b.filter p).size ≥ (a.filter p).size + 1 := by
  -- Convert to List level (Array.size = toList.length definitionally)
  show (b.filter p).toList.length ≥ (a.filter p).toList.length + 1
  simp only [Array.toList_filter]
  -- Goal: (b.toList.filter p).length ≥ (a.toList.filter p).length + 1
  have h_len_le : a.toList.length ≤ b.toList.length := by
    simp only [Array.length_toList]; omega
  -- Prefix equality via ext_getElem
  have h_take : b.toList.take a.toList.length = a.toList := by
    apply List.ext_getElem
    · simp only [List.length_take]; omega
    · intro n hn₁ hn₂
      simp only [List.getElem_take, Array.getElem_toList]
      exact h_pres n (by simp only [Array.length_toList] at hn₂; exact hn₂)
  -- Split b.toList = a.toList ++ drop
  have h_split_eq : b.toList = a.toList ++ b.toList.drop a.toList.length := by
    have := List.take_append_drop a.toList.length b.toList
    rw [h_take] at this; exact this.symm
  -- Rewrite filter length as sum of parts
  have h_filter_eq : (b.toList.filter p).length =
      (a.toList.filter p).length + (b.toList.drop a.toList.length |>.filter p).length := by
    have := congrArg (fun l => (l.filter p).length) h_split_eq
    simp only [List.filter_append, List.length_append] at this
    exact this
  rw [h_filter_eq]
  -- Suffices: the drop's filter has ≥ 1 element
  suffices (b.toList.drop a.toList.length |>.filter p).length ≥ 1 by omega
  -- The drop has ≥ 1 element and its first element passes p
  have h_drop_len : (b.toList.drop a.toList.length).length ≥ 1 := by
    simp only [List.length_drop, Array.length_toList]; omega
  have h_head_p : p ((b.toList.drop a.toList.length)[0]'(by omega)) = true := by
    simp only [List.getElem_drop, Nat.add_zero, Array.getElem_toList]
    exact h_new
  exact List_filter_length_ge_one _ _ h_drop_len h_head_p

-- Variant: if array `b` extends array `a`, has at least one more element, and
-- some element at position `j ≥ a.size` passes filter `p`,
-- then `(b.filter p).size ≥ (a.filter p).size + 1`.
-- Used when we know a specific NEW element (e.g. the last) is non-placeholder,
-- but don't know the exact value at the first new position `a.size`.
theorem filtered_grows_of_any_new {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : b.size ≥ a.size + 1)
    (h_pres : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i])
    (j : Nat) (hj_lo : a.size ≤ j) (hj_hi : j < b.size)
    (h_new : p (b[j]'hj_hi) = true) :
    (b.filter p).size ≥ (a.filter p).size + 1 := by
  show (b.filter p).toList.length ≥ (a.filter p).toList.length + 1
  simp only [Array.toList_filter]
  have h_len_le : a.toList.length ≤ b.toList.length := by
    simp only [Array.length_toList]; omega
  have h_take : b.toList.take a.toList.length = a.toList := by
    apply List.ext_getElem
    · simp only [List.length_take]; omega
    · intro n hn₁ hn₂
      simp only [List.getElem_take, Array.getElem_toList]
      exact h_pres n (by simp only [Array.length_toList] at hn₂; exact hn₂)
  have h_split_eq : b.toList = a.toList ++ b.toList.drop a.toList.length := by
    have := List.take_append_drop a.toList.length b.toList
    rw [h_take] at this; exact this.symm
  have h_filter_eq : (b.toList.filter p).length =
      (a.toList.filter p).length + (b.toList.drop a.toList.length |>.filter p).length := by
    have := congrArg (fun l => (l.filter p).length) h_split_eq
    simp only [List.filter_append, List.length_append] at this
    exact this
  rw [h_filter_eq]
  suffices (b.toList.drop a.toList.length |>.filter p).length ≥ 1 by omega
  -- j - a.size is a valid index in the drop
  have h_j_drop : j - a.toList.length < (b.toList.drop a.toList.length).length := by
    simp only [List.length_drop, Array.length_toList]; omega
  -- The element at j-a.size in drop equals b[j]
  have h_drop_eq : (b.toList.drop a.toList.length)[j - a.toList.length]'h_j_drop = b[j]'hj_hi := by
    simp only [List.getElem_drop, Array.getElem_toList, Array.length_toList]
    congr 1; omega
  -- So it passes p
  have h_j_p : p ((b.toList.drop a.toList.length)[j - a.toList.length]'h_j_drop) = true := by
    rw [h_drop_eq]; exact h_new
  -- That element is in the filter
  have h_mem : (b.toList.drop a.toList.length)[j - a.toList.length]'h_j_drop ∈
      (b.toList.drop a.toList.length).filter p :=
    List.mem_filter.mpr ⟨List.getElem_mem h_j_drop, h_j_p⟩
  -- So the filter is non-empty, hence length ≥ 1
  cases h_cases : (b.toList.drop a.toList.length).filter p with
  | nil => rw [h_cases] at h_mem; simp at h_mem
  | cons => simp

/-! #### Per-dispatch-layer filtered growth lemmas -/

-- scanDocumentStart grows filtered array by ≥1.
-- The last new token is .documentStart (non-placeholder).
theorem scanDocumentStart_filtered_grows (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ((scanDocumentStart s).tokens.filter p).size ≥ (s.tokens.filter p).size + 1 := by
  apply filtered_grows_of_any_new s.tokens (scanDocumentStart s).tokens _
    (ScannerCorrectness.ScanHelpers.scanDocumentStart_adds_tokens s)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanDocumentStart_preserves_prefix s i hi)
    ((scanDocumentStart s).tokens.size - 1)
    (by have := ScannerCorrectness.ScanHelpers.scanDocumentStart_adds_tokens s; omega)
    (by have := ScannerCorrectness.ScanHelpers.scanDocumentStart_adds_tokens s; omega)
  -- h_new: the last token is .documentStart (non-placeholder)
  unfold scanDocumentStart; dsimp only []
  simp only [ScannerCorrectness.advanceN_preserves_tokens, emit_tokens_push]
  simp only [Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
  decide

-- scanDocumentEnd grows filtered array by ≥1.
-- The last new token is .documentEnd (non-placeholder).
theorem scanDocumentEnd_filtered_grows (s s' : ScannerState)
    (h : scanDocumentEnd s = .ok s') :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (s'.tokens.filter p).size ≥ (s.tokens.filter p).size + 1 := by
  apply filtered_grows_of_any_new s.tokens s'.tokens _
    (ScannerCorrectness.ScanHelpers.scanDocumentEnd_adds_tokens s s' h)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanDocumentEnd_preserves_prefix s s' h i hi)
    (s'.tokens.size - 1)
    (by have := ScannerCorrectness.ScanHelpers.scanDocumentEnd_adds_tokens s s' h; omega)
    (by have := ScannerCorrectness.ScanHelpers.scanDocumentEnd_adds_tokens s s' h; omega)
  -- h_new: the last token is .documentEnd (non-placeholder)
  unfold scanDocumentEnd at h; dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h <;> (split at h <;> first | contradiction | skip) <;>
        (injection h with h_eq; subst h_eq; dsimp only []
         simp only [ScannerCorrectness.advanceN_preserves_tokens, emit_tokens_push]
         simp only [Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
         decide)

/-! #### Directive new-token identification (Tier 1, Turn 1)

`scanDirective` is the one structural-dispatch leaf where the post-state's
filtered token count is *not* always strictly greater than the pre-state:
the YAML 1.2.2 §6.8.3 reserved-directive branch (`%FOO ...`) skips the
trailing line and emits no token at all.  The two YAML/TAG branches do
emit a `.versionDirective`/`.tagDirective` token via `emitAt`.

The three lemmas below characterize the YAML/TAG branches' new token
exactly (`scan{Yaml,Tag}Directive_new_token_eq`) and combine that with a
contradiction in the reserved branch to produce a clean "filtered grows
by ≥1" lemma at the `scanDirective` level under a raw-growth precondition
(`scanDirective_filtered_grows`).  The `h_grew` hypothesis is sound here
because `scanDirective` itself does not invoke `scanNextToken_preprocess`
— the `saveSimpleKey`-induced placeholder pushes happen *before*
structural dispatch, so at this level a strict raw-token-size increase
genuinely identifies a YAML/TAG branch.
-/

/-- The new token emitted by a successful `scanYamlDirective` is exactly
    `.versionDirective major minor` for some `major`/`minor` parsed from
    the input — a non-placeholder. -/
theorem scanYamlDirective_new_token_eq (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState)
    (h_ws : s_after_ws.tokens = s.tokens)
    (h : scanYamlDirective s s_after_ws startPos = .ok s') :
    ∃ major minor : Nat,
      s'.tokens = s.tokens.push { pos := startPos, val := .versionDirective major minor } := by
  unfold scanYamlDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · -- some '#'
        split at h
        · contradiction
        · injection h with h_eq; subst h_eq
          dsimp only [ScannerState.emitAt]
          apply Exists.intro
          apply Exists.intro
          rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
              ScannerCorrectness.ScanHelpers.collectVersionMinorLoop_preserves_tokens,
              ScannerCorrectness.ScanHelpers.collectVersionMajorLoop_preserves_tokens, h_ws]
      · -- some c (not '#')
        split at h
        · contradiction
        · split at h <;> try contradiction
          all_goals (injection h with h_eq; subst h_eq
                     dsimp only [ScannerState.emitAt]
                     apply Exists.intro
                     apply Exists.intro
                     rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
                         ScannerCorrectness.ScanHelpers.collectVersionMinorLoop_preserves_tokens,
                         ScannerCorrectness.ScanHelpers.collectVersionMajorLoop_preserves_tokens, h_ws])
      · -- none
        injection h with h_eq; subst h_eq
        dsimp only [ScannerState.emitAt]
        apply Exists.intro
        apply Exists.intro
        rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
            ScannerCorrectness.ScanHelpers.collectVersionMinorLoop_preserves_tokens,
            ScannerCorrectness.ScanHelpers.collectVersionMajorLoop_preserves_tokens, h_ws]

/-- The new token emitted by a successful `scanTagDirective` is exactly
    `.tagDirective handle pfx` for some `handle`/`pfx` parsed from the
    input — a non-placeholder. -/
theorem scanTagDirective_new_token_eq (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState)
    (h_ws : s_after_ws.tokens = s.tokens)
    (h : scanTagDirective s s_after_ws startPos = .ok s') :
    ∃ handle pfx : String,
      s'.tokens = s.tokens.push { pos := startPos, val := .tagDirective handle pfx } := by
  unfold scanTagDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · -- some '#'
    split at h
    · contradiction
    · injection h with h_eq; subst h_eq
      dsimp only [ScannerState.emitAt]
      apply Exists.intro
      apply Exists.intro
      rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectTagPrefixLoop_preserves_tokens,
          ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectTagHandleDirectiveLoop_preserves_tokens, h_ws]
  · -- some c (not '#')
    split at h
    · contradiction
    · injection h with h_eq; subst h_eq
      dsimp only [ScannerState.emitAt]
      apply Exists.intro
      apply Exists.intro
      rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectTagPrefixLoop_preserves_tokens,
          ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectTagHandleDirectiveLoop_preserves_tokens, h_ws]
  · -- none
    injection h with h_eq; subst h_eq
    dsimp only [ScannerState.emitAt]
    apply Exists.intro
    apply Exists.intro
    rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
        ScannerCorrectness.ScanHelpers.collectTagPrefixLoop_preserves_tokens,
        ScannerCorrectness.skipWhitespace_preserves_tokens,
        ScannerCorrectness.ScanHelpers.collectTagHandleDirectiveLoop_preserves_tokens, h_ws]

/-- `scanDirective` grows the filtered token count by ≥1 *whenever* it
    grows the raw token count.  The contrapositive of the awkward case:
    the RESERVED branch (`%FOO`) yields `s'.tokens.size = s.tokens.size`,
    which contradicts `h_grew`; in YAML/TAG branches the new token is
    `.versionDirective`/`.tagDirective` (non-placeholder) by the
    `*_new_token_eq` lemmas above. -/
theorem scanDirective_filtered_grows (s s' : ScannerState)
    (h : scanDirective s = .ok s')
    (h_grew : s'.tokens.size > s.tokens.size) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  apply filtered_grows_of_any_new s.tokens s'.tokens _
    (by omega)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanDirective_preserves_prefix s s' h i hi)
    s.tokens.size
    (Nat.le.refl)
    (by omega)
  -- Goal: (s'.tokens[s.tokens.size]'_).val != .placeholder = true
  unfold scanDirective at h
  dsimp only [] at h
  split at h
  · contradiction  -- !s.allowDirectives → throw
  · have h_ws : (skipWhitespace (collectDirectiveNameLoop s.advance ""
        (s.inputEnd - s.advance.offset)).2).tokens = s.tokens := by
      rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectDirectiveNameLoop_preserves_tokens,
          ScannerCorrectness.advance_preserves_tokens]
    split at h
    · -- YAML
      split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h
        subst h_eq
        obtain ⟨major, minor, h_eq_tok⟩ :=
          scanYamlDirective_new_token_eq s _ _ s_inner h_ws h_inner
        have h_tokens : (skipToEndOfLine s_inner).tokens =
            s.tokens.push { pos := s.currentPos, val := .versionDirective major minor } := by
          rw [ScannerCorrectness.skipToEndOfLine_preserves_tokens, h_eq_tok]
        simp only [h_tokens, Array.getElem_push_eq]
        rfl
      · contradiction
    · split at h
      · -- TAG
        split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h
          subst h_eq
          obtain ⟨handle, tagPfx, h_eq_tok⟩ :=
            scanTagDirective_new_token_eq s _ _ s_inner h_ws h_inner
          have h_tokens : (skipToEndOfLine s_inner).tokens =
              s.tokens.push { pos := s.currentPos, val := .tagDirective handle tagPfx } := by
            rw [ScannerCorrectness.skipToEndOfLine_preserves_tokens, h_eq_tok]
          simp only [h_tokens, Array.getElem_push_eq]
          rfl
        · contradiction
      · -- RESERVED: no token emitted, contradicts h_grew
        injection h with h_eq
        subst h_eq
        exfalso
        rw [ScannerCorrectness.skipToEndOfLine_preserves_tokens, h_ws] at h_grew
        omega

-- Structural dispatch: full case analysis proving ≥+1 for docStart and docEnd,
-- and ≥0 for directives.  For the directive case, YAML/TAG emit non-placeholder
-- tokens but unknown directives (%RESERVED) emit none.
-- We keep ≥0 (monotone) for the overall structural dispatch but prove ≥+1
-- for the document marker sub-cases which is sufficient for scanNextToken.
theorem dispatchStructural_filtered_mono (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size := by
  have h_mono := ScannerCorrectness.ScanHelpers.dispatchStructural_tokens_mono s c s' h
  have h_pres := ScannerCorrectness.ScanHelpers.dispatchStructural_preserves_prefix s c s' h
  obtain ⟨suffix, h_eq⟩ := Array_filter_prefix_of_raw_prefix s.tokens s'.tokens
    (fun t => t.val != .placeholder) h_mono h_pres
  show (s'.tokens.filter (fun t => t.val != .placeholder)).toList.length ≥
       (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
  rw [h_eq, List.length_append]; omega
-- Flow indicator dispatch: each function emits exactly 1 non-placeholder token.
-- scanFlowSequenceStart/End, scanFlowMappingStart/End push one token each;
-- scanFlowEntry pushes .flowEntry. validateFlowClose is error-only (no state change).
theorem dispatchFlowIndicators_filtered_grows (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_error_simp,
             ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  -- Each goal corresponds to one flow function: seq start, seq end, map start, map end, entry.
  all_goals (
    apply filtered_grows_of_extended_prefix s.tokens _ (fun t => t.val != .placeholder)
    case h_sz =>
      first
        | (have := ScannerCorrectness.scanFlowSequenceStart_adds_one_token s; omega)
        | (have := ScannerCorrectness.scanFlowSequenceEnd_adds_one_token s; omega)
        | (have := ScannerCorrectness.scanFlowMappingStart_adds_one_token s; omega)
        | (have := ScannerCorrectness.scanFlowMappingEnd_adds_one_token s; omega)
        | (have := ScannerCorrectness.ScanHelpers.scanFlowEntry_adds_one_token s _ (by assumption); omega)
    case h_pres =>
      intro i hi
      first
        | exact ScannerCorrectness.ScanHelpers.scanFlowSequenceStart_preserves_prefix s i hi
        | exact ScannerCorrectness.ScanHelpers.scanFlowSequenceEnd_preserves_prefix s i hi
        | exact ScannerCorrectness.ScanHelpers.scanFlowMappingStart_preserves_prefix s i hi
        | exact ScannerCorrectness.ScanHelpers.scanFlowMappingEnd_preserves_prefix s i hi
        | exact ScannerCorrectness.ScanHelpers.scanFlowEntry_preserves_prefix s _ (by assumption) i hi
    case h_new =>
      first
        | (unfold scanFlowSequenceStart; dsimp only []
           simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                       Array.getElem_push_eq]; decide)
        | (unfold scanFlowSequenceEnd; dsimp only []
           simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                       Array.getElem_push_eq]; decide)
        | (unfold scanFlowMappingStart; dsimp only []
           simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                       Array.getElem_push_eq]; decide)
        | (unfold scanFlowMappingEnd; dsimp only []
           simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                       Array.getElem_push_eq]; decide)
        | (-- scanFlowEntry: monadic, unfold to trace the emitted token
           rename_i s' h_fe
           unfold scanFlowEntry at h_fe
           simp only [bind, Except.bind] at h_fe
           repeat (split at h_fe)
           all_goals (first
             | contradiction
             | (injection h_fe with h_eq; subst h_eq; dsimp only []
                simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                            Array.getElem_push_eq]; decide)))
  )

-- Block indicator dispatch: scanBlockEntry, scanKey, scanValue.
-- scanValue uses setIfInBounds → needs scanValuePrepare_filtered_mono.
-- Per-block-function filtered growth lemmas.
-- scanBlockEntry: pushSequenceIndent (monotonic) + emit .blockEntry (+1).
theorem scanBlockEntry_filtered_grows (s s' : ScannerState)
    (h : scanBlockEntry s = .ok s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  apply filtered_grows_of_any_new s.tokens s'.tokens _
    (ScannerCorrectness.ScanHelpers.scanBlockEntry_adds_tokens s s' h)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanBlockEntry_preserves_prefix s s' h i hi)
    (s'.tokens.size - 1)
    (by have := ScannerCorrectness.ScanHelpers.scanBlockEntry_adds_tokens s s' h; omega)
    (by have := ScannerCorrectness.ScanHelpers.scanBlockEntry_adds_tokens s s' h; omega)
  -- h_new: the last token is .blockEntry (non-placeholder)
  unfold scanBlockEntry at h; dsimp only [] at h
  simp only [bind, Except.bind] at h
  repeat (split at h)
  all_goals (first | contradiction | skip)
  all_goals (injection h with h_eq; subst h_eq; dsimp only [])
  all_goals simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                        Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
  all_goals decide

-- scanKey: pushMappingIndent (monotonic) + emit .key (+1).
theorem scanKey_filtered_grows (s s' : ScannerState)
    (h : scanKey s = .ok s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  apply filtered_grows_of_any_new s.tokens s'.tokens _
    (by have := ScannerCorrectness.scanKey_adds_one_token s s' h; omega)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanKey_preserves_prefix s s' h i hi)
    (s'.tokens.size - 1)
    (by have := ScannerCorrectness.scanKey_adds_one_token s s' h; omega)
    (by have := ScannerCorrectness.scanKey_adds_one_token s s' h; omega)
  -- h_new: the last token is .key (non-placeholder)
  unfold scanKey at h
  simp only [] at h
  split at h
  · -- !inFlow: pushMappingIndent called
    split at h
    · split at h
      · contradiction
      · injection h with h_eq; subst h_eq; dsimp only []
        simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                    Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
        decide
    · injection h with h_eq; subst h_eq; dsimp only []
      simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                  Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
      decide
  · -- inFlow: no pushMappingIndent
    split at h
    · split at h
      · contradiction
      · injection h with h_eq; subst h_eq; dsimp only []
        simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                    Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
        decide
    · injection h with h_eq; subst h_eq; dsimp only []
      simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                  Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
      decide

-- scanValue: setIfInBounds replaces placeholder → non-placeholder (monotonic),
-- then emit .value (+1). Uses Array_setIfInBounds_filter_mono for monotonicity
-- through scanValuePrepare, then filtered_grows_of_extended_prefix for the emit step.
set_option maxHeartbeats 400000 in
theorem scanValue_filtered_grows (s s' : ScannerState)
    (h : scanValue s = .ok s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  unfold scanValue at h; dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · injection h with h_eq; subst h_eq; dsimp only []
      simp only [ScannerCorrectness.advance_preserves_tokens]
      -- Goal: ((scanValuePrepare (scanValueClearKey s)).emit(.value).tokens.filter p).size
      --       ≥ (s.tokens.filter p).size + 1
      -- Step 1: emit .value adds 1 non-placeholder via filtered_grows_of_extended_prefix
      have h_emit_grows :=
        filtered_grows_of_extended_prefix
          (scanValuePrepare (scanValueClearKey s)).tokens
          ((scanValuePrepare (scanValueClearKey s)).emit .value).tokens
          (fun t => t.val != .placeholder)
          (by unfold ScannerState.emit; simp [Array.size_push])
          (fun i hi => ScannerCorrectness.emit_preserves_tokens_at _ .value i hi)
          (by simp only [emit_tokens_push, Array.getElem_push_eq]; decide)
      -- Step 2: scanValuePrepare is filter-monotonic
      have h_ck : (scanValueClearKey s).tokens = s.tokens :=
        ScannerCorrectness.scanValueClearKey_preserves_tokens s
      suffices h_prep_mono :
          ((scanValuePrepare (scanValueClearKey s)).tokens.filter
            (fun t => t.val != .placeholder)).size ≥
          (s.tokens.filter (fun t => t.val != .placeholder)).size by omega
      rw [← h_ck]
      unfold scanValuePrepare
      split
      · -- simpleKey.possible = true
        rename_i h_sk
        split
        · split
          · -- Two setIfInBounds
            dsimp only []
            have h1 := Array_setIfInBounds_filter_mono (scanValueClearKey s).tokens
              (scanValueClearKey s).simpleKey.tokenIndex
              ⟨(scanValueClearKey s).simpleKey.pos, .blockMappingStart, (scanValueClearKey s).simpleKey.pos⟩
              (fun t : Positioned YamlToken => t.val != .placeholder) rfl
            have h2 := Array_setIfInBounds_filter_mono
              ((scanValueClearKey s).tokens.setIfInBounds (scanValueClearKey s).simpleKey.tokenIndex
                ⟨(scanValueClearKey s).simpleKey.pos, .blockMappingStart, (scanValueClearKey s).simpleKey.pos⟩)
              ((scanValueClearKey s).simpleKey.tokenIndex + 1)
              ⟨(scanValueClearKey s).simpleKey.pos, .key, (scanValueClearKey s).simpleKey.pos⟩
              (fun t : Positioned YamlToken => t.val != .placeholder) rfl
            omega
          · -- One setIfInBounds
            dsimp only []
            have := Array_setIfInBounds_filter_mono (scanValueClearKey s).tokens
              ((scanValueClearKey s).simpleKey.tokenIndex + 1)
              ⟨(scanValueClearKey s).simpleKey.pos, .key, (scanValueClearKey s).simpleKey.pos⟩
              (fun t : Positioned YamlToken => t.val != .placeholder) rfl
            omega
        · -- inFlow: one setIfInBounds
          dsimp only []
          have := Array_setIfInBounds_filter_mono (scanValueClearKey s).tokens
            ((scanValueClearKey s).simpleKey.tokenIndex + 1)
            ⟨(scanValueClearKey s).simpleKey.pos, .key, (scanValueClearKey s).simpleKey.pos⟩
            (fun t : Positioned YamlToken => t.val != .placeholder) rfl
          omega
      · split
        · dsimp only []; omega
        · split
          · -- pushMappingIndent
            unfold pushMappingIndent
            split
            · -- emit .blockMappingStart
              dsimp only []
              have := filtered_grows_of_extended_prefix (scanValueClearKey s).tokens
                ((scanValueClearKey s).emit .blockMappingStart).tokens
                (fun t : Positioned YamlToken => t.val != .placeholder)
                (by unfold ScannerState.emit; simp [Array.size_push])
                (fun i hi => ScannerCorrectness.emit_preserves_tokens_at _ .blockMappingStart i hi)
                (by simp only [emit_tokens_push, Array.getElem_push_eq]; decide)
              omega
            · omega
          · omega

-- Block indicator dispatch: scanBlockEntry, scanKey, scanValue.
theorem dispatchBlockIndicators_filtered_grows (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (have := scanBlockEntry_filtered_grows _ _ (by assumption); simp_all <;> omega)
    | (have := scanKey_filtered_grows _ _ (by assumption); simp_all <;> omega)
    | (have := scanValue_filtered_grows _ _ (by assumption); simp_all <;> omega)
    | (simp_all; done)

-- Content dispatch: each content function emits exactly 1 non-placeholder token.
-- Helper: the newly-added token at index s.tokens.size is non-placeholder.
-- Each content scanner emits .anchor/.alias/.tag/.scalar — never .placeholder.
-- The proof mirrors dispatchContent_preserves_prefix but tracks the NEW token value
-- instead of preserving existing tokens.
set_option maxHeartbeats 3200000 in
theorem dispatchContent_new_not_placeholder (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (h_strict : s'.tokens.size ≥ s.tokens.size + 1) :
    (s'.tokens[s.tokens.size]'(by omega)).val ≠ YamlToken.placeholder := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  -- '&' anchor
  split at h
  · generalize h_sc : scanAnchorOrAlias s true = result at h
    cases result with
    | error => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h; dsimp only []
      unfold scanAnchorOrAlias at h_sc; dsimp only [] at h_sc
      split at h_sc
      · exact absurd h_sc (by simp)
      · have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
        unfold ScannerState.emitAt; dsimp only []
        simp only [ScannerCorrectness.ScanHelpers.collectAnchorNameLoop_preserves_tokens,
                    ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
        split <;> intro h <;> cases h
  · split at h
    · -- '*' alias
      split at h
      · simp at h
      · generalize h_sc : scanAnchorOrAlias s false = result at h
        cases result with
        | error => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          unfold scanAnchorOrAlias at h_sc; dsimp only [] at h_sc
          split at h_sc
          · exact absurd h_sc (by simp)
          · have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
            unfold ScannerState.emitAt; dsimp only []
            simp only [ScannerCorrectness.ScanHelpers.collectAnchorNameLoop_preserves_tokens,
                        ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
            intro h; cases h
    · split at h
      · -- '!' tag
        generalize h_sc : scanTag s = result at h
        cases result with
        | error => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          unfold scanTag at h_sc; dsimp only [] at h_sc
          split at h_sc
          · -- '<' → scanVerbatimTag (Except-returning)
            simp only [bind, Except.bind] at h_sc
            generalize hv : scanVerbatimTag s.advance s.currentPos = vresult at h_sc
            cases vresult with
            | error => simp at h_sc
            | ok s_verb =>
              dsimp only [] at h_sc
              have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
              unfold scanVerbatimTag at hv; dsimp only [] at hv
              split at hv
              · exact absurd hv (by simp)
              · split at hv
                · exact absurd hv (by simp)
                · have h_eq := Except.ok.inj hv; subst h_eq
                  unfold ScannerState.emitAt; dsimp only []
                  simp only [ScannerCorrectness.ScanHelpers.collectVerbatimTagLoop_preserves_tokens,
                              ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
                  intro h; cases h
          · -- '!' → scanSecondaryTag (pure)
            have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
            unfold scanSecondaryTag; dsimp only []
            unfold ScannerState.emitAt; dsimp only []
            simp only [ScannerCorrectness.ScanHelpers.collectTagSuffixLoop_preserves_tokens,
                        ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
            intro h; cases h
          · -- other → scanNamedTag (pure)
            have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
            unfold scanNamedTag; dsimp only []; split
            · -- foundBang = true
              unfold ScannerState.emitAt; dsimp only []
              simp only [ScannerCorrectness.ScanHelpers.collectTagSuffixLoop_preserves_tokens,
                          ScannerCorrectness.ScanHelpers.collectTagHandleLoop_preserves_tokens,
                          ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
              intro h; cases h
            · -- foundBang = false
              unfold ScannerState.emitAt; dsimp only []
              simp only [ScannerCorrectness.ScanHelpers.collectTagHandleLoop_preserves_tokens,
                          ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
              intro h; cases h
      · -- remaining: block scalar, double/single quoted, plain
        -- Further case-split per character
        split at h
        · -- '|' or '>' → scanBlockScalar
          generalize h_sc : scanBlockScalar s = result at h
          cases result with
          | error => simp at h
          | ok s_bs =>
            simp only [Except.ok.injEq] at h; subst h
            unfold scanBlockScalar at h_sc; simp only [] at h_sc
            split at h_sc
            · contradiction
            · unfold scanBlockScalarBody at h_sc; simp only [] at h_sc
              repeat (any_goals (split at h_sc))
              all_goals (try contradiction)
              all_goals (simp only [Except.ok.injEq] at h_sc; subst h_sc; dsimp only [])
              all_goals (unfold ScannerState.emitAt; dsimp only [])
              all_goals simp only [ScannerCorrectness.ScanHelpers.collectBlockScalarLoop_preserves_tokens,
                                   ScannerCorrectness.ScanHelpers.scanBlockScalarConsumeNewline_preserves_tokens _ _ (by assumption),
                                   ScannerCorrectness.ScanHelpers.scanBlockScalarSkipComment_preserves_tokens,
                                   ScannerCorrectness.skipWhitespace_preserves_tokens,
                                   ScannerCorrectness.ScanHelpers.parseBlockHeaderLoop_preserves_tokens,
                                   ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
              all_goals (intro h; cases h)
        · split at h
          · -- '"' → scanDoubleQuoted
            generalize h_sc : scanDoubleQuoted s = result at h
            cases result with
            | error => simp at h
            | ok s_dq =>
              simp only [Except.ok.injEq] at h
              -- s' may have simpleKey update: split at the conditional
              split at h <;> (subst h; try dsimp only [])
              all_goals (
                unfold scanDoubleQuoted at h_sc
                simp only [bind, Except.bind] at h_sc
                split at h_sc <;> try contradiction
                rename_i heq_dq
                have h_collect := ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
                  s.advance "" _ _ _ _ _ _ heq_dq
                have h_adv := ScannerCorrectness.advance_preserves_tokens s
                split at h_sc
                · split at h_sc <;> try contradiction
                  injection h_sc with h_eq; subst h_eq; dsimp only []
                  unfold ScannerState.emitAt; dsimp only []
                  simp only [h_collect, h_adv, Array.getElem_push_eq]
                  intro h; cases h
                · injection h_sc with h_eq; subst h_eq; dsimp only []
                  unfold ScannerState.emitAt; dsimp only []
                  simp only [h_collect, h_adv, Array.getElem_push_eq]
                  intro h; cases h)
          · split at h
            · -- '\'' → scanSingleQuoted
              generalize h_sc : scanSingleQuoted s = result at h
              cases result with
              | error => simp at h
              | ok s_sq =>
                simp only [Except.ok.injEq] at h
                split at h <;> (subst h; try dsimp only [])
                all_goals (
                  unfold scanSingleQuoted at h_sc
                  simp only [bind, Except.bind] at h_sc
                  split at h_sc <;> try contradiction
                  rename_i heq_sq
                  have h_collect := ScannerCorrectness.ScanHelpers.collectSingleQuotedLoop_preserves_tokens
                    s.advance "" _ _ _ _ _ _ heq_sq
                  have h_adv := ScannerCorrectness.advance_preserves_tokens s
                  split at h_sc
                  · split at h_sc <;> try contradiction
                    injection h_sc with h_eq; subst h_eq; dsimp only []
                    unfold ScannerState.emitAt; dsimp only []
                    simp only [h_collect, h_adv, Array.getElem_push_eq]
                    intro h; cases h
                  · injection h_sc with h_eq; subst h_eq; dsimp only []
                    unfold ScannerState.emitAt; dsimp only []
                    simp only [h_collect, h_adv, Array.getElem_push_eq]
                    intro h; cases h)
            · split at h
              · -- canStartPlainScalar → scanPlainScalar
                generalize h_sc : scanPlainScalar s = result at h
                cases result with
                | error => simp at h
                | ok s_ps =>
                  simp only [Except.ok.injEq] at h; subst h
                  unfold scanPlainScalar at h_sc
                  simp only [bind, Except.bind] at h_sc
                  split at h_sc <;> try contradiction
                  rename_i heq_ps
                  injection h_sc with h_eq; subst h_eq; dsimp only []
                  unfold ScannerState.emitAt; dsimp only []
                  have h_collect := ScannerCorrectness.ScanHelpers.collectPlainScalarLoop_preserves_tokens
                    s "" "" _ _ _ _ _ heq_ps
                  simp only [h_collect, Array.getElem_push_eq]
                  intro h; cases h
              · -- error case: unexpectedChar
                simp at h

-- All content tokens (anchor, alias, tag, scalar) are non-placeholder.
set_option maxHeartbeats 3200000 in
theorem dispatchContent_filtered_grows (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  have h_pres i (hi : i < s.tokens.size) :=
    ScannerCorrectness.ScanHelpers.dispatchContent_preserves_prefix s c s' h i hi
  have h_strict : s'.tokens.size ≥ s.tokens.size + 1 := by
    have h_mono := ScannerCorrectness.ScanHelpers.dispatchContent_tokens_mono s c s' h
    -- Each scanner adds exactly 1 token (≥ + 1):
    unfold scanNextToken_dispatchContent at h
    simp only [bind, ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
    simp only [Except.bind] at h
    repeat (any_goals (split at h))
    any_goals contradiction
    all_goals first
      | (have := ScannerCorrectness.ScanHelpers.scanBlockScalar_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (have := ScannerCorrectness.ScanHelpers.scanDoubleQuoted_adds_one_token s _ (by assumption);
         simp only [Except.ok.injEq] at h; subst h; dsimp only []; omega)
      | (have := ScannerCorrectness.ScanHelpers.scanSingleQuoted_adds_one_token s _ (by assumption);
         simp only [Except.ok.injEq] at h; subst h; dsimp only []; omega)
      | (have := ScannerCorrectness.ScanHelpers.scanDoubleQuoted_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (have := ScannerCorrectness.ScanHelpers.scanSingleQuoted_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (have := ScannerCorrectness.ScanHelpers.scanPlainScalar_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (simp only [Except.ok.injEq] at h; subst h; dsimp only [];
         have := ScannerCorrectness.ScanHelpers.scanAnchorOrAlias_adds_one_token s true _ (by assumption); omega)
      | (have := ScannerCorrectness.ScanHelpers.scanAnchorOrAlias_adds_one_token s false _ (by assumption); simp_all <;> omega)
      | (have := ScannerCorrectness.ScanHelpers.scanTag_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (simp_all <;> omega)
  exact filtered_grows_of_any_new s.tokens s'.tokens _
    h_strict (fun i hi => h_pres i hi) s.tokens.size
    (by omega) (by omega)
    (by have := dispatchContent_new_not_placeholder s s' c h h_strict
        simp only [bne_iff_ne]; exact this)

/-! #### Dispatch-level filtered growth (Turn 3 of EmitterScannability migration)

These three helpers compose `preprocess_filtered_mono` (≥), `allowDir_ite_filter`
(=), and one of the `dispatch*_filtered_grows` lemmas (≥ +1) to give a clean
witness that — given a SUCCESSFUL non-structural dispatch path — `scanNextToken`
strictly grows the filtered token count.  They are the building blocks Turn 3
uses inside each `scanNextToken_flow_*` emitter helper to expose a per-step
`ScanChainGrew` witness alongside the existing `scanNextToken s = .ok (some s')`
output, sidestepping the line-8343 sorry. -/

theorem scanNextToken_via_flow_dispatch_filtered_grows
    (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (_h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (_h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok (some s_result)) :
    (s_result.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  have h_pp_mono := preprocess_filtered_mono s _ _ h_pp
  have h_ad_eq_filter :
      (s_ad.tokens.filter (fun t => t.val != .placeholder)).size =
      (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
    rw [h_ad_eq]; split <;> rfl
  have h_disp := dispatchFlowIndicators_filtered_grows _ _ _ h_flow
  omega

theorem scanNextToken_via_block_dispatch_filtered_grows
    (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (_h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (_h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (_h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok (some s_result)) :
    (s_result.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  have h_pp_mono := preprocess_filtered_mono s _ _ h_pp
  have h_ad_eq_filter :
      (s_ad.tokens.filter (fun t => t.val != .placeholder)).size =
      (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
    rw [h_ad_eq]; split <;> rfl
  have h_disp := dispatchBlockIndicators_filtered_grows _ _ _ h_block
  omega

theorem scanNextToken_via_content_dispatch_filtered_grows
    (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (_h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (_h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (_h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (_h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok none)
    (h_content : scanNextToken_dispatchContent s_ad c = .ok s_result) :
    (s_result.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  have h_pp_mono := preprocess_filtered_mono s _ _ h_pp
  have h_ad_eq_filter :
      (s_ad.tokens.filter (fun t => t.val != .placeholder)).size =
      (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
    rw [h_ad_eq]; split <;> rfl
  have h_disp := dispatchContent_filtered_grows _ _ _ h_content
  omega

-- In flow context, every successful `scanNextToken` step strictly grows the
-- filtered token count.  This is the in-flow analogue of the loose
-- `scanNextToken_filtered_grows` (which carries a sorry on the
-- structural-directive branch).  With `s.inFlow = true ∧ s.currentIndent < 0
-- ∧ s.col > 0` and the next character being non-whitespace,
-- `dispatchStructural_none_flow` rules out the directive branch entirely, so
-- the conclusion goes through unconditionally for emitter outputs.
--
-- Used at construction sites of `EmitScansInFlow` family (Tier 1 Turn 3) to
-- obtain the per-step witness needed to build `ScanChainGrew`.
set_option maxHeartbeats 800000 in
theorem scanNextToken_filtered_grows_in_flow
    (s s' : ScannerState) (c : Char) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨c :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#')
    (h_snt : scanNextToken s = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size >
    (s.tokens.filter (fun t => t.val != .placeholder)).size := by
  -- Step 1: pin down preprocess output.
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, c)) :=
    scanNextToken_preprocess_flow s c rest s.col hcorr h_flow h_nws h_nlb h_nc
  -- Step 2: structural dispatch returns none (saveSimpleKey preserves
  -- inFlow / currentIndent / col).
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) c = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col_pos)
  -- Step 3: post-allowDir state s_ad and its inFlow witness for checkBlockFlowIndent.
  let s_ad : ScannerState := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have hs_ad : s_ad = if (saveSimpleKey s).allowDirectives then
      { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
    else saveSimpleKey s := rfl
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok () :=
    checkBlockFlowIndent_ok_flow _ _ (h_ad_flow ▸ h_flow)
  -- Step 4: unfold scanNextToken using the pinned dispatch info.
  unfold scanNextToken at h_snt
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind, h_pp, h_struct,
             ← hs_ad, h_check] at h_snt
  -- Step 5: case-analyze on dispatchFlowIndicators result.
  match h_flow_eq : scanNextToken_dispatchFlowIndicators s_ad c with
  | .error _ => rw [h_flow_eq] at h_snt; simp at h_snt
  | .ok (some s_flow) =>
    rw [h_flow_eq] at h_snt; simp only at h_snt
    injection h_snt with h_eq; injection h_eq with h_eq; subst h_eq
    have h_grew := scanNextToken_via_flow_dispatch_filtered_grows
      s _ s_ad s_flow c h_pp h_struct hs_ad h_check h_flow_eq
    omega
  | .ok none =>
    rw [h_flow_eq] at h_snt; simp only at h_snt
    -- Now case-analyze on dispatchBlockIndicators result.
    match h_block_eq : scanNextToken_dispatchBlockIndicators s_ad c with
    | .error _ => rw [h_block_eq] at h_snt; simp at h_snt
    | .ok (some s_block) =>
      rw [h_block_eq] at h_snt; simp only at h_snt
      injection h_snt with h_eq; injection h_eq with h_eq; subst h_eq
      have h_grew := scanNextToken_via_block_dispatch_filtered_grows
        s _ s_ad s_block c h_pp h_struct hs_ad h_check h_flow_eq h_block_eq
      omega
    | .ok none =>
      rw [h_block_eq] at h_snt; simp only at h_snt
      -- Final dispatch: content.
      match h_cont_eq : scanNextToken_dispatchContent s_ad c with
      | .error _ => rw [h_cont_eq] at h_snt; simp at h_snt
      | .ok s_cont =>
        rw [h_cont_eq] at h_snt; simp only at h_snt
        injection h_snt with h_eq; injection h_eq with h_eq; subst h_eq
        have h_grew := scanNextToken_via_content_dispatch_filtered_grows
          s _ s_ad s_cont c h_pp h_struct hs_ad h_check h_flow_eq h_block_eq h_cont_eq
        omega



end L4YAML.Proofs.EmitterScannability
