/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.ParseStream

/-! # `IndexedEmitterScannability.RoundTrip` — Phase 3 Step 6f.3b3.roundtrip.{fidelity, filterinfra}

**Status**: §5.1 (compose invariance for scalars) + §5.4.G prefix-and-tokens
infrastructure + §5.4.G filtered-token tracking (emit-string structure,
flow-close tokens equation, outermost-close existential extensions) landed.
Indexed twins of legacy `EmitterScannability.lean` lines 8490–8530 (§5.1) and
8875–9262 (§5.4.G).

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **§5.1  Compose invariance for scalars** (legacy lines 8490–8530):
    `resolveAliases_scalarIx`, `stripAnchors_scalarIx`,
    `compose_scalar_contentIx`, `contentEq_scalar_contentIx`,
    `contentEq_scalar_composeIx`. **Value-level** — these lemmas
    operate on `YamlValue`, `Scalar`, `YamlDocument` and don't
    depend on the indexed scanner state; they port verbatim.

  - **§5.4.G.1  Prefix and tokens primitives** (legacy lines 8875–8967):
    `unwindIndents_noop_short_stackIx`,
    `scanFiltered_tokens_eq_of_chain_short_stackIx`,
    `ScanChainIx_tokens_mono`, `scanNextTokenIx_prefix_and_sk_inv`,
    `ScanChainIx_preserves_raw_prefix`. **Indexed-substrate**.
    These bridge `scanFilteredIx_of_chain_eq` (FlowMonoChain §5
    Invariant) into the emitter-state setting where the indent
    stack is at most a singleton sentinel.

  - **§5.4.G.2  Emit-string structure** (legacy line 9057):
    `emitPairList_toList_ne_nilIx`. Value-level fact about the
    emitter output string shape.

  - **§5.4.G.3  Flow-close tokens equation** (legacy lines 9064–9078):
    `scanFlowSequenceEnd_tokens_eqIx`, `scanFlowMappingEnd_tokens_eqIx`.
    Sharper variants of the existing `scanFlow*EndIx_tokens_eq`
    (`IndexedScannerPlainScalarValid.lean` §12f) that expose the
    underlying `Array.push` shape with the explicit `IxToken`.

  - **§5.4.G.4  Flow-close outermost extensions** (legacy lines
    9080–9262): `scanNextToken_flow_close_seq_outermost_extIx`,
    `scanNextToken_flow_close_mapping_outermost_extIx`. The
    close-bracket / close-brace existential extension lemmas: from
    a state with `flowLevel = 1` and `peek? = ']'`/`'}'` only, one
    `scanNextTokenIx` step produces a result state whose filtered
    token array is the input filtered array with `.flowSequenceEnd`
    / `.flowMappingEnd` appended (and `flowLevel = 0`,
    `directivesPresent = false`, `peek? = none`, indents preserved).

Subsequent sub-steps populate the main filtered-growth theorem
(`maintheorem`), and the universal round-trip capstone (`universal`).

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan. Note that
**this file inherits the 7 pre-existing `sorry` warnings** carried
forward from the legacy file; whether to discharge them on the
indexed substrate or preserve carry-forward is decided per-`sorry`
at port time in the `maintheorem`/`universal` sub-sessions.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.RoundTrip

open L4YAML
open L4YAML.Grammar
open L4YAML.Indexed
open L4YAML.Emit
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.TokenParser.Indexed
open L4YAML.Proofs.Indexed.EmitterScannability.EmitScans
open L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.Composition
open L4YAML.Proofs.Indexed.Grammable
open L4YAML.Proofs.Indexed.ScannerCorrectness
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid

/-! ## §5  Content Fidelity Infrastructure

Helper lemmas for the content fidelity proof (`emit_roundtrip_content_eqIx`).
-/

/-! ### §5.1  Compose invariance for scalars

`YamlDocument.compose` applies `resolveAliases` and `stripAnchors`.
For scalars, `resolveAliases` is identity and `stripAnchors` only
clears the anchor field. Since `contentEq` ignores anchors, compose
doesn't affect content equivalence for scalars.

These are **value-level** facts and port verbatim from legacy
(lines 8503–8529). They don't depend on the indexed substrate. -/

/-- `resolveAliases` is identity on scalars. -/
theorem resolveAliases_scalarIx (s : Scalar)
    (anchors : Array (String × YamlValue)) :
    (YamlValue.scalar s).resolveAliases anchors = .scalar s := by
  unfold YamlValue.resolveAliases; rfl

/-- `stripAnchors` on a scalar just clears the anchor field. -/
theorem stripAnchors_scalarIx (s : Scalar) :
    (YamlValue.scalar s).stripAnchors = .scalar { s with anchor := none } := by
  unfold YamlValue.stripAnchors; rfl

/-- `compose` on a scalar document preserves the content field. -/
theorem compose_scalar_contentIx (doc : YamlDocument) (s : Scalar)
    (h_val : doc.value = .scalar s) :
    (doc.compose).value = .scalar { s with anchor := none } := by
  unfold YamlDocument.compose; dsimp only []
  rw [h_val, resolveAliases_scalarIx, stripAnchors_scalarIx]

/-- `contentEq` for scalars only depends on the content string. -/
theorem contentEq_scalar_contentIx (s₁ s₂ : Scalar)
    (h : s₁.content = s₂.content) : contentEq (.scalar s₁) (.scalar s₂) = true := by
  unfold contentEq; simp [h]

/-- `contentEq` through compose for scalars: original vs composed. -/
theorem contentEq_scalar_composeIx (s_orig : Scalar) (s_parsed : Scalar)
    (h_content : s_orig.content = s_parsed.content) :
    contentEq (.scalar s_orig) (.scalar { s_parsed with anchor := none }) = true :=
  contentEq_scalar_contentIx s_orig { s_parsed with anchor := none } h_content

/-! ### §5.4.G  Infrastructure for filtered token tracking (indexed)

The legacy `EmitterScannability.lean` §5.4.G groups five infrastructure
lemmas that bridge `scanFiltered_of_chain_eq` (the FlowMonoChain
Invariant §5 export) into the emitter-state setting. The indexed
substrate has matching predicates and primitives:

  - `unwindIndentsIx_tokens_size_le` (Dispatch §1.7) — ≤-monotone,
    parallel to legacy `unwindIndents_adds_tokens`.
  - `unwindIndentsIx_preserves_prefix` (Production
    `IndexedScannerPlainScalarValid` §3) — token-index preservation.
  - `scanNextTokenIx_tokens_size_le` (Dispatch §6) — single-step
    monotone, parallel to legacy `scanNextToken_adds_tokens`.
  - `SimpleKeyAboveIx` + `scanNextTokenIx_preserves_prefix` +
    `scanNextTokenIx_maintains_SimpleKeyAboveIx` (StreamStart §2.1).
  - `scanFilteredIx_of_chain_eq` (FlowMonoChain Sync Invariant §5).

The five lemmas below repackage these primitives in the shape
the round-trip cluster's downstream consumers expect. -/

/-- `unwindIndentsIx` is identity when the indent stack has at most
    one entry. This covers emitter output where `indents = #[]` (the
    default from `ScannerStateIx.mk'`). `unwindIndentsLoopIx` checks
    `s.indents.size > 1` before unwinding; with size ≤ 1, the
    condition fails immediately and the state is returned unchanged.

    **Verbatim port** from legacy `unwindIndents_noop_short_stack`
    (line 8881) — the proof structure is identical because
    `unwindIndentsIx` shares the legacy's `match`/`if` skeleton. -/
theorem unwindIndents_noop_short_stackIx {input : String}
    (s : ScannerStateIx input) (h_stack : s.indents.size ≤ 1) :
    unwindIndentsIx s (-1) = s := by
  unfold unwindIndentsIx
  unfold unwindIndentsLoopIx
  split
  · -- fuel = 0 case (s.indents.size = 0): match returns s directly.
    rfl
  · -- fuel = fuel' + 1 case (s.indents.size ≥ 1): the if-condition
    -- `s.currentIndent > -1 && s.indents.size > 1` must be false.
    split
    · -- if-then branch: requires `s.indents.size > 1`, contradicting
      -- `h_stack : s.indents.size ≤ 1`.
      exfalso
      rename_i h_cond
      simp only [Bool.and_eq_true, decide_eq_true_iff] at h_cond
      omega
    · rfl

/-- When a `ScanChainIx` starts from `s₀ = (mk' input).emit streamStart`
    via `scanFilteredIx`, the token-array equation simplifies to the
    direct `s_final.emit streamEnd` form provided the final indent stack
    is at most a singleton. Combines `scanFilteredIx_of_chain_eq` (the
    FlowMonoChain Sync Invariant §5 export) with `unwindIndents_noop_
    short_stackIx`. -/
theorem scanFiltered_tokens_eq_of_chain_short_stackIx
    (input : String) (s₀ s_final : ScannerStateIx input) (n : Nat)
    (h_s0 : s₀ = (ScannerStateIx.mk' input).emit YamlToken.streamStart)
    (h_no_bom : (ScannerStateIx.mk' input).peek? ≠ some '﻿')
    (h_chain : ScanChainIx s₀ n s_final)
    (h_eof : scanNextTokenIx s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4)
    (h_stack : s_final.indents.size ≤ 1) :
    scanFilteredIx input = .ok ⟨((s_final.emit YamlToken.streamEnd).tokens.tokens.filter
      (fun t => t.token != YamlToken.placeholder))⟩ := by
  have h_eq := scanFilteredIx_of_chain_eq input s₀ s_final n h_s0 h_no_bom h_chain
    h_eof h_fl h_dp h_fuel
  rwa [unwindIndents_noop_short_stackIx s_final h_stack] at h_eq

/-- `ScanChainIx` token-stream monotonicity: the token array grows
    (non-strictly) through any scan chain. Inducts on the chain,
    discharging each step with `scanNextTokenIx_tokens_size_le`. -/
theorem ScanChainIx_tokens_mono {input : String} {s s' : ScannerStateIx input}
    {n : Nat} (h_chain : ScanChainIx s n s') : s'.tokens.size ≥ s.tokens.size := by
  induction h_chain with
  | zero => exact Nat.le_refl _
  | step h_snt _h_rest ih =>
    exact Nat.le_trans (scanNextTokenIx_tokens_size_le h_snt) ih

/-- Combined per-step prefix preservation and simpleKey-invariant
    maintenance. Bundles `scanNextTokenIx_preserves_prefix` (extracting
    the equality from its existential conclusion) with
    `scanNextTokenIx_maintains_SimpleKeyAboveIx` so consumers can pull
    both facts from a single chain step.

    **Precondition shape**: `SimpleKeyAboveIx s n` says all active
    simple keys (current + stacked) have token indices ≥ `n`, which
    keeps simple-key placeholder writes from clobbering the
    prefix. **Conclusion shape**: returns the direct equality
    `s'.tokens[i] = s.tokens[i]` (the implicit size bound is computed
    from `scanNextTokenIx_tokens_size_le`) plus `SimpleKeyAboveIx s' n`,
    enabling straightforward induction in
    `ScanChainIx_preserves_raw_prefix`. -/
theorem scanNextTokenIx_prefix_and_sk_inv {input : String}
    (s s' : ScannerStateIx input)
    (h_next : scanNextTokenIx s = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n) :
    (∀ (i : Nat) (hi : i < n),
      s'.tokens[i]'(by
        have := scanNextTokenIx_tokens_size_le h_next; omega) =
      s.tokens[i]'(by omega)) ∧
    SimpleKeyAboveIx s' n := by
  refine ⟨?_, scanNextTokenIx_maintains_SimpleKeyAboveIx s s' n h_n h_inv h_next⟩
  intro i hi
  obtain ⟨_, h_eq⟩ := scanNextTokenIx_preserves_prefix s s' n h_n h_inv h_next i hi
  exact h_eq

/-- Through a `ScanChainIx` of `k` steps, all raw token positions below
    `n₀` are preserved, provided `n₀ ≤ s.tokens.size` and
    `SimpleKeyAboveIx s n₀` holds. The `SimpleKeyAboveIx` invariant is
    maintained through each step by `scanNextTokenIx_prefix_and_sk_inv`,
    making the induction straightforward. -/
theorem ScanChainIx_preserves_raw_prefix {input : String}
    {s s' : ScannerStateIx input} {k : Nat}
    (h_chain : ScanChainIx s k s')
    (n₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n₀)
    (i : Nat) (hi : i < n₀) :
    s'.tokens[i]'(by have := ScanChainIx_tokens_mono h_chain; omega) =
    s.tokens[i]'(by omega) := by
  induction h_chain with
  | zero => rfl
  | step h_snt _h_rest ih =>
    rename_i s_mid s'_inner n
    have h_adds := scanNextTokenIx_tokens_size_le h_snt
    have ⟨h_pres, h_inv'⟩ := scanNextTokenIx_prefix_and_sk_inv _ _ h_snt n₀ h_n₀ h_inv
    exact (ih (Nat.le_trans h_n₀ h_adds) h_inv').trans (h_pres i hi)

/-! ### §5.4.G.2  Emit-string structure (verbatim from legacy)

`emit.emitPairList` produces a non-empty string when the input has at
least one pair. This is a pure value-level lemma — no indexed substrate
involvement; the same `emitPairList` function is shared between the
legacy and indexed pipelines. Ports verbatim from legacy line 9058. -/

/-- `emitPairList` for non-empty pairs produces a non-empty string. -/
theorem emitPairList_toList_ne_nilIx (p : YamlValue × YamlValue)
    (ps : List (YamlValue × YamlValue)) :
    (L4YAML.Emit.emit.emitPairList (p :: ps)).toList ≠ [] := by
  obtain ⟨c, rest', h_eq, _, _, _⟩ := emitPairList_first_charIx p ps
  rw [h_eq]; exact List.cons_ne_nil _ _

/-! ### §5.4.G.3  Flow-close tokens equation

Sharper variants of `scanFlowSequenceEndIx_tokens_eq` /
`scanFlowMappingEndIx_tokens_eq` (`IndexedScannerPlainScalarValid.lean`
§12f) that expose the underlying `Array.push` shape with the explicit
`IxToken`. The existing `_tokens_eq` lemmas reduce
`(scanFlow*EndIx s).tokens` to `(s.emit _).tokens`; here we go one
step further to `s.tokens.tokens.push (IxToken.mk' …)`, which is the
shape the close-bracket outermost-extension theorems consume below.

**Verbatim port** from legacy `scanFlowSequenceEnd_tokens_eq` /
`scanFlowMappingEnd_tokens_eq` (lines 9065, 9073) — the indexed shape
differs only by the `IxToken.mk'` construction (vs. legacy
`{ pos := s.currentPos, val := … }`); structurally `rfl` discharges
both. -/

/-- `scanFlowSequenceEndIx` pushes exactly one `.flowSequenceEnd`
    `IxToken` onto the underlying token array. -/
theorem scanFlowSequenceEnd_tokens_eqIx {input : String}
    (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).tokens.tokens =
      s.tokens.tokens.push (Indexed.IxToken.mk' (input := input)
        s.cursor.pos YamlToken.flowSequenceEnd s.cursor.pos
        (Nat.le_refl _) s.cursor.posBound) := by
  rw [scanFlowSequenceEndIx_tokens_eq]
  rfl

/-- `scanFlowMappingEndIx` pushes exactly one `.flowMappingEnd`
    `IxToken` onto the underlying token array. -/
theorem scanFlowMappingEnd_tokens_eqIx {input : String}
    (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).tokens.tokens =
      s.tokens.tokens.push (Indexed.IxToken.mk' (input := input)
        s.cursor.pos YamlToken.flowMappingEnd s.cursor.pos
        (Nat.le_refl _) s.cursor.posBound) := by
  rw [scanFlowMappingEndIx_tokens_eq]
  rfl

/-! ### §5.4.G.4  Flow-close outermost extensions

The close-bracket / close-brace existential extension lemmas: from a
state with `flowLevel = 1`, `peek? = ']'` / `'}'` (and nothing after),
one `scanNextTokenIx` step produces a result state whose filtered
token array is the input filtered array with `.flowSequenceEnd` /
`.flowMappingEnd` appended. These compose the §1 (`preprocess_flow` →
`saveSimpleKeyIx`), §2 (`checkBlockFlowIndent_ok_close_*`), §3
(`dispatchFlowIndicators_close_*`), and §7
(`scanNextTokenIx_via_flow_dispatch`) pipeline lemmas from
`FlowMonoChain.Maintenance.Pipeline` / `.Sync.{Scenarios.Preflow,
Invariant}`, with `scanFlow*EndIx_detail` (`.Sync.Detail`) handling
the result-state field equations.

**Adaptation notes from legacy**:

  - Legacy `s.col` / `s.col_pos > 0` → indexed `s.cursor.pos.col` /
    `s.cursor.pos.col > 0`.
  - Legacy `Positioned YamlToken` with `{ pos := s.currentPos, val :=
    .flowSequenceEnd }` → indexed `IxToken.mk' s.cursor.pos
    .flowSequenceEnd s.cursor.pos (Nat.le_refl _) s.cursor.posBound`.
  - Legacy splits `dispatchFlowIndicators_close_bracket_nested` /
    `_outermost`; indexed has the single
    `dispatchFlowIndicators_close_bracket` (Pipeline §3) which
    handles both via `s.flowLevel > 0`.
  - Legacy `saveSimpleKey_preserves_{inFlow, col, indents, flowLevel,
    directivesPresent}` → indexed `@[simp]` field projections
    `saveSimpleKeyIx_{inFlow, cursor, indents, flowLevel,
    directivesPresent}` (Preserve.Helpers §2).
  - Legacy `scanFlowSequenceEnd_{flowLevel, _preserves_dp,
    _preserves_indents}` separate lemmas → indexed
    `scanFlowSequenceEndIx_detail` (Sync.Detail §4) bundles
    SurfCorr + flowLevel + dp + indents + col into one fact,
    yielding a tighter proof.
  - Legacy `saveSimpleKey_filter_placeholder` → indexed
    `saveSimpleKeyIx_filter_placeholder` (Preserve.Helpers §5);
    same statement modulo `.tokens.tokens` projection chain. -/

/-- Close-bracket step for outermost `]`: filtered token array is the
    input filtered array with `.flowSequenceEnd` appended.

    Traces through `saveSimpleKeyIx` (adds only placeholders, filtered
    out by `saveSimpleKeyIx_filter_placeholder`) → `allowDirectives`
    update (no token change) → `scanFlowSequenceEndIx` (appends
    `.flowSequenceEnd` which passes the placeholder filter). Indexed
    twin of legacy `scanNextToken_flow_close_seq_outermost_ext` (line
    8086). -/
theorem scanNextToken_flow_close_seq_outermost_extIx {input : String}
    (s : ScannerStateIx input)
    (hcorr : ScannerSurfCorrIx s ⟨[']'], s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    ∃ s' : ScannerStateIx input,
      scanNextTokenIx s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ s'.indents = s.indents
      ∧ (∃ tok : Indexed.IxToken input, tok.token = YamlToken.flowSequenceEnd ∧
          s'.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder) =
          (s.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)).push tok) := by
  -- §1: preprocess on flow context produces `saveSimpleKeyIx s` + `']'`.
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, ']')) :=
    scanNextTokenIx_preprocess_flow s ']' [] s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- saveSimpleKeyIx preserves inFlow / cursor (and hence col, offset).
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_cur : (saveSimpleKeyIx s).cursor = s.cursor := saveSimpleKeyIx_cursor s
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [h_sk_cur]
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent
    rw [saveSimpleKeyIx_indents]
  -- §2: structural dispatch returns none.
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow)
      (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- §3: the allowDirectives-update intermediate state.
  let s_ad : ScannerStateIx input :=
    if (saveSimpleKeyIx s).allowDirectives then
      { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
    else saveSimpleKeyIx s
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad ']' = .ok () :=
    checkBlockFlowIndent_ok_close_bracket s_ad
  -- s_ad preserves flowLevel / directivesPresent / cursor / indents from s.
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact FlowMonoChain.saveSimpleKeyIx_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKeyIx_directivesPresent s
  have h_ad_cur : s_ad.cursor = s.cursor := by
    simp only [s_ad]; split <;> exact h_sk_cur
  have h_ad_col : s_ad.cursor.pos.col = s.cursor.pos.col := by
    rw [h_ad_cur]
  have h_ad_indents : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKeyIx_indents s
  -- Transfer ScannerSurfCorrIx through saveSimpleKeyIx + allowDirectives update.
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨[']'], s_ad.cursor.pos.col⟩ := by
    rw [h_ad_col]
    refine ScannerSurfCorrIx_transfer hcorr ?_ h_ad_col h_ad_indents
    rw [h_ad_cur]
  -- §3: flow dispatch on `']'` with flowLevel = 1 > 0 returns `scanFlowSequenceEndIx s_ad`.
  have h_ad_fl_pos : s_ad.flowLevel > 0 := by
    rw [h_ad_fl, h_fl]; decide
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad ']' =
      .ok (some (scanFlowSequenceEndIx s_ad)) :=
    dispatchFlowIndicators_close_bracket s_ad h_ad_fl_pos
  -- §4: factoring lemma assembles the full `scanNextTokenIx s`.
  have h_snt : scanNextTokenIx s = .ok (some (scanFlowSequenceEndIx s_ad)) :=
    scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
      (scanFlowSequenceEndIx s_ad) ']' h_pp h_struct rfl h_check h_flow_disp
  -- §5: `scanFlowSequenceEndIx_detail` bundles SurfCorr / flowLevel / dp / indents / col.
  obtain ⟨h_corr_final, h_fl_final, h_dp_final, h_ind_final, _⟩ :=
    scanFlowSequenceEndIx_detail s_ad [] h_ad_corr
  -- Result fields (refer directly to `scanFlowSequenceEndIx s_ad`).
  have h_result_fl : (scanFlowSequenceEndIx s_ad).flowLevel = 0 := by
    rw [h_fl_final, h_ad_fl, h_fl]
  have h_result_dp : (scanFlowSequenceEndIx s_ad).directivesPresent = false := by
    rw [h_dp_final, h_ad_dp]; exact h_dp
  have h_result_eof : (scanFlowSequenceEndIx s_ad).peek? = none :=
    peek_none_of_empty_surfIx _ _ h_corr_final
  have h_result_indents : (scanFlowSequenceEndIx s_ad).indents = s.indents := by
    rw [h_ind_final]; exact h_ad_indents
  -- §6: filtered tokens. saveSimpleKeyIx_filter_placeholder discharges the
  --      saveSimpleKey step; the allowDirectives update doesn't touch tokens.
  have h_ad_tokens_filter :
      s_ad.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder) =
      s.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder) := by
    simp only [s_ad]
    split <;> exact saveSimpleKeyIx_filter_placeholder s
  -- `scanFlowSequenceEnd_tokens_eqIx s_ad` then gives the push form;
  -- `.flowSequenceEnd ≠ .placeholder` so `Array.filter_push` keeps the token.
  let new_ixtok : Indexed.IxToken input :=
    Indexed.IxToken.mk' (input := input) s_ad.cursor.pos YamlToken.flowSequenceEnd
      s_ad.cursor.pos (Nat.le_refl _) s_ad.cursor.posBound
  have h_result_tokens : ∃ tok : Indexed.IxToken input,
      tok.token = YamlToken.flowSequenceEnd ∧
      (scanFlowSequenceEndIx s_ad).tokens.tokens.filter
          (fun t => t.token != YamlToken.placeholder) =
      (s.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)).push tok := by
    refine ⟨new_ixtok, rfl, ?_⟩
    rw [scanFlowSequenceEnd_tokens_eqIx s_ad, Array.filter_push]
    have h_keep : (new_ixtok.token != YamlToken.placeholder) = true := rfl
    rw [if_pos h_keep, h_ad_tokens_filter]
  exact ⟨scanFlowSequenceEndIx s_ad, h_snt, h_result_fl, h_result_dp,
         h_result_eof, h_result_indents, h_result_tokens⟩

/-- Close-brace step for outermost `}`: filtered token array is the
    input filtered array with `.flowMappingEnd` appended. Indexed twin
    of legacy `scanNextToken_flow_close_mapping_outermost_ext` (line
    9176). Structurally identical to the close-bracket case modulo
    the bracket / brace / sequenceEnd / mappingEnd substitutions. -/
theorem scanNextToken_flow_close_mapping_outermost_extIx {input : String}
    (s : ScannerStateIx input)
    (hcorr : ScannerSurfCorrIx s ⟨['}'], s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    ∃ s' : ScannerStateIx input,
      scanNextTokenIx s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ s'.indents = s.indents
      ∧ (∃ tok : Indexed.IxToken input, tok.token = YamlToken.flowMappingEnd ∧
          s'.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder) =
          (s.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)).push tok) := by
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, '}')) :=
    scanNextTokenIx_preprocess_flow s '}' [] s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_cur : (saveSimpleKeyIx s).cursor = s.cursor := saveSimpleKeyIx_cursor s
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [h_sk_cur]
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent
    rw [saveSimpleKeyIx_indents]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow)
      (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad : ScannerStateIx input :=
    if (saveSimpleKeyIx s).allowDirectives then
      { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
    else saveSimpleKeyIx s
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad '}' = .ok () :=
    checkBlockFlowIndent_ok_close_brace s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact FlowMonoChain.saveSimpleKeyIx_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKeyIx_directivesPresent s
  have h_ad_cur : s_ad.cursor = s.cursor := by
    simp only [s_ad]; split <;> exact h_sk_cur
  have h_ad_col : s_ad.cursor.pos.col = s.cursor.pos.col := by
    rw [h_ad_cur]
  have h_ad_indents : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKeyIx_indents s
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨['}'], s_ad.cursor.pos.col⟩ := by
    rw [h_ad_col]
    refine ScannerSurfCorrIx_transfer hcorr ?_ h_ad_col h_ad_indents
    rw [h_ad_cur]
  have h_ad_fl_pos : s_ad.flowLevel > 0 := by
    rw [h_ad_fl, h_fl]; decide
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad '}' =
      .ok (some (scanFlowMappingEndIx s_ad)) :=
    dispatchFlowIndicators_close_brace s_ad h_ad_fl_pos
  have h_snt : scanNextTokenIx s = .ok (some (scanFlowMappingEndIx s_ad)) :=
    scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
      (scanFlowMappingEndIx s_ad) '}' h_pp h_struct rfl h_check h_flow_disp
  obtain ⟨h_corr_final, h_fl_final, h_dp_final, h_ind_final, _⟩ :=
    scanFlowMappingEndIx_detail s_ad [] h_ad_corr
  have h_result_fl : (scanFlowMappingEndIx s_ad).flowLevel = 0 := by
    rw [h_fl_final, h_ad_fl, h_fl]
  have h_result_dp : (scanFlowMappingEndIx s_ad).directivesPresent = false := by
    rw [h_dp_final, h_ad_dp]; exact h_dp
  have h_result_eof : (scanFlowMappingEndIx s_ad).peek? = none :=
    peek_none_of_empty_surfIx _ _ h_corr_final
  have h_result_indents : (scanFlowMappingEndIx s_ad).indents = s.indents := by
    rw [h_ind_final]; exact h_ad_indents
  have h_ad_tokens_filter :
      s_ad.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder) =
      s.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder) := by
    simp only [s_ad]
    split <;> exact saveSimpleKeyIx_filter_placeholder s
  let new_ixtok : Indexed.IxToken input :=
    Indexed.IxToken.mk' (input := input) s_ad.cursor.pos YamlToken.flowMappingEnd
      s_ad.cursor.pos (Nat.le_refl _) s_ad.cursor.posBound
  have h_result_tokens : ∃ tok : Indexed.IxToken input,
      tok.token = YamlToken.flowMappingEnd ∧
      (scanFlowMappingEndIx s_ad).tokens.tokens.filter
          (fun t => t.token != YamlToken.placeholder) =
      (s.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)).push tok := by
    refine ⟨new_ixtok, rfl, ?_⟩
    rw [scanFlowMappingEnd_tokens_eqIx s_ad, Array.filter_push]
    have h_keep : (new_ixtok.token != YamlToken.placeholder) = true := rfl
    rw [if_pos h_keep, h_ad_tokens_filter]
  exact ⟨scanFlowMappingEndIx s_ad, h_snt, h_result_fl, h_result_dp,
         h_result_eof, h_result_indents, h_result_tokens⟩

end L4YAML.Proofs.Indexed.EmitterScannability.RoundTrip
