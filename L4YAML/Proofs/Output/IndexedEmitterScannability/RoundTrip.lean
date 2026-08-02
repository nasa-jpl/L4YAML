/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.ParseStream

/-! # `IndexedEmitterScannability.RoundTrip` — Phase 3 Step 6f.3b3.roundtrip.{fidelity, filterinfra, maintheorem.growth}

**Status**: §5.1 (compose invariance for scalars) + §5.4.G prefix-and-tokens
infrastructure + §5.4.G filtered-token tracking (emit-string structure,
flow-close tokens equation, outermost-close existential extensions) +
§5.4.G.5 foundation lemmas for filtered chain reasoning (flow-context
emission equations, chain combinators, prefix preservation, scanner
boundary tokens) landed.
Indexed twins of legacy `EmitterScannability.lean` lines 8490–8530 (§5.1),
8875–9262 (§5.4.G.1–4), 9016–9056 + 9267–9473 (§5.4.G.5).

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
open L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth
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
lemma resolveAliases_scalarIx (s : Scalar)
    (anchors : Array (String × YamlValue)) :
    (YamlValue.scalar s).resolveAliases anchors = .scalar s := by
  unfold YamlValue.resolveAliases; rfl

/-- `stripAnchors` on a scalar just clears the anchor field. -/
lemma stripAnchors_scalarIx (s : Scalar) :
    (YamlValue.scalar s).stripAnchors = .scalar { s with anchor := none } := by
  unfold YamlValue.stripAnchors; rfl

/-- `resolveAliasesOrdered` returns scalars unchanged (whatever binding it makes). -/
lemma resolveAliasesOrdered_fst_scalarIx (s : Scalar)
    (anchors : Array (String × YamlValue)) (env : List (String × YamlValue)) :
    ((YamlValue.scalar s).resolveAliasesOrdered anchors env).fst = .scalar s := by
  simp only [YamlValue.resolveAliasesOrdered]

/-- `compose` on a scalar document preserves the content field. -/
lemma compose_scalar_contentIx (doc : YamlDocument) (s : Scalar)
    (h_val : doc.value = .scalar s) :
    (doc.compose).value = .scalar { s with anchor := none } := by
  unfold YamlDocument.compose; dsimp only []
  rw [h_val, resolveAliasesOrdered_fst_scalarIx, stripAnchors_scalarIx]

/-- `contentEq` for scalars only depends on the content string. -/
lemma contentEq_scalar_contentIx (s₁ s₂ : Scalar)
    (h : s₁.content = s₂.content) : contentEq (.scalar s₁) (.scalar s₂) = true := by
  unfold contentEq; simp [h]

/-- `contentEq` through compose for scalars: original vs composed. -/
lemma contentEq_scalar_composeIx (s_orig : Scalar) (s_parsed : Scalar)
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
lemma unwindIndents_noop_short_stackIx {input : String}
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
lemma scanFiltered_tokens_eq_of_chain_short_stackIx
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
lemma ScanChainIx_tokens_mono {input : String} {s s' : ScannerStateIx input}
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
lemma scanNextTokenIx_prefix_and_sk_inv {input : String}
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
lemma ScanChainIx_preserves_raw_prefix {input : String}
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
lemma emitPairList_toList_ne_nilIx (p : YamlValue × YamlValue)
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
lemma scanFlowSequenceEnd_tokens_eqIx {input : String}
    (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).tokens.tokens =
      s.tokens.tokens.push (Indexed.IxToken.mk' (input := input)
        s.cursor.pos YamlToken.flowSequenceEnd s.cursor.pos
        (Nat.le_refl _) s.cursor.posBound) := by
  rw [scanFlowSequenceEndIx_tokens_eq]
  rfl

/-- `scanFlowMappingEndIx` pushes exactly one `.flowMappingEnd`
    `IxToken` onto the underlying token array. -/
lemma scanFlowMappingEnd_tokens_eqIx {input : String}
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
lemma scanNextToken_flow_close_seq_outermost_extIx {input : String}
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
      ((saveSimpleKeyIx_directivesPresent s).trans h_dp)
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
lemma scanNextToken_flow_close_mapping_outermost_extIx {input : String}
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
      ((saveSimpleKeyIx_directivesPresent s).trans h_dp)
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

/-! ## §5.4.G.5  Foundation lemmas for filtered chain reasoning

Step `6f.3b3.roundtrip.maintheorem.growth` — **first of 4 sub-sessions**
for the elaborated `.maintheorem` sub-split (the Blueprint's original
3-way `growth-chain / body-characterization / structure-proof` was
bumped to 4-way after a substrate survey revealed
`scanFiltered_boundary_tokens` as a 99-LOC theorem with non-trivial
list/filter manipulation independent of the body characterizations;
see plan-tree in Blueprint).

This section ships:

  - **§5.4.G.5.1** (legacy 9378–9422): flow-context filtered emission
    equations for `scanFlowSequenceStartIx`, `scanFlowMappingStartIx`,
    `scanFlowEntryIx`.
  - **§5.4.G.5.2** (legacy 9426–9473): chain combinators
    `ScanChainIx_deterministic` and `ScanChainIx.split`.
  - **§5.4.G.5.3** (legacy 9043–9056): prefix preservation through
    `FlowMonoChainIx`, namely `FlowMonoChainIx_filtered_prefix`
    (name corrected: the legacy `ScanChain_filtered_prefix` is a
    misnomer since it's actually keyed on `FlowMonoChain`, not
    `ScanChain`).
  - **§5.4.G.5.4** (legacy 9267–9365): scanner boundary tokens,
    `scanFilteredIx_boundary_tokens`.

**Skipped**: `ScanChain_filtered_grows` (legacy 9016–9024). Its proof
depends on the loose `scanNextToken_filtered_grows` which carries a
`sorry` on the directive case (line 9013); downstream sub-sessions
should consume `ScanChainGrewIx_filtered_grows` (already landed at
`EmitScans.lean:173`) by building strict-variant `ScanChainGrewIx`
chains — sidesteps the directive sorry entirely.

**Substrate** (all already landed):
  - `scanFlowSequenceStartIx_tokens_eq`,
    `scanFlowMappingStartIx_tokens_eq` (PlainScalarValid §12f);
    `scanFlowEntryIx_tokens_eq`
    (FilteredGrowth/PerDispatch/StructFlow.lean §0).
  - `emit_tokens_pushIx` (FilteredGrowth/FirstFiltered.lean:424).
  - `Array_filter_prefix_of_raw_prefix`
    (FilteredGrowth/FirstFiltered.lean:439).
  - `FlowMonoChainIx_preserves_raw_prefix`
    (FlowMonoChain/Sync/Invariant.lean:419) +
    `FlowMonoChainIx.tokens_mono` (FlowMonoChain/Basic.lean:190) +
    `FlowMonoChainIx.flowLevel_ge_start`
    (FlowMonoChain/Basic.lean:130).
  - `scanIx_produces_at_least_two`
    (ScannerCorrectness/Basic.lean:550) +
    `scanIx_first_is_streamStart`
    (ScannerCorrectness/StreamStart.lean:910) +
    `scanIx_last_is_streamEnd`
    (ScannerCorrectness/Basic.lean:576).
-/

/-! ### §5.4.G.5.1  Flow-context filtered emission equations

Three small `Array.filter`-shape equations for the three flow-context
scanner steps that each push exactly one non-`.placeholder` token:
`flowSequenceStart`, `flowMappingStart`, `flowEntry`. Each is a 4-step
rewrite chain (`scanFlow*Ix_tokens_eq` → `emit_tokens_pushIx` →
`Array.filter_push` → `decide`). Indexed twins of legacy
`scanFlowSequenceStart_filtered`, `scanFlowMappingStart_filtered`,
`scanFlowEntry_filtered` (lines 9378–9422). -/

/-- `scanFlowSequenceStartIx` filtered token equation: adds exactly one
    `.flowSequenceStart` non-placeholder token. Indexed twin of legacy
    `scanFlowSequenceStart_filtered` (line 9378). -/
lemma scanFlowSequenceStartIx_filtered {input : String}
    (s : ScannerStateIx input) :
    let p := fun (t : Indexed.IxToken input) => t.token != YamlToken.placeholder
    (scanFlowSequenceStartIx s).tokens.tokens.filter p =
    (s.tokens.tokens.filter p).push (Indexed.IxToken.mk' (input := input)
      s.cursor.pos YamlToken.flowSequenceStart s.cursor.pos
      (Nat.le_refl _) s.cursor.posBound) := by
  intro p
  have h_eq : (scanFlowSequenceStartIx s).tokens.tokens =
      (s.emit YamlToken.flowSequenceStart).tokens.tokens := by
    rw [scanFlowSequenceStartIx_tokens_eq]
  rw [h_eq, emit_tokens_pushIx, Array.filter_push]
  rfl

/-- `scanFlowMappingStartIx` filtered token equation: adds exactly one
    `.flowMappingStart` non-placeholder token. Indexed twin of legacy
    `scanFlowMappingStart_filtered` (line 9389). -/
lemma scanFlowMappingStartIx_filtered {input : String}
    (s : ScannerStateIx input) :
    let p := fun (t : Indexed.IxToken input) => t.token != YamlToken.placeholder
    (scanFlowMappingStartIx s).tokens.tokens.filter p =
    (s.tokens.tokens.filter p).push (Indexed.IxToken.mk' (input := input)
      s.cursor.pos YamlToken.flowMappingStart s.cursor.pos
      (Nat.le_refl _) s.cursor.posBound) := by
  intro p
  have h_eq : (scanFlowMappingStartIx s).tokens.tokens =
      (s.emit YamlToken.flowMappingStart).tokens.tokens := by
    rw [scanFlowMappingStartIx_tokens_eq]
  rw [h_eq, emit_tokens_pushIx, Array.filter_push]
  rfl

/-- `scanFlowEntryIx` filtered token equation (when it succeeds): adds
    exactly one `.flowEntry` non-placeholder token. Indexed twin of
    legacy `scanFlowEntry_filtered` (line 9401). -/
lemma scanFlowEntryIx_filtered {input : String}
    {s s' : ScannerStateIx input}
    (h : scanFlowEntryIx s = .ok s') :
    let p := fun (t : Indexed.IxToken input) => t.token != YamlToken.placeholder
    s'.tokens.tokens.filter p =
    (s.tokens.tokens.filter p).push (Indexed.IxToken.mk' (input := input)
      s.cursor.pos YamlToken.flowEntry s.cursor.pos
      (Nat.le_refl _) s.cursor.posBound) := by
  intro p
  have h_eq : s'.tokens.tokens = (s.emit YamlToken.flowEntry).tokens.tokens := by
    rw [scanFlowEntryIx_tokens_eq h]
  rw [h_eq, emit_tokens_pushIx, Array.filter_push]
  rfl

/-! ### §5.4.G.5.2  Chain combinators

`ScanChainIx_deterministic` (two chains from the same start with the
same step count reach the same end, by chain induction + functional
agreement of `scanNextTokenIx`) and `ScanChainIx.split` (split a chain
of `n₁ + n₂` steps at the `n₁`-th boundary). Indexed twins of legacy
`ScanChain_deterministic` (line 9426) and `ScanChain.split` (line 9438).
Pure inductions on the chain shape — no substrate dependency beyond
`Option.some.inj` + `Except.ok.inj`. -/

/-- Two `ScanChainIx`s from the same start state with the same step
    count reach the same end state. Indexed twin of legacy
    `ScanChain_deterministic` (line 9426). -/
lemma ScanChainIx_deterministic {input : String}
    {s s₁ s₂ : ScannerStateIx input} {n : Nat}
    (h₁ : ScanChainIx s n s₁) (h₂ : ScanChainIx s n s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | zero => cases h₂; rfl
  | @step s s_mid₁ s₁ k h_snt₁ _ ih =>
    match h₂ with
    | .step h_snt₂ h_rest₂ =>
      have : s_mid₁ = _ := Option.some.inj (Except.ok.inj (h_snt₁.symm.trans h_snt₂))
      subst this
      exact ih h_rest₂

/-- Split a `ScanChainIx` of length `n₁ + n₂` at the `n₁`-th boundary:
    if `s` reaches `s₁` in `n₁` steps and `s₂` in `n₁ + n₂` steps, then
    `s₁` reaches `s₂` in `n₂` steps. Indexed twin of legacy
    `ScanChain.split` (line 9438). -/
lemma ScanChainIx.split {input : String}
    {s s₁ s₂ : ScannerStateIx input} {n₁ n₂ : Nat}
    (h₁ : ScanChainIx s n₁ s₁) (h_total : ScanChainIx s (n₁ + n₂) s₂) :
    ScanChainIx s₁ n₂ s₂ := by
  induction h₁ generalizing s₂ with
  | zero => simpa using h_total
  | @step s s_mid s₁ k h_snt₁ _ ih =>
    have h_rw : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [h_rw] at h_total
    match h_total with
    | .step h_snt₂ h_rest₂ =>
      have : s_mid = _ := Option.some.inj (Except.ok.inj (h_snt₁.symm.trans h_snt₂))
      subst this
      exact ih h_rest₂

/-! ### §5.4.G.5.3  Prefix preservation through FlowMonoChainIx

Through a `FlowMonoChainIx`, the filtered token array of the final
state has the filtered array of the initial state as a prefix. Lifts
the raw-index prefix preservation
(`FlowMonoChainIx_preserves_raw_prefix`) to filtered-array prefix
preservation via `Array_filter_prefix_of_raw_prefix`.

**Name correction from legacy**: the legacy theorem is named
`ScanChain_filtered_prefix` but its hypothesis is `FlowMonoChain`, not
`ScanChain`. The indexed port renames to `FlowMonoChainIx_filtered_prefix`
to match the actual hypothesis shape.

**Hypothesis structure** (matching legacy line 9043):
  - `h_fmc`: `FlowMonoChainIx fl₀ s n s'`.
  - `h_sk`: `s.simpleKey.possible = false` (no in-flight reservation).
  - `h_sync`: `s.simpleKeyStack.size ≥ s.flowLevel`.
  - `h_stack_floor`: stack entries at index ≥ `fl₀` with
    `possible = true` have `tokenIndex ≥ s.tokens.size`.

Both call sites (in downstream `parseStream_emit*` theorems) have
`fl₀ = s₁.flowLevel = 1` with `s₁.simpleKeyStack.size = 1`, making
`h_stack_floor` vacuously true. Indexed twin of legacy
`ScanChain_filtered_prefix` (line 9043). -/

lemma FlowMonoChainIx_filtered_prefix {input : String}
    {s s' : ScannerStateIx input} {n fl₀ : Nat}
    (h_fmc : FlowMonoChainIx fl₀ s n s')
    (h_sk : s.simpleKey.possible = false)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_stack_floor : ∀ j, fl₀ ≤ j → (hj : j < s.simpleKeyStack.size) →
      s.simpleKeyStack[j].possible = true →
      s.simpleKeyStack[j].tokenIndex ≥ s.tokens.size) :
    let p := fun (t : Indexed.IxToken input) => t.token != YamlToken.placeholder
    ∃ suffix, (s'.tokens.tokens.filter p).toList =
              (s.tokens.tokens.filter p).toList ++ suffix := by
  have h_inv : SimpleKeyAboveFloorIx s s.tokens.size fl₀ :=
    ⟨fun hp => absurd hp (by simp [h_sk]),
     h_stack_floor,
     by have := h_fmc.flowLevel_ge_start; omega⟩
  refine Array_filter_prefix_of_raw_prefix s.tokens.tokens s'.tokens.tokens _
    (FlowMonoChainIx.tokens_mono h_fmc) (fun i hi => ?_)
  obtain ⟨_, h_eq⟩ := FlowMonoChainIx_preserves_raw_prefix h_fmc s.tokens.size
    (Nat.le_refl _) h_inv h_sync i hi
  exact h_eq

/-! ### §5.4.G.5.4  Scanner boundary tokens

`scanFilteredIx_boundary_tokens` characterizes the structural flanks of
`scanFilteredIx`'s output: at least two tokens, leading `.streamStart`,
trailing `.streamEnd`. Lifts the raw-scan boundary facts
(`scanIx_produces_at_least_two`, `scanIx_first_is_streamStart`,
`scanIx_last_is_streamEnd`) through the placeholder-stripping filter
via the observation that `.streamStart` and `.streamEnd` are themselves
non-`.placeholder` and so survive the filter (`List.head_filter` /
`List.getLast_filter` chain).

Indexed twin of legacy `scanFiltered_boundary_tokens` (line 9267). -/

lemma scanFilteredIx_boundary_tokens (input : String)
    (tokens : Indexed.TokenStream input)
    (h : scanFilteredIx input = .ok tokens) :
    tokens.tokens.size ≥ 2 ∧
    tokens.tokens[0]!.token = YamlToken.streamStart ∧
    tokens.tokens[tokens.tokens.size - 1]!.token = YamlToken.streamEnd := by
  unfold scanFilteredIx at h
  -- Case split on the underlying scan result.
  generalize h_scan : scanIx input = result at h
  match result with
  | .error _ => simp at h
  | .ok raw =>
  -- h : .ok { tokens := raw.tokens.filter ... } = .ok tokens
  injection h with h_eq
  -- h_eq : { tokens := raw.tokens.filter ... } = tokens — destructure to underlying array.
  have h_tokens_eq : tokens.tokens = raw.tokens.filter
      (fun t => t.token != YamlToken.placeholder) := by
    rw [← h_eq]
  -- Raw scan boundary properties.
  have h_raw_sz : raw.tokens.size ≥ 2 := scanIx_produces_at_least_two raw h_scan
  have h_raw_first : (raw.tokens[0]'(by omega)).token = YamlToken.streamStart :=
    scanIx_first_is_streamStart raw h_scan (by omega)
  have h_raw_last : (raw.tokens[raw.tokens.size - 1]'(by omega)).token = YamlToken.streamEnd :=
    scanIx_last_is_streamEnd raw h_scan (by omega)
  -- List-level reasoning: head/last pass filter, preserved in filtered list.
  let p : Indexed.IxToken input → Bool := fun t => t.token != YamlToken.placeholder
  let l := raw.tokens.toList
  have h_l_ne : l ≠ [] := by
    intro h0
    have : raw.tokens.size = 0 := by show l.length = 0; simp [h0]
    omega
  have h_p_first : p (l.head h_l_ne) = true := by
    show ((l.head h_l_ne).token != YamlToken.placeholder) = true
    have : (l.head h_l_ne).token = YamlToken.streamStart := by
      rw [List.head_eq_getElem]; exact h_raw_first
    rw [this]; decide
  have h_p_last : p (l.getLast h_l_ne) = true := by
    show ((l.getLast h_l_ne).token != YamlToken.placeholder) = true
    have : (l.getLast h_l_ne).token = YamlToken.streamEnd := by
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
  -- Filtered size ≥ 2.
  have h_filt_sz_list : (l.filter p).length ≥ 2 := by
    have h_pos : (l.filter p).length > 0 := List.length_pos_iff.mpr h_flt_ne
    have h_ne_1 : (l.filter p).length ≠ 1 := by
      intro h1
      obtain ⟨a, h_eq'⟩ := List.length_eq_one_iff.mp h1
      have : l.head h_l_ne = l.getLast h_l_ne := by
        rw [← h_head_filt, ← h_last_filt]; simp [h_eq']
      have := congrArg Indexed.IxToken.token this
      rw [show (l.head h_l_ne).token = YamlToken.streamStart
            from by rw [List.head_eq_getElem]; exact h_raw_first,
          show (l.getLast h_l_ne).token = YamlToken.streamEnd
            from by rw [List.getLast_eq_getElem]; exact h_raw_last] at this
      cases this
    omega
  have h_filt_sz : (raw.tokens.filter p).size ≥ 2 := by
    show (raw.tokens.filter p).toList.length ≥ 2
    rw [Array.toList_filter]; exact h_filt_sz_list
  -- Transport to tokens via h_tokens_eq.
  have h_tsz : tokens.tokens.size ≥ 2 := h_tokens_eq ▸ h_filt_sz
  refine ⟨h_tsz, ?_, ?_⟩
  · -- tokens[0]!.token = .streamStart
    suffices h : (raw.tokens.filter p)[0]!.token = YamlToken.streamStart by
      rw [h_tokens_eq]; exact h
    rw [getElem!_pos _ 0 (by omega)]
    have h_first_val : ((l.filter p).head h_flt_ne).token = YamlToken.streamStart := by
      rw [h_head_filt, List.head_eq_getElem]; exact h_raw_first
    rw [List.head_eq_getElem] at h_first_val
    show ((raw.tokens.filter p).toList[0]'(show 0 < (raw.tokens.filter p).size from by omega)).token
      = YamlToken.streamStart
    simp only [Array.toList_filter]; exact h_first_val
  · -- tokens[N-1]!.token = .streamEnd
    suffices h : (raw.tokens.filter p)[(raw.tokens.filter p).size - 1]!.token
                  = YamlToken.streamEnd by
      rw [h_tokens_eq]; exact h
    rw [getElem!_pos _ _ (by omega)]
    have h_last_val : ((l.filter p).getLast h_flt_ne).token = YamlToken.streamEnd := by
      rw [h_last_filt, List.getLast_eq_getElem]; exact h_raw_last
    rw [List.getLast_eq_getElem] at h_last_val
    have h_sz_eq : (raw.tokens.filter p).size = (l.filter p).length := by
      have : (raw.tokens.filter p).toList = l.filter p := Array.toList_filter
      show (raw.tokens.filter p).toList.length = (l.filter p).length; rw [this]
    show ((raw.tokens.filter p).toList[(raw.tokens.filter p).size - 1]'(by
            show (raw.tokens.filter p).size - 1 < (raw.tokens.filter p).size; omega)).token
      = YamlToken.streamEnd
    simp only [Array.toList_filter, h_sz_eq]; exact h_last_val

/-! ## §5.4.G.6  Body characterization (sub-session `.body1`)

Sub-step `6f.3b3.roundtrip.maintheorem.body1`. Port the Part-1 (first new
filtered token shape) of `emitList_body_filtered_characterization` and
`emitPairList_body_filtered_characterization` (legacy 9474–9552 and
9570–9646). The Part-2 outer-level-flowEntry claims are deferred to
`.body2`.

These body theorems lift the strict-growth chain produced by
`emitList_scans_nonemptyIx` / `emitPairList_scans_nonemptyIx` (`EmitScans.lean`
§2 / §3) to a token-count characterization at the first new filtered
position (`old_sz = (s.tokens.tokens.filter p).size`): after the chain
the filtered token array has strictly more entries than at the start,
so `old_sz < (s'.tokens.tokens.filter p).size`.

**SKAF-style hypotheses dropped from the Part-1 signature**: the
original scaffold draft of these `_part1` wrappers carried `h_sk`
(`s.simpleKey.possible = false`), `h_sync`, and `h_stack_floor`
forward as placeholders for the eventual second-conjunct (token-
shape) work. None of them is actually used in the Part-1 body
(only the first conjunct `old_sz < (s'.filter).size` is proved
here, which doesn't depend on `FlowMonoChainIx_filtered_prefix`).
The `.body1.tokenshape.{list,pair}` sub-sessions will re-introduce
the SKAF-style hypotheses at their own signatures when they
extend with the token-shape conjunct. The downstream consumer
(`scanFilteredIx_emitSeq_nonempty_structure`) will then discharge
them from `scanNextTokenIx_flow_open_seq_init` (Endpoint.lean §6).

**Conjunct deviation from legacy Part 1**: the legacy Part-1 has TWO
conjuncts (`old_sz < (s'.filter).size` ∧ `token at old_sz is a content
start`). The legacy SECOND conjunct is itself a `sorry` (line 9550),
and porting it on the indexed substrate would require establishing the
`SimpleKeyAboveFloorIx` invariant on the post-first-step state to
propagate the per-character first-filtered-token lemmas
(`FilteredGrowth/FirstFiltered.lean` §1–§3) from `s_first` through the
rest chain via `FlowMonoChainIx_filtered_prefix`. The required SKAF
derivation case-analyzes on the first step (`scanFlowSequenceStartIx` /
`scanFlowMappingStartIx` / `scanDoubleQuotedIx`) and exceeds the
sub-session LOC budget. The indexed port ships ONLY the FIRST conjunct
(`old_sz < (s'.tokens.tokens.filter p).size`). The token-shape second
conjunct lands in `.body1.tokenshape` (next sub-session) along with the
matching `.body2` outer-level-flowEntry claim. -/

/-! ### §5.4.G.6.1  emitList body Part 1 -/

/-- Body characterization for `emitList` in flow context (Part 1 only,
    first-conjunct only, sub-session `.body1.list`): scanning the
    comma-separated body of a non-empty flow sequence advances at least
    one new (non-`.placeholder`) token. The token-shape second conjunct
    (`content start at old_sz`) and the outer-level flowEntry Part-2
    claim are deferred to `.body1.tokenshape` / `.body2`. Indexed twin
    of legacy `emitList_body_filtered_characterization` (lines
    9474–9552), first-conjunct fragment of Part-1 only. -/
lemma emitList_body_filtered_characterizationIx_part1
    {input : String} (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlowIx (input := input) v)
    (s : ScannerStateIx input) (rest : List Char)
    (h_corr : ScannerSurfCorrIx s
      ⟨(L4YAML.Emit.emit.emitList items).toList ++ rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.cursor.pos.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_endline : EndLineOnLineIx s)
    (h_dp : s.directivesPresent = false) :
    let p := fun (t : Indexed.IxToken input) => t.token != YamlToken.placeholder
    let old_sz := (s.tokens.tokens.filter p).size
    ∃ n s', ScanChainIx s n s'
    ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.cursor.pos.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.cursor.pos.line = s.cursor.pos.line
    ∧ AllTokensOnLineIx s' s'.cursor.pos.line
    ∧ EndLineOnLineIx s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChainIx s.flowLevel s n s'
    ∧ old_sz < (s'.tokens.tokens.filter p).size := by
  intro p old_sz
  -- Construct the strict chain from EmitListScansInFlowIx.
  have h_scan := emitList_scans_nonemptyIx items h_ne h_all
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc⟩ :=
    h_scan s rest h_corr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_dp
  -- Strict chain growth: through n steps, filtered count grows by ≥ n.
  have h_grows := ScanChainGrewIx_filtered_grows h_chain
  -- n ≥ 1 because emitList of a non-empty list is non-empty.
  have h_n_pos : n ≥ 1 := by
    match n, h_chain with
    | 0, .zero =>
      exfalso
      have h_chars_eq :=
        CouplingBridge.CharsFromOffset_unique h_corr.chars_from h_corr'.chars_from
      have h_len := congrArg List.length h_chars_eq
      simp only [List.length_append] at h_len
      have h_nil : (L4YAML.Emit.emit.emitList items).toList = [] := by
        match h_list : (L4YAML.Emit.emit.emitList items).toList with
        | [] => rfl
        | _ :: _ => simp [h_list] at h_len
      cases items with
      | nil => exact h_ne rfl
      | cons v vs => exact absurd h_nil (emitList_toList_ne_nil v vs)
    | _ + 1, _ => omega
  -- old_sz < (s'.filter).size from strict growth (n ≥ 1).
  have h_lt : old_sz < (s'.tokens.tokens.filter p).size := by
    show (s.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)).size <
         (s'.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)).size
    omega
  -- Assemble the result: forget strict chain to ScanChainIx at the public boundary.
  exact ⟨n, s', h_chain.toScanChainIx, h_corr', h_fl', h_dp', h_ids', h_ek',
         h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
         h_stack', h_fmc, h_lt⟩

/-! ### §5.4.G.6.2  emitPairList body Part 1 -/

/-- Body characterization for `emitPairList` in flow context (Part 1 only,
    first-conjunct only, sub-session `.body1.pair`): scanning the
    comma-separated body of a non-empty flow mapping advances at least
    one new (non-`.placeholder`) token. The legacy Part-1 includes
    additionally `n ≥ 3` (key + value-indicator + value) and "first new
    filtered token is `.key`" — both deferred to `.body1.tokenshape`
    along with the Part-2 outer-level flowEntry claim. Indexed twin of
    legacy `emitPairList_body_filtered_characterization` (lines
    9570–9646), first-conjunct fragment of Part-1 only.

    See `§5.4.G.6.1`'s deviation note for the reasoning about why the
    second conjunct (token shape) is deferred: the indexed
    `FlowMonoChainIx_filtered_prefix` propagation needs `SimpleKeyAboveFloorIx`
    on the post-first-step state, and `scanValuePrepareIx`'s
    placeholder→.key conversion adds further intricacy for the pair case
    (the `.key` first-filtered-token claim comes from step 2, not step 1). -/
lemma emitPairList_body_filtered_characterizationIx_part1
    {input : String} (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlowIx (input := input) p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlowIx (input := input) p.2)
    (s : ScannerStateIx input) (rest : List Char)
    (h_corr : ScannerSurfCorrIx s
      ⟨(L4YAML.Emit.emit.emitPairList pairs).toList ++ rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.cursor.pos.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_endline : EndLineOnLineIx s)
    (h_dp : s.directivesPresent = false) :
    let p := fun (t : Indexed.IxToken input) => t.token != YamlToken.placeholder
    let old_sz := (s.tokens.tokens.filter p).size
    ∃ n s', ScanChainIx s n s'
    ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.cursor.pos.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.cursor.pos.line = s.cursor.pos.line
    ∧ AllTokensOnLineIx s' s'.cursor.pos.line
    ∧ EndLineOnLineIx s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChainIx s.flowLevel s n s'
    ∧ old_sz < (s'.tokens.tokens.filter p).size := by
  intro p old_sz
  -- Construct the strict chain from EmitPairListScansInFlowIx.
  have h_scan := emitPairList_scans_nonemptyIx pairs h_ne h_all_k h_all_v
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc⟩ :=
    h_scan s rest h_corr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_dp
  -- Strict chain growth: through n steps, filtered count grows by ≥ n.
  have h_grows := ScanChainGrewIx_filtered_grows h_chain
  -- n ≥ 1 because emitPairList of a non-empty list is non-empty.
  have h_n_pos : n ≥ 1 := by
    match n, h_chain with
    | 0, .zero =>
      exfalso
      have h_chars_eq :=
        CouplingBridge.CharsFromOffset_unique h_corr.chars_from h_corr'.chars_from
      have h_len := congrArg List.length h_chars_eq
      simp only [List.length_append] at h_len
      have h_nil : (L4YAML.Emit.emit.emitPairList pairs).toList = [] := by
        match h_list : (L4YAML.Emit.emit.emitPairList pairs).toList with
        | [] => rfl
        | _ :: _ => simp [h_list] at h_len
      cases pairs with
      | nil => exact h_ne rfl
      | cons p ps => exact absurd h_nil (emitPairList_toList_ne_nilIx p ps)
    | _ + 1, _ => omega
  -- old_sz < (s'.filter).size from strict growth (n ≥ 1).
  have h_lt : old_sz < (s'.tokens.tokens.filter p).size := by
    show (s.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)).size <
         (s'.tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)).size
    omega
  -- Assemble the result: forget strict chain to ScanChainIx at the public boundary.
  exact ⟨n, s', h_chain.toScanChainIx, h_corr', h_fl', h_dp', h_ids', h_ek',
         h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
         h_stack', h_fmc, h_lt⟩

end L4YAML.Proofs.Indexed.EmitterScannability.RoundTrip
