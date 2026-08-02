/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.EmitScans

/-! # `EmitScansStrong` — Phase 3 Step
`6f.3b3.roundtrip.maintheorem.body1.tokenshape.substrate`

**Sub-sub-session 1 of `.body1.tokenshape`** (second-of-3 after the
second scope discovery — see Reflection 152, refined by Reflection 153).

Ships ONE new strong predicate and ONE strong inductive theorem:

  * **§1 `EmitPairListScansInFlowIx_strong`** — strengthening of
    `EmitPairListScansInFlowIx` (`EmitScans.lean §3`) that additionally
    exposes the **`n ≥ 3` lower bound** on the chain length. Direct
    consumer enabler for the legacy `emitPairList_body_filtered_
    characterization` sorry at line 9638 (`n ≥ 3`).
  * **§2 `emitPairList_scans_nonemptyIx_strong`** — proof by induction
    on the pair list, mirroring the singleton/multi-pair split of the
    weak `emitPairList_scans_nonemptyIx`. The `n ≥ 3` bound emerges
    from the chain composition `n₁(key) + 1(colon) + (n_v' + 1)(value)`
    with each sub-chain bounded below by 1 via the same
    non-empty-emit argument the weak proof uses to establish
    `h_n_v_pos`.

**`.body1.tokenshape.substrate.b` additions** (§3, §4) — landed
2026-05-28:

  * **§3 `scanValuePrepareIx_flow_pointwise`** — pointwise
    characterization of `scanValuePrepareIx` in the flow branch.
    Per Reflection 153 discovery (`scanValuePrepareIx` overwrites
    position `idx + 1`, NOT `idx`): exposes that the new token at
    position `idx + 1` is `.key` and every other position is
    preserved. Used by `.tokenshape.pair` to identify the first
    new filtered token as `.key`.
  * **§4 `FlowMonoChainIx_filtered_prefix_no_overwrite`** —
    floor-parameterized filtered-prefix preservation through a
    `FlowMonoChainIx`. Takes `SimpleKeyAboveFloorIx` as an explicit
    input (instead of constructing it from `simpleKey.possible =
    false`), so the lemma applies whenever the consumer can
    establish SKAF directly. This admits the case where the chain
    starts in a state with `simpleKey.possible = true` provided the
    chosen floor `n₀ ≤ simpleKey.tokenIndex`. Reflection 153's
    refinement of the no-overwrite hypothesis design materialises
    here as: the "protected" raw prefix is positions `i < n₀`,
    where `n₀` is consumer-chosen and SKAF-justified.

**`.body1.tokenshape.substrate.c` additions** (§5) — landed
2026-05-29 per Reflection 155:

  * **§5 `NoOverwriteAtIx s m`** + the parallel infrastructure of
    constructors / dispatcher maintenance / capstone /
    chain-induction wrapper. Per Reflection 155 discovery during
    `.tokenshape.list` design: §4's SKAF-input wrapper is
    INSUFFICIENT for the consumer scenario after `[` because with
    `s.simpleKeyAllowed = true`, step 1's `saveSimpleKey` creates a
    stack entry with `tokenIndex = m₀ = s.tokens.size`, so SKAF at
    any floor `≥ m₀ + 1` fails. The first new filtered token sits
    at raw position `m_first = m₀ + 2` (above the simpleKey
    reservation), so we need per-position no-overwrite preservation
    rather than SKAF-floor preservation. §5 ships:
    - `NoOverwriteAtIx s m` invariant (current simpleKey + stack
      entries all satisfy `possible = true → m ≠ tokenIndex ∧ m
      ≠ tokenIndex + 1`).
    - 4 transport constructors (cleared+preserved, preserved,
      flow_open, flow_close) — parallel to SKAF's constructors
      (`FlowMonoChain/Basic.lean §2.1`).
    - preprocess maintenance (`scanNextTokenIx_preprocess_maintains_
      NoOverwriteAtIx`) tracking saveSimpleKey activation under
      `m < tokens.size`.
    - 4 dispatcher maintenance lemmas (structural / flow-indicators /
      block-indicators / content) — parallel to SKAF's dispatcher
      maintenance (`FlowMonoChain/Basic.lean §2.3`).
    - Capstone `scanNextTokenIx_maintains_NoOverwriteAtIx` —
      parallel to `scanNextTokenIx_maintains_SKAFIx`.
    - `scanValuePrepareIx_preserves_position_specific` and
      `scanValueIx_preserves_position_specific` — pointwise (≠m)
      analogs of the (`<n` + `tokenIndex ≥ n`)-form preservation
      lemmas in `IndexedScannerPlainScalarValid §12k`.
    - `scanNextTokenIx_preserves_position_specific` — step-level
      dispatcher case-analysis mirroring
      `scanNextTokenIx_preserves_prefix_of_simpleKey`
      (`FlowMonoChain/Sync/Invariant.lean §3`) but with the "≠m"
      hypothesis form.
    - `FlowMonoChainIx_preserves_position_specific` — chain-
      induction wrapper mirroring `FlowMonoChainIx_preserves_raw_
      prefix` (`FlowMonoChain/Sync/Invariant.lean §4`).

  Differs from SKAF: NO sync hypothesis needed (no floor → no
  stack-size lower bound for the flow-close case). Closes zero
  legacy sorries — pure enablement for `.tokenshape.list` and
  `.tokenshape.pair`.

**Axiom posture**: pure triple `[propext, Classical.choice, Quot.sound]`.
No new axioms introduced.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.EmitScans

open L4YAML
open L4YAML.CharPredicates
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
open L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid
open L4YAML.Proofs.Indexed.ScannerCorrectness

variable {input : String}

/-! ## §1  `EmitPairListScansInFlowIx_strong` — strong pair predicate

Adds the `n ≥ 3` chain-length lower bound to the conclusion of
`EmitPairListScansInFlowIx`. The bound comes from the singleton-case
chain composition `n₁(key emit) + 1(colon) + (n_v' + 1)(value emit)`
where each component is positive (key emit produces ≥ 1 step,
colon is exactly 1 step, value emit produces ≥ 1 step). The
multi-pair case adds a comma step and a recursive call, both
positive, so the bound is preserved.

This predicate directly enables the legacy
`emitPairList_body_filtered_characterization` sorry at line 9638
(`n ≥ 3`) — the consumer derives the bound from the strong
predicate's output. -/

/-- `EmitPairListScansInFlowIx_strong pairs`: strong version of
    `EmitPairListScansInFlowIx pairs` (see `EmitScans.lean §3` for the
    weak version's documentation) additionally exposing the chain
    length lower bound `n ≥ 3`. -/
def EmitPairListScansInFlowIx_strong (pairs : List (YamlValue × YamlValue)) : Prop :=
  ∀ (s : ScannerStateIx input) (rest : List Char),
    ScannerSurfCorrIx s ⟨(L4YAML.Emit.emit.emitPairList pairs).toList ++ rest, s.cursor.pos.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.cursor.pos.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLineIx s s.cursor.pos.line →
    EndLineOnLineIx s →
    s.directivesPresent = false →
    ∃ n s', ScanChainGrewIx (fun t => t.token != .placeholder) s n s'
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
      ∧ n ≥ 3

/-- `EmitPairListScansInFlowIx_strong` implies the weak version
    (drops the `n ≥ 3` conjunct). Useful as a degradation when the
    consumer doesn't need the strong claim. -/
lemma EmitPairListScansInFlowIx_strong.toWeak {pairs : List (YamlValue × YamlValue)}
    (h_strong : EmitPairListScansInFlowIx_strong (input := input) pairs) :
    EmitPairListScansInFlowIx (input := input) pairs := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_dp
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, _h_n_ge_3⟩ :=
    h_strong s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_dp
  exact ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
         h_indent', h_line', h_atol', h_endline', h_stack', h_fmc⟩

/-! ## §2  `emitPairList_scans_nonemptyIx_strong` — inductive proof

Mirrors the weak `emitPairList_scans_nonemptyIx` (`EmitScans.lean §3`)
structurally, threading the `n ≥ 3` lower bound through both the
singleton and multi-pair branches via the per-sub-chain positivity
arguments already used in the weak proof for `h_n_v_pos` (value scan
non-empty) and `h_n_r_pos` (recursive pair-list scan non-empty). The
new positivity argument needed is `h_n₁_pos` (key scan non-empty),
proven by the same non-empty-`emit` → non-empty-chain argument. -/

/-- Non-empty pair list scanning, **strong version**: additionally
    asserts `n ≥ 3`. Mirrors `emitPairList_scans_nonemptyIx` structure
    (singleton + multi-pair induction); the lower bound emerges from
    the chain composition `n₁(key) + 1(colon) + (n_v' + 1)(value)`
    with positive sub-chains. -/
lemma emitPairList_scans_nonemptyIx_strong (pairs : List (YamlValue × YamlValue))
    (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlowIx (input := input) p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlowIx (input := input) p.2) :
    EmitPairListScansInFlowIx_strong (input := input) pairs := by
  induction pairs with
  | nil => contradiction
  | cons p tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_dp
    match tail, ih with
    | [], _ =>
      -- ══ Singleton [(k,v)]: emit k ++ ": " ++ emit v ══
      have h_eq : (L4YAML.Emit.emit.emitPairList [p]).toList ++ rest_chars =
          (L4YAML.Emit.emit p.1).toList ++
            ([':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++ rest_chars) := by
        simp [L4YAML.Emit.emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: scan key via EmitScansInFlowIx
      have h_ek_key : EmitScansInFlowIx (input := input) p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, _ska₁, _h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁⟩ :=
        h_ek_key s ([':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_dp
      -- NEW: extract n₁ ≥ 1 from non-empty `emit p.1`.
      have h_n₁_pos : n₁ ≥ 1 := by
        match n₁, h_chain₁ with
        | 0, .zero =>
          exfalso
          have h_chars_eq :=
            CouplingBridge.CharsFromOffset_unique hcorr.chars_from h_corr₁.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (L4YAML.Emit.emit p.1).toList = [] := by
            match h_list : (L4YAML.Emit.emit p.1).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.1
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      -- Step 2: scan ':' via scanNextToken_flow_valueIx
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂⟩ :=
        scanNextToken_flow_valueIx s₁ ((L4YAML.Emit.emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
          (h_dp₁.trans h_dp)
      -- Step 3: handle the leading space before the value via the preprocess-eq twin
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorrIx s₂
          ⟨' ' :: c_v :: (rest_v ++ rest_chars), s₂.cursor.pos.col⟩ := by
        have h_eq_chars : ' ' :: ((L4YAML.Emit.emit p.2).toList ++ rest_chars) =
            ' ' :: c_v :: (rest_v ++ rest_chars) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerStateIx.inFlow
        exact decide_eq_true (by rw [h_fl₂, h_fl₁]; exact h_fl)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerStateIx.currentIndent; rw [h_ids₂]; exact h_indent₁
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃,
              _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃⟩ :=
        scanNextTokenIx_preprocess_flow_ws1 s₂ c_v (rest_v ++ rest_chars) h_corr₂_ws
          h_s2_flow h_nws_v h_nlb_v h_nc_v h_s2_indent
      have h_corr₃' : ScannerSurfCorrIx s₃
          ⟨(L4YAML.Emit.emit p.2).toList ++ rest_chars, s₃.cursor.pos.col⟩ := by
        have : c_v :: (rest_v ++ rest_chars) =
            (L4YAML.Emit.emit p.2).toList ++ rest_chars := by
          rw [h_first_v]; simp only [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: scan value via EmitScansInFlowIx
      have h_ev : EmitScansInFlowIx (input := input) p.2 := h_all_v p (.head _)
      obtain ⟨n₃, s_end, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, _, _, h_atol_end,
              h_endline_end, h_stack_end, h_fmc₃⟩ :=
        h_ev s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂])
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_dp₃, h_dp₂, h_dp₁]; exact h_dp)
      -- Step 5: lift chain for s₂ via the preprocessing equality
      have h_snt_eq : scanNextTokenIx s₂ = scanNextTokenIx s₃ :=
        scanNextTokenIx_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq :=
            CouplingBridge.CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (L4YAML.Emit.emit p.2).toList = [] := by
            match h_list : (L4YAML.Emit.emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      have h_filt_le :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≤
          (s₃.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrewIx (fun t => t.token != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrewIx_of_scanNextTokenIx_eq h_snt_eq h_filt_le h_chain₃
      have h_grew₂ :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size >
          (s₁.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorrIx s₁
            ⟨':' :: (' ' :: (L4YAML.Emit.emit p.2).toList ++ rest_chars), s₁.cursor.pos.col⟩ := by
          have : [':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++ rest_chars =
              ':' :: (' ' :: (L4YAML.Emit.emit p.2).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextTokenIx_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (L4YAML.Emit.emit p.2).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      have h_fmc₃' : FlowMonoChainIx s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by rw [h_fl₃, h_fl₂, h_fl₁]) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChainIx s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChainIx_of_scanNextTokenIx_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChainIx.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrewIx.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      -- NEW: n ≥ 3 from h_n₁_pos and arithmetic (n₁ ≥ 1, n₃' + 1 ≥ 1).
      have h_n_ge_3 : n₁ + 1 + (n₃' + 1) ≥ 3 := by omega
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_,
        h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, h_n_ge_3⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack_v₂, h_stack₁]
    | p' :: ps, ih =>
      -- ══ Multi-pair: emit k ++ ": " ++ emit v ++ ", " ++ emitPairList (p' :: ps) ══
      have h_eq : (L4YAML.Emit.emit.emitPairList (p :: p' :: ps)).toList ++ rest_chars =
          (L4YAML.Emit.emit p.1).toList ++ ([':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
        simp [L4YAML.Emit.emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: scan key via EmitScansInFlowIx
      have h_ek_key : EmitScansInFlowIx (input := input) p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, _ska₁, _h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁⟩ :=
        h_ek_key s ([':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_dp
      -- Step 2: scan ':' via scanNextToken_flow_valueIx
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂⟩ :=
        scanNextToken_flow_valueIx s₁
          ((L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
          (h_dp₁.trans h_dp)
      -- Step 3: handle the leading space before the value
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorrIx s₂
          ⟨' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars),
            s₂.cursor.pos.col⟩ := by
        have h_eq_chars : ' ' :: ((L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) =
            ' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerStateIx.inFlow
        exact decide_eq_true (by rw [h_fl₂, h_fl₁]; exact h_fl)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerStateIx.currentIndent; rw [h_ids₂]; exact h_indent₁
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃,
              _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃⟩ :=
        scanNextTokenIx_preprocess_flow_ws1 s₂ c_v
          (rest_v ++ [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₂_ws h_s2_flow h_nws_v h_nlb_v h_nc_v h_s2_indent
      have h_corr₃' : ScannerSurfCorrIx s₃
          ⟨(L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars,
            s₃.cursor.pos.col⟩ := by
        have : c_v :: (rest_v ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) =
            (L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars := by
          rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        rwa [this] at h_corr₃
      -- Step 4: scan value via EmitScansInFlowIx
      have h_ev : EmitScansInFlowIx (input := input) p.2 := h_all_v p (.head _)
      have h_corr₃_assoc : ScannerSurfCorrIx s₃
          ⟨(L4YAML.Emit.emit p.2).toList ++ ([',', ' '] ++
            (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₃.cursor.pos.col⟩ := by
        simp only [List.append_assoc] at h_corr₃' ⊢; exact h_corr₃'
      obtain ⟨n_v, s_v, h_chain_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v,
              h_ek_v, h_col_v, h_flow_v, h_indent_v, _h_line_v, _ska_v, h_last_v, h_atol_v,
              h_endline_v, h_stack_v, h_fmc_v⟩ :=
        h_ev s₃
          ([',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₃_assoc
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂])
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_dp₃, h_dp₂, h_dp₁]; exact h_dp)
      have h_snt_eq_v : scanNextTokenIx s₂ = scanNextTokenIx s₃ :=
        scanNextTokenIx_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n_v_pos : n_v ≥ 1 := by
        match n_v, h_chain_v with
        | 0, .zero =>
          exfalso
          have h_chars_eq :=
            CouplingBridge.CharsFromOffset_unique h_corr₃'.chars_from h_corr_v.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (L4YAML.Emit.emit p.2).toList = [] := by
            match h_list : (L4YAML.Emit.emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
      have h_filt_le_v :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≤
          (s₃.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws_v : ScanChainGrewIx (fun t => t.token != .placeholder)
            s₂ (n_v' + 1) s_v :=
        ScanChainGrewIx_of_scanNextTokenIx_eq h_snt_eq_v h_filt_le_v h_chain_v
      have h_grew₂ :
          (s₂.tokens.tokens.filter (fun t => t.token != .placeholder)).size >
          (s₁.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorrIx s₁
            ⟨':' :: (' ' :: (L4YAML.Emit.emit p.2).toList ++ [',', ' '] ++
              (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars),
              s₁.cursor.pos.col⟩ := by
          have : [':', ' '] ++ (L4YAML.Emit.emit p.2).toList ++ [',', ' '] ++
              (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ':' :: (' ' :: (L4YAML.Emit.emit p.2).toList ++ [',', ' '] ++
              (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextTokenIx_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (L4YAML.Emit.emit p.2).toList ++ [',', ' '] ++
              (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- Step 6: scan ',' via scanNextTokenIx_flow_comma
      obtain ⟨s_c, h_snt_c, h_corr_c, h_fl_c, h_dp_c, h_ids_c, h_ek_c, h_col_c, _h_line_c,
              h_atol_c, h_endline_c, h_stack_c⟩ :=
        scanNextTokenIx_flow_comma s_v
          (' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_atol_v h_endline_v
          (by rw [h_dp_v, h_dp₃, h_dp₂, h_dp₁]; exact h_dp)
      -- Step 7: handle the leading space before the next pair
      obtain ⟨c_p, rest_p, h_first_p, h_nws_p, h_nlb_p, h_nc_p⟩ :=
        emitPairList_first_charIx p' ps
      have h_corr_c_ws : ScannerSurfCorrIx s_c
          ⟨' ' :: c_p :: (rest_p ++ rest_chars), s_c.cursor.pos.col⟩ := by
        have : ' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars =
            ' ' :: c_p :: (rest_p ++ rest_chars) := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_c
      have h_sc_flow : s_c.inFlow = true := by
        unfold ScannerStateIx.inFlow
        exact decide_eq_true (by rw [h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
      have h_sc_indent : s_c.currentIndent < 0 := by
        unfold ScannerStateIx.currentIndent; rw [h_ids_c]; exact h_indent_v
      obtain ⟨s_pp, h_corr_pp, h_flow_pp, h_fl_pp, h_indent_pp, h_col_pp, h_dp_pp, h_ids_pp,
              h_ek_pp, _h_line_pp, h_pp_eq_r, h_atol_transfer_pp, h_endline_transfer_pp,
              h_stack_pp, h_toks_pp⟩ :=
        scanNextTokenIx_preprocess_flow_ws1 s_c c_p (rest_p ++ rest_chars) h_corr_c_ws
          h_sc_flow h_nws_p h_nlb_p h_nc_p h_sc_indent
      have h_corr_pp' : ScannerSurfCorrIx s_pp
          ⟨(L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars, s_pp.cursor.pos.col⟩ := by
        have : c_p :: (rest_p ++ rest_chars) =
            (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_pp
      -- Step 8: recursive scan of emitPairList (p' :: ps) via STRONG IH
      have h_tail_all_k : ∀ q ∈ p' :: ps, EmitScansInFlowIx (input := input) q.1 :=
        fun q hq => h_all_k q (.tail _ hq)
      have h_tail_all_v : ∀ q ∈ p' :: ps, EmitScansInFlowIx (input := input) q.2 :=
        fun q hq => h_all_v q (.tail _ hq)
      have h_ih_list : EmitPairListScansInFlowIx_strong (input := input) (p' :: ps) :=
        ih (by simp) h_tail_all_k h_tail_all_v
      obtain ⟨n_r, s_end, h_chain_r, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end,
              h_endline_end, h_stack_end, h_fmc_r, _h_n_r_ge_3⟩ :=
        h_ih_list s_pp rest_chars h_corr_pp'
          h_flow_pp
          (by rw [h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent_pp]; exact h_sc_indent)
          (by rw [h_col_pp]; omega)
          (by rw [h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂])
          (h_atol_transfer_pp h_atol_c)
          (h_endline_transfer_pp h_endline_c)
          (by rw [h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁]; exact h_dp)
      have h_snt_eq_r : scanNextTokenIx s_c = scanNextTokenIx s_pp :=
        scanNextTokenIx_eq_of_preprocess s_c s_pp h_pp_eq_r
      have h_n_r_pos : n_r ≥ 1 := by
        match n_r, h_chain_r with
        | 0, .zero =>
          exfalso
          have h_chars_eq :=
            CouplingBridge.CharsFromOffset_unique h_corr_pp'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList = [] := by
            match h_list : (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emitPairList_first_charIx p' ps
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_r', rfl⟩ : ∃ k, n_r = k + 1 := ⟨n_r - 1, by omega⟩
      have h_filt_le_r :
          (s_c.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≤
          (s_pp.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        rw [h_toks_pp]; exact Nat.le_refl _
      have h_chain_ws_r : ScanChainGrewIx (fun t => t.token != .placeholder)
            s_c (n_r' + 1) s_end :=
        ScanChainGrewIx_of_scanNextTokenIx_eq h_snt_eq_r h_filt_le_r h_chain_r
      have h_grew_c :
          (s_c.tokens.tokens.filter (fun t => t.token != .placeholder)).size >
          (s_v.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
        have h_corr_v_cons : ScannerSurfCorrIx s_v
            ⟨',' :: (' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars),
              s_v.cursor.pos.col⟩ := by
          have : [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ',' :: (' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr_v
        exact scanNextTokenIx_filtered_grows_in_flow s_v s_c ','
          (' ' :: (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v_cons h_flow_v h_indent_v h_col_v
          (by decide) (by decide) (by decide) h_snt_c
      have h_fmc_v' : FlowMonoChainIx s.flowLevel s₃ (n_v' + 1) s_v :=
        (show s.flowLevel = s₃.flowLevel from by rw [h_fl₃, h_fl₂, h_fl₁]) ▸ h_fmc_v
      have h_fmc_ws_v : FlowMonoChainIx s.flowLevel s₂ (n_v' + 1) s_v :=
        FlowMonoChainIx_of_scanNextTokenIx_eq h_snt_eq_v (by omega) h_fmc_v'
      have h_fmc_r' : FlowMonoChainIx s.flowLevel s_pp (n_r' + 1) s_end :=
        (show s.flowLevel = s_pp.flowLevel from by
          rw [h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]) ▸ h_fmc_r
      have h_fmc_ws_r : FlowMonoChainIx s.flowLevel s_c (n_r' + 1) s_end :=
        FlowMonoChainIx_of_scanNextTokenIx_eq h_snt_eq_r (by omega) h_fmc_r'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChainIx.single h_snt₂ (by omega) (by omega)).trans
          (h_fmc_ws_v.trans
            ((FlowMonoChainIx.single h_snt_c (by omega) (by omega)).trans h_fmc_ws_r)))
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrewIx.single h_snt₂ h_grew₂).trans
          (h_chain_ws_v.trans
            ((ScanChainGrewIx.single h_snt_c h_grew_c).trans h_chain_ws_r)))
      have h_arith : n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) =
          n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1) := by omega
      -- NEW: n ≥ 3 from n₁ ≥ 1 (via h_n_v_pos / h_n_r_pos similar) + arithmetic.
      have h_n_ge_3 : n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1) ≥ 3 := by omega
      refine ⟨n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1), s_end,
        h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_,
        h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, h_n_ge_3⟩
      · rw [h_fl_end, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids_pp, h_ids_c, h_ids_v, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line_pp, _h_line_c, _h_line_v, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁]

/-! ## §3  `scanValuePrepareIx_flow_pointwise` — `idx + 1` overwrite

Per Reflection 153 discovery: in flow context (`s.inFlow = true`), the
`s.simpleKey.possible = true` branch of `scanValuePrepareIx` overwrites
position `s.simpleKey.tokenIndex + 1` (NOT `s.simpleKey.tokenIndex`)
with `.key`, leaving every other position untouched and the array
size unchanged.

Direct consumer enabler for `.tokenshape.pair`'s sorry 9644 (first new
filtered token is `.key`): combined with the `saveSimpleKey` placeholder
shape at positions `m₀` and `m₀ + 1`, this lemma identifies the position
that becomes `.key`.

The non-flow branch (`!s.inFlow`) additionally writes
`.blockMappingStart` at `idx` and updates `indents`; we don't
characterize that branch here since `.tokenshape.{list,pair}` are flow-
only consumers. -/

/-- Token-array shape of `scanValuePrepareIx` in flow context: equals
    the original tokens with a single `setIfInBounds` at position
    `tokenIndex + 1` writing a `.key`-shaped token. -/
lemma scanValuePrepareIx_flow_tokens_eq (s : ScannerStateIx input)
    (h_sk : s.simpleKey.possible = true)
    (h_flow : s.inFlow = true) :
    (scanValuePrepareIx s).tokens.tokens =
      s.tokens.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1)
        (Indexed.IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.key
          s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound) := by
  unfold scanValuePrepareIx
  simp only [h_sk, h_flow, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [overwriteAtCursor_tokens_tokens]

/-- `scanValuePrepareIx` in flow context preserves total token array
    size (overwriteAtCursor uses `setIfInBounds`, which is size-stable). -/
lemma scanValuePrepareIx_flow_size_eq (s : ScannerStateIx input)
    (h_sk : s.simpleKey.possible = true)
    (h_flow : s.inFlow = true) :
    (scanValuePrepareIx s).tokens.tokens.size = s.tokens.tokens.size := by
  rw [scanValuePrepareIx_flow_tokens_eq s h_sk h_flow, Array.size_setIfInBounds]

/-- Pointwise effect of `scanValuePrepareIx` in flow context with
    `simpleKey.possible = true`: position `idx + 1` becomes `.key`,
    every other position is preserved. Bundles together with
    `scanValuePrepareIx_flow_size_eq` (the size statement) and
    `scanValuePrepareIx_flow_tokens_eq` (the underlying setIfInBounds
    equation). -/
lemma scanValuePrepareIx_flow_pointwise (s : ScannerStateIx input)
    (h_sk : s.simpleKey.possible = true)
    (h_flow : s.inFlow = true) :
    -- (key) IF position `idx + 1` is in range, the new token there is `.key`.
    (∀ (h_lt : s.simpleKey.tokenIndex + 1 < s.tokens.tokens.size),
      ((scanValuePrepareIx s).tokens.tokens[s.simpleKey.tokenIndex + 1]'(by
        rw [scanValuePrepareIx_flow_size_eq s h_sk h_flow]; exact h_lt)).token =
        YamlToken.key) ∧
    -- (rest) all positions `i ≠ idx + 1` are preserved.
    (∀ (i : Nat) (hi : i < s.tokens.tokens.size) (_h_ne : i ≠ s.simpleKey.tokenIndex + 1),
      ((scanValuePrepareIx s).tokens.tokens[i]'(by
        rw [scanValuePrepareIx_flow_size_eq s h_sk h_flow]; exact hi)) =
        s.tokens.tokens[i]'hi) := by
  -- The h_ne hypothesis appears unused inside the bound proof of the second
  -- conjunct's signature but IS used in the proof body via the
  -- Array.getElem_setIfInBounds_ne call (see refine_2 branch).
  -- Mark the signature-level scope unused via `set_option` if linter complains.
  have h_unfold := scanValuePrepareIx_flow_tokens_eq s h_sk h_flow
  refine ⟨?_, ?_⟩
  · -- position idx+1 = .key.
    intro h_lt
    -- Rewrite both the bound and the term through h_unfold.
    have h_lt_set : s.simpleKey.tokenIndex + 1 < (s.tokens.tokens.setIfInBounds
        (s.simpleKey.tokenIndex + 1)
        (Indexed.IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.key
          s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound)).size := by
      rw [Array.size_setIfInBounds]; exact h_lt
    have h_eq : (scanValuePrepareIx s).tokens.tokens[s.simpleKey.tokenIndex + 1]'(by
        rw [scanValuePrepareIx_flow_size_eq s h_sk h_flow]; exact h_lt) =
      (s.tokens.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1)
        (Indexed.IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.key
          s.simpleKey.cursor.pos (Nat.le_refl _)
          s.simpleKey.cursor.posBound))[s.simpleKey.tokenIndex + 1]'h_lt_set := by
      congr 1
    rw [h_eq, Array.getElem_setIfInBounds_self]
    rfl
  · -- other positions preserved.
    intro i hi h_ne
    have h_lt_set : i < (s.tokens.tokens.setIfInBounds
        (s.simpleKey.tokenIndex + 1)
        (Indexed.IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.key
          s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound)).size := by
      rw [Array.size_setIfInBounds]; exact hi
    have h_eq : (scanValuePrepareIx s).tokens.tokens[i]'(by
        rw [scanValuePrepareIx_flow_size_eq s h_sk h_flow]; exact hi) =
      (s.tokens.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1)
        (Indexed.IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.key
          s.simpleKey.cursor.pos (Nat.le_refl _)
          s.simpleKey.cursor.posBound))[i]'h_lt_set := by
      congr 1
    rw [h_eq, Array.getElem_setIfInBounds_ne hi (fun h => h_ne h.symm)]

/-! ## §4  `FlowMonoChainIx_filtered_prefix_no_overwrite` — floor-parameterized

Generalization of `FlowMonoChainIx_filtered_prefix` (in
`RoundTrip.lean §5.4.G.5.3`): takes `SimpleKeyAboveFloorIx` as input
directly rather than constructing it from `s.simpleKey.possible =
false`. This admits the case where the chain starts in a state with
a pending simple key, provided the consumer-chosen floor `n₀ ≤
s.simpleKey.tokenIndex`.

Reflection 153 motivation: `scanFlowEntryIx` does NOT clear
`simpleKey.possible` — the prior `FlowMonoChainIx_filtered_prefix` is
unusable directly when the chain enters via a `,` after a pending
key. With this floor-parameterized variant, the consumer can pick
`n₀ = old_tokens_size` (or `n₀ = s.simpleKey.tokenIndex`, etc.) and
discharge SKAF appropriately for that floor.

Proof: reduces to `FlowMonoChainIx_preserves_raw_prefix` (`Sync/
Invariant.lean §4`) for per-position raw preservation, then lifts to
filtered-prefix preservation via `Array_filter_prefix_of_raw_prefix`
applied to `s.tokens.tokens.take n₀` and `s'.tokens.tokens`. -/

/-- Raw-prefix preservation through `FlowMonoChainIx`,
    floor-parameterized: instead of requiring `s.simpleKey.possible =
    false` (as in `FlowMonoChainIx_filtered_prefix` of `RoundTrip.lean
    §5.4.G.5.3`), takes the `SimpleKeyAboveFloorIx s n₀ fl₀` invariant
    directly. This admits the case where the chain starts in a state
    with a pending simple key, provided the consumer-chosen floor `n₀
    ≤ s.simpleKey.tokenIndex`.

    Per-position raw form: for every `i < n₀`, the token at position
    `i` in `s'` equals the token at position `i` in `s`. Effectively a
    semantic re-naming of `FlowMonoChainIx_preserves_raw_prefix`
    (`Sync/Invariant.lean §4`) emphasizing the "no-overwrite" reading.
    Consumers lift to filtered-prefix via `Array_filter_prefix_of_raw_prefix`. -/
lemma FlowMonoChainIx_filtered_prefix_no_overwrite
    {s s' : ScannerStateIx input} {n fl₀ n₀ : Nat}
    (h_fmc : FlowMonoChainIx fl₀ s n s')
    (h_n₀_le : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloorIx s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (i : Nat) (hi : i < n₀) :
    ∃ (h_size : i < s'.tokens.size),
      s'.tokens[i]'h_size = s.tokens[i]'(Nat.lt_of_lt_of_le hi h_n₀_le) :=
  FlowMonoChainIx_preserves_raw_prefix h_fmc n₀ h_n₀_le h_inv h_sync i hi

/-- Filtered-list-prefix companion of `FlowMonoChainIx_filtered_prefix_no_overwrite`:
    if the raw prefix of length `n₀` is preserved (per the per-position
    wrapper above), the filtered token list at `s'` extends the
    filtered list of the first `n₀` raw tokens at `s`. -/
lemma FlowMonoChainIx_filtered_prefix_no_overwrite_list
    {s s' : ScannerStateIx input} {n fl₀ n₀ : Nat}
    (h_fmc : FlowMonoChainIx fl₀ s n s')
    (h_n₀_le : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloorIx s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel) :
    let p := fun (t : Indexed.IxToken input) => t.token != YamlToken.placeholder
    ∃ suffix, (s'.tokens.tokens.filter p).toList =
              ((s.tokens.tokens.toList.take n₀).filter p) ++ suffix := by
  intro p
  -- Raw preservation for i < n₀.
  have h_size_le : n₀ ≤ s'.tokens.tokens.size := by
    have h_mono : s.tokens.size ≤ s'.tokens.size := FlowMonoChainIx.tokens_mono h_fmc
    have h_eq_s : s.tokens.tokens.size = s.tokens.size := rfl
    have h_eq_s' : s'.tokens.tokens.size = s'.tokens.size := rfl
    omega
  have h_pres : ∀ i (hi : i < n₀),
      s'.tokens.tokens[i]'(Nat.lt_of_lt_of_le hi h_size_le) =
        s.tokens.tokens[i]'(by
          have h_eq : s.tokens.tokens.size = s.tokens.size := rfl
          rw [h_eq]; exact Nat.lt_of_lt_of_le hi h_n₀_le) := by
    intro i hi
    obtain ⟨_, h_eq⟩ := FlowMonoChainIx_preserves_raw_prefix h_fmc n₀ h_n₀_le h_inv h_sync i hi
    exact h_eq
  -- Convert to list-level: s'.tokens.tokens.toList agrees with s.tokens.tokens.toList on the
  -- first n₀ positions. Construct the split.
  have h_take : s'.tokens.tokens.toList.take n₀ = s.tokens.tokens.toList.take n₀ := by
    apply List.ext_getElem
    · simp only [List.length_take, Array.length_toList]
      have h1 : n₀ ≤ s.tokens.tokens.size := by
        show n₀ ≤ s.tokens.size; exact h_n₀_le
      have h2 : n₀ ≤ s'.tokens.tokens.size := h_size_le
      omega
    · intro k hk₁ hk₂
      simp only [List.getElem_take, Array.getElem_toList] at hk₁ hk₂ ⊢
      have h_k_lt_n₀ : k < n₀ := by
        rw [List.length_take] at hk₁
        omega
      exact h_pres k h_k_lt_n₀
  -- Now split s'.tokens.tokens.toList = take n₀ ++ drop n₀, filter both sides.
  have h_split : s'.tokens.tokens.toList =
      s'.tokens.tokens.toList.take n₀ ++ s'.tokens.tokens.toList.drop n₀ := by
    rw [List.take_append_drop]
  rw [Array.toList_filter, h_split, List.filter_append, h_take]
  exact ⟨(s'.tokens.tokens.toList.drop n₀).filter p, rfl⟩

/-! ## §5  `NoOverwriteAtIx` — pointwise position preservation
    (Reflection 155, `.substrate.c`)

Per Reflection 155, the consumer scenario for `.tokenshape.list`
(chain starts in a state with `s.simpleKeyAllowed = true`) has
`saveSimpleKey` activate at step 1, pushing 2 placeholders + creating
a simpleKey at `tokenIndex = m₀ = original s.tokens.size`. The first
new filtered token (flowSequenceStart) lands at raw position
`m_first = m₀ + 2`, ABOVE the simpleKey reservation. SKAF cannot be
discharged at any floor ≥ m₀ + 1 (the new entry's tokenIndex < n₀),
so substrate.b's `_filtered_prefix_no_overwrite_list` only covers raw
positions strictly below `m_first`.

This section ships the parallel infrastructure for **per-position
no-overwrite preservation**: an invariant `NoOverwriteAtIx s m` that
quantifies over ALL simpleKey-related state (current + stack) and
asserts no future promotion writes can land on position `m`, plus
maintenance lemmas through `scanNextTokenIx`, plus chain-induction.

Hypothesis form: `simpleKey.possible = true → m ≠ tokenIndex ∧ m ≠
tokenIndex + 1` (and analogously for every stack entry). This rules
out promotion-overwrite at position `m`, the ONLY way `tokens[m]`
could be overwritten through a `scanNextTokenIx` step (`scanValueIx`
via `scanValuePrepareIx` writes at `tokenIndex` and `tokenIndex + 1`
of the current simpleKey).

Strategically parallel to `SimpleKeyAboveFloorIx` (`FlowMonoChain/
Basic.lean §2`) but with `≠ m` instead of `≥ n`. Differs in not
requiring sync hypothesis (no floor → no stack-size lower bound
needed for the flow-close case). -/

/-- `NoOverwriteAtIx s m`: position `m` cannot be overwritten by any
    future simpleKey promotion (current or stacked). -/
def NoOverwriteAtIx (s : ScannerStateIx input) (m : Nat) : Prop :=
  (s.simpleKey.possible = true →
    m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) ∧
  (∀ (j : Nat) (h : j < s.simpleKeyStack.size),
    s.simpleKeyStack[j].possible = true →
    m ≠ s.simpleKeyStack[j].tokenIndex ∧ m ≠ s.simpleKeyStack[j].tokenIndex + 1)

/-! ### §5.1  NoOverwriteAtIx constructors -/

/-- If `s_out` clears the simple key and preserves the stack, then
    `NoOverwriteAtIx` transports. Parallel to
    `SimpleKeyAboveFloorIx_of_cleared_preserved` (`FlowMonoChain/
    Basic.lean §2.1`). -/
lemma NoOverwriteAtIx_of_cleared_preserved
    (s_out s_in : ScannerStateIx input) (m : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : NoOverwriteAtIx s_in m) :
    NoOverwriteAtIx s_out m :=
  ⟨fun hp => absurd hp (by rw [h_sk]; decide),
   fun j hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp⟩

/-- If `s_out` preserves both `simpleKey` and `simpleKeyStack`, then
    `NoOverwriteAtIx` transports. Parallel to
    `SimpleKeyAboveFloorIx_of_preserved`. -/
lemma NoOverwriteAtIx_of_preserved
    (s_out s_in : ScannerStateIx input) (m : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKey)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : NoOverwriteAtIx s_in m) :
    NoOverwriteAtIx s_out m :=
  ⟨fun hp => by rw [h_sk] at hp ⊢; exact h_inv.1 hp,
   fun j hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp⟩

/-- Flow-open transport: `s_out` clears the current simple key and
    pushes the old `simpleKey` onto `simpleKeyStack`. Parallel to
    `SimpleKeyAboveFloorIx_of_flow_open`. -/
lemma NoOverwriteAtIx_of_flow_open
    (s_out s_in : ScannerStateIx input) (m : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.push s_in.simpleKey)
    (h_inv : NoOverwriteAtIx s_in m) :
    NoOverwriteAtIx s_out m := by
  refine ⟨fun hp => absurd hp (by rw [h_sk]; decide), fun j hj hp => ?_⟩
  simp only [h_stack, Array.size_push] at hj
  by_cases hlt : j < s_in.simpleKeyStack.size
  · have hp' : s_in.simpleKeyStack[j].possible = true := by
      simp only [h_stack, Array.getElem_push, dif_pos hlt] at hp; exact hp
    have h_orig := h_inv.2 j hlt hp'
    show m ≠ s_out.simpleKeyStack[j].tokenIndex ∧
         m ≠ s_out.simpleKeyStack[j].tokenIndex + 1
    simp only [h_stack, Array.getElem_push, dif_pos hlt]; exact h_orig
  · have hj_eq : j = s_in.simpleKeyStack.size := by omega
    subst hj_eq
    have hp' : s_in.simpleKey.possible = true := by
      simp only [h_stack, Array.getElem_push, dif_neg hlt] at hp; exact hp
    have h_orig := h_inv.1 hp'
    show m ≠ s_out.simpleKeyStack[s_in.simpleKeyStack.size].tokenIndex ∧
         m ≠ s_out.simpleKeyStack[s_in.simpleKeyStack.size].tokenIndex + 1
    simp only [h_stack, Array.getElem_push, dif_neg hlt]; exact h_orig

/-- Flow-close transport: `s_out` restores `simpleKey` from
    `simpleKeyStack.back?` and pops the stack. Parallel to
    `SimpleKeyAboveFloorIx_of_flow_close` but with no sync hypothesis
    (NoOverwriteAt's stack-entry conjunct covers ALL slots, so popping
    just reduces the universe of obligations). -/
lemma NoOverwriteAtIx_of_flow_close
    (s_out s_in : ScannerStateIx input) (m : Nat)
    (h_sk : s_out.simpleKey =
      s_in.simpleKeyStack.back?.getD { cursor := IxCursor.start input })
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.pop)
    (h_inv : NoOverwriteAtIx s_in m) :
    NoOverwriteAtIx s_out m := by
  refine ⟨fun hp => ?_, fun j hj hp => ?_⟩
  · by_cases h_nonempty : s_in.simpleKeyStack.size > 0
    · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
      have h_back : s_in.simpleKeyStack.back?.getD { cursor := IxCursor.start input } =
          s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
        simp [Array.back?, h_lt]
      rw [h_sk, h_back] at hp ⊢
      exact h_inv.2 _ h_lt hp
    · have h_empty : s_in.simpleKeyStack.size = 0 := by omega
      have h_none : s_in.simpleKeyStack.back? = none := by simp [Array.back?, h_empty]
      rw [h_sk, h_none] at hp; simp at hp
  · simp only [h_stack, Array.size_pop] at hj
    simp only [h_stack, Array.getElem_pop] at hp ⊢
    exact h_inv.2 j (by omega) hp

/-! ### §5.2  saveSimpleKey + preprocess pointwise maintenance -/

/-- `saveSimpleKeyIx` maintains the pointwise no-overwrite invariant
    on `simpleKey`: if the new simpleKey is possible, its `tokenIndex`
    is either unchanged (no-op branch) or set to `st.tokens.size`
    (set branch), and both ≠ m / ≠ m given `m < st.tokens.size`.
    Parallel to `saveSimpleKeyIx_simpleKey_inv` (`FlowMonoChain/
    Basic.lean §2.2`) but with the `≠m` hypothesis form. -/
lemma saveSimpleKeyIx_simpleKey_pointwise_inv {input : String}
    (st : ScannerStateIx input) (m : Nat) (h_tok : m < st.tokens.size)
    (h_inv : st.simpleKey.possible = true →
      m ≠ st.simpleKey.tokenIndex ∧ m ≠ st.simpleKey.tokenIndex + 1) :
    (saveSimpleKeyIx st).simpleKey.possible = true →
    m ≠ (saveSimpleKeyIx st).simpleKey.tokenIndex ∧
    m ≠ (saveSimpleKeyIx st).simpleKey.tokenIndex + 1 := by
  unfold saveSimpleKeyIx
  split
  · exact h_inv
  · split
    · intro _; dsimp only []; exact ⟨by omega, by omega⟩
    · exact h_inv

/-- `scanNextTokenIx_preprocess` carries the simpleKey pointwise
    invariant. Parallel to `scanNextTokenIx_preprocess_simpleKey_inv`
    (`FlowMonoChain/Basic.lean §2.2`). -/
lemma scanNextTokenIx_preprocess_simpleKey_pointwise_inv {input : String}
    (s s1 : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_preprocess s = .ok (some (s1, c))) (m : Nat)
    (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) :
    s1.simpleKey.possible = true →
    m ≠ s1.simpleKey.tokenIndex ∧ m ≠ s1.simpleKey.tokenIndex + 1 := by
  intro h_poss
  unfold scanNextTokenIx_preprocess at h
  dsimp only at h
  have h_sk_skip : s.skipToContentS.simpleKey = s.simpleKey :=
    skipToContentS_preserves_simpleKey s
  have h_tok_skip : s.skipToContentS.tokens.size = s.tokens.size := by
    rw [skipToContentS_tokens]
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have h_unwind_sz :=
            unwindIndentsIx_tokens_size_le s.skipToContentS s.skipToContentS.cursor.pos.col
          have h_unwind_sk :=
            unwindIndentsIx_preserves_simpleKey s.skipToContentS s.skipToContentS.cursor.pos.col
          have h_tok_post : m <
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                  with needIndentCheck := false } : ScannerStateIx input).tokens.size := by
            show m < (unwindIndentsIx s.skipToContentS _).tokens.size; omega
          have h_sk_post :
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                  with needIndentCheck := false } : ScannerStateIx input).simpleKey.possible
                = true →
              m ≠ ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                      with needIndentCheck := false } : ScannerStateIx input).simpleKey.tokenIndex ∧
              m ≠ ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col
                      with needIndentCheck := false } : ScannerStateIx input).simpleKey.tokenIndex
                + 1 := by
            show (unwindIndentsIx s.skipToContentS _).simpleKey.possible = true → _
            rw [h_unwind_sk, h_sk_skip]; exact h_inv
          exact saveSimpleKeyIx_simpleKey_pointwise_inv _ m h_tok_post h_sk_post h_poss
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have h_tok_post : m < s.skipToContentS.tokens.size := by omega
          have h_sk_post : s.skipToContentS.simpleKey.possible = true →
              m ≠ s.skipToContentS.simpleKey.tokenIndex ∧
              m ≠ s.skipToContentS.simpleKey.tokenIndex + 1 := by
            rw [h_sk_skip]; exact h_inv
          exact saveSimpleKeyIx_simpleKey_pointwise_inv s.skipToContentS m h_tok_post h_sk_post h_poss

/-- `scanNextTokenIx_preprocess` maintains the full `NoOverwriteAtIx`
    invariant. Parallel to `scanNextTokenIx_preprocess_maintains_SKAFIx`. -/
lemma scanNextTokenIx_preprocess_maintains_NoOverwriteAtIx {input : String}
    (s s1 : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_preprocess s = .ok (some (s1, c)))
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : NoOverwriteAtIx s m) :
    NoOverwriteAtIx s1 m := by
  refine ⟨?_, ?_⟩
  · exact scanNextTokenIx_preprocess_simpleKey_pointwise_inv s s1 c h m h_m h_inv.1
  · intro j hj hp
    have h_stack := scanNextTokenIx_preprocess_preserves_simpleKeyStack s s1 c h
    simp only [h_stack] at hj hp ⊢
    exact h_inv.2 j hj hp

/-! ### §5.3  Dispatcher maintenance for NoOverwriteAtIx -/

/-- `scanNextTokenIx_dispatchStructural` maintains `NoOverwriteAtIx`.
    Parallel to `scanNextTokenIx_dispatchStructural_maintains_SKAFIx`. -/
lemma scanNextTokenIx_dispatchStructural_maintains_NoOverwriteAtIx {input : String}
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s'))
    (m : Nat) (_h_m : m < s.tokens.size)
    (h_inv : NoOverwriteAtIx s m) :
    NoOverwriteAtIx s' m := by
  unfold scanNextTokenIx_dispatchStructural at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact NoOverwriteAtIx_of_cleared_preserved _ s m
        (scanDocumentStartIx_clears_simpleKey s)
        (scanDocumentStartIx_preserves_simpleKeyStack s) h_inv
    | (rename_i h_eq; exact NoOverwriteAtIx_of_cleared_preserved _ s m
        (scanDocumentEndIx_clears_simpleKey s _ h_eq)
        (scanDocumentEndIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact NoOverwriteAtIx_of_preserved _ s m
        (scanDirectiveIx_preserves_simpleKey s _ h_eq)
        (scanDirectiveIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanNextTokenIx_dispatchFlowIndicators` maintains `NoOverwriteAtIx`.
    Parallel to `scanNextTokenIx_dispatchFlowIndicators_maintains_SKAFIx`. -/
lemma scanNextTokenIx_dispatchFlowIndicators_maintains_NoOverwriteAtIx {input : String}
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s'))
    (m : Nat) (_h_m : m < s.tokens.size)
    (h_inv : NoOverwriteAtIx s m) :
    NoOverwriteAtIx s' m := by
  unfold scanNextTokenIx_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact NoOverwriteAtIx_of_flow_open _ s m
        (scanFlowSequenceStartIx_simpleKey_cleared s)
        (scanFlowSequenceStartIx_stack_pushed s) h_inv
    | exact NoOverwriteAtIx_of_flow_open _ s m
        (scanFlowMappingStartIx_simpleKey_cleared s)
        (scanFlowMappingStartIx_stack_pushed s) h_inv
    | exact NoOverwriteAtIx_of_flow_close _ s m
        (scanFlowSequenceEndIx_simpleKey_restored s)
        (scanFlowSequenceEndIx_stack_popped s) h_inv
    | exact NoOverwriteAtIx_of_flow_close _ s m
        (scanFlowMappingEndIx_simpleKey_restored s)
        (scanFlowMappingEndIx_stack_popped s) h_inv
    | (rename_i h_eq; exact NoOverwriteAtIx_of_preserved _ s m
        (scanFlowEntryIx_preserves_simpleKey s _ h_eq)
        (scanFlowEntryIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanNextTokenIx_dispatchBlockIndicators` maintains `NoOverwriteAtIx`.
    Parallel to `scanNextTokenIx_dispatchBlockIndicators_maintains_SKAFIx`. -/
lemma scanNextTokenIx_dispatchBlockIndicators_maintains_NoOverwriteAtIx {input : String}
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s'))
    (m : Nat) (_h_m : m < s.tokens.size)
    (h_inv : NoOverwriteAtIx s m) :
    NoOverwriteAtIx s' m := by
  unfold scanNextTokenIx_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact NoOverwriteAtIx_of_preserved _ s m
        (scanBlockEntryIx_preserves_simpleKey s _ h_eq)
        (scanBlockEntryIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact NoOverwriteAtIx_of_cleared_preserved _ s m
        (scanKeyIx_clears_simpleKey s _ h_eq)
        (scanKeyIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact NoOverwriteAtIx_of_cleared_preserved _ s m
        (scanValueIx_clears_simpleKey s _ h_eq)
        (scanValueIx_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanNextTokenIx_dispatchContent` maintains `NoOverwriteAtIx`.
    Parallel to `scanNextTokenIx_dispatchContent_maintains_SKAFIx`. -/
lemma scanNextTokenIx_dispatchContent_maintains_NoOverwriteAtIx {input : String}
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchContent s c = .ok s')
    (m : Nat) (_h_m : m < s.tokens.size)
    (h_inv : NoOverwriteAtIx s m) :
    NoOverwriteAtIx s' m := by
  -- Peel the 7-way content dispatch one `if` at a time with `by_cases`/`rw` (splitting the whole
  -- dispatch at once exceeds the internal simp step budget under Lean 4.31.0); anchor/alias/tag use
  -- the explicit `_preserves_simpleKey`/`_preserves_simpleKeyStack` lemmas, the scalar branches
  -- (block/quoted/plain) are cursor-only updates so SK / stack are preserved structurally (`rfl`).
  unfold scanNextTokenIx_dispatchContent at h
  by_cases hg1 : (c == '&') = true
  · -- '&' anchor
    rw [if_pos hg1] at h
    try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h; cases h
    | ok v =>
      rw [hA] at h
      simp only [Except.ok.injEq] at h; subst h
      exact NoOverwriteAtIx_of_preserved _ s m
        (scanAnchorOrAliasIx_preserves_simpleKey s true v hA)
        (scanAnchorOrAliasIx_preserves_simpleKeyStack s true v hA) h_inv
  · rw [if_neg hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    by_cases hg2 : (c == '*') = true
    · -- '*' alias
      rw [if_pos hg2] at h
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h; cases h
      | ok v =>
        rw [hA] at h
        simp only [Except.ok.injEq] at h; subst h
        exact NoOverwriteAtIx_of_preserved _ s m
          (scanAnchorOrAliasIx_preserves_simpleKey s false v hA)
          (scanAnchorOrAliasIx_preserves_simpleKeyStack s false v hA) h_inv
    · rw [if_neg hg2] at h
      by_cases hg3 : (c == '!') = true
      · -- '!' tag
        rw [if_pos hg3] at h
        cases hT : scanTagIx s with
        | error e => rw [hT] at h; cases h
        | ok v =>
          rw [hT] at h
          simp only [Except.ok.injEq] at h; subst h
          exact NoOverwriteAtIx_of_preserved _ s m
            (scanTagIx_preserves_simpleKey s v hT)
            (scanTagIx_preserves_simpleKeyStack s v hT) h_inv
      · rw [if_neg hg3] at h
        by_cases hg4 : (c == '|' || c == '>') = true
        · -- block scalar
          rw [if_pos hg4] at h
          split at h
          · simp only [Except.ok.injEq] at h; subst h
            exact NoOverwriteAtIx_of_preserved _ s m rfl rfl h_inv
          · cases h
        · rw [if_neg hg4] at h
          by_cases hg5 : (c == '"') = true
          · -- double-quoted
            rw [if_pos hg5] at h
            split at h
            · simp only [Except.ok.injEq] at h; subst h
              exact NoOverwriteAtIx_of_preserved _ s m rfl rfl h_inv
            · cases h
          · rw [if_neg hg5] at h
            by_cases hg6 : (c == '\'') = true
            · -- single-quoted
              rw [if_pos hg6] at h
              split at h
              · simp only [Except.ok.injEq] at h; subst h
                exact NoOverwriteAtIx_of_preserved _ s m rfl rfl h_inv
              · cases h
            · rw [if_neg hg6] at h
              -- plain scalar (success) vs error: one small inner `if`
              split at h
              · simp only [Except.ok.injEq] at h; subst h
                exact NoOverwriteAtIx_of_preserved _ s m rfl rfl h_inv
              · cases h

/-! ### §5.4  scanNextTokenIx capstone for NoOverwriteAtIx -/

set_option maxHeartbeats 400000 in
/-- Capstone: `scanNextTokenIx` maintains `NoOverwriteAtIx`. Parallel
    to `scanNextTokenIx_maintains_SKAFIx` (`FlowMonoChain.Basic §2.4`)
    but with the pointwise (≠m) invariant — no sync hypothesis needed. -/
lemma scanNextTokenIx_maintains_NoOverwriteAtIx {input : String}
    (s s' : ScannerStateIx input)
    (h_next : scanNextTokenIx s = .ok (some s'))
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : NoOverwriteAtIx s m) :
    NoOverwriteAtIx s' m := by
  have h_allow_sk : ∀ st : ScannerStateIx input,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by intro st; split <;> rfl
  have h_allow_stack : ∀ st : ScannerStateIx input,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKeyStack = st.simpleKeyStack := by intro st; split <;> rfl
  have h_allow_tok : ∀ st : ScannerStateIx input,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := by intro st; split <;> rfl
  unfold scanNextTokenIx at h_next
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp [reduceCtorEq] at h_next
    · rename_i s1 c1 hPre
      have h_pre_inv :=
        scanNextTokenIx_preprocess_maintains_NoOverwriteAtIx s _ _ hPre m h_m h_inv
      have h_pre_mono := scanNextTokenIx_preprocess_tokens_size_le s _ _ hPre
      have h_pre_m : m < s1.tokens.size := Nat.lt_of_lt_of_le h_m h_pre_mono
      split at h_next
      · contradiction
      · split at h_next
        · rename_i s'' hStruct
          simp only [Except.ok.injEq, Option.some.injEq] at h_next
          subst h_next
          exact scanNextTokenIx_dispatchStructural_maintains_NoOverwriteAtIx _ _ _ hStruct
            m h_pre_m h_pre_inv
        · have h_s2_inv : NoOverwriteAtIx
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1) m :=
            NoOverwriteAtIx_of_preserved _ s1 m
              (h_allow_sk s1) (h_allow_stack s1) h_pre_inv
          have h_s2_m : m <
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1).tokens.size := by
            rw [h_allow_tok]; exact h_pre_m
          -- Fix B pending-directives check: error arm contradicts h_next
          split at h_next
          · contradiction
          split at h_next
          · contradiction
          · split at h_next
            · contradiction
            · split at h_next
              · rename_i s'' hFlow
                simp only [Except.ok.injEq, Option.some.injEq] at h_next
                subst h_next
                exact scanNextTokenIx_dispatchFlowIndicators_maintains_NoOverwriteAtIx _ _ _ hFlow
                  m h_s2_m h_s2_inv
              · split at h_next
                · contradiction
                · split at h_next
                  · rename_i s'' hBlock
                    simp only [Except.ok.injEq, Option.some.injEq] at h_next
                    subst h_next
                    exact scanNextTokenIx_dispatchBlockIndicators_maintains_NoOverwriteAtIx _ _ _ hBlock
                      m h_s2_m h_s2_inv
                  · split at h_next
                    · contradiction
                    · rename_i sC hContent
                      simp only [Except.ok.injEq, Option.some.injEq] at h_next
                      subst h_next
                      exact scanNextTokenIx_dispatchContent_maintains_NoOverwriteAtIx _ _ _ hContent
                        m h_s2_m h_s2_inv

/-! ### §5.5  Step-level pointwise preservation -/

/-- Pointwise (≠m) form of `scanValuePrepareIx_preserves_prefix`
    (`IndexedScannerPlainScalarValid §12k`): preserves position `m`
    given the simpleKey hypothesis `m ≠ tokenIndex ∧ m ≠ tokenIndex + 1`.
    Mirrors the prefix-form proof at line 5101 but uses the pointwise
    hypothesis directly (no need to derive `tokenIndex ≠ m` from
    `i < n ≤ tokenIndex`). -/
lemma scanValuePrepareIx_preserves_position_specific {input : String}
    (s : ScannerStateIx input)
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) :
    (scanValuePrepareIx s).tokens[m]'(by
        have := scanValuePrepareIx_tokens_size_le s; omega) =
    s.tokens[m]'h_m := by
  have h_sz : s.tokens.size = s.tokens.tokens.size := rfl
  unfold scanValuePrepareIx
  split
  · rename_i h_poss
    obtain ⟨h_ne_idx, h_ne_idx1⟩ := h_inv h_poss
    split
    · split
      · -- non-flow, col > currentIndent: two overwriteAtCursor at idx, idx+1
        have h_m_lt : m < s.tokens.tokens.size := by omega
        have h_m_lt1 : m < (s.tokens.tokens.setIfInBounds s.simpleKey.tokenIndex
            (IxToken.mk' s.simpleKey.cursor.pos YamlToken.blockMappingStart
              s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound)).size := by
          rw [Array.size_setIfInBounds]; exact h_m_lt
        change (((s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
                YamlToken.blockMappingStart).overwriteAtCursor
              (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor YamlToken.key).tokens)[m]'_ =
          s.tokens[m]'h_m
        change (((s.tokens.tokens.setIfInBounds s.simpleKey.tokenIndex _).setIfInBounds
              (s.simpleKey.tokenIndex + 1) _))[m]'_ = s.tokens.tokens[m]'h_m_lt
        exact (Array.getElem_setIfInBounds_ne h_m_lt1
                (show s.simpleKey.tokenIndex + 1 ≠ m from fun h => h_ne_idx1 h.symm)).trans
              (Array.getElem_setIfInBounds_ne h_m_lt
                (show s.simpleKey.tokenIndex ≠ m from fun h => h_ne_idx h.symm))
      · -- non-flow, col ≤ currentIndent: one overwriteAtCursor at idx+1
        have h_m_lt : m < s.tokens.tokens.size := by omega
        change (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor
                YamlToken.key).tokens[m]'_ = s.tokens[m]'h_m
        change (s.tokens.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1) _)[m]'_ =
          s.tokens.tokens[m]'h_m_lt
        exact Array.getElem_setIfInBounds_ne h_m_lt
              (show s.simpleKey.tokenIndex + 1 ≠ m from fun h => h_ne_idx1 h.symm)
    · -- flow: one overwriteAtCursor at idx+1
      have h_m_lt : m < s.tokens.tokens.size := by omega
      change (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor
              YamlToken.key).tokens[m]'_ = s.tokens[m]'h_m
      change (s.tokens.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1) _)[m]'_ =
        s.tokens.tokens[m]'h_m_lt
      exact Array.getElem_setIfInBounds_ne h_m_lt
            (show s.simpleKey.tokenIndex + 1 ≠ m from fun h => h_ne_idx1 h.symm)
  · split
    · rfl
    · split
      · exact pushMappingIndentIx_preserves_prefix s s.cursor.pos.col m h_m
      · rfl

/-- Pointwise (≠m) form of `scanValueIx_preserves_prefix`. -/
lemma scanValueIx_preserves_position_specific {input : String}
    (s s' : ScannerStateIx input)
    (h_ok : scanValueIx s = .ok s')
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) :
    s'.tokens[m]'(by have := scanValueIx_tokens_size_le h_ok; omega) =
    s.tokens[m]'h_m := by
  unfold scanValueIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · cases h_ok
  · split at h_ok
    · cases h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      have h_ck := scanValueClearKeyIx_tokens s
      have h_inv' : (scanValueClearKeyIx s).simpleKey.possible = true →
          m ≠ (scanValueClearKeyIx s).simpleKey.tokenIndex ∧
          m ≠ (scanValueClearKeyIx s).simpleKey.tokenIndex + 1 := by
        unfold scanValueClearKeyIx
        split
        · split
          · simp
          · split
            · simp
            · exact h_inv
        · exact h_inv
      have h_m' : m < (scanValueClearKeyIx s).tokens.size := by rw [h_ck]; exact h_m
      have h_prep := scanValuePrepareIx_preserves_position_specific (scanValueClearKeyIx s)
        m h_m' h_inv'
      have h_prep_sz := scanValuePrepareIx_tokens_size_le (scanValueClearKeyIx s)
      have h_m_lt_prep : m < (scanValuePrepareIx (scanValueClearKeyIx s)).tokens.size := by
        rw [h_ck] at h_prep_sz; omega
      have h_emit := emit_preserves_tokens_at
        (scanValuePrepareIx (scanValueClearKeyIx s)) YamlToken.value m h_m_lt_prep
      show ((scanValuePrepareIx (scanValueClearKeyIx s)).emit YamlToken.value).tokens[m]'_ =
        s.tokens[m]'h_m
      calc ((scanValuePrepareIx (scanValueClearKeyIx s)).emit YamlToken.value).tokens[m]'_
          = (scanValuePrepareIx (scanValueClearKeyIx s)).tokens[m]'h_m_lt_prep := h_emit
        _ = (scanValueClearKeyIx s).tokens[m]'(by rw [h_ck]; omega) := h_prep
        _ = s.tokens[m]'h_m := by simp

set_option maxHeartbeats 400000 in
/-- Per-step pointwise preservation of position `m` through
    `scanNextTokenIx`. Parallel to `scanNextTokenIx_preserves_prefix_
    of_simpleKey` (`FlowMonoChain/Sync/Invariant.lean §3`) but with
    `m ≠ tokenIndex ∧ m ≠ tokenIndex + 1` hypothesis instead of
    `tokenIndex ≥ n`.

    Per Reflection 155: this is the step-level primitive needed by
    `.tokenshape.list` and `.tokenshape.pair` consumers when the
    protected position sits ABOVE the simpleKey reservation. -/
lemma scanNextTokenIx_preserves_position_specific {input : String}
    (s s' : ScannerStateIx input) (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1)
    (h_ok : scanNextTokenIx s = .ok (some s')) :
    ∃ (h_size : m < s'.tokens.size),
      s'.tokens[m]'h_size = s.tokens[m]'h_m := by
  unfold scanNextTokenIx at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  generalize h_pp : scanNextTokenIx_preprocess s = pp_res at h_ok
  cases pp_res with
  | error e => simp at h_ok
  | ok pp_inner =>
    cases pp_inner with
    | none => simp at h_ok
    | some pair =>
      cases pair with
      | mk s_pp c =>
        have h_inv_pp : s_pp.simpleKey.possible = true →
            m ≠ s_pp.simpleKey.tokenIndex ∧ m ≠ s_pp.simpleKey.tokenIndex + 1 :=
          scanNextTokenIx_preprocess_simpleKey_pointwise_inv s s_pp c h_pp m h_m h_inv
        obtain ⟨h_m_pp, h_pre_eq⟩ :=
          _preprocess_preserves_prefix s s_pp c (m + 1) h_m h_pp m (Nat.lt_succ_self m)
        have h_m_pp_lt : m < s_pp.tokens.size := h_m_pp
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            rcases scanNextTokenIx_dispatchStructural_ok_some_cases h_ds with heq | hOk | hOk
            · subst heq
              have h_pref := scanDocumentStartIx_preserves_prefix s_pp m h_m_pp_lt
              have h_sz : m < (scanDocumentStartIx s_pp).tokens.size := by
                have := scanDocumentStartIx_tokens_size_le s_pp; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
            · have h_pref := scanDocumentEndIx_preserves_prefix s_pp _ hOk m h_m_pp_lt
              have h_sz : m < s_str.tokens.size := by
                have := scanDocumentEndIx_tokens_size_le hOk; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
            · have h_pref := scanDirectiveIx_preserves_prefix s_pp _ hOk m h_m_pp_lt
              have h_sz : m < s_str.tokens.size := by
                have := scanDirectiveIx_tokens_size_le hOk; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_dir_tok : s_dir.tokens = s_pp.tokens := by
              rw [← h_dir_def]; exact _dir_update_tokens s_pp
            have h_m_dir : m < s_dir.tokens.size := by rw [h_dir_tok]; exact h_m_pp_lt
            have h_dir_eq : s_dir.tokens[m]'h_m_dir = s_pp.tokens[m]'h_m_pp_lt := by
              have : ∀ (h : m < s_pp.tokens.size),
                  s_dir.tokens[m]'(h_dir_tok ▸ h) = s_pp.tokens[m]'h := by
                intro h; congr 1
              exact this h_m_pp_lt
            have h_inv_dir : s_dir.simpleKey.possible = true →
                m ≠ s_dir.simpleKey.tokenIndex ∧ m ≠ s_dir.simpleKey.tokenIndex + 1 := by
              rw [← h_dir_def]
              split <;> exact h_inv_pp
            -- Fix B pending-directives check: error arm contradicts h_ok
            split at h_ok
            · contradiction
            generalize h_ck : scanNextTokenIx_checkBlockFlowIndent s_dir c = ck_res at h_ok
            cases ck_res with
            | error e => simp at h_ok
            | ok _ =>
              dsimp only [] at h_ok
              generalize h_df : scanNextTokenIx_dispatchFlowIndicators s_dir c = df_res at h_ok
              cases df_res with
              | error e => simp at h_ok
              | ok df_inner =>
                cases df_inner with
                | some s_flow =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                  subst h_ok
                  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h_df with
                    heq | heq | heq | heq | hOk
                  · subst heq
                    have h_pref := scanFlowSequenceStartIx_preserves_prefix s_dir m h_m_dir
                    have h_sz : m < (scanFlowSequenceStartIx s_dir).tokens.size := by
                      have := scanFlowSequenceStartIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowSequenceEndIx_preserves_prefix s_dir m h_m_dir
                    have h_sz : m < (scanFlowSequenceEndIx s_dir).tokens.size := by
                      have := scanFlowSequenceEndIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowMappingStartIx_preserves_prefix s_dir m h_m_dir
                    have h_sz : m < (scanFlowMappingStartIx s_dir).tokens.size := by
                      have := scanFlowMappingStartIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowMappingEndIx_preserves_prefix s_dir m h_m_dir
                    have h_sz : m < (scanFlowMappingEndIx s_dir).tokens.size := by
                      have := scanFlowMappingEndIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · have h_pref := scanFlowEntryIx_preserves_prefix s_dir s_flow hOk m h_m_dir
                    have h_sz : m < s_flow.tokens.size := by
                      have := scanFlowEntryIx_tokens_size_le hOk; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                | none =>
                  dsimp only [] at h_ok
                  generalize h_db : scanNextTokenIx_dispatchBlockIndicators s_dir c = db_res at h_ok
                  cases db_res with
                  | error e => simp at h_ok
                  | ok db_inner =>
                    cases db_inner with
                    | some s_blk =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                      subst h_ok
                      rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h_db with
                        hOk | hOk | hOk
                      · have h_pref := scanBlockEntryIx_preserves_prefix s_dir s_blk hOk m h_m_dir
                        have h_sz : m < s_blk.tokens.size := by
                          have := scanBlockEntryIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                      · have h_pref := scanKeyIx_preserves_prefix s_dir s_blk hOk m h_m_dir
                        have h_sz : m < s_blk.tokens.size := by
                          have := scanKeyIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                      · have h_pref := scanValueIx_preserves_position_specific s_dir s_blk hOk
                          m h_m_dir h_inv_dir
                        have h_sz : m < s_blk.tokens.size := by
                          have := scanValueIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        have h_pref :=
                          scanNextTokenIx_dispatchContent_preserves_prefix s_dir s_ct c h_dc m h_m_dir
                        have h_sz : m < s_ct.tokens.size := by
                          have := scanNextTokenIx_dispatchContent_tokens_size_le h_dc; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩

/-! ### §5.6  Chain-induction wrapper -/

/-- Chain-induction wrapper for pointwise position preservation
    through a `FlowMonoChainIx`. Parallel to `FlowMonoChainIx_preserves_
    raw_prefix` (`FlowMonoChain/Sync/Invariant.lean §4`) but with
    `NoOverwriteAtIx m` instead of `SimpleKeyAboveFloorIx`.

    Per Reflection 155: enables `.tokenshape.list` and `.tokenshape.
    pair` consumers to preserve a specific position above the simpleKey
    reservation through the rest of the chain. -/
lemma FlowMonoChainIx_preserves_position_specific {input : String}
    {s s' : ScannerStateIx input} {n fl₀ : Nat}
    (h_fmc : FlowMonoChainIx fl₀ s n s')
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : NoOverwriteAtIx s m) :
    ∃ (h_size : m < s'.tokens.size),
      s'.tokens[m]'h_size = s.tokens[m]'h_m := by
  induction h_fmc with
  | zero => exact ⟨h_m, rfl⟩
  | step _ h_snt h_rest ih =>
    have h_inv_mid := scanNextTokenIx_maintains_NoOverwriteAtIx _ _ h_snt m h_m h_inv
    obtain ⟨h_step_size, h_step_eq⟩ :=
      scanNextTokenIx_preserves_position_specific _ _ m h_m h_inv.1 h_snt
    obtain ⟨h_rest_size, h_rest_eq⟩ := ih h_step_size h_inv_mid
    exact ⟨h_rest_size, h_rest_eq.trans h_step_eq⟩

end L4YAML.Proofs.Indexed.EmitterScannability.EmitScans
