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

**What `.substrate.b` does NOT yet ship** (deferred further):

  - `EmitListScansInFlowIx_strong` exposing the first-step boundary
    state. Not strictly required by `.tokenshape.list` if that
    sub-sub-session does its own `cases h_fmc` decomposition.
  - The fully-automated SCALAR-LIST no-overwrite invariant
    (preserving positions ABOVE `simpleKey.tokenIndex + 1` through
    the chain). Analysis (Reflection 154, this session) showed
    this requires a per-step invariant of the form "active
    `simpleKey.tokenIndex+1 ∉ {protected positions}`", maintained
    through `scanNextTokenIx_maintains_SKAFIx`-style induction —
    workable but ~200 LOC of new step-level lemmas. The
    consumer-side (`.tokenshape.list` / `.tokenshape.pair`) can
    instead provide its own consumer-targeted SKAF instance to
    apply §4's lemma at an appropriate floor.

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
theorem EmitPairListScansInFlowIx_strong.toWeak {pairs : List (YamlValue × YamlValue)}
    (h_strong : EmitPairListScansInFlowIx_strong (input := input) pairs) :
    EmitPairListScansInFlowIx (input := input) pairs := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, _h_n_ge_3⟩ :=
    h_strong s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
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
theorem emitPairList_scans_nonemptyIx_strong (pairs : List (YamlValue × YamlValue))
    (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlowIx (input := input) p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlowIx (input := input) p.2) :
    EmitPairListScansInFlowIx_strong (input := input) pairs := by
  induction pairs with
  | nil => contradiction
  | cons p tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
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
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
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
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- Step 2: scan ':' via scanNextToken_flow_valueIx
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂⟩ :=
        scanNextToken_flow_valueIx s₁
          ((L4YAML.Emit.emit p.2).toList ++
            [',', ' '] ++ (L4YAML.Emit.emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
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
theorem scanValuePrepareIx_flow_tokens_eq (s : ScannerStateIx input)
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
theorem scanValuePrepareIx_flow_size_eq (s : ScannerStateIx input)
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
theorem scanValuePrepareIx_flow_pointwise (s : ScannerStateIx input)
    (h_sk : s.simpleKey.possible = true)
    (h_flow : s.inFlow = true) :
    -- (key) IF position `idx + 1` is in range, the new token there is `.key`.
    (∀ (h_lt : s.simpleKey.tokenIndex + 1 < s.tokens.tokens.size),
      ((scanValuePrepareIx s).tokens.tokens[s.simpleKey.tokenIndex + 1]'(by
        rw [scanValuePrepareIx_flow_size_eq s h_sk h_flow]; exact h_lt)).token =
        YamlToken.key) ∧
    -- (rest) all positions `i ≠ idx + 1` are preserved.
    (∀ (i : Nat) (hi : i < s.tokens.tokens.size) (h_ne : i ≠ s.simpleKey.tokenIndex + 1),
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
theorem FlowMonoChainIx_filtered_prefix_no_overwrite
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
theorem FlowMonoChainIx_filtered_prefix_no_overwrite_list
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

end L4YAML.Proofs.Indexed.EmitterScannability.EmitScans
