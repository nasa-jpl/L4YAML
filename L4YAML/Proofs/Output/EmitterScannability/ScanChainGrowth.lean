/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.EmitterScannability.FilteredGrowth

/-!
# Emitter Scannability — Strict Chain Growth + Saved-Key Survival + Pipeline

Foundation module extracted 2026-05-31 from `EmitterScannability.lean`. Imports the
previous foundation layer `FilteredGrowth`; the base imports this transitively.
Namespace reopened; contiguous prefix slice ⇒ no forward references.

Contents: the strict-variant `ScanChainGrew` track, saved-key survival across a
key-node scan, the emitList/emitPairList SKDR-witness scanning theorems (§H), and
the §4 full-pipeline composition (Emit → Scan → Parse).
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

/-! ### Strict-variant track: `ScanChainGrew`

`ScanChainGrew p` is `ScanChain` augmented with a per-step witness that
the filtered count under predicate `p` strictly increases at each step.
Built constructively at the call site, it is the honest replacement for
the former loose per-step lemma `scanNextToken_filtered_grows`: that lemma
claimed a `≥ +1` filtered-growth bound for *every* successful step, which is
false on the YAML 1.2.2 §6.8.3 RESERVED-directive branch (`%FOO …` scans to
`skipToEndOfLine`, emitting no token), and so carried a `sorry`.  It and its
`ScanChain` corollary `ScanChain_filtered_grows` have been **removed** (see
`FilteredTracking.lean`); the `+ n` bound now comes from
`ScanChainGrew_filtered_grows` below, whose per-step witnesses are produced
where the emitter-body chains are actually built — there are no reserved
directives there.  Forgetful `toScanChain` lets a strict chain be passed
wherever a `ScanChain` was expected. -/
inductive ScanChainGrew (p : Positioned YamlToken → Bool) :
    ScannerState → Nat → ScannerState → Prop where
  | zero {s : ScannerState} : ScanChainGrew p s 0 s
  | step {s s_mid s' : ScannerState} {n : Nat} :
         scanNextToken s = .ok (some s_mid) →
         (s_mid.tokens.filter p).size > (s.tokens.filter p).size →
         ScanChainGrew p s_mid n s' →
         ScanChainGrew p s (n + 1) s'

/-- Forgetful map: a `ScanChainGrew` is, in particular, a `ScanChain`. -/
theorem ScanChainGrew.toScanChain {p : Positioned YamlToken → Bool}
    {s s' : ScannerState} {n : Nat}
    (h : ScanChainGrew p s n s') : ScanChain s n s' := by
  induction h with
  | zero => exact .zero
  | step h_snt _h_grew _h_rest ih => exact .step h_snt ih

/-- A zero-length `ScanChainGrew` leaves the state unchanged. -/
theorem ScanChainGrew.eq_of_zero {p : Positioned YamlToken → Bool}
    {s s' : ScannerState} (h : ScanChainGrew p s 0 s') : s' = s := by
  cases h; rfl

/-- Single-step constructor for `ScanChainGrew`. -/
theorem ScanChainGrew.single {p : Positioned YamlToken → Bool}
    {s s' : ScannerState}
    (h : scanNextToken s = .ok (some s'))
    (h_grew : (s'.tokens.filter p).size > (s.tokens.filter p).size) :
    ScanChainGrew p s 1 s' :=
  .step h h_grew .zero

/-- Transitivity for `ScanChainGrew`: concatenate two strict chains. -/
theorem ScanChainGrew.trans {p : Positioned YamlToken → Bool}
    {s₁ s₂ s₃ : ScannerState} {n₁ n₂ : Nat}
    (h1 : ScanChainGrew p s₁ n₁ s₂) (h2 : ScanChainGrew p s₂ n₂ s₃) :
    ScanChainGrew p s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_snt h_grew _h_rest ih =>
    have h_ih := ih h2
    have hk : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [hk]
    exact .step h_snt h_grew h_ih

/-- Strict-chain growth: through a `ScanChainGrew p` of `n` steps, the
    filtered token array grows by at least `n`.  Same conclusion as
    `ScanChain_filtered_grows`, but proven directly from the per-step
    witness — does not depend on `scanNextToken_filtered_grows` (and so
    does not depend on the line-8379 sorry). -/
theorem ScanChainGrew_filtered_grows {p : Positioned YamlToken → Bool}
    {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChainGrew p s n s') :
    (s'.tokens.filter p).size ≥ (s.tokens.filter p).size + n := by
  induction h_chain with
  | zero => omega
  | step _h_snt h_grew _h_rest ih => omega

/-- Lift a `ScanChainGrew` through a `scanNextToken` equality.  Used when
    `s₂` is derived from `s₁` by preprocessing whitespace (which preserves
    the dispatch result via `scanNextToken_eq_of_preprocess` and is
    monotone on filtered token count via `preprocess_filtered_mono`).  The
    chain must be non-empty (length ≥ 1) so the first step's witness can
    be transitively weakened from `s₂.tokens.filter` down to
    `s₁.tokens.filter`. -/
theorem ScanChainGrew_of_scanNextToken_eq {p : Positioned YamlToken → Bool}
    {s₁ s₂ s' : ScannerState} {n : Nat}
    (h_eq : scanNextToken s₁ = scanNextToken s₂)
    (h_le : (s₁.tokens.filter p).size ≤ (s₂.tokens.filter p).size)
    (h_chain : ScanChainGrew p s₂ (n + 1) s') :
    ScanChainGrew p s₁ (n + 1) s' := by
  cases h_chain with
  | step h_snt h_grew h_rest =>
    refine .step (by rw [h_eq]; exact h_snt) ?_ h_rest
    omega

-- ═══ EmitScansInFlow: flow-context scanner acceptance ═══

/-- `EmitScansInFlow v` asserts that `emit v` can be scanned successfully
    from any scanner state in flow context.

    This is the inductive property needed for flow collection composition:
    each sub-expression of a flow collection scans correctly from mid-stream,
    preserving scanner invariants for subsequent tokens.

    **Tier 1 Turn 3 update**: produces `ScanChainGrew` (strict per-step
    filtered-growth witness) rather than the loose `ScanChain`.  Consumers
    that only need `ScanChain` may use `.toScanChain` to forget the
    witness. -/
def EmitScansInFlow (v : YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit v).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ s'.simpleKeyAllowed = false
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'

/-- `EmitListScansInFlow items` asserts that scanning the comma-separated
    emitList output succeeds in flow context, preserving invariants.
    This is the body between `[` and `]` in a flow sequence. -/
def EmitListScansInFlow (items : List YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'

/-- Empty list body is trivially scanned (0-step chain). -/
theorem emitList_scans_empty : EmitListScansInFlow [] := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
  -- emit.emitList [] = "", toList = [], so state is already at rest
  have h_eq : (emit.emitList ([] : List YamlValue)).toList ++ rest = rest := by
    simp only [emit.emitList]; rfl
  rw [h_eq] at hcorr
  exact ⟨0, s, .zero, hcorr, rfl, rfl, rfl, rfl, h_col, h_flow, h_indent, rfl, h_atol, h_endline, rfl, .zero (Nat.le.refl)⟩

/-- Non-empty list scanning via induction on the item list.
    Structure: singleton case uses EmitScansInFlow directly;
    multi-item case chains emit v + comma + space + recursive emitList. -/
theorem emitList_scans_nonempty (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlow v) :
    EmitListScansInFlow items := by
  induction items with
  | nil => contradiction
  | cons v tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    match tail, ih with
    | [], _ =>
      -- Singleton [v]: emitList [v] = emit v
      have h_eq : (emit.emitList [v]).toList = (emit v).toList := by
        simp only [emit.emitList]
      rw [h_eq] at hcorr
      obtain ⟨n, s', h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow', h_indent', h_line_v, _, _, h_atol', h_endline', h_stack', h_fmc'⟩ :=
        h_all v (.head _) s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      exact ⟨n, s', h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow', h_indent', h_line_v, h_atol', h_endline', h_stack', h_fmc'⟩
    | v' :: vs, ih =>
      -- Multi-item: emitList (v :: v' :: vs) = emit v ++ ", " ++ emitList (v' :: vs)
      -- Rewrite chars to decompose
      have h_eq : (emit.emitList (v :: v' :: vs)).toList ++ rest_chars =
          (emit v).toList ++ ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
        simp [emit.emitList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan emit v via EmitScansInFlow
      have h_ev : EmitScansInFlow v := h_all v (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_flow₁, h_indent₁, _h_line₁, _, h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁⟩ :=
        h_ev s ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- Step 2: Scan ',' via scanNextToken_flow_comma
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂⟩ :=
        scanNextToken_flow_comma s₁
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁
          h_last₁ h_atol₁ h_endline₁
      -- s₂ at ' ' :: (emitList (v' :: vs)).toList ++ rest_chars
      -- Step 3: Handle leading space via preprocessing equality
      obtain ⟨c, rest', h_first, h_nws, h_nlb, h_nc⟩ := emitList_first_char v' vs
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c :: (rest' ++ rest_chars), s₂.col⟩ := by
        have : ' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars =
            ' ' :: c :: (rest' ++ rest_chars) := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₂]; omega)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₂]; exact h_indent₁
      have h_s2_col : s₂.col > 0 := by rw [h_col₂]; omega
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c (rest' ++ rest_chars) h_corr₂_ws
          h_s2_flow h_nws h_nlb h_nc h_s2_indent
      -- s₃ at c :: rest' ++ rest_chars = (emitList (v' :: vs)).toList ++ rest_chars
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit.emitList (v' :: vs)).toList ++ rest_chars, s₃.col⟩ := by
        have : c :: (rest' ++ rest_chars) = (emit.emitList (v' :: vs)).toList ++ rest_chars := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: Recursive scan of emitList (v' :: vs) from s₃
      have h_tail_all : ∀ w ∈ v' :: vs, EmitScansInFlow w :=
        fun w hw => h_all w (.tail _ hw)
      have h_ih_list : EmitListScansInFlow (v' :: vs) :=
        ih (by simp) h_tail_all
      obtain ⟨n₃, s_end, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc₃⟩ :=
        h_ih_list s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂, h_ek₁]; exact h_ek)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
      -- Step 5: Lift chain for s₂ via preprocessing equality
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      -- Chain from s₃ must have n₃ ≥ 1 (emitList is non-empty)
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit.emitList (v' :: vs)).toList = [] := by
            match h_list : (emit.emitList (v' :: vs)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          exact absurd h_nil (emitList_toList_ne_nil v' vs)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      -- Lift the recursive ScanChainGrew through the preprocess equality.
      -- preprocess_flow_ws1 preserves tokens (h_toks_pp₃ : s₃.tokens = s₂.tokens),
      -- so the per-step witness from h_chain₃ at s₃ remains valid at s₂.
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain₃
      -- Per-step witness for the comma step (s₁ → s₂): the next char is ','.
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars), s₁.col⟩ := by
          have : [',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars =
              ',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ','
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- FlowMonoChain: lift recursive chain through preprocessing, then compose
      have h_fmc₃' : FlowMonoChain s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      -- Compose strict chains: emit v (n₁) + comma (1) + space+rest (n₃'+1)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all⟩
      · -- flowLevel preserved
        rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · -- directivesPresent preserved
        rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · -- indents preserved
        rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · -- explicitKeyLine preserved
        rw [h_ek_end, h_ek₃, h_ek₂, h_ek₁]
      · -- line preserved
        rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · -- simpleKeyStack preserved
        rw [h_stack_end, h_stack_pp₃, h_stack₂, h_stack₁]

-- ═══ Flow mapping pair list scanning ═══

-- The first char of `emitPairList (p :: ps)` is the first char of `emit p.1` (the key).
theorem emitPairList_first_char (p : YamlValue × YamlValue) (ps : List (YamlValue × YamlValue)) :
    ∃ c rest', (emit.emitPairList (p :: ps)).toList = c :: rest' ∧
      isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ c ≠ '#' := by
  obtain ⟨c, ev_rest, h_emit_eq, h_nws, h_nlb, h_nc⟩ := emit_first_char p.1
  match ps with
  | [] =>
    simp only [emit.emitPairList]
    rw [show (emit p.1 ++ ": " ++ emit p.2).toList =
        (emit p.1).toList ++ (": " ++ emit p.2).toList from by
      simp [String.toList_append]]
    rw [h_emit_eq]
    exact ⟨c, ev_rest ++ (": " ++ emit p.2).toList, by simp, h_nws, h_nlb, h_nc⟩
  | p' :: ps' =>
    have h_ep : (emit.emitPairList (p :: p' :: ps')).toList =
        (emit p.1).toList ++ (": " ++ emit p.2 ++ ", " ++ emit.emitPairList (p' :: ps')).toList := by
      simp [emit.emitPairList, String.toList_append, List.append_assoc]
    rw [h_ep, h_emit_eq]
    exact ⟨c, ev_rest ++ (": " ++ emit p.2 ++ ", " ++ emit.emitPairList (p' :: ps')).toList,
      by simp, h_nws, h_nlb, h_nc⟩

-- isValueCandidate returns true when peekAt? 1 is a space (blank).
-- This works through ALL branches of isValueCandidate because each branch
-- has a peekAt? 1 fallback path.
theorem isValueCandidate_of_peekAt_blank (s : ScannerState)
    (h : s.peekAt? 1 = some ' ') :
    isValueCandidate s = true := by
  unfold isValueCandidate
  split
  · split
    · -- offset ≠: match tokens[size-1]?; if isJsonNodeToken then true else peekAt fallback
      dsimp only []
      split  -- match tokens[...]?
      · split  -- if isJsonNodeToken tok.val
        · dsimp only []  -- reduces true = true
        · rw [h]; decide
      · rw [h]; decide
    · -- offset =: similar
      dsimp only []
      split
      · split
        · dsimp only []
        · rw [h]; decide
      · rw [h]; decide
  · rw [h]; dsimp only []; simp [isBlankBool, isWhiteSpaceBool, isSpaceBool, isTabBool]

-- Value indicator `:` scanning in flow context.
-- Value indicator `:` scanning in flow context.
-- After scanning a key (e.g., double-quoted scalar), `:` dispatches through
-- isValueCandidate → scanValue, emitting a .value token and advancing past `:`.
-- Requires space after `:` (emitter always produces ": ") for isValueCandidate
-- to hold in all simpleKey branches via peekAt? fallback.
-- Result state is at `' ' :: rest'` (space not yet consumed).
theorem scanNextToken_flow_value (s : ScannerState)
    (rest' : List Char)
    (hcorr : ScannerSurfCorr s ⟨':' :: ' ' :: rest', s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_sv : scanValueValidate (saveSimpleKey s) = .ok ())
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨' ' :: rest', s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.col = s.col + 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ s'.simpleKey.possible = false
      -- When a simple key was saved (and not re-reserved this step), `scanValuePrepare`
      -- in flow retroactively writes `.key` at `tokenIndex + 1`, leaving all other
      -- in-bounds positions untouched. This is the colon's token effect (sorry 9644).
      ∧ (s.simpleKeyAllowed = false → s.simpleKey.possible = true →
          s.simpleKey.tokenIndex + 1 < s.tokens.size →
          s'.tokens[s.simpleKey.tokenIndex + 1]? =
            some ⟨s.simpleKey.pos, .key, s.simpleKey.pos⟩ ∧
          (∀ i, i < s.tokens.size → i ≠ s.simpleKey.tokenIndex + 1 →
            s'.tokens[i]? = s.tokens[i]?))
      -- The colon's `.value` push: `scanValue` always `emit .value` at the end,
      -- so (when no key was re-reserved this step, i.e. `ska = false`) the token
      -- array grows by exactly one `.value` token at the old end. This is the
      -- push half of the colon's filtered-LIST delta (toward sorries 9646/9552).
      ∧ (s.simpleKeyAllowed = false →
          s'.tokens.size = s.tokens.size + 1 ∧
          ∃ pos, s'.tokens[s.tokens.size]? = some ⟨pos, .value, pos⟩) := by
  -- Step 1: Preprocessing — `:` is non-ws content char
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ':')) :=
    scanNextToken_preprocess_flow s ':' (' ' :: rest') s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: Structural dispatch returns none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ':' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  -- Step 4: checkBlockFlowIndent passes in flow
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check : scanNextToken_checkBlockFlowIndent s_ad ':' = .ok () :=
    checkBlockFlowIndent_ok_flow _ _ (h_ad_flow ▸ h_flow)
  -- Step 5: Flow dispatch returns none (`:` is not a flow indicator)
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad ':' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Step 6: isValueCandidate via peekAt? 1 = space fallback
  have h_ad_offset : s_ad.offset = s.offset := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s
  have h_ad_input : s_ad.input = s.input := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s
  have h_ad_inputEnd : s_ad.inputEnd = s.inputEnd := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s
  have ⟨h_pk_colon, h_lt_colon⟩ := peek_of_chars_cons s ':' (' ' :: rest') s.col hcorr
  have h_adv_corr := advance_non_newline_corr s ':' (' ' :: rest') hcorr h_lt_colon
    (by decide) (by decide)
  have ⟨h_pk_space, _⟩ := peek_of_chars_cons s.advance ' ' rest' (s.col + 1) h_adv_corr
  have h_peekAt1 : s.peekAt? 1 = some ' ' := by
    rw [← L4YAML.Proofs.ScannerPlainContent.advance_peek_eq_peekAt_one s ':' h_pk_colon]
    exact h_pk_space
  have h_ad_peekAt1 : s_ad.peekAt? 1 = some ' ' := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop
    rw [h_ad_offset, h_ad_input, h_ad_inputEnd]
    change ScannerState.peekAt?Loop s.input s.inputEnd ⟨s.offset⟩ 1 = some ' '
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop at h_peekAt1; exact h_peekAt1
  have h_vc : isValueCandidate s_ad = true :=
    isValueCandidate_of_peekAt_blank s_ad h_ad_peekAt1
  -- Step 7: Block dispatch yields scanValue
  have h_block_eq : scanNextToken_dispatchBlockIndicators s_ad ':' =
      (scanValue s_ad >>= fun s' => .ok (some s')) := by
    unfold scanNextToken_dispatchBlockIndicators
    simp only [show (':' == '-') = false from by decide, Bool.false_and,
               show (':' == '?') = false from by decide,
               show (':' == ':') = true from by decide, Bool.true_and, h_vc, ite_true]
    rfl
  -- Step 8: scanValue decomposition
  have h_ad_ek : s_ad.explicitKeyLine = none := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = none
      unfold saveSimpleKey; split <;> (try exact h_ek) <;> split <;> exact h_ek
    · unfold saveSimpleKey; split <;> (try exact h_ek) <;> split <;> exact h_ek
  have h_ckr : scanValueClearKey s_ad = s_ad := by
    unfold scanValueClearKey; rw [h_ad_ek]
  have h_validate : scanValueValidate s_ad = .ok () := by
    -- scanValueValidate only reads simpleKey, tokens, inFlow, isInFlowSequence,
    -- explicitKeyLine, line, col, currentIndent — none affected by allowDirectives
    have : scanValueValidate s_ad = scanValueValidate (saveSimpleKey s) := by
      simp only [s_ad]; split <;> (unfold scanValueValidate; rfl)
    rw [this]; exact h_sv
  -- scanValueTabCheck is identity in flow
  have h_ad_inFlow : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  -- Unfold scanValue, building the result state
  -- scanValue s_ad = do
  --   let s_kc := scanValueClearKey s_ad  -- = s_ad (since ek = none)
  --   scanValueValidate s_kc              -- .ok ()
  --   let s_prep := scanValuePrepare s_kc
  --   let s_tok := s_prep.emit .value
  --   let s_adv := s_tok.advance
  --   scanValueTabCheck s_ad.col s_ad.currentIndent s_adv  -- .ok () in flow
  --   .ok { s_adv with simpleKeyAllowed := true, explicitKeyLine := none }
  let s_prep := scanValuePrepare s_ad
  let s_tok := s_prep.emit .value
  let s_adv := s_tok.advance
  have h_scanValue_result : scanValue s_ad =
      (scanValueTabCheck (s_ad.col : Int) s_ad.currentIndent s_adv >>= fun () =>
        .ok { s_adv with simpleKeyAllowed := true, explicitKeyLine := none }) := by
    unfold scanValue
    dsimp only []  -- zeta-reduce let bindings in the unfolded body
    rw [h_ckr, h_validate]
    dsimp only [Bind.bind, Except.bind]
  -- scanValueTabCheck is .ok () since !s_adv.inFlow = false
  -- s_adv.inFlow = s_prep.inFlow = s_ad.inFlow = true (through emit and advance)
  have h_prep_inFlow : s_prep.inFlow = s_ad.inFlow := by
    show (scanValuePrepare s_ad).inFlow = s_ad.inFlow
    unfold scanValuePrepare
    split <;> (split <;> try split) <;> simp_all [ScannerState.inFlow]
  have h_tok_inFlow : s_tok.inFlow = s_prep.inFlow := by
    show (s_prep.emit .value).inFlow = s_prep.inFlow
    simp only [ScannerState.emit, ScannerState.inFlow]; rfl
  have h_adv_inFlow : s_adv.inFlow = s_tok.inFlow := by
    show s_tok.advance.inFlow = s_tok.inFlow
    exact advance_inFlow s_tok
  have h_tab_ok : scanValueTabCheck (s_ad.col : Int) s_ad.currentIndent s_adv = .ok () := by
    unfold scanValueTabCheck
    have : s_adv.inFlow = true := by
      rw [h_adv_inFlow, h_tok_inFlow, h_prep_inFlow]; exact h_ad_inFlow
    simp [this]
  -- Derive scanValue s_ad = .ok s_final
  let s_final : ScannerState := { s_adv with simpleKeyAllowed := true, explicitKeyLine := none }
  have h_scanValue_ok : scanValue s_ad = .ok s_final := by
    rw [h_scanValue_result, h_tab_ok]; dsimp only [Bind.bind, Except.bind]
  -- Derive block dispatch result
  have h_block_result : scanNextToken_dispatchBlockIndicators s_ad ':' = .ok (some s_final) := by
    rw [h_block_eq, h_scanValue_ok]; dsimp only [Bind.bind, Except.bind]
  -- Compose pipeline
  have h_snt : scanNextToken s = .ok (some s_final) :=
    scanNextToken_via_block_dispatch s (saveSimpleKey s) s_ad s_final ':'
      h_pp h_struct (by rfl) h_check h_flow_none h_block_result
  -- scanValuePrepare preserves key fields in flow context
  -- (only modifies tokens and simpleKey when inFlow = true)
  have h_svp_flow := h_ad_inFlow
  have h_prep_fl : s_prep.flowLevel = s_ad.flowLevel := by
    show (scanValuePrepare s_ad).flowLevel = s_ad.flowLevel
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_dp : s_prep.directivesPresent = s_ad.directivesPresent := by
    show (scanValuePrepare s_ad).directivesPresent = s_ad.directivesPresent
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_indents : s_prep.indents = s_ad.indents := by
    show (scanValuePrepare s_ad).indents = s_ad.indents
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_col : s_prep.col = s_ad.col := by
    show (scanValuePrepare s_ad).col = s_ad.col
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_offset : s_prep.offset = s_ad.offset := by
    show (scanValuePrepare s_ad).offset = s_ad.offset
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_input : s_prep.input = s_ad.input := by
    show (scanValuePrepare s_ad).input = s_ad.input
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_inputEnd : s_prep.inputEnd = s_ad.inputEnd := by
    show (scanValuePrepare s_ad).inputEnd = s_ad.inputEnd
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  -- s_ad fields equal s fields (through allowDirectives branch + saveSimpleKey)
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_indents : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_col s
  -- Surface field equalities between s_final/s_adv and s.advance
  have h_final_input : s_final.input = s.advance.input := by
    show s_adv.input = s.advance.input
    rw [show s_adv.input = s_tok.input from advance_input s_tok]
    show s_prep.input = s.advance.input
    rw [h_prep_input, h_ad_input, advance_input s]
  have h_final_offset : s_final.offset = s.advance.offset := by
    show s_adv.offset = s.advance.offset
    exact advance_offset_of_eq s_tok s
      (by show s_prep.input = s.input; rw [h_prep_input, h_ad_input])
      (by show s_prep.offset = s.offset; rw [h_prep_offset, h_ad_offset])
      (by show s_prep.inputEnd = s.inputEnd; rw [h_prep_inputEnd, h_ad_inputEnd])
  have h_final_inputEnd : s_final.inputEnd = s.advance.inputEnd := by
    show s_adv.inputEnd = s.advance.inputEnd
    rw [show s_adv.inputEnd = s_tok.inputEnd from advance_inputEnd s_tok]
    show s_prep.inputEnd = s.advance.inputEnd
    rw [h_prep_inputEnd, h_ad_inputEnd, advance_inputEnd s]
  have h_final_indents : s_final.indents = s.advance.indents := by
    show s_adv.indents = s.advance.indents
    rw [advance_indents s_tok]
    show s_prep.indents = s.advance.indents
    rw [h_prep_indents, h_ad_indents, advance_indents s]
  -- Line preservation
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have h_prep_line : s_prep.line = s_ad.line := by
    show (scanValuePrepare s_ad).line = s_ad.line
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  refine ⟨s_final, h_snt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ScannerSurfCorr s_final ⟨' ' :: rest', s_final.col⟩
    exact {
      chars_from := by rw [h_final_input, h_final_offset]; exact h_adv_corr.chars_from
      col_eq := rfl
      end_eq := by rw [h_final_inputEnd, h_final_input]; exact h_adv_corr.end_eq
      input_prefix := by rw [h_final_input, h_final_offset]; exact h_adv_corr.input_prefix
      indent_cols_nonneg := by
        intro i hi h0
        have hi' : i < s.advance.indents.size := by
          rw [← h_final_indents]; exact hi
        have : s_final.indents[i] = s.advance.indents[i]'hi' := by
          simp only [h_final_indents]
        rw [this]; exact h_adv_corr.indent_cols_nonneg i hi' h0
    }
  · -- s_final.flowLevel = s.flowLevel
    show s_adv.flowLevel = s.flowLevel
    rw [show s_adv.flowLevel = s_tok.flowLevel from advance_flowLevel s_tok]
    show s_prep.flowLevel = s.flowLevel
    rw [h_prep_fl, h_ad_fl]
  · -- s_final.directivesPresent = s.directivesPresent
    show s_adv.directivesPresent = s.directivesPresent
    rw [show s_adv.directivesPresent = s_tok.directivesPresent from advance_dp s_tok]
    show s_prep.directivesPresent = s.directivesPresent
    rw [h_prep_dp, h_ad_dp]
  · -- s_final.indents = s.indents
    show s_adv.indents = s.indents
    rw [show s_adv.indents = s_tok.indents from advance_indents s_tok]
    show s_prep.indents = s.indents
    rw [h_prep_indents, h_ad_indents]
  · -- s_final.col = s.col + 1
    show s_adv.col = s.col + 1
    -- s_adv = s_tok.advance, s_tok at ':' (non-newline), advance increments col
    have h_tok_col : s_tok.col = s.col := by
      show s_prep.col = s.col; rw [h_prep_col, h_ad_col]
    have h_tok_offset : s_tok.offset = s.offset := by
      show s_prep.offset = s.offset; rw [h_prep_offset, h_ad_offset]
    have h_tok_input : s_tok.input = s.input := by
      show s_prep.input = s.input; rw [h_prep_input, h_ad_input]
    have h_tok_inputEnd : s_tok.inputEnd = s.inputEnd := by
      show s_prep.inputEnd = s.inputEnd; rw [h_prep_inputEnd, h_ad_inputEnd]
    have h_tok_lt : s_tok.offset < s_tok.inputEnd := by
      rw [h_tok_offset, h_tok_inputEnd]; exact h_lt_colon
    -- Character at s_tok's position is `:`
    have h_s_char : String.Pos.Raw.get s.input ⟨s.offset⟩ = ':' := by
      have h_pk := h_pk_colon; unfold ScannerState.peek? at h_pk
      simp only [show s.offset < s.inputEnd from h_lt_colon, ite_true] at h_pk
      exact Option.some.inj h_pk
    have h_tok_char : String.Pos.Raw.get s_tok.input ⟨s_tok.offset⟩ = ':' := by
      rw [h_tok_input, h_tok_offset]; exact h_s_char
    rw [show s_adv.col = s_tok.advance.col from rfl]
    rw [advance_col_non_newline s_tok h_tok_lt
      (by rw [h_tok_char]; decide)
      (by rw [h_tok_char]; decide)]
    rw [h_tok_col]
  · -- s_final.inFlow = true
    show s_adv.inFlow = true
    rw [h_adv_inFlow, h_tok_inFlow, h_prep_inFlow]; exact h_ad_inFlow
  · -- s_final.currentIndent < 0
    show s_adv.currentIndent < 0
    have h_adv_indents : s_adv.indents = s.indents := by
      show s_tok.advance.indents = s.indents
      rw [advance_indents s_tok]
      show s_prep.indents = s.indents
      rw [h_prep_indents, h_ad_indents]
    unfold ScannerState.currentIndent
    rw [h_adv_indents]
    unfold ScannerState.currentIndent at h_indent
    exact h_indent
  · -- s_final.line = s.line
    show s_adv.line = s.line
    have h_tok_offset : s_tok.offset = s.offset := by
      show s_prep.offset = s.offset; rw [h_prep_offset, h_ad_offset]
    have h_tok_input : s_tok.input = s.input := by
      show s_prep.input = s.input; rw [h_prep_input, h_ad_input]
    have h_tok_inputEnd : s_tok.inputEnd = s.inputEnd := by
      show s_prep.inputEnd = s.inputEnd; rw [h_prep_inputEnd, h_ad_inputEnd]
    have h_tok_lt : s_tok.offset < s_tok.inputEnd := by
      rw [h_tok_offset, h_tok_inputEnd]; exact h_lt_colon
    have h_tok_peek : s_tok.peek? = some ':' := by
      unfold ScannerState.peek? at h_pk_colon ⊢
      rw [h_tok_offset, h_tok_inputEnd, h_tok_input]
      simp only [show s.offset < s.inputEnd from h_lt_colon, ite_true] at h_pk_colon ⊢
      exact h_pk_colon
    rw [advance_line_of_peek s_tok ':' h_tok_lt h_tok_peek (by decide) (by decide)]
    show s_prep.line = s.line; rw [h_prep_line, h_ad_line]
  · -- AllTokensOnLine s_final s_final.line
    -- s_final = { s_adv with simpleKeyAllowed, explicitKeyLine }, same tokens/line as s_adv
    have h_tok_offset' : s_tok.offset = s.offset := by
      show s_prep.offset = s.offset; rw [h_prep_offset, h_ad_offset]
    have h_tok_input' : s_tok.input = s.input := by
      show s_prep.input = s.input; rw [h_prep_input, h_ad_input]
    have h_tok_inputEnd' : s_tok.inputEnd = s.inputEnd := by
      show s_prep.inputEnd = s.inputEnd; rw [h_prep_inputEnd, h_ad_inputEnd]
    have h_tok_lt' : s_tok.offset < s_tok.inputEnd := by
      rw [h_tok_offset', h_tok_inputEnd']; exact h_lt_colon
    have h_tok_peek' : s_tok.peek? = some ':' := by
      unfold ScannerState.peek? at h_pk_colon ⊢
      rw [h_tok_offset', h_tok_inputEnd', h_tok_input']
      simp only [show s.offset < s.inputEnd from h_lt_colon, ite_true] at h_pk_colon ⊢
      exact h_pk_colon
    have h_adv_line : s_adv.line = s.line := by
      rw [advance_line_of_peek s_tok ':' h_tok_lt' h_tok_peek' (by decide) (by decide)]
      show s_prep.line = s.line; rw [h_prep_line, h_ad_line]
    rw [show s_final.line = s_adv.line from rfl, h_adv_line]
    change AllTokensOnLine s_adv s.line
    have h_sk_endline : EndLineOnLine (saveSimpleKey s) :=
      EndLineOnLine_saveSimpleKey_flow s h_endline
    have h_ad_endline : EndLineOnLine s_ad := by
      simp only [s_ad, EndLineOnLine]; split <;> exact h_sk_endline
    exact AllTokensOnLine_advance _ _
      (AllTokensOnLine_emit _ _ _
        (AllTokensOnLine_scanValuePrepare_flow s_ad s.line
          (AllTokensOnLine_allowDirectives _ _
            (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl))
          h_ad_line h_ad_inFlow h_ad_ek h_ad_endline)
        (by rw [h_prep_line, h_ad_line]))
  · -- EndLineOnLine s_final — vacuously true: scanValuePrepare in flow always gives possible = false
    intro h_poss
    exfalso
    have h_chain : s_final.simpleKey = (scanValuePrepare s_ad).simpleKey := by
      show s_adv.simpleKey = _
      rw [ScannerCorrectness.advance_preserves_simpleKey, ScannerCorrectness.emit_preserves_simpleKey]
    have h_false : s_final.simpleKey.possible = false := by
      rw [h_chain]
      unfold scanValuePrepare
      simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
      split
      · rfl
      · split
        · rfl
        · simp_all
    rw [h_false] at h_poss; exact absurd h_poss (by decide)
  · -- s_final.simpleKeyStack = s.simpleKeyStack
    show s_adv.simpleKeyStack = s.simpleKeyStack
    rw [ScannerCorrectness.advance_preserves_simpleKeyStack, ScannerCorrectness.emit_preserves_simpleKeyStack]
    have h_svp_stack : (scanValuePrepare s_ad).simpleKeyStack = s_ad.simpleKeyStack := by
      unfold scanValuePrepare
      simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
      split
      · rfl
      · split <;> rfl
    rw [h_svp_stack]
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · -- s_final.simpleKey.possible = false
    show s_adv.simpleKey.possible = false
    rw [ScannerCorrectness.advance_preserves_simpleKey, ScannerCorrectness.emit_preserves_simpleKey]
    exact ScannerCorrectness.scanValuePrepare_clears_simpleKey s_ad
  · -- Colon's `.key` token effect: when a key was saved (ska=false this step,
    -- possible=true), scanValuePrepare writes `.key` at tokenIndex+1.
    intro h_ska_false h_poss h_lt
    have h_save_id : saveSimpleKey s = s :=
      saveSimpleKey_id_of_flow_ska_false_ek_none s h_flow h_ska_false h_ek
    have h_adsk : s_ad.simpleKey = s.simpleKey := by
      simp only [s_ad, h_save_id]; split <;> rfl
    have h_adtok : s_ad.tokens = s.tokens := by
      simp only [s_ad, h_save_id]; split <;> rfl
    have h_ad_poss : s_ad.simpleKey.possible = true := by rw [h_adsk]; exact h_poss
    -- scanValuePrepare in flow with a possible key: tokens = setIfInBounds (idx+1) .key
    have h_prep_eq : (scanValuePrepare s_ad).tokens =
        s_ad.tokens.setIfInBounds (s_ad.simpleKey.tokenIndex + 1)
          ⟨s_ad.simpleKey.pos, .key, s_ad.simpleKey.pos⟩ := by
      unfold scanValuePrepare
      rw [if_pos h_ad_poss]
      split
      · rename_i h_neg; simp [h_ad_inFlow] at h_neg
      · rfl
    -- s_final.tokens = (scanValuePrepare s_ad).tokens.push <value token>
    have h_final_tok : s_final.tokens =
        (scanValuePrepare s_ad).tokens.push { pos := s_prep.currentPos, val := .value } := by
      show s_adv.tokens = _
      rw [ScannerCorrectness.advance_preserves_tokens]
      rfl
    -- Normalised setIfInBounds form on `s.tokens` at `s.simpleKey.tokenIndex + 1`.
    have h_prep_eq' : (scanValuePrepare s_ad).tokens =
        s.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1)
          ⟨s.simpleKey.pos, .key, s.simpleKey.pos⟩ := by
      rw [h_prep_eq, h_adtok, h_adsk]
    have h_prep_size : (scanValuePrepare s_ad).tokens.size = s.tokens.size := by
      rw [h_prep_eq', Array.size_setIfInBounds]
    refine ⟨?_, ?_⟩
    · -- s_final.tokens[idx+1]? = some .key
      rw [h_final_tok, Array.getElem?_push,
          if_neg (by rw [h_prep_size]; omega : s.simpleKey.tokenIndex + 1 ≠
            (scanValuePrepare s_ad).tokens.size),
          h_prep_eq',
          Array.getElem?_eq_getElem (by rw [Array.size_setIfInBounds]; omega),
          Array.getElem_setIfInBounds_self]
    · -- other in-bounds positions unchanged
      intro i hi hne
      rw [h_final_tok, Array.getElem?_push,
          if_neg (by rw [h_prep_size]; omega : i ≠ (scanValuePrepare s_ad).tokens.size),
          h_prep_eq',
          Array.getElem?_eq_getElem (by rw [Array.size_setIfInBounds]; exact hi),
          Array.getElem?_eq_getElem hi,
          Array.getElem_setIfInBounds_ne hi (fun h => hne h.symm)]
  · -- Colon's `.value` push: `scanValue` always emits `.value` at the end, so when
    -- no key is re-reserved this step (`ska = false`, hence `saveSimpleKey s = s`)
    -- the token array grows by exactly one `.value` token at the old end.
    intro h_ska_false
    have h_save_id : saveSimpleKey s = s :=
      saveSimpleKey_id_of_flow_ska_false_ek_none s h_flow h_ska_false h_ek
    have h_adtok : s_ad.tokens = s.tokens := by
      simp only [s_ad, h_save_id]; split <;> rfl
    -- s_final.tokens = (scanValuePrepare s_ad).tokens.push <value token>
    have h_final_tok : s_final.tokens =
        (scanValuePrepare s_ad).tokens.push { pos := s_prep.currentPos, val := .value } := by
      show s_adv.tokens = _
      rw [ScannerCorrectness.advance_preserves_tokens]; rfl
    -- scanValuePrepare preserves token-array size in every flow branch.
    have h_prep_size_gen : (scanValuePrepare s_ad).tokens.size = s_ad.tokens.size := by
      unfold scanValuePrepare
      simp only [h_ad_inFlow, Bool.not_true, Bool.false_eq_true, ite_false]
      split
      · rw [Array.size_setIfInBounds]
      · split <;> rfl
    have h_size : s_final.tokens.size = s.tokens.size + 1 := by
      rw [h_final_tok, Array.size_push, h_prep_size_gen, h_adtok]
    refine ⟨h_size, s_prep.currentPos, ?_⟩
    -- the pushed token sits at index `s.tokens.size = (scanValuePrepare s_ad).tokens.size`
    have h_idx_eq : s.tokens.size = (scanValuePrepare s_ad).tokens.size := by
      rw [h_prep_size_gen, h_adtok]
    rw [h_final_tok, h_idx_eq, Array.getElem?_push, if_pos rfl]

/-- **Colon filtered-LIST characterization** (the `(a1)` ASSEMBLE step toward
    legacy sorries 9646 / 9552). When the colon scans from a saved-key state
    (`ska = false`, `possible = true`) whose reserved *spare* slot `N+1`
    (`= tokenIndex + 1`) is still a `.placeholder` (the `(a2)` layout exposed by
    `EmitScansInFlowSavedKey`), the colon's filtered token list grows by exactly:
    *insert one delta-0 `.key` at the filtered rank of slot `N+1`*, then *append
    one delta-0 `.value`*.

    Pure glue: it reconstructs the colon's structural token equation
    `s'.tokens = (s.tokens.setIfInBounds (N+1) keyTok).push valueTok` pointwise from
    `scanNextToken_flow_value`'s `.key`-write + `.value`-push exposures (via
    `Array.ext_getElem?`), then turns it into the filtered-list equation with the
    insert-at-rank lemma `Array_filter_setIfInBounds_of_not_pass` + `Array.filter_push`.
    No remaining scanner exposure. -/
theorem scanNextToken_flow_value_block (s : ScannerState)
    (rest' : List Char)
    (hcorr : ScannerSurfCorr s ⟨':' :: ' ' :: rest', s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_sv : scanValueValidate (saveSimpleKey s) = .ok ())
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_ska : s.simpleKeyAllowed = false)
    (h_poss : s.simpleKey.possible = true)
    (h_lt : s.simpleKey.tokenIndex + 1 < s.tokens.size)
    (h_ph : (s.tokens[s.simpleKey.tokenIndex + 1]'h_lt).val = .placeholder) :
    ∃ s' pos_v, scanNextToken s = .ok (some s')
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList =
          ((s.tokens.toList.take (s.simpleKey.tokenIndex + 1)).filter
              (fun t => t.val != .placeholder)
            ++ (⟨s.simpleKey.pos, .key, s.simpleKey.pos⟩ : Positioned YamlToken) ::
               (s.tokens.toList.drop (s.simpleKey.tokenIndex + 2)).filter
                 (fun t => t.val != .placeholder))
          ++ [(⟨pos_v, .value, pos_v⟩ : Positioned YamlToken)] := by
  obtain ⟨s', h_snt, _, _, _, _, _, _, _, _, _, _, _, _, _, h_keyw, h_valpush⟩ :=
    scanNextToken_flow_value s rest' hcorr h_flow h_indent h_col_pos h_ek h_sv h_atol h_endline
  obtain ⟨h_key_at, h_pres⟩ := h_keyw h_ska h_poss h_lt
  obtain ⟨h_size, pos_v, h_val_at⟩ := h_valpush h_ska
  refine ⟨s', pos_v, h_snt, ?_⟩
  -- Structural token equation, reconstructed pointwise from the two exposures.
  have h_struct : s'.tokens =
      (s.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1)
        ⟨s.simpleKey.pos, .key, s.simpleKey.pos⟩).push ⟨pos_v, .value, pos_v⟩ := by
    apply Array.ext_getElem?
    intro i
    rw [Array.getElem?_push, Array.size_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hi_sz : i = s.tokens.size
    · rw [if_pos hi_sz, hi_sz]; exact h_val_at
    · rw [if_neg hi_sz]
      by_cases hi_key : s.simpleKey.tokenIndex + 1 = i
      · rw [if_pos hi_key, if_pos h_lt, ← hi_key]; exact h_key_at
      · rw [if_neg hi_key]
        by_cases hi_lt : i < s.tokens.size
        · exact h_pres i hi_lt (fun h => hi_key h.symm)
        · rw [Array.getElem?_eq_none (show s'.tokens.size ≤ i by omega),
              Array.getElem?_eq_none (show s.tokens.size ≤ i by omega)]
  rw [h_struct, Array.filter_push,
      if_pos (show (fun t : Positioned YamlToken => t.val != .placeholder)
                ⟨pos_v, .value, pos_v⟩ = true from rfl),
      Array.toList_push]
  congr 1
  exact Array_filter_setIfInBounds_of_not_pass s.tokens (s.simpleKey.tokenIndex + 1)
    ⟨s.simpleKey.pos, .key, s.simpleKey.pos⟩ (fun t => t.val != .placeholder) h_lt
    (by simp [h_ph]) rfl

/-- `EmitPairListScansInFlow pairs` asserts that scanning the
    emitPairList output succeeds in flow context, preserving invariants.
    This is the body between `{` and `}` in a flow mapping. -/
def EmitPairListScansInFlow (pairs : List (YamlValue × YamlValue)) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'

/-- Strong version of `EmitPairListScansInFlow`: additionally exposes the
    chain-length lower bound `n ≥ 3` (key emit + value indicator + value emit,
    each a positive sub-chain). Only inhabited for non-empty pair lists (the
    empty list scans in `0` steps). Mirrors the indexed
    `EmitPairListScansInFlowIx_strong`; directly enables Part 1 (`n ≥ 3`) of
    `emitPairList_body_filtered_characterization`. -/
def EmitPairListScansInFlow_strong (pairs : List (YamlValue × YamlValue)) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      ∧ n ≥ 3

/-- `EmitPairListScansInFlow_strong` implies the weak version (drops `n ≥ 3`). -/
theorem EmitPairListScansInFlow_strong.toWeak {pairs : List (YamlValue × YamlValue)}
    (h_strong : EmitPairListScansInFlow_strong pairs) :
    EmitPairListScansInFlow pairs := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, _⟩ :=
    h_strong s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
  exact ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
         h_indent', h_line', h_atol', h_endline', h_stack', h_fmc⟩

theorem emitPairList_scans_empty : EmitPairListScansInFlow [] := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
  have h_eq : (emit.emitPairList ([] : List (YamlValue × YamlValue))).toList ++ rest = rest := by
    simp [emit.emitPairList]
  exact ⟨0, s, .zero, h_eq ▸ hcorr, rfl, rfl, rfl, rfl, h_col, h_flow, h_indent, rfl, h_atol, h_endline, rfl, .zero (Nat.le.refl)⟩

-- Non-empty pair list scanning: each pair contributes key + ":" + space + value steps.
-- Uses emitPairList_first_char, scanNextToken_flow_value, scanNextToken_flow_comma,
-- scanNextToken_preprocess_flow_ws1, and EmitScansInFlow for keys and values.
--
-- Note: scanValueValidate discharge is sorry'd pending line/token tracking
-- (Change B Layer 1.1 — checks 2 and 4 require isInFlowSequence + token analysis).
theorem emitPairList_scans_nonempty (pairs : List (YamlValue × YamlValue))
    (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlow p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlow p.2) :
    EmitPairListScansInFlow_strong pairs := by
  induction pairs with
  | nil => contradiction
  | cons p tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    match tail, ih with
    | [], _ =>
      -- ══ Singleton [(k,v)]: emitPairList [(k,v)] = emit k ++ ": " ++ emit v ══
      have h_eq : (emit.emitPairList [p]).toList ++ rest_chars =
          (emit p.1).toList ++ ([':',  ' '] ++ (emit p.2).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan key via EmitScansInFlow
      have h_ek_key : EmitScansInFlow p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_ska₁, _, h_atol₁, h_endline₁, h_stack₁, h_fmc₁⟩ :=
        h_ek_key s ([':',  ' '] ++ (emit p.2).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- NEW (strong): n₁ ≥ 1 from non-empty `emit p.1` (key scan is positive).
      have h_n₁_pos : n₁ ≥ 1 := by
        match n₁, h_chain₁ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique hcorr.chars_from h_corr₁.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.1).toList = [] := by
            match h_list : (emit p.1).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.1
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      -- Step 2: Derive saveSimpleKey identity and scanValueValidate
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      -- Step 3: Scan ':' via scanNextToken_flow_value
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁ ((emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      -- Step 4: Handle leading space before value via preprocessing equality
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c_v :: (rest_v ++ rest_chars), s₂.col⟩ := by
        have h_eq_chars : (' ' :: (emit p.2).toList ++ rest_chars) =
            (' ' :: c_v :: (rest_v ++ rest_chars)) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₂
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_v (rest_v ++ rest_chars) h_corr₂_ws
          h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++ rest_chars, s₃.col⟩ := by
        have h_eq_chars : (c_v :: (rest_v ++ rest_chars)) =
            ((emit p.2).toList ++ rest_chars) := by
          rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₃
      -- Step 5: Scan value via EmitScansInFlow
      have h_ev : EmitScansInFlow p.2 := h_all_v p (.head _)
      obtain ⟨n₃, s_end, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, _, _, h_atol_end, h_endline_end, h_stack_end, h_fmc₃⟩ :=
        h_ev s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
      -- Step 6: Lift chain for s₂ via preprocessing equality
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.2).toList = [] := by
            match h_list : (emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain₃
      -- Per-step witness for the colon step (s₁ → s₂): the next char is ':'.
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (emit p.2).toList ++ rest_chars), s₁.col⟩ := by
          have : [':', ' '] ++ (emit p.2).toList ++ rest_chars =
              ':' :: (' ' :: (emit p.2).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (emit p.2).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- FlowMonoChain: lift value chain through preprocessing, compose with key + colon
      have h_fmc₃' : FlowMonoChain s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      -- Compose strict chains: key (n₁) + colon (1) + space+value (n₃'+1)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, by omega⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack_v₂, h_stack₁]
    | p' :: ps, ih =>
      -- ══ Multi-pair: emit k ++ ": " ++ emit v ++ ", " ++ emitPairList (p' :: ps) ══
      have h_eq : (emit.emitPairList (p :: p' :: ps)).toList ++ rest_chars =
          (emit p.1).toList ++ ([':',  ' '] ++ (emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan key via EmitScansInFlow
      have h_ek_key : EmitScansInFlow p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_ska₁, h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁⟩ :=
        h_ek_key s ([':',  ' '] ++ (emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- NEW (strong): n₁ ≥ 1 from non-empty `emit p.1` (key scan is positive).
      have h_n₁_pos : n₁ ≥ 1 := by
        match n₁, h_chain₁ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique hcorr.chars_from h_corr₁.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.1).toList = [] := by
            match h_list : (emit p.1).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.1
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      -- Step 2: Derive saveSimpleKey identity and scanValueValidate
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      -- Step 3: Scan ':' via scanNextToken_flow_value
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁
          ((emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      -- Step 4: Handle leading space before value
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c_v :: (rest_v ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₂.col⟩ := by
        have h_eq_chars : (' ' :: (emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) =
            (' ' :: c_v :: (rest_v ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₂
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_v
          (rest_v ++ [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₂_ws h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars, s₃.col⟩ := by
        have h_eq_chars : (c_v :: (rest_v ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) =
            ((emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
          rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₃
      -- Step 5: Scan value via EmitScansInFlow
      have h_ev : EmitScansInFlow p.2 := h_all_v p (.head _)
      have h_corr₃_assoc : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++ ([',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₃.col⟩ := by
        simp only [List.append_assoc] at h_corr₃' ⊢; exact h_corr₃'
      obtain ⟨n_v, s_v, h_chain_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v,
              h_ek_v, h_col_v, h_flow_v, h_indent_v, _h_line_v, _, h_last_v, h_atol_v, h_endline_v, h_stack_v, h_fmc_v⟩ :=
        h_ev s₃
          ([',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₃_assoc
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
      -- Lift value chain through preprocessing equality
      have h_snt_eq_v : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n_v_pos : n_v ≥ 1 := by
        match n_v, h_chain_v with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_v.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.2).toList = [] := by
            match h_list : (emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
      have h_filt_le_v : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                         (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws_v : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n_v' + 1) s_v :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_v h_filt_le_v h_chain_v
      -- Per-step witness for the colon step (s₁ → s₂): next char is ':'.
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₁.col⟩ := by
          have : [':', ' '] ++ (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- Step 6: Scan ',' via scanNextToken_flow_comma
      obtain ⟨s_c, h_snt_c, h_corr_c, h_fl_c, h_dp_c, h_ids_c, h_ek_c, h_col_c, _h_line_c, h_atol_c, h_endline_c, h_stack_c⟩ :=
        scanNextToken_flow_comma s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_atol_v h_endline_v
      -- Step 7: Handle leading space before next pair
      obtain ⟨c_p, rest_p, h_first_p, h_nws_p, h_nlb_p, h_nc_p⟩ :=
        emitPairList_first_char p' ps
      have h_corr_c_ws : ScannerSurfCorr s_c
          ⟨' ' :: c_p :: (rest_p ++ rest_chars), s_c.col⟩ := by
        have : ' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
            ' ' :: c_p :: (rest_p ++ rest_chars) := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_c
      have h_sc_flow : s_c.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_c]; omega)
      have h_sc_indent : s_c.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids_c]; exact h_indent_v
      obtain ⟨s_pp, h_corr_pp, h_flow_pp, h_fl_pp, h_indent_pp, h_col_pp,
              h_dp_pp, h_ids_pp, h_ek_pp, _h_line_pp, h_pp_eq_r, h_atol_transfer_pp, h_endline_transfer_pp, h_stack_pp, h_toks_pp, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s_c c_p (rest_p ++ rest_chars) h_corr_c_ws
          h_sc_flow h_nws_p h_nlb_p h_nc_p h_sc_indent
      have h_corr_pp' : ScannerSurfCorr s_pp
          ⟨(emit.emitPairList (p' :: ps)).toList ++ rest_chars, s_pp.col⟩ := by
        have : c_p :: (rest_p ++ rest_chars) =
            (emit.emitPairList (p' :: ps)).toList ++ rest_chars := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_pp
      -- Step 8: Recursive scan of emitPairList (p' :: ps)
      have h_tail_all_k : ∀ q ∈ p' :: ps, EmitScansInFlow q.1 :=
        fun q hq => h_all_k q (.tail _ hq)
      have h_tail_all_v : ∀ q ∈ p' :: ps, EmitScansInFlow q.2 :=
        fun q hq => h_all_v q (.tail _ hq)
      have h_ih_list : EmitPairListScansInFlow (p' :: ps) :=
        (ih (by simp) h_tail_all_k h_tail_all_v).toWeak
      obtain ⟨n_r, s_end, h_chain_r, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc_r⟩ :=
        h_ih_list s_pp rest_chars h_corr_pp'
          h_flow_pp
          (by rw [h_fl_pp, h_fl_c]; rw [h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent_pp]; exact h_sc_indent)
          (by rw [h_col_pp]; omega)
          (by rw [h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂])
          (h_atol_transfer_pp h_atol_c)
          (h_endline_transfer_pp h_endline_c)
      -- Lift recursive chain through preprocessing equality
      have h_snt_eq_r : scanNextToken s_c = scanNextToken s_pp :=
        scanNextToken_eq_of_preprocess s_c s_pp h_pp_eq_r
      have h_n_r_pos : n_r ≥ 1 := by
        match n_r, h_chain_r with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr_pp'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit.emitPairList (p' :: ps)).toList = [] := by
            match h_list : (emit.emitPairList (p' :: ps)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emitPairList_first_char p' ps
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_r', rfl⟩ : ∃ k, n_r = k + 1 := ⟨n_r - 1, by omega⟩
      have h_filt_le_r : (s_c.tokens.filter (fun t => t.val != .placeholder)).size ≤
                         (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp]; exact Nat.le_refl _
      have h_chain_ws_r : ScanChainGrew (fun t => t.val != .placeholder)
            s_c (n_r' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_r h_filt_le_r h_chain_r
      -- Per-step witness for the comma step (s_v → s_c): next char is ','.
      have h_grew_c : (s_c.tokens.filter (fun t => t.val != .placeholder)).size >
                      (s_v.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr_v_cons : ScannerSurfCorr s_v
            ⟨',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s_v.col⟩ := by
          have : [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr_v
        exact scanNextToken_filtered_grows_in_flow s_v s_c ','
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v_cons h_flow_v h_indent_v h_col_v
          (by decide) (by decide) (by decide) h_snt_c
      -- FlowMonoChain: compose all sub-chains
      -- value chain: lift through preprocessing s₂→s₃
      have h_fmc_v' : FlowMonoChain s.flowLevel s₃ (n_v' + 1) s_v :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc_v
      have h_fmc_ws_v : FlowMonoChain s.flowLevel s₂ (n_v' + 1) s_v :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_v (by omega) h_fmc_v'
      -- recursive chain: lift through preprocessing s_c→s_pp
      have h_fmc_r' : FlowMonoChain s.flowLevel s_pp (n_r' + 1) s_end :=
        (show s.flowLevel = s_pp.flowLevel from by omega) ▸ h_fmc_r
      have h_fmc_ws_r : FlowMonoChain s.flowLevel s_c (n_r' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_r (by omega) h_fmc_r'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans
          (h_fmc_ws_v.trans
            ((FlowMonoChain.single h_snt_c (by omega)
              (by omega)).trans h_fmc_ws_r)))
      -- Step 9: Compose strict chains
      -- key(n₁) + colon(1) + space+value(n_v'+1) + comma(1) + space+recurse(n_r'+1)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans
          (h_chain_ws_v.trans
            ((ScanChainGrew.single h_snt_c h_grew_c).trans h_chain_ws_r)))
      have h_arith : n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) =
          n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1) := by omega
      refine ⟨n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1), s_end,
        h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, by omega⟩
      · -- flowLevel preserved
        rw [h_fl_end, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]
      · -- directivesPresent preserved
        rw [h_dp_end, h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁]
      · -- indents preserved
        rw [h_ids_end, h_ids_pp, h_ids_c, h_ids_v, h_ids₃, h_ids₂, h_ids₁]
      · -- explicitKeyLine preserved
        rw [h_ek_end, h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line_pp, _h_line_c, _h_line_v, _h_line₃, _h_line₂, _h_line₁]
      · -- simpleKeyStack preserved
        rw [h_stack_end, h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁]

/-- Every grammable value satisfies `EmitScansInFlow`. -/
theorem emit_scans_in_flow (v : YamlValue) {inFlow : Bool} (hg : Grammable v inFlow) :
    EmitScansInFlow v := by
  induction hg with
  | scalar s _ h =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    -- emit (.scalar s) = "\"" ++ escapeString s.content ++ "\""
    -- Rewrite hcorr to match scanNextToken_flow_scanDoubleQuoted precondition
    have h_chars : (emit (.scalar s)).toList ++ rest =
        ['"'] ++ (escapeString s.content).toList ++ ['"'] ++ rest := by
      simp only [emit, emitScalar, String.toList_append]; rfl
    have hcorr' : ScannerSurfCorr s_state
        ⟨['"'] ++ (escapeString s.content).toList ++ ['"'] ++ rest, s_state.col⟩ := by
      rwa [← h_chars]
    obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_tok', h_ska', _h_line', h_atol', h_endline', h_stack'⟩ :=
      scanNextToken_flow_scanDoubleQuoted s_state s.content rest hcorr' h_flow h_indent h_col
        h_atol (by intro h_poss; exact h_endline h_poss)
    -- Per-step witness for the scalar's scanNextToken call.
    have h_grew : (s'.tokens.filter (fun t => t.val != .placeholder)).size >
                  (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s' '"'
        ((escapeString s.content).toList ++ ['"'] ++ rest)
        (by have : ['"'] ++ (escapeString s.content).toList ++ ['"'] ++ rest =
                    '"' :: ((escapeString s.content).toList ++ ['"'] ++ rest) := by
              simp only [List.cons_append, List.nil_append, List.append_assoc]
            rwa [this] at hcorr')
        h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt
    refine ⟨1, s', ScanChainGrew.single h_snt h_grew, h_corr', h_fl', h_dp', h_ids', h_ek',
      ?_, ?_, ?_, _h_line', h_ska', ?_, ?_, ?_, ?_, ?_⟩
    · exact h_col'
    · unfold ScannerState.inFlow; rw [h_fl']
      unfold ScannerState.inFlow at h_flow; exact h_flow
    · unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent
    · exact h_tok'
    · exact h_atol'
    · exact h_endline'
    · exact h_stack'
    · exact FlowMonoChain.single h_snt (Nat.le.refl) (by omega)
  | sequence style items tag anchor _ h ih =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    -- emit (.sequence ...) = "[" ++ emitList items.toList ++ "]"
    -- Convert: unfold emit and distribute String.toList over ++
    have h_chars : (emit (.sequence style items tag anchor)).toList ++ rest =
        ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    -- hcorr₀ now has ['['] ++ ... which is def-eq to '[' :: ...
    -- Step 1: Scan '[' with nested flow open
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, _h_sk_poss₁, _h_toks_gt₁, _h_stack_push₁⟩ :=
      scanNextToken_flow_open_nested s_state
        ((emit.emitList items.toList).toList ++ [']'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    -- Step 2: Scan emitList body via EmitListScansInFlow
    have h_list_scan : EmitListScansInFlow items.toList := by
      match h_list : items.toList with
      | [] => exact emitList_scans_empty
      | _ :: _ =>
        exact emitList_scans_nonempty _ (by simp) (fun w hw => by
          -- Convert list membership to array index for IH
          have hw' : w ∈ items.toList := h_list ▸ hw
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw'
          have h_sz : i < items.size := by
            rwa [Array.length_toList] at hi
          exact h_eq ▸ ih ⟨i, h_sz⟩)
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂⟩ :=
      h_list_scan s₁ ([']'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
        (by rw [h_ek₁]; exact h_ek)
        h_atol₁ -- AllTokensOnLine s₁ s₁.line (from flow_open_nested postcondition)
        h_endline₁ -- EndLineOnLine s₁ (from flow_open_nested postcondition)
    -- Step 3: Scan ']' with nested close (flowLevel ≥ 2)
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    -- Derive StackEndLineOnLine s₂ s₂.line from open theorem's postcondition
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, _, _⟩ :=
      scanNextToken_flow_close_seq_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    -- Compose: [ (1 step) + list body (n₂ steps) + ] (1 step)
    -- FlowMonoChain: open bracket (fl→fl+1) + body (floor fl+1) + close (fl+1→fl)
    -- The body chain has floor s₁.flowLevel = s_state.flowLevel + 1.
    -- Weaken to s_state.flowLevel, then compose with open/close single steps.
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ :=
      h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
        (h_fmc₂'.trans
          (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    -- Per-step witnesses: '[' (s_state → s₁) and ']' (s₂ → s₃).
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest), s_state.col⟩ := by
        have : ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest =
            '[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      exact scanNextToken_filtered_grows_in_flow s_state s₁ '['
        ((emit.emitList items.toList).toList ++ [']'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col
        (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨']' :: rest, s₂.col⟩ := by
        have : [']'] ++ rest = ']' :: rest := by simp
        rwa [this] at h_corr₂
      exact scanNextToken_filtered_grows_in_flow s₂ s₃ ']' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
        (by decide) (by decide) (by decide) h_snt₃
    refine ⟨(1 + n₂) + 1, s₃,
      (ScanChainGrew.single h_snt₁ h_grew₁).trans
        (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all⟩
    · -- flowLevel: (fl+1) - 1 = fl
      rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · -- explicitKeyLine preserved
      rw [h_ek₃, h_ek₂, h_ek₁]
    · -- col > 0
      rw [h_col₃]; omega
    · -- inFlow
      unfold ScannerState.inFlow
      exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · -- currentIndent
      unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · -- line preserved
      rw [_h_line₃, _h_line₂, _h_line₁]
    · -- AllTokensOnLine s₃ s₃.line (from close theorem postcondition)
      exact h_atol₃
    · -- EndLineOnLine s₃ (from close theorem postcondition)
      exact h_endline₃
    · -- simpleKeyStack: s₃.simpleKeyStack = s_state.simpleKeyStack
      -- Chain: close pops → list preserved → open pushed then pop cancels
      rw [h_stack₃, h_stack₂, h_stack_pop₁]
  | mapping style pairs tag anchor _ hk hv ihk ihv =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    -- emit (.mapping ...) = "{" ++ emitPairList pairs.toList ++ "}"
    have h_chars : (emit (.mapping style pairs tag anchor)).toList ++ rest =
        ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    -- Step 1: Scan '{' with nested flow open
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, _h_sk_poss₁, _h_toks_gt₁, _h_stack_push₁⟩ :=
      scanNextToken_flow_open_mapping_nested s_state
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    -- Step 2: Scan emitPairList body via EmitPairListScansInFlow
    have h_pair_scan : EmitPairListScansInFlow pairs.toList := by
      match h_list : pairs.toList with
      | [] => exact emitPairList_scans_empty
      | _ :: _ =>
        exact (emitPairList_scans_nonempty _ (by simp) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ ihk ⟨i, h_sz⟩) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ ihv ⟨i, h_sz⟩)).toWeak
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂⟩ :=
      h_pair_scan s₁ (['}'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
        (by rw [h_ek₁]; exact h_ek)
        h_atol₁
        h_endline₁ -- EndLineOnLine s₁ (from flow_open_mapping_nested postcondition)
    -- Step 3: Scan '}' with nested close (flowLevel ≥ 2)
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    -- Derive StackEndLineOnLine s₂ s₂.line from open theorem's postcondition
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, _, _⟩ :=
      scanNextToken_flow_close_mapping_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    -- Compose: { (1 step) + pair body (n₂ steps) + } (1 step)
    -- FlowMonoChain: open brace (fl→fl+1) + body (floor fl+1) + close (fl+1→fl)
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ :=
      h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
        (h_fmc₂'.trans
          (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    -- Per-step witnesses: '{' (s_state → s₁) and '}' (s₂ → s₃).
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest), s_state.col⟩ := by
        have : ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest =
            '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      exact scanNextToken_filtered_grows_in_flow s_state s₁ '{'
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col
        (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨'}' :: rest, s₂.col⟩ := by
        have : ['}'] ++ rest = '}' :: rest := by simp
        rwa [this] at h_corr₂
      exact scanNextToken_filtered_grows_in_flow s₂ s₃ '}' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
        (by decide) (by decide) (by decide) h_snt₃
    refine ⟨(1 + n₂) + 1, s₃,
      (ScanChainGrew.single h_snt₁ h_grew₁).trans
        (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all⟩
    · rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · -- explicitKeyLine preserved
      rw [h_ek₃, h_ek₂, h_ek₁]
    · rw [h_col₃]; omega
    · unfold ScannerState.inFlow
      exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · -- line preserved
      rw [_h_line₃, _h_line₂, _h_line₁]
    · -- AllTokensOnLine s₃ s₃.line (from close theorem postcondition)
      exact h_atol₃
    · -- EndLineOnLine s₃ (from close theorem postcondition)
      exact h_endline₃
    · -- simpleKeyStack: s₃.simpleKeyStack = s_state.simpleKeyStack
      rw [h_stack₃, h_stack₂, h_stack_pop₁]

/-! ## Saved-key survival across a key-node scan (`.body1.tokenshape.pair.keyshape`)

`EmitScansInFlowSavedKey v` is the substrate that closes legacy sorry 9644
(`emitPairList`'s first new filtered token is `.key`).  It states that scanning
`emit v` in flow context, starting from a state where a simple key is *allowed*
(`simpleKeyAllowed = true`, `simpleKey.possible = false`, stack synced to the
flow level), leaves the saved key **alive at its reserved slot**:
`s'.simpleKey.possible = true ∧ s'.simpleKey.tokenIndex = s.tokens.size`, with
raw slot `N = s.tokens.size` still a `.placeholder`.

The crux is composite nodes: the opening `[`/`{` reserves the key at `N` via
`saveSimpleKey`, then *pushes* it onto the simple-key stack (the inner level
starts fresh).  The body preserves the whole stack and never touches slot `N`
(its reservations are above the floor `s.flowLevel + 1`).  The closing `]`/`}`
*restores* the simple key from the popped stack top — exactly the saved key at
`N`.  Scalars are the easy base case: `saveSimpleKey` reserves at `N`,
`scanDoubleQuoted` preserves the simple key, so the key survives directly.

This is a *new* invariant (exact-`tokenIndex` survival), distinct from
`SimpleKeyAboveFloor`'s `≥ n` lower bound and from the `SavedKeyDoesntResolve`
non-resolution witness used by `.tokenshape.list.discharge`. -/

/-- `saveSimpleKey` reserves a `.placeholder` at the old token-array size when
    a simple key is allowed and no explicit key is pending. -/
theorem saveSimpleKey_getElem?_size (s : ScannerState)
    (h_ek : s.explicitKeyLine = none) (h_ska : s.simpleKeyAllowed = true) :
    (saveSimpleKey s).tokens[s.tokens.size]? = some ⟨s.currentPos, .placeholder, s.currentPos⟩ := by
  unfold saveSimpleKey
  have h_guard : (s.inFlow && s.explicitKeyLine == some s.line) = false := by rw [h_ek]; simp
  simp only [h_guard, Bool.false_eq_true, ↓reduceIte, h_ska]
  simp [Array.getElem?_push, Array.size_push]

/-- `saveSimpleKey` reserves a *second* `.placeholder` at `N + 1` (the spare slot)
    when a simple key is allowed and no explicit key is pending.  Companion to
    `saveSimpleKey_getElem?_size`: both slots `N`, `N + 1` are placeholders, which
    is what the colon's retroactive `.set` of `.key` at `tokenIndex + 1 = N + 1`
    relies on to be a clean filtered-list insertion. -/
theorem saveSimpleKey_getElem?_size_succ (s : ScannerState)
    (h_ek : s.explicitKeyLine = none) (h_ska : s.simpleKeyAllowed = true) :
    (saveSimpleKey s).tokens[s.tokens.size + 1]? = some ⟨s.currentPos, .placeholder, s.currentPos⟩ := by
  unfold saveSimpleKey
  have h_guard : (s.inFlow && s.explicitKeyLine == some s.line) = false := by rw [h_ek]; simp
  simp only [h_guard, Bool.false_eq_true, ↓reduceIte, h_ska]
  -- index N+1 is exactly the size of the inner push, so the outer push hits it
  rw [Array.getElem?_push, if_pos (by rw [Array.size_push])]

/-- Scalar key head facts: scanning a double-quoted scalar in flow from
    `simpleKeyAllowed = true` leaves the saved key alive at slot `N`. -/
theorem scanNextToken_flow_scalar_savedKey (s : ScannerState)
    (content : String) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none) (h_ska : s.simpleKeyAllowed = true) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.simpleKey.possible = true
      ∧ s'.simpleKey.tokenIndex = s.tokens.size
      ∧ s.tokens.size + 1 < s'.tokens.size
      ∧ (∀ (h : s.tokens.size < s'.tokens.size),
          (s'.tokens[s.tokens.size]'h).val = .placeholder)
      ∧ (∀ (h : s.tokens.size + 1 < s'.tokens.size),
          (s'.tokens[s.tokens.size + 1]'h).val = .placeholder) := by
  obtain ⟨h_skp, h_skt, _h_sks, h_skz⟩ := saveSimpleKey_eval s h_ek h_ska
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have hcorr' : ScannerSurfCorr s ⟨'"' :: ((escapeString content).toList ++ ['"'] ++ rest), s.col⟩ := by
    have : ['"'] ++ (escapeString content).toList ++ ['"'] ++ rest =
        '"' :: ((escapeString content).toList ++ ['"'] ++ rest) := by
      simp only [List.cons_append, List.nil_append, List.append_assoc]
    rwa [this] at hcorr
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
    scanNextToken_preprocess_flow s '"' ((escapeString content).toList ++ ['"'] ++ rest) s.col
      hcorr' h_flow (by decide) (by decide) (by decide)
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
    else saveSimpleKey s
  have h_ad_sk : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by simp only [s_ad]; split <;> rfl
  have h_ad_tokens : s_ad.tokens = (saveSimpleKey s).tokens := by simp only [s_ad]; split <;> rfl
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_flow_true : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '"' h_ad_flow_true
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  -- s_ad corr (transfer through saveSimpleKey + allowDirectives, which preserve input geometry)
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, s_ad.col⟩ := by
    rw [h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  obtain ⟨s_dq, h_dq_eq, _, _, _, _, _, _, _, _, _⟩ :=
    scanDoubleQuoted_flow_ok s_ad content rest h_ad_corr h_ad_flow_true
  have h_sdq_sk : s_dq.simpleKey = s_ad.simpleKey :=
    ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s_ad s_dq h_dq_eq
  have h_sdq_poss : s_dq.simpleKey.possible = true := by rw [h_sdq_sk, h_ad_sk]; exact h_skp
  obtain ⟨ct, h_dq_tok⟩ := scanDoubleQuoted_tokens_push h_dq_eq
  have h_dc : scanNextToken_dispatchContent s_ad '"' = Except.ok
      { s_dq with simpleKey := { s_dq.simpleKey with endLine := s_dq.line } } := by
    unfold scanNextToken_dispatchContent
    simp [bind, Except.bind, pure, Except.pure, h_dq_eq, h_sdq_poss]
  have h_snt : scanNextToken s = Except.ok (some
      { s_dq with simpleKey := { s_dq.simpleKey with endLine := s_dq.line } }) :=
    scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl h_check
      h_flow_none h_block_none h_dc
  refine ⟨_, h_snt, ?_, ?_, ?_, ?_, ?_⟩
  · show s_dq.simpleKey.possible = true
    exact h_sdq_poss
  · show s_dq.simpleKey.tokenIndex = s.tokens.size
    rw [h_sdq_sk, h_ad_sk]; exact h_skt
  · show s.tokens.size + 1 < s_dq.tokens.size
    rw [h_dq_tok, Array.size_push, h_ad_tokens, h_skz]; omega
  · intro h
    have h_ad_lt : s.tokens.size < s_ad.tokens.size := by rw [h_ad_tokens, h_skz]; omega
    -- raw[N] = placeholder, via getElem? to dodge dependent-index rewrites
    have h_get? : s_dq.tokens[s.tokens.size]? = some ⟨s.currentPos, .placeholder, s.currentPos⟩ := by
      rw [h_dq_tok, Array.getElem?_push, if_neg (by omega : s.tokens.size ≠ s_ad.tokens.size), h_ad_tokens]
      exact saveSimpleKey_getElem?_size s h_ek h_ska
    have h_some : s_dq.tokens[s.tokens.size]? = some (s_dq.tokens[s.tokens.size]'h) :=
      Array.getElem?_eq_getElem h
    have := Option.some.inj (h_some.symm.trans h_get?)
    show (s_dq.tokens[s.tokens.size]'h).val = .placeholder
    rw [this]
  · intro h
    have h_ad_lt : s.tokens.size + 1 < s_ad.tokens.size := by rw [h_ad_tokens, h_skz]; omega
    -- raw[N+1] = placeholder (the spare slot), same getElem? routing as raw[N]
    have h_get? : s_dq.tokens[s.tokens.size + 1]? = some ⟨s.currentPos, .placeholder, s.currentPos⟩ := by
      rw [h_dq_tok, Array.getElem?_push, if_neg (by omega : s.tokens.size + 1 ≠ s_ad.tokens.size), h_ad_tokens]
      exact saveSimpleKey_getElem?_size_succ s h_ek h_ska
    have h_some : s_dq.tokens[s.tokens.size + 1]? = some (s_dq.tokens[s.tokens.size + 1]'h) :=
      Array.getElem?_eq_getElem h
    have := Option.some.inj (h_some.symm.trans h_get?)
    show (s_dq.tokens[s.tokens.size + 1]'h).val = .placeholder
    rw [this]

/-- Flow `[` open with a saved key: reserves the key placeholder at slot `N`
    and emits `.flowSequenceStart` at `N + 2`, so `tokens[N] = .placeholder`. -/
theorem scanNextToken_flow_open_seq_savedKey (s s' : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none) (h_ska : s.simpleKeyAllowed = true)
    (h_snt : scanNextToken s = .ok (some s')) :
    s'.tokens.size = s.tokens.size + 3 ∧
    s'.tokens[s.tokens.size]? = some ⟨s.currentPos, .placeholder, s.currentPos⟩ ∧
    s'.tokens[s.tokens.size + 1]? = some ⟨s.currentPos, .placeholder, s.currentPos⟩ := by
  obtain ⟨_, _h_skt, _, h_skz⟩ := saveSimpleKey_eval s h_ek h_ska
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true } else saveSimpleKey s
  have h_ad_tokens : s_ad.tokens = (saveSimpleKey s).tokens := by simp only [s_ad]; split <;> rfl
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
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
  obtain ⟨tok, h_tok⟩ : ∃ tok, (scanFlowSequenceStart s_ad).tokens = s_ad.tokens.push tok :=
    ⟨_, by unfold scanFlowSequenceStart ScannerState.emit; rw [ScannerCorrectness.advance_preserves_tokens]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h_s', ScannerCorrectness.scanFlowSequenceStart_adds_one_token, h_ad_tokens, h_skz]
  · rw [h_s', h_tok, Array.getElem?_push,
        if_neg (by rw [h_ad_tokens, h_skz]; omega : s.tokens.size ≠ s_ad.tokens.size), h_ad_tokens]
    exact saveSimpleKey_getElem?_size s h_ek h_ska
  · rw [h_s', h_tok, Array.getElem?_push,
        if_neg (by rw [h_ad_tokens, h_skz]; omega : s.tokens.size + 1 ≠ s_ad.tokens.size), h_ad_tokens]
    exact saveSimpleKey_getElem?_size_succ s h_ek h_ska

/-- Flow `{` open with a saved key (mapping analogue of the above). -/
theorem scanNextToken_flow_open_mapping_savedKey (s s' : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none) (h_ska : s.simpleKeyAllowed = true)
    (h_snt : scanNextToken s = .ok (some s')) :
    s'.tokens.size = s.tokens.size + 3 ∧
    s'.tokens[s.tokens.size]? = some ⟨s.currentPos, .placeholder, s.currentPos⟩ ∧
    s'.tokens[s.tokens.size + 1]? = some ⟨s.currentPos, .placeholder, s.currentPos⟩ := by
  obtain ⟨_, _h_skt, _, h_skz⟩ := saveSimpleKey_eval s h_ek h_ska
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true } else saveSimpleKey s
  have h_ad_tokens : s_ad.tokens = (saveSimpleKey s).tokens := by simp only [s_ad]; split <;> rfl
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
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
  obtain ⟨tok, h_tok⟩ : ∃ tok, (scanFlowMappingStart s_ad).tokens = s_ad.tokens.push tok :=
    ⟨_, by unfold scanFlowMappingStart ScannerState.emit; rw [ScannerCorrectness.advance_preserves_tokens]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h_s', ScannerCorrectness.scanFlowMappingStart_adds_one_token, h_ad_tokens, h_skz]
  · rw [h_s', h_tok, Array.getElem?_push,
        if_neg (by rw [h_ad_tokens, h_skz]; omega : s.tokens.size ≠ s_ad.tokens.size), h_ad_tokens]
    exact saveSimpleKey_getElem?_size s h_ek h_ska
  · rw [h_s', h_tok, Array.getElem?_push,
        if_neg (by rw [h_ad_tokens, h_skz]; omega : s.tokens.size + 1 ≠ s_ad.tokens.size), h_ad_tokens]
    exact saveSimpleKey_getElem?_size_succ s h_ek h_ska

/-- `EmitScansInFlowSavedKey v`: scanning `emit v` in flow from a state where a
    simple key is allowed leaves the saved key alive at its reserved slot `N`. -/
def EmitScansInFlowSavedKey (v : YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit v).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    s.simpleKeyAllowed = true →
    s.simpleKey.possible = false →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.simpleKey.possible = true
      ∧ s'.simpleKey.tokenIndex = s.tokens.size
      ∧ s.tokens.size + 1 < s'.tokens.size
      ∧ (∀ (h : s.tokens.size < s'.tokens.size),
          (s'.tokens[s.tokens.size]'h).val = .placeholder)
      ∧ (∀ (h : s.tokens.size + 1 < s'.tokens.size),
          (s'.tokens[s.tokens.size + 1]'h).val = .placeholder)

/-- Producer for `EmitScansInFlowSavedKey` by induction on `Grammable v inFlow`.
    Scalars survive directly; composites push the saved key on `[`/`{`, preserve
    it across the body, and restore it on `]`/`}`. -/
theorem emit_scans_in_flow_saved_key (v : YamlValue) {inFlow : Bool} (hg : Grammable v inFlow) :
    EmitScansInFlowSavedKey v := by
  induction hg with
  | scalar sc _ h =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sk h_sync
    have h_chars : (emit (.scalar sc)).toList ++ rest =
        ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest := by
      simp only [emit, emitScalar, String.toList_append]; rfl
    have hcorr' : ScannerSurfCorr s_state
        ⟨['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest, s_state.col⟩ := by
      rwa [← h_chars]
    obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_tok', h_ska', _h_line', h_atol', h_endline', h_stack'⟩ :=
      scanNextToken_flow_scanDoubleQuoted s_state sc.content rest hcorr' h_flow h_indent h_col
        h_atol (by intro h_poss; exact h_endline h_poss)
    obtain ⟨s'', h_snt'', h_poss'', h_tidx'', h_size'', h_ph'', h_ph1''⟩ :=
      scanNextToken_flow_scalar_savedKey s_state sc.content rest hcorr' h_flow h_indent h_col h_ek h_ska
    have h_eq : s'' = s' := Option.some.inj (Except.ok.inj (h_snt''.symm.trans h_snt))
    subst h_eq
    have h_grew : (s''.tokens.filter (fun t => t.val != .placeholder)).size >
                  (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s'' '"'
        ((escapeString sc.content).toList ++ ['"'] ++ rest)
        (by have : ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest =
                    '"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest) := by
              simp only [List.cons_append, List.nil_append, List.append_assoc]
            rwa [this] at hcorr')
        h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt''
    refine ⟨1, s'', ScanChainGrew.single h_snt'' h_grew, h_corr', h_fl', h_dp', h_ids', h_ek',
      h_col', ?_, ?_, _h_line', h_atol', h_endline', h_stack',
      FlowMonoChain.single h_snt'' (Nat.le.refl) (by omega),
      h_ska', h_poss'', h_tidx'', h_size'', h_ph'', h_ph1''⟩
    · unfold ScannerState.inFlow; rw [h_fl']
      unfold ScannerState.inFlow at h_flow; exact h_flow
    · unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent
  | sequence style items tag anchor _ h _ih =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sk h_sync
    have h_chars : (emit (.sequence style items tag anchor)).toList ++ rest =
        ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    have h_corr_state_cons : ScannerSurfCorr s_state
        ⟨'[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest), s_state.col⟩ := by
      have : ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest =
          '[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      rwa [this] at hcorr₀
    obtain ⟨_h_skp, _h_skt, _, _⟩ := saveSimpleKey_eval s_state h_ek h_ska
    -- Step 1: open '['
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
      scanNextToken_flow_open_nested s_state
        ((emit.emitList items.toList).toList ++ [']'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    obtain ⟨h_s1_size, h_s1_rawN, h_s1_rawN1⟩ :=
      scanNextToken_flow_open_seq_savedKey s_state s₁ ((emit.emitList items.toList).toList ++ [']'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col h_ek h_ska h_snt₁
    have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    -- Step 2: body via EmitListScansInFlow
    have h_list_scan : EmitListScansInFlow items.toList := by
      match h_list : items.toList with
      | [] => exact emitList_scans_empty
      | _ :: _ =>
        exact emitList_scans_nonempty _ (by simp) (fun w hw => by
          have hw' : w ∈ items.toList := h_list ▸ hw
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw'
          have h_sz : i < items.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow _ (h ⟨i, h_sz⟩))
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂⟩ :=
      h_list_scan s₁ ([']'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
        (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
    -- body preserves raw prefix [0..N+1): floor s₁.flowLevel excludes the frozen key at index s.flowLevel
    have h_stack_size₁ : s₁.simpleKeyStack.size = s₁.flowLevel := by
      rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
    have h_skaf₁ : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 1) s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_body_rawN : s₂.tokens[s_state.tokens.size]? = s₁.tokens[s_state.tokens.size]? := by
      have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 1)
        (by omega) h_skaf₁ (by omega) s_state.tokens.size (by omega)
      rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
          Array.getElem?_eq_getElem (by omega), h_eq]
    -- raw[N+1] preserved across the body (same floor argument, both key clauses vacuous)
    have h_skaf₁' : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 2) s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_body_rawN1 : s₂.tokens[s_state.tokens.size + 1]? = s₁.tokens[s_state.tokens.size + 1]? := by
      have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 2)
        (by omega) h_skaf₁' (by omega) (s_state.tokens.size + 1) (by omega)
      rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
          Array.getElem?_eq_getElem (by omega), h_eq]
    -- Step 3: close ']'
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, h_skrestore₃, h_prefix₃⟩ :=
      scanNextToken_flow_close_seq_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    -- assemble chain + FlowMonoChain (as in emit_scans_in_flow)
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
        (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s₁ '['
        ((emit.emitList items.toList).toList ++ [']'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨']' :: rest, s₂.col⟩ := by
        have : [']'] ++ rest = ']' :: rest := by simp
        rwa [this] at h_corr₂
      exact scanNextToken_filtered_grows_in_flow s₂ s₃ ']' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
    -- survival: simpleKey restored to the saved key at N
    have h_skey_eq : s₃.simpleKey = (saveSimpleKey s_state).simpleKey := by
      rw [h_skrestore₃, h_stack₂, h_stack_push₁]; simp [Array.back?_push]
    have h_close_mono : s₂.tokens.size ≤ s₃.tokens.size := by
      have := ScannerCorrectness.scanNextToken_adds_tokens s₂ s₃ h_snt₃; omega
    have h_body_mono : s₁.tokens.size ≤ s₂.tokens.size := h_fmc₂.tokens_mono
    -- raw[N] = placeholder at s₃
    have h_s3_rawN? : s₃.tokens[s_state.tokens.size]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
      rw [h_prefix₃ s_state.tokens.size (by omega), h_body_rawN, h_s1_rawN]
    have h_s3_rawN1? : s₃.tokens[s_state.tokens.size + 1]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
      rw [h_prefix₃ (s_state.tokens.size + 1) (by omega), h_body_rawN1, h_s1_rawN1]
    refine ⟨(1 + n₂) + 1, s₃,
      (ScanChainGrew.single h_snt₁ h_grew₁).trans
        (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_atol₃, h_endline₃, ?_, h_fmc_all,
      h_ska₃, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · rw [h_ek₃, h_ek₂, h_ek₁]
    · rw [h_col₃]; omega
    · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · rw [_h_line₃, _h_line₂, _h_line₁]
    · rw [h_stack₃, h_stack₂, h_stack_pop₁]
    · -- simpleKey.possible = true
      rw [h_skey_eq]; exact _h_skp
    · -- tokenIndex = N
      rw [h_skey_eq]; exact _h_skt
    · -- N+1 < s₃.tokens.size
      omega
    · -- raw[N] = placeholder
      intro h
      have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'h) :=
        Array.getElem?_eq_getElem h
      have := Option.some.inj (h_some.symm.trans h_s3_rawN?)
      rw [this]
    · -- raw[N+1] = placeholder
      intro h
      have h_some : s₃.tokens[s_state.tokens.size + 1]? = some (s₃.tokens[s_state.tokens.size + 1]'h) :=
        Array.getElem?_eq_getElem h
      have := Option.some.inj (h_some.symm.trans h_s3_rawN1?)
      rw [this]
  | mapping style pairs tag anchor _ hk hv _ihk _ihv =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sk h_sync
    have h_chars : (emit (.mapping style pairs tag anchor)).toList ++ rest =
        ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    have h_corr_state_cons : ScannerSurfCorr s_state
        ⟨'{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest), s_state.col⟩ := by
      have : ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest =
          '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      rwa [this] at hcorr₀
    obtain ⟨_h_skp, _h_skt, _, _⟩ := saveSimpleKey_eval s_state h_ek h_ska
    -- Step 1: open '{'
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, h_sk_poss₁, _h_toks_gt₁, h_stack_push₁⟩ :=
      scanNextToken_flow_open_mapping_nested s_state
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    obtain ⟨h_s1_size, h_s1_rawN, h_s1_rawN1⟩ :=
      scanNextToken_flow_open_mapping_savedKey s_state s₁ ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col h_ek h_ska h_snt₁
    have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    -- Step 2: body via EmitPairListScansInFlow
    have h_pair_scan : EmitPairListScansInFlow pairs.toList := by
      match h_list : pairs.toList with
      | [] => exact emitPairList_scans_empty
      | _ :: _ =>
        exact (emitPairList_scans_nonempty _ (by simp) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow _ (hk ⟨i, h_sz⟩)) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow _ (hv ⟨i, h_sz⟩))).toWeak
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂⟩ :=
      h_pair_scan s₁ (['}'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
        (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
    have h_stack_size₁ : s₁.simpleKeyStack.size = s₁.flowLevel := by
      rw [h_stack_push₁, Array.size_push, h_sync, h_fl₁]
    have h_skaf₁ : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 1) s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_body_rawN : s₂.tokens[s_state.tokens.size]? = s₁.tokens[s_state.tokens.size]? := by
      have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 1)
        (by omega) h_skaf₁ (by omega) s_state.tokens.size (by omega)
      rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
          Array.getElem?_eq_getElem (by omega), h_eq]
    have h_skaf₁' : SimpleKeyAboveFloor s₁ (s_state.tokens.size + 2) s₁.flowLevel := by
      refine ⟨fun hp => by rw [h_sk_poss₁] at hp; exact absurd hp (by decide),
        fun j hj hjb _ => by exfalso; omega, by omega⟩
    have h_body_rawN1 : s₂.tokens[s_state.tokens.size + 1]? = s₁.tokens[s_state.tokens.size + 1]? := by
      have h_eq := FlowMonoChain_preserves_raw_prefix h_fmc₂ (s_state.tokens.size + 2)
        (by omega) h_skaf₁' (by omega) (s_state.tokens.size + 1) (by omega)
      rw [Array.getElem?_eq_getElem (by have := h_fmc₂.tokens_mono; omega),
          Array.getElem?_eq_getElem (by omega), h_eq]
    -- Step 3: close '}'
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, h_skrestore₃, h_prefix₃⟩ :=
      scanNextToken_flow_close_mapping_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
        (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s₁ '{'
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨'}' :: rest, s₂.col⟩ := by
        have : ['}'] ++ rest = '}' :: rest := by simp
        rwa [this] at h_corr₂
      exact scanNextToken_filtered_grows_in_flow s₂ s₃ '}' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
    have h_skey_eq : s₃.simpleKey = (saveSimpleKey s_state).simpleKey := by
      rw [h_skrestore₃, h_stack₂, h_stack_push₁]; simp [Array.back?_push]
    have h_close_mono : s₂.tokens.size ≤ s₃.tokens.size := by
      have := ScannerCorrectness.scanNextToken_adds_tokens s₂ s₃ h_snt₃; omega
    have h_body_mono : s₁.tokens.size ≤ s₂.tokens.size := h_fmc₂.tokens_mono
    have h_s3_rawN? : s₃.tokens[s_state.tokens.size]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
      rw [h_prefix₃ s_state.tokens.size (by omega), h_body_rawN, h_s1_rawN]
    have h_s3_rawN1? : s₃.tokens[s_state.tokens.size + 1]? = some ⟨s_state.currentPos, .placeholder, s_state.currentPos⟩ := by
      rw [h_prefix₃ (s_state.tokens.size + 1) (by omega), h_body_rawN1, h_s1_rawN1]
    refine ⟨(1 + n₂) + 1, s₃,
      (ScanChainGrew.single h_snt₁ h_grew₁).trans
        (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_atol₃, h_endline₃, ?_, h_fmc_all,
      h_ska₃, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · rw [h_ek₃, h_ek₂, h_ek₁]
    · rw [h_col₃]; omega
    · unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · rw [_h_line₃, _h_line₂, _h_line₁]
    · rw [h_stack₃, h_stack₂, h_stack_pop₁]
    · rw [h_skey_eq]; exact _h_skp
    · rw [h_skey_eq]; exact _h_skt
    · omega
    · intro h
      have h_some : s₃.tokens[s_state.tokens.size]? = some (s₃.tokens[s_state.tokens.size]'h) :=
        Array.getElem?_eq_getElem h
      have := Option.some.inj (h_some.symm.trans h_s3_rawN?)
      rw [this]
    · intro h
      have h_some : s₃.tokens[s_state.tokens.size + 1]? = some (s₃.tokens[s_state.tokens.size + 1]'h) :=
        Array.getElem?_eq_getElem h
      have := Option.some.inj (h_some.symm.trans h_s3_rawN1?)
      rw [this]

/-! ## `emitList`/`emitPairList` scanning WITH a `SavedKeyDoesntResolve` witness
    (substrate-consuming, `.body1.tokenshape.list.establishing`)

This section ships `emitList_scans_nonempty_with_skdr`: a parallel theorem to
`emitList_scans_nonempty` that, in addition to the existing `FlowMonoChain`
witness and scanner invariants, produces a
`SavedKeyDoesntResolve s.flowLevel s.tokens.size s n s'` witness — i.e. evidence
that scanning the flow-sequence body never lets a saved key resolve at raw
position `N = s.tokens.size`, so raw position `N + 1` is preserved across the
whole body chain. This is the witness the downstream `.discharge` session feeds
to `SavedKeyDoesntResolve_preserves_position_target` (substrate.f §F.3).

**Construction strategy (per Reflection 162's hybrid plan).** The SKDR witness is
built step-by-step over the *same* chain structure as `emitList_scans_nonempty`,
classifying each `scanNextToken` step:

  - **non-`:` steps** — every structural / bracket / comma / scalar-head / content
    step.  Handled uniformly by substrate.g's
    `scanNextToken_at_non_colon_preserves_positions` (the dispatched char is not
    `:`, so position `N + 1` is preserved *unconditionally*, even at the
    delicate comma-after-scalar boundary where the saved key sits at `tokenIndex
    = N`).  Packaged as `SavedKeyDoesntResolve.step_of_non_colon`.
  - **`:` steps** — only the value-colon inside a *nested* flow mapping.  There
    the saved key sits at `tokenIndex ≥ N + 1 > N`, so substrate.f's
    `step_of_tokenIndex_ne` applies.  The `tokenIndex ≠ N` side-condition is
    discharged from substrate.d's `NoOverwriteAt (N + 1)` invariant, which is
    *re-established after each flow-open* (where the body's start size already
    exceeds `N + 1`) and maintained across the key-scan sub-chain by
    `scanNextToken_maintains_NoOverwriteAt`.

The recursion mirrors `emit_scans_in_flow` over `Grammable`'s three constructors,
threading the fixed protected target `n_target` (never the per-call size).

**Closes zero legacy sorries**: pure enablement for `.tokenshape.list.discharge`. -/

/-! ### §H.0  Keyshape first-token transfer (`.keyshape.discharge`, sorry 9644) -/

/-- Part-2 transfer for `.keyshape.discharge`.  Given the post-key state `s₁`
    (saved key alive at slot `N := s.tokens.size`, with `raw[N] = .placeholder`),
    the post-colon state `s₂` (`raw[N+1] = .key`, simple key cleared, stack synced),
    a residual `FlowMonoChain` `s₂ → s_end`, and the full chain `s → s_end`, the first
    new filtered token of `s_end` (at index `old_sz`) is `.key`.

    The colon converted slot `N+1` from a placeholder to `.key`; slot `N` stays a
    placeholder.  The residual chain never overwrites `N`/`N+1` (no stacked key targets
    them — `SimpleKeyStackValid` pins them strictly below `N`), and the bulk prefix
    `[0..N)` is preserved by the full chain.  A reference array `s.tokens ++ [ph, .key]`
    transfers the filtered token via `Array_filter_getElem_of_raw_prefix`. -/
theorem keyshape_first_token_key
    {n_all n_resid : Nat} (s s₁ s₂ s_end : ScannerState)
    (h_sk : s.simpleKey.possible = false)
    (h_sync : s.simpleKeyStack.size = s.flowLevel)
    (h_ssv : ScannerCorrectness.SimpleKeyStackValid s)
    (h_fl : s.flowLevel > 0)
    (h_fmc_all : FlowMonoChain s.flowLevel s n_all s_end)
    (h_fmc_resid : FlowMonoChain s.flowLevel s₂ n_resid s_end)
    (h_sz₁ : s.tokens.size + 1 < s₁.tokens.size)
    (h_ph₁ : ∀ (h : s.tokens.size < s₁.tokens.size),
        (s₁.tokens[s.tokens.size]'h).val = .placeholder)
    (h_stack₂ : s₂.simpleKeyStack = s.simpleKeyStack)
    (h_sk2_poss : s₂.simpleKey.possible = false)
    (h_key2 : s₂.tokens[s.tokens.size + 1]? =
        some ⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩)
    (h_pres2 : ∀ i, i < s₁.tokens.size → i ≠ s.tokens.size + 1 →
        s₂.tokens[i]? = s₁.tokens[i]?) :
    ∀ (h : (s.tokens.filter (fun t => t.val != .placeholder)).size <
           (s_end.tokens.filter (fun t => t.val != .placeholder)).size),
      ((s_end.tokens.filter (fun t => t.val != .placeholder))[
        (s.tokens.filter (fun t => t.val != .placeholder)).size]'h).val = .key := by
  intro h_old_lt
  -- s₂ has `N+1` in bounds (from `h_key2 = some`), hence `N` too.
  have h_N1_lt2 : s.tokens.size + 1 < s₂.tokens.size := by
    rcases Nat.lt_or_ge (s.tokens.size + 1) s₂.tokens.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at h_key2; exact absurd h_key2 (by simp)
  have h_N_lt2 : s.tokens.size < s₂.tokens.size := by omega
  -- No stacked key targets a position `≥ N` (SimpleKeyStackValid pins them `< N`).
  have h_fno : ∀ m, s.tokens.size ≤ m → FlowNoOverwriteAt s₂ m := fun m hm =>
    ⟨fun hp => absurd hp (by rw [h_sk2_poss]; decide),
     fun j hj hpos => by
       simp only [h_stack₂] at hj hpos ⊢
       have hv := (h_ssv j hj hpos).2.1
       omega⟩
  -- Residual chain preserves slots `N` and `N+1`.
  obtain ⟨h_N_lt_end, h_N_eq⟩ :=
    FlowMonoChain_preserves_position_specific_flow (by omega) h_fmc_resid s.tokens.size h_N_lt2
      (h_fno s.tokens.size (Nat.le_refl _))
  obtain ⟨h_N1_lt_end, h_N1_eq⟩ :=
    FlowMonoChain_preserves_position_specific_flow (by omega) h_fmc_resid (s.tokens.size + 1) h_N1_lt2
      (h_fno (s.tokens.size + 1) (by omega))
  -- Value facts at `s_end`: slot `N` placeholder, slot `N+1` `.key`.
  have h_endN_ph : (s_end.tokens[s.tokens.size]'h_N_lt_end).val = .placeholder := by
    rw [h_N_eq]
    have e : s₂.tokens[s.tokens.size]'h_N_lt2 = s₁.tokens[s.tokens.size]'(by omega) :=
      Option.some.inj
        ((Array.getElem?_eq_getElem h_N_lt2).symm.trans
          ((h_pres2 s.tokens.size (by omega) (by omega)).trans (Array.getElem?_eq_getElem (by omega))))
    rw [e]; exact h_ph₁ _
  have h_endN1_key : (s_end.tokens[s.tokens.size + 1]'h_N1_lt_end).val = .key := by
    rw [h_N1_eq]
    have e : s₂.tokens[s.tokens.size + 1]'h_N1_lt2 = ⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ :=
      Option.some.inj ((Array.getElem?_eq_getElem h_N1_lt2).symm.trans h_key2)
    rw [e]
  -- Bulk prefix `[0..N)` of `s_end` agrees with `s` (SimpleKeyAboveFloor floor).
  have h_prefix : ∀ i (hi : i < s.tokens.size), s_end.tokens[i]'(by
      have := FlowMonoChain.tokens_mono h_fmc_all; omega) = s.tokens[i]'hi := by
    intro i hi
    exact FlowMonoChain_preserves_raw_prefix h_fmc_all s.tokens.size (Nat.le_refl _)
      ⟨fun hpp => absurd hpp (by rw [h_sk]; decide),
       fun j hjf hj _ => by exfalso; rw [h_sync] at hj; omega,
       Nat.le_of_eq h_sync.symm⟩
      (Nat.le_of_eq h_sync.symm) i hi
  -- Reference array `s.tokens ++ [tokN, tokN1]` whose filter pins `.key` at `old_sz`.
  obtain ⟨tokN, htokN_def⟩ :
      ∃ x, x = s_end.tokens[s.tokens.size]'h_N_lt_end := ⟨_, rfl⟩
  obtain ⟨tokN1, htokN1_def⟩ :
      ∃ x, x = s_end.tokens[s.tokens.size + 1]'h_N1_lt_end := ⟨_, rfl⟩
  have h_pN : (fun (t : Positioned YamlToken) => t.val != .placeholder) tokN = false := by
    simp only [htokN_def, h_endN_ph]; rfl
  have h_pN1 : (fun (t : Positioned YamlToken) => t.val != .placeholder) tokN1 = true := by
    simp only [htokN1_def, h_endN1_key]; rfl
  have h_ref_filter : ((s.tokens.push tokN).push tokN1).filter (fun t => t.val != .placeholder) =
      (s.tokens.filter (fun t => t.val != .placeholder)).push tokN1 := by
    rw [Array.filter_push, Array.filter_push]
    simp [h_pN, h_pN1]
  have h_old_lt_ref : (s.tokens.filter (fun t => t.val != .placeholder)).size <
      (((s.tokens.push tokN).push tokN1).filter (fun t => t.val != .placeholder)).size := by
    rw [h_ref_filter, Array.size_push]; omega
  have h_ref_get : (((s.tokens.push tokN).push tokN1).filter (fun t => t.val != .placeholder))[
      (s.tokens.filter (fun t => t.val != .placeholder)).size]? = some tokN1 := by
    rw [h_ref_filter, Array.getElem?_push, if_pos rfl]
  -- Raw-prefix equality `ref` ⊑ `s_end.tokens` (sizes + pointwise, via `getElem?`).
  have h_ref_le : ((s.tokens.push tokN).push tokN1).size ≤ s_end.tokens.size := by
    rw [Array.size_push, Array.size_push]; omega
  have h_raw : ∀ i (hi : i < ((s.tokens.push tokN).push tokN1).size),
      s_end.tokens[i]'(by
        have hi2 : i < s.tokens.size + 2 := by simpa [Array.size_push] using hi
        omega) = ((s.tokens.push tokN).push tokN1)[i]'hi := by
    intro i hi
    have hi2 : i < s.tokens.size + 2 := by simpa [Array.size_push] using hi
    have h_get? : s_end.tokens[i]? = ((s.tokens.push tokN).push tokN1)[i]? := by
      rw [Array.getElem?_push, Array.getElem?_push, Array.size_push]
      rcases Nat.lt_trichotomy i s.tokens.size with hlt | heq | hgt
      · rw [if_neg (by omega), if_neg (by omega),
            Array.getElem?_eq_getElem (show i < s_end.tokens.size by omega),
            Array.getElem?_eq_getElem hlt, h_prefix i hlt]
      · subst heq
        rw [if_neg (by omega), if_pos rfl,
            Array.getElem?_eq_getElem h_N_lt_end, htokN_def]
      · obtain rfl : i = s.tokens.size + 1 := by omega
        rw [if_pos rfl, Array.getElem?_eq_getElem h_N1_lt_end, htokN1_def]
    rw [Array.getElem?_eq_getElem (show i < s_end.tokens.size by omega),
        Array.getElem?_eq_getElem hi] at h_get?
    exact Option.some.inj h_get?
  -- Transfer and conclude.
  have h_trans := Array_filter_getElem_of_raw_prefix ((s.tokens.push tokN).push tokN1) s_end.tokens
    (fun t => t.val != .placeholder) h_ref_le h_raw
    (s.tokens.filter (fun t => t.val != .placeholder)).size h_old_lt_ref h_old_lt
  rw [h_trans]
  have h_eq : (((s.tokens.push tokN).push tokN1).filter (fun t => t.val != .placeholder))[
      (s.tokens.filter (fun t => t.val != .placeholder)).size]'h_old_lt_ref = tokN1 :=
    Option.some.inj ((Array.getElem?_eq_getElem h_old_lt_ref).symm.trans h_ref_get)
  rw [h_eq, htokN1_def]
  exact h_endN1_key

/-- Keyshape producer: like `emitPairList_scans_nonempty` but additionally exposes
    that the first new filtered token is `.key` (Part 2 of
    `emitPairList_body_filtered_characterization`, legacy sorry 9644).

    Built by re-deriving the bundle so the residual `FlowMonoChain` from the post-colon
    state is in hand (avoiding chain factoring): the first key is scanned via the
    saved-key substrate (`EmitScansInFlowSavedKey`), the colon's strengthened token
    effect pins `.key` at `N+1`, and `keyshape_first_token_key` performs the filter
    transfer.  The value and any remaining pairs reuse `EmitScansInFlow` and the plain
    `emitPairList_scans_nonempty` producer. -/
theorem emitPairList_scans_nonempty_keyshape
    (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlow p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlow p.2)
    (h_all_k_sk : ∀ p ∈ pairs, EmitScansInFlowSavedKey p.1)
    (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line) (h_endline : EndLineOnLine s)
    (h_sk : s.simpleKey.possible = false)
    (h_ska : s.simpleKeyAllowed = true)
    (h_sync : s.simpleKeyStack.size = s.flowLevel)
    (h_ssv : ScannerCorrectness.SimpleKeyStackValid s) :
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      ∧ n ≥ 3
      ∧ ((s.tokens.filter (fun t => t.val != .placeholder)).size <
            (s'.tokens.filter (fun t => t.val != .placeholder)).size ∧
          (∀ (h : (s.tokens.filter (fun t => t.val != .placeholder)).size <
              (s'.tokens.filter (fun t => t.val != .placeholder)).size),
            ((s'.tokens.filter (fun t => t.val != .placeholder))[
              (s.tokens.filter (fun t => t.val != .placeholder)).size]'h).val = .key)) := by
  obtain ⟨p, tail, rfl⟩ : ∃ p tail, pairs = p :: tail := by
    cases pairs with
    | nil => exact absurd rfl h_ne
    | cons p tail => exact ⟨p, tail, rfl⟩
  match tail with
  | [] =>
    -- ══ Singleton [(k,v)]: emitPairList [(k,v)] = emit k ++ ": " ++ emit v ══
    have h_eq : (emit.emitPairList [p]).toList ++ rest =
        (emit p.1).toList ++ ([':',  ' '] ++ (emit p.2).toList ++ rest) := by
      simp [emit.emitPairList, String.toList_append, List.append_assoc]
    rw [h_eq] at hcorr
    -- Step 1: Scan key via the saved-key substrate.
    obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
            h_flow₁, h_indent₁, _h_line₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
            h_ska₁, h_sk_poss₁, h_sk_tidx₁, h_sz₁, h_ph₁, _⟩ :=
      (h_all_k_sk p (.head _)) s ([':',  ' '] ++ (emit p.2).toList ++ rest)
        hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sk h_sync
    have h_n₁_pos : n₁ ≥ 1 := by
      match n₁, h_chain₁ with
      | 0, h => have hss : s = s₁ := by cases h; rfl
                rw [← hss] at h_sz₁; omega
      | _ + 1, _ => omega
    have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
        (by rw [h_ek₁]; exact h_ek)
    have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
      rw [h_sk_id]
      exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
        (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
    -- Step 2: Scan ':' via the strengthened colon (exposes the `.key` token effect).
    obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
            h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂,
            h_sk2_poss, h_colon_key, _⟩ :=
      scanNextToken_flow_value s₁ ((emit p.2).toList ++ rest)
        h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
        h_atol₁ h_endline₁
    -- Step 3: leading space before value via preprocessing equality
    obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
    have h_corr₂_ws : ScannerSurfCorr s₂
        ⟨' ' :: c_v :: (rest_v ++ rest), s₂.col⟩ := by
      have h_eq_chars : (' ' :: (emit p.2).toList ++ rest) =
          (' ' :: c_v :: (rest_v ++ rest)) := by
        congr 1; rw [h_first_v]; simp only [List.cons_append]
      exact h_eq_chars ▸ h_corr₂
    obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
      scanNextToken_preprocess_flow_ws1 s₂ c_v (rest_v ++ rest) h_corr₂_ws
        h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
    have h_corr₃' : ScannerSurfCorr s₃
        ⟨(emit p.2).toList ++ rest, s₃.col⟩ := by
      have h_eq_chars : (c_v :: (rest_v ++ rest)) =
          ((emit p.2).toList ++ rest) := by
        rw [h_first_v]; simp only [List.cons_append]
      exact h_eq_chars ▸ h_corr₃
    -- Step 4: Scan value via EmitScansInFlow
    have h_ev : EmitScansInFlow p.2 := h_all_v p (.head _)
    obtain ⟨n₃, s_end, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
            h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, _, _, h_atol_end, h_endline_end, h_stack_end, h_fmc₃⟩ :=
      h_ev s₃ rest h_corr₃'
        h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
        (by rw [h_indent₃]; exact h_indent₂)
        (by rw [h_col₃]; omega)
        (by rw [h_ek₃]; exact h_ek₂)
        (h_atol_transfer₃ h_atol₂)
        (h_endline_transfer₃ h_endline₂)
    have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
      scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
    have h_n₃_pos : n₃ ≥ 1 := by
      match n₃, h_chain₃ with
      | 0, .zero =>
        exfalso
        have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
        have h_len := congrArg List.length h_chars_eq
        simp only [List.length_append] at h_len
        have h_nil : (emit p.2).toList = [] := by
          match h_list : (emit p.2).toList with
          | [] => rfl
          | _ :: _ => simp [h_list] at h_len
        obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
        exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
      | _ + 1, _ => omega
    obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
    have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                     (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
      rw [h_toks_pp₃]; exact Nat.le_refl _
    have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
          s₂ (n₃' + 1) s_end :=
      ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain₃
    have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr₁_cons : ScannerSurfCorr s₁
          ⟨':' :: (' ' :: (emit p.2).toList ++ rest), s₁.col⟩ := by
        have : [':', ' '] ++ (emit p.2).toList ++ rest =
            ':' :: (' ' :: (emit p.2).toList ++ rest) := by
          simp only [List.cons_append, List.nil_append]
        rwa [this] at h_corr₁
      exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
        (' ' :: (emit p.2).toList ++ rest)
        h_corr₁_cons h_flow₁ h_indent₁ h_col₁
        (by decide) (by decide) (by decide) h_snt₂
    have h_fmc₃' : FlowMonoChain s.flowLevel s₃ (n₃' + 1) s_end :=
      (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc₃
    have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n₃' + 1) s_end :=
      FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc₃'
    have h_fmc_all := h_fmc₁.trans
      ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
    have h_chain_all := h_chain₁.trans
      ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
    have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
    refine ⟨n₁ + 1 + (n₃' + 1), s_end, h_arith ▸ h_chain_all,
      h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, by omega, ?_⟩
    · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
    · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
    · rw [h_ek_end, h_ek₃, h_ek₂]; exact h_ek.symm
    · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
    · rw [h_stack_end, h_stack_pp₃, h_stack_v₂, h_stack₁]
    · -- Part 2: first new filtered token is `.key`
      obtain ⟨h_key2', h_pres2'⟩ :=
        h_colon_key h_ska₁ h_sk_poss₁ (by rw [h_sk_tidx₁]; exact h_sz₁)
      refine ⟨by have := ScanChainGrew_filtered_grows (h_arith ▸ h_chain_all); omega, ?_⟩
      exact keyshape_first_token_key s s₁ s₂ s_end h_sk h_sync h_ssv h_fl
        (h_arith ▸ h_fmc_all) h_fmc_ws h_sz₁ h_ph₁
        (h_stack_v₂.trans h_stack₁) h_sk2_poss
        (h_sk_tidx₁ ▸ h_key2') (h_sk_tidx₁ ▸ h_pres2')
  | p' :: ps =>
    -- ══ Multi-pair: emit k ++ ": " ++ emit v ++ ", " ++ emitPairList (p' :: ps) ══
    have h_eq : (emit.emitPairList (p :: p' :: ps)).toList ++ rest =
        (emit p.1).toList ++ ([':',  ' '] ++ (emit p.2).toList ++
          [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest) := by
      simp [emit.emitPairList, String.toList_append, List.append_assoc]
    rw [h_eq] at hcorr
    -- Step 1: Scan key via the saved-key substrate.
    obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
            h_flow₁, h_indent₁, _h_line₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
            h_ska₁, h_sk_poss₁, h_sk_tidx₁, h_sz₁, h_ph₁, _⟩ :=
      (h_all_k_sk p (.head _)) s
        ([':',  ' '] ++ (emit p.2).toList ++
          [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest)
        hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sk h_sync
    have h_n₁_pos : n₁ ≥ 1 := by
      match n₁, h_chain₁ with
      | 0, h => have hss : s = s₁ := by cases h; rfl
                rw [← hss] at h_sz₁; omega
      | _ + 1, _ => omega
    have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
        (by rw [h_ek₁]; exact h_ek)
    have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
      rw [h_sk_id]
      exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
        (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
    -- Step 2: Scan ':' via the strengthened colon.
    obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
            h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂,
            h_sk2_poss, h_colon_key, _⟩ :=
      scanNextToken_flow_value s₁
        ((emit p.2).toList ++
          [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest)
        h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
        h_atol₁ h_endline₁
    -- Step 3: leading space before value
    obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
    have h_corr₂_ws : ScannerSurfCorr s₂
        ⟨' ' :: c_v :: (rest_v ++
          [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest), s₂.col⟩ := by
      have h_eq_chars : (' ' :: (emit p.2).toList ++
          [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest) =
          (' ' :: c_v :: (rest_v ++
          [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest)) := by
        congr 1; rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
      exact h_eq_chars ▸ h_corr₂
    obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
      scanNextToken_preprocess_flow_ws1 s₂ c_v
        (rest_v ++ [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest)
        h_corr₂_ws h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
    have h_corr₃' : ScannerSurfCorr s₃
        ⟨(emit p.2).toList ++
          [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest, s₃.col⟩ := by
      have h_eq_chars : (c_v :: (rest_v ++
          [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest)) =
          ((emit p.2).toList ++
          [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest) := by
        rw [h_first_v]; simp only [List.cons_append]
      exact h_eq_chars ▸ h_corr₃
    -- Step 4: Scan value via EmitScansInFlow
    have h_ev : EmitScansInFlow p.2 := h_all_v p (.head _)
    have h_corr₃_assoc : ScannerSurfCorr s₃
        ⟨(emit p.2).toList ++ ([',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest), s₃.col⟩ := by
      simp only [List.append_assoc] at h_corr₃' ⊢; exact h_corr₃'
    obtain ⟨n_v, s_v, h_chain_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v,
            h_ek_v, h_col_v, h_flow_v, h_indent_v, _h_line_v, _, h_last_v, h_atol_v, h_endline_v, h_stack_v, h_fmc_v⟩ :=
      h_ev s₃
        ([',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest)
        h_corr₃_assoc
        h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
        (by rw [h_indent₃]; exact h_indent₂)
        (by rw [h_col₃]; omega)
        (by rw [h_ek₃]; exact h_ek₂)
        (h_atol_transfer₃ h_atol₂)
        (h_endline_transfer₃ h_endline₂)
    have h_snt_eq_v : scanNextToken s₂ = scanNextToken s₃ :=
      scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
    have h_n_v_pos : n_v ≥ 1 := by
      match n_v, h_chain_v with
      | 0, .zero =>
        exfalso
        have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_v.chars_from
        have h_len := congrArg List.length h_chars_eq
        simp only [List.length_append] at h_len
        have h_nil : (emit p.2).toList = [] := by
          match h_list : (emit p.2).toList with
          | [] => rfl
          | _ :: _ => simp [h_list] at h_len
        obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
        exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
      | _ + 1, _ => omega
    obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
    have h_filt_le_v : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
      rw [h_toks_pp₃]; exact Nat.le_refl _
    have h_chain_ws_v : ScanChainGrew (fun t => t.val != .placeholder)
          s₂ (n_v' + 1) s_v :=
      ScanChainGrew_of_scanNextToken_eq h_snt_eq_v h_filt_le_v h_chain_v
    have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr₁_cons : ScannerSurfCorr s₁
          ⟨':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
            (emit.emitPairList (p' :: ps)).toList ++ rest), s₁.col⟩ := by
        have : [':', ' '] ++ (emit p.2).toList ++ [',', ' '] ++
            (emit.emitPairList (p' :: ps)).toList ++ rest =
            ':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
            (emit.emitPairList (p' :: ps)).toList ++ rest) := by
          simp only [List.cons_append, List.nil_append]
        rwa [this] at h_corr₁
      exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
        (' ' :: (emit p.2).toList ++ [',', ' '] ++
            (emit.emitPairList (p' :: ps)).toList ++ rest)
        h_corr₁_cons h_flow₁ h_indent₁ h_col₁
        (by decide) (by decide) (by decide) h_snt₂
    -- Step 5: Scan ',' via scanNextToken_flow_comma
    obtain ⟨s_c, h_snt_c, h_corr_c, h_fl_c, h_dp_c, h_ids_c, h_ek_c, h_col_c, _h_line_c, h_atol_c, h_endline_c, h_stack_c⟩ :=
      scanNextToken_flow_comma s_v
        (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest)
        h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_atol_v h_endline_v
    obtain ⟨c_p, rest_p, h_first_p, h_nws_p, h_nlb_p, h_nc_p⟩ :=
      emitPairList_first_char p' ps
    have h_corr_c_ws : ScannerSurfCorr s_c
        ⟨' ' :: c_p :: (rest_p ++ rest), s_c.col⟩ := by
      have : ' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest =
          ' ' :: c_p :: (rest_p ++ rest) := by
        rw [h_first_p]; simp only [List.cons_append]
      rwa [this] at h_corr_c
    have h_sc_flow : s_c.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_c]; omega)
    have h_sc_indent : s_c.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids_c]; exact h_indent_v
    obtain ⟨s_pp, h_corr_pp, h_flow_pp, h_fl_pp, h_indent_pp, h_col_pp,
            h_dp_pp, h_ids_pp, h_ek_pp, _h_line_pp, h_pp_eq_r, h_atol_transfer_pp, h_endline_transfer_pp, h_stack_pp, h_toks_pp, _, _⟩ :=
      scanNextToken_preprocess_flow_ws1 s_c c_p (rest_p ++ rest) h_corr_c_ws
        h_sc_flow h_nws_p h_nlb_p h_nc_p h_sc_indent
    have h_corr_pp' : ScannerSurfCorr s_pp
        ⟨(emit.emitPairList (p' :: ps)).toList ++ rest, s_pp.col⟩ := by
      have : c_p :: (rest_p ++ rest) =
          (emit.emitPairList (p' :: ps)).toList ++ rest := by
        rw [h_first_p]; simp only [List.cons_append]
      rwa [this] at h_corr_pp
    -- Step 6: scan emitPairList (p' :: ps) via the plain producer
    have h_tail_all_k : ∀ q ∈ p' :: ps, EmitScansInFlow q.1 :=
      fun q hq => h_all_k q (.tail _ hq)
    have h_tail_all_v : ∀ q ∈ p' :: ps, EmitScansInFlow q.2 :=
      fun q hq => h_all_v q (.tail _ hq)
    have h_tail_list : EmitPairListScansInFlow (p' :: ps) :=
      (emitPairList_scans_nonempty (p' :: ps) (by simp) h_tail_all_k h_tail_all_v).toWeak
    obtain ⟨n_r, s_end, h_chain_r, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
            h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc_r⟩ :=
      h_tail_list s_pp rest h_corr_pp'
        h_flow_pp
        (by rw [h_fl_pp, h_fl_c]; rw [h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
        (by rw [h_indent_pp]; exact h_sc_indent)
        (by rw [h_col_pp]; omega)
        (by rw [h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂])
        (h_atol_transfer_pp h_atol_c)
        (h_endline_transfer_pp h_endline_c)
    have h_snt_eq_r : scanNextToken s_c = scanNextToken s_pp :=
      scanNextToken_eq_of_preprocess s_c s_pp h_pp_eq_r
    have h_n_r_pos : n_r ≥ 1 := by
      match n_r, h_chain_r with
      | 0, .zero =>
        exfalso
        have h_chars_eq := CharsFromOffset_unique h_corr_pp'.chars_from h_corr_end.chars_from
        have h_len := congrArg List.length h_chars_eq
        simp only [List.length_append] at h_len
        have h_nil : (emit.emitPairList (p' :: ps)).toList = [] := by
          match h_list : (emit.emitPairList (p' :: ps)).toList with
          | [] => rfl
          | _ :: _ => simp [h_list] at h_len
        obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emitPairList_first_char p' ps
        exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
      | _ + 1, _ => omega
    obtain ⟨n_r', rfl⟩ : ∃ k, n_r = k + 1 := ⟨n_r - 1, by omega⟩
    have h_filt_le_r : (s_c.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
      rw [h_toks_pp]; exact Nat.le_refl _
    have h_chain_ws_r : ScanChainGrew (fun t => t.val != .placeholder)
          s_c (n_r' + 1) s_end :=
      ScanChainGrew_of_scanNextToken_eq h_snt_eq_r h_filt_le_r h_chain_r
    have h_grew_c : (s_c.tokens.filter (fun t => t.val != .placeholder)).size >
                    (s_v.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr_v_cons : ScannerSurfCorr s_v
          ⟨',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest), s_v.col⟩ := by
        have : [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest =
            ',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest) := by
          simp only [List.cons_append, List.nil_append]
        rwa [this] at h_corr_v
      exact scanNextToken_filtered_grows_in_flow s_v s_c ','
        (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest)
        h_corr_v_cons h_flow_v h_indent_v h_col_v
        (by decide) (by decide) (by decide) h_snt_c
    have h_fmc_v' : FlowMonoChain s.flowLevel s₃ (n_v' + 1) s_v :=
      (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc_v
    have h_fmc_ws_v : FlowMonoChain s.flowLevel s₂ (n_v' + 1) s_v :=
      FlowMonoChain_of_scanNextToken_eq h_snt_eq_v (by omega) h_fmc_v'
    have h_fmc_r' : FlowMonoChain s.flowLevel s_pp (n_r' + 1) s_end :=
      (show s.flowLevel = s_pp.flowLevel from by omega) ▸ h_fmc_r
    have h_fmc_ws_r : FlowMonoChain s.flowLevel s_c (n_r' + 1) s_end :=
      FlowMonoChain_of_scanNextToken_eq h_snt_eq_r (by omega) h_fmc_r'
    -- residual FlowMonoChain from the post-colon state `s₂`
    have h_fmc_resid : FlowMonoChain s.flowLevel s₂ ((n_v' + 1) + (1 + (n_r' + 1))) s_end :=
      h_fmc_ws_v.trans ((FlowMonoChain.single h_snt_c (by omega) (by omega)).trans h_fmc_ws_r)
    have h_fmc_all := h_fmc₁.trans
      ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_resid)
    have h_chain_all := h_chain₁.trans
      ((ScanChainGrew.single h_snt₂ h_grew₂).trans
        (h_chain_ws_v.trans
          ((ScanChainGrew.single h_snt_c h_grew_c).trans h_chain_ws_r)))
    have h_arith : n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) =
        n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1) := by omega
    have h_arith' : n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) =
        n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) := rfl
    refine ⟨n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1), s_end,
      h_arith ▸ h_chain_all,
      h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, by omega, ?_⟩
    · rw [h_fl_end, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]
    · rw [h_dp_end, h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids_end, h_ids_pp, h_ids_c, h_ids_v, h_ids₃, h_ids₂, h_ids₁]
    · rw [h_ek_end, h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂]; exact h_ek.symm
    · rw [h_line_end, _h_line_pp, _h_line_c, _h_line_v, _h_line₃, _h_line₂, _h_line₁]
    · rw [h_stack_end, h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁]
    · -- Part 2: first new filtered token is `.key`
      obtain ⟨h_key2', h_pres2'⟩ :=
        h_colon_key h_ska₁ h_sk_poss₁ (by rw [h_sk_tidx₁]; exact h_sz₁)
      refine ⟨by have := ScanChainGrew_filtered_grows (h_arith ▸ h_chain_all); omega, ?_⟩
      exact keyshape_first_token_key s s₁ s₂ s_end h_sk h_sync h_ssv h_fl
        (h_arith ▸ h_fmc_all) h_fmc_resid h_sz₁ h_ph₁
        (h_stack_v₂.trans h_stack₁) h_sk2_poss
        (h_sk_tidx₁ ▸ h_key2') (h_sk_tidx₁ ▸ h_pres2')

/-! ### §H.1  SKDR construction combinators -/

/-- Lower the flow floor of a `SavedKeyDoesntResolve`.  Mirrors
    `FlowMonoChain.weaken`: every `flowLevel ≥ fl₀` obligation stays valid when
    `fl₀` shrinks. -/
theorem SavedKeyDoesntResolve.weaken {fl₀ fl₁ n_target : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : SavedKeyDoesntResolve fl₀ n_target s n s') (h_le : fl₁ ≤ fl₀) :
    SavedKeyDoesntResolve fl₁ n_target s n s' := by
  induction h with
  | zero h_fl => exact .zero (Nat.le_trans h_le h_fl)
  | step h_fl h_snt h_pres _h_rest ih => exact .step (Nat.le_trans h_le h_fl) h_snt h_pres ih

/-- **Non-`:` step constructor.**  If the step's dispatched character is not `:`,
    the step preserves position `n_target + 1` unconditionally (substrate.g), so
    it extends a `SavedKeyDoesntResolve`.  This is the bridge from substrate.g's
    per-character primitive into substrate.f's chain predicate. -/
theorem SavedKeyDoesntResolve.step_of_non_colon
    {fl₀ n_target : Nat} {s s_mid s' : ScannerState} {n : Nat}
    (h_fl : s.flowLevel ≥ fl₀)
    (h_snt : scanNextToken s = .ok (some s_mid))
    (h_no_colon : ∀ t c, scanNextToken_preprocess s = .ok (some (t, c)) → c ≠ ':')
    (h_rest : SavedKeyDoesntResolve fl₀ n_target s_mid n s') :
    SavedKeyDoesntResolve fl₀ n_target s (n + 1) s' := by
  refine .step h_fl h_snt ?_ h_rest
  intro h_size
  have h_adds := ScannerCorrectness.scanNextToken_adds_tokens s s_mid h_snt
  exact ⟨by omega,
    scanNextToken_at_non_colon_preserves_positions s s_mid h_snt h_no_colon (n_target + 1) h_size⟩

/-- From a *known* flow-context dispatched character `c ≠ ':'`, derive the
    universally-quantified non-`:` hypothesis used by
    `SavedKeyDoesntResolve.step_of_non_colon`.  `scanNextToken_preprocess` is a
    function, so any `(t, c')` it yields equals `(saveSimpleKey s, c)`. -/
theorem no_colon_of_preprocess_flow (s : ScannerState) (c : Char) (rest : List Char)
    (col : Nat) (hcorr : ScannerSurfCorr s ⟨c :: rest, col⟩)
    (h_flow : s.inFlow = true) (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false) (h_nc : c ≠ '#') (h_col : c ≠ ':') :
    ∀ t c', scanNextToken_preprocess s = .ok (some (t, c')) → c' ≠ ':' := by
  have h_pp := scanNextToken_preprocess_flow s c rest col hcorr h_flow h_nws h_nlb h_nc
  intro t c' h_eq
  rw [h_pp] at h_eq
  simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_eq
  rw [← h_eq.2]; exact h_col

/-- Chain-level maintenance of substrate.d's `NoOverwriteAt m`: if position `m`
    starts un-overwritable and `m < s.tokens.size`, it stays un-overwritable
    across an entire `FlowMonoChain`.  Direct induction delegating each step to
    `scanNextToken_maintains_NoOverwriteAt`. -/
theorem FlowMonoChain_maintains_NoOverwriteAt {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s') (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : NoOverwriteAt s m) : NoOverwriteAt s' m := by
  induction h_fmc with
  | zero => exact h_inv
  | step h_fl h_snt h_rest ih =>
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt
    have h_inv' := scanNextToken_maintains_NoOverwriteAt _ _ h_snt m h_m h_inv
    exact ih (Nat.lt_of_lt_of_le h_m h_adds) h_inv'

/-- **Bulk converter.**  A `FlowMonoChain` upgrades to a `SavedKeyDoesntResolve`
    at target `n_target` as soon as `SimpleKeyAboveFloor (n_target + 1)` holds at
    the chain start (and `n_target + 1 ≤ size`).  Every step then has
    `simpleKey.tokenIndex ≥ n_target + 1 > n_target`, so `step_of_tokenIndex_ne`
    fires uniformly — no per-character classification needed.  This handles every
    *inner* emit sub-chain (where the body starts past the protected position);
    only the top-level body boundary needs the substrate.g per-step route. -/
theorem SavedKeyDoesntResolve_of_FlowMonoChain_skFloor
    {fl₀ n_target : Nat} {s s' : ScannerState} {n : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s')
    (h_fl_pos : fl₀ ≥ 1)
    (h_le : n_target + 1 ≤ s.tokens.size)
    (h_skf : SimpleKeyAboveFloor s (n_target + 1) fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel) :
    SavedKeyDoesntResolve fl₀ n_target s n s' := by
  induction h_fmc with
  | zero h_fl => exact .zero h_fl
  | @step s s_mid s' n h_fl h_snt h_rest ih =>
    have h_fl_mid := h_rest.flowLevel_ge_start
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens s s_mid h_snt
    have h_skf_mid := scanNextToken_maintains_SimpleKeyAboveFloor s s_mid h_snt (n_target + 1) fl₀
      h_le h_skf h_sync h_fl_mid
    have h_sync_mid := scanNextToken_preserves_sync s s_mid h_snt h_sync
    have h_not_target : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≠ n_target := by
      intro hp; have := h_skf.1 hp; omega
    exact SavedKeyDoesntResolve.step_of_tokenIndex_ne h_fl_pos h_fl h_snt h_not_target
      (ih (by omega) h_skf_mid h_sync_mid)

/-- **Bulk converter (substrate.d flavour).**  Like
    `SavedKeyDoesntResolve_of_FlowMonoChain_skFloor` but driven by substrate.d's
    `NoOverwriteAt (n_target + 1)` instead of `SimpleKeyAboveFloor` — no
    stack-floor / sync hypotheses, just `n_target + 1 < size`.  `NoOverwriteAt`'s
    second clause (`n_target + 1 ≠ tokenIndex + 1`) gives exactly the
    `tokenIndex ≠ n_target` that `step_of_tokenIndex_ne` needs, while tolerating
    harmless low keys (`tokenIndex < n_target`).  Used for emit sub-bodies that
    start strictly past the protected position. -/
theorem SavedKeyDoesntResolve_of_FlowMonoChain_noOverwrite
    {fl₀ n_target : Nat} {s s' : ScannerState} {n : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s')
    (h_fl_pos : fl₀ ≥ 1)
    (h_lt : n_target + 1 < s.tokens.size)
    (h_inv : NoOverwriteAt s (n_target + 1)) :
    SavedKeyDoesntResolve fl₀ n_target s n s' := by
  induction h_fmc with
  | zero h_fl => exact .zero h_fl
  | @step s s_mid s' n h_fl h_snt h_rest ih =>
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens s s_mid h_snt
    have h_inv_mid := scanNextToken_maintains_NoOverwriteAt s s_mid h_snt (n_target + 1) h_lt h_inv
    have h_not_target : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≠ n_target := by
      intro hp h_eq; exact (h_inv.1 hp).2 (by omega)
    exact SavedKeyDoesntResolve.step_of_tokenIndex_ne h_fl_pos h_fl h_snt h_not_target
      (ih (by omega) h_inv_mid)

/-! ### §H.2  SKDR-producing scanning theorems (the `.establishing.consumer`)

Parallel to `emit_scans_in_flow` / `emitList_scans_nonempty` but additionally
producing a `SavedKeyDoesntResolve s.flowLevel N s n s'` witness for an externally
fixed protected target `N ≤ s.tokens.size`.  Two extra hypotheses beyond the plain
predicates:

  * `N ≤ s.tokens.size` — the protected slot `N + 1` is the first slot a saved key
    could resolve into; `N = s.tokens.size` at the top-level body is the boundary.
  * `s.simpleKeyStack.size = s.flowLevel` (`ExactSync`) — the stack tracks the flow
    level exactly in flow context.  This is the enabler (Reflection 165): at a flow
    open the polluting key (if any) is pushed to stack index `flowLevel = innerFloor
    - 1`, *below* the inner floor, so `SimpleKeyAboveFloor (N + 1)` re-holds at the
    inner body start and the `_skFloor` converter takes the whole inner body — no
    inner `:`-step ever needs individual treatment.  `ExactSync` threads for free
    through the existing `simpleKeyStack`/`flowLevel` preservation conjuncts.

Construction per `emit_scans_in_flow_with_skdr` case:
  * scalar — single non-`:` step (`"`), `step_of_non_colon`.
  * sequence/mapping — `[`/`{` (non-`:`) + inner body via `_skFloor` converter
    (weakened to the outer floor) + `]`/`}` (non-`:`).  The inner body's opaque
    `FlowMonoChain` comes from the plain `emitList_scans_nonempty` /
    `emitPairList_scans_nonempty`.

`emitList_scans_nonempty_with_skdr` walks the *top-level* body item-by-item
(each item via `emit_scans_in_flow_with_skdr`, commas via `step_of_non_colon`),
because the top-level body starts at the boundary where the converters do not
apply.  Closes zero legacy sorries directly; ships the witness consumed by
`.tokenshape.list.discharge`. -/

/-- SKDR-augmented `EmitScansInFlow`: see §H.2 header. -/
def EmitScansInFlowSKDR (v : YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char) (N : Nat),
    ScannerSurfCorr s ⟨(emit v).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    N ≤ s.tokens.size →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ s'.simpleKeyAllowed = false
      ∧ (∀ t, lastRealTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      ∧ SavedKeyDoesntResolve s.flowLevel N s n s'

/-- SKDR-producing companion to `emit_scans_in_flow`. -/
theorem emit_scans_in_flow_with_skdr (v : YamlValue) {inFlow : Bool}
    (hg : Grammable v inFlow) : EmitScansInFlowSKDR v := by
  induction hg with
  | scalar sc _ h =>
    intro s_state rest N hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_N h_sync
    have h_chars : (emit (.scalar sc)).toList ++ rest =
        ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest := by
      simp only [emit, emitScalar, String.toList_append]; rfl
    have hcorr' : ScannerSurfCorr s_state
        ⟨['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest, s_state.col⟩ := by
      rwa [← h_chars]
    obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_tok', h_ska', _h_line', h_atol', h_endline', h_stack'⟩ :=
      scanNextToken_flow_scanDoubleQuoted s_state sc.content rest hcorr' h_flow h_indent h_col
        h_atol (by intro h_poss; exact h_endline h_poss)
    have h_corr_cons : ScannerSurfCorr s_state
        ⟨'"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest), s_state.col⟩ := by
      have : ['"'] ++ (escapeString sc.content).toList ++ ['"'] ++ rest =
              '"' :: ((escapeString sc.content).toList ++ ['"'] ++ rest) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      rwa [this] at hcorr'
    have h_grew : (s'.tokens.filter (fun t => t.val != .placeholder)).size >
                  (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s' '"'
        ((escapeString sc.content).toList ++ ['"'] ++ rest)
        h_corr_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt
    have h_nc : ∀ t c, scanNextToken_preprocess s_state = .ok (some (t, c)) → c ≠ ':' :=
      no_colon_of_preprocess_flow s_state '"' ((escapeString sc.content).toList ++ ['"'] ++ rest)
        s_state.col h_corr_cons h_flow (by decide) (by decide) (by decide) (by decide)
    have h_skdr : SavedKeyDoesntResolve s_state.flowLevel N s_state 1 s' :=
      SavedKeyDoesntResolve.step_of_non_colon (Nat.le.refl) h_snt h_nc (.zero (by omega))
    refine ⟨1, s', ScanChainGrew.single h_snt h_grew, h_corr', h_fl', h_dp', h_ids', h_ek',
      ?_, ?_, ?_, _h_line', h_ska', ?_, ?_, ?_, ?_, ?_, h_skdr⟩
    · exact h_col'
    · unfold ScannerState.inFlow; rw [h_fl']
      unfold ScannerState.inFlow at h_flow; exact h_flow
    · unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent
    · exact h_tok'
    · exact h_atol'
    · exact h_endline'
    · exact h_stack'
    · exact FlowMonoChain.single h_snt (Nat.le.refl) (by omega)
  | sequence style items tag anchor _ h _ih =>
    intro s_state rest N hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_N h_sync
    have h_chars : (emit (.sequence style items tag anchor)).toList ++ rest =
        ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, h_sk_poss₁, h_toks_gt₁⟩ :=
      scanNextToken_flow_open_nested s_state
        ((emit.emitList items.toList).toList ++ [']'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    have h_list_scan : EmitListScansInFlow items.toList := by
      match h_list : items.toList with
      | [] => exact emitList_scans_empty
      | _ :: _ =>
        exact emitList_scans_nonempty _ (by simp) (fun w hw => by
          have hw' : w ∈ items.toList := h_list ▸ hw
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw'
          have h_sz : i < items.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow _ (h ⟨i, h_sz⟩))
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂⟩ :=
      h_list_scan s₁ ([']'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
        (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, _, _⟩ :=
      scanNextToken_flow_close_seq_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
        (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    have h_corr_state_cons : ScannerSurfCorr s_state
        ⟨'[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest), s_state.col⟩ := by
      have : ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest =
          '[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      rwa [this] at hcorr₀
    have h_corr₂_cons : ScannerSurfCorr s₂ ⟨']' :: rest, s₂.col⟩ := by
      have : [']'] ++ rest = ']' :: rest := by simp
      rwa [this] at h_corr₂
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s₁ '['
        ((emit.emitList items.toList).toList ++ [']'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s₂ s₃ ']' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
    -- SKDR: '[' (non-`:`) + inner body (converter) + ']' (non-`:`)
    have h_s1_stacksize : s₁.simpleKeyStack.size = s_state.flowLevel + 1 := by
      have hp := congrArg Array.size h_stack_pop₁
      rw [Array.size_pop] at hp; omega
    have h_skf₁ : SimpleKeyAboveFloor s₁ (N + 1) s₁.flowLevel := by
      refine ⟨fun hp => absurd hp (by rw [h_sk_poss₁]; decide), fun j hfl hj _hp => ?_, ?_⟩
      · exfalso; rw [h_fl₁] at hfl; rw [h_s1_stacksize] at hj; omega
      · rw [h_fl₁]; omega
    have h_skdr_body : SavedKeyDoesntResolve s₁.flowLevel N s₁ n₂ s₂ :=
      SavedKeyDoesntResolve_of_FlowMonoChain_skFloor h_fmc₂ (by rw [h_fl₁]; omega)
        (by omega) h_skf₁ (by rw [h_fl₁]; omega)
    have h_skdr_body' : SavedKeyDoesntResolve s_state.flowLevel N s₁ n₂ s₂ :=
      h_skdr_body.weaken (by rw [h_fl₁]; omega)
    have h_nc_open : ∀ t c, scanNextToken_preprocess s_state = .ok (some (t, c)) → c ≠ ':' :=
      no_colon_of_preprocess_flow s_state '[' ((emit.emitList items.toList).toList ++ [']'] ++ rest)
        s_state.col h_corr_state_cons h_flow (by decide) (by decide) (by decide) (by decide)
    have h_nc_close : ∀ t c, scanNextToken_preprocess s₂ = .ok (some (t, c)) → c ≠ ':' :=
      no_colon_of_preprocess_flow s₂ ']' rest s₂.col h_corr₂_cons h_s2_inflow
        (by decide) (by decide) (by decide) (by decide)
    have h_skdr_close : SavedKeyDoesntResolve s_state.flowLevel N s₂ 1 s₃ :=
      SavedKeyDoesntResolve.step_of_non_colon (by rw [h_fl₂, h_fl₁]; omega) h_snt₃ h_nc_close
        (.zero (by rw [h_fl₃, h_fl₂, h_fl₁]; omega))
    have h_skdr_all : SavedKeyDoesntResolve s_state.flowLevel N s_state ((n₂ + 1) + 1) s₃ :=
      SavedKeyDoesntResolve.step_of_non_colon (Nat.le.refl) h_snt₁ h_nc_open
        (h_skdr_body'.trans h_skdr_close)
    refine ⟨(1 + n₂) + 1, s₃,
      (ScanChainGrew.single h_snt₁ h_grew₁).trans
        (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all, ?_⟩
    · rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · rw [h_ek₃, h_ek₂, h_ek₁]
    · rw [h_col₃]; omega
    · unfold ScannerState.inFlow
      exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · rw [_h_line₃, _h_line₂, _h_line₁]
    · exact h_atol₃
    · exact h_endline₃
    · rw [h_stack₃, h_stack₂, h_stack_pop₁]
    · exact (show (n₂ + 1) + 1 = (1 + n₂) + 1 by omega) ▸ h_skdr_all
  | mapping style pairs tag anchor _ hk hv _ihk _ihv =>
    intro s_state rest N hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_N h_sync
    have h_chars : (emit (.mapping style pairs tag anchor)).toList ++ rest =
        ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁, h_endline₁, h_stack_endline₁, h_stack_pop₁, h_sk_poss₁, h_toks_gt₁⟩ :=
      scanNextToken_flow_open_mapping_nested s_state
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    have h_pair_scan : EmitPairListScansInFlow pairs.toList := by
      match h_list : pairs.toList with
      | [] => exact emitPairList_scans_empty
      | _ :: _ =>
        exact (emitPairList_scans_nonempty _ (by simp) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow _ (hk ⟨i, h_sz⟩)) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow _ (hv ⟨i, h_sz⟩))).toWeak
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow, h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂⟩ :=
      h_pair_scan s₁ (['}'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
        (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃, _h_line₃, h_atol₃, h_endline₃, h_stack₃, _, _⟩ :=
      scanNextToken_flow_close_mapping_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ := h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le.refl) (by omega)).trans
        (h_fmc₂'.trans (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    have h_corr_state_cons : ScannerSurfCorr s_state
        ⟨'{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest), s_state.col⟩ := by
      have : ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest =
          '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      rwa [this] at hcorr₀
    have h_corr₂_cons : ScannerSurfCorr s₂ ⟨'}' :: rest, s₂.col⟩ := by
      have : ['}'] ++ rest = '}' :: rest := by simp
      rwa [this] at h_corr₂
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s₁ '{'
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s₂ s₃ '}' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂ (by decide) (by decide) (by decide) h_snt₃
    have h_s1_stacksize : s₁.simpleKeyStack.size = s_state.flowLevel + 1 := by
      have hp := congrArg Array.size h_stack_pop₁
      rw [Array.size_pop] at hp; omega
    have h_skf₁ : SimpleKeyAboveFloor s₁ (N + 1) s₁.flowLevel := by
      refine ⟨fun hp => absurd hp (by rw [h_sk_poss₁]; decide), fun j hfl hj _hp => ?_, ?_⟩
      · exfalso; rw [h_fl₁] at hfl; rw [h_s1_stacksize] at hj; omega
      · rw [h_fl₁]; omega
    have h_skdr_body : SavedKeyDoesntResolve s₁.flowLevel N s₁ n₂ s₂ :=
      SavedKeyDoesntResolve_of_FlowMonoChain_skFloor h_fmc₂ (by rw [h_fl₁]; omega)
        (by omega) h_skf₁ (by rw [h_fl₁]; omega)
    have h_skdr_body' : SavedKeyDoesntResolve s_state.flowLevel N s₁ n₂ s₂ :=
      h_skdr_body.weaken (by rw [h_fl₁]; omega)
    have h_nc_open : ∀ t c, scanNextToken_preprocess s_state = .ok (some (t, c)) → c ≠ ':' :=
      no_colon_of_preprocess_flow s_state '{' ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        s_state.col h_corr_state_cons h_flow (by decide) (by decide) (by decide) (by decide)
    have h_nc_close : ∀ t c, scanNextToken_preprocess s₂ = .ok (some (t, c)) → c ≠ ':' :=
      no_colon_of_preprocess_flow s₂ '}' rest s₂.col h_corr₂_cons h_s2_inflow
        (by decide) (by decide) (by decide) (by decide)
    have h_skdr_close : SavedKeyDoesntResolve s_state.flowLevel N s₂ 1 s₃ :=
      SavedKeyDoesntResolve.step_of_non_colon (by rw [h_fl₂, h_fl₁]; omega) h_snt₃ h_nc_close
        (.zero (by rw [h_fl₃, h_fl₂, h_fl₁]; omega))
    have h_skdr_all : SavedKeyDoesntResolve s_state.flowLevel N s_state ((n₂ + 1) + 1) s₃ :=
      SavedKeyDoesntResolve.step_of_non_colon (Nat.le.refl) h_snt₁ h_nc_open
        (h_skdr_body'.trans h_skdr_close)
    refine ⟨(1 + n₂) + 1, s₃,
      (ScanChainGrew.single h_snt₁ h_grew₁).trans
        (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all, ?_⟩
    · rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · rw [h_ek₃, h_ek₂, h_ek₁]
    · rw [h_col₃]; omega
    · unfold ScannerState.inFlow
      exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · rw [_h_line₃, _h_line₂, _h_line₁]
    · exact h_atol₃
    · exact h_endline₃
    · rw [h_stack₃, h_stack₂, h_stack_pop₁]
    · exact (show (n₂ + 1) + 1 = (1 + n₂) + 1 by omega) ▸ h_skdr_all

/-- Lift a `SavedKeyDoesntResolve` across a token-preserving preprocessing step.
    `scanNextToken_preprocess_flow_ws1` makes `scanNextToken s₂ = scanNextToken s₃`
    while preserving tokens (`s₃.tokens = s₂.tokens`), so a SKDR chain rooted at the
    preprocessed `s₃` re-roots at `s₂` step-for-step (the first step's position-`N+1`
    witness transfers through the token equality).  SKDR analogue of
    `ScanChainGrew_of_scanNextToken_eq` / `FlowMonoChain_of_scanNextToken_eq`. -/
theorem SavedKeyDoesntResolve_lift_preprocess {fl₀ N : Nat} {s₂ s₃ s_end : ScannerState}
    {n : Nat}
    (h_eq : scanNextToken s₂ = scanNextToken s₃)
    (h_fl₂ : s₂.flowLevel ≥ fl₀)
    (h_toks : s₃.tokens = s₂.tokens)
    (h : SavedKeyDoesntResolve fl₀ N s₃ (n + 1) s_end) :
    SavedKeyDoesntResolve fl₀ N s₂ (n + 1) s_end := by
  cases h with
  | step _h_fl₃ h_snt₃ h_pres h_rest =>
    refine .step h_fl₂ (h_eq.trans h_snt₃) ?_ h_rest
    intro h_size
    have h_size₃ : N + 1 < s₃.tokens.size := by rw [h_toks]; exact h_size
    obtain ⟨h_size_mid, h_eq_mid⟩ := h_pres h_size₃
    refine ⟨h_size_mid, ?_⟩
    rw [h_eq_mid]
    congr 1

/-- SKDR-augmented `EmitListScansInFlow`: see §H.2 header. -/
def EmitListScansInFlowSKDR (items : List YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char) (N : Nat),
    ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    N ≤ s.tokens.size →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      ∧ SavedKeyDoesntResolve s.flowLevel N s n s'

/-- SKDR-producing companion to `emitList_scans_nonempty`.  Walks the top-level
    flow-sequence body item-by-item; each item via `emit_scans_in_flow_with_skdr`,
    each comma via `step_of_non_colon` (the `ExactSync` invariant threads through
    the existing `simpleKeyStack`/`flowLevel` preservation conjuncts). -/
theorem emitList_scans_nonempty_with_skdr (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlowSKDR v) :
    EmitListScansInFlowSKDR items := by
  induction items with
  | nil => contradiction
  | cons v tail ih =>
    intro s rest_chars N hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_N h_sync
    match tail, ih with
    | [], _ =>
      have h_eq : (emit.emitList [v]).toList = (emit v).toList := by
        simp only [emit.emitList]
      rw [h_eq] at hcorr
      obtain ⟨n, s', h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow', h_indent', h_line_v, _, _, h_atol', h_endline', h_stack', h_fmc', h_skdr'⟩ :=
        h_all v (.head _) s rest_chars N hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_N h_sync
      exact ⟨n, s', h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow', h_indent', h_line_v, h_atol', h_endline', h_stack', h_fmc', h_skdr'⟩
    | v' :: vs, ih =>
      have h_eq : (emit.emitList (v :: v' :: vs)).toList ++ rest_chars =
          (emit v).toList ++ ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
        simp [emit.emitList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan emit v via EmitScansInFlowSKDR (at the same target N)
      have h_ev : EmitScansInFlowSKDR v := h_all v (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_flow₁, h_indent₁, _h_line₁, _h_ska₁, h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁, h_skdr₁⟩ :=
        h_ev s ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars) N
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_N h_sync
      -- Step 2: Scan ',' via scanNextToken_flow_comma
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂⟩ :=
        scanNextToken_flow_comma s₁
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ h_last₁ h_atol₁ h_endline₁
      obtain ⟨c, rest', h_first, h_nws, h_nlb, h_nc⟩ := emitList_first_char v' vs
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c :: (rest' ++ rest_chars), s₂.col⟩ := by
        have : ' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars =
            ' ' :: c :: (rest' ++ rest_chars) := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₂]; omega)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₂]; exact h_indent₁
      have h_s2_col : s₂.col > 0 := by rw [h_col₂]; omega
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c (rest' ++ rest_chars) h_corr₂_ws
          h_s2_flow h_nws h_nlb h_nc h_s2_indent
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit.emitList (v' :: vs)).toList ++ rest_chars, s₃.col⟩ := by
        have : c :: (rest' ++ rest_chars) = (emit.emitList (v' :: vs)).toList ++ rest_chars := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: Recursive scan of emitList (v' :: vs) from s₃ at the SAME N
      have h_tail_all : ∀ w ∈ v' :: vs, EmitScansInFlowSKDR w :=
        fun w hw => h_all w (.tail _ hw)
      have h_ih_list : EmitListScansInFlowSKDR (v' :: vs) := ih (by simp) h_tail_all
      -- N ≤ s₃.tokens.size (tokens grew) and ExactSync s₃ (threaded preservation)
      have h_N₃ : N ≤ s₃.tokens.size := by
        have h1 := h_fmc₁.tokens_mono
        have h2 := ScannerCorrectness.scanNextToken_adds_tokens s₁ s₂ h_snt₂
        have h3 : s₃.tokens.size = s₂.tokens.size := by rw [h_toks_pp₃]
        omega
      have h_sync₃ : s₃.simpleKeyStack.size = s₃.flowLevel := by
        rw [h_stack_pp₃, h_stack₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync
      obtain ⟨n₃, s_end, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc₃, h_skdr₃⟩ :=
        h_ih_list s₃ rest_chars N h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂, h_ek₁]; exact h_ek)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          h_N₃ h_sync₃
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit.emitList (v' :: vs)).toList = [] := by
            match h_list : (emit.emitList (v' :: vs)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          exact absurd h_nil (emitList_toList_ne_nil v' vs)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain₃
      have h_corr₁_cons : ScannerSurfCorr s₁
          ⟨',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars), s₁.col⟩ := by
        have : [',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars =
            ',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
          simp only [List.cons_append, List.nil_append]
        rwa [this] at h_corr₁
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size :=
        scanNextToken_filtered_grows_in_flow s₁ s₂ ','
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁ (by decide) (by decide) (by decide) h_snt₂
      have h_fmc₃' : FlowMonoChain s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      -- SKDR: item (n₁) + comma (non-`:`) + lifted tail (n₃'+1)
      have h_nc_comma : ∀ t cc, scanNextToken_preprocess s₁ = .ok (some (t, cc)) → cc ≠ ':' :=
        no_colon_of_preprocess_flow s₁ ',' (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          s₁.col h_corr₁_cons h_flow₁ (by decide) (by decide) (by decide) (by decide)
      have h_skdr_tail₂ : SavedKeyDoesntResolve s.flowLevel N s₂ (n₃' + 1) s_end :=
        SavedKeyDoesntResolve_lift_preprocess h_snt_eq (by rw [h_fl₂, h_fl₁]; omega)
          h_toks_pp₃ ((show s.flowLevel = s₃.flowLevel from by omega) ▸ h_skdr₃)
      have h_skdr_comma : SavedKeyDoesntResolve s.flowLevel N s₁ ((n₃' + 1) + 1) s_end :=
        SavedKeyDoesntResolve.step_of_non_colon (by rw [h_fl₁]; omega) h_snt₂ h_nc_comma h_skdr_tail₂
      have h_skdr_all : SavedKeyDoesntResolve s.flowLevel N s (n₁ + ((n₃' + 1) + 1)) s_end :=
        h_skdr₁.trans h_skdr_comma
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all,
        (show n₁ + ((n₃' + 1) + 1) = n₁ + 1 + (n₃' + 1) from by omega) ▸ h_skdr_all⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂, h_ek₁]
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack₂, h_stack₁]

-- Helper: extract existential from isOk
theorem scanFiltered_exists_of_isOk {s : String}
    (h : (Scanner.scanFiltered s).toBool = true) :
    ∃ tokens, Scanner.scanFiltered s = .ok tokens := by
  cases h_eq : Scanner.scanFiltered s with
  | ok tokens => exact ⟨tokens, rfl⟩
  | error _ =>
    exfalso; revert h; simp [h_eq]; rfl

/-- **Main theorem**: The scanner accepts any canonical emitter output.

    For any grammable `YamlValue`, `scanFiltered (emit v)` succeeds.
    This is Step 1 of the universal round-trip proof.

    **Proof strategy**: Structural induction on `YamlValue`.
    - Scalar case: delegates to `scan_accepts_emitScalar`
    - Sequence/mapping cases: delegates to scanner acceptance of
      flow collections with inductively-accepted sub-expressions
    - Alias case: impossible (excluded by `Grammable`)

    Note: generalized to arbitrary `inFlow` to enable structural induction
    on `Grammable`. The `emit` function ignores `inFlow` (always produces
    flow format), so scanner acceptance is independent of the flow context
    under which the value is grammable. -/
theorem emit_produces_valid_yaml (v : YamlValue) {inFlow : Bool} (hg : Grammable v inFlow) :
    ∃ tokens, scanFiltered (emit v) = .ok tokens := by
  induction hg with
  | scalar s _ h =>
    -- emit (.scalar s) = emitScalar s.content
    exact scan_accepts_emitScalar s.content
  | sequence style items tag anchor _ h ih =>
    -- emit (.sequence style items tag anchor) = "[" ++ emitList items.toList ++ "]"
    change ∃ tokens, scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens
    match h_items : items.toList with
    | [] =>
      simp only [emit.emitList]
      exact scanFiltered_exists_of_isOk (by native_decide)
    | _ :: _ =>
      -- Non-empty: compose flow open '[', body scanning, flow close ']', EOF
      -- Rewrite goal back to use items.toList (match substituted it)
      simp only [← h_items]
      -- Step 1: Show input.toList starts with '['
      have h_toList : ("[" ++ emit.emitList items.toList ++ "]").toList =
          '[' :: (emit.emitList items.toList).toList ++ [']'] := by
        simp only [String.toList_append]; rfl
      -- Step 2: Scan '[' from initial state via flow_open_init
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
              h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, _h_sk₁, _h_filt₁, _⟩ :=
        scanNextToken_flow_open_init ("[" ++ emit.emitList items.toList ++ "]")
          ((emit.emitList items.toList).toList ++ [']']) h_toList
      -- Step 3: Build EmitListScansInFlow for non-empty items list
      have h_list_scan : EmitListScansInFlow items.toList :=
        emitList_scans_nonempty items.toList (by simp [h_items]) (fun w hw => by
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw
          have h_sz : i < items.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow items[i] (h ⟨i, h_sz⟩))
      -- Step 4: Apply body scanning (emitList → ScanChain through body)
      obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
              h_ek₂, h_col₂, h_inflow₂, h_indent₂, _h_line₂, _, _, _, _⟩ :=
        h_list_scan s₁ [']'] h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega)
          h_indent₁ (by rw [h_col₁]; omega) h_ek₁
          (h_line₁ ▸ h_atol₁) -- AllTokensOnLine s₁ s₁.line
          h_endline₁ -- EndLineOnLine s₁
      -- Step 5: Scan ']' (outermost, flowLevel = 1 → 0)
      obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃⟩ :=
        scanNextToken_flow_close_seq_outermost s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
          (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
      -- Step 6: EOF
      have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
      -- Step 7: BOM check (input starts with '[', not BOM)
      have h_no_bom : (ScannerState.mk' ("[" ++ emit.emitList items.toList ++ "]")).peek?
          ≠ some '\uFEFF' := by
        have h_chars := chars_from_zero_toList ("[" ++ emit.emitList items.toList ++ "]")
        rw [h_toList] at h_chars
        have h_corr := initial_corr _ _ h_chars
        have ⟨h_pk, _⟩ := peek_of_chars_cons _ '['
          ((emit.emitList items.toList).toList ++ [']']) 0 h_corr
        rw [h_pk]; decide
      -- Step 8: Compose chain: '[' (1 step) + body (n₂ steps) + ']' (1 step)
      -- Forget the strict ScanChainGrew witness back to ScanChain for the consumer.
      have h_chain_all := (ScanChain.single h_snt₁).trans
        (h_chain₂.toScanChain.trans (ScanChain.single h_snt₃))
      -- Apply scanFiltered_of_chain
      exact scanFiltered_of_chain _ _ s₃ _ rfl h_no_bom h_chain_all h_eof h_fl₃ h_dp₃
        (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
  | mapping style pairs tag anchor _ hk hv ihk ihv =>
    -- emit (.mapping style pairs tag anchor) = "{" ++ emitPairList pairs.toList ++ "}"
    change ∃ tokens, scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens
    match h_pairs : pairs.toList with
    | [] =>
      simp only [emit.emitPairList]
      exact scanFiltered_exists_of_isOk (by native_decide)
    | _ :: _ =>
      -- Non-empty: compose flow open '{', body scanning, flow close '}', EOF
      simp only [← h_pairs]
      -- Step 1: Show input.toList starts with '{'
      have h_toList : ("{" ++ emit.emitPairList pairs.toList ++ "}").toList =
          '{' :: (emit.emitPairList pairs.toList).toList ++ ['}'] := by
        simp only [String.toList_append]; rfl
      -- Step 2: Scan '{' from initial state via flow_open_mapping_init
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
              h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, _h_sk₁, _h_filt₁, _⟩ :=
        scanNextToken_flow_open_mapping_init ("{" ++ emit.emitPairList pairs.toList ++ "}")
          ((emit.emitPairList pairs.toList).toList ++ ['}']) h_toList
      -- Step 3: Build EmitPairListScansInFlow for non-empty pair list
      have h_pair_scan : EmitPairListScansInFlow pairs.toList :=
        (emitPairList_scans_nonempty pairs.toList (by simp [h_pairs]) (fun p hp => by
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow pairs[i].1 (hk ⟨i, h_sz⟩)) (fun p hp => by
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow pairs[i].2 (hv ⟨i, h_sz⟩))).toWeak
      -- Step 4: Apply body scanning
      obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
              h_ek₂, h_col₂, h_inflow₂, h_indent₂, _h_line₂, _, _, _, _⟩ :=
        h_pair_scan s₁ ['}'] h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega)
          h_indent₁ (by rw [h_col₁]; omega) h_ek₁
          (h_line₁ ▸ h_atol₁) -- AllTokensOnLine s₁ s₁.line
          h_endline₁ -- EndLineOnLine s₁
      -- Step 5: Scan '}' (outermost, flowLevel = 1 → 0)
      obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃⟩ :=
        scanNextToken_flow_close_mapping_outermost s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
          (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
      -- Step 6: EOF
      have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
      -- Step 7: BOM check (input starts with '{', not BOM)
      have h_no_bom : (ScannerState.mk' ("{" ++ emit.emitPairList pairs.toList ++ "}")).peek?
          ≠ some '\uFEFF' := by
        have h_chars := chars_from_zero_toList ("{" ++ emit.emitPairList pairs.toList ++ "}")
        rw [h_toList] at h_chars
        have h_corr := initial_corr _ _ h_chars
        have ⟨h_pk, _⟩ := peek_of_chars_cons _ '{'
          ((emit.emitPairList pairs.toList).toList ++ ['}']) 0 h_corr
        rw [h_pk]; decide
      -- Step 8: Compose chain
      -- Forget the strict ScanChainGrew witness back to ScanChain for the consumer.
      have h_chain_all := (ScanChain.single h_snt₁).trans
        (h_chain₂.toScanChain.trans (ScanChain.single h_snt₃))
      -- Apply scanFiltered_of_chain
      exact scanFiltered_of_chain _ _ s₃ _ rfl h_no_bom h_chain_all h_eof h_fl₃ h_dp₃
        (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)

/-! ## §4  Full Pipeline: Emit → Scan → Parse

Combining scanner acceptance (Step 1) with parser acceptance (Step 2).

### Step 2 Architecture

Step 1 gives us `scanFiltered (emit v) = .ok tokens`. Step 2 must show
that `parseStream` also succeeds on those tokens. The key argument:

1. **Stream boundaries**: `scanFiltered` always produces `streamStart` as
   the first token and `streamEnd` as the last (by scanner construction).
2. **Single implicit document**: The emitter produces no `---`/`...` markers
   and no directives, so `parseStreamLoop` in `.initial` state sees bare
   content → enters `parseDocument` with no directive overhead.
3. **No bare-document violation**: After the single document is parsed, only
   `streamEnd` remains. `StreamState.validNextToken .afterDocument .streamEnd`
   is always `true`, so `invalidBareDocument` cannot fire.
4. **Parser dispatch succeeds**: `parseNode` dispatches on token type:
   - `scalar` (double-quoted) → single token consumption, always succeeds
   - `flowSequenceStart` → `parseFlowSequence` handles `[`, `,`, `]`
   - `flowMappingStart` → `parseFlowMapping` handles `{`, `:`, `,`, `}`
5. **Fuel sufficiency**: `parseStream` allocates `tokens.size` fuel.
   Each recursive `parseNode` call consumes ≥1 token, so fuel cannot
   be exhausted for well-formed flow output.
6. **No semantic errors**: The emitter produces no anchors (no
   `duplicateAnchor`), no aliases (no `undefinedAlias`), no tags (no
   `undeclaredTagHandle`), and no block content (no `trailingContent`
   on document start line).
-/

-- ═══ Challenge 2: parseStreamLoop state machine — single implicit document ═══
-- If the parser sees content (not streamEnd), parseDocument succeeds and
-- leaves peek? at streamEnd, then parseStreamLoop produces exactly one document.
theorem parseStreamLoop_single_doc
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≥ 2)
    (tok : YamlToken) (h_peek : ps.peek? = some tok) (h_not_se : tok ≠ .streamEnd)
    (doc : YamlDocument) (ps' : ParseState)
    (h_doc : parseDocument ps = .ok (doc, ps'))
    (h_peek' : ps'.peek? = some .streamEnd) :
    parseStreamLoop ps #[] .initial fuel = .ok #[doc] := by
  -- Two iterations: first parses document, second sees streamEnd and returns.
  cases fuel with
  | zero => omega
  | succ fuel' => cases fuel' with
    | zero => omega
    | succ f =>
      -- First iteration: unfold parseStreamLoop, resolve fuel match
      unfold parseStreamLoop; dsimp only []  -- reduce Nat.succ match
      rw [h_peek]  -- substitute ps.peek? = some tok
      -- Case-split by YamlToken constructor to resolve the compiled match.
      -- .streamEnd is impossible (contradicts h_not_se); all others take catch-all.
      cases tok
      <;> first | exact absurd rfl h_not_se | skip
      -- All 22 remaining goals: content branch (identical proof)
      all_goals (
        dsimp only []  -- reduce the YamlToken match
        simp only [StreamState.validNextToken, Bool.not_true]
        rw [h_doc]; dsimp only []
        have h_peek'_r : (ParseState.mk ps'.tokens ps'.pos #[]
            ps'.tagHandles ps'.trackPositions #[] #[]).peek?
            = some .streamEnd := h_peek'
        simp only [ParseState.tryConsume, h_peek'_r,
                   show (BEq.beq YamlToken.streamEnd YamlToken.documentEnd) = false
                     from by decide]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [parseStreamLoop, h_peek'_r]
        -- Both if-branches are identical (stuck or not, result is same)
        split <;> rfl)

/-- **Grammability preservation**: The parsed output of emitter output
    is grammable. Follows from `parseStream_output_grammable` applied
    to the scan+parse decomposition. -/
theorem emit_parsed_grammable (v : YamlValue)
    (docs : Array YamlDocument)
    (h : parseYaml (emit v) = .ok docs) :
    ∀ doc ∈ docs.toList, Grammable doc.value false := by
  simp only [parseYaml] at h
  split at h
  · rename_i raw_docs h_raw
    injection h with h_eq
    have ⟨tokens, h_scan, h_parse⟩ := Composition.parseYamlRaw_ok_decompose (emit v) raw_docs h_raw
    have h_gram := ParserGrammable.parseStream_output_grammable (emit v) tokens raw_docs h_scan h_parse
    intro doc hdoc
    rw [← h_eq] at hdoc
    simp only [Array.toList_map] at hdoc
    obtain ⟨raw_doc, h_raw_mem, h_compose_eq⟩ := List.mem_map.mp hdoc
    subst h_compose_eq
    exact h_gram raw_doc h_raw_mem
  · simp at h


end L4YAML.Proofs.EmitterScannability
