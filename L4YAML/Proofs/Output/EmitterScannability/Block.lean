import L4YAML.Proofs.Output.EmitterScannability.WellBracketed

/-!
# Block-tracking substrate for flow-collection emitter scannability

Extracted from `L4YAML.Proofs.Output.EmitterScannability` (2026-05-31) to keep the
base file manageable.  **Re-parented (2026-05-31) to import `WellBracketed` directly**
instead of the base — moving the whole block-tracking layer *upstream* of
`NonemptyStructure` so the round-trip body characterizations can consume
`emit_scans_in_flow_block` (the `.bridge.assemble` dependency inversion).  Block uses
nothing from the base or `NonemptyStructure`, so the move is purely structural.
Contains the block-tracking *superset* predicates
(`EmitScansInFlowBlock`, `EmitListScansInFlowBlock`, `EmitScansInFlowSavedKeyBlock`,
`EmitPairListScansInFlowBlock`) and their producers, which expose the filtered-LIST
`WellBracketed` `block` that the round-trip bridge's `.assemble` step consumes at the
flow-body characterization sites (legacy sorries 9646 / 9552).

These declarations stay in the original `L4YAML.Proofs.EmitterScannability` namespace,
so their fully-qualified names are unchanged by the move.
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

open L4YAML.Proofs.ParserGrammable (flowBracketDelta flowBracketBalance
  flowBracketBalance_compose flowBracketBalance_push)

/-! ### §G.balance.bridge.blockwb.predicate — per-`emit v` block-EntrySafe substrate

    `EmitScansInFlowBlock v` is a **superset** of `EmitScansInFlow v`: the same
    preconditions and *all* the same state postconditions, plus the filtered-LIST
    delta exposed as an explicit `block` with three combinatorial facts —
    `WellBracketed block`, `EntrySafe block`, and a content-start head.  These are
    what the bridge's outer assembly (`.assemble`) consumes to build a `SafeBody`
    at the two characterization sorry sites (9552 / 9646).

    This session lands the **sequence-side** substrate: the per-value predicate
    (full superset), the list-body predicate `EmitListScansInFlowBlock` (whose
    `block` is `WellBracketed`, the shape `wrap_seq_block` wraps), the comma
    separator push lemma above, and the `WellBracketed`-body list producer
    `emitList_scans_block_nonempty` (parallel to `emitList_scans_nonempty`,
    consuming the per-item block as hypothesis).  The mapping-body predicate and
    the monolithic `Grammable` producer `emit_scans_in_flow_block` are deferred:
    the mapping body's `WellBracketed`-ness hinges on the colon's retroactive
    placeholder→`.key` insertion (the list form of the discharged 9644 machinery),
    a separate harder sub-task. -/

/-- A content-start token: a scalar, or the opener of a flow sequence/mapping —
    the value of the first filtered token any `emit v` block produces.  This is
    the `Q` predicate the sequence-body `SafeBody` is built over. -/
def ContentStartTok (t : YamlToken) : Prop :=
  (∃ c st, t = .scalar c st) ∨ t = .flowSequenceStart ∨ t = .flowMappingStart

/-- Block-tracking superset of `EmitScansInFlow`: additionally exposes the
    filtered-LIST delta `block` of scanning `emit v`, with `block` `WellBracketed`
    (closes into a `WellBracketed` body) and `EntrySafe` with a content-start
    head (serves as a `SafeBody` entry). -/
def EmitScansInFlowBlock (v : YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit v).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s' block,
      ScanChainGrew (fun t => t.val != .placeholder) s n s'
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
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
      ∧ WellBracketed block
      ∧ EntrySafe block
      ∧ (∃ (h : block ≠ []), ContentStartTok (block.head h).val)

/-- Block-tracking superset of `EmitListScansInFlow`: the comma-separated body
    between `[` and `]`.  Its filtered-LIST delta `block` is `WellBracketed` —
    exactly the interior `wrap_seq_block` frames into a flow-sequence block. -/
def EmitListScansInFlowBlock (items : List YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s' block,
      ScanChainGrew (fun t => t.val != .placeholder) s n s'
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
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
      ∧ WellBracketed block

/-- Empty list body: 0-step chain, empty (`WellBracketed`) block. -/
theorem emitList_scans_block_empty : EmitListScansInFlowBlock [] := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline _h_sync
  have h_eq : (emit.emitList ([] : List YamlValue)).toList ++ rest = rest := by
    simp only [emit.emitList]; rfl
  rw [h_eq] at hcorr
  exact ⟨0, s, [], .zero, hcorr, rfl, rfl, rfl, rfl, h_col, h_flow, h_indent, rfl,
    h_atol, h_endline, rfl, .zero (Nat.le.refl), by simp, WellBracketed_nil⟩

/-- Non-empty list body via induction on the item list, parallel to
    `emitList_scans_nonempty` but additionally accumulating the `WellBracketed`
    block: each item block (from `EmitScansInFlowBlock`) is `WellBracketed`, each
    `", "` separator contributes a single delta-`0` `.flowEntry`, and the recursive
    tail block is `WellBracketed`; `WellBracketed_append` glues them. -/
theorem emitList_scans_block_nonempty (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlowBlock v) :
    EmitListScansInFlowBlock items := by
  induction items with
  | nil => contradiction
  | cons v tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
    match tail, ih with
    | [], _ =>
      have h_eq : (emit.emitList [v]).toList = (emit v).toList := by
        simp only [emit.emitList]
      rw [h_eq] at hcorr
      obtain ⟨n, s', block, h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow',
              h_indent', h_line_v, _h_ska, _h_last, h_atol', h_endline', h_stack', h_fmc',
              h_block_eq, h_wb, _h_es, _h_cs⟩ :=
        h_all v (.head _) s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      exact ⟨n, s', block, h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow',
        h_indent', h_line_v, h_atol', h_endline', h_stack', h_fmc', h_block_eq, h_wb⟩
    | v' :: vs, ih =>
      have h_eq : (emit.emitList (v :: v' :: vs)).toList ++ rest_chars =
          (emit v).toList ++ ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
        simp [emit.emitList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan emit v via EmitScansInFlowBlock (item block `block₁`)
      have h_ev : EmitScansInFlowBlock v := h_all v (.head _)
      obtain ⟨n₁, s₁, block₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_flow₁,
              h_indent₁, _h_line₁, _h_ska₁, h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_block_eq₁, h_wb₁, _h_es₁, _h_cs₁⟩ :=
        h_ev s ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
      -- Step 2: Scan ',' via scanNextToken_flow_comma (state) + push lemma (block)
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, _h_line₂, h_atol₂, h_endline₂, h_stack₂⟩ :=
        scanNextToken_flow_comma s₁
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁
          h_last₁ h_atol₁ h_endline₁
      obtain ⟨feTok, h_feTok_val, h_comma_eq⟩ :=
        scanNextToken_flow_comma_filtered_push s₁
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ h_last₁ h_snt₂
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
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit.emitList (v' :: vs)).toList ++ rest_chars, s₃.col⟩ := by
        have : c :: (rest' ++ rest_chars) = (emit.emitList (v' :: vs)).toList ++ rest_chars := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: Recursive scan of emitList (v' :: vs) from s₃ (tail block `block_rest`)
      have h_tail_all : ∀ w ∈ v' :: vs, EmitScansInFlowBlock w :=
        fun w hw => h_all w (.tail _ hw)
      have h_ih_list : EmitListScansInFlowBlock (v' :: vs) :=
        ih (by simp) h_tail_all
      obtain ⟨n₃, s_end, block_rest, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc₃, h_block_eq_end, h_wb_rest⟩ :=
        h_ih_list s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂, h_ek₁]; exact h_ek)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_stack_pp₃, h_stack₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
      -- Step 5: Lift chain for s₂ via preprocessing equality
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
      have h_fmc₃' : FlowMonoChain s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      -- Block accumulation: block = block₁ ++ [feTok] ++ block_rest
      -- s₃ filtered toList = s₁ ++ [feTok] (comma push, space preserves tokens)
      have h_block_eq₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ (block₁ ++ [feTok]) := by
        have h_s3_s2 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp₃]
        rw [h_s3_s2, congrArg Array.toList h_comma_eq, Array.toList_push, h_block_eq₁,
            List.append_assoc]
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, block₁ ++ [feTok] ++ block_rest,
        h_arith ▸ h_chain_all, h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end,
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, ?_, ?_⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂, h_ek₁]
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack₂, h_stack₁]
      · -- block equation: s_end = s₃ ++ block_rest = s ++ (block₁ ++ [feTok]) ++ block_rest
        rw [h_block_eq_end, h_block_eq₃, List.append_assoc]
      · -- WellBracketed (block₁ ++ [feTok] ++ block_rest)
        exact WellBracketed_append _ _
          (WellBracketed_append _ _ h_wb₁
            (WellBracketed_singleton_delta_zero feTok (by rw [h_feTok_val]; exact flowBracketDelta_flowEntry)))
          h_wb_rest

/-- **Combined per-key substrate** for the mapping-body producer: the saved-key
    layout (`EmitScansInFlowSavedKey`) *and* the `WellBracketed` filtered block
    (`EmitScansInFlowBlock`) of scanning the key `emit v` in flow, produced together by
    one chain so the mapping-body producer never has to *reconcile* two separate scans
    of the same key.

    Reconciling a `EmitScansInFlowBlock` run and a `EmitScansInFlowSavedKey` run of the
    same key would require a `scanNextToken` strict-offset-progress capstone (to force
    the two chains' step counts equal so `ScanChain_deterministic` applies) — the
    non-indexed §11 capstone is unproved (only the indexed `scanNextTokenIx_offset_gt`
    exists).  Bundling both effects into one predicate sidesteps that entirely.

    The block conjuncts mirror `EmitScansInFlowBlock` (append-equation + `WellBracketed`),
    plus a **take-side filter equation** `(s'.tokens.take (N+1)).filter = s.tokens.filter`
    (`N = s.tokens.size`): with the layout's slot-`N+1` placeholder, this lets the colon's
    mid-key insertion (`scanNextToken_flow_value_block`) re-anchor to the pair-start prefix
    as the clean front-insert `.key :: block_k` via `List_filter_drop_succ_of_take`.
    The producer (`emit_scans_in_flow_saved_key_block`, by `Grammable` induction — deferred)
    proves it; its mapping case feeds `emitPairList_scans_block_nonempty` with the key IH. -/
def EmitScansInFlowSavedKeyBlock (v : YamlValue) : Prop :=
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
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s' block,
      ScanChainGrew (fun t => t.val != .placeholder) s n s'
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
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
      ∧ (s'.tokens.toList.take (s.tokens.size + 1)).filter (fun t => t.val != .placeholder)
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
      ∧ WellBracketed block

/-- Block-tracking superset of `EmitPairListScansInFlow`: the comma-separated
    `key: value` body between `{` and `}` in a flow mapping.  Its filtered-LIST delta
    `block` is `WellBracketed` — exactly the interior `wrap_map_block` frames into a
    flow-mapping block.

    Unlike the sequence-side `EmitListScansInFlowBlock`, this predicate carries the
    three **simple-key** preconditions (`simpleKey.possible = false`,
    `simpleKeyAllowed = true`, `simpleKeyStack.size = flowLevel`): the per-pair colon step
    retroactively converts a reserved placeholder to `.key`, and these invariants (the
    same ones `EmitScansInFlowSavedKeyBlock` — the per-key combined substrate — requires)
    are what let the producer pin that `.key` at the pair-start rank.  A `{`-opener
    establishes them, and the comma re-establishes them for each subsequent pair
    (`scanNextToken_flow_comma` sets `simpleKeyAllowed := true` and preserves the
    stack; the value's `EmitScansInFlowBlock` leaves `simpleKey.possible = false`).
    `SimpleKeyStackValid` is *not* needed — the combined key substrate derives the
    colon's placeholder layout without it. -/
def EmitPairListScansInFlowBlock (pairs : List (YamlValue × YamlValue)) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    s.simpleKeyAllowed = true →
    s.simpleKeyStack.size = s.flowLevel →
    ∃ n s' block,
      ScanChainGrew (fun t => t.val != .placeholder) s n s'
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
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block
      ∧ WellBracketed block

/-- Empty pair-list body: 0-step chain, empty (`WellBracketed`) block. -/
theorem emitPairList_scans_block_empty : EmitPairListScansInFlowBlock [] := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
  have h_eq : (emit.emitPairList ([] : List (YamlValue × YamlValue))).toList ++ rest = rest := by
    simp [emit.emitPairList]
  rw [h_eq] at hcorr
  exact ⟨0, s, [], .zero, hcorr, rfl, rfl, rfl, rfl, h_col, h_flow, h_indent, rfl,
    h_atol, h_endline, rfl, .zero (Nat.le.refl), by simp, WellBracketed_nil⟩

/-- **Non-empty pair-list body producer** (the mapping-side analogue of
    `emitList_scans_block_nonempty`).  Builds the `WellBracketed` filtered block of
    scanning `emitPairList pairs` between `{` and `}` from per-key combined substrates
    (`EmitScansInFlowSavedKeyBlock` — layout + key block + take-side re-anchor) and
    per-value blocks (`EmitScansInFlowBlock`).  This is the **reconciliation-free**
    pivot: the key is scanned exactly once, and the colon's retroactive
    placeholder→`.key` insertion is pinned to the pair-start prefix via the take-side
    equation + `List_filter_drop_succ_of_take`, so the per-pair filtered delta is the
    clean `.key :: block_k ++ [.value] ++ block_v` (each piece delta-0 or `WellBracketed`),
    glued by `WellBracketed_append`.  The `", "` separator between pairs contributes one
    delta-0 `.flowEntry` and re-establishes the per-pair simple-key preconditions
    (`scanNextToken_flow_comma_simpleKey` + the ws1 simple-key preservation). -/
theorem emitPairList_scans_block_nonempty (pairs : List (YamlValue × YamlValue))
    (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlowSavedKeyBlock p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlowBlock p.2) :
    EmitPairListScansInFlowBlock pairs := by
  induction pairs with
  | nil => contradiction
  | cons p tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
    match tail, ih with
    | [], _ =>
      -- ══ Singleton [(k,v)]: emitPairList [(k,v)] = emit k ++ ": " ++ emit v ══
      have h_eq : (emit.emitPairList [p]).toList ++ rest_chars =
          (emit p.1).toList ++ ([':', ' '] ++ (emit p.2).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan key via EmitScansInFlowSavedKeyBlock (saved-key layout + key block)
      have h_ek_key : EmitScansInFlowSavedKeyBlock p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, block_k, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_ska₁, h_poss₁, h_tidx₁, h_szlt₁, _h_ph0₁, h_ph1₁, h_blockeq_k, h_take_k, h_wb_k⟩ :=
        h_ek_key s ([':', ' '] ++ (emit p.2).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
      -- Step 2: scanValueValidate for the colon (saveSimpleKey identity, ska₁ = false)
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      -- Step 3: Scan ':' — state via scanNextToken_flow_value
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁ ((emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      -- Step 3b: Scan ':' — filtered-LIST equation via scanNextToken_flow_value_block
      have h_lt_k : s₁.simpleKey.tokenIndex + 1 < s₁.tokens.size := by rw [h_tidx₁]; exact h_szlt₁
      have h_ph_k : (s₁.tokens[s₁.simpleKey.tokenIndex + 1]'h_lt_k).val = .placeholder := by
        simp only [h_tidx₁]; exact h_ph1₁ h_szlt₁
      obtain ⟨s₂', pos_v, h_snt₂', h_block_colon⟩ :=
        scanNextToken_flow_value_block s₁ ((emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁ h_ska₁ h_poss₁ h_lt_k h_ph_k
      have h_s2_eq : s₂' = s₂ := Option.some.inj (Except.ok.inj (h_snt₂'.symm.trans h_snt₂))
      rw [h_s2_eq] at h_block_colon
      -- Re-anchor the colon's mid-key insertion to the pair-start prefix.
      have h_hk : s.tokens.size + 1 < s₁.tokens.toList.length := by
        rw [Array.length_toList]; exact h_szlt₁
      have h_old : (fun t : Positioned YamlToken => t.val != .placeholder)
          (s₁.tokens.toList[s.tokens.size + 1]'h_hk) = false := by
        have hph := h_ph1₁ h_szlt₁
        simp only [Array.getElem_toList, hph]; rfl
      have h_full : s₁.tokens.toList.filter (fun t => t.val != .placeholder)
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block_k := by
        rw [← Array.toList_filter]; exact h_blockeq_k
      have h_drop : (s₁.tokens.toList.drop (s.tokens.size + 2)).filter
            (fun t => t.val != .placeholder) = block_k :=
        List_filter_drop_succ_of_take s₁.tokens.toList (s.tokens.size + 1)
          (fun t => t.val != .placeholder) h_hk h_old _ block_k h_take_k h_full
      rw [h_tidx₁, h_take_k, h_drop] at h_block_colon
      -- block_kc = .key :: (block_k ++ [.value]) (the per-key+colon filtered delta)
      have h_block_kc : (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                (block_k ++ [⟨pos_v, .value, pos_v⟩])) := by
        rw [h_block_colon]; simp only [List.append_assoc, List.cons_append]
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
      -- Step 5: Scan value via EmitScansInFlowBlock (value block block_v)
      have h_ev : EmitScansInFlowBlock p.2 := h_all_v p (.head _)
      obtain ⟨n_v, s_end, block_v, h_chain_v, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, _h_ska_v, _h_last_v,
              h_atol_end, h_endline_end, h_stack_end, h_fmc_v, h_blockeq_v, h_wb_v, _h_es_v, _h_cs_v⟩ :=
        h_ev s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_stack_pp₃, h_stack_v₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
      -- Step 6: Lift chain for s₂ via preprocessing equality
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n_v_pos : n_v ≥ 1 := by
        match n_v, h_chain_v with
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
      obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n_v' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain_v
      -- Per-step witness for the colon step (s₁ → s₂)
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
      have h_fmc_v' : FlowMonoChain s.flowLevel s₃ (n_v' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc_v
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n_v' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc_v'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n_v' + 1)) = n₁ + 1 + (n_v' + 1) := by omega
      -- Block accumulation: block = (.key :: block_k ++ [.value]) ++ block_v
      have h_block_end : (s_end.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ ((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) := by
        have h_s3_s2 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp₃]
        rw [h_blockeq_v, h_s3_s2, h_block_kc, List.append_assoc]
      refine ⟨n₁ + 1 + (n_v' + 1), s_end,
        (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ :: (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v,
        h_arith ▸ h_chain_all, h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end,
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, h_block_end, ?_⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack_v₂, h_stack₁]
      · -- WellBracketed ((.key :: block_k ++ [.value]) ++ block_v)
        exact WellBracketed_append _ _
          (WellBracketed_cons_delta_zero _ _ flowBracketDelta_key
            (WellBracketed_append _ _ h_wb_k
              (WellBracketed_singleton_delta_zero _ (by rfl))))
          h_wb_v
    | p' :: ps, ih =>
      -- ══ Multi-pair: emit k ++ ": " ++ emit v ++ ", " ++ emitPairList (p' :: ps) ══
      have h_eq : (emit.emitPairList (p :: p' :: ps)).toList ++ rest_chars =
          (emit p.1).toList ++ ([':', ' '] ++ (emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan key via EmitScansInFlowSavedKeyBlock
      have h_ek_key : EmitScansInFlowSavedKeyBlock p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, block_k, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_ska₁, h_poss₁, h_tidx₁, h_szlt₁, _h_ph0₁, h_ph1₁, h_blockeq_k, h_take_k, h_wb_k⟩ :=
        h_ek_key s ([':', ' '] ++ (emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
      -- Step 2: scanValueValidate for the colon
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      -- Step 3: Scan ':' — state
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂, _, _, _⟩ :=
        scanNextToken_flow_value s₁
          ((emit p.2).toList ++ [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      -- Step 3b: Scan ':' — filtered-LIST equation
      have h_lt_k : s₁.simpleKey.tokenIndex + 1 < s₁.tokens.size := by rw [h_tidx₁]; exact h_szlt₁
      have h_ph_k : (s₁.tokens[s₁.simpleKey.tokenIndex + 1]'h_lt_k).val = .placeholder := by
        simp only [h_tidx₁]; exact h_ph1₁ h_szlt₁
      obtain ⟨s₂', pos_v, h_snt₂', h_block_colon⟩ :=
        scanNextToken_flow_value_block s₁
          ((emit p.2).toList ++ [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁ h_ska₁ h_poss₁ h_lt_k h_ph_k
      have h_s2_eq : s₂' = s₂ := Option.some.inj (Except.ok.inj (h_snt₂'.symm.trans h_snt₂))
      rw [h_s2_eq] at h_block_colon
      have h_hk : s.tokens.size + 1 < s₁.tokens.toList.length := by
        rw [Array.length_toList]; exact h_szlt₁
      have h_old : (fun t : Positioned YamlToken => t.val != .placeholder)
          (s₁.tokens.toList[s.tokens.size + 1]'h_hk) = false := by
        have hph := h_ph1₁ h_szlt₁
        simp only [Array.getElem_toList, hph]; rfl
      have h_full : s₁.tokens.toList.filter (fun t => t.val != .placeholder)
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList ++ block_k := by
        rw [← Array.toList_filter]; exact h_blockeq_k
      have h_drop : (s₁.tokens.toList.drop (s.tokens.size + 2)).filter
            (fun t => t.val != .placeholder) = block_k :=
        List_filter_drop_succ_of_take s₁.tokens.toList (s.tokens.size + 1)
          (fun t => t.val != .placeholder) h_hk h_old _ block_k h_take_k h_full
      rw [h_tidx₁, h_take_k, h_drop] at h_block_colon
      have h_block_kc : (s₂.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ (⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                (block_k ++ [⟨pos_v, .value, pos_v⟩])) := by
        rw [h_block_colon]; simp only [List.append_assoc, List.cons_append]
      -- Step 4: Handle leading space before value
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₂.col⟩ := by
        have h_eq_chars : (' ' :: (emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) =
            (' ' :: c_v :: (rest_v ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₂
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _, _⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_v
          (rest_v ++ [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₂_ws h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars, s₃.col⟩ := by
        have h_eq_chars : (c_v :: (rest_v ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) =
            ((emit p.2).toList ++
            [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
          rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₃
      -- Step 5: Scan value via EmitScansInFlowBlock
      have h_ev : EmitScansInFlowBlock p.2 := h_all_v p (.head _)
      have h_corr₃_assoc : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++ ([',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₃.col⟩ := by
        simp only [List.append_assoc] at h_corr₃' ⊢; exact h_corr₃'
      obtain ⟨n_v, s_v, block_v, h_chain_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v,
              h_ek_v, h_col_v, h_flow_v, h_indent_v, _h_line_v, h_ska_v, h_last_v,
              h_atol_v, h_endline_v, h_stack_v, h_fmc_v, h_blockeq_v, h_wb_v, _h_es_v, _h_cs_v⟩ :=
        h_ev s₃ ([',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₃_assoc
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
          (by rw [h_stack_pp₃, h_stack_v₂, h_stack₁, h_fl₃, h_fl₂, h_fl₁]; exact h_sync)
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
      -- Step 6: Scan ',' via scanNextToken_flow_comma (state) + companions (block, simpleKey)
      obtain ⟨s_c, h_snt_c, h_corr_c, h_fl_c, h_dp_c, h_ids_c, h_ek_c, h_col_c, _h_line_c, h_atol_c, h_endline_c, h_stack_c⟩ :=
        scanNextToken_flow_comma s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_atol_v h_endline_v
      obtain ⟨feTok, h_feTok_val, h_comma_eq⟩ :=
        scanNextToken_flow_comma_filtered_push s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_snt_c
      obtain ⟨h_ska_c_true, _h_sk_c_eq⟩ :=
        scanNextToken_flow_comma_simpleKey s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_snt_c
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
              h_dp_pp, h_ids_pp, h_ek_pp, _h_line_pp, h_pp_eq_r, h_atol_transfer_pp, h_endline_transfer_pp, h_stack_pp, h_toks_pp, h_sk_pp, h_ska_pp⟩ :=
        scanNextToken_preprocess_flow_ws1 s_c c_p (rest_p ++ rest_chars) h_corr_c_ws
          h_sc_flow h_nws_p h_nlb_p h_nc_p h_sc_indent
      have h_corr_pp' : ScannerSurfCorr s_pp
          ⟨(emit.emitPairList (p' :: ps)).toList ++ rest_chars, s_pp.col⟩ := by
        have : c_p :: (rest_p ++ rest_chars) =
            (emit.emitPairList (p' :: ps)).toList ++ rest_chars := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_pp
      -- Step 8: Recursive scan of emitPairList (p' :: ps) via EmitPairListScansInFlowBlock
      have h_tail_all_k : ∀ q ∈ p' :: ps, EmitScansInFlowSavedKeyBlock q.1 :=
        fun q hq => h_all_k q (.tail _ hq)
      have h_tail_all_v : ∀ q ∈ p' :: ps, EmitScansInFlowBlock q.2 :=
        fun q hq => h_all_v q (.tail _ hq)
      have h_ih_list : EmitPairListScansInFlowBlock (p' :: ps) :=
        ih (by simp) h_tail_all_k h_tail_all_v
      obtain ⟨n_r, s_end, block_rest, h_chain_r, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end, h_endline_end, h_stack_end, h_fmc_r, h_blockeq_rest, h_wb_rest⟩ :=
        h_ih_list s_pp rest_chars h_corr_pp'
          h_flow_pp
          (by rw [h_fl_pp, h_fl_c]; rw [h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent_pp]; exact h_sc_indent)
          (by rw [h_col_pp]; omega)
          (by rw [h_ek_pp, h_ek_c, h_ek_v, h_ek₃]; exact h_ek₂)
          (h_atol_transfer_pp h_atol_c)
          (h_endline_transfer_pp h_endline_c)
          (by rw [h_ska_pp]; exact h_ska_c_true)
          (by rw [h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁,
              h_sync, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁])
      -- Lift chains through the two preprocessing equalities
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
            ⟨',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s_v.col⟩ := by
          have : [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr_v
        exact scanNextToken_filtered_grows_in_flow s_v s_c ','
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v_cons h_flow_v h_indent_v h_col_v
          (by decide) (by decide) (by decide) h_snt_c
      -- FlowMonoChain composition
      have h_fmc_v' : FlowMonoChain s.flowLevel s₃ (n_v' + 1) s_v :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc_v
      have h_fmc_ws_v : FlowMonoChain s.flowLevel s₂ (n_v' + 1) s_v :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_v (by omega) h_fmc_v'
      have h_fmc_r' : FlowMonoChain s.flowLevel s_pp (n_r' + 1) s_end :=
        (show s.flowLevel = s_pp.flowLevel from by omega) ▸ h_fmc_r
      have h_fmc_ws_r : FlowMonoChain s.flowLevel s_c (n_r' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_r (by omega) h_fmc_r'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans
          (h_fmc_ws_v.trans
            ((FlowMonoChain.single h_snt_c (by omega) (by omega)).trans h_fmc_ws_r)))
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans
          (h_chain_ws_v.trans
            ((ScanChainGrew.single h_snt_c h_grew_c).trans h_chain_ws_r)))
      have h_arith : n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) =
          n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1) := by omega
      -- Block accumulation: block_kc ++ block_v ++ [feTok] ++ block_rest
      have h_block_end : (s_end.tokens.filter (fun t => t.val != .placeholder)).toList
          = (s.tokens.filter (fun t => t.val != .placeholder)).toList
            ++ ((((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) ++ block_rest) := by
        have h_s3_s2 : (s₃.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s₂.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp₃]
        have h_block_v_end : (s_v.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s.tokens.filter (fun t => t.val != .placeholder)).toList
              ++ ((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) := by
          rw [h_blockeq_v, h_s3_s2, h_block_kc, List.append_assoc]
        have h_block_c_end : (s_c.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s.tokens.filter (fun t => t.val != .placeholder)).toList
              ++ (((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ ::
                  (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) := by
          rw [congrArg Array.toList h_comma_eq, Array.toList_push, h_block_v_end, List.append_assoc]
        have h_s_pp_c : (s_pp.tokens.filter (fun t => t.val != .placeholder)).toList
            = (s_c.tokens.filter (fun t => t.val != .placeholder)).toList := by
          rw [h_toks_pp]
        rw [h_blockeq_rest, h_s_pp_c, h_block_c_end, List.append_assoc]
      refine ⟨n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1), s_end,
        (((⟨s₁.simpleKey.pos, .key, s₁.simpleKey.pos⟩ :: (block_k ++ [⟨pos_v, .value, pos_v⟩])) ++ block_v) ++ [feTok]) ++ block_rest,
        h_arith ▸ h_chain_all, h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end,
        ?_, h_atol_end, h_endline_end, ?_, h_arith ▸ h_fmc_all, h_block_end, ?_⟩
      · rw [h_fl_end, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids_pp, h_ids_c, h_ids_v, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek_pp, h_ek_c, h_ek_v, h_ek₃]; exact h_ek₂.trans h_ek.symm
      · rw [h_line_end, _h_line_pp, _h_line_c, _h_line_v, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁]
      · -- WellBracketed (((block_kc ++ block_v) ++ [feTok]) ++ block_rest)
        exact WellBracketed_append _ _
          (WellBracketed_append _ _
            (WellBracketed_append _ _
              (WellBracketed_cons_delta_zero _ _ flowBracketDelta_key
                (WellBracketed_append _ _ h_wb_k
                  (WellBracketed_singleton_delta_zero _ (by rfl))))
              h_wb_v)
            (WellBracketed_singleton_delta_zero feTok (by rw [h_feTok_val]; exact flowBracketDelta_flowEntry)))
          h_wb_rest

end L4YAML.Proofs.EmitterScannability
