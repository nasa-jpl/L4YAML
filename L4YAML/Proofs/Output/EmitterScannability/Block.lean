import L4YAML.Proofs.Output.EmitterScannability

/-!
# Block-tracking substrate for flow-collection emitter scannability

Extracted from `L4YAML.Proofs.Output.EmitterScannability` (2026-05-31) to keep the
base file manageable.  Contains the block-tracking *superset* predicates
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
      ∧ s'.simpleKey.possible = false

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
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
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
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    match tail, ih with
    | [], _ =>
      have h_eq : (emit.emitList [v]).toList = (emit v).toList := by
        simp only [emit.emitList]
      rw [h_eq] at hcorr
      obtain ⟨n, s', block, h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow',
              h_indent', h_line_v, _h_ska, _h_last, h_atol', h_endline', h_stack', h_fmc',
              h_block_eq, h_wb, _h_es, _h_cs, _h_poss⟩ :=
        h_all v (.head _) s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
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
              h_block_eq₁, h_wb₁, _h_es₁, _h_cs₁, _h_poss₁⟩ :=
        h_ev s ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
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
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃⟩ :=
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
    s.simpleKey.possible = false →
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
    s.simpleKey.possible = false →
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
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sk h_ska h_sync
  have h_eq : (emit.emitPairList ([] : List (YamlValue × YamlValue))).toList ++ rest = rest := by
    simp [emit.emitPairList]
  rw [h_eq] at hcorr
  exact ⟨0, s, [], .zero, hcorr, rfl, rfl, rfl, rfl, h_col, h_flow, h_indent, rfl,
    h_atol, h_endline, rfl, .zero (Nat.le.refl), by simp, WellBracketed_nil⟩

end L4YAML.Proofs.EmitterScannability
