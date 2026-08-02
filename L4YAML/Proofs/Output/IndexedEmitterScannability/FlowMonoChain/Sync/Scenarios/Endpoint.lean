/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.FlowClose

/-! # `FlowMonoChain.Sync.Scenarios.Endpoint` — Phase 3 Step
`6f.3b3.flowmono.sync.scenarios.endpoint`

**Sub-session 3 of `.flowmono.sync.scenarios`** (final `.flowmono`
sub-session; legacy `Proofs/Output/EmitterScannability.lean` lines
3258–3329, 4910–5005, 5274–5326, 5445–5586).

Four scenarios closing out `.flowmono`:

  * **§1 `initial_corrIx`** — the new infrastructure consumed only by
    the init-state chains below. Builds `ScannerSurfCorrIx
    (ScannerStateIx.mk' input) ⟨input.toList, 0⟩` directly from
    `chars_from_zero_toList` (state-level offset 0, col 0, sentinel
    indent stack of size 1 with index 0 only).

  * **§2 `scanNextTokenIx_preprocess_init_state`** — the
    preprocessing simplification at the initial scanner state
    (`(ScannerStateIx.mk' input).emit .streamStart`) when the input
    starts with a content character. The reduction chain is:
    `skipToContentS` (identity — content char), `hasMore = true`,
    `unwindIndentsIx` (identity — `currentIndent = -1` ≤ `col = 0`),
    no trailing-content (size unchanged), `saveSimpleKeyIx`, `peek?`.
    The witness state `s_pp` preserves all 12 invariants needed by
    downstream init-state chains.

  * **§3 `scanNextTokenIx_flow_close_seq_outermost`** — `]` at
    `flowLevel = 1` with EOF after the close (no trailing input).
    Uses the same dispatcher as `_close_seq_nested`
    (`dispatchFlowIndicators_close_bracket s_ad h_fl_pos`) since the
    indexed pipeline lacks `validateFlowClose` tail-validation
    (Reflection 127). Distinct from `_nested` only at the scenario
    level: precondition `s.flowLevel = 1` + `peek_none_of_empty_surfIx`-
    closed `rest = []` yields `flowLevel = 0` and `peek? = none`.

  * **§4 `scanNextTokenIx_flow_close_mapping_outermost`** — mirror of
    §3 for `}` and `scanFlowMappingEndIx`.

  * **§5 `scanNextTokenIx_flow_open_mapping_init`** — `{` at the
    initial scanner state (no flow context, sentinel indents) for a
    top-level mapping. Composes §2 with `dispatchStructural_none_brace_
    init` + `checkBlockFlowIndent_brace_init` + `dispatchFlowIndicators_
    brace` + `scanFlowMappingStartIx_detail`. Consumed by
    `.emitscans.toplevel` for `emit_produces_valid_yamlIx` (top-level
    mapping body).

  * **§6 `scanNextTokenIx_flow_open_seq_init`** — `[` at the initial
    scanner state for a top-level sequence. Direct sequence analog of §5
    (`'{' ↦ '['`, `scanFlowMappingStartIx ↦ scanFlowSequenceStartIx`,
    `dispatchStructural_none_brace_init ↦ dispatchStructural_none_
    bracket_init`, `checkBlockFlowIndent_brace_init ↦ checkBlockFlow
    Indent_bracket_init`, `dispatchFlowIndicators_brace ↦ dispatch
    FlowIndicators_bracket`). Landed as part of `.emitscans.toplevel`
    SS1; the original `.flowmono` sub-session 3 did not need it (the
    chain lemmas of that family only consumed the `{` twin), so it
    sits in this scenario file but counts against `.emitscans.toplevel`'s
    LOC budget rather than `.flowmono.sync.scenarios.endpoint`.

With this sub-session, `.flowmono` closes: 13/13 sub-sessions across
9 files. Next file-level session: `.filteredgrowth`
(`Proofs/Output/IndexedEmitterScannability/FilteredGrowth.lean`,
~1320 LOC, 4 sub-sessions).
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
open L4YAML.Surface
open L4YAML.Proofs.CouplingBridge

variable {input : String}

/-! ## §1  `initial_corrIx`

The initial scanner state `(ScannerStateIx.mk' input)` sits at offset
0, line 0, col 0 with a single sentinel indent entry; this is enough
to satisfy `ScannerSurfCorrIx` over the full `input.toList`. -/

/-- The initial `ScannerStateIx.mk' input` is in surface correspondence
    with the full input list at col 0. Indexed twin of `initial_corr`
    (`Proofs/Coupling/CouplingBridge.lean:261`). -/
lemma initial_corrIx (input : String) :
    ScannerSurfCorrIx (input := input) (ScannerStateIx.mk' input)
      ⟨input.toList, 0⟩ := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · -- chars_from: CharsFromOffset input 0 input.toList
    -- (ScannerStateIx.mk' input).cursor.pos.offset = 0
    exact chars_from_zero_toList input
  · -- input_prefix: ∃ pre, input.toList = pre ++ input.toList
    --                ∧ listByteSize pre = 0
    exact ⟨[], by simp, rfl⟩
  · -- indent_cols_nonneg: indents = #[{column := -1, isSequence := false}],
    -- so size = 1; precondition `i > 0` rules out the single index.
    intro i hi h0
    -- (ScannerStateIx.mk' input).indents.size = 1 by definition
    have h_sz : (ScannerStateIx.mk' input).indents.size = 1 := rfl
    rw [h_sz] at hi
    omega

/-! ## §2  `scanNextTokenIx_preprocess_init_state`

The preprocessing reduction at the initial scanner state. The proof
threads the seven sub-stages of `scanNextTokenIx_preprocess`:
`skipToContentS` (identity), `hasMore`, `unwindIndentsIx` (identity
at sentinel), trailing-content check, `saveSimpleKeyIx`, `peek?`.
-/

/-- At the initial scanner state (`(ScannerStateIx.mk' input).emit
    .streamStart`) with a content character at the front,
    `scanNextTokenIx_preprocess` returns `(saveSimpleKeyIx { ... with
    needIndentCheck := false }, c)`. The witness `s_pp` preserves
    every field needed by downstream init-state chains (flowLevel,
    indents, cursor position, allowDirectives, etc.).
    Indexed twin of `scanNextToken_preprocess_init_state` (legacy 3258). -/
lemma scanNextTokenIx_preprocess_init_state (input : String) (c : Char)
    (rest : List Char)
    (h_toList : input.toList = c :: rest)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#') :
    ∃ s_pp, scanNextTokenIx_preprocess
            ((ScannerStateIx.mk' input).emit YamlToken.streamStart)
          = .ok (some (s_pp, c))
      ∧ s_pp.flowLevel = 0
      ∧ s_pp.inFlow = false
      ∧ s_pp.currentIndent = -1
      ∧ s_pp.cursor.pos.col = 0
      ∧ s_pp.allowDirectives = true
      ∧ s_pp.directivesPresent = false
      ∧ s_pp.indents = #[{ column := -1, isSequence := false }]
      ∧ s_pp.cursor.pos.offset = 0
      ∧ s_pp.explicitKeyLine = none
      ∧ s_pp.cursor.pos.line = 0
      ∧ AllTokensOnLineIx s_pp s_pp.cursor.pos.line
      ∧ s_pp.tokens.tokens.filter (fun t => t.token != .placeholder)
          = ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.tokens.filter
              (fun t => t.token != .placeholder) := by
  -- Build ScannerSurfCorrIx for the initial state, transferred through `emit .streamStart`
  have h_corr₀ : ScannerSurfCorrIx (input := input) (ScannerStateIx.mk' input)
      ⟨c :: rest, 0⟩ := by
    have h := initial_corrIx input
    rw [h_toList] at h
    exact h
  have h_corr_s₀ : ScannerSurfCorrIx ((ScannerStateIx.mk' input).emit YamlToken.streamStart)
      ⟨c :: rest, 0⟩ :=
    ScannerSurfCorrIx_transfer h_corr₀ rfl rfl rfl
  have ⟨h_pk₀, h_lt⟩ :=
    peek_of_chars_consIx_state ((ScannerStateIx.mk' input).emit YamlToken.streamStart)
      c rest 0 h_corr_s₀
  -- skipToContentS is identity (c is non-whitespace, non-linebreak, non-`#`)
  have h_stc : ((ScannerStateIx.mk' input).emit YamlToken.streamStart).skipToContentS
      = (ScannerStateIx.mk' input).emit YamlToken.streamStart :=
    skipToContentS_id_of_content _ h_pk₀ h_nws h_nlb h_nc
  -- hasMore = true (offset 0 < input.utf8ByteSize since the input has at least one char)
  have h_hm : ((ScannerStateIx.mk' input).emit YamlToken.streamStart).hasMore = true := by
    unfold ScannerStateIx.hasMore IxCursor.hasMore
    exact decide_eq_true h_lt
  -- The witness state: { ... with needIndentCheck := false } then saveSimpleKeyIx
  -- Note: needIndentCheck = true on initial state; the if-branch fires unwindIndentsIx
  -- with currentIndent = -1 ≤ col = 0, which is the identity (no entries to pop).
  -- The unwindIndentsIx result then has needIndentCheck := false.
  have h_inFlow_false : ((ScannerStateIx.mk' input).emit YamlToken.streamStart).inFlow = false := by
    unfold ScannerStateIx.inFlow
    show (decide ((((ScannerStateIx.mk' input).emit YamlToken.streamStart).flowLevel > 0)) : Bool) = false
    rfl
  have h_nic_true :
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).needIndentCheck = true := rfl
  -- unwindIndentsIx at sentinel indents (size 1) with currentIndent = -1 ≤ col = 0
  -- yields exactly s (cursor unchanged via @[simp] unwindIndentsIx_cursor).
  -- Critically: only the sentinel entry; size never decreases below 1.
  have h_uwi : unwindIndentsIx ((ScannerStateIx.mk' input).emit YamlToken.streamStart)
        ((ScannerStateIx.mk' input).emit YamlToken.streamStart).cursor.pos.col
      = (ScannerStateIx.mk' input).emit YamlToken.streamStart := by
    unfold unwindIndentsIx unwindIndentsLoopIx
    split <;> rfl
  -- Refine: introduce the witness state explicitly and use it to drive the conclusion
  refine ⟨saveSimpleKeyIx { (ScannerStateIx.mk' input).emit YamlToken.streamStart
                              with needIndentCheck := false },
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- scanNextTokenIx_preprocess = .ok (some (witness, c))
    unfold scanNextTokenIx_preprocess
    -- skipToContentS = self; hasMore = true
    simp only [h_stc, h_hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    -- !inFlow ∧ needIndentCheck = true, so the unwindIndentsIx branch fires
    simp only [h_inFlow_false, h_nic_true, Bool.not_false, Bool.true_and, ↓reduceIte]
    -- Substitute the unwindIndentsIx identity, then needIndentCheck record update
    rw [show unwindIndentsIx ((ScannerStateIx.mk' input).emit YamlToken.streamStart)
            ((ScannerStateIx.mk' input).emit YamlToken.streamStart).cursor.pos.col
          = (ScannerStateIx.mk' input).emit YamlToken.streamStart from h_uwi]
    -- After the record update: { ... with needIndentCheck := false }
    -- Trailing-content guard: size unchanged (both sides are 1)
    simp only [show ¬ (({ (ScannerStateIx.mk' input).emit YamlToken.streamStart with
                         needIndentCheck := false } : ScannerStateIx input).indents.size <
                       ((ScannerStateIx.mk' input).emit YamlToken.streamStart).indents.size)
                  from by
                  show ¬ ((1 : Nat) < 1); omega,
               decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    -- Final peek? matches some c via saveSimpleKeyIx_peek?
    rw [show (saveSimpleKeyIx { (ScannerStateIx.mk' input).emit YamlToken.streamStart
                                with needIndentCheck := false }).peek?
            = some c by
      rw [saveSimpleKeyIx_peek?]
      -- needIndentCheck record update preserves cursor, hence peek?
      change ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? = some c
      exact h_pk₀]
  · -- flowLevel = 0
    rw [saveSimpleKeyIx_flowLevel]; rfl
  · -- inFlow = false
    show (saveSimpleKeyIx _).inFlow = false
    unfold ScannerStateIx.inFlow
    rw [saveSimpleKeyIx_flowLevel]; rfl
  · -- currentIndent = -1
    unfold ScannerStateIx.currentIndent
    rw [saveSimpleKeyIx_indents]; rfl
  · -- cursor.pos.col = 0
    rw [saveSimpleKeyIx_cursor]; rfl
  · -- allowDirectives = true
    rw [saveSimpleKeyIx_allowDirectives]; rfl
  · -- directivesPresent = false
    rw [saveSimpleKeyIx_directivesPresent]; rfl
  · -- indents = sentinel
    rw [saveSimpleKeyIx_indents]; rfl
  · -- offset = 0
    rw [saveSimpleKeyIx_cursor]; rfl
  · -- explicitKeyLine = none
    rw [saveSimpleKeyIx_explicitKeyLine]; rfl
  · -- line = 0
    rw [saveSimpleKeyIx_cursor]; rfl
  · -- AllTokensOnLineIx witness 0
    rw [show (saveSimpleKeyIx { (ScannerStateIx.mk' input).emit YamlToken.streamStart with
                                needIndentCheck := false } : ScannerStateIx input).cursor.pos.line
            = 0 from by rw [saveSimpleKeyIx_cursor]; rfl]
    -- The token stream after `emit .streamStart` is a single token at line 0.
    -- saveSimpleKeyIx adds either nothing (identity branch) or two placeholders at the cursor.
    -- The needIndentCheck record update doesn't touch tokens.
    have h_emit_line :
        ((ScannerStateIx.mk' input).emit YamlToken.streamStart).cursor.pos.line = 0 := rfl
    have h_mk'_atol : AllTokensOnLineIx (ScannerStateIx.mk' input) 0 := by
      intro i hi
      -- (mk' input).tokens.size = 0 (TokenStream.empty)
      have h_sz : (ScannerStateIx.mk' input).tokens.size = 0 := rfl
      rw [h_sz] at hi
      exact absurd hi (Nat.not_lt_zero _)
    have h_emit_atol :
        AllTokensOnLineIx ((ScannerStateIx.mk' input).emit YamlToken.streamStart) 0 :=
      AllTokensOnLineIx_emit (ScannerStateIx.mk' input) YamlToken.streamStart 0
        h_mk'_atol rfl
    have h_nic_atol :
        AllTokensOnLineIx
          ({ (ScannerStateIx.mk' input).emit YamlToken.streamStart with
              needIndentCheck := false } : ScannerStateIx input) 0 :=
      AllTokensOnLineIx_of_tokens_eq (s := (ScannerStateIx.mk' input).emit YamlToken.streamStart)
        rfl h_emit_atol
    have h_nic_line :
        ({ (ScannerStateIx.mk' input).emit YamlToken.streamStart with
            needIndentCheck := false } : ScannerStateIx input).cursor.pos.line = 0 :=
      h_emit_line
    exact AllTokensOnLineIx_saveSimpleKeyIx _ 0 h_nic_atol h_nic_line
  · -- Filter preservation: saveSimpleKeyIx_filter_placeholder, then trivial for record update
    exact saveSimpleKeyIx_filter_placeholder _

/-! ## §3  `scanNextTokenIx_flow_close_seq_outermost`

`]` at `flowLevel = 1` with EOF after the close (`rest = []`). The
dispatcher and pipeline composition are identical to `_close_seq_
nested` (no `validateFlowClose` in indexed); the result conclusions
differ: `flowLevel = 0` and `peek? = none`. -/

/-- Full `scanNextTokenIx` for `']'` at outermost flow close
    (`flowLevel = 1`, EOF). Indexed twin of `scanNextToken_flow_close_
    seq_outermost` (legacy 4947). -/
lemma scanNextTokenIx_flow_close_seq_outermost (s : ScannerStateIx input)
    (hcorr : ScannerSurfCorrIx s ⟨[']'], s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    ∃ s', scanNextTokenIx s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none := by
  -- Step 1: preprocessing
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, ']')) :=
    scanNextTokenIx_preprocess_flow s ']' [] s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) ']' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: introduce s_ad via opaque equation
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if (saveSimpleKeyIx s).allowDirectives then
        { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
      else saveSimpleKeyIx s := ⟨_, rfl⟩
  -- Step 4: checkBlockFlowIndent for ']'
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad ']' = .ok () :=
    checkBlockFlowIndent_ok_close_bracket s_ad
  -- Step 5: derive field equalities for s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_indents s
  have h_ad_cursor : s_ad.cursor = s.cursor := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_cursor s
  -- Step 6: flow dispatch (shared with nested; no validateFlowClose)
  have h_fl_pos : s_ad.flowLevel > 0 := by rw [h_ad_fl, h_fl]; omega
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad ']' =
      .ok (some (scanFlowSequenceEndIx s_ad)) :=
    dispatchFlowIndicators_close_bracket s_ad h_fl_pos
  have h_snt := scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
    (scanFlowSequenceEndIx s_ad) ']'
    h_pp h_struct h_s_ad_def h_check h_flow_disp
    ((saveSimpleKeyIx_directivesPresent s).trans h_dp)
  -- Step 7: extract via scanFlowSequenceEndIx_detail (for s_ad at position [']']
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨[']'], s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_ad_cursor]; exact hcorr.chars_from
    · rw [h_ad_cursor]; exact hcorr.input_prefix
    · intro i hi h0
      have hi' : i < s.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s.indents[i]'hi' := by congr 1
      rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, _, _⟩ :=
    scanFlowSequenceEndIx_detail s_ad [] h_ad_corr
  -- Result conclusions
  have h_s'_fl : (scanFlowSequenceEndIx s_ad).flowLevel = 0 := by
    rw [h_fl_f, h_ad_fl, h_fl]
  have h_s'_dp : (scanFlowSequenceEndIx s_ad).directivesPresent = false := by
    rw [h_dp_f, h_ad_dp]; exact h_dp
  -- EOF after the close: h_corr_f gives ScannerSurfCorrIx at ⟨[], col + 1⟩
  have h_s'_peek : (scanFlowSequenceEndIx s_ad).peek? = none :=
    peek_none_of_empty_surfIx (scanFlowSequenceEndIx s_ad) (s_ad.cursor.pos.col + 1) h_corr_f
  exact ⟨scanFlowSequenceEndIx s_ad, h_snt, h_s'_fl, h_s'_dp, h_s'_peek⟩

/-! ## §4  `scanNextTokenIx_flow_close_mapping_outermost`

Mirror of §3 for `}` and `scanFlowMappingEndIx`. -/

/-- Full `scanNextTokenIx` for `'}'` at outermost flow close
    (`flowLevel = 1`, EOF). Indexed twin of `scanNextToken_flow_close_
    mapping_outermost` (legacy 5274). -/
lemma scanNextTokenIx_flow_close_mapping_outermost (s : ScannerStateIx input)
    (hcorr : ScannerSurfCorrIx s ⟨['}'], s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    ∃ s', scanNextTokenIx s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none := by
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, '}')) :=
    scanNextTokenIx_preprocess_flow s '}' [] s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) '}' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if (saveSimpleKeyIx s).allowDirectives then
        { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
      else saveSimpleKeyIx s := ⟨_, rfl⟩
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad '}' = .ok () :=
    checkBlockFlowIndent_ok_close_brace s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_indents s
  have h_ad_cursor : s_ad.cursor = s.cursor := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_cursor s
  have h_fl_pos : s_ad.flowLevel > 0 := by rw [h_ad_fl, h_fl]; omega
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad '}' =
      .ok (some (scanFlowMappingEndIx s_ad)) :=
    dispatchFlowIndicators_close_brace s_ad h_fl_pos
  have h_snt := scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
    (scanFlowMappingEndIx s_ad) '}'
    h_pp h_struct h_s_ad_def h_check h_flow_disp
    ((saveSimpleKeyIx_directivesPresent s).trans h_dp)
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨['}'], s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_ad_cursor]; exact hcorr.chars_from
    · rw [h_ad_cursor]; exact hcorr.input_prefix
    · intro i hi h0
      have hi' : i < s.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s.indents[i]'hi' := by congr 1
      rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, _, _⟩ :=
    scanFlowMappingEndIx_detail s_ad [] h_ad_corr
  have h_s'_fl : (scanFlowMappingEndIx s_ad).flowLevel = 0 := by
    rw [h_fl_f, h_ad_fl, h_fl]
  have h_s'_dp : (scanFlowMappingEndIx s_ad).directivesPresent = false := by
    rw [h_dp_f, h_ad_dp]; exact h_dp
  have h_s'_peek : (scanFlowMappingEndIx s_ad).peek? = none :=
    peek_none_of_empty_surfIx (scanFlowMappingEndIx s_ad) (s_ad.cursor.pos.col + 1) h_corr_f
  exact ⟨scanFlowMappingEndIx s_ad, h_snt, h_s'_fl, h_s'_dp, h_s'_peek⟩

/-! ## §5  `scanNextTokenIx_flow_open_mapping_init`

`{` at the initial scanner state for a top-level mapping. Threads
the init-state preprocessing (§2) through the dispatcher chain
(`dispatchStructural_none_brace_init` + `checkBlockFlowIndent_brace_
init` + `dispatchFlowIndicators_brace`) and extracts the result via
`scanFlowMappingStartIx_detail`. -/

/-- `scanNextTokenIx` on the initial scanner state at `{` dispatches
    to `scanFlowMappingStartIx`, entering flow context.
    Indexed twin of `scanNextToken_flow_open_mapping_init` (legacy 5445). -/
lemma scanNextTokenIx_flow_open_mapping_init (input : String) (rest : List Char)
    (h_toList : input.toList = '{' :: rest) :
    let s₀ := (ScannerStateIx.mk' input).emit YamlToken.streamStart
    ∃ s', scanNextTokenIx s₀ = .ok (some s')
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = 1
      ∧ s'.directivesPresent = false
      ∧ s'.indents = s₀.indents
      ∧ s'.cursor.pos.col = 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.cursor.pos.line = 0
      ∧ AllTokensOnLineIx s' 0
      ∧ EndLineOnLineIx s'
      ∧ s'.simpleKey.possible = false
      ∧ s'.simpleKeyStack.size = s'.flowLevel := by
  intro s₀
  -- Step 1: preprocessing (uses §2)
  have h_pp := scanNextTokenIx_preprocess_init_state input '{' rest h_toList
    (by decide) (by decide) (by decide)
  obtain ⟨s_pp, h_pp_eq, h_fl_pp, h_inflow_pp, h_ci_pp, h_col_pp,
          h_ad_pp, h_dp_pp, h_ids, h_off, h_ek_pp,
          h_line_pp, h_atol_pp, _h_pp_filt⟩ := h_pp
  -- Step 2: ScannerSurfCorrIx for s_pp at ⟨'{' :: rest, s_pp.col⟩
  have h_corr₀ : ScannerSurfCorrIx (input := input) (ScannerStateIx.mk' input)
      ⟨'{' :: rest, 0⟩ := by
    have h := initial_corrIx input
    rw [h_toList] at h
    exact h
  have h_corr_s₀ : ScannerSurfCorrIx s₀ ⟨'{' :: rest, 0⟩ :=
    ScannerSurfCorrIx_transfer h_corr₀ rfl rfl rfl
  have h_corr_pp : ScannerSurfCorrIx s_pp ⟨'{' :: rest, s_pp.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · -- chars_from at offset s_pp.cursor.pos.offset = 0
      rw [h_off]
      exact h_corr_s₀.chars_from
    · -- input_prefix
      obtain ⟨pre, hpre, hsize⟩ := h_corr_s₀.input_prefix
      exact ⟨pre, hpre, by rw [h_off]; exact hsize⟩
    · -- indent_cols_nonneg: s_pp.indents = s₀.indents (sentinel-only); size = 1, i > 0 impossible
      intro i hi _h0
      have h_sz : s_pp.indents.size = 1 := by rw [h_ids]; rfl
      rw [h_sz] at hi
      omega
  have ⟨h_pk_pp, h_lt_pp⟩ :=
    peek_of_chars_consIx_state s_pp '{' rest _ h_corr_pp
  -- Step 3: atDocumentStart/End = false for '{' (uses h_pk_pp + col = 0)
  have h_pat0 : s_pp.cursor.peekAt? 0 = s_pp.peek? := by
    -- peekAt? 0 = peek? by definition (peekAt?Loop with n = 0)
    unfold IxCursor.peekAt? IxCursor.peekAt?Loop
    show s_pp.cursor.peek? = s_pp.cursor.peek?
    rfl
  have h_ds : atDocumentStartIx s_pp.cursor = false := by
    unfold atDocumentStartIx
    rw [h_pat0]
    show (s_pp.cursor.pos.col == 0 &&
      (match s_pp.peek? with | some d => isSequenceEntryBool d | none => false) &&
      (match s_pp.cursor.peekAt? 1 with | some d => isSequenceEntryBool d | none => false) &&
      (match s_pp.cursor.peekAt? 2 with | some d => isSequenceEntryBool d | none => false) &&
      (match s_pp.cursor.peekAt? 3 with | none => true | some d => isBlankBool d)) = false
    rw [h_pk_pp]
    simp [isSequenceEntryBool]
  have h_de : atDocumentEndIx s_pp.cursor = false := by
    unfold atDocumentEndIx
    rw [h_pat0]
    show (s_pp.cursor.pos.col == 0 &&
      (match s_pp.peek? with | some d => isDocEndDotBool d | none => false) &&
      (match s_pp.cursor.peekAt? 1 with | some d => isDocEndDotBool d | none => false) &&
      (match s_pp.cursor.peekAt? 2 with | some d => isDocEndDotBool d | none => false) &&
      (match s_pp.cursor.peekAt? 3 with | none => true | some d => isBlankBool d)) = false
    rw [h_pk_pp]
    simp [isDocEndDotBool]
  -- Step 4: structural dispatch → none
  have h_struct := dispatchStructural_none_brace_init s_pp h_fl_pp h_ds h_de
  -- Step 5: allowDirectives update → s_ad (opaque equation)
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if s_pp.allowDirectives then
        { s_pp with allowDirectives := false, documentEverStarted := true }
      else s_pp := ⟨_, rfl⟩
  -- Step 6: derive s_ad field equalities (all preserved from s_pp through the if)
  have h_ad_fl : s_ad.flowLevel = 0 := by
    rw [h_s_ad_def]; split <;> exact h_fl_pp
  have h_ad_dp : s_ad.directivesPresent = false := by
    rw [h_s_ad_def]; split <;> exact h_dp_pp
  have h_ad_ids : s_ad.indents = s_pp.indents := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_ek : s_ad.explicitKeyLine = s_pp.explicitKeyLine := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_cursor : s_ad.cursor = s_pp.cursor := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_tokens : s_ad.tokens = s_pp.tokens := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_simpleKeyStack : s_ad.simpleKeyStack = s_pp.simpleKeyStack := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_simpleKey : s_ad.simpleKey = s_pp.simpleKey := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_ci : s_ad.currentIndent = -1 := by
    unfold ScannerStateIx.currentIndent
    rw [h_ad_ids]
    have : s_pp.indents = #[{ column := -1, isSequence := false }] := h_ids
    rw [this]; rfl
  -- Step 7: checkBlockFlowIndent passes for `{` at init state
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad '{' = .ok () :=
    checkBlockFlowIndent_brace_init s_ad h_ad_fl h_ad_ci
  -- Step 8: flow dispatch → some (scanFlowMappingStartIx s_ad)
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad '{' =
      .ok (some (scanFlowMappingStartIx s_ad)) :=
    dispatchFlowIndicators_brace s_ad
  -- Step 9: compose via scanNextTokenIx_via_flow_dispatch
  have h_snt := scanNextTokenIx_via_flow_dispatch s₀ s_pp s_ad
    (scanFlowMappingStartIx s_ad) '{'
    h_pp_eq h_struct h_s_ad_def h_check h_flow_disp h_dp_pp
  -- Step 10: extract via scanFlowMappingStartIx_detail
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨'{' :: rest, s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_ad_cursor]; exact h_corr_pp.chars_from
    · rw [h_ad_cursor]
    · rw [h_ad_cursor]; exact h_corr_pp.input_prefix
    · intro i hi h0
      have hi' : i < s_pp.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s_pp.indents[i]'hi' := by
        congr 1
      rw [heq]; exact h_corr_pp.indent_cols_nonneg i hi' h0
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowMappingStartIx_detail s_ad rest h_ad_corr
  -- Step 11: result field computations
  have h_ad_col : s_ad.cursor.pos.col = 0 := by
    rw [h_ad_cursor]; exact h_col_pp
  have h_ad_line : s_ad.cursor.pos.line = 0 := by
    rw [h_ad_cursor]; exact h_line_pp
  have h_s'_fl : (scanFlowMappingStartIx s_ad).flowLevel = 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_s'_dp : (scanFlowMappingStartIx s_ad).directivesPresent = false := by
    rw [h_dp_f]; exact h_ad_dp
  have h_s'_ids : (scanFlowMappingStartIx s_ad).indents = s₀.indents := by
    rw [h_ids_f, h_ad_ids]; exact h_ids
  have h_s'_col : (scanFlowMappingStartIx s_ad).cursor.pos.col = 1 := by
    rw [h_col_f, h_ad_col]
  have h_s'_corr : ScannerSurfCorrIx (scanFlowMappingStartIx s_ad)
      ⟨rest, (scanFlowMappingStartIx s_ad).cursor.pos.col⟩ := by
    rw [h_col_f]; exact h_corr_f
  have h_s'_ek : (scanFlowMappingStartIx s_ad).explicitKeyLine = none := by
    rw [scanFlowMappingStartIx_explicitKeyLine, h_ad_ek]; exact h_ek_pp
  have h_ad_pk : s_ad.cursor.peek? = some '{' := by
    show s_ad.peek? = some '{'
    rw [show s_ad.peek? = s_pp.peek? from by
      show s_ad.cursor.peek? = s_pp.cursor.peek?
      rw [h_ad_cursor]]
    exact h_pk_pp
  have h_ad_lt : s_ad.cursor.pos.offset < input.utf8ByteSize := by
    rw [h_ad_cursor]; exact h_lt_pp
  have h_s'_line : (scanFlowMappingStartIx s_ad).cursor.pos.line = 0 := by
    show (s_ad.emit YamlToken.flowMappingStart).advance.cursor.pos.line = 0
    rw [advance_cursor, emit_cursor]
    exact (advance_line_of_peekIx s_ad.cursor '{' h_ad_lt h_ad_pk
      (by decide) (by decide)).trans h_ad_line
  have h_s'_inflow : (scanFlowMappingStartIx s_ad).inFlow = true := by
    unfold ScannerStateIx.inFlow
    rw [h_s'_fl]; decide
  have h_s'_ci : (scanFlowMappingStartIx s_ad).currentIndent < 0 := by
    unfold ScannerStateIx.currentIndent
    rw [h_s'_ids]
    -- s₀.indents = #[{column := -1, isSequence := false}] → back? = some {column := -1}
    show (match s₀.indents.back? with | some e => e.column | none => -1) < 0
    have h_back : s₀.indents.back? = some { column := -1, isSequence := false } := rfl
    rw [h_back]; decide
  -- AllTokensOnLineIx
  have h_pp_atol_line :
      AllTokensOnLineIx s_pp s_pp.cursor.pos.line := h_atol_pp
  have h_ad_atol : AllTokensOnLineIx s_ad s_pp.cursor.pos.line := by
    have h_eq_pp : s_pp.cursor.pos.line = 0 := h_line_pp
    rw [h_eq_pp] at h_pp_atol_line ⊢
    exact AllTokensOnLineIx_of_tokens_eq h_ad_tokens h_pp_atol_line
  have h_ad_atol0 : AllTokensOnLineIx s_ad 0 := by
    rw [h_line_pp] at h_ad_atol
    exact h_ad_atol
  have h_s'_atol : AllTokensOnLineIx (scanFlowMappingStartIx s_ad) 0 := by
    have h_ad_line_pp : s_ad.cursor.pos.line = 0 := by rw [h_ad_cursor]; exact h_line_pp
    exact AllTokensOnLineIx_scanFlowMappingStartIx s_ad 0 h_ad_atol0 h_ad_line_pp
  -- EndLineOnLineIx via simpleKey_not_possible
  have h_s'_endline : EndLineOnLineIx (scanFlowMappingStartIx s_ad) := by
    intro h_poss
    rw [scanFlowMappingStartIx_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  -- simpleKey.possible = false
  have h_s'_sk_poss : (scanFlowMappingStartIx s_ad).simpleKey.possible = false :=
    scanFlowMappingStartIx_simpleKey_not_possible s_ad
  -- simpleKeyStack.size = flowLevel
  have h_s'_stack_sz : (scanFlowMappingStartIx s_ad).simpleKeyStack.size =
      (scanFlowMappingStartIx s_ad).flowLevel := by
    rw [h_s'_fl, scanFlowMappingStartIx_stack_pushed, Array.size_push]
    rw [h_ad_simpleKeyStack]
    -- s_pp.simpleKeyStack = s₀.simpleKeyStack = #[] via preprocess preservation.
    have h_pre := scanNextTokenIx_preprocess_preserves_simpleKeyStack s₀ s_pp _ h_pp_eq
    rw [h_pre]
    -- s₀.simpleKeyStack = ((ScannerStateIx.mk' input).emit YamlToken.streamStart).simpleKeyStack = #[]
    have h_s0_stack_sz : s₀.simpleKeyStack.size = 0 := rfl
    rw [h_s0_stack_sz]
  -- Combine
  refine ⟨scanFlowMappingStartIx s_ad, h_snt, h_s'_corr, h_s'_fl, h_s'_dp, h_s'_ids,
          h_s'_col, h_s'_inflow, h_s'_ci, h_s'_ek, h_s'_line, h_s'_atol, h_s'_endline,
          h_s'_sk_poss, h_s'_stack_sz⟩

/-! ## §6  `scanNextTokenIx_flow_open_seq_init`

`[` at the initial scanner state for a top-level sequence. Mechanical
sequence analog of §5 (`scanNextTokenIx_flow_open_mapping_init`);
substitutions: `'{' ↦ '['`, `scanFlowMappingStartIx ↦
scanFlowSequenceStartIx`, `dispatchStructural_none_brace_init ↦
dispatchStructural_none_bracket_init`, `checkBlockFlowIndent_brace_
init ↦ checkBlockFlowIndent_bracket_init`, `dispatchFlowIndicators_
brace ↦ dispatchFlowIndicators_bracket`, `YamlToken.flowMappingStart ↦
YamlToken.flowSequenceStart`. -/

/-- `scanNextTokenIx` on the initial scanner state at `[` dispatches
    to `scanFlowSequenceStartIx`, entering flow context. Indexed twin
    of `scanNextToken_flow_open_init` (legacy 4095). -/
lemma scanNextTokenIx_flow_open_seq_init (input : String) (rest : List Char)
    (h_toList : input.toList = '[' :: rest) :
    let s₀ := (ScannerStateIx.mk' input).emit YamlToken.streamStart
    ∃ s', scanNextTokenIx s₀ = .ok (some s')
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = 1
      ∧ s'.directivesPresent = false
      ∧ s'.indents = s₀.indents
      ∧ s'.cursor.pos.col = 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.cursor.pos.line = 0
      ∧ AllTokensOnLineIx s' 0
      ∧ EndLineOnLineIx s'
      ∧ s'.simpleKey.possible = false
      ∧ s'.simpleKeyStack.size = s'.flowLevel := by
  intro s₀
  -- Step 1: preprocessing (uses §2)
  have h_pp := scanNextTokenIx_preprocess_init_state input '[' rest h_toList
    (by decide) (by decide) (by decide)
  obtain ⟨s_pp, h_pp_eq, h_fl_pp, h_inflow_pp, h_ci_pp, h_col_pp,
          h_ad_pp, h_dp_pp, h_ids, h_off, h_ek_pp,
          h_line_pp, h_atol_pp, _h_pp_filt⟩ := h_pp
  -- Step 2: ScannerSurfCorrIx for s_pp at ⟨'[' :: rest, s_pp.col⟩
  have h_corr₀ : ScannerSurfCorrIx (input := input) (ScannerStateIx.mk' input)
      ⟨'[' :: rest, 0⟩ := by
    have h := initial_corrIx input
    rw [h_toList] at h
    exact h
  have h_corr_s₀ : ScannerSurfCorrIx s₀ ⟨'[' :: rest, 0⟩ :=
    ScannerSurfCorrIx_transfer h_corr₀ rfl rfl rfl
  have h_corr_pp : ScannerSurfCorrIx s_pp ⟨'[' :: rest, s_pp.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_off]; exact h_corr_s₀.chars_from
    · obtain ⟨pre, hpre, hsize⟩ := h_corr_s₀.input_prefix
      exact ⟨pre, hpre, by rw [h_off]; exact hsize⟩
    · intro i hi _h0
      have h_sz : s_pp.indents.size = 1 := by rw [h_ids]; rfl
      rw [h_sz] at hi
      omega
  have ⟨h_pk_pp, h_lt_pp⟩ :=
    peek_of_chars_consIx_state s_pp '[' rest _ h_corr_pp
  -- Step 3: atDocumentStart/End = false for '[' (uses h_pk_pp + col = 0)
  have h_pat0 : s_pp.cursor.peekAt? 0 = s_pp.peek? := by
    unfold IxCursor.peekAt? IxCursor.peekAt?Loop
    show s_pp.cursor.peek? = s_pp.cursor.peek?
    rfl
  have h_ds : atDocumentStartIx s_pp.cursor = false := by
    unfold atDocumentStartIx
    rw [h_pat0]
    show (s_pp.cursor.pos.col == 0 &&
      (match s_pp.peek? with | some d => isSequenceEntryBool d | none => false) &&
      (match s_pp.cursor.peekAt? 1 with | some d => isSequenceEntryBool d | none => false) &&
      (match s_pp.cursor.peekAt? 2 with | some d => isSequenceEntryBool d | none => false) &&
      (match s_pp.cursor.peekAt? 3 with | none => true | some d => isBlankBool d)) = false
    rw [h_pk_pp]
    simp [isSequenceEntryBool]
  have h_de : atDocumentEndIx s_pp.cursor = false := by
    unfold atDocumentEndIx
    rw [h_pat0]
    show (s_pp.cursor.pos.col == 0 &&
      (match s_pp.peek? with | some d => isDocEndDotBool d | none => false) &&
      (match s_pp.cursor.peekAt? 1 with | some d => isDocEndDotBool d | none => false) &&
      (match s_pp.cursor.peekAt? 2 with | some d => isDocEndDotBool d | none => false) &&
      (match s_pp.cursor.peekAt? 3 with | none => true | some d => isBlankBool d)) = false
    rw [h_pk_pp]
    simp [isDocEndDotBool]
  -- Step 4: structural dispatch → none
  have h_struct := dispatchStructural_none_bracket_init s_pp h_fl_pp h_ds h_de
  -- Step 5: allowDirectives update → s_ad (opaque equation)
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if s_pp.allowDirectives then
        { s_pp with allowDirectives := false, documentEverStarted := true }
      else s_pp := ⟨_, rfl⟩
  -- Step 6: derive s_ad field equalities (all preserved from s_pp through the if)
  have h_ad_fl : s_ad.flowLevel = 0 := by
    rw [h_s_ad_def]; split <;> exact h_fl_pp
  have h_ad_dp : s_ad.directivesPresent = false := by
    rw [h_s_ad_def]; split <;> exact h_dp_pp
  have h_ad_ids : s_ad.indents = s_pp.indents := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_ek : s_ad.explicitKeyLine = s_pp.explicitKeyLine := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_cursor : s_ad.cursor = s_pp.cursor := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_tokens : s_ad.tokens = s_pp.tokens := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_simpleKeyStack : s_ad.simpleKeyStack = s_pp.simpleKeyStack := by
    rw [h_s_ad_def]; split <;> rfl
  have _h_ad_simpleKey : s_ad.simpleKey = s_pp.simpleKey := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_ci : s_ad.currentIndent = -1 := by
    unfold ScannerStateIx.currentIndent
    rw [h_ad_ids]
    have : s_pp.indents = #[{ column := -1, isSequence := false }] := h_ids
    rw [this]; rfl
  -- Step 7: checkBlockFlowIndent passes for `[` at init state
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad '[' = .ok () :=
    checkBlockFlowIndent_bracket_init s_ad h_ad_fl h_ad_ci
  -- Step 8: flow dispatch → some (scanFlowSequenceStartIx s_ad)
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad '[' =
      .ok (some (scanFlowSequenceStartIx s_ad)) :=
    dispatchFlowIndicators_bracket s_ad
  -- Step 9: compose via scanNextTokenIx_via_flow_dispatch
  have h_snt := scanNextTokenIx_via_flow_dispatch s₀ s_pp s_ad
    (scanFlowSequenceStartIx s_ad) '['
    h_pp_eq h_struct h_s_ad_def h_check h_flow_disp h_dp_pp
  -- Step 10: extract via scanFlowSequenceStartIx_detail
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨'[' :: rest, s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_ad_cursor]; exact h_corr_pp.chars_from
    · rw [h_ad_cursor]
    · rw [h_ad_cursor]; exact h_corr_pp.input_prefix
    · intro i hi h0
      have hi' : i < s_pp.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s_pp.indents[i]'hi' := by
        congr 1
      rw [heq]; exact h_corr_pp.indent_cols_nonneg i hi' h0
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowSequenceStartIx_detail s_ad rest h_ad_corr
  -- Step 11: result field computations
  have h_ad_col : s_ad.cursor.pos.col = 0 := by
    rw [h_ad_cursor]; exact h_col_pp
  have h_ad_line : s_ad.cursor.pos.line = 0 := by
    rw [h_ad_cursor]; exact h_line_pp
  have h_s'_fl : (scanFlowSequenceStartIx s_ad).flowLevel = 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_s'_dp : (scanFlowSequenceStartIx s_ad).directivesPresent = false := by
    rw [h_dp_f]; exact h_ad_dp
  have h_s'_ids : (scanFlowSequenceStartIx s_ad).indents = s₀.indents := by
    rw [h_ids_f, h_ad_ids]; exact h_ids
  have h_s'_col : (scanFlowSequenceStartIx s_ad).cursor.pos.col = 1 := by
    rw [h_col_f, h_ad_col]
  have h_s'_corr : ScannerSurfCorrIx (scanFlowSequenceStartIx s_ad)
      ⟨rest, (scanFlowSequenceStartIx s_ad).cursor.pos.col⟩ := by
    rw [h_col_f]; exact h_corr_f
  have h_s'_ek : (scanFlowSequenceStartIx s_ad).explicitKeyLine = none := by
    rw [scanFlowSequenceStartIx_explicitKeyLine, h_ad_ek]; exact h_ek_pp
  have h_ad_pk : s_ad.cursor.peek? = some '[' := by
    show s_ad.peek? = some '['
    rw [show s_ad.peek? = s_pp.peek? from by
      show s_ad.cursor.peek? = s_pp.cursor.peek?
      rw [h_ad_cursor]]
    exact h_pk_pp
  have h_ad_lt : s_ad.cursor.pos.offset < input.utf8ByteSize := by
    rw [h_ad_cursor]; exact h_lt_pp
  have h_s'_line : (scanFlowSequenceStartIx s_ad).cursor.pos.line = 0 := by
    show (s_ad.emit YamlToken.flowSequenceStart).advance.cursor.pos.line = 0
    rw [advance_cursor, emit_cursor]
    exact (advance_line_of_peekIx s_ad.cursor '[' h_ad_lt h_ad_pk
      (by decide) (by decide)).trans h_ad_line
  have h_s'_inflow : (scanFlowSequenceStartIx s_ad).inFlow = true := by
    unfold ScannerStateIx.inFlow
    rw [h_s'_fl]; decide
  have h_s'_ci : (scanFlowSequenceStartIx s_ad).currentIndent < 0 := by
    unfold ScannerStateIx.currentIndent
    rw [h_s'_ids]
    -- s₀.indents = #[{column := -1, isSequence := false}] → back? = some {column := -1}
    show (match s₀.indents.back? with | some e => e.column | none => -1) < 0
    have h_back : s₀.indents.back? = some { column := -1, isSequence := false } := rfl
    rw [h_back]; decide
  -- AllTokensOnLineIx
  have h_pp_atol_line :
      AllTokensOnLineIx s_pp s_pp.cursor.pos.line := h_atol_pp
  have h_ad_atol : AllTokensOnLineIx s_ad s_pp.cursor.pos.line := by
    have h_eq_pp : s_pp.cursor.pos.line = 0 := h_line_pp
    rw [h_eq_pp] at h_pp_atol_line ⊢
    exact AllTokensOnLineIx_of_tokens_eq h_ad_tokens h_pp_atol_line
  have h_ad_atol0 : AllTokensOnLineIx s_ad 0 := by
    rw [h_line_pp] at h_ad_atol
    exact h_ad_atol
  have h_s'_atol : AllTokensOnLineIx (scanFlowSequenceStartIx s_ad) 0 := by
    have h_ad_line_pp : s_ad.cursor.pos.line = 0 := by rw [h_ad_cursor]; exact h_line_pp
    exact AllTokensOnLineIx_scanFlowSequenceStartIx s_ad 0 h_ad_atol0 h_ad_line_pp
  -- EndLineOnLineIx via simpleKey_not_possible
  have h_s'_endline : EndLineOnLineIx (scanFlowSequenceStartIx s_ad) := by
    intro h_poss
    rw [scanFlowSequenceStartIx_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  -- simpleKey.possible = false
  have h_s'_sk_poss : (scanFlowSequenceStartIx s_ad).simpleKey.possible = false :=
    scanFlowSequenceStartIx_simpleKey_not_possible s_ad
  -- simpleKeyStack.size = flowLevel
  have h_s'_stack_sz : (scanFlowSequenceStartIx s_ad).simpleKeyStack.size =
      (scanFlowSequenceStartIx s_ad).flowLevel := by
    rw [h_s'_fl, scanFlowSequenceStartIx_stack_pushed, Array.size_push]
    rw [h_ad_simpleKeyStack]
    have h_pre := scanNextTokenIx_preprocess_preserves_simpleKeyStack s₀ s_pp _ h_pp_eq
    rw [h_pre]
    have h_s0_stack_sz : s₀.simpleKeyStack.size = 0 := rfl
    rw [h_s0_stack_sz]
  -- Combine
  refine ⟨scanFlowSequenceStartIx s_ad, h_snt, h_s'_corr, h_s'_fl, h_s'_dp, h_s'_ids,
          h_s'_col, h_s'_inflow, h_s'_ci, h_s'_ek, h_s'_line, h_s'_atol, h_s'_endline,
          h_s'_sk_poss, h_s'_stack_sz⟩

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
