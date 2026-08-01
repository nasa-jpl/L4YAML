/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.Preflow

/-! # `FlowMonoChain.Sync.Scenarios.FlowClose` — Phase 3 Step
`6f.3b3.flowmono.sync.scenarios.flowclose`

**Sub-session 2 of `.flowmono.sync.scenarios`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 4793–4908, 5141–5245,
5329–5420).

Three mid-chain scenario theorems, each following the same skeleton
established by `_flow_comma` in `.preflow`:

  * **§1 `scanNextTokenIx_flow_close_seq_nested`** — `]` at
    flowLevel ≥ 2. Threads preprocess → `dispatchStructural` (none)
    → allowDirectives update → `checkBlockFlowIndent_ok_close_bracket`
    → `dispatchFlowIndicators_close_bracket` → `scanFlowSequenceEndIx`.
    Yields `flowLevel - 1`, `simpleKeyStack.pop`,
    `lastRealTokenValIx? = .flowSequenceEnd` (a non-`.flow*` token so
    downstream `_flow_comma` calls can chain).

  * **§2 `scanNextTokenIx_flow_close_mapping_nested`** — `}` at
    flowLevel ≥ 2. Mirror of §1 with `scanFlowMappingEndIx` and
    `.flowMappingEnd`.

  * **§3 `scanNextTokenIx_flow_open_mapping_nested`** — `{` inside an
    existing flow context. Threads preprocess → `dispatchStructural`
    (none) → allowDirectives update → `checkBlockFlowIndent_ok_flow`
    → `dispatchFlowIndicators_brace` → `scanFlowMappingStartIx`.
    Yields `flowLevel + 1`, `simpleKeyStack.pop = s.simpleKeyStack`
    (push undone by `.pop`), `StackEndLineOnLineIx s' s'.line` (the
    pushed key inherits `EndLineOnLineIx` from the prior state).

## Indexed simplification

The legacy `_close_*_nested` proofs split from `_close_*_outermost`
along `validateFlowClose` (which checks `flowLevel = 0` and EOF
*after* `scanFlowSequenceEnd`). The indexed pipeline has no
`validateFlowClose` tail-validation (see comment on
`dispatchFlowIndicators_close_bracket` in
`Maintenance/Pipeline.lean`), so the dispatcher succeeds for any
`flowLevel > 0`. The split between `_nested` and `_outermost`
survives at the *scenario* level because their callers have
different preconditions and different result conclusions (nested
needs `flowLevel - 1`, `StackEndLineOnLineIx`, `simpleKeyStack.pop`;
outermost needs `flowLevel = 0`, `peek? = none`).

## Stack-back?-getD bookkeeping for `EndLineOnLineIx`

After `scanFlowSequenceEndIx`/`scanFlowMappingEndIx`, the result
state's `simpleKey` is restored from `simpleKeyStack.back?.getD
{ cursor := IxCursor.start input }`. To discharge
`EndLineOnLineIx`, we case-split on `back?`:

  * `none` branch — `getD` returns the default record whose
    `possible := false` (structure-default), so the `EndLineOnLineIx
    s'` hypothesis vacuously holds.
  * `some sk` branch — `getD` returns `sk`; the
    `StackEndLineOnLineIx` precondition gives `sk.possible → sk.endLine
    = l ∧ sk.pos.line = l`, exactly what we need.
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

variable {input : String}

/-! ## §1  `scanNextTokenIx_flow_close_seq_nested`

`]` at flowLevel ≥ 2 inside an existing flow context. -/

/-- Full `scanNextTokenIx` for `']'` at flowLevel ≥ 2.
    Indexed twin of `scanNextToken_flow_close_seq_nested` (legacy 4793). -/
lemma scanNextTokenIx_flow_close_seq_nested (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨']' :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_stack_endline : StackEndLineOnLineIx s s.cursor.pos.line) :
    ∃ s', scanNextTokenIx s = .ok (some s')
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = s.flowLevel - 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.cursor.pos.col = s.cursor.pos.col + 1
      ∧ (∀ t, lastRealTokenValIx? s'.tokens = some t →
          t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
          ∧ t ≠ YamlToken.flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.cursor.pos.line = s.cursor.pos.line
      ∧ AllTokensOnLineIx s' s'.cursor.pos.line
      ∧ EndLineOnLineIx s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack.pop := by
  -- Step 1: preprocessing
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, ']')) :=
    scanNextTokenIx_preprocess_flow s ']' rest s.cursor.pos.col hcorr h_flow
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
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_explicitKeyLine s
  have h_ad_cursor : s_ad.cursor = s.cursor := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_cursor s
  have h_ad_tokens : s_ad.tokens = (saveSimpleKeyIx s).tokens := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
    have h1 : (saveSimpleKeyIx s).simpleKeyStack = s.simpleKeyStack :=
      saveSimpleKeyIx_preserves_simpleKeyStack s
    rw [h_s_ad_def]; split <;> exact h1
  -- Step 6: flow dispatch (no validateFlowClose in indexed pipeline)
  have h_fl_pos : s_ad.flowLevel > 0 := by rw [h_ad_fl]; omega
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad ']' =
      .ok (some (scanFlowSequenceEndIx s_ad)) :=
    dispatchFlowIndicators_close_bracket s_ad h_fl_pos
  -- Step 7: compose via scanNextTokenIx_via_flow_dispatch
  have h_snt := scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
    (scanFlowSequenceEndIx s_ad) ']'
    h_pp h_struct h_s_ad_def h_check h_flow_disp
  -- Step 8: extract via scanFlowSequenceEndIx_detail
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨']' :: rest, s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_ad_cursor]; exact hcorr.chars_from
    · rw [h_ad_cursor]; exact hcorr.input_prefix
    · intro i hi h0
      have hi' : i < s.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s.indents[i]'hi' := by congr 1
      rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowSequenceEndIx_detail s_ad rest h_ad_corr
  -- Field equalities for the result state (scanFlowSequenceEndIx s_ad)
  have h_s'_corr : ScannerSurfCorrIx (scanFlowSequenceEndIx s_ad)
      ⟨rest, (scanFlowSequenceEndIx s_ad).cursor.pos.col⟩ := by
    rw [h_col_f]; exact h_corr_f
  have h_s'_fl : (scanFlowSequenceEndIx s_ad).flowLevel = s.flowLevel - 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_s'_dp : (scanFlowSequenceEndIx s_ad).directivesPresent = s.directivesPresent :=
    h_dp_f.trans h_ad_dp
  have h_s'_ids : (scanFlowSequenceEndIx s_ad).indents = s.indents :=
    h_ids_f.trans h_ad_ids
  have h_s'_ek : (scanFlowSequenceEndIx s_ad).explicitKeyLine = s.explicitKeyLine := by
    rw [scanFlowSequenceEndIx_explicitKeyLine]; exact h_ad_ek
  have h_s'_col : (scanFlowSequenceEndIx s_ad).cursor.pos.col = s.cursor.pos.col + 1 := by
    rw [h_col_f, show s_ad.cursor.pos.col = s.cursor.pos.col from by rw [h_ad_cursor]]
  -- lastRealTokenValIx? = .flowSequenceEnd → ≠ any flow opener / entry
  have h_s'_last : ∀ t, lastRealTokenValIx? (scanFlowSequenceEndIx s_ad).tokens = some t →
      t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
      ∧ t ≠ YamlToken.flowEntry := by
    intro t ht
    rw [scanFlowSequenceEndIx_lastRealTokenValIx] at ht
    injection ht with ht; subst ht
    exact ⟨nofun, nofun, nofun⟩
  -- simpleKeyAllowed = false
  have h_s'_ska : (scanFlowSequenceEndIx s_ad).simpleKeyAllowed = false := by
    unfold scanFlowSequenceEndIx; rfl
  -- line preservation
  have ⟨h_peek_ad, h_lt_ad⟩ :=
    peek_of_chars_consIx_state s_ad ']' rest s_ad.cursor.pos.col h_ad_corr
  have h_ad_line : s_ad.cursor.pos.line = s.cursor.pos.line := by rw [h_ad_cursor]
  have h_s'_line : (scanFlowSequenceEndIx s_ad).cursor.pos.line = s.cursor.pos.line := by
    show (s_ad.emit YamlToken.flowSequenceEnd).advance.cursor.pos.line = s.cursor.pos.line
    rw [advance_cursor, emit_cursor]
    exact (advance_line_of_peekIx s_ad.cursor ']' h_lt_ad h_peek_ad
      (by decide) (by decide)).trans h_ad_line
  -- AllTokensOnLineIx via _scanFlowSequenceEndIx (emit + advance)
  have h_s'_atol :
      AllTokensOnLineIx (scanFlowSequenceEndIx s_ad)
        (scanFlowSequenceEndIx s_ad).cursor.pos.line := by
    rw [h_s'_line]
    have h_atol_sk : AllTokensOnLineIx (saveSimpleKeyIx s) s.cursor.pos.line :=
      AllTokensOnLineIx_saveSimpleKeyIx s s.cursor.pos.line h_atol rfl
    have h_atol_ad : AllTokensOnLineIx s_ad s.cursor.pos.line :=
      AllTokensOnLineIx_of_tokens_eq h_ad_tokens h_atol_sk
    exact AllTokensOnLineIx_scanFlowSequenceEndIx s_ad s.cursor.pos.line h_atol_ad h_ad_line
  -- simpleKeyStack.pop
  have h_s'_stack : (scanFlowSequenceEndIx s_ad).simpleKeyStack = s.simpleKeyStack.pop := by
    rw [scanFlowSequenceEndIx_stack_popped]; rw [h_ad_stack]
  -- EndLineOnLineIx — simpleKey is restored from stack
  have h_s'_endline : EndLineOnLineIx (scanFlowSequenceEndIx s_ad) := by
    intro h_poss
    rw [scanFlowSequenceEndIx_simpleKey_restored] at h_poss
    rw [h_ad_stack] at h_poss
    rw [h_s'_line]
    -- s'.simpleKey = simpleKeyStack.back?.getD (default with possible := false)
    rw [show (scanFlowSequenceEndIx s_ad).simpleKey =
        s.simpleKeyStack.back?.getD { cursor := IxCursor.start input } by
      rw [scanFlowSequenceEndIx_simpleKey_restored]; rw [h_ad_stack]]
    -- StackEndLineOnLineIx: case-split on back?
    unfold StackEndLineOnLineIx at h_stack_endline
    cases h_back : s.simpleKeyStack.back? with
    | none =>
      rw [h_back] at h_poss
      simp [Option.getD] at h_poss
    | some sk =>
      rw [h_back] at h_poss h_stack_endline
      simp [Option.getD] at h_poss ⊢
      have ⟨h1, h2⟩ := h_stack_endline h_poss
      refine ⟨h1, ?_⟩
      -- SimpleKeyStateIx.pos sk = sk.cursor.pos
      show sk.cursor.pos.line = s.cursor.pos.line
      exact h2
  refine ⟨_, h_snt, h_s'_corr, h_s'_fl, h_s'_dp, h_s'_ids, h_s'_ek, h_s'_col,
         h_s'_last, h_s'_ska, h_s'_line, h_s'_atol, h_s'_endline, h_s'_stack⟩

/-! ## §2  `scanNextTokenIx_flow_close_mapping_nested`

`}` at flowLevel ≥ 2 inside an existing flow context. Mirror of §1
with `scanFlowMappingEndIx` and `.flowMappingEnd`. -/

/-- Full `scanNextTokenIx` for `'}'` at flowLevel ≥ 2.
    Indexed twin of `scanNextToken_flow_close_mapping_nested`
    (legacy 5141). -/
lemma scanNextTokenIx_flow_close_mapping_nested (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨'}' :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_stack_endline : StackEndLineOnLineIx s s.cursor.pos.line) :
    ∃ s', scanNextTokenIx s = .ok (some s')
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = s.flowLevel - 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.cursor.pos.col = s.cursor.pos.col + 1
      ∧ (∀ t, lastRealTokenValIx? s'.tokens = some t →
          t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
          ∧ t ≠ YamlToken.flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.cursor.pos.line = s.cursor.pos.line
      ∧ AllTokensOnLineIx s' s'.cursor.pos.line
      ∧ EndLineOnLineIx s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack.pop := by
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, '}')) :=
    scanNextTokenIx_preprocess_flow s '}' rest s.cursor.pos.col hcorr h_flow
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
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_explicitKeyLine s
  have h_ad_cursor : s_ad.cursor = s.cursor := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_cursor s
  have h_ad_tokens : s_ad.tokens = (saveSimpleKeyIx s).tokens := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
    have h1 : (saveSimpleKeyIx s).simpleKeyStack = s.simpleKeyStack :=
      saveSimpleKeyIx_preserves_simpleKeyStack s
    rw [h_s_ad_def]; split <;> exact h1
  have h_fl_pos : s_ad.flowLevel > 0 := by rw [h_ad_fl]; omega
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad '}' =
      .ok (some (scanFlowMappingEndIx s_ad)) :=
    dispatchFlowIndicators_close_brace s_ad h_fl_pos
  have h_snt := scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
    (scanFlowMappingEndIx s_ad) '}'
    h_pp h_struct h_s_ad_def h_check h_flow_disp
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨'}' :: rest, s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_ad_cursor]; exact hcorr.chars_from
    · rw [h_ad_cursor]; exact hcorr.input_prefix
    · intro i hi h0
      have hi' : i < s.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s.indents[i]'hi' := by congr 1
      rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowMappingEndIx_detail s_ad rest h_ad_corr
  have h_s'_corr : ScannerSurfCorrIx (scanFlowMappingEndIx s_ad)
      ⟨rest, (scanFlowMappingEndIx s_ad).cursor.pos.col⟩ := by
    rw [h_col_f]; exact h_corr_f
  have h_s'_fl : (scanFlowMappingEndIx s_ad).flowLevel = s.flowLevel - 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_s'_dp : (scanFlowMappingEndIx s_ad).directivesPresent = s.directivesPresent :=
    h_dp_f.trans h_ad_dp
  have h_s'_ids : (scanFlowMappingEndIx s_ad).indents = s.indents :=
    h_ids_f.trans h_ad_ids
  have h_s'_ek : (scanFlowMappingEndIx s_ad).explicitKeyLine = s.explicitKeyLine := by
    rw [scanFlowMappingEndIx_explicitKeyLine]; exact h_ad_ek
  have h_s'_col : (scanFlowMappingEndIx s_ad).cursor.pos.col = s.cursor.pos.col + 1 := by
    rw [h_col_f, show s_ad.cursor.pos.col = s.cursor.pos.col from by rw [h_ad_cursor]]
  have h_s'_last : ∀ t, lastRealTokenValIx? (scanFlowMappingEndIx s_ad).tokens = some t →
      t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
      ∧ t ≠ YamlToken.flowEntry := by
    intro t ht
    rw [scanFlowMappingEndIx_lastRealTokenValIx] at ht
    injection ht with ht; subst ht
    exact ⟨nofun, nofun, nofun⟩
  have h_s'_ska : (scanFlowMappingEndIx s_ad).simpleKeyAllowed = false := by
    unfold scanFlowMappingEndIx; rfl
  have ⟨h_peek_ad, h_lt_ad⟩ :=
    peek_of_chars_consIx_state s_ad '}' rest s_ad.cursor.pos.col h_ad_corr
  have h_ad_line : s_ad.cursor.pos.line = s.cursor.pos.line := by rw [h_ad_cursor]
  have h_s'_line : (scanFlowMappingEndIx s_ad).cursor.pos.line = s.cursor.pos.line := by
    show (s_ad.emit YamlToken.flowMappingEnd).advance.cursor.pos.line = s.cursor.pos.line
    rw [advance_cursor, emit_cursor]
    exact (advance_line_of_peekIx s_ad.cursor '}' h_lt_ad h_peek_ad
      (by decide) (by decide)).trans h_ad_line
  have h_s'_atol :
      AllTokensOnLineIx (scanFlowMappingEndIx s_ad)
        (scanFlowMappingEndIx s_ad).cursor.pos.line := by
    rw [h_s'_line]
    have h_atol_sk : AllTokensOnLineIx (saveSimpleKeyIx s) s.cursor.pos.line :=
      AllTokensOnLineIx_saveSimpleKeyIx s s.cursor.pos.line h_atol rfl
    have h_atol_ad : AllTokensOnLineIx s_ad s.cursor.pos.line :=
      AllTokensOnLineIx_of_tokens_eq h_ad_tokens h_atol_sk
    exact AllTokensOnLineIx_scanFlowMappingEndIx s_ad s.cursor.pos.line h_atol_ad h_ad_line
  have h_s'_stack : (scanFlowMappingEndIx s_ad).simpleKeyStack = s.simpleKeyStack.pop := by
    rw [scanFlowMappingEndIx_stack_popped]; rw [h_ad_stack]
  have h_s'_endline : EndLineOnLineIx (scanFlowMappingEndIx s_ad) := by
    intro h_poss
    rw [scanFlowMappingEndIx_simpleKey_restored] at h_poss
    rw [h_ad_stack] at h_poss
    rw [h_s'_line]
    rw [show (scanFlowMappingEndIx s_ad).simpleKey =
        s.simpleKeyStack.back?.getD { cursor := IxCursor.start input } by
      rw [scanFlowMappingEndIx_simpleKey_restored]; rw [h_ad_stack]]
    unfold StackEndLineOnLineIx at h_stack_endline
    cases h_back : s.simpleKeyStack.back? with
    | none =>
      rw [h_back] at h_poss
      simp [Option.getD] at h_poss
    | some sk =>
      rw [h_back] at h_poss h_stack_endline
      simp [Option.getD] at h_poss ⊢
      have ⟨h1, h2⟩ := h_stack_endline h_poss
      refine ⟨h1, ?_⟩
      show sk.cursor.pos.line = s.cursor.pos.line
      exact h2
  refine ⟨_, h_snt, h_s'_corr, h_s'_fl, h_s'_dp, h_s'_ids, h_s'_ek, h_s'_col,
         h_s'_last, h_s'_ska, h_s'_line, h_s'_atol, h_s'_endline, h_s'_stack⟩

/-! ## §3  `scanNextTokenIx_flow_open_mapping_nested`

`{` inside an existing flow context — push onto `simpleKeyStack`,
increment `flowLevel`, yield `StackEndLineOnLineIx s' s'.line`
inheriting the prior `EndLineOnLineIx s`. -/

/-- Full `scanNextTokenIx` for `'{'` inside an existing flow context.
    Indexed twin of `scanNextToken_flow_open_mapping_nested`
    (legacy 5329). -/
lemma scanNextTokenIx_flow_open_mapping_nested (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨'{' :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_endline : EndLineOnLineIx s) :
    ∃ s', scanNextTokenIx s = .ok (some s')
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = s.flowLevel + 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.cursor.pos.col = s.cursor.pos.col + 1
      ∧ s'.cursor.pos.line = s.cursor.pos.line
      ∧ AllTokensOnLineIx s' s'.cursor.pos.line
      ∧ EndLineOnLineIx s'
      ∧ StackEndLineOnLineIx s' s'.cursor.pos.line
      ∧ s'.simpleKeyStack.pop = s.simpleKeyStack := by
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, '{')) :=
    scanNextTokenIx_preprocess_flow s '{' rest s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) '{' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if (saveSimpleKeyIx s).allowDirectives then
        { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
      else saveSimpleKeyIx s := ⟨_, rfl⟩
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    rw [h_s_ad_def]; split <;> exact h_sk_flow
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad '{' = .ok () :=
    checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_explicitKeyLine s
  have h_ad_cursor : s_ad.cursor = s.cursor := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_cursor s
  have h_ad_tokens : s_ad.tokens = (saveSimpleKeyIx s).tokens := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
    have h1 : (saveSimpleKeyIx s).simpleKeyStack = s.simpleKeyStack :=
      saveSimpleKeyIx_preserves_simpleKeyStack s
    rw [h_s_ad_def]; split <;> exact h1
  -- The saved simpleKey carried by `s_ad` is `(saveSimpleKeyIx s).simpleKey`
  have h_ad_simpleKey : s_ad.simpleKey = (saveSimpleKeyIx s).simpleKey := by
    rw [h_s_ad_def]; split <;> rfl
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad '{' =
      .ok (some (scanFlowMappingStartIx s_ad)) :=
    dispatchFlowIndicators_brace s_ad
  have h_snt := scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
    (scanFlowMappingStartIx s_ad) '{'
    h_pp h_struct h_s_ad_def h_check h_flow_disp
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨'{' :: rest, s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_ad_cursor]; exact hcorr.chars_from
    · rw [h_ad_cursor]; exact hcorr.input_prefix
    · intro i hi h0
      have hi' : i < s.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s.indents[i]'hi' := by congr 1
      rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowMappingStartIx_detail s_ad rest h_ad_corr
  have h_s'_corr : ScannerSurfCorrIx (scanFlowMappingStartIx s_ad)
      ⟨rest, (scanFlowMappingStartIx s_ad).cursor.pos.col⟩ := by
    rw [h_col_f]; exact h_corr_f
  have h_s'_fl : (scanFlowMappingStartIx s_ad).flowLevel = s.flowLevel + 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_s'_dp : (scanFlowMappingStartIx s_ad).directivesPresent = s.directivesPresent :=
    h_dp_f.trans h_ad_dp
  have h_s'_ids : (scanFlowMappingStartIx s_ad).indents = s.indents :=
    h_ids_f.trans h_ad_ids
  have h_s'_ek : (scanFlowMappingStartIx s_ad).explicitKeyLine = s.explicitKeyLine := by
    rw [scanFlowMappingStartIx_explicitKeyLine]; exact h_ad_ek
  have h_s'_col : (scanFlowMappingStartIx s_ad).cursor.pos.col = s.cursor.pos.col + 1 := by
    rw [h_col_f, show s_ad.cursor.pos.col = s.cursor.pos.col from by rw [h_ad_cursor]]
  have ⟨h_peek_ad, h_lt_ad⟩ :=
    peek_of_chars_consIx_state s_ad '{' rest s_ad.cursor.pos.col h_ad_corr
  have h_ad_line : s_ad.cursor.pos.line = s.cursor.pos.line := by rw [h_ad_cursor]
  have h_s'_line : (scanFlowMappingStartIx s_ad).cursor.pos.line = s.cursor.pos.line := by
    show (s_ad.emit YamlToken.flowMappingStart).advance.cursor.pos.line = s.cursor.pos.line
    rw [advance_cursor, emit_cursor]
    exact (advance_line_of_peekIx s_ad.cursor '{' h_lt_ad h_peek_ad
      (by decide) (by decide)).trans h_ad_line
  have h_s'_atol :
      AllTokensOnLineIx (scanFlowMappingStartIx s_ad)
        (scanFlowMappingStartIx s_ad).cursor.pos.line := by
    rw [h_s'_line]
    have h_atol_sk : AllTokensOnLineIx (saveSimpleKeyIx s) s.cursor.pos.line :=
      AllTokensOnLineIx_saveSimpleKeyIx s s.cursor.pos.line h_atol rfl
    have h_atol_ad : AllTokensOnLineIx s_ad s.cursor.pos.line :=
      AllTokensOnLineIx_of_tokens_eq h_ad_tokens h_atol_sk
    exact AllTokensOnLineIx_scanFlowMappingStartIx s_ad s.cursor.pos.line h_atol_ad h_ad_line
  -- EndLineOnLineIx: scanFlowMappingStartIx sets simpleKey.possible = false
  have h_s'_endline : EndLineOnLineIx (scanFlowMappingStartIx s_ad) := by
    intro h_poss
    rw [scanFlowMappingStartIx_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  -- StackEndLineOnLineIx: pushed simpleKey inherits EndLineOnLineIx from s
  have h_s_ad_endline : EndLineOnLineIx s_ad := by
    have h_sk_endline : EndLineOnLineIx (saveSimpleKeyIx s) :=
      EndLineOnLineIx_saveSimpleKeyIx s h_endline
    -- Lift through the `if allowDirectives` record update (cursor + simpleKey unchanged)
    intro h_poss
    rw [h_ad_simpleKey] at h_poss
    have ⟨h1, h2⟩ := h_sk_endline h_poss
    refine ⟨?_, ?_⟩
    · rw [h_ad_simpleKey, h1]
      show (saveSimpleKeyIx s).cursor.pos.line = s_ad.cursor.pos.line
      rw [saveSimpleKeyIx_cursor, h_ad_cursor]
    · rw [h_ad_simpleKey, h2]
      show (saveSimpleKeyIx s).cursor.pos.line = s_ad.cursor.pos.line
      rw [saveSimpleKeyIx_cursor, h_ad_cursor]
  have h_s'_stackend : StackEndLineOnLineIx (scanFlowMappingStartIx s_ad)
      (scanFlowMappingStartIx s_ad).cursor.pos.line := by
    unfold StackEndLineOnLineIx
    rw [scanFlowMappingStartIx_stack_pushed, Array.back?_push, h_s'_line]
    intro h_poss
    -- pushed key = s_ad.simpleKey
    have ⟨h1, h2⟩ := h_s_ad_endline h_poss
    refine ⟨h1.trans h_ad_line, ?_⟩
    show s_ad.simpleKey.cursor.pos.line = s.cursor.pos.line
    exact h2.trans h_ad_line
  -- simpleKeyStack.pop = s.simpleKeyStack
  have h_s'_stackpop : (scanFlowMappingStartIx s_ad).simpleKeyStack.pop = s.simpleKeyStack := by
    rw [scanFlowMappingStartIx_stack_pushed, Array.pop_push]; exact h_ad_stack
  refine ⟨_, h_snt, h_s'_corr, h_s'_fl, h_s'_dp, h_s'_ids, h_s'_ek, h_s'_col,
         h_s'_line, h_s'_atol, h_s'_endline, h_s'_stackend, h_s'_stackpop⟩

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
