/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Detail
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Invariant
import L4YAML.Proofs.Scanner.IndexedIndent

/-! # `FlowMonoChain.Sync.Scenarios.Preflow` — Phase 3 Step
`6f.3b3.flowmono.sync.scenarios.preflow`

**Sub-session 1 of `.flowmono.sync.scenarios`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 3561–3585 and 4572–4684).

Two deliverables:

  * **§1 `scanNextTokenIx_preprocess_flow`** — the cornerstone
    preprocessing simplification used by every mid-chain scenario.
    In flow context with a content character at the cursor (non-ws,
    non-lb, non-`#`), `scanNextTokenIx_preprocess s = .ok (some
    (saveSimpleKeyIx s, c))`. The proof factors through the cursor-
    level `skipToContent_at_content` (from `IndexedIndent`) lifted
    to the state-level `skipToContentS` (which only updates the
    cursor when the line *changes*; here the cursor is unchanged so
    the else-branch fires and returns `s` verbatim).

  * **§2 `scanNextTokenIx_flow_comma`** — the first scenario chain
    using `_preprocess_flow`. Threads a `','`-character through
    preprocess → `dispatchStructural` (returns `none` in flow context
    with `currentIndent < 0` and `col > 0`) → allowDirectives update
    → `checkBlockFlowIndent` (vacuous for `','`) → `dispatchFlow
    Indicators_comma` → `scanFlowEntryIx_ok` (precondition: no
    trailing flow delimiter). All conclusions about
    `ScannerSurfCorrIx`, `AllTokensOnLineIx`, `EndLineOnLineIx`, and
    simple-key-stack preservation match the legacy. Indexed twin of
    `scanNextToken_flow_comma` (legacy 4575).

## Scope justification — why this is a separate sub-session

The legacy `.sync.scenarios` plan called for shipping all 9 theorems
(2 preprocessing helpers + 7 scenario chains) in one ~700 LOC file.
Per the in-session retroactive modularisation pattern (Reflection
129), we split into three sibling sub-sessions:

  * **`.preflow`** (this file): preprocessing helper + first
    scenario.
  * **`.flowclose`** (next session): the 3 remaining mid-chain
    scenarios (`_close_seq_nested`, `_close_mapping_nested`,
    `_open_mapping_nested`).
  * **`.endpoint`** (later): the 2 outermost EOF scenarios
    (`_close_seq_outermost`, `_close_mapping_outermost`) plus the
    init-state chains (`_preprocess_init_state`,
    `_flow_open_mapping_init`).

Each sub-session matches one auxiliary precondition pattern:
mid-chain (this file + `.flowclose`) share the same `saveSimpleKeyIx
+ s_ad + checkBlockFlowIndent_ok_*` skeleton; the EOF cases need
`peek_none_of_empty_surfIx`; the init-state cases need
`initial_corrIx`-style infrastructure not yet ported.
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

/-! ## §1  `scanNextTokenIx_preprocess_flow`

In flow context with a content character at the cursor,
`scanNextTokenIx_preprocess` reduces to `.ok (some (saveSimpleKeyIx
s, c))`. -/

/-- State-level wrapper for `IndexedIndent.skipToContent_at_content`:
    when the cursor sits at a content character, `skipToContentS` is
    the identity. The line doesn't change (cursor doesn't advance),
    so the `skipToContentS` definition takes the else branch
    `{ s with cursor := s.cursor } = s`. -/
theorem skipToContentS_id_of_content (s : ScannerStateIx input)
    {ch : Char} (h_pk : s.peek? = some ch)
    (h_nws : isWhiteSpaceBool ch = false)
    (h_nlb : isLineBreakBool ch = false)
    (h_nc : ch ≠ '#') :
    s.skipToContentS = s := by
  have h_cur_eq : L4YAML.Scanner.Indexed.skipToContent s.cursor = s.cursor :=
    L4YAML.Scanner.Indexed.skipToContent_at_content s.cursor h_pk h_nws h_nlb h_nc
  unfold ScannerStateIx.skipToContentS
  rw [h_cur_eq]
  simp

/-- The cornerstone preprocessing reduction in flow context.
    Indexed twin of `scanNextToken_preprocess_flow` (legacy 3561). -/
theorem scanNextTokenIx_preprocess_flow (s : ScannerStateIx input) (c : Char)
    (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorrIx s ⟨c :: rest, col⟩)
    (h_flow : s.inFlow = true)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#') :
    scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, c)) := by
  -- Step 1: peek and offset bound from ScannerSurfCorrIx
  have ⟨h_pk, h_lt⟩ := peek_of_chars_consIx_state s c rest col hcorr
  -- Step 2: skipToContentS is identity (content character)
  have h_stc : s.skipToContentS = s :=
    skipToContentS_id_of_content s h_pk h_nws h_nlb h_nc
  -- Step 3: hasMore = true
  have h_hm : s.hasMore = true := by
    unfold ScannerStateIx.hasMore IxCursor.hasMore
    exact decide_eq_true h_lt
  -- Step 4: Reduce the preprocess function
  unfold scanNextTokenIx_preprocess
  -- skipToContentS s = s
  simp only [h_stc, h_hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  -- !s.inFlow = false → skip unwindIndents branch
  simp only [h_flow, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  -- indents.size < indents.size = false
  simp only [show ¬(s.indents.size < s.indents.size) from by omega,
    decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  -- saveSimpleKeyIx s.peek? = s.peek? = some c
  rw [saveSimpleKeyIx_peek?, h_pk]

/-! ## §2  `scanNextTokenIx_flow_comma`

Full `scanNextTokenIx` for `','` in flow context. Threads
preprocessing (via §1) → structural dispatch (none) → flow dispatch
(`dispatchFlowIndicators_comma`). -/

/-- Full `scanNextTokenIx` for `','` in flow context.
    Indexed twin of `scanNextToken_flow_comma` (legacy 4575). -/
theorem scanNextTokenIx_flow_comma (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨',' :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_last : ∀ t, lastRealTokenValIx? s.tokens = some t →
      t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
      ∧ t ≠ YamlToken.flowEntry)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_endline : EndLineOnLineIx s) :
    ∃ s', scanNextTokenIx s = .ok (some s')
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.cursor.pos.col = s.cursor.pos.col + 1
      ∧ s'.cursor.pos.line = s.cursor.pos.line
      ∧ AllTokensOnLineIx s' s'.cursor.pos.line
      ∧ EndLineOnLineIx s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack := by
  -- Step 1: preprocessing
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, ',')) :=
    scanNextTokenIx_preprocess_flow s ',' rest s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none
  -- (saveSimpleKeyIx s preserves inFlow / currentIndent / cursor.pos.col)
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) ',' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: introduce s_ad via opaque equation (avoids Mathlib's `set` tactic)
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if (saveSimpleKeyIx s).allowDirectives then
        { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
      else saveSimpleKeyIx s := ⟨_, rfl⟩
  -- Step 4: checkBlockFlowIndent for ','
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad ',' = .ok () :=
    checkBlockFlowIndent_ok_comma s_ad
  -- Step 5: derive field equalities for s_ad (via case split on h_s_ad_def)
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
  have h_ad_simpleKey : s_ad.simpleKey = (saveSimpleKeyIx s).simpleKey := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
    have h1 : (saveSimpleKeyIx s).simpleKeyStack = s.simpleKeyStack :=
      saveSimpleKeyIx_preserves_simpleKeyStack s
    rw [h_s_ad_def]; split <;> exact h1
  -- Step 6: flow dispatch for ',' requires flowLevel > 0 and last-token guard
  have h_fl_pos : s_ad.flowLevel > 0 := by
    rw [h_ad_fl]
    unfold ScannerStateIx.inFlow at h_flow
    exact of_decide_eq_true h_flow
  have h_ad_last : ∀ t, lastRealTokenValIx? s_ad.tokens = some t →
      t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
      ∧ t ≠ YamlToken.flowEntry := by
    intro t ht
    rw [h_ad_tokens] at ht
    exact saveSimpleKeyIx_preserves_lastRealTokenValIx_ne_flow s h_last t ht
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad ',' =
      .ok (some { (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }) :=
    dispatchFlowIndicators_comma s_ad h_fl_pos h_ad_last
  -- Step 7: compose via scanNextTokenIx_via_flow_dispatch
  have h_snt := scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
    { (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true } ','
    h_pp h_struct h_s_ad_def h_check h_flow_disp
  -- Step 8: extract result properties using the field equalities for s_ad
  -- For the result state s' := { (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }
  -- Reach in via explicit `show` since s' is just a definitional sugar.
  -- (a) ScannerSurfCorrIx for s_ad at the precondition position
  have h_ad_corr : ScannerSurfCorrIx s_ad ⟨',' :: rest, s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_ad_cursor]; exact hcorr.chars_from
    · rw [h_ad_cursor]; exact hcorr.input_prefix
    · intro i hi h0
      have hi' : i < s.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s.indents[i]'hi' := by congr 1
      rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0
  -- (b) Get the post-advance state's surface correspondence + col/cursor properties
  have ⟨h_peek_ad, h_lt_ad⟩ :=
    peek_of_chars_consIx_state s_ad ',' rest s_ad.cursor.pos.col h_ad_corr
  -- s'.cursor = (s_ad.emit .flowEntry).advance.cursor = s_ad.cursor.advance = s.cursor.advance
  have h_s'_cursor : ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input).cursor = s.cursor.advance := by
    show (s_ad.emit YamlToken.flowEntry).advance.cursor = s.cursor.advance
    rw [advance_cursor, emit_cursor, h_ad_cursor]
  -- s'.indents = s_ad.indents = s.indents
  have h_s'_indents : ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input).indents = s.indents := by
    show (s_ad.emit YamlToken.flowEntry).advance.indents = s.indents
    rw [advance_indents, emit_indents]; exact h_ad_ids
  -- For ScannerSurfCorrIx, we need to use advance_non_newline_corrIx_state
  -- But that lemma assumes the new state shares cursor with s.cursor.advance,
  -- so we wrap accordingly.
  have h_offset_s : s.cursor.pos.offset < input.utf8ByteSize := by
    have ⟨_, h_lt_s⟩ := peek_of_chars_consIx_state s ',' rest s.cursor.pos.col hcorr
    exact h_lt_s
  have h_s'_corr : ScannerSurfCorrIx
      ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input) ⟨rest, s.cursor.pos.col + 1⟩ :=
    advance_non_newline_corrIx_state s _ ',' rest hcorr h_s'_cursor h_s'_indents
      h_offset_s (by decide) (by decide)
  -- s'.cursor.pos.col = s.cursor.pos.col + 1
  have h_s'_col : ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input).cursor.pos.col = s.cursor.pos.col + 1 :=
    h_s'_corr.col_eq.symm
  -- s'.flowLevel = s.flowLevel
  have h_s'_fl : ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input).flowLevel = s.flowLevel := by
    show (s_ad.emit YamlToken.flowEntry).advance.flowLevel = s.flowLevel
    rw [show (s_ad.emit YamlToken.flowEntry).advance.flowLevel = s_ad.flowLevel from rfl]
    exact h_ad_fl
  -- s'.directivesPresent = s.directivesPresent
  have h_s'_dp : ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input).directivesPresent = s.directivesPresent := by
    show (s_ad.emit YamlToken.flowEntry).advance.directivesPresent = s.directivesPresent
    rw [advance_directivesPresent, emit_directivesPresent]; exact h_ad_dp
  -- s'.explicitKeyLine = s.explicitKeyLine
  have h_s'_ek : ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input).explicitKeyLine = s.explicitKeyLine := by
    show (s_ad.emit YamlToken.flowEntry).advance.explicitKeyLine = s.explicitKeyLine
    rw [advance_explicitKeyLine, emit_explicitKeyLine]; exact h_ad_ek
  -- s'.cursor.pos.line = s.cursor.pos.line via cursor-level advance_line_of_peekIx
  have ⟨h_pk_s, h_lt_s⟩ : s.peek? = some ',' ∧ s.cursor.pos.offset < input.utf8ByteSize :=
    peek_of_chars_consIx_state s ',' rest s.cursor.pos.col hcorr
  have h_s'_line : ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input).cursor.pos.line = s.cursor.pos.line := by
    rw [h_s'_cursor]
    exact advance_line_of_peekIx s.cursor ',' h_lt_s h_pk_s (by decide) (by decide)
  -- s'.simpleKeyStack = s.simpleKeyStack
  have h_s'_stack : ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input).simpleKeyStack = s.simpleKeyStack := by
    show s_ad.simpleKeyStack = s.simpleKeyStack
    exact h_ad_stack
  -- AllTokensOnLineIx s' s'.cursor.pos.line
  have h_s'_atol : AllTokensOnLineIx
      ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input)
      ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input).cursor.pos.line := by
    rw [h_s'_line]
    have h_atol_sk : AllTokensOnLineIx (saveSimpleKeyIx s) s.cursor.pos.line :=
      AllTokensOnLineIx_saveSimpleKeyIx s s.cursor.pos.line h_atol rfl
    have h_atol_ad : AllTokensOnLineIx s_ad s.cursor.pos.line :=
      AllTokensOnLineIx_of_tokens_eq h_ad_tokens h_atol_sk
    have h_ad_line : s_ad.cursor.pos.line = s.cursor.pos.line := by
      rw [h_ad_cursor]
    exact AllTokensOnLineIx_scanFlowEntry_expr s_ad s.cursor.pos.line h_atol_ad h_ad_line
  -- EndLineOnLineIx s'
  have h_s'_endline : EndLineOnLineIx
      ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
        : ScannerStateIx input) := by
    intro h_poss
    -- s'.simpleKey = (s_ad.emit .flowEntry).advance.simpleKey = s_ad.simpleKey
    --             = (saveSimpleKeyIx s).simpleKey   (via h_ad_simpleKey)
    have h_s'_sk : ({ (s_ad.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }
          : ScannerStateIx input).simpleKey = (saveSimpleKeyIx s).simpleKey := by
      show s_ad.simpleKey = (saveSimpleKeyIx s).simpleKey; exact h_ad_simpleKey
    have h_sk_endline : EndLineOnLineIx (saveSimpleKeyIx s) :=
      EndLineOnLineIx_saveSimpleKeyIx s h_endline
    rw [h_s'_sk] at h_poss ⊢
    have ⟨h1, h2⟩ := h_sk_endline h_poss
    rw [h_s'_line]
    have h_sk_line : (saveSimpleKeyIx s).cursor.pos.line = s.cursor.pos.line := by
      rw [saveSimpleKeyIx_cursor]
    exact ⟨h1.trans h_sk_line, h2.trans h_sk_line⟩
  -- Combine
  refine ⟨_, h_snt, ?_, h_s'_fl, h_s'_dp, h_s'_indents, h_s'_ek, h_s'_col, h_s'_line,
         h_s'_atol, h_s'_endline, h_s'_stack⟩
  rw [h_s'_col]; exact h_s'_corr

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
