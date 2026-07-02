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

/-! ## §1b  `scanNextTokenIx_preprocess_flow_ws1`

Variant of §1 with a single leading space: preprocessing of
`' ' :: c :: rest` yields the same result as preprocessing of the
post-space state `s.advance`. Key idea: `skipToContentS` absorbs the
one space (advancing the cursor by one within the same line), reaching
the same content cursor as `skipToContentS` on `s.advance` (which is
the identity there). Used by `emitList_scans_nonemptyIx` to step over
the space after a flow `,`. Indexed twin of legacy
`scanNextToken_preprocess_flow_ws1` (legacy 3590).

The indexed skip machinery is simpler than legacy: there is no
`needIndentCheck`/`skipToContentWs`/`skipSpaces` split — `skipToContent`
does `skipWhitespace` then a single peek-case. So the cursor-level
absorb lemma `skipToContent_one_space` is short. -/

/-- Cursor-level: `skipToContent` absorbs exactly one leading space when
    the following character is content (non-ws, non-lb, non-`#`).
    `skipWhitespace` advances past the lone space; the peek-case then
    stops at the content character. -/
theorem skipToContent_one_space (c : IxCursor input) {ch : Char}
    (h_sp : c.peek? = some ' ')
    (h_next : c.advance.peek? = some ch)
    (h_nws : isWhiteSpaceBool ch = false)
    (h_nlb : isLineBreakBool ch = false)
    (h_nc : ch ≠ '#') :
    L4YAML.Scanner.Indexed.skipToContent c = c.advance := by
  -- offset bound: peek = some ' ' ⟹ in range
  have h_lt : c.pos.offset < input.utf8ByteSize := by
    by_cases h : c.pos.offset < input.utf8ByteSize
    · exact h
    · rw [(IxCursor.peek?_eq_none_iff c).mpr (Nat.le_of_not_lt h)] at h_sp
      simp at h_sp
  -- `skipWhitespace c = c.advance`: one whitespace step, then stop at content.
  have hSW : L4YAML.Scanner.Indexed.skipWhitespace c = c.advance := by
    unfold L4YAML.Scanner.Indexed.skipWhitespace
    obtain ⟨n, hn⟩ : ∃ n, input.utf8ByteSize = n + 1 :=
      ⟨input.utf8ByteSize - 1, by omega⟩
    rw [hn]
    unfold L4YAML.Scanner.Indexed.skipWhitespaceLoop
    have hpw_c : peekIsWhiteSpace c = true := by
      unfold peekIsWhiteSpace; rw [h_sp]; decide
    simp only [hpw_c, if_true]
    have hpw_adv : peekIsWhiteSpace c.advance = false := by
      unfold peekIsWhiteSpace; rw [h_next]; exact h_nws
    cases n with
    | zero => rfl
    | succ m => simp [L4YAML.Scanner.Indexed.skipWhitespaceLoop, hpw_adv]
  -- `skipToContent c` settles at `c.advance` (content, not `#`, not line break).
  unfold L4YAML.Scanner.Indexed.skipToContent L4YAML.Scanner.Indexed.skipToContentLoop
  simp only [hSW, h_next,
    show isCommentBool ch = false from by unfold isCommentBool; simp [h_nc],
    h_nlb, Bool.false_eq_true, if_false]

/-- State-level: `skipToContentS` absorbs one leading space, yielding
    `s.advance`. The line is unchanged (advance past a space), so the
    `skipToContentS` newline-reset branch is not taken. -/
theorem skipToContentS_ws1 (s : ScannerStateIx input) {c : Char}
    (h_sp : s.peek? = some ' ')
    (h_next : s.advance.peek? = some c)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#')
    (h_lt : s.cursor.pos.offset < input.utf8ByteSize) :
    s.skipToContentS = s.advance := by
  have h_cur : L4YAML.Scanner.Indexed.skipToContent s.cursor = s.cursor.advance :=
    skipToContent_one_space s.cursor h_sp h_next h_nws h_nlb h_nc
  have h_line : s.cursor.advance.pos.line = s.cursor.pos.line :=
    advance_line_of_peekIx s.cursor ' ' h_lt h_sp (by decide) (by decide)
  unfold ScannerStateIx.skipToContentS ScannerStateIx.advance
  rw [h_cur]
  simp only [h_line, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

/-- Preprocessing of `' ' :: c :: rest` in flow context equals
    preprocessing of the post-space state `s.advance`, with that state's
    invariants exposed. Indexed twin of `scanNextToken_preprocess_flow_ws1`
    (legacy 3590). -/
theorem scanNextTokenIx_preprocess_flow_ws1 (s : ScannerStateIx input) (c : Char)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨' ' :: c :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#')
    (_h_indent : s.currentIndent < 0) :
    ∃ s₁, ScannerSurfCorrIx s₁ ⟨c :: rest, s₁.cursor.pos.col⟩
      ∧ s₁.inFlow = true
      ∧ s₁.flowLevel = s.flowLevel
      ∧ s₁.currentIndent = s.currentIndent
      ∧ s₁.cursor.pos.col = s.cursor.pos.col + 1
      ∧ s₁.directivesPresent = s.directivesPresent
      ∧ s₁.indents = s.indents
      ∧ s₁.explicitKeyLine = s.explicitKeyLine
      ∧ s₁.cursor.pos.line = s.cursor.pos.line
      ∧ scanNextTokenIx_preprocess s = scanNextTokenIx_preprocess s₁
      ∧ (AllTokensOnLineIx s s.cursor.pos.line →
          AllTokensOnLineIx s₁ s₁.cursor.pos.line)
      ∧ (EndLineOnLineIx s → EndLineOnLineIx s₁)
      ∧ s₁.simpleKeyStack = s.simpleKeyStack
      ∧ s₁.tokens = s.tokens := by
  -- The post-space state is `s.advance` (advance only moves the cursor).
  have ⟨h_sp, h_lt⟩ := peek_of_chars_consIx_state s ' ' (c :: rest) _ hcorr
  -- Surface correspondence at `c :: rest` after the space.
  have h_corr_adv : ScannerSurfCorrIx s.advance ⟨c :: rest, s.cursor.pos.col + 1⟩ :=
    advance_non_newline_corrIx_state s s.advance ' ' (c :: rest) hcorr rfl rfl
      h_lt (by decide) (by decide)
  have ⟨h_next, h_lt_adv⟩ := peek_of_chars_consIx_state s.advance c rest _ h_corr_adv
  -- Field facts for `s.advance` (advance preserves everything but the cursor).
  have h_col_adv : s.advance.cursor.pos.col = s.cursor.pos.col + 1 := h_corr_adv.col_eq.symm
  have h_line_adv : s.advance.cursor.pos.line = s.cursor.pos.line :=
    advance_line_of_peekIx_state s ' ' h_lt h_sp (by decide) (by decide)
  have h_flow_adv : s.advance.inFlow = true := h_flow
  have h_hm_adv : s.advance.hasMore = true := by
    unfold ScannerStateIx.hasMore IxCursor.hasMore; exact decide_eq_true h_lt_adv
  have h_stc_ws : s.skipToContentS = s.advance :=
    skipToContentS_ws1 s h_sp h_next h_nws h_nlb h_nc h_lt
  -- `ScannerSurfCorrIx` restated at the witness column.
  have h_corr₁ : ScannerSurfCorrIx s.advance ⟨c :: rest, s.advance.cursor.pos.col⟩ := by
    rw [h_col_adv]; exact h_corr_adv
  -- Both preprocess paths reduce to `.ok (some (saveSimpleKeyIx s.advance, c))`.
  have h_pp_s : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s.advance, c)) := by
    unfold scanNextTokenIx_preprocess
    simp only [h_stc_ws, h_hm_adv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp only [h_flow_adv, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    simp only [show ¬(s.advance.indents.size < s.advance.indents.size) from by omega,
      decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [saveSimpleKeyIx_peek?, h_next]
  have h_pp_adv : scanNextTokenIx_preprocess s.advance =
      .ok (some (saveSimpleKeyIx s.advance, c)) :=
    scanNextTokenIx_preprocess_flow s.advance c rest (s.cursor.pos.col + 1)
      h_corr_adv h_flow_adv h_nws h_nlb h_nc
  refine ⟨s.advance, h_corr₁, h_flow_adv, rfl, rfl, h_col_adv, rfl, rfl, rfl, h_line_adv,
    h_pp_s.trans h_pp_adv.symm, ?_, ?_, rfl, rfl⟩
  · -- AllTokensOnLineIx transfers: same tokens (defeq), same line.
    intro h_a i hi
    rw [h_line_adv]; exact h_a i hi
  · -- EndLineOnLineIx transfers: same simpleKey (defeq), same line.
    intro h_e h_poss
    rw [h_line_adv]; exact h_e h_poss

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
