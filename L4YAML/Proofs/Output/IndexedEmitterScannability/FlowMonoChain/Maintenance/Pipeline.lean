/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Maintenance.FlowDispatch

/-! # `FlowMonoChain.Maintenance.Pipeline` — Phase 3 Step 6f.3b3.flowmono.maintenance.pipeline

**Sub-session 2 of `.flowmono.maintenance`** (legacy
`Proofs/Output/EmitterScannability.lean` lines ~3735–~3901,
~4066–~4082, ~4354–~4393, ~4554–~4570, ~4777–~4789, ~4918–~4943,
~5057–~5064, ~5119–~5139, ~5247–~5272, ~5425–~5440; ~400 LOC
contribution before substrate elimination).

Per-character dispatch return-value lemmas (one each for the
"this character does not handle the input" / "this character does
handle the input" outcomes of each of the five sub-dispatches)
plus pipeline composition lemmas (`scanNextTokenIx_via_*`).

## Indexed simplification

The legacy `.maintenance` block split flow-close (`]`, `}`) into
**nested** and **outermost** variants because `validateFlowClose`
ran a tail-validation step (must be at EOF after `flowLevel = 0`).
The indexed `scanNextTokenIx_dispatchFlowIndicators` has **no**
`validateFlowClose` step — flow close just emits the close token
and decrements `flowLevel`, with a single `flowLevel == 0` guard
to reject close-outside-flow. So each legacy `_close_bracket_
nested` / `_close_bracket_outermost` pair collapses to a single
`dispatchFlowIndicators_close_bracket` lemma (and similarly for
brace).

Likewise `scanFlowEntryIx_ok` is one lemma; the legacy split
between `scanFlowEntry_ok` (success precondition) and
`scanFlowEntry_detail` (full ScannerSurfCorr) collapses on the
indexed substrate because the indexed pipeline does not carry a
`ScannerSurfCorr` invariant. The `_detail` variants defer to
`.sync` (which will introduce the indexed surface-correspondence
bridge).

## Scope

  - **§1** — `dispatchStructural` return-value lemmas:
    `_none_flow` (inflow / underindent skip),
    `_none_bracket_init` / `_none_brace_init` (col=0 / no doc marker).
  - **§2** — `checkBlockFlowIndent` return-value lemmas:
    `_ok_flow` (inflow), `_bracket_init` / `_brace_init` (top level
    with currentIndent = -1), `_ok_comma`, `_ok_close_bracket`,
    `_ok_close_brace`.
  - **§3** — `dispatchFlowIndicators` return-value lemmas:
    `_none` (non-flow-indicator), `_bracket`, `_brace`,
    `_close_bracket` (flowLevel > 0),
    `_close_brace` (flowLevel > 0), `_comma` (flowLevel > 0,
    last token not flow delimiter).
  - **§4** — `dispatchBlockIndicators` return-value lemmas:
    `_none_quote`, `_none_comma`, `_none_close_bracket`,
    `_none_close_brace`.
  - **§5** — `scanFlowEntryIx_ok`: precondition for the comma
    dispatch (composes with `dispatchFlowIndicators_comma`).
  - **§6** — Pipeline composition: `scanNextTokenIx_via_content_
    dispatch` (success), `_via_content_dispatch_error`,
    `_via_block_dispatch`. (`_via_flow_dispatch` already lives
    in `Preserve/Step.lean`.)

## Legacy mapping

  | Section | Legacy lines     | Indexed counterpart                |
  | ------- | ---------------- | ---------------------------------- |
  | §1      | 3735–3747, 4066–4073, 5425–5432 | `dispatchStructural_*` |
  | §2      | 3750–3756, 4077–4082, 4382–4393, 5119–5123, 5434–5440 | `checkBlockFlowIndent_*` |
  | §3      | 3759–3774, 4085–4088, 5057–5064, 4777–4789 (+4918–4943 → collapsed), 5125–5139 (+5247–5272 → collapsed), 4554–4570 | `dispatchFlowIndicators_*` |
  | §4      | 3777–3788, 4354–4377                | `dispatchBlockIndicators_*` |
  | §5      | 4398–4421                          | `scanFlowEntryIx_ok` |
  | §6      | 3852–3901                          | `scanNextTokenIx_via_*` |

## Deferred to `.sync`

`_detail` variants of `scanFlow{Sequence,Mapping}{Start,End}` and
`scanFlowEntry_detail`, plus `scanNextToken_flow_*` scenario
chains, require the indexed `ScannerSurfCorr` bridge built in
`.sync`.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx

variable {input : String}

/-! ## §1  `dispatchStructural` return-value lemmas -/

/-- In flow context with `currentIndent < 0` and `col > 0`,
    structural dispatch returns `none` (no doc-marker / directive
    handling at non-zero column). Indexed twin of
    `dispatchStructural_none_flow` (legacy 3735). -/
lemma dispatchStructural_none_flow (s : ScannerStateIx input) (c : Char)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0) :
    scanNextTokenIx_dispatchStructural s c = .ok none := by
  unfold scanNextTokenIx_dispatchStructural
  have h_col_ne : (s.cursor.pos.col == 0) = false :=
    decide_eq_false (by omega)
  simp [pure, Pure.pure, Except.pure, h_flow, h_col_ne, show ¬(s.currentIndent ≥ (0 : Int)) from by omega, show ¬((s.cursor.pos.col : Int) ≤ s.currentIndent) from by omega]

/-- At initial state (`flowLevel = 0`, not at doc-start/end markers),
    structural dispatch returns `none` for any non-`%` character.
    Indexed twin of `dispatchStructural_none_bracket_init`
    (legacy 4066) / `_none_brace_init` (legacy 5425), generalised
    to any character — caller supplies the specialisation. -/
lemma dispatchStructural_none_non_directive (s : ScannerStateIx input) (c : Char)
    (h_fl : s.flowLevel = 0)
    (h_noDocStart : atDocumentStartIx s.cursor = false)
    (h_noDocEnd : atDocumentEndIx s.cursor = false)
    (h_not_pct : c ≠ '%') :
    scanNextTokenIx_dispatchStructural s c = .ok none := by
  unfold scanNextTokenIx_dispatchStructural
  have h_not_inflow : s.inFlow = false := by
    unfold ScannerStateIx.inFlow; rw [h_fl]; rfl
  have h_c_pct : (c == '%') = false := beq_eq_false_iff_ne.mpr h_not_pct
  simp [pure, Pure.pure, Except.pure, h_not_inflow, h_noDocStart, h_noDocEnd, h_c_pct]

/-- Specialisation for `'['` at initial state. -/
lemma dispatchStructural_none_bracket_init (s : ScannerStateIx input)
    (h_fl : s.flowLevel = 0)
    (h_noDocStart : atDocumentStartIx s.cursor = false)
    (h_noDocEnd : atDocumentEndIx s.cursor = false) :
    scanNextTokenIx_dispatchStructural s '[' = .ok none :=
  dispatchStructural_none_non_directive s '[' h_fl h_noDocStart h_noDocEnd (by decide)

/-- Specialisation for `'{'` at initial state. -/
lemma dispatchStructural_none_brace_init (s : ScannerStateIx input)
    (h_fl : s.flowLevel = 0)
    (h_noDocStart : atDocumentStartIx s.cursor = false)
    (h_noDocEnd : atDocumentEndIx s.cursor = false) :
    scanNextTokenIx_dispatchStructural s '{' = .ok none :=
  dispatchStructural_none_non_directive s '{' h_fl h_noDocStart h_noDocEnd (by decide)

/-! ## §2  `checkBlockFlowIndent` return-value lemmas -/

/-- In flow context, the indent guard is vacuous. -/
lemma checkBlockFlowIndent_ok_flow (s : ScannerStateIx input) (c : Char)
    (h_flow : s.inFlow = true) :
    scanNextTokenIx_checkBlockFlowIndent s c = .ok () := by
  unfold scanNextTokenIx_checkBlockFlowIndent
  simp only [h_flow, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- At initial state (`flowLevel = 0`, `currentIndent = -1`),
    `checkBlockFlowIndent` passes for `'['` (the indent guard fails
    because `-1 ≥ 0` is false). -/
lemma checkBlockFlowIndent_bracket_init (s : ScannerStateIx input)
    (h_fl : s.flowLevel = 0)
    (h_indent : s.currentIndent = -1) :
    scanNextTokenIx_checkBlockFlowIndent s '[' = .ok () := by
  unfold scanNextTokenIx_checkBlockFlowIndent
  have h_not_inflow : s.inFlow = false := by
    unfold ScannerStateIx.inFlow; rw [h_fl]; rfl
  have h_indent_neg : ¬ (s.currentIndent ≥ (0 : Int)) := by rw [h_indent]; decide
  simp only [h_not_inflow, Bool.not_false, Bool.true_and, h_indent_neg,
    decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- At initial state, `checkBlockFlowIndent` passes for `'{'`. -/
lemma checkBlockFlowIndent_brace_init (s : ScannerStateIx input)
    (h_fl : s.flowLevel = 0)
    (h_indent : s.currentIndent = -1) :
    scanNextTokenIx_checkBlockFlowIndent s '{' = .ok () := by
  unfold scanNextTokenIx_checkBlockFlowIndent
  have h_not_inflow : s.inFlow = false := by
    unfold ScannerStateIx.inFlow; rw [h_fl]; rfl
  have h_indent_neg : ¬ (s.currentIndent ≥ (0 : Int)) := by rw [h_indent]; decide
  simp only [h_not_inflow, Bool.not_false, Bool.true_and, h_indent_neg,
    decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- The indent guard fires only on `'['` / `'{'`; for `','` it passes. -/
lemma checkBlockFlowIndent_ok_comma (s : ScannerStateIx input) :
    scanNextTokenIx_checkBlockFlowIndent s ',' = .ok () := by
  unfold scanNextTokenIx_checkBlockFlowIndent
  simp only [show (',' == '[') = false from by decide,
    show (',' == '{') = false from by decide, Bool.or_self,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- The indent guard fires only on `'['` / `'{'`; for `']'` it passes. -/
lemma checkBlockFlowIndent_ok_close_bracket (s : ScannerStateIx input) :
    scanNextTokenIx_checkBlockFlowIndent s ']' = .ok () := by
  unfold scanNextTokenIx_checkBlockFlowIndent
  simp only [show (']' == '[') = false from by decide,
    show (']' == '{') = false from by decide, Bool.or_self,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- The indent guard fires only on `'['` / `'{'`; for `'}'` it passes. -/
lemma checkBlockFlowIndent_ok_close_brace (s : ScannerStateIx input) :
    scanNextTokenIx_checkBlockFlowIndent s '}' = .ok () := by
  unfold scanNextTokenIx_checkBlockFlowIndent
  simp only [show ('}' == '[') = false from by decide,
    show ('}' == '{') = false from by decide, Bool.or_self,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-! ## §3  `dispatchFlowIndicators` return-value lemmas -/

/-- For a character that is none of `[`, `]`, `{`, `}`, `,`, flow
    dispatch returns `none`. Indexed twin of
    `dispatchFlowIndicators_none` (legacy 3759). -/
lemma dispatchFlowIndicators_none (s : ScannerStateIx input) (c : Char)
    (h1 : c ≠ '[') (h2 : c ≠ ']') (h3 : c ≠ '{') (h4 : c ≠ '}') (h5 : c ≠ ',') :
    scanNextTokenIx_dispatchFlowIndicators s c = .ok none := by
  unfold scanNextTokenIx_dispatchFlowIndicators
  simp [pure, Pure.pure, Except.pure, beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h3, beq_eq_false_iff_ne.mpr h4, beq_eq_false_iff_ne.mpr h5]

/-- Flow dispatch for `'['` always returns
    `some (scanFlowSequenceStartIx s)`. -/
lemma dispatchFlowIndicators_bracket (s : ScannerStateIx input) :
    scanNextTokenIx_dispatchFlowIndicators s '[' =
      .ok (some (scanFlowSequenceStartIx s)) := by
  unfold scanNextTokenIx_dispatchFlowIndicators
  simp only [pure, Pure.pure, Except.pure,
    show ('[' == '[') = true from by decide, ↓reduceIte]

/-- Flow dispatch for `'{'` always returns
    `some (scanFlowMappingStartIx s)`. -/
lemma dispatchFlowIndicators_brace (s : ScannerStateIx input) :
    scanNextTokenIx_dispatchFlowIndicators s '{' =
      .ok (some (scanFlowMappingStartIx s)) := by
  unfold scanNextTokenIx_dispatchFlowIndicators
  simp only [pure, Pure.pure, Except.pure, show ('{' == '[') = false from by decide,     show ('{' == ']') = false from by decide, show ('{' == '{') = true from by decide, ↓reduceIte, Bool.false_eq_true]

/-- Flow dispatch for `']'` with `flowLevel > 0` returns
    `some (scanFlowSequenceEndIx s)`. The legacy split between
    `_close_bracket_nested` (flowLevel ≥ 2) and
    `_close_bracket_outermost` (flowLevel = 1, EOF) collapses
    because the indexed pipeline has no `validateFlowClose`
    tail-validation. -/
lemma dispatchFlowIndicators_close_bracket (s : ScannerStateIx input)
    (h_fl : s.flowLevel > 0) :
    scanNextTokenIx_dispatchFlowIndicators s ']' =
      .ok (some (scanFlowSequenceEndIx s)) := by
  unfold scanNextTokenIx_dispatchFlowIndicators
  have h_ne : (s.flowLevel == 0) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  simp only [pure, Pure.pure, Except.pure, show (']' == '[') = false from by decide,
    show (']' == ']') = true from by decide,
    h_ne, ↓reduceIte, Bool.false_eq_true]

/-- Flow dispatch for `'}'` with `flowLevel > 0` returns
    `some (scanFlowMappingEndIx s)`. -/
lemma dispatchFlowIndicators_close_brace (s : ScannerStateIx input)
    (h_fl : s.flowLevel > 0) :
    scanNextTokenIx_dispatchFlowIndicators s '}' =
      .ok (some (scanFlowMappingEndIx s)) := by
  unfold scanNextTokenIx_dispatchFlowIndicators
  have h_ne : (s.flowLevel == 0) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  simp only [pure, Pure.pure, Except.pure, show ('}' == '[') = false from by decide,     show ('}' == ']') = false from by decide, show ('}' == '{') = false from by decide, show ('}' == '}') = true from by decide, h_ne, ↓reduceIte, Bool.false_eq_true]

/-! ## §5  `scanFlowEntryIx_ok` (used by `_comma`) -/

/-- `scanFlowEntryIx` succeeds when the last real token is not a
    flow delimiter. Indexed twin of `scanFlowEntry_ok` (legacy 4398). -/
lemma scanFlowEntryIx_ok (s : ScannerStateIx input)
    (h_last : ∀ t, lastRealTokenValIx? s.tokens = some t →
      t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
      ∧ t ≠ YamlToken.flowEntry) :
    scanFlowEntryIx s =
      .ok { (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true } := by
  unfold scanFlowEntryIx
  simp only [bind, Except.bind]
  cases h_lrt : lastRealTokenValIx? s.tokens with
  | none => rfl
  | some t =>
    have ⟨h1, h2, h3⟩ := h_last t h_lrt
    have e1 : (t == YamlToken.flowSequenceStart) = false :=
      beq_eq_false_iff_ne.mpr h1
    have e2 : (t == YamlToken.flowMappingStart) = false :=
      beq_eq_false_iff_ne.mpr h2
    have e3 : (t == YamlToken.flowEntry) = false :=
      beq_eq_false_iff_ne.mpr h3
    simp only [e1, e2, e3, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

/-- Flow dispatch for `','` with `flowLevel > 0` and a non-flow-
    delimiter last token returns `some` of the comma-emit chain. -/
lemma dispatchFlowIndicators_comma (s : ScannerStateIx input)
    (h_fl : s.flowLevel > 0)
    (h_last : ∀ t, lastRealTokenValIx? s.tokens = some t →
      t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
      ∧ t ≠ YamlToken.flowEntry) :
    scanNextTokenIx_dispatchFlowIndicators s ',' =
      .ok (some { (s.emit YamlToken.flowEntry).advance with
                  simpleKeyAllowed := true }) := by
  unfold scanNextTokenIx_dispatchFlowIndicators
  have h_ne : (s.flowLevel == 0) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure,
    show (',' == '[') = false from by decide,
    show (',' == ']') = false from by decide,
    show (',' == '{') = false from by decide,
    show (',' == '}') = false from by decide,
    show (',' == ',') = true from by decide,
    h_ne, ↓reduceIte, Bool.false_eq_true]
  rw [scanFlowEntryIx_ok s h_last]

/-! ## §4  `dispatchBlockIndicators` return-value lemmas

Each returns `.ok none` because the character is neither `'-'` nor
`'?'` nor `':'`. -/

/-- Block dispatch returns `none` for `'"'`. -/
lemma dispatchBlockIndicators_none_quote (s : ScannerStateIx input) :
    scanNextTokenIx_dispatchBlockIndicators s '"' = .ok none := by
  unfold scanNextTokenIx_dispatchBlockIndicators
  simp only [pure, Pure.pure, Except.pure, show ('"' == '-') = false from by decide, show ('"' == '?') = false from by decide, show ('"' == ':') = false from by decide, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Block dispatch returns `none` for `','`. -/
lemma dispatchBlockIndicators_none_comma (s : ScannerStateIx input) :
    scanNextTokenIx_dispatchBlockIndicators s ',' = .ok none := by
  unfold scanNextTokenIx_dispatchBlockIndicators
  simp only [pure, Pure.pure, Except.pure, show (',' == '-') = false from by decide, show (',' == '?') = false from by decide, show (',' == ':') = false from by decide, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Block dispatch returns `none` for `']'`. -/
lemma dispatchBlockIndicators_none_close_bracket (s : ScannerStateIx input) :
    scanNextTokenIx_dispatchBlockIndicators s ']' = .ok none := by
  unfold scanNextTokenIx_dispatchBlockIndicators
  simp only [pure, Pure.pure, Except.pure, show (']' == '-') = false from by decide,
    show (']' == '?') = false from by decide,
    show (']' == ':') = false from by decide,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Block dispatch returns `none` for `'}'`. -/
lemma dispatchBlockIndicators_none_close_brace (s : ScannerStateIx input) :
    scanNextTokenIx_dispatchBlockIndicators s '}' = .ok none := by
  unfold scanNextTokenIx_dispatchBlockIndicators
  simp only [pure, Pure.pure, Except.pure, show ('}' == '-') = false from by decide, show ('}' == '?') = false from by decide, show ('}' == ':') = false from by decide, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-! ## §6  Pipeline composition

`scanNextTokenIx_via_flow_dispatch` already lives in
`Preserve/Step.lean`. Here we add the two siblings: content
dispatch (success and error) and block-indicator dispatch. -/

/-- When all four upstream stages (preprocess → struct → check →
    flow → block) yield `.ok none` and content dispatch produces a
    result, `scanNextTokenIx` returns that result.
    Indexed twin of `scanNextToken_via_content_dispatch` (legacy 3852). -/
lemma scanNextTokenIx_via_content_dispatch
    (s s_pp s_ad s_result : ScannerStateIx input) (c : Char)
    (h_pp : scanNextTokenIx_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextTokenIx_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_check : scanNextTokenIx_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextTokenIx_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextTokenIx_dispatchBlockIndicators s_ad c = .ok none)
    (h_content : scanNextTokenIx_dispatchContent s_ad c = .ok s_result)
    (h_ndp : s_pp.directivesPresent = false) :
    scanNextTokenIx s = .ok (some s_result) := by
  unfold scanNextTokenIx
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_pp]; dsimp only []
  rw [h_struct]; dsimp only []
  rw [scanNextTokenIx_checkNoPendingDirectives_ok _ h_ndp]; dsimp only []
  rw [← h_ad_eq]
  rw [h_check]; dsimp only []
  rw [h_flow]; dsimp only []
  rw [h_block]; dsimp only []
  rw [h_content]

/-- Error variant: when content dispatch errors, `scanNextTokenIx`
    propagates that error. Indexed twin of
    `scanNextToken_via_content_dispatch_error` (legacy 3869). -/
lemma scanNextTokenIx_via_content_dispatch_error
    (s s_pp s_ad : ScannerStateIx input) (c : Char) (e : ScanError)
    (h_pp : scanNextTokenIx_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextTokenIx_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_check : scanNextTokenIx_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextTokenIx_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextTokenIx_dispatchBlockIndicators s_ad c = .ok none)
    (h_content : scanNextTokenIx_dispatchContent s_ad c = .error e)
    (h_ndp : s_pp.directivesPresent = false) :
    scanNextTokenIx s = .error e := by
  unfold scanNextTokenIx
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_pp]; dsimp only []
  rw [h_struct]; dsimp only []
  rw [scanNextTokenIx_checkNoPendingDirectives_ok _ h_ndp]; dsimp only []
  rw [← h_ad_eq]
  rw [h_check]; dsimp only []
  rw [h_flow]; dsimp only []
  rw [h_block]; dsimp only []
  rw [h_content]

/-- When structural/flow dispatches yield `.ok none` and block-
    indicator dispatch produces a result, `scanNextTokenIx` returns
    that result. Used for `:` (value indicator) in flow context.
    Indexed twin of `scanNextToken_via_block_dispatch` (legacy 3889). -/
lemma scanNextTokenIx_via_block_dispatch
    (s s_pp s_ad s_result : ScannerStateIx input) (c : Char)
    (h_pp : scanNextTokenIx_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextTokenIx_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_check : scanNextTokenIx_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextTokenIx_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextTokenIx_dispatchBlockIndicators s_ad c = .ok (some s_result))
    (h_ndp : s_pp.directivesPresent = false) :
    scanNextTokenIx s = .ok (some s_result) := by
  unfold scanNextTokenIx
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure]
  rw [h_pp]; dsimp only []
  rw [h_struct]; dsimp only []
  rw [scanNextTokenIx_checkNoPendingDirectives_ok _ h_ndp]; dsimp only []
  rw [← h_ad_eq]
  rw [h_check]; dsimp only []
  rw [h_flow]; dsimp only []
  rw [h_block]

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
