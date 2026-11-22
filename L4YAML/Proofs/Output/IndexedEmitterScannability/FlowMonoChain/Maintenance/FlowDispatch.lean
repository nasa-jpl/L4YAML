/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Preserve.Helpers

@[expose] public section Blanket

/-! # `FlowMonoChain.Maintenance.FlowDispatch` — Phase 3 Step 6f.3b3.flowmono.maintenance.flowdispatch

**Sub-session 1 of `.flowmono.maintenance`** (~700 legacy LOC contribution
before substrate elimination).
Per-flow-dispatcher state-field preservation, `flowLevel` change
lemmas, and `lastRealTokenValIx?` push helpers.

## Indexed simplification

The legacy `.maintenance` machinery weaves together two unrelated
concerns: (a) **per-flow-dispatcher field preservation** — twenty
legacy theorems of the form `scanFlow{Sequence,Mapping}{Start,End}_
preserves_{dp,indents,ek,line,flowLevel}` plus their `scanFlowEntry`
analogs, each requiring an `unfold; simp only [advance_*, emit_*,
ScannerState.emit]` step — and (b) **pipeline dispatch composition**
— the `scanNextToken_via_{content,block}_dispatch` family that
threads `scanNextToken_preprocess` → `dispatchStructural` →
`allowDirectives` → `dispatchFlowIndicators`
→ `dispatchBlockIndicators` → `dispatchContent` for specific
scenarios. We split these into two files so each stays tight:

  - This file (`FlowDispatch.lean`) bundles concern (a).
  - The sibling `Pipeline.lean` bundles concern (b).

On the indexed substrate, concern (a) collapses dramatically: each
`scanFlow{Sequence,Mapping}{Start,End}Ix` and `scanFlowEntryIx` is a
single `let s := s.emit tok; let s := s.advance; { s with ... }`
chain whose final record update touches only `flowLevel` /
`flowStack` / `simpleKeyStack` / `simpleKey` / `simpleKeyAllowed`.
The "preserved" fields are *all other fields*: `directivesPresent`,
`indents`, `explicitKeyLine`, `allowDirectives`, `needIndentCheck`.
Each preservation reduces to one `rfl` (the entire chain unfolds
through nested record updates that never mention the field). Five
fields × five dispatchers = 25 lemmas, all `unfold; rfl`-shape.

Plus the `flowLevel` change lemmas (`+1` for Start dispatchers,
`-1` for End dispatchers, `0` for `scanFlowEntryIx`) — Start
variants ship here; End variants already live in
[`FlowMonoChain/Basic.lean`](FlowMonoChain/Basic.lean) (consumed by
`scanNextTokenIx_dispatchFlowIndicators_maintains_SKAFIx`);
`scanFlowEntryIx_preserves_flowLevel` already lives in
[`FlowMonoChain/Preserve/Step.lean`](FlowMonoChain/Preserve/Step.lean).

## Scope

  - **§1** — `scanFlowSequenceStartIx` state-field preservation
    (5 fields) + `flowLevel_eq`.
  - **§2** — `scanFlowMappingStartIx` state-field preservation
    (5 fields) + `flowLevel_eq`.
  - **§3** — `scanFlowSequenceEndIx` state-field preservation
    (5 fields). `flowLevel_eq` already in `Basic.lean`.
  - **§4** — `scanFlowMappingEndIx` state-field preservation
    (5 fields). `flowLevel_eq` already in `Basic.lean`.
  - **§5** — `scanFlowEntryIx` state-field preservation (5 fields,
    `Except`-form). `flowLevel` already in `Preserve/Step.lean`.
  - **§6** — `lastRealTokenValIx_push_*` helpers
    (non-placeholder and two-placeholder push cases).
  - **§7** — `saveSimpleKeyIx_preserves_lastRealTokenValIx_ne_flow`:
    `saveSimpleKeyIx` preserves the "no trailing flow delimiter"
    property of `lastRealTokenValIx?`.

## Legacy mapping

  | Section | Indexed counterpart |
  | ------- | ------------------- |
  | §1      | `scanFlowSequenceStartIx_*`   |
  | §2      | `scanFlowMappingStartIx_*`    |
  | §3      | `scanFlowSequenceEndIx_*`     |
  | §4      | `scanFlowMappingEndIx_*`      |
  | §5      | `scanFlowEntryIx_*` (legacy did not collate per-field) |
  | §6      | `lastRealTokenValIx_push_*`   |
  | §7      | `saveSimpleKeyIx_preserves_lastRealTokenValIx_ne_flow` |

## Deferred to `.maintenance.pipeline`

The dispatch return-value lemmas (`dispatchStructural_none_*`,
`dispatchFlowIndicators_*`,
`dispatchBlockIndicators_none_*`) and pipeline composition
(`scanNextTokenIx_via_{content,block}_dispatch[_error]`) ship in the
sibling `Pipeline.lean` file.

## Deferred to `.sync`

Detail lemmas built on `ScannerSurfCorr` (`scanFlowSequenceStart_
detail`, `scanFlowSequenceEnd_detail`, `scanFlowMappingStart_detail`,
`scanFlowMappingEnd_detail`, `scanFlowEntry_detail`, `scanFlowEntry_ok`,
`scanNextToken_flow_*` scenario chains) defer until the indexed
surface-correspondence bridge is built in `.sync`.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx

variable {input : String}

/-! ## §1  `scanFlowSequenceStartIx` field preservation -/

@[simp] lemma scanFlowSequenceStartIx_directivesPresent (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).directivesPresent = s.directivesPresent := by
  unfold scanFlowSequenceStartIx; rfl

@[simp] lemma scanFlowSequenceStartIx_indents (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).indents = s.indents := by
  unfold scanFlowSequenceStartIx; rfl

@[simp] lemma scanFlowSequenceStartIx_explicitKeyLine (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).explicitKeyLine = none := by
  unfold scanFlowSequenceStartIx; rfl

@[simp] lemma scanFlowSequenceStartIx_allowDirectives (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).allowDirectives = s.allowDirectives := by
  unfold scanFlowSequenceStartIx; rfl

@[simp] lemma scanFlowSequenceStartIx_needIndentCheck (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).needIndentCheck = s.needIndentCheck := by
  unfold scanFlowSequenceStartIx; rfl

lemma scanFlowSequenceStartIx_flowLevel_eq (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).flowLevel = s.flowLevel + 1 := by
  unfold scanFlowSequenceStartIx
  simp only [advance_flowLevel, emit_flowLevel]

/-! ## §2  `scanFlowMappingStartIx` field preservation -/

@[simp] lemma scanFlowMappingStartIx_directivesPresent (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).directivesPresent = s.directivesPresent := by
  unfold scanFlowMappingStartIx; rfl

@[simp] lemma scanFlowMappingStartIx_indents (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).indents = s.indents := by
  unfold scanFlowMappingStartIx; rfl

@[simp] lemma scanFlowMappingStartIx_explicitKeyLine (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).explicitKeyLine = none := by
  unfold scanFlowMappingStartIx; rfl

@[simp] lemma scanFlowMappingStartIx_allowDirectives (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).allowDirectives = s.allowDirectives := by
  unfold scanFlowMappingStartIx; rfl

@[simp] lemma scanFlowMappingStartIx_needIndentCheck (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).needIndentCheck = s.needIndentCheck := by
  unfold scanFlowMappingStartIx; rfl

lemma scanFlowMappingStartIx_flowLevel_eq (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).flowLevel = s.flowLevel + 1 := by
  unfold scanFlowMappingStartIx
  simp only [advance_flowLevel, emit_flowLevel]

/-! ## §3  `scanFlowSequenceEndIx` field preservation

`flowLevel_eq` (`.flowLevel = s.flowLevel - 1`) already lives in
`FlowMonoChain.Basic` (used by the FlowIndicators SKAF dispatcher). -/

@[simp] lemma scanFlowSequenceEndIx_directivesPresent (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).directivesPresent = s.directivesPresent := by
  unfold scanFlowSequenceEndIx; rfl

@[simp] lemma scanFlowSequenceEndIx_indents (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).indents = s.indents := by
  unfold scanFlowSequenceEndIx; rfl

@[simp] lemma scanFlowSequenceEndIx_explicitKeyLine (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).explicitKeyLine = (s.explicitKeyStack.back?.getD (none, -1)).1 := by
  unfold scanFlowSequenceEndIx; rfl

@[simp] lemma scanFlowSequenceEndIx_allowDirectives (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).allowDirectives = s.allowDirectives := by
  unfold scanFlowSequenceEndIx; rfl

@[simp] lemma scanFlowSequenceEndIx_needIndentCheck (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).needIndentCheck = false := by
  unfold scanFlowSequenceEndIx; rfl

/-! ## §4  `scanFlowMappingEndIx` field preservation -/

@[simp] lemma scanFlowMappingEndIx_directivesPresent (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).directivesPresent = s.directivesPresent := by
  unfold scanFlowMappingEndIx; rfl

@[simp] lemma scanFlowMappingEndIx_indents (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).indents = s.indents := by
  unfold scanFlowMappingEndIx; rfl

@[simp] lemma scanFlowMappingEndIx_explicitKeyLine (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).explicitKeyLine = (s.explicitKeyStack.back?.getD (none, -1)).1 := by
  unfold scanFlowMappingEndIx; rfl

@[simp] lemma scanFlowMappingEndIx_allowDirectives (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).allowDirectives = s.allowDirectives := by
  unfold scanFlowMappingEndIx; rfl

@[simp] lemma scanFlowMappingEndIx_needIndentCheck (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).needIndentCheck = false := by
  unfold scanFlowMappingEndIx; rfl

/-! ## §5  `scanFlowEntryIx` field preservation (`Except`-form)

`scanFlowEntryIx` has an `Except` shape with a guard for trailing
`,`/`[`/`{` (`invalidFlowEntry` error). The success branch is the
`emit .flowEntry |>.advance |> { _ with simpleKeyAllowed := true }`
chain; the field-preservation lemmas factor through `repeat split`
to peel the guard. -/

lemma scanFlowEntryIx_preserves_directivesPresent
    (s s' : ScannerStateIx input) (h : scanFlowEntryIx s = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals rfl

lemma scanFlowEntryIx_preserves_indents
    (s s' : ScannerStateIx input) (h : scanFlowEntryIx s = .ok s') :
    s'.indents = s.indents := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals rfl

/-- The `,` CLEARS the explicit-key line (item 9l): `[150] ns-flow-pair`'s
    explicit alternative is one entry, and the `,` starts the next one. -/
lemma scanFlowEntryIx_clears_explicitKeyLine
    (s s' : ScannerStateIx input) (h : scanFlowEntryIx s = .ok s') :
    s'.explicitKeyLine = none := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals rfl

lemma scanFlowEntryIx_preserves_allowDirectives
    (s s' : ScannerStateIx input) (h : scanFlowEntryIx s = .ok s') :
    s'.allowDirectives = s.allowDirectives := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals rfl

lemma scanFlowEntryIx_preserves_needIndentCheck
    (s s' : ScannerStateIx input) (h : scanFlowEntryIx s = .ok s') :
    s'.needIndentCheck = s.needIndentCheck := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals rfl

/-! ## §6  `lastRealTokenValIx_push_*` helpers

`lastRealTokenValIx?` skips up to two trailing `.placeholder` slots
before reporting the last real token value. Two push patterns matter
for `.maintenance` consumers:

  - **Push of a non-`.placeholder` token** — last real token equals
    that token.
  - **Push of two `.placeholder` tokens** — last real token either
    equals the pre-push last real token (when the original stream
    has size > 0) or equals `.placeholder` (when the original is
    empty). -/

/-- After pushing a non-`.placeholder` token onto a token stream,
    `lastRealTokenValIx?` returns the pushed token's value.

    Indexed twin of legacy `lastRealTokenVal_push_non_ph`. -/
lemma lastRealTokenValIx_push_non_ph
    (ts : Indexed.TokenStream input)
    (t : IxToken input) (h_nph : t.token ≠ YamlToken.placeholder) :
    lastRealTokenValIx? (ts.push t) = some t.token := by
  unfold lastRealTokenValIx?
  show (let arr := (ts.push t).tokens
    if arr.size > 0 then
      let lastIdx := arr.size - 1
      let tok1 := arr[lastIdx]!.token
      if tok1 == YamlToken.placeholder && lastIdx > 0 then
        let tok2 := arr[lastIdx - 1]!.token
        if tok2 == YamlToken.placeholder && lastIdx > 1 then
          some arr[lastIdx - 2]!.token
        else some tok2
      else some tok1
    else none) = some t.token
  simp only [Indexed.TokenStream.push, Array.size_push,
    show ts.tokens.size + 1 > 0 from by omega, ↓reduceIte,
    show ts.tokens.size + 1 - 1 = ts.tokens.size from by omega]
  rw [getElem!_pos _ _ (by simp [Array.size_push])]
  simp only [Array.getElem_push_eq]
  have h_eq_false : (t.token == YamlToken.placeholder) = false :=
    beq_eq_false_iff_ne.mpr h_nph
  simp only [h_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- After pushing two `.placeholder` tokens onto a token stream,
    `lastRealTokenValIx?` either reports the pre-push last real
    token or reports `.placeholder` (when the original stream was
    empty or had only one slot).

    Indexed twin of legacy `lastRealTokenVal_push_two_ph`. -/
lemma lastRealTokenValIx_push_two_ph
    (ts : Indexed.TokenStream input)
    (ph1 ph2 : IxToken input)
    (h1 : ph1.token = YamlToken.placeholder)
    (h2 : ph2.token = YamlToken.placeholder)
    (t : YamlToken)
    (ht : lastRealTokenValIx? ((ts.push ph1).push ph2) = some t) :
    lastRealTokenValIx? ts = some t ∨ t = YamlToken.placeholder := by
  unfold lastRealTokenValIx? at ht
  simp only [Indexed.TokenStream.push, Array.size_push] at ht
  simp only [show ts.tokens.size + 1 + 1 > 0 from by omega, ↓reduceIte,
    show ts.tokens.size + 1 + 1 - 1 = ts.tokens.size + 1 from by omega] at ht
  -- tok1 = arr[ts.size + 1]!.token = ph2.token = .placeholder
  have h_elem1 : ((ts.tokens.push ph1).push ph2)[ts.tokens.size + 1]!.token
      = YamlToken.placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.getElem_push, Array.size_push, h2]
  simp only [h_elem1,
    show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
    Bool.true_and, show ts.tokens.size + 1 > 0 from by omega,
    show ts.tokens.size + 1 - 1 = ts.tokens.size from by omega] at ht
  -- tok2 = arr[ts.size]!.token = ph1.token = .placeholder
  have h_elem2 : ((ts.tokens.push ph1).push ph2)[ts.tokens.size]!.token
      = YamlToken.placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push]; omega)]
    simp [Array.getElem_push, Array.size_push, h1]
  by_cases h_gt : ts.tokens.size > 0
  · -- Original stream has tokens → arr[ts.size - 1] equals original last
    have h_elem3 : ((ts.tokens.push ph1).push ph2)[ts.tokens.size - 1]!.token
        = ts.tokens[ts.tokens.size - 1]!.token := by
      rw [getElem!_pos _ _ (by simp [Array.size_push]; omega),
          getElem!_pos _ _ (by omega)]
      simp only [Array.getElem_push,
        show ts.tokens.size - 1 < (ts.tokens.push ph1).size from by
          simp [Array.size_push]; omega,
        show ts.tokens.size - 1 < ts.tokens.size from by omega, dite_true]
    simp only [h_elem2,
      show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show ts.tokens.size + 1 > 1 from by omega,
      show ts.tokens.size + 1 - 2 = ts.tokens.size - 1 from by omega,
      h_elem3] at ht
    injection ht with ht_val
    by_cases h_ne : t = YamlToken.placeholder
    · exact .inr h_ne
    · left; unfold lastRealTokenValIx?
      show (let arr := ts.tokens
        if arr.size > 0 then
          let lastIdx := arr.size - 1
          let tok1 := arr[lastIdx]!.token
          if tok1 == YamlToken.placeholder && lastIdx > 0 then
            let tok2 := arr[lastIdx - 1]!.token
            if tok2 == YamlToken.placeholder && lastIdx > 1 then
              some arr[lastIdx - 2]!.token
            else some tok2
          else some tok1
        else none) = some t
      simp only [h_gt, ↓reduceIte, ht_val,
        show (t == YamlToken.placeholder) = false from
          beq_eq_false_iff_ne.mpr h_ne, Bool.false_and, Bool.false_eq_true]
  · -- Original stream is empty → arr[ts.size - 1]? is out of bounds;
    -- the inner `tok2 > 1` test fails (`ts.size + 1 = 1 > 1` is false)
    simp only [h_elem2,
      show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show ¬(ts.tokens.size + 1 > 1) from by omega] at ht
    injection ht with ht_val; exact .inr ht_val.symm

/-! ## §7  `saveSimpleKeyIx` preserves "no trailing flow delimiter"

`saveSimpleKeyIx` either leaves the token stream untouched
(`saveSimpleKeyIx_tokens_cases` identity branch) or pushes exactly
two `.placeholder` tokens (`twoPlaceholderEmits` branch). The
"no trailing flow delimiter" property of `lastRealTokenValIx?`
carries through both cases by §6. -/

lemma saveSimpleKeyIx_preserves_lastRealTokenValIx_ne_flow
    (s : ScannerStateIx input)
    (h_last : ∀ t, lastRealTokenValIx? s.tokens = some t →
      t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
      ∧ t ≠ YamlToken.flowEntry)
    (t : YamlToken)
    (ht : lastRealTokenValIx? (saveSimpleKeyIx s).tokens = some t) :
    t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
      ∧ t ≠ YamlToken.flowEntry := by
  rcases L4YAML.Proofs.Indexed.ScannerPlainScalarValid.saveSimpleKeyIx_tokens_cases s
    with h_id | h_two
  · rw [h_id] at ht; exact h_last t ht
  · rw [h_two] at ht
    -- twoPlaceholderEmits s = (s.emit placeholder).emit placeholder
    -- so its tokens is (s.tokens.push ph1).push ph2 with both placeholders
    show t ≠ _ ∧ t ≠ _ ∧ t ≠ _
    have h_unfold : (L4YAML.Proofs.Indexed.ScannerPlainScalarValid.twoPlaceholderEmits s).tokens
        = (s.tokens.push
            (IxToken.mk' (input := input) s.cursor.pos YamlToken.placeholder s.cursor.pos
              (Nat.le_refl _) s.cursor.posBound)).push
            (IxToken.mk' (input := input) s.cursor.pos YamlToken.placeholder s.cursor.pos
              (Nat.le_refl _) s.cursor.posBound) := by
      show ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens = _
      rfl
    rw [h_unfold] at ht
    have h_or := lastRealTokenValIx_push_two_ph s.tokens
      (IxToken.mk' (input := input) s.cursor.pos YamlToken.placeholder s.cursor.pos
        (Nat.le_refl _) s.cursor.posBound)
      (IxToken.mk' (input := input) s.cursor.pos YamlToken.placeholder s.cursor.pos
        (Nat.le_refl _) s.cursor.posBound)
      rfl rfl t ht
    cases h_or with
    | inl h => exact h_last t h
    | inr h => subst h; exact ⟨by decide, by decide, by decide⟩

/-! ## §8  `scanFlow{Sequence,Mapping}StartIx` last-real-token facts

Used by the flow-opener step lemmas (Fix A) to re-establish the
`completesFlowValue = false` invariant after opening a flow collection:
the newly-emitted `.flow{Sequence,Mapping}Start` is the last real token,
and it does not complete a flow value.  Indexed twins of
`scanFlow{Sequence,Mapping}Start_lastRealTokenVal` (ScanSteps). -/

/-- After `scanFlowSequenceStartIx`, the last real token is
    `.flowSequenceStart`. -/
lemma scanFlowSequenceStartIx_lastRealTokenVal (s : ScannerStateIx input) :
    lastRealTokenValIx? (scanFlowSequenceStartIx s).tokens
      = some YamlToken.flowSequenceStart := by
  have h : (scanFlowSequenceStartIx s).tokens = s.tokens.push
      (IxToken.mk' (input := input) s.cursor.pos YamlToken.flowSequenceStart
        s.cursor.pos (Nat.le_refl _) s.cursor.posBound) := rfl
  rw [h]
  exact lastRealTokenValIx_push_non_ph s.tokens
    (IxToken.mk' (input := input) s.cursor.pos YamlToken.flowSequenceStart
      s.cursor.pos (Nat.le_refl _) s.cursor.posBound)
    (show YamlToken.flowSequenceStart ≠ YamlToken.placeholder by decide)

/-- After `scanFlowMappingStartIx`, the last real token is
    `.flowMappingStart`. -/
lemma scanFlowMappingStartIx_lastRealTokenVal (s : ScannerStateIx input) :
    lastRealTokenValIx? (scanFlowMappingStartIx s).tokens
      = some YamlToken.flowMappingStart := by
  have h : (scanFlowMappingStartIx s).tokens = s.tokens.push
      (IxToken.mk' (input := input) s.cursor.pos YamlToken.flowMappingStart
        s.cursor.pos (Nat.le_refl _) s.cursor.posBound) := rfl
  rw [h]
  exact lastRealTokenValIx_push_non_ph s.tokens
    (IxToken.mk' (input := input) s.cursor.pos YamlToken.flowMappingStart
      s.cursor.pos (Nat.le_refl _) s.cursor.posBound)
    (show YamlToken.flowMappingStart ≠ YamlToken.placeholder by decide)

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

end Blanket
