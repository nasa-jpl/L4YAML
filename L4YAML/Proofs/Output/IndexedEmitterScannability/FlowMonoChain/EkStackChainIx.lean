/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Preserve.Step
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Maintenance.Pipeline
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKeyIx

@[expose] public section Blanket

/-! # FlowStackChainIx — `explicitKeyStack` moves in lockstep with `flowLevel` (indexed)

Indexed mirror of `Proofs/Output/EmitterScannability/FlowStackChain.lean`.
`ScannerStateIx.explicitKeyStack` is written only by the four flow-collection
functions (`scanFlowSequenceStartIx`/`scanFlowMappingStartIx` push a kind
marker and increment `flowLevel`; `scanFlowSequenceEndIx`/
`scanFlowMappingEndIx` pop it and decrement `flowLevel`).  Every other
scanner function copies the field through record updates.  This file makes
that lockstep precise across a full `scanNextTokenIx` step and lifts it to
balanced scan chains:

* **§1** — `explicitKeyStack` preservation suite for every scanner leaf reached by
  `scanNextTokenIx` outside the four flow open/close functions.  Mechanical
  clones of the `_preserves_simpleKeyStack` suite in
  `Production/IndexedScannerPlainScalarValid.lean` §12: the originals are
  field-agnostic structural walks, so the same scripts prove the
  `explicitKeyStack` twins verbatim.
* **§2** — flow open/close `explicitKeyStack` component facts + preprocess /
  per-dispatcher preservation.
* **§3** — `scanNextTokenIx_dispatchFlowIndicators_ekStack_step`: the
  5-arm fact for the flow-indicator dispatcher (preserve / push `true` /
  push `false` / pop) — includes the 9a kind-check throw arms.
* **§4** — `scanNextTokenIx_ekStack_step`: the per-step trichotomy — one
  scanner step either preserves `explicitKeyStack` (and `flowLevel`), pushes one
  kind marker (incrementing `flowLevel`), or pops one (decrementing it).
* **§5** — `FlowMonoChainIx.ekStack_invariant` /
  `FlowMonoChainIx.ekStack_eq`: a balanced scan chain never disturbs the
  `explicitKeyStack` entries below the floor; a chain that starts and ends at the
  floor preserves `explicitKeyStack` exactly.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML.Proofs.CloseStaleExplicitKeyIx

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid
open L4YAML.Proofs.Indexed.ScannerCorrectness
open L4YAML.Proofs.FlowAdjacencyIx

variable {input : String}

/-! ## §1  `explicitKeyStack` preservation suite (scanner leaves)

Clones of the `_preserves_simpleKeyStack` suite in
`Production/IndexedScannerPlainScalarValid.lean` §12 with
`simpleKeyStack` renamed to `explicitKeyStack`: the original proofs are
field-agnostic structural walks, so they transfer verbatim.
(`saveSimpleKeyIx_explicitKeyStack` already lives in `Preserve/Helpers.lean`.) -/

@[simp] lemma advance_explicitKeyStack (s : ScannerStateIx input) :
    s.advance.explicitKeyStack = s.explicitKeyStack := rfl

@[simp] lemma advanceN_explicitKeyStack (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).explicitKeyStack = s.explicitKeyStack := rfl

@[simp] lemma emit_explicitKeyStack (s : ScannerStateIx input) (tok : YamlToken) :
    (s.emit tok).explicitKeyStack = s.explicitKeyStack := rfl

@[simp] lemma emitAt_explicitKeyStack (s : ScannerStateIx input) (startPos : YamlPos)
    (tok : YamlToken) (h : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok h).explicitKeyStack = s.explicitKeyStack := rfl

@[simp] lemma overwriteAtCursor_explicitKeyStack (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken) :
    (s.overwriteAtCursor i sk tok).explicitKeyStack = s.explicitKeyStack := rfl

@[simp] lemma skipToContentS_explicitKeyStack (s : ScannerStateIx input) :
    s.skipToContentS.explicitKeyStack = s.explicitKeyStack := by
  unfold ScannerStateIx.skipToContentS
  dsimp only
  split <;> rfl

lemma unwindIndentsLoopIx_explicitKeyStack (s : ScannerStateIx input)
    (col : Int) (fuel : Nat) :
    (unwindIndentsLoopIx s col fuel).explicitKeyStack = s.explicitKeyStack := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold unwindIndentsLoopIx
    split
    · exact ih _
    · rfl

lemma unwindIndentsIx_explicitKeyStack (s : ScannerStateIx input) (col : Int) :
    (unwindIndentsIx s col).explicitKeyStack = s.explicitKeyStack :=
  unwindIndentsLoopIx_explicitKeyStack s col _

lemma pushSequenceIndentIx_preserves_explicitKeyStack
    (s : ScannerStateIx input) (col : Int) :
    (pushSequenceIndentIx s col).explicitKeyStack = s.explicitKeyStack := by
  unfold pushSequenceIndentIx; split <;> rfl

lemma pushMappingIndentIx_preserves_explicitKeyStack
    (s : ScannerStateIx input) (col : Int) :
    (pushMappingIndentIx s col).explicitKeyStack = s.explicitKeyStack := by
  unfold pushMappingIndentIx; split <;> rfl

lemma scanDocumentStartIx_preserves_explicitKeyStack (s : ScannerStateIx input) :
    (scanDocumentStartIx s).explicitKeyStack = s.explicitKeyStack := by
  unfold scanDocumentStartIx
  show (unwindIndentsIx s (-1)).explicitKeyStack = s.explicitKeyStack
  exact unwindIndentsIx_explicitKeyStack s (-1)

lemma scanDocumentEndIx_preserves_explicitKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanDocumentEndIx s = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanDocumentEndIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    show (unwindIndentsIx s (-1)).explicitKeyStack = s.explicitKeyStack
  all_goals exact unwindIndentsIx_explicitKeyStack s (-1)

lemma scanYamlDirectiveIx_preserves_explicitKeyStack {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input)
    (startPos : YamlPos) (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanYamlDirectiveIx at h
  simp only [bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)

lemma scanTagDirectiveIx_preserves_explicitKeyStack {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input)
    (startPos : YamlPos) (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanTagDirectiveIx at h
  simp only [bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)

lemma scanDirectiveIx_preserves_explicitKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanDirectiveIx s = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanDirectiveIx at h
  split at h
  · simp at h
  · dsimp only [] at h
    split at h
    · split at h
      · rename_i s_sub h_sub
        simp only [Except.ok.injEq] at h; subst h
        exact (scanYamlDirectiveIx_preserves_explicitKeyStack _ _ _ _ _ h_sub).trans rfl
      · simp at h
    · split at h
      · split at h
        · rename_i s_sub h_sub
          simp only [Except.ok.injEq] at h; subst h
          exact (scanTagDirectiveIx_preserves_explicitKeyStack _ _ _ _ _ h_sub).trans rfl
        · simp at h
      · simp only [Except.ok.injEq] at h; subst h; rfl

lemma scanBlockEntryIx_preserves_explicitKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanBlockEntryIx s = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanBlockEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    first
    | exact pushSequenceIndentIx_preserves_explicitKeyStack s s.cursor.pos.col
    | rfl

lemma scanKeyIx_preserves_explicitKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanKeyIx s = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanKeyIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    first
    | exact pushMappingIndentIx_preserves_explicitKeyStack s s.cursor.pos.col
    | rfl

lemma scanValueClearKeyIx_preserves_explicitKeyStack (s : ScannerStateIx input) :
    (scanValueClearKeyIx s).explicitKeyStack = s.explicitKeyStack := by
  unfold scanValueClearKeyIx
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

lemma scanValuePrepareIx_preserves_explicitKeyStack (s : ScannerStateIx input) :
    (scanValuePrepareIx s).explicitKeyStack = s.explicitKeyStack := by
  unfold scanValuePrepareIx
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · exact pushMappingIndentIx_preserves_explicitKeyStack s s.cursor.pos.col
      · rfl

lemma scanValueIx_preserves_explicitKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanValueIx s = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanValueIx at h
  simp only [bind, Except.bind] at h
  -- Three guards since item 31: validate, indent-tab check, tab check
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  show ((scanValuePrepareIx (scanValueClearKeyIx s)).emit
        YamlToken.value).advance.explicitKeyStack = s.explicitKeyStack
  rw [advance_explicitKeyStack, emit_explicitKeyStack,
      scanValuePrepareIx_preserves_explicitKeyStack,
      scanValueClearKeyIx_preserves_explicitKeyStack]

lemma scanAnchorOrAliasIx_preserves_explicitKeyStack {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanAnchorOrAliasIx at h
  dsimp only [] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h; subst h; rfl

lemma scanTagIx_preserves_explicitKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanTagIx s = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanTagIx at h
  dsimp only [] at h
  split at h
  · -- '<' verbatim tag branch
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h; subst h; rfl
  · -- '!' secondary tag branch
    simp only [Except.ok.injEq] at h; subst h; rfl
  · -- default branch
    simp only [Except.ok.injEq] at h; subst h; rfl

lemma scanFlowEntryIx_preserves_explicitKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanFlowEntryIx s = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_explicitKeyStack, emit_explicitKeyStack]

/-! ## §2  Flow open/close component facts + preprocess / dispatchers -/

/-- `scanFlowSequenceStartIx` pushes `true` (a sequence marker). -/
lemma scanFlowSequenceStartIx_explicitKeyStack (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).explicitKeyStack
      = s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol) := by
  unfold scanFlowSequenceStartIx; rfl

/-- `scanFlowMappingStartIx` pushes `false` (a mapping marker). -/
lemma scanFlowMappingStartIx_explicitKeyStack (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).explicitKeyStack
      = s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol) := by
  unfold scanFlowMappingStartIx; rfl

/-- `scanFlowSequenceEndIx` pops `explicitKeyStack`. -/
lemma scanFlowSequenceEndIx_explicitKeyStack (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).explicitKeyStack = s.explicitKeyStack.pop := by
  unfold scanFlowSequenceEndIx; rfl

/-- `scanFlowMappingEndIx` pops `explicitKeyStack`. -/
lemma scanFlowMappingEndIx_explicitKeyStack (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).explicitKeyStack = s.explicitKeyStack.pop := by
  unfold scanFlowMappingEndIx; rfl

/-- `scanNextTokenIx_preprocess` preserves `explicitKeyStack`. Clone of
    `scanNextTokenIx_preprocess_preserves_simpleKeyStack` (Basic §2.2). -/
lemma scanNextTokenIx_preprocess_preserves_explicitKeyStack {input : String}
    (s s1 : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_preprocess s = .ok (some (s1, c))) :
    s1.explicitKeyStack = s.explicitKeyStack := by
  unfold scanNextTokenIx_preprocess at h
  dsimp only at h
  have h_skip := skipToContentS_explicitKeyStack s
  -- Peel the §6.1/§6.6 strictness-walker guard (item 7).
  split at h
  · simp at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          rw [closeStaleExplicitKeyIx_explicitKeyStack, saveSimpleKeyIx_explicitKeyStack]
          show (unwindIndentsIx _ _).explicitKeyStack = s.explicitKeyStack
          rw [unwindIndentsIx_explicitKeyStack, h_skip]
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          rw [closeStaleExplicitKeyIx_explicitKeyStack, saveSimpleKeyIx_explicitKeyStack, h_skip]

lemma scanNextTokenIx_dispatchStructural_preserves_explicitKeyStack
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    s'.explicitKeyStack = s.explicitKeyStack := by
  rcases scanNextTokenIx_dispatchStructural_ok_some_cases h with heq | hOk | hOk
  · subst heq; exact scanDocumentStartIx_preserves_explicitKeyStack s
  · exact scanDocumentEndIx_preserves_explicitKeyStack s _ hOk
  · exact scanDirectiveIx_preserves_explicitKeyStack s _ hOk

lemma scanNextTokenIx_dispatchBlockIndicators_preserves_explicitKeyStack
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    s'.explicitKeyStack = s.explicitKeyStack := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h with hOk | hOk | hOk
  · exact scanBlockEntryIx_preserves_explicitKeyStack s _ hOk
  · exact scanKeyIx_preserves_explicitKeyStack s _ hOk
  · exact scanValueIx_preserves_explicitKeyStack s _ hOk

lemma scanNextTokenIx_dispatchContent_preserves_explicitKeyStack
    (s : ScannerStateIx input) (c : Char) (s' : ScannerStateIx input)
    (h : scanNextTokenIx_dispatchContent s c = .ok s') :
    s'.explicitKeyStack = s.explicitKeyStack := by
  -- Clone of `scanNextTokenIx_dispatchContent_preserves_simpleKeyStack`
  -- (Preserve/Step.lean §3.1): peel the 7-way content dispatch one `if`
  -- at a time; anchor/alias/tag use the explicit `_preserves_explicitKeyStack`
  -- lemmas, scalar branches preserve `explicitKeyStack` structurally.
  unfold scanNextTokenIx_dispatchContent at h
  by_cases hg1 : (c == '&') = true
  · -- '&' anchor
    rw [ite_eq_left hg1] at h
    try simp only [Bind.bind, Except.bind] at h
    split at h   -- item 9e: the property-run guard
    · cases h
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h; cases h
    | ok v =>
      rw [hA] at h
      simp only [Except.ok.injEq] at h; subst h
      exact scanAnchorOrAliasIx_preserves_explicitKeyStack s true v hA
  · rw [ite_eq_right hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    by_cases hg2 : (c == '*') = true
    · -- '*' alias
      rw [ite_eq_left hg2] at h
      split at h   -- item 9e: the property-run guard
      · cases h
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h; cases h
      | ok v =>
        rw [hA] at h
        -- item 9h: `aliasTrailingErrIx` is a CHECK — the state is untouched.
        dsimp only [] at h
        split at h
        · cases h
        simp only [Except.ok.injEq] at h; subst h
        exact scanAnchorOrAliasIx_preserves_explicitKeyStack s false v hA
    · rw [ite_eq_right hg2] at h
      by_cases hg3 : (c == '!') = true
      · -- '!' tag
        rw [ite_eq_left hg3] at h
        split at h   -- item 9e: the property-run guard
        · cases h
        cases hT : scanTagIx s with
        | error e => rw [hT] at h; cases h
        | ok v =>
          rw [hT] at h
          simp only [Except.ok.injEq] at h; subst h
          exact scanTagIx_preserves_explicitKeyStack s v hT
      · rw [ite_eq_right hg3] at h
        by_cases hg4 : (c == '|' || c == '>') = true
        · -- block scalar
          rw [ite_eq_left hg4] at h
          -- Peel the §6.7 header-newline guard: its throw arm cannot be `.ok`.
          split at h
          · cases h
          -- Peel the §6.1/§8.1.3 body-validator guard (item 7 strictness).
          split at h
          · cases h
          -- Peel the §6.1/§8.1.1 tab-stop guard (`blockScalarTabStopErrIx`).
          split at h
          · cases h
          split at h
          · simp only [Except.ok.injEq] at h; subst h; rfl
          · cases h
        · rw [ite_eq_right hg4] at h
          by_cases hg5 : (c == '"') = true
          · -- double-quoted
            rw [ite_eq_left hg5] at h
            -- Peel the quoted-scalar strictness guard (item 7).
            split at h
            · cases h
            split at h
            · simp only [Except.ok.injEq] at h; subst h; rfl
            · cases h
          · rw [ite_eq_right hg5] at h
            by_cases hg6 : (c == '\'') = true
            · -- single-quoted
              rw [ite_eq_left hg6] at h
              -- Peel the quoted-scalar strictness guard (item 7).
              split at h
              · cases h
              split at h
              · simp only [Except.ok.injEq] at h; subst h; rfl
              · cases h
            · rw [ite_eq_right hg6] at h
              -- plain scalar (success) vs error: one small inner `if`
              split at h
              · -- item 50: the plain strictness walker's throw contradicts `.ok`
                split at h
                · cases h
                simp only [Except.ok.injEq] at h; subst h; rfl
              · cases h

/-! ## §3  Flow-indicator dispatcher step fact -/

set_option maxHeartbeats 800000 in
/-- The 5-arm `flowLevel`/`explicitKeyStack` fact for the indexed flow-indicator
    dispatcher: `[`/`{` push the outer explicit-key stamp, `]`/`}` pop (with
    `flowLevel > 0` from the level guard and the 9a kind check dead in the
    ok arms), and `,` preserves both fields. -/
lemma scanNextTokenIx_dispatchFlowIndicators_ekStack_step
    (s s' : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) :
    (s'.flowLevel = s.flowLevel ∧ s'.explicitKeyStack = s.explicitKeyStack) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧ s'.explicitKeyStack
      = s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol)) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧ s'.explicitKeyStack
      = s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol)) ∨
    (s.flowLevel > 0 ∧ s'.flowLevel + 1 = s.flowLevel ∧
      s'.explicitKeyStack = s.explicitKeyStack.pop) := by
  unfold scanNextTokenIx_dispatchFlowIndicators at h
  replace h := peel_flowAdjIx h
  by_cases hg1 : (c == '[') = true
  · rw [ite_eq_left hg1] at h
    have hs : s' = scanFlowSequenceStartIx s := by
      have hi := (Except.ok.injEq _ _).mp h
      exact ((Option.some.injEq _ _).mp hi).symm
    subst hs
    exact Or.inr (Or.inl ⟨scanFlowSequenceStartIx_flowLevel_eq s,
      scanFlowSequenceStartIx_explicitKeyStack s⟩)
  · rw [ite_eq_right hg1] at h
    by_cases hg2 : (c == ']') = true
    · rw [ite_eq_left hg2] at h
      by_cases hg2' : (s.flowLevel == 0) = true
      · rw [ite_eq_left hg2'] at h
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      · rw [ite_eq_right hg2'] at h
        by_cases hg2'' : (s.flowStack.back? != some true) = true
        · rw [ite_eq_left hg2''] at h
          simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        · rw [ite_eq_right hg2''] at h
          have hs : s' = scanFlowSequenceEndIx s := by
            have hi := (Except.ok.injEq _ _).mp h
            exact ((Option.some.injEq _ _).mp hi).symm
          subst hs
          have h_pos : s.flowLevel > 0 := by
            simp only [beq_iff_eq] at hg2'; omega
          refine Or.inr (Or.inr (Or.inr
            ⟨h_pos, ?_, scanFlowSequenceEndIx_explicitKeyStack s⟩))
          rw [scanFlowSequenceEndIx_flowLevel_eq s]; omega
    · rw [ite_eq_right hg2] at h
      by_cases hg3 : (c == '{') = true
      · rw [ite_eq_left hg3] at h
        have hs : s' = scanFlowMappingStartIx s := by
          have hi := (Except.ok.injEq _ _).mp h
          exact ((Option.some.injEq _ _).mp hi).symm
        subst hs
        exact Or.inr (Or.inr (Or.inl ⟨scanFlowMappingStartIx_flowLevel_eq s,
          scanFlowMappingStartIx_explicitKeyStack s⟩))
      · rw [ite_eq_right hg3] at h
        by_cases hg4 : (c == '}') = true
        · rw [ite_eq_left hg4] at h
          by_cases hg4' : (s.flowLevel == 0) = true
          · rw [ite_eq_left hg4'] at h
            simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          · rw [ite_eq_right hg4'] at h
            by_cases hg4'' : (s.flowStack.back? != some false) = true
            · rw [ite_eq_left hg4''] at h
              simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            · rw [ite_eq_right hg4''] at h
              have hs : s' = scanFlowMappingEndIx s := by
                have hi := (Except.ok.injEq _ _).mp h
                exact ((Option.some.injEq _ _).mp hi).symm
              subst hs
              have h_pos : s.flowLevel > 0 := by
                simp only [beq_iff_eq] at hg4'; omega
              refine Or.inr (Or.inr (Or.inr
                ⟨h_pos, ?_, scanFlowMappingEndIx_explicitKeyStack s⟩))
              rw [scanFlowMappingEndIx_flowLevel_eq s]; omega
        · rw [ite_eq_right hg4] at h
          by_cases hg5 : (c == ',') = true
          · rw [ite_eq_left hg5] at h
            by_cases hg5' : (s.flowLevel == 0) = true
            · rw [ite_eq_left hg5'] at h
              simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            · rw [ite_eq_right hg5'] at h
              cases hSFE : scanFlowEntryIx s with
              | error e =>
                rw [hSFE] at h
                simp [Bind.bind, Except.bind] at h
              | ok v =>
                rw [hSFE] at h
                simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
                  Except.ok.injEq, Option.some.injEq] at h
                subst h
                exact Or.inl ⟨scanFlowEntryIx_preserves_flowLevel s _ hSFE,
                  scanFlowEntryIx_preserves_explicitKeyStack s _ hSFE⟩
          · rw [ite_eq_right hg5] at h
            simp [Pure.pure, Except.pure] at h

/-! ## §4  Per-step trichotomy -/

set_option maxHeartbeats 1600000 in
/-- One `scanNextTokenIx` step moves `explicitKeyStack` in lockstep with
    `flowLevel`: it either preserves both, pushes one stamp entry while incrementing
    `flowLevel`, or pops one while decrementing `flowLevel` (which was
    positive).  (Item 98: `explicitKeyStack` twin of the `flowStack` file.) -/
lemma scanNextTokenIx_ekStack_step {s s' : ScannerStateIx input}
    (h : scanNextTokenIx s = .ok (some s')) :
    (s'.flowLevel = s.flowLevel ∧ s'.explicitKeyStack = s.explicitKeyStack) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧
      ∃ e, s'.explicitKeyStack = s.explicitKeyStack.push e) ∨
    (s'.flowLevel = s.flowLevel + 1 ∧
      ∃ e, s'.explicitKeyStack = s.explicitKeyStack.push e) ∨
    (s.flowLevel > 0 ∧ s'.flowLevel + 1 = s.flowLevel ∧
      s'.explicitKeyStack = s.explicitKeyStack.pop) := by
  unfold scanNextTokenIx at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize h_pp : scanNextTokenIx_preprocess s = pp_res at h
  cases pp_res with
  | error e => simp at h
  | ok pp_inner =>
    cases pp_inner with
    | none => simp at h
    | some pair =>
      cases pair with
      | mk s_pp c =>
        have h_pre_st := scanNextTokenIx_preprocess_preserves_explicitKeyStack s s_pp c h_pp
        have h_pre_fl := scanNextTokenIx_preprocess_preserves_flowLevel s s_pp c h_pp
        dsimp only [] at h
        -- §9.2 dangling-node check (item 133)
        have h_dn : ∃ u, scanNextTokenIx_checkDanglingNode s s_pp = .ok u := by
          cases hx : scanNextTokenIx_checkDanglingNode s s_pp with
          | error e => rw [hx] at h; simp at h
          | ok u => exact ⟨u, rfl⟩
        obtain ⟨uDN, h_dn⟩ := h_dn
        rw [h_dn] at h
        dsimp only [] at h
        -- §8.1 flow-value floor (item 172): peeled the same way.
        have h_fvp : ∃ u, scanNextTokenIx_checkFlowValueIndent s s_pp = .ok u := by
          cases hx : scanNextTokenIx_checkFlowValueIndent s s_pp with
          | error e => rw [hx] at h; simp at h
          | ok u => exact ⟨u, rfl⟩
        obtain ⟨uFV, h_fvp⟩ := h_fvp
        rw [h_fvp] at h
        dsimp only [] at h
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h
        cases ds_res with
        | error e => simp at h
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h
            subst h
            refine Or.inl ⟨?_, ?_⟩
            · rw [scanNextTokenIx_dispatchStructural_preserves_flowLevel _ c _ h_ds,
                  h_pre_fl]
            · rw [scanNextTokenIx_dispatchStructural_preserves_explicitKeyStack _ c _ h_ds,
                  h_pre_st]
          | none =>
            dsimp only [] at h
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h
            have h_dir_st : s_dir.explicitKeyStack = s_pp.explicitKeyStack := by
              rw [← h_dir_def]; split <;> rfl
            have h_dir_fl : s_dir.flowLevel = s_pp.flowLevel := by
              rw [← h_dir_def]; split <;> rfl
            -- Fix B pending-directives check: error arm contradicts h
            split at h
            · contradiction
            -- §9.2 bare-document check (item 132): the same shape
            split at h
            · contradiction
            generalize h_df : scanNextTokenIx_dispatchFlowIndicators s_dir c = df_res at h
            cases df_res with
            | error e => simp at h
            | ok df_inner =>
              cases df_inner with
              | some s_flow =>
                simp only [Except.ok.injEq, Option.some.injEq] at h
                subst h
                rcases scanNextTokenIx_dispatchFlowIndicators_ekStack_step _ _ c h_df with
                  ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h0, h1, h2⟩
                · exact Or.inl ⟨by omega, by rw [h2, h_dir_st, h_pre_st]⟩
                · exact Or.inr (Or.inl ⟨by omega, _, by rw [h2, h_dir_st, h_pre_st]⟩)
                · exact Or.inr (Or.inr (Or.inl ⟨by omega, _,
                    by rw [h2, h_dir_st, h_pre_st]⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega,
                    by rw [h2, h_dir_st, h_pre_st]⟩))
              | none =>
                dsimp only [] at h
                generalize h_db : scanNextTokenIx_dispatchBlockIndicators s_dir c = db_res at h
                cases db_res with
                | error e => simp at h
                | ok db_inner =>
                  cases db_inner with
                  | some s_blk =>
                    simp only [Except.ok.injEq, Option.some.injEq] at h
                    subst h
                    refine Or.inl ⟨?_, ?_⟩
                    · rw [scanNextTokenIx_dispatchBlockIndicators_preserves_flowLevel
                          _ c _ h_db, h_dir_fl, h_pre_fl]
                    · rw [scanNextTokenIx_dispatchBlockIndicators_preserves_explicitKeyStack
                          _ c _ h_db, h_dir_st, h_pre_st]
                  | none =>
                    dsimp only [] at h
                    -- item 47: adjacent-value check (pure, no state change)
                    generalize h_av : scanNextTokenIx_checkAdjacentValue s_dir c = av_res at h
                    cases av_res with
                    | error e => simp at h
                    | ok _ =>
                    generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h
                    cases dc_res with
                    | error e => simp at h
                    | ok s_ct =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h
                      subst h
                      refine Or.inl ⟨?_, ?_⟩
                      · rw [scanNextTokenIx_dispatchContent_preserves_flowLevel
                            _ c _ h_dc, h_dir_fl, h_pre_fl]
                      · rw [scanNextTokenIx_dispatchContent_preserves_explicitKeyStack
                            _ c _ h_dc, h_dir_st, h_pre_st]

/-! ## §5  Chain theorems over `FlowMonoChainIx` -/

/-- Through a `FlowMonoChainIx` with floor `fl₀`, the `explicitKeyStack` entries
    below the floor are never disturbed: if the start state's stack splits
    as `base ++ extra` with `extra` tracking the excess flow depth
    (`extra.size = flowLevel - fl₀`), the end state's stack is
    `base ++ extra'` with `extra'` tracking the end state's excess depth.
    Pops always stay inside `extra` because the chain keeps
    `flowLevel ≥ fl₀`. -/
lemma FlowMonoChainIx.ekStack_invariant {fl₀ : Nat}
    {t s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ t n s') :
    ∀ base extra : Array (Option Nat × Int), t.explicitKeyStack = base ++ extra →
      extra.size = t.flowLevel - fl₀ → t.flowLevel ≥ fl₀ →
      ∃ extra', s'.explicitKeyStack = base ++ extra' ∧
        extra'.size = s'.flowLevel - fl₀ := by
  induction h with
  | zero _h_fl =>
    intro _base extra h_eq h_size _h_ge
    exact ⟨extra, h_eq, h_size⟩
  | @step s s_mid s'' m _h_fl h_snt h_rest ih =>
    intro base extra h_eq h_size h_ge
    have h_mid_ge : s_mid.flowLevel ≥ fl₀ := h_rest.flowLevel_ge_start
    rcases scanNextTokenIx_ekStack_step h_snt with
      ⟨h1, h2⟩ | ⟨h1, e, h2⟩ | ⟨h1, e, h2⟩ | ⟨h0, h1, h2⟩
    · -- preserve
      exact ih base extra (h2.trans h_eq) (by omega) (by omega)
    · -- push (seq open)
      refine ih base (extra.push e) ?_ ?_ (by omega)
      · rw [h2, h_eq, Array.push_append]
      · rw [Array.size_push]; omega
    · -- push (map open)
      refine ih base (extra.push e) ?_ ?_ (by omega)
      · rw [h2, h_eq, Array.push_append]
      · rw [Array.size_push]; omega
    · -- pop: the chain floor keeps the pop inside `extra`
      have h_extra : 0 < extra.size := by omega
      refine ih base extra.pop ?_ ?_ (by omega)
      · rw [h2, h_eq, Array.pop_append, ite_eq_right]
        simp only [Array.isEmpty_iff]
        intro hh; subst hh; simp at h_extra
      · rw [Array.size_pop]; omega

/-- A balanced `FlowMonoChainIx` — starting and ending at the floor flow
    level — preserves `explicitKeyStack` exactly. -/
lemma FlowMonoChainIx.ekStack_eq {fl₀ : Nat}
    {s s' : ScannerStateIx input} {n : Nat}
    (h : FlowMonoChainIx fl₀ s n s')
    (h_s : s.flowLevel = fl₀) (h_s' : s'.flowLevel = fl₀) :
    s'.explicitKeyStack = s.explicitKeyStack := by
  obtain ⟨extra', h_eq, h_size⟩ :=
    h.ekStack_invariant s.explicitKeyStack #[] (by simp) (by simp [h_s]) (by omega)
  have h_zero : extra'.size = 0 := by omega
  rw [h_eq, Array.eq_empty_of_size_eq_zero h_zero, Array.append_empty]

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

end Blanket
