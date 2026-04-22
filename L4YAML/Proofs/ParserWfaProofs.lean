import L4YAML.Spec.Grammar
import L4YAML.Parser.Composition
import L4YAML.Proofs.ParserGrammableBase
import L4YAML.Proofs.ParserNodeProofs
import L4YAML.Proofs.ParserWellBehaved
import L4YAML.Proofs.Foundation.ValueAlgebra

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

set_option autoImplicit false

/-!
# WellFormedAnchors Preservation through parseNode

Proves that `parseNode` preserves `WellFormedAnchors`:
if the input anchors satisfy WFA, then the output anchors do too.

Architecture: strong induction on fuel, same pattern as AG and AAR proofs.
Sub-parsers only modify anchors through recursive `parseNode` calls, so
WFA propagates through each sub-parser by the induction hypothesis.
The only non-trivial case is `applyNodeFinalization`: when an anchor is
registered, the cleaned value is universally grammable by
`adaptForFlowContext_grammable_forall ∘ compose_value_grammable`.
-/

namespace L4YAML.Proofs.ParserGrammable

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.ScannerPlainScalarValid
open L4YAML.Proofs.Composition
open L4YAML.Proofs.ValueAlgebra
open ParserNodeProofs

-- Custom tactic: unfold all `*.loop*` constants in a hypothesis.
open Lean Lean.Meta Lean.Elab.Tactic in
elab "unfold_loop_at" h:ident : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let fvarId ← getFVarId h
    let ldecl ← fvarId.getDecl
    let ty := ldecl.type
    let namesRef ← IO.mkRef (∅ : NameSet)
    let _ ← Lean.Meta.transform ty (pre := fun e => do
      let fn := e.getAppFn
      if fn.isConst then
        let name := fn.constName!
        let leaf := if name.isStr then name.getString! else ""
        let parentLeaf := if name.getPrefix.isStr then name.getPrefix.getString! else ""
        if leaf == "loop" || parentLeaf == "loop" then
          namesRef.modify (·.insert name)
      return .continue)
    let names ← namesRef.get
    if names.isEmpty then throwError "no loop constants found"
    let mut currentTy := ty
    for name in names do
      let result ← Lean.Meta.unfold currentTy name
      currentTy := result.expr
    if ty == currentTy then throwError "no change"
    let mvarId ← mvarId.replaceLocalDeclDefEq fvarId currentTy
    replaceMainGoal [mvarId]

-- ============================================================
-- §1  Definitions and helpers
-- ============================================================

-- The WFA induction hypothesis.
def ParseNodeWFA (tokens : Array (Positioned YamlToken)) (n : Nat) : Prop :=
  ∀ (ps : ParseState) (m : Nat) (val : YamlValue) (ps' : ParseState),
    m ≤ n →
    ps.tokens = tokens →
    parseNode ps m = .ok (val, ps') →
    WellFormedAnchors ps.anchors →
    WellFormedAnchors ps'.anchors

-- Empty anchors are trivially well-formed.
theorem WFA_empty : WellFormedAnchors (#[] : Array (String × YamlValue)) := by
  intro name val h_find _
  simp [Array.findSome?] at h_find

-- WellFormedAnchors is preserved when pushing a universally-grammable entry.
theorem WFA_of_push (anchors : Array (String × YamlValue))
    (entry : String × YamlValue)
    (h_wfa : WellFormedAnchors anchors)
    (h_new : ∀ inFlow, Grammable entry.2.stripAnchors inFlow) :
    WellFormedAnchors (anchors.push entry) := by
  intro name val h_find inFlow
  rw [Array.findSome?_push] at h_find
  -- h_find : (anchors.findSome? f).or (f entry) = some val
  generalize hg : anchors.findSome? (fun x =>
    match x with | (n, v) => if n == name then some v else none) = found at h_find
  cases found with
  | some v' =>
    -- found in original array
    dsimp only [Option.or] at h_find
    injection h_find with h_eq; subst h_eq
    exact h_wfa name v' hg inFlow
  | none =>
    -- must come from entry
    dsimp only [Option.or] at h_find
    split at h_find
    · injection h_find with h_eq; subst h_eq; exact h_new inFlow
    · simp at h_find

-- ============================================================
-- §2  applyNodeFinalization preserves WFA
-- ============================================================

-- addAnchor preserves WFA when the value has a Grammable composition.
theorem addAnchor_wfa (ps : ParseState) (name : String) (val : YamlValue)
    (h_wfa : WellFormedAnchors ps.anchors)
    (h_gram : ∀ inFlow, Grammable ((val.resolveAliases ps.anchors).stripAnchors.adaptForFlowContext) inFlow) :
    WellFormedAnchors (ps.addAnchor name val).anchors := by
  unfold ParseState.addAnchor
  dsimp only []
  apply WFA_of_push
  · exact h_wfa
  · intro inFlow
    have h_eq : ((val.resolveAliases ps.anchors).stripAnchors.adaptForFlowContext).stripAnchors =
        (val.resolveAliases ps.anchors).stripAnchors.adaptForFlowContext :=
      stripAnchors_of_cleaned (val.resolveAliases ps.anchors)
    rw [h_eq]
    exact h_gram inFlow

-- Helper: compose + adaptForFlowContext gives universally-grammable values.
theorem cleaned_grammable_forall
    (val : YamlValue) (ps : ParseState)
    (h_scannable : Scannable val false)
    (h_aar : AllAliasesResolve val ps.anchors)
    (h_wfa : WellFormedAnchors ps.anchors) :
    ∀ inFlow, Grammable ((val.resolveAliases ps.anchors).stripAnchors.adaptForFlowContext) inFlow := by
  have h_g := compose_value_grammable val ps.anchors false h_scannable h_aar h_wfa
  exact adaptForFlowContext_grammable_forall _ _ h_g

-- applyNodeFinalization preserves WFA when Scannable + AAR + WFA hold.
theorem applyNodeFinalization_wfa
    (val : YamlValue) (ps : ParseState) (props : NodeProperties) (nodeStartPos : YamlPos)
    (h_wfa : WellFormedAnchors ps.anchors)
    (h_scannable : Scannable val false)
    (h_aar : AllAliasesResolve val ps.anchors) :
    WellFormedAnchors (applyNodeFinalization val ps props nodeStartPos).2.anchors := by
  rcases props with ⟨anchor, tag, dup⟩
  cases anchor with
  | none =>
    simp only [applyNodeFinalization]
    split <;> exact h_wfa
  | some name =>
    cases val with
    | scalar s =>
      simp only [applyNodeFinalization]
      split <;> exact addAnchor_wfa ps name _ h_wfa
        (cleaned_grammable_forall _ ps h_scannable h_aar h_wfa)
    | alias a =>
      simp only [applyNodeFinalization]
      split <;> exact addAnchor_wfa ps name _ h_wfa
        (cleaned_grammable_forall _ ps h_scannable h_aar h_wfa)
    | sequence style items otag oanchor =>
      cases otag <;> cases oanchor <;> simp only [applyNodeFinalization] <;> split
      all_goals (first
        | exact addAnchor_wfa ps name _ h_wfa
            (cleaned_grammable_forall _ ps h_scannable h_aar h_wfa)
        | (exact addAnchor_wfa ps name _ h_wfa
            (cleaned_grammable_forall _ ps
              (.sequence _ _ _ _ _
                (by cases h_scannable with | sequence _ _ _ _ _ h => exact h))
              (aar_retag_sequence ps.anchors tag (some name) h_aar) h_wfa)))
    | mapping style pairs otag oanchor =>
      cases otag <;> cases oanchor <;> simp only [applyNodeFinalization] <;> split
      all_goals (first
        | exact addAnchor_wfa ps name _ h_wfa
            (cleaned_grammable_forall _ ps h_scannable h_aar h_wfa)
        | (exact addAnchor_wfa ps name _ h_wfa
            (cleaned_grammable_forall _ ps
              (.mapping _ _ _ _ _
                (by cases h_scannable with | mapping _ _ _ _ _ hk _ => exact hk)
                (by cases h_scannable with | mapping _ _ _ _ _ _ hv => exact hv))
              (aar_retag_mapping ps.anchors tag (some name) h_aar) h_wfa)))

-- ============================================================
-- §3  parseNodeContent and sub-parser WFA
-- ============================================================

-- All sub-parsers only modify anchors through recursive parseNode calls.
-- Therefore WFA propagation through each sub-parser follows mechanically
-- from the induction hypothesis (for parseNode) and token/anchor preservation
-- lemmas (from ParseNodeWB and advance/tryConsume).

-- Helper: advance preserves anchors and tokens.
theorem advance_anchors (ps : ParseState) :
    ps.advance.anchors = ps.anchors := by simp [ParseState.advance]

theorem advance_tokens (ps : ParseState) :
    ps.advance.tokens = ps.tokens := by simp [ParseState.advance]

-- Helper: tryConsume preserves anchors and tokens.
theorem tc_anchors (ps : ParseState) (tok : YamlToken) :
    (ps.tryConsume tok).2.anchors = ps.anchors := by
  unfold ParseState.tryConsume; split <;> (try split) <;> simp [ParseState.advance]

theorem tc_tokens (ps : ParseState) (tok : YamlToken) :
    (ps.tryConsume tok).2.tokens = ps.tokens := by
  unfold ParseState.tryConsume; split <;> (try split) <;> simp [ParseState.advance]

-- Get tokens preservation from ParseNodeWB.
theorem parseNode_tokens_of_wb
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseNode ps fuel = .ok (val, ps')) :
    ps'.tokens = tokens :=
  (h_wb ps fuel val ps' h_fuel h_tok h_ok).2.2.2

-- parseExplicitKey: emptyNode or parseNode
theorem parseExplicitKey_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseExplicitKey ps fuel = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  all_goals (first
    | (simp only [Except.ok.injEq] at h_ok; obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa)
    | exact h_ih ps fuel _ _ h_fuel h_tok h_ok h_wfa)

-- parseBlockSequenceLoop
theorem parseBlockSequenceLoop_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1) (h_tok : ps.tokens = tokens)
    (result : Array YamlValue) (ps' : ParseState)
    (h_ok : parseBlockSequenceLoop ps fuel items = .ok (result, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
  | succ k ih_fuel =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · -- peek? = some .blockEntry
      have h_wfa_adv : WellFormedAnchors ps.advance.anchors :=
        advance_anchors ps ▸ h_wfa
      have h_tok_adv : ps.advance.tokens = tokens :=
        (advance_tokens ps).trans h_tok
      split at h_ok
      -- empty entry cases: recurse
      all_goals (first
        | exact ih_fuel ps.advance (items.push emptyNode) (by omega)
            h_tok_adv h_ok h_wfa_adv
        | skip)
      -- non-empty: parseNode then recurse
      · generalize h_ps_a : ps.advance = ps_a at h_ok
        have h_tok_a : ps_a.tokens = tokens := by rw [← h_ps_a]; exact h_tok_adv
        have h_wfa_a : WellFormedAnchors ps_a.anchors := by rw [← h_ps_a]; exact h_wfa_adv
        generalize h_ps_wf : { ps_a with currentPath := _ } = ps_wf at h_ok
        split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_tok_wf : ps_wf.tokens = tokens := by
            rw [← h_ps_wf]; exact h_tok_a
          have h_wfa_wf : WellFormedAnchors ps_wf.anchors := by
            rw [← h_ps_wf]; exact h_wfa_a
          have h_wfa_n := h_ih ps_wf k _ _ (by omega) h_tok_wf heq_pn h_wfa_wf
          have h_tok_n := parseNode_tokens_of_wb h_wb ps_wf k (by omega) h_tok_wf _ _ heq_pn
          generalize h_ps_r : { ps_n with currentPath := _ } = ps_r at h_ok
          have h_wfa_r : WellFormedAnchors ps_r.anchors := by
            rw [← h_ps_r]; exact h_wfa_n
          have h_tok_r : ps_r.tokens = tokens := by
            rw [← h_ps_r]; exact h_tok_n
          exact ih_fuel ps_r _ (by omega) h_tok_r h_ok h_wfa_r
    · -- not blockEntry
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa

-- parseBlockSequence
theorem parseBlockSequence_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseBlockSequence ps fuel = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_wfa_loop := parseBlockSequenceLoop_wfa h_ih h_wb
        ps.advance k #[] (by omega) ((advance_tokens ps).trans h_tok)
        items ps_loop heq_loop (advance_anchors ps ▸ h_wfa)
      split at h_ok <;> (
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
      · rw [advance_anchors]; exact h_wfa_loop
      · exact h_wfa_loop

-- parseImplicitBlockSequenceLoop
theorem parseImplicitBlockSequenceLoop_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1) (h_tok : ps.tokens = tokens)
    (result : Array YamlValue) (ps' : ParseState)
    (h_ok : parseImplicitBlockSequenceLoop ps fuel items = .ok (result, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
  | succ k ih_fuel =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · have h_wfa_adv : WellFormedAnchors ps.advance.anchors :=
        advance_anchors ps ▸ h_wfa
      have h_tok_adv : ps.advance.tokens = tokens :=
        (advance_tokens ps).trans h_tok
      split at h_ok
      all_goals (first
        | exact ih_fuel ps.advance (items.push emptyNode) (by omega)
            h_tok_adv h_ok h_wfa_adv
        | skip)
      · generalize h_ps_a : ps.advance = ps_a at h_ok
        have h_tok_a : ps_a.tokens = tokens := by rw [← h_ps_a]; exact h_tok_adv
        have h_wfa_a : WellFormedAnchors ps_a.anchors := by rw [← h_ps_a]; exact h_wfa_adv
        generalize h_ps_wf : { ps_a with currentPath := _ } = ps_wf at h_ok
        split at h_ok
        · simp at h_ok
        · rename_i pn_res heq_pn
          obtain ⟨val_n, ps_n⟩ := pn_res
          dsimp only [] at h_ok
          have h_tok_wf : ps_wf.tokens = tokens := by
            rw [← h_ps_wf]; exact h_tok_a
          have h_wfa_wf : WellFormedAnchors ps_wf.anchors := by
            rw [← h_ps_wf]; exact h_wfa_a
          have h_wfa_n := h_ih ps_wf k _ _ (by omega) h_tok_wf heq_pn h_wfa_wf
          have h_tok_n := parseNode_tokens_of_wb h_wb ps_wf k (by omega) h_tok_wf _ _ heq_pn
          generalize h_ps_r : { ps_n with currentPath := _ } = ps_r at h_ok
          have h_wfa_r : WellFormedAnchors ps_r.anchors := by
            rw [← h_ps_r]; exact h_wfa_n
          have h_tok_r : ps_r.tokens = tokens := by
            rw [← h_ps_r]; exact h_tok_n
          exact ih_fuel ps_r _ (by omega) h_tok_r h_ok h_wfa_r
    · simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa

-- parseImplicitBlockSequence
theorem parseImplicitBlockSequence_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseImplicitBlockSequence ps fuel = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseImplicitBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      exact parseImplicitBlockSequenceLoop_wfa h_ih h_wb
        ps k #[] (by omega) h_tok items ps_loop heq_loop h_wfa

-- parseBlockMappingEntryValue
set_option maxHeartbeats 400000 in
theorem parseBlockMappingEntryValue_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (keyHasContent : Bool) (keyLine keyCol : Nat)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseBlockMappingEntryValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  have h_tc_wfa : WellFormedAnchors (ps.tryConsume .value).2.anchors := by
    rw [tc_anchors]; exact h_wfa
  have h_tc_tok : (ps.tryConsume .value).2.tokens = tokens := by
    rw [tc_tokens]; exact h_tok
  split at h_ok
  · -- consumed = true
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- emptyNode goals
    all_goals (try (obtain ⟨rfl, rfl⟩ := h_ok; exact h_tc_wfa))
    -- parseNode goals
    all_goals exact h_ih _ fuel _ _ h_fuel h_tc_tok h_ok h_tc_wfa
  · -- consumed = false
    obtain ⟨rfl, rfl⟩ := h_ok; exact h_tc_wfa

-- handleBlockMappingValueEntry
theorem handleBlockMappingValueEntry_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (pairIdx : Nat) (val : YamlValue) (ps' : ParseState)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_wfa_adv : WellFormedAnchors ps.advance.anchors :=
    advance_anchors ps ▸ h_wfa
  have h_tok_adv : ps.advance.tokens = tokens :=
    (advance_tokens ps).trans h_tok
  -- Split on the inner match (peek? dispatch)
  split at h_ok
  -- emptyNode cases (some .key, some .blockEnd, none)
  all_goals (try (
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    dsimp only []
    exact h_wfa_adv))
  -- Remaining: parseNode
  · split at h_ok
    · simp at h_ok
    · rename_i pn_res heq_pn
      obtain ⟨v, ps_n⟩ := pn_res
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      dsimp only []
      exact h_ih _ fuel _ _ h_fuel
        (by dsimp only []; exact h_tok_adv) heq_pn
        (by dsimp only []; exact h_wfa_adv)

-- ── §3a  Tokens preservation for compound sub-parsers ──────────────

theorem parseExplicitKey_tok
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseExplicitKey ps fuel = .ok (val, ps')) :
    ps'.tokens = tokens := by
  unfold parseExplicitKey at h_ok; split at h_ok
  all_goals (first
    | (simp only [Except.ok.injEq] at h_ok; obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_tok)
    | exact parseNode_tokens_of_wb h_wb ps fuel h_fuel h_tok _ _ h_ok)

set_option maxHeartbeats 400000 in
theorem parseBlockMappingEntryValue_tok
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (keyHasContent : Bool) (keyLine keyCol : Nat)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok (val, ps')) :
    ps'.tokens = tokens := by
  unfold parseBlockMappingEntryValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  have h_tc_tok : (ps.tryConsume .value).2.tokens = tokens := (tc_tokens _ _).trans h_tok
  split at h_ok
  · all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (try (obtain ⟨rfl, rfl⟩ := h_ok; exact h_tc_tok))
    all_goals exact parseNode_tokens_of_wb h_wb _ fuel h_fuel h_tc_tok _ _ h_ok
  · obtain ⟨rfl, rfl⟩ := h_ok; exact h_tc_tok

theorem handleBlockMappingValueEntry_tok
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (pairIdx : Nat) (val : YamlValue) (ps' : ParseState)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok (val, ps')) :
    ps'.tokens = tokens := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_tok_adv : ps.advance.tokens = tokens := (advance_tokens ps).trans h_tok
  -- Split on the inner match (peek? dispatch)
  split at h_ok
  all_goals (try (
    simp only [Except.ok.injEq] at h_ok; obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    dsimp only []; exact h_tok_adv))
  · split at h_ok
    · simp at h_ok
    · rename_i pn_res heq_pn; obtain ⟨v, ps_n⟩ := pn_res
      dsimp only [] at h_ok; simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
      dsimp only []
      exact parseNode_tokens_of_wb h_wb _ fuel h_fuel
        (by dsimp only []; exact h_tok_adv) _ _ heq_pn

-- Helpers accepting undestruct'd pair results (for goals after split where v✝ is opaque)
theorem pn_tok_pair
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (result : YamlValue × ParseState)
    (h_ok : parseNode ps fuel = .ok result) :
    result.2.tokens = tokens := by
  obtain ⟨v, ps'⟩ := result
  exact parseNode_tokens_of_wb h_wb ps fuel h_fuel h_tok v ps' h_ok

theorem bev_tok_pair
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (keyHasContent : Bool) (keyLine keyCol : Nat)
    (result : YamlValue × ParseState)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok result) :
    result.2.tokens = tokens := by
  obtain ⟨v, ps'⟩ := result
  exact parseBlockMappingEntryValue_tok h_wb ps fuel h_fuel h_tok keyHasContent keyLine keyCol v ps' h_ok

theorem pn_wfa_pair
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (result : YamlValue × ParseState)
    (h_ok : parseNode ps fuel = .ok result)
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors result.2.anchors := by
  obtain ⟨v, ps'⟩ := result
  exact h_ih ps fuel v ps' h_fuel h_tok h_ok h_wfa

theorem bev_wfa_pair
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (keyHasContent : Bool) (keyLine keyCol : Nat)
    (result : YamlValue × ParseState)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok result)
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors result.2.anchors := by
  obtain ⟨v, ps'⟩ := result
  exact parseBlockMappingEntryValue_wfa h_ih ps fuel h_fuel h_tok keyHasContent keyLine keyCol v ps' h_ok h_wfa

set_option maxHeartbeats 800000 in
theorem handleBlockMappingKeyEntry_tok
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (pairIdx : Nat) (key val : YamlValue) (ps' : ParseState)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok (key, val, ps')) :
    ps'.tokens = tokens := by
  unfold handleBlockMappingKeyEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_tok_adv : ps.advance.tokens = tokens := (advance_tokens ps).trans h_tok
  split at h_ok <;> first | contradiction | skip
  all_goals (try (simp only [emptyNode] at h_ok))
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (obtain ⟨_, _, rfl⟩ := h_ok)
  all_goals (dsimp only [] at *)
  -- emptyNode branches: BEV input has same tokens as ps.advance
  all_goals (try (
    refine bev_tok_pair h_wb _ fuel h_fuel ?htok _ _ _ _ ?hok
    case hok => assumption
    case htok => dsimp only []; exact h_tok_adv))
  -- parseNode branches: derive tokens from parseNode first
  all_goals (
    refine bev_tok_pair h_wb ?_ fuel h_fuel ?htok ?_ ?_ ?_ ?_ ?hok
    case hok => assumption
    case htok =>
      dsimp only []
      first
      | exact h_tok_adv
      | (refine pn_tok_pair h_wb ?_ fuel h_fuel ?pntok ?_ ?pnok
         case pnok => assumption
         case pntok => exact h_tok_adv))

theorem parseFlowMappingValue_tok
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (savedPath : YamlPath) (keyContent : String)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok (val, ps')) :
    ps'.tokens = tokens := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  -- ps → withField → tryConsume .key → tryConsume .value → optional parseNode → withField
  have h_tc1 : ({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.tokens = tokens := by
    rw [tc_tokens]; exact h_tok
  have h_tc2 : (({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.tryConsume .value).2.tokens
      = tokens := by rw [tc_tokens]; exact h_tc1
  split at h_ok <;> first | contradiction | skip
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
  -- emptyNode: ps' = { tc_state with currentPath := savedPath }
  all_goals try (dsimp only []; exact h_tc2)
  -- parseNode: ps' = { ps_pn with currentPath := savedPath }
  all_goals (
    dsimp only []
    exact parseNode_tokens_of_wb h_wb _ fuel h_fuel h_tc2 _ _ (by assumption))

set_option maxHeartbeats 800000 in
theorem parseSinglePairMapping_tok
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseSinglePairMapping ps fuel = .ok (val, ps')) :
    ps'.tokens = tokens := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_tok_adv : ps.advance.tokens = tokens := (advance_tokens ps).trans h_tok
    split at h_ok <;> first | contradiction | skip
    all_goals (try (simp only [emptyNode] at h_ok))
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (simp only [Except.ok.injEq] at h_ok)
    all_goals (obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
    all_goals (dsimp only [] at *)
    all_goals (first
      | exact h_tok_adv
      | exact (tc_tokens _ _).trans h_tok_adv
      | (refine pn_tok_pair h_wb ?_ k (by omega) ?pntok ?_ ?pnok
         case pnok => assumption
         case pntok => exact (tc_tokens _ _).trans h_tok_adv)
      | (refine pn_tok_pair h_wb ?_ k (by omega) ?pntok ?_ ?pnok
         case pnok => assumption
         case pntok =>
           refine (tc_tokens _ _).trans ?_
           refine pn_tok_pair h_wb ?_ k (by omega) ?pntok2 ?_ ?pnok2
           case pnok2 => assumption
           case pntok2 => exact h_tok_adv)
      | (refine (tc_tokens _ _).trans ?_
         refine pn_tok_pair h_wb ?_ k (by omega) ?pntok ?_ ?pnok
         case pnok => assumption
         case pntok => exact h_tok_adv))

-- ── §3b  Remaining WFA lemmas ──────────────────────────────────────

-- handleBlockMappingKeyEntry
set_option maxHeartbeats 1600000 in
theorem handleBlockMappingKeyEntry_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (pairIdx : Nat) (key val : YamlValue) (ps' : ParseState)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok (key, val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold handleBlockMappingKeyEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_wfa_adv : WellFormedAnchors ps.advance.anchors :=
    advance_anchors ps ▸ h_wfa
  have h_tok_adv : ps.advance.tokens = tokens :=
    (advance_tokens ps).trans h_tok
  split at h_ok <;> first | contradiction | skip
  all_goals (try (simp only [emptyNode] at h_ok))
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (obtain ⟨_, _, rfl⟩ := h_ok)
  all_goals (dsimp only [] at *)
  -- emptyNode branches
  all_goals (try (
    refine bev_wfa_pair h_ih ?_ fuel h_fuel ?htok ?_ ?_ ?_ ?_ ?hok ?hwfa
    case hok => assumption
    case htok => dsimp only []; exact h_tok_adv
    case hwfa => dsimp only []; exact h_wfa_adv))
  -- parseNode branches
  all_goals (
    refine bev_wfa_pair h_ih ?_ fuel h_fuel ?htok ?_ ?_ ?_ ?_ ?hok ?hwfa
    case hok => assumption
    case htok =>
      dsimp only []
      first
      | exact h_tok_adv
      | (refine pn_tok_pair h_wb ?_ fuel h_fuel ?pntok ?_ ?pnok
         case pnok => assumption
         case pntok => exact h_tok_adv)
    case hwfa =>
      dsimp only []
      first
      | exact h_wfa_adv
      | (refine pn_wfa_pair h_ih ?_ fuel h_fuel ?pntok2 ?_ ?pnok2 ?pnwfa2
         case pnok2 => assumption
         case pntok2 => exact h_tok_adv
         case pnwfa2 => exact h_wfa_adv))
theorem parseBlockMappingLoop_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1) (h_tok : ps.tokens = tokens)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseState)
    (h_ok : parseBlockMappingLoop ps fuel pairs = .ok (result, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseBlockMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
  | succ k ih_fuel =>
    unfold parseBlockMappingLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · -- key
      split at h_ok
      · simp at h_ok
      · rename_i entry_res heq_entry
        obtain ⟨key_v, val_v, ps_entry⟩ := entry_res
        dsimp only [] at h_ok
        have h_wfa_entry := handleBlockMappingKeyEntry_wfa h_ih h_wb ps k (by omega)
            h_tok _ key_v val_v ps_entry heq_entry h_wfa
        have h_tok_entry := handleBlockMappingKeyEntry_tok h_wb ps k (by omega)
            h_tok _ key_v val_v ps_entry heq_entry
        exact ih_fuel ps_entry _ (by omega) h_tok_entry h_ok h_wfa_entry
    · -- value (implicit key)
      split at h_ok
      · simp at h_ok
      · rename_i val_res heq_val
        obtain ⟨val_v, ps_val⟩ := val_res
        dsimp only [] at h_ok
        have h_wfa_val := handleBlockMappingValueEntry_wfa h_ih ps k (by omega)
            h_tok _ val_v ps_val heq_val h_wfa
        have h_tok_val := handleBlockMappingValueEntry_tok h_wb ps k (by omega)
            h_tok _ val_v ps_val heq_val
        exact ih_fuel ps_val _ (by omega) h_tok_val h_ok h_wfa_val
    · -- not key/value
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa

-- parseBlockMapping
theorem parseBlockMapping_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseBlockMapping ps fuel = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseBlockMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_wfa_loop := parseBlockMappingLoop_wfa h_ih h_wb ps.advance k #[] (by omega)
          ((advance_tokens ps).trans h_tok) pairs ps_loop heq_loop (advance_anchors ps ▸ h_wfa)
      split at h_ok <;> (
        simp only [Except.ok.injEq] at h_ok
        obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
      · rw [advance_anchors]; exact h_wfa_loop
      · exact h_wfa_loop

-- parseFlowMappingValue
theorem parseFlowMappingValue_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (savedPath : YamlPath) (keyContent : String)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_wfa_wf : WellFormedAnchors ({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.anchors := by
    rw [tc_anchors]; exact h_wfa
  have h_tc2_wfa : WellFormedAnchors
      (({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.tryConsume .value).2.anchors := by
    rw [tc_anchors]; exact h_wfa_wf
  have h_tc2_tok : (({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.tryConsume .value).2.tokens
      = tokens := by rw [tc_tokens]; rw [tc_tokens]; exact h_tok
  split at h_ok <;> first | contradiction | skip
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
  -- emptyNode: result state = { tc2_state with currentPath := savedPath }
  all_goals try (dsimp only []; exact h_tc2_wfa)
  -- parseNode: result state = { ps_pn with currentPath := savedPath }
  all_goals (
    dsimp only []
    exact h_ih _ fuel _ _ h_fuel h_tc2_tok (by assumption) h_tc2_wfa)

-- parseSinglePairMapping
set_option maxHeartbeats 1600000 in
theorem parseSinglePairMapping_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseSinglePairMapping ps fuel = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_wfa_adv : WellFormedAnchors ps.advance.anchors := advance_anchors ps ▸ h_wfa
    have h_tok_adv : ps.advance.tokens = tokens := (advance_tokens ps).trans h_tok
    split at h_ok <;> first | contradiction | skip
    all_goals (try (simp only [emptyNode] at h_ok))
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (simp only [Except.ok.injEq] at h_ok)
    all_goals (obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok)
    all_goals (dsimp only [] at *)
    all_goals (first
      | exact h_wfa_adv
      | (rw [tc_anchors]; exact h_wfa_adv)
      | (refine pn_wfa_pair h_ih ?_ k (by omega) ?pntok ?_ ?pnok ?pnwfa
         case pnok => assumption
         case pntok => exact (tc_tokens _ _).trans h_tok_adv
         case pnwfa => rw [tc_anchors]; exact h_wfa_adv)
      | (refine pn_wfa_pair h_ih ?_ k (by omega) ?pntok ?_ ?pnok ?pnwfa
         case pnok => assumption
         case pntok =>
           refine (tc_tokens _ _).trans ?_
           refine pn_tok_pair h_wb ?_ k (by omega) ?pt2 ?_ ?po2
           case po2 => assumption
           case pt2 => exact h_tok_adv
         case pnwfa =>
           rw [tc_anchors]
           refine pn_wfa_pair h_ih ?_ k (by omega) ?pt3 ?_ ?po3 ?pw3
           case po3 => assumption
           case pt3 => exact h_tok_adv
           case pw3 => exact h_wfa_adv)
      | (rw [tc_anchors]
         refine pn_wfa_pair h_ih ?_ k (by omega) ?pntok ?_ ?pnok ?pnwfa
         case pnok => assumption
         case pntok => exact h_tok_adv
         case pnwfa => exact h_wfa_adv))

-- parseFlowSequenceLoop
set_option maxHeartbeats 1600000 in
theorem parseFlowSequenceLoop_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (items : Array YamlValue)
    (h_fuel : fuel ≤ n + 1) (h_tok : ps.tokens = tokens)
    (result : Array YamlValue) (ps' : ParseState)
    (h_ok : parseFlowSequenceLoop ps fuel items = .ok (result, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
  | succ k ih_fuel =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    next => -- flowSequenceEnd
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
    next => -- other
      split at h_ok
      · -- items.size > 0
        split at h_ok
        next => -- flowEntry → advance then dispatch
          have h_wfa_adv : WellFormedAnchors ps.advance.anchors := advance_anchors ps ▸ h_wfa
          have h_tok_adv : ps.advance.tokens = tokens := (advance_tokens ps).trans h_tok
          split at h_ok
          next => -- key → parseSinglePairMapping
            split at h_ok
            next => simp at h_ok
            next spm_res heq_spm =>
              obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
              have h_wfa3 := parseSinglePairMapping_wfa h_ih h_wb
                ({ ps.advance with currentPath := _ }) k (by omega)
                (by dsimp only []; exact h_tok_adv)
                mv ps3 (by dsimp only [] at *; exact heq_spm)
                (by dsimp only []; exact h_wfa_adv)
              have h_tok3 := parseSinglePairMapping_tok h_wb
                ({ ps.advance with currentPath := _ }) k (by omega)
                (by dsimp only []; exact h_tok_adv)
                mv ps3 (by dsimp only [] at *; exact heq_spm)
              generalize h_ps_r : { ps3 with currentPath := _ } = ps_r at h_ok
              exact ih_fuel ps_r _ (by omega)
                (by subst h_ps_r; dsimp only []; exact h_tok3) h_ok
                (by subst h_ps_r; dsimp only []; exact h_wfa3)
          next => -- flowSequenceEnd
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact advance_anchors ps ▸ h_wfa
          next => -- other → parseNode
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
              have h_wfa3 := h_ih ({ ps.advance with currentPath := _ }) k v ps3 (by omega)
                (by dsimp only []; exact h_tok_adv)
                (by dsimp only [] at *; exact heq_pn)
                (by dsimp only []; exact h_wfa_adv)
              have h_tok3 := parseNode_tokens_of_wb h_wb
                ({ ps.advance with currentPath := _ }) k (by omega)
                (by dsimp only []; exact h_tok_adv) v ps3
                (by dsimp only [] at *; exact heq_pn)
              generalize h_ps_r : { ps3 with currentPath := _ } = ps_r at h_ok
              exact ih_fuel ps_r _ (by omega)
                (by subst h_ps_r; dsimp only []; exact h_tok3) h_ok
                (by subst h_ps_r; dsimp only []; exact h_wfa3)
        next => -- not flowEntry → early return
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
      · -- items.size = 0
        split at h_ok
        next => -- key → parseSinglePairMapping
          split at h_ok
          next => simp at h_ok
          next spm_res heq_spm =>
            obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
            let ps_wf : ParseState := { ps with currentPath := ps.currentPath.push (.index items.size) }
            have h_wfa3 : WellFormedAnchors ps3.anchors :=
              parseSinglePairMapping_wfa h_ih h_wb ps_wf k (by omega)
                h_tok mv ps3 heq_spm h_wfa
            have h_tok3 : ps3.tokens = tokens :=
              parseSinglePairMapping_tok h_wb ps_wf k (by omega) h_tok mv ps3 heq_spm
            generalize h_ps_r : { ps3 with currentPath := _ } = ps_r at h_ok
            exact ih_fuel ps_r _ (by omega)
              (by subst h_ps_r; dsimp only []; exact h_tok3) h_ok
              (by subst h_ps_r; dsimp only []; exact h_wfa3)
        next => -- flowSequenceEnd
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
        next => -- other → parseNode
          split at h_ok
          next => simp at h_ok
          next pn_res heq_pn =>
            obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
            let ps_wf : ParseState := { ps with currentPath := ps.currentPath.push (.index items.size) }
            have h_wfa3 : WellFormedAnchors ps3.anchors :=
              h_ih ps_wf k v ps3 (by omega) h_tok heq_pn h_wfa
            have h_tok3 : ps3.tokens = tokens :=
              parseNode_tokens_of_wb h_wb ps_wf k (by omega) h_tok v ps3 heq_pn
            generalize h_ps_r : { ps3 with currentPath := _ } = ps_r at h_ok
            exact ih_fuel ps_r _ (by omega)
              (by subst h_ps_r; dsimp only []; exact h_tok3) h_ok
              (by subst h_ps_r; dsimp only []; exact h_wfa3)

-- parseFlowSequence
theorem parseFlowSequence_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseFlowSequence ps fuel = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseFlowSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_wfa_loop := parseFlowSequenceLoop_wfa h_ih h_wb ps.advance k #[] (by omega)
          ((advance_tokens ps).trans h_tok) items ps_loop heq_loop (advance_anchors ps ▸ h_wfa)
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok; obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
        rw [advance_anchors]; exact h_wfa_loop
      · simp at h_ok

-- parseFlowMappingLoop
set_option maxHeartbeats 1600000 in
theorem parseFlowMappingLoop_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue))
    (h_fuel : fuel ≤ n + 1) (h_tok : ps.tokens = tokens)
    (result : Array (YamlValue × YamlValue)) (ps' : ParseState)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok (result, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
  | succ k ih_fuel =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    next => -- flowMappingEnd
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
    next => -- other
      split at h_ok
      · -- pairs.size > 0
        split at h_ok
        next => -- flowEntry → advance then dispatch
          have h_wfa_adv : WellFormedAnchors ps.advance.anchors := advance_anchors ps ▸ h_wfa
          have h_tok_adv : ps.advance.tokens = tokens := (advance_tokens ps).trans h_tok
          split at h_ok
          next => -- flowMappingEnd
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact advance_anchors ps ▸ h_wfa
          next => -- key → advance → parseExplicitKey → FMV → recurse
            have h_wfa_adv2 : WellFormedAnchors ps.advance.advance.anchors := by
              rw [advance_anchors]; exact h_wfa_adv
            have h_tok_adv2 : ps.advance.advance.tokens = tokens :=
              (advance_tokens ps.advance).trans h_tok_adv
            split at h_ok
            next => simp at h_ok
            next ek_res heq_ek =>
              obtain ⟨key_v, ps_ek⟩ := ek_res; dsimp only [] at h_ok
              have h_wfa_ek := parseExplicitKey_wfa h_ih ps.advance.advance k (by omega)
                  h_tok_adv2 key_v ps_ek heq_ek h_wfa_adv2
              have h_tok_ek := parseExplicitKey_tok h_wb ps.advance.advance k (by omega)
                  h_tok_adv2 key_v ps_ek heq_ek
              split at h_ok
              next => simp at h_ok
              next fmv_res heq_fmv =>
                obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
                have h_wfa_fmv := parseFlowMappingValue_wfa h_ih ps_ek k (by omega)
                    h_tok_ek _ _ val_v ps_fmv heq_fmv h_wfa_ek
                have h_tok_fmv := parseFlowMappingValue_tok h_wb ps_ek k (by omega)
                    h_tok_ek _ _ val_v ps_fmv heq_fmv
                exact ih_fuel ps_fmv _ (by omega) h_tok_fmv h_ok h_wfa_fmv
          next => -- other → parseNode → FMV → recurse
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨key_v, ps_pn⟩ := pn_res; dsimp only [] at h_ok
              have h_wfa_pn := h_ih ps.advance k key_v ps_pn (by omega) h_tok_adv heq_pn h_wfa_adv
              have h_tok_pn := parseNode_tokens_of_wb h_wb ps.advance k (by omega) h_tok_adv
                  key_v ps_pn heq_pn
              split at h_ok
              next => simp at h_ok
              next fmv_res heq_fmv =>
                obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
                have h_wfa_fmv := parseFlowMappingValue_wfa h_ih ps_pn k (by omega)
                    h_tok_pn _ _ val_v ps_fmv heq_fmv h_wfa_pn
                have h_tok_fmv := parseFlowMappingValue_tok h_wb ps_pn k (by omega)
                    h_tok_pn _ _ val_v ps_fmv heq_fmv
                exact ih_fuel ps_fmv _ (by omega) h_tok_fmv h_ok h_wfa_fmv
        next => -- not flowEntry → early return
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
      · -- pairs.size = 0
        split at h_ok
        next => -- flowMappingEnd
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok; exact h_wfa
        next => -- key → advance → parseExplicitKey → FMV → recurse
          have h_wfa_adv : WellFormedAnchors ps.advance.anchors := advance_anchors ps ▸ h_wfa
          have h_tok_adv : ps.advance.tokens = tokens := (advance_tokens ps).trans h_tok
          split at h_ok
          next => simp at h_ok
          next ek_res heq_ek =>
            obtain ⟨key_v, ps_ek⟩ := ek_res; dsimp only [] at h_ok
            have h_wfa_ek := parseExplicitKey_wfa h_ih ps.advance k (by omega)
                h_tok_adv key_v ps_ek heq_ek h_wfa_adv
            have h_tok_ek := parseExplicitKey_tok h_wb ps.advance k (by omega)
                h_tok_adv key_v ps_ek heq_ek
            split at h_ok
            next => simp at h_ok
            next fmv_res heq_fmv =>
              obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
              have h_wfa_fmv := parseFlowMappingValue_wfa h_ih ps_ek k (by omega)
                  h_tok_ek _ _ val_v ps_fmv heq_fmv h_wfa_ek
              have h_tok_fmv := parseFlowMappingValue_tok h_wb ps_ek k (by omega)
                  h_tok_ek _ _ val_v ps_fmv heq_fmv
              exact ih_fuel ps_fmv _ (by omega) h_tok_fmv h_ok h_wfa_fmv
        next => -- other → parseNode → FMV → recurse
          split at h_ok
          next => simp at h_ok
          next pn_res heq_pn =>
            obtain ⟨key_v, ps_pn⟩ := pn_res; dsimp only [] at h_ok
            have h_wfa_pn := h_ih ps k key_v ps_pn (by omega) h_tok heq_pn h_wfa
            have h_tok_pn := parseNode_tokens_of_wb h_wb ps k (by omega) h_tok key_v ps_pn heq_pn
            split at h_ok
            next => simp at h_ok
            next fmv_res heq_fmv =>
              obtain ⟨val_v, ps_fmv⟩ := fmv_res; dsimp only [] at h_ok
              have h_wfa_fmv := parseFlowMappingValue_wfa h_ih ps_pn k (by omega)
                  h_tok_pn _ _ val_v ps_fmv heq_fmv h_wfa_pn
              have h_tok_fmv := parseFlowMappingValue_tok h_wb ps_pn k (by omega)
                  h_tok_pn _ _ val_v ps_fmv heq_fmv
              exact ih_fuel ps_fmv _ (by omega) h_tok_fmv h_ok h_wfa_fmv

-- parseFlowMapping
theorem parseFlowMapping_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n) (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n + 1)
    (h_tok : ps.tokens = tokens)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseFlowMapping ps fuel = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseFlowMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs, ps_loop⟩ := loop_res
      dsimp only [] at h_ok
      have h_wfa_loop := parseFlowMappingLoop_wfa h_ih h_wb ps.advance k #[] (by omega)
          ((advance_tokens ps).trans h_tok) pairs ps_loop heq_loop (advance_anchors ps ▸ h_wfa)
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok; obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
        rw [advance_anchors]; exact h_wfa_loop
      · simp at h_ok

-- parseNodeContent dispatches to sub-parsers, each preserving WFA.
theorem parseNodeContent_wfa
    {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWFA tokens n)
    (h_wb : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (h_tok : ps.tokens = tokens)
    (props : NodeProperties) (val : YamlValue) (ps' : ParseState)
    (h_ok : parseNodeContent ps fuel props = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors := by
  unfold parseNodeContent at h_ok
  split at h_ok
  · -- scalar: ps' = ps.advance
    simp only [Except.ok.injEq] at h_ok; obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    rw [advance_anchors]; exact h_wfa
  · exact parseBlockSequence_wfa h_ih h_wb ps fuel (by omega) h_tok _ _ h_ok h_wfa
  · exact parseBlockMapping_wfa h_ih h_wb ps fuel (by omega) h_tok _ _ h_ok h_wfa
  · exact parseImplicitBlockSequence_wfa h_ih h_wb ps fuel (by omega) h_tok _ _ h_ok h_wfa
  · exact parseFlowSequence_wfa h_ih h_wb ps fuel (by omega) h_tok _ _ h_ok h_wfa
  · exact parseFlowMapping_wfa h_ih h_wb ps fuel (by omega) h_tok _ _ h_ok h_wfa
  · -- empty scalar: ps' = ps
    simp only [Except.ok.injEq] at h_ok; obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
    exact h_wfa

-- ============================================================
-- §4  Main theorem: parseNode preserves WFA
-- ============================================================

-- parseNodeProperties doesn't modify anchors.
-- (It only calls advance to skip tag/anchor tokens.)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000000 in
set_option linter.unusedSimpArgs false in
theorem parseNodeProperties_anchors_eq
    (ps : ParseState) (props : NodeProperties) (ps' : ParseState)
    (h : parseNodeProperties ps = .ok (props, ps')) :
    ps'.anchors = ps.anchors := by
  -- Same loop unrolling as parseNodeProperties_tokens (ParserWellBehaved.lean)
  unfold parseNodeProperties at h
  unfold ForIn.forIn instForInOfForIn' at h
  unfold ForIn'.forIn' Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad at h
  unfold Std.Legacy.Range.forIn' at h
  unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [] at h
  unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [] at h
  try unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  try unfold_loop_at h
  try simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  split at h
  · contradiction
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_hfst, rfl⟩ := h
    rename_i heq
    split at heq
    · contradiction
    · rename_i v heq_first
      cases v with
      | done x =>
        simp (config := { iota := true }) only [] at heq
        simp only [Except.ok.injEq] at heq; subst heq
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (try contradiction)
        all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq] at heq_first)
        all_goals (try cases heq_first)
        all_goals (try subst heq_first)
        all_goals (first | rfl | simp [ParseState.advance])
      | yield x =>
        simp (config := { iota := true }) only [] at heq
        split at heq
        · contradiction
        · rename_i v2 heq_second
          cases v2 with
          | done y =>
            simp (config := { iota := true }) only [] at heq
            simp only [Except.ok.injEq] at heq; subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq, ForInStep.yield.injEq] at *)
            all_goals (try subst_vars)
            all_goals (first | rfl | simp [ParseState.advance])
          | yield y =>
            simp only [dite_false] at heq
            simp only [Except.ok.injEq] at heq
            subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq, ForInStep.yield.injEq] at *)
            all_goals (try subst_vars)
            all_goals (first | rfl | simp [ParseState.advance])

set_option maxHeartbeats 800000 in
theorem parseNode_wfa_all
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens) :
    ∀ n, ParseNodeWFA tokens n := by
  intro n
  induction n with
  | zero =>
    intro ps m val ps' h_le h_tok h_ok h_wfa
    have : m = 0 := by omega
    subst this
    simp [parseNode] at h_ok
  | succ n ih =>
    intro ps m val ps' h_le h_tok h_ok h_wfa
    cases m with
    | zero => simp [parseNode] at h_ok
    | succ k =>
      have h_k_le : k ≤ n := by omega
      have h_pnwb : ParseNodeWB tokens n := parseNode_wb_all tokens h_fpsv h_matched n
      unfold parseNode at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok
      split at h_ok
      · -- Alias branch: just advance, anchors unchanged
        split at h_ok <;> first | contradiction | skip
        split at h_ok <;> (
          simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
          exact h_wfa)
      · -- Non-alias: properties → validate → content → finalize
        split at h_ok
        · simp at h_ok
        · rename_i props_res heq_props; obtain ⟨props, ps_props⟩ := props_res
          dsimp only [] at h_ok
          -- parseNodeProperties preserves tokens and anchors
          have h_tok_props : ps_props.tokens = tokens :=
            (parseNodeProperties_tokens ps props ps_props heq_props).trans h_tok
          have h_anch_props := parseNodeProperties_anchors_eq ps props ps_props heq_props
          have h_wfa_props : WellFormedAnchors ps_props.anchors := h_anch_props ▸ h_wfa
          -- validateNodeProps (may throw, doesn't change state)
          split at h_ok <;> first | contradiction | skip
          -- parseNodeContent
          split at h_ok
          · simp at h_ok
          · rename_i content_res heq_content; obtain ⟨val_c, ps_c⟩ := content_res
            dsimp only [] at h_ok
            -- WFA propagation through content
            have h_wfa_c := parseNodeContent_wfa ih h_pnwb ps_props k h_k_le
              h_tok_props props val_c ps_c heq_content h_wfa_props
            -- Scannable from WB
            have h_cwb := parseNodeContent_wb tokens n k h_k_le h_fpsv h_pnwb h_matched
              ps_props props (val_c, ps_c) h_tok_props heq_content
            -- AAR from content_aar
            have h_aar_c := parseNodeContent_aar
              (parseNode_aar_all n) (parseNode_ag_all n)
              ps_props k (by omega) props val_c ps_c heq_content
            -- h_ok: applyNodeFinalization val_c ps_c props nodeStartPos = (val, ps')
            -- (after Except.ok injection)
            simp only [Except.ok.injEq] at h_ok
            have h_ps' : ps' = (applyNodeFinalization val_c ps_c props _).2 :=
              (congrArg Prod.snd h_ok).symm
            rw [h_ps']
            exact applyNodeFinalization_wfa val_c ps_c props _ h_wfa_c h_cwb.1 h_aar_c

-- Extraction: single-call version.
theorem parseNode_wfa
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens)
    (ps : ParseState) (fuel : Nat) (val : YamlValue) (ps' : ParseState)
    (h_tok : ps.tokens = tokens)
    (h_ok : parseNode ps fuel = .ok (val, ps'))
    (h_wfa : WellFormedAnchors ps.anchors) :
    WellFormedAnchors ps'.anchors :=
  parseNode_wfa_all tokens h_fpsv h_matched fuel ps fuel val ps'
    Nat.le.refl h_tok h_ok h_wfa

-- ============================================================
-- §5  prepareDocumentState preserves anchors and tokens
-- ============================================================

/-- `parseDirectives` preserves the anchors array (only `pos` changes). -/
theorem parseDirectives_anchors (ps : ParseState) :
    (parseDirectives ps).2.anchors = ps.anchors := by
  unfold parseDirectives
  simp only [Id.run]
  generalize ps.tokens.size - ps.pos = fuel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
             Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize List.range' 0 fuel 1 = ls
  suffices h : ∀ (acc : MProd (Array Directive) ParseState),
      acc.2.anchors = ps.anchors →
      (Id.run (do
          let r ← @forIn Id (List Nat) Nat _ _ ls acc (fun x r =>
            match r.snd.peek? with
            | some (.versionDirective major minor) => do
              pure PUnit.unit
              pure (ForInStep.yield (MProd.mk (r.fst.push (.yaml (toString major ++ "." ++ toString minor))) r.snd.advance))
            | some (.tagDirective handle tagPrefix) => do
              pure PUnit.unit
              pure (ForInStep.yield (MProd.mk (r.fst.push (.tag handle tagPrefix)) r.snd.advance))
            | _ => pure (ForInStep.done (MProd.mk r.fst r.snd)))
          pure (r.fst, r.snd))).snd.anchors = ps.anchors by
    exact h (MProd.mk #[] ps) rfl
  intro acc h_inv
  induction ls generalizing acc with
  | nil =>
    simp only [Id.run, List.forIn'_nil, ForIn.forIn, bind, pure]
    exact h_inv
  | cons x xs ih =>
    simp only [ForIn.forIn, List.forIn'_cons, Id.run, bind, pure] at ih ⊢
    split
    · rename_i b heq
      revert heq; split
      · intro heq; contradiction
      · intro heq; contradiction
      · intro heq
        have := ForInStep.done.inj heq
        subst this; exact h_inv
    · rename_i b heq
      apply ih; revert heq; split
      · intro heq
        have := ForInStep.yield.inj heq
        subst this; simp [ParseState.advance, h_inv]
      · intro heq
        have := ForInStep.yield.inj heq
        subst this; simp [ParseState.advance, h_inv]
      · intro heq; contradiction

theorem prepareDocumentState_anchors_eq
    (ps : ParseState) (dirs : Array Directive) (ps' : ParseState)
    (h : prepareDocumentState ps = .ok (dirs, ps')) :
    ps'.anchors = ps.anchors := by
  have h_anch :
      ({ (parseDirectives ps).2 with
          tagHandles := (parseDirectives ps).1.filterMap fun
            | Directive.tag handle tagPrefix => some (handle, tagPrefix)
            | _ => none }.tryConsume .documentStart).2.anchors = ps.anchors := by
    calc
      ({ (parseDirectives ps).2 with
          tagHandles := (parseDirectives ps).1.filterMap fun
            | Directive.tag handle tagPrefix => some (handle, tagPrefix)
            | _ => none }.tryConsume .documentStart).2.anchors
          = ({ (parseDirectives ps).2 with
                tagHandles := (parseDirectives ps).1.filterMap fun
                  | Directive.tag handle tagPrefix => some (handle, tagPrefix)
                  | _ => none }).anchors :=
              tryConsume_snd_anchors _ _
      _ = (parseDirectives ps).2.anchors := rfl
      _ = ps.anchors := parseDirectives_anchors ps
  unfold prepareDocumentState at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  all_goals (first | split at h | skip)
  all_goals (first | split at h | skip)
  all_goals (first | split at h | skip)
  all_goals (first | split at h | skip)
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h)
  all_goals (
    obtain ⟨_, rfl⟩ := h
    exact h_anch)

theorem prepareDocumentState_tokens_eq
    (ps : ParseState) (dirs : Array Directive) (ps' : ParseState)
    (h : prepareDocumentState ps = .ok (dirs, ps')) :
    ps'.tokens = ps.tokens :=
  prepareDocumentState_tokens_preserved ps dirs ps' h

-- ============================================================
-- §6  parseDocument produces WFA anchors
-- ============================================================

theorem parseDocument_wfa
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens)
    (ps : ParseState) (doc : YamlDocument) (ps' : ParseState)
    (h_tok : ps.tokens = tokens)
    (h_wfa : WellFormedAnchors ps.anchors)
    (h_ok : parseDocument ps = .ok (doc, ps')) :
    WellFormedAnchors doc.anchors := by
  unfold parseDocument at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i prep_result h_prep
    obtain ⟨dirs, ps1⟩ := prep_result
    dsimp only [] at h_ok
    have h_prep_tok : ps1.tokens = tokens :=
      (prepareDocumentState_tokens_eq ps dirs ps1 h_prep).trans h_tok
    have h_prep_anch : ps1.anchors = ps.anchors :=
      prepareDocumentState_anchors_eq ps dirs ps1 h_prep
    have h_wfa_ps1 : WellFormedAnchors ps1.anchors := h_prep_anch ▸ h_wfa
    -- split on match ps1.peek?: emptyNode arms vs parseNode arm
    split at h_ok
    all_goals (try (
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := h_ok
      dsimp only []
      exact h_wfa_ps1))
    -- remaining: parseNode arm
    split at h_ok
    · simp at h_ok
    · rename_i node_result h_pn
      obtain ⟨val, ps2⟩ := node_result
      dsimp only [] at h_ok
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok
      obtain ⟨rfl, rfl⟩ := h_ok
      dsimp only []
      exact parseNode_wfa tokens h_fpsv h_matched ps1 (4 * ps1.tokens.size + 4)
        val ps2 h_prep_tok h_pn h_wfa_ps1

-- ============================================================
-- §7  parseStream produces documents with WFA anchors
-- ============================================================

-- parseDocument preserves tokens (for stream loop token threading).
theorem parseDocument_tokens_eq
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens)
    (ps : ParseState) (doc : YamlDocument) (ps' : ParseState)
    (h_tok : ps.tokens = tokens)
    (h_ok : parseDocument ps = .ok (doc, ps')) :
    ps'.tokens = ps.tokens :=
  parseDocument_tokens_preserved ps doc ps' (h_tok ▸ h_fpsv) (h_tok ▸ h_matched) h_ok

-- tryConsume preserves tokens and anchors.
theorem tryConsume_tokens_wfa (ps : ParseState) (tok : YamlToken) :
    (ps.tryConsume tok).2.tokens = ps.tokens := by
  unfold ParseState.tryConsume; split <;> (try split) <;> simp [ParseState.advance]

theorem tryConsume_anchors_wfa (ps : ParseState) (tok : YamlToken) :
    (ps.tryConsume tok).2.anchors = ps.anchors := by
  unfold ParseState.tryConsume; split <;> (try split) <;> simp [ParseState.advance]

-- expect preserves tokens.
theorem expect_tokens_wfa (ps : ParseState) (tok : YamlToken) (msg : String)
    (ps' : ParseState)
    (h : ps.expect tok msg = .ok ps') :
    ps'.tokens = ps.tokens := by
  unfold ParseState.expect at h
  split at h
  · -- some case: if t = tok then ok advance else error
    split at h
    · simp only [Except.ok.injEq] at h; subst h; simp [ParseState.advance]
    · simp at h
  · -- none case: error = ok ps'
    simp at h

theorem parseStreamLoop_wfa
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens)
    (ps : ParseState) (docs : Array YamlDocument)
    (streamState : StreamState) (fuel : Nat)
    (h_tok : ps.tokens = tokens)
    (h_wfa_ps : WellFormedAnchors ps.anchors)
    (h_acc : ∀ doc ∈ docs.toList, WellFormedAnchors doc.anchors)
    (result : Array YamlDocument)
    (h_ok : parseStreamLoop ps docs streamState fuel = .ok result) :
    ∀ doc ∈ result.toList, WellFormedAnchors doc.anchors := by
  induction fuel generalizing ps docs streamState with
  | zero =>
    simp only [parseStreamLoop] at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
  | succ fuel ih =>
    unfold parseStreamLoop at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
    · -- some tok
      split at h_ok
      · simp at h_ok -- invalid token → error
      · -- valid token → parseDocument
        generalize h_pd : parseDocument ps = pd_result at h_ok
        cases pd_result with
        | error e => simp at h_ok
        | ok val =>
          obtain ⟨doc_new, ps_doc⟩ := val
          dsimp only [] at h_ok
          have h_wfa_doc : WellFormedAnchors doc_new.anchors :=
            parseDocument_wfa tokens h_fpsv h_matched ps doc_new ps_doc
              h_tok h_wfa_ps h_pd
          have h_acc' : ∀ doc ∈ (docs.push doc_new).toList, WellFormedAnchors doc.anchors := by
            intro d hd
            rw [Array.toList_push] at hd
            simp only [List.mem_append, List.mem_singleton] at hd
            rcases hd with hd_old | rfl
            · exact h_acc d hd_old
            · exact h_wfa_doc
          have h_tok_doc : ps_doc.tokens = tokens :=
            (parseDocument_tokens_eq tokens h_fpsv h_matched ps doc_new ps_doc h_tok h_pd).trans h_tok
          -- Position check → return or recurse
          split at h_ok
          · -- pos == savedPos: return docs'
            simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc'
          · -- recurse with reset anchors + tryConsume
            apply ih
            · -- tokens preserved
              exact (tryConsume_tokens_wfa
                { ps_doc with anchors := #[], nodePositions := #[], currentPath := #[] }
                .documentEnd).trans h_tok_doc
            · -- well-formed anchors after reset + tryConsume
              have h_eq := tryConsume_anchors_wfa
                { ps_doc with anchors := #[], nodePositions := #[], currentPath := #[] }
                .documentEnd
              simp only [h_eq]; exact WFA_empty
            · exact h_acc'
            · exact h_ok

-- The final theorem: parse stream output has well-formed anchors.
theorem parseStream_output_anchors_wellformed
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, WellFormedAnchors doc.anchors := by
  unfold parseStream at h_parse
  simp only [bind, Except.bind] at h_parse
  split at h_parse
  · simp at h_parse
  · rename_i ps_init heq_expect
    have h_tok_init : ps_init.tokens = tokens :=
      expect_tokens_wfa { tokens := tokens, trackPositions := false } .streamStart _ ps_init heq_expect
    have h_wfa_init : WellFormedAnchors ps_init.anchors := by
      have : ps_init.anchors = #[] := by
        unfold ParseState.expect at heq_expect
        split at heq_expect
        · -- some case: split the if
          split at heq_expect
          · simp only [Except.ok.injEq] at heq_expect; subst heq_expect
            simp [ParseState.advance]
          · simp at heq_expect
        · -- none case: contradiction
          simp at heq_expect
      rw [this]; exact WFA_empty
    apply parseStreamLoop_wfa tokens h_fpsv h_matched ps_init #[] .initial tokens.size
      h_tok_init h_wfa_init
    · intro doc hd; simp at hd
    · exact h_parse

end L4YAML.Proofs.ParserGrammable
