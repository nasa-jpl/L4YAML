/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Parser.ParserScannableBase
public import L4YAML.Parser.Composition
public import L4YAML.Algebra.Value

@[expose] public section Blanket

/-!
# The `Scannable`-valued parse-side anchor table

`ParserScannableBase` mirrors the COMPOSE chain: `resolveAliasesOrdered` reads
the threaded environment, so `WellFormedEnvS` is the only well-formedness
hypothesis it needs.  The PARSE side has a second table — `ParseState.anchors`,
written by `ParseState.addAnchor` at node finalization and read by
`resolveAliases` — and `WellFormedAnchors` requires every value in it to be
`Grammable` after stripping.

That is false for a node that has itself as a descendant via an alias.
`&x [*x]` binds `x` to a value which still carries `.alias "x"`, and `Grammable`
has no alias constructor at all, so the parse-side predicate cannot hold of the
table the parser actually builds for that input — see
`Tests/Guards/Proofs/AliasNodeRoute.lean`, where both halves of that are
machine-checked (`alias_not_grammable`, `selfDesc_not_aar`).

This module mirrors the parse-side table onto `Scannable`, which is `Grammable`
plus the `| alias` constructor.  Each declaration below is its `Grammable`
original with the predicate renamed, and **one carries new content**:
`compose_value_scannable` takes no `AllAliasesResolve` hypothesis.  Its
`Grammable` original needs one because its alias case has to *find* the resolved
value before `WellFormedAnchors` can speak about it; the mirror splits on the
lookup instead and closes the missing branch with `Scannable.alias`.  That is
the whole difference, and it is why the mirror can carry a shape the original
refuses: the parse-time table legitimately misses for a self-descendant node,
because a collection's anchor binds only after its items are resolved.
-/

namespace L4YAML.Proofs.ParserGrammable

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Algebra.Value

/-- The `Scannable`-valued mirror of `WellFormedAnchors`: every value in the
    parse-side anchor table is `Scannable` after stripping, at every flow
    context. -/
def WellFormedAnchorsS (anchors : Array (String × YamlValue)) : Prop :=
  ∀ (name : String) (val : YamlValue),
    anchors.findSome? (fun (n, v) => if n == name then some v else none) = some val →
      ∀ inFlow, Scannable val.stripAnchors inFlow

/-- C1 for the parse-side table, **with no `AllAliasesResolve` hypothesis**.

    The alias case splits on the lookup rather than being handed a witness that
    it succeeds: where the table has the name, `WellFormedAnchorsS` speaks about
    the value it found; where it misses, `resolveAliases` returns the alias
    itself and `Scannable.alias` carries it.  The missing branch is exactly the
    self-descendant node, and it is unreachable in the `Grammable` original —
    which is why that original can demand resolution and this mirror cannot. -/
lemma compose_value_scannable
    (v : YamlValue) (anchors : Array (String × YamlValue)) (inFlow : Bool)
    (h_scan : Scannable v inFlow)
    (h_anchors : WellFormedAnchorsS anchors) :
    Scannable (v.resolveAliases anchors).stripAnchors inFlow := by
  induction h_scan with
  | scalar s inFlow h_ss =>
    exact .scalar { s with anchor := none } inFlow
      ((ScalarScannable_strip_anchor s inFlow).mp h_ss)
  | alias name inFlow =>
    have h_eq : (YamlValue.alias name).resolveAliases anchors =
      (match anchors.findSome? (fun (n, v) => if n == name then some v else none) with
       | some v => v | none => .alias name) := rfl
    rw [h_eq]
    cases h_find : anchors.findSome? (fun (n, v) => if n == name then some v else none) with
    | some resolved => exact h_anchors name resolved h_find inFlow
    | none => exact .alias name inFlow
  | sequence style items tag anchor inFlow h_items ih_items =>
    show Scannable (.sequence style
      (YamlValue.stripAnchors.stripList
        (YamlValue.resolveAliases.resolveList items.toList anchors).toArray.toList).toArray
      tag none) inFlow
    rw [List.toList_toArray, stripList_eq_map, resolveList_eq_map]
    apply Scannable.sequence
    intro ⟨i, hi⟩
    simp at hi ⊢
    exact ih_items ⟨i, hi⟩
  | mapping style pairs tag anchor inFlow hk hv ih_k ih_v =>
    show Scannable (.mapping style
      (YamlValue.stripAnchors.stripPairs
        (YamlValue.resolveAliases.resolvePairs pairs.toList anchors).toArray.toList).toArray
      tag none) inFlow
    rw [List.toList_toArray, stripPairs_eq_map, resolvePairs_eq_map]
    apply Scannable.mapping
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_k ⟨i, hi⟩
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_v ⟨i, hi⟩

/-- `WellFormedAnchorsS` survives a push whose value is universally `Scannable`
    after stripping. -/
lemma WFAS_of_push (anchors : Array (String × YamlValue))
    (entry : String × YamlValue)
    (h_wfa : WellFormedAnchorsS anchors)
    (h_new : ∀ inFlow, Scannable entry.2.stripAnchors inFlow) :
    WellFormedAnchorsS (anchors.push entry) := by
  intro name val h_find inFlow
  rw [Array.findSome?_push] at h_find
  generalize hg : anchors.findSome? (fun x =>
    match x with | (n, v) => if n == name then some v else none) = found at h_find
  cases found with
  | some v' =>
    dsimp only [Option.or] at h_find
    injection h_find with h_eq; subst h_eq
    exact h_wfa name v' hg inFlow
  | none =>
    dsimp only [Option.or] at h_find
    split at h_find
    · injection h_find with h_eq; subst h_eq; exact h_new inFlow
    · simp at h_find

/-- strip + `adaptForFlowContext` + compose gives universally-`Scannable`
    values after stripping — the shape `addAnchor` stores, as `WFAS_of_push`
    wants it.  Stated on the TABLE rather than on a parser state, so the legacy
    and indexed twins share it; their states differ and their anchor tables do
    not. -/
lemma cleaned_scannable_forall
    (val : YamlValue) (anchors : Array (String × YamlValue))
    (h_scannable : Scannable val false)
    (h_wfa : WellFormedAnchorsS anchors) :
    ∀ inFlow,
      Scannable (((val.stripAnchors.adaptForFlowContext).resolveAliases anchors).stripAnchors)
        inFlow :=
  fun inFlow =>
    compose_value_scannable _ anchors inFlow
      (adaptForFlowContext_scannable_forall _ _
        (stripAnchors_preserves_Scannable val false h_scannable) inFlow)
      h_wfa

/-- `addAnchor` preserves `WellFormedAnchorsS`. -/
lemma addAnchor_wfaS (ps : ParseState) (name : String) (val : YamlValue)
    (h_wfa : WellFormedAnchorsS ps.anchors)
    (h_scan : ∀ inFlow,
      Scannable (((val.stripAnchors.adaptForFlowContext).resolveAliases ps.anchors).stripAnchors)
        inFlow) :
    WellFormedAnchorsS (ps.addAnchor name val).anchors := by
  rw [ParseState.addAnchor_anchors]
  exact WFAS_of_push _ _ h_wfa h_scan

/-- **The lemma the parse-side clique turns on**, mirrored: node finalization
    preserves `WellFormedAnchorsS` given only that the finalized value is
    `Scannable`.  Its `Grammable` original additionally takes
    `AllAliasesResolve val ps.anchors`, and that premise is false exactly where
    this mirror is needed. -/
lemma applyNodeFinalization_wfaS
    (val : YamlValue) (ps : ParseState) (props : NodeProperties) (nodeStartPos : YamlPos)
    (h_wfa : WellFormedAnchorsS ps.anchors)
    (h_scannable : Scannable val false) :
    WellFormedAnchorsS (applyNodeFinalization val ps props nodeStartPos).2.anchors := by
  rcases props with ⟨anchor, tag, dup⟩
  cases anchor with
  | none =>
    simp only [applyNodeFinalization]
    split <;> exact h_wfa
  | some name =>
    cases val with
    | scalar s =>
      simp only [applyNodeFinalization]
      split <;> exact addAnchor_wfaS ps name _ h_wfa
        (cleaned_scannable_forall _ ps.anchors h_scannable h_wfa)
    | alias a =>
      simp only [applyNodeFinalization]
      split <;> exact addAnchor_wfaS ps name _ h_wfa
        (cleaned_scannable_forall _ ps.anchors h_scannable h_wfa)
    | sequence style items otag oanchor =>
      cases otag <;> cases oanchor <;> simp only [applyNodeFinalization] <;> split
      all_goals (first
        | exact addAnchor_wfaS ps name _ h_wfa
            (cleaned_scannable_forall _ ps.anchors h_scannable h_wfa)
        | (exact addAnchor_wfaS ps name _ h_wfa
            (cleaned_scannable_forall _ ps.anchors
              (.sequence _ _ _ _ _
                (by cases h_scannable with | sequence _ _ _ _ _ h => exact h))
              h_wfa)))
    | mapping style pairs otag oanchor =>
      cases otag <;> cases oanchor <;> simp only [applyNodeFinalization] <;> split
      all_goals (first
        | exact addAnchor_wfaS ps name _ h_wfa
            (cleaned_scannable_forall _ ps.anchors h_scannable h_wfa)
        | (exact addAnchor_wfaS ps name _ h_wfa
            (cleaned_scannable_forall _ ps.anchors
              (.mapping _ _ _ _ _
                (by cases h_scannable with | mapping _ _ _ _ _ hk _ => exact hk)
                (by cases h_scannable with | mapping _ _ _ _ _ _ hv => exact hv))
              h_wfa)))

end L4YAML.Proofs.ParserGrammable

end Blanket
