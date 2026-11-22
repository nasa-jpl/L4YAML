/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Parser.ParserGrammableBase

@[expose] public section Blanket

/-! # Value Algebra for `YamlValue`  (Algebra Items 18–21)

Algebraic properties of `stripAnchors` and `adaptForFlowContext`:

- **Item 18** — `stripAnchors_idempotent`
- **Item 19** — `adaptForFlowContext_idempotent`
- **Item 20** — `stripAnchors ∘ adaptForFlowContext` commutativity
- **Item 21** — pipeline idempotence: `(strip ∘ adapt)² = strip ∘ adapt`
- **§7** — `strip` and `adapt` commute with `resolveAliases` over a table
  of cleaned values (`cleaned_resolveAliases_comm`)

These properties justify the `addAnchor` pipeline in `ParseStateIx.lean`
and `Parser/State.lean`:
  `cleaned = (val.stripAnchors.adaptForFlowContext).resolveAliases ps.anchors`
ensure `WellFormedAnchors` is preserved when re-processing anchor values, and
show (§7) that cleaning the raw value first — linear in the anchor's own
syntax, sharing the substituted subtrees — stores exactly the value the
resolve-first order `(val.resolveAliases A).stripAnchors.adaptForFlowContext`
would have, so the reorder is a pure cost change.

## Provenance

Migrated from `L4YAML/Proofs/Foundation/ValueAlgebra.lean` during
Initiative 4 Phase 2 (D4: one file per item-cluster). No semantic
change; namespace move only — the namespace changes from
`L4YAML.Proofs.ValueAlgebra` to `L4YAML.Algebra.Value`.
-/

set_option autoImplicit false
open L4YAML L4YAML.Proofs.ParserGrammable

namespace L4YAML.Algebra.Value

-- ============================================================
-- §1 Per-constructor reduction lemmas
-- ============================================================

@[simp] lemma stripAnchors_scalar' (s : Scalar) :
    (YamlValue.scalar s).stripAnchors = .scalar { s with anchor := none } := rfl

@[simp] lemma adaptForFlowContext_scalar' (s : Scalar) :
    (YamlValue.scalar s).adaptForFlowContext =
    if s.style == .plain && hasFlowIndicator s.content.toList
    then .scalar { s with style := .doubleQuoted }
    else .scalar s := rfl

-- ============================================================
-- §2 sizeOf helpers for termination
-- ============================================================

-- For nested inductives, omega cannot connect `sizeOf x < sizeOf items`
-- to `sizeOf x < sizeOf (.sequence style items tag anchor)`.
-- The auto-generated `sizeOf_spec` lemmas bridge this gap.

lemma sizeOf_lt_of_mem_toList {v : YamlValue} {items : Array YamlValue}
    (h : v ∈ items.toList) : sizeOf v < sizeOf items :=
  Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp h)

lemma sizeOf_pair_lt_of_mem_toList {p : YamlValue × YamlValue}
    {pairs : Array (YamlValue × YamlValue)} (h : p ∈ pairs.toList) :
    sizeOf p.1 < sizeOf pairs ∧ sizeOf p.2 < sizeOf pairs := by
  have hm := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp h)
  have : sizeOf p = 1 + sizeOf p.1 + sizeOf p.2 := by obtain ⟨k, v⟩ := p; rfl
  constructor <;> omega

-- Shared decreasing_by tactic for all recursive proofs on YamlValue
local macro "yaml_decreasing" : tactic =>
  `(tactic| all_goals (
    simp only [YamlValue.sequence.sizeOf_spec, YamlValue.mapping.sizeOf_spec,
      Prod.fst, Prod.snd] at *; omega))

-- ============================================================
-- §3 Item 18 — stripAnchors is idempotent
-- ============================================================

lemma stripAnchors_idempotent (v : YamlValue) :
    v.stripAnchors.stripAnchors = v.stripAnchors := by
  match v with
  | .scalar _ => rfl
  | .alias _ => rfl
  | .sequence style items tag _ =>
    show YamlValue.sequence style
      (YamlValue.stripAnchors.stripList (YamlValue.stripAnchors.stripList items.toList).toArray.toList).toArray tag none =
      YamlValue.sequence style (YamlValue.stripAnchors.stripList items.toList).toArray tag none
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, stripList_eq_map, stripList_eq_map, List.map_map]
    exact List.map_congr_left fun x hx =>
      have := sizeOf_lt_of_mem_toList hx; stripAnchors_idempotent x
  | .mapping style pairs tag _ =>
    show YamlValue.mapping style
      (YamlValue.stripAnchors.stripPairs (YamlValue.stripAnchors.stripPairs pairs.toList).toArray.toList).toArray tag none =
      YamlValue.mapping style (YamlValue.stripAnchors.stripPairs pairs.toList).toArray tag none
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, stripPairs_eq_map, stripPairs_eq_map, List.map_map]
    apply List.map_congr_left
    intro ⟨k, w⟩ hkw
    have ⟨hk, hw⟩ := sizeOf_pair_lt_of_mem_toList hkw
    simp only [Function.comp]
    exact Prod.ext (stripAnchors_idempotent k) (stripAnchors_idempotent w)
termination_by sizeOf v
decreasing_by yaml_decreasing

-- ============================================================
-- §4 Item 20 — stripAnchors and adaptForFlowContext commute
-- ============================================================

lemma stripAnchors_adaptForFlowContext_comm (v : YamlValue) :
    v.adaptForFlowContext.stripAnchors = v.stripAnchors.adaptForFlowContext := by
  match v with
  | .scalar s =>
    simp only [adaptForFlowContext_scalar', stripAnchors_scalar']
    rw [apply_ite YamlValue.stripAnchors]
    simp only [stripAnchors_scalar']
  | .alias _ => rfl
  | .sequence style items tag anchor =>
    show YamlValue.sequence style
        (YamlValue.stripAnchors.stripList (YamlValue.adaptForFlowContext.adaptList items.toList).toArray.toList).toArray tag none =
      YamlValue.sequence style
        (YamlValue.adaptForFlowContext.adaptList (YamlValue.stripAnchors.stripList items.toList).toArray.toList).toArray tag none
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, adaptList_eq_map, stripList_eq_map, List.map_map,
        List.toList_toArray, stripList_eq_map, adaptList_eq_map, List.map_map]
    exact List.map_congr_left fun x hx =>
      have := sizeOf_lt_of_mem_toList hx
      stripAnchors_adaptForFlowContext_comm x
  | .mapping style pairs tag anchor =>
    show YamlValue.mapping style
        (YamlValue.stripAnchors.stripPairs (YamlValue.adaptForFlowContext.adaptPairs pairs.toList).toArray.toList).toArray tag none =
      YamlValue.mapping style
        (YamlValue.adaptForFlowContext.adaptPairs (YamlValue.stripAnchors.stripPairs pairs.toList).toArray.toList).toArray tag none
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, adaptPairs_eq_map, stripPairs_eq_map, List.map_map,
        List.toList_toArray, stripPairs_eq_map, adaptPairs_eq_map, List.map_map]
    apply List.map_congr_left
    intro ⟨k, w⟩ hkw
    have ⟨hk, hw⟩ := sizeOf_pair_lt_of_mem_toList hkw
    simp only [Function.comp]
    exact Prod.ext (stripAnchors_adaptForFlowContext_comm k)
                    (stripAnchors_adaptForFlowContext_comm w)
termination_by sizeOf v
decreasing_by yaml_decreasing

-- ============================================================
-- §5 Item 19 — adaptForFlowContext is idempotent
-- ============================================================

lemma adaptForFlowContext_idempotent (v : YamlValue) :
    v.adaptForFlowContext.adaptForFlowContext = v.adaptForFlowContext := by
  match v with
  | .scalar s =>
    simp only [adaptForFlowContext_scalar']
    split
    · simp only [adaptForFlowContext_scalar']
      simp (config := { decide := true })
    · -- isFalse branch → second adaptForFlowContext
      simp only [adaptForFlowContext_scalar']
      split
      · rename_i h1 h2; simp_all
      · rfl
  | .alias _ => rfl
  | .sequence style items tag anchor =>
    show YamlValue.sequence style
        (YamlValue.adaptForFlowContext.adaptList (YamlValue.adaptForFlowContext.adaptList items.toList).toArray.toList).toArray tag anchor =
      YamlValue.sequence style
        (YamlValue.adaptForFlowContext.adaptList items.toList).toArray tag anchor
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, adaptList_eq_map, adaptList_eq_map, List.map_map]
    exact List.map_congr_left fun x hx =>
      have := sizeOf_lt_of_mem_toList hx; adaptForFlowContext_idempotent x
  | .mapping style pairs tag anchor =>
    show YamlValue.mapping style
        (YamlValue.adaptForFlowContext.adaptPairs (YamlValue.adaptForFlowContext.adaptPairs pairs.toList).toArray.toList).toArray tag anchor =
      YamlValue.mapping style
        (YamlValue.adaptForFlowContext.adaptPairs pairs.toList).toArray tag anchor
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, adaptPairs_eq_map, adaptPairs_eq_map, List.map_map]
    apply List.map_congr_left
    intro ⟨k, w⟩ hkw
    have ⟨hk, hw⟩ := sizeOf_pair_lt_of_mem_toList hkw
    simp only [Function.comp]
    exact Prod.ext (adaptForFlowContext_idempotent k) (adaptForFlowContext_idempotent w)
termination_by sizeOf v
decreasing_by yaml_decreasing

-- ============================================================
-- §6 Item 21 — Pipeline corollaries
-- ============================================================

-- The cleaning pipeline stripAnchors → adaptForFlowContext
-- Applied twice (strip ∘ adapt ∘ strip ∘ adapt) = once (strip ∘ adapt)
lemma stripAnchors_adaptForFlowContext_pipeline_idempotent (v : YamlValue) :
    (v.stripAnchors.adaptForFlowContext).stripAnchors.adaptForFlowContext =
    v.stripAnchors.adaptForFlowContext := by
  rw [stripAnchors_adaptForFlowContext_comm]
  rw [stripAnchors_idempotent]
  rw [adaptForFlowContext_idempotent]

-- After stripping a cleaned value, we get the cleaned value back.
-- Key for WellFormedAnchors preservation: the stored value `cleaned = strip(adapt(v))`
-- satisfies `cleaned.stripAnchors = cleaned`.
lemma stripAnchors_of_cleaned (v : YamlValue) :
    (v.stripAnchors.adaptForFlowContext).stripAnchors =
    v.stripAnchors.adaptForFlowContext := by
  rw [stripAnchors_adaptForFlowContext_comm, stripAnchors_idempotent]

-- ============================================================
-- §7 Cleaning commutes with alias substitution over a cleaned table
-- ============================================================

/-- A value `stripAnchors ∘ adaptForFlowContext` leaves fixed — the shape every
    entry of the parse-side anchor table has. -/
def Cleaned (v : YamlValue) : Prop :=
  v.stripAnchors.adaptForFlowContext = v

lemma Cleaned.stripAnchors_eq {v : YamlValue} (h : Cleaned v) : v.stripAnchors = v := by
  have := stripAnchors_of_cleaned v
  rw [h] at this
  exact this

lemma Cleaned.adaptForFlowContext_eq {v : YamlValue} (h : Cleaned v) :
    v.adaptForFlowContext = v :=
  calc v.adaptForFlowContext
      = (v.stripAnchors.adaptForFlowContext).adaptForFlowContext := by rw [h]
    _ = v.stripAnchors.adaptForFlowContext := adaptForFlowContext_idempotent _
    _ = v := h

lemma cleaned_of_pipeline (v : YamlValue) : Cleaned (v.stripAnchors.adaptForFlowContext) :=
  stripAnchors_adaptForFlowContext_pipeline_idempotent v

/-- A successful first-match lookup returns a table entry's value. -/
lemma mem_of_findSome?_eq_some {A : Array (String × YamlValue)} {name : String}
    {val : YamlValue}
    (h : A.findSome? (fun (n, v) => if n == name then some v else none) = some val) :
    ∃ p ∈ A, p.2 = val := by
  obtain ⟨⟨n, v⟩, hmem, hf⟩ := Array.exists_of_findSome?_eq_some h
  refine ⟨(n, v), hmem, ?_⟩
  by_cases hn : (n == name) = true
  · simp only [hn, ite_true, Option.some.injEq] at hf
    exact hf
  · simp [hn] at hf

/-- `stripAnchors` commutes with `resolveAliases` when every table value is
    already anchor-free: `.alias` nodes are untouched by `stripAnchors`, and a
    substituted value is its own `stripAnchors`. -/
lemma stripAnchors_resolveAliases (v : YamlValue) (A : Array (String × YamlValue))
    (hA : ∀ p ∈ A, p.2.stripAnchors = p.2) :
    (v.resolveAliases A).stripAnchors = v.stripAnchors.resolveAliases A := by
  match v with
  | .scalar s =>
    simp only [YamlValue.resolveAliases, stripAnchors_scalar']
  | .alias name =>
    have hs : (YamlValue.alias name).stripAnchors = .alias name := rfl
    rw [hs]
    unfold YamlValue.resolveAliases
    cases h_find : A.findSome? (fun (n, v) => if n == name then some v else none) with
    | some val =>
      simp only
      obtain ⟨p, hp, hpv⟩ := mem_of_findSome?_eq_some h_find
      rw [← hpv]; exact hA p hp
    | none => simp only; exact hs
  | .sequence style items tag anchor =>
    show YamlValue.sequence style
        (YamlValue.stripAnchors.stripList
          (YamlValue.resolveAliases.resolveList items.toList A).toArray.toList).toArray tag none =
      YamlValue.sequence style
        (YamlValue.resolveAliases.resolveList
          (YamlValue.stripAnchors.stripList items.toList).toArray.toList A).toArray tag none
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, stripList_eq_map, resolveList_eq_map, List.map_map,
        List.toList_toArray, resolveList_eq_map, stripList_eq_map, List.map_map]
    exact List.map_congr_left fun x hx =>
      have := sizeOf_lt_of_mem_toList hx
      stripAnchors_resolveAliases x A hA
  | .mapping style pairs tag anchor =>
    show YamlValue.mapping style
        (YamlValue.stripAnchors.stripPairs
          (YamlValue.resolveAliases.resolvePairs pairs.toList A).toArray.toList).toArray tag none =
      YamlValue.mapping style
        (YamlValue.resolveAliases.resolvePairs
          (YamlValue.stripAnchors.stripPairs pairs.toList).toArray.toList A).toArray tag none
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, stripPairs_eq_map, resolvePairs_eq_map, List.map_map,
        List.toList_toArray, resolvePairs_eq_map, stripPairs_eq_map, List.map_map]
    apply List.map_congr_left
    intro ⟨k, w⟩ hkw
    have ⟨hk, hw⟩ := sizeOf_pair_lt_of_mem_toList hkw
    simp only [Function.comp]
    exact Prod.ext (stripAnchors_resolveAliases k A hA) (stripAnchors_resolveAliases w A hA)
termination_by sizeOf v
decreasing_by yaml_decreasing

/-- `adaptForFlowContext` commutes with `resolveAliases` when every table value
    is already flow-adapted. -/
lemma adaptForFlowContext_resolveAliases (v : YamlValue) (A : Array (String × YamlValue))
    (hA : ∀ p ∈ A, p.2.adaptForFlowContext = p.2) :
    (v.resolveAliases A).adaptForFlowContext = v.adaptForFlowContext.resolveAliases A := by
  match v with
  | .scalar s =>
    simp only [YamlValue.resolveAliases, adaptForFlowContext_scalar']
    split <;> simp only [YamlValue.resolveAliases]
  | .alias name =>
    have hs : (YamlValue.alias name).adaptForFlowContext = .alias name := rfl
    rw [hs]
    unfold YamlValue.resolveAliases
    cases h_find : A.findSome? (fun (n, v) => if n == name then some v else none) with
    | some val =>
      simp only
      obtain ⟨p, hp, hpv⟩ := mem_of_findSome?_eq_some h_find
      rw [← hpv]; exact hA p hp
    | none => simp only; exact hs
  | .sequence style items tag anchor =>
    show YamlValue.sequence style
        (YamlValue.adaptForFlowContext.adaptList
          (YamlValue.resolveAliases.resolveList items.toList A).toArray.toList).toArray tag anchor =
      YamlValue.sequence style
        (YamlValue.resolveAliases.resolveList
          (YamlValue.adaptForFlowContext.adaptList items.toList).toArray.toList A).toArray tag anchor
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, adaptList_eq_map, resolveList_eq_map, List.map_map,
        List.toList_toArray, resolveList_eq_map, adaptList_eq_map, List.map_map]
    exact List.map_congr_left fun x hx =>
      have := sizeOf_lt_of_mem_toList hx
      adaptForFlowContext_resolveAliases x A hA
  | .mapping style pairs tag anchor =>
    show YamlValue.mapping style
        (YamlValue.adaptForFlowContext.adaptPairs
          (YamlValue.resolveAliases.resolvePairs pairs.toList A).toArray.toList).toArray tag anchor =
      YamlValue.mapping style
        (YamlValue.resolveAliases.resolvePairs
          (YamlValue.adaptForFlowContext.adaptPairs pairs.toList).toArray.toList A).toArray tag anchor
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, adaptPairs_eq_map, resolvePairs_eq_map, List.map_map,
        List.toList_toArray, resolvePairs_eq_map, adaptPairs_eq_map, List.map_map]
    apply List.map_congr_left
    intro ⟨k, w⟩ hkw
    have ⟨hk, hw⟩ := sizeOf_pair_lt_of_mem_toList hkw
    simp only [Function.comp]
    exact Prod.ext (adaptForFlowContext_resolveAliases k A hA)
      (adaptForFlowContext_resolveAliases w A hA)
termination_by sizeOf v
decreasing_by yaml_decreasing

/-- **The `addAnchor` reorder is exact.**  Over a table of cleaned values,
    resolving first and cleaning the (expanded) result is the same value as
    cleaning the raw value and resolving afterwards.  The right-hand side is
    what `addAnchor` stores: it walks only the anchor's own syntax and shares
    every substituted subtree, where the left-hand side rebuilds the whole
    expansion.

    Chain (Rule 1): the specification of `addAnchor`'s order in both parser
    states; the capstones that read the anchor table (`parse_sound_*`,
    `parse_complete`, `universal_roundtrip`'s alias path) hold for the
    linear-cost order by this equation — see `Blueprint/04-capstones.md`,
    "Significance & risk". -/
lemma cleaned_resolveAliases_comm (v : YamlValue) (A : Array (String × YamlValue))
    (hA : ∀ p ∈ A, Cleaned p.2) :
    (v.resolveAliases A).stripAnchors.adaptForFlowContext =
      (v.stripAnchors.adaptForFlowContext).resolveAliases A := by
  rw [stripAnchors_resolveAliases v A (fun p hp => (hA p hp).stripAnchors_eq),
      adaptForFlowContext_resolveAliases _ A (fun p hp => (hA p hp).adaptForFlowContext_eq)]

/-- The stored value is itself cleaned, so the table invariant is closed under
    `addAnchor`'s push. -/
lemma cleaned_resolveAliases (v : YamlValue) (A : Array (String × YamlValue))
    (hA : ∀ p ∈ A, Cleaned p.2) :
    Cleaned ((v.stripAnchors.adaptForFlowContext).resolveAliases A) := by
  unfold Cleaned
  rw [← cleaned_resolveAliases_comm _ A hA,
      stripAnchors_adaptForFlowContext_pipeline_idempotent]

lemma cleaned_table_push (A : Array (String × YamlValue)) (name : String) (v : YamlValue)
    (hA : ∀ p ∈ A, Cleaned p.2) :
    ∀ p ∈ A.push (name, (v.stripAnchors.adaptForFlowContext).resolveAliases A), Cleaned p.2 := by
  intro p hp
  rcases Array.mem_push.mp hp with hmem | heq
  · exact hA p hmem
  · subst heq
    exact cleaned_resolveAliases v A hA

end L4YAML.Algebra.Value

end Blanket
