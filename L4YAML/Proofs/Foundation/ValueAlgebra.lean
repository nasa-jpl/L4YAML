import L4YAML.Proofs.Parser.ParserGrammableBase

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

set_option autoImplicit false
open L4YAML L4YAML.Proofs.ParserGrammable

/-! # Value Algebra for YamlValue

Algebraic properties of `stripAnchors` and `adaptForFlowContext`:

- `stripAnchors` is idempotent
- `adaptForFlowContext` is idempotent
- The two commute: `strip ∘ adapt = adapt ∘ strip`
- Combined pipeline idempotency: `(strip ∘ adapt) ∘ (strip ∘ adapt) = strip ∘ adapt`

These properties justify the `addAnchor` pipeline in `TokenParser.lean`:
  `cleaned = (val.resolveAliases ps.anchors).stripAnchors.adaptForFlowContext`
and ensure `WellFormedAnchors` is preserved when re-processing anchor values.
-/

namespace L4YAML.Proofs.ValueAlgebra

-- ============================================================
-- §1 Per-constructor reduction lemmas
-- ============================================================

@[simp] theorem stripAnchors_scalar' (s : Scalar) :
    (YamlValue.scalar s).stripAnchors = .scalar { s with anchor := none } := rfl

@[simp] theorem adaptForFlowContext_scalar' (s : Scalar) :
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

theorem sizeOf_lt_of_mem_toList {v : YamlValue} {items : Array YamlValue}
    (h : v ∈ items.toList) : sizeOf v < sizeOf items :=
  Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp h)

theorem sizeOf_pair_lt_of_mem_toList {p : YamlValue × YamlValue}
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
-- §3 stripAnchors is idempotent
-- ============================================================

theorem stripAnchors_idempotent (v : YamlValue) :
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
-- §4 stripAnchors and adaptForFlowContext commute
-- ============================================================

theorem stripAnchors_adaptForFlowContext_comm (v : YamlValue) :
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
-- §5 adaptForFlowContext is idempotent
-- ============================================================

theorem adaptForFlowContext_idempotent (v : YamlValue) :
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
-- §6 Pipeline corollaries
-- ============================================================

-- The addAnchor pipeline: resolveAliases → stripAnchors → adaptForFlowContext
-- Applied twice (strip ∘ adapt ∘ strip ∘ adapt) = once (strip ∘ adapt)
theorem stripAnchors_adaptForFlowContext_pipeline_idempotent (v : YamlValue) :
    (v.stripAnchors.adaptForFlowContext).stripAnchors.adaptForFlowContext =
    v.stripAnchors.adaptForFlowContext := by
  rw [stripAnchors_adaptForFlowContext_comm]
  rw [stripAnchors_idempotent]
  rw [adaptForFlowContext_idempotent]

-- After stripping a cleaned value, we get the cleaned value back.
-- Key for WellFormedAnchors preservation: the stored value `cleaned = strip(adapt(v))`
-- satisfies `cleaned.stripAnchors = cleaned`.
theorem stripAnchors_of_cleaned (v : YamlValue) :
    (v.stripAnchors.adaptForFlowContext).stripAnchors =
    v.stripAnchors.adaptForFlowContext := by
  rw [stripAnchors_adaptForFlowContext_comm, stripAnchors_idempotent]

end L4YAML.Proofs.ValueAlgebra
