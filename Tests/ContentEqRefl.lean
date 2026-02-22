import Lean4Yaml.Emitter

/-!
# contentEq_refl full proof

Uses `show` to bypass the equation-generation limitation, combined with
`contentEqList_refl`/`contentEqPairList_refl` helper lemmas and
well-founded recursion on `sizeOf`.
-/

open Lean4Yaml Lean4Yaml.Emit

/-- `contentEqList` is reflexive given an IH on elements. -/
private theorem contentEqList_refl (vs : List YamlValue)
    (ih : ∀ v, v ∈ vs → contentEq v v = true) :
    contentEq.contentEqList vs vs = true := by
  induction vs with
  | nil => simp [contentEq.contentEqList]
  | cons hd tl ihtl =>
    simp [contentEq.contentEqList]
    exact ⟨ih hd (.head tl), ihtl (fun v hv => ih v (.tail hd hv))⟩

/-- `contentEqPairList` is reflexive given an IH on pairs. -/
private theorem contentEqPairList_refl (ps : List (YamlValue × YamlValue))
    (ih : ∀ p, p ∈ ps → contentEq p.1 p.1 = true ∧ contentEq p.2 p.2 = true) :
    contentEq.contentEqPairList ps ps = true := by
  induction ps with
  | nil => simp [contentEq.contentEqPairList]
  | cons hd tl ihtl =>
    obtain ⟨k, v⟩ := hd
    simp only [contentEq.contentEqPairList]
    have h := ih (k, v) (.head tl)
    simp only [Bool.and_eq_true]
    exact ⟨⟨h.1, h.2⟩, ihtl (fun p hp => ih p (.tail (k, v) hp))⟩

/-- `contentEq` is reflexive: every value is content-equivalent to itself. -/
theorem contentEq_refl (v : YamlValue) : contentEq v v = true := by
  match v with
  | .scalar s =>
    show (s.content == s.content) = true
    exact beq_self_eq_true s.content
  | .sequence style items tag =>
    show (items.size == items.size && contentEq.contentEqList items.toList items.toList) = true
    simp only [beq_self_eq_true, Bool.true_and]
    exact contentEqList_refl items.toList (fun v hv => contentEq_refl v)
  | .mapping style pairs tag =>
    show (pairs.size == pairs.size && contentEq.contentEqPairList pairs.toList pairs.toList) = true
    simp only [beq_self_eq_true, Bool.true_and]
    exact contentEqPairList_refl pairs.toList (fun p hp =>
      ⟨contentEq_refl p.1, contentEq_refl p.2⟩)
termination_by v
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem hv
    cases items; simp_all [Array.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hp
    cases pairs; cases p; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hp
    cases pairs; cases p; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
