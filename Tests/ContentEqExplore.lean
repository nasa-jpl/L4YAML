import Lean4Yaml.Emitter

/-!
# contentEq_refl exploration

Scratch file exploring proof strategies for the universal `contentEq_refl`
theorem. The main obstacle is that Lean 4.28 cannot generate equational
theorems for `contentEq` (due to `where`-clause helpers processing
`Array.toList`), so `simp [contentEq]` and `unfold contentEq` both fail.

## Key findings

1. `delta contentEq` works — it does a non-recursive unfold of the definition.
2. `simp [contentEq.contentEqList]` and `simp [contentEq.contentEqPairList]`
   work — the `where`-clause helpers DO get equational theorems.
3. `show` can expose the computational form in each match branch, letting us
   bypass the equation-generation failure at the top level.
4. `Prod.mk.sizeOf_spec` is the correct name (not `Prod.sizeOf_spec`).
5. `List.sizeOf_lt_of_mem` gives `< sizeOf xs` for `List`, while
   `Array.sizeOf_lt_of_mem` gives `< sizeOf arr` for `Array`.

## Strategy for the main proof

- Match on `v` (scalar / sequence / mapping)
- Scalar: `show (s.content == s.content) = true` + `beq_self_eq_true`
- Sequence: `show (items.size == items.size && contentEqList ...) = true` +
  `simp` for the `beq` part + `contentEqList_refl` helper with recursive call
- Mapping: Same pattern with `contentEqPairList_refl`
- Termination: `termination_by v` with `List.sizeOf_lt_of_mem` for elements
  and `Prod.mk.sizeOf_spec` for product components
-/

open Lean4Yaml Lean4Yaml.Emit

-- ═══════════════════════════════════════════════════════════════════
-- §1: Verify that `where`-clause helpers have equational theorems
-- ═══════════════════════════════════════════════════════════════════

-- contentEqList nil/nil
#check @contentEq.contentEqList.eq_1
-- contentEqList cons/cons
#check @contentEq.contentEqList.eq_2
-- contentEqPairList nil/nil
#check @contentEq.contentEqPairList.eq_1
-- contentEqPairList cons/cons
#check @contentEq.contentEqPairList.eq_2

-- ═══════════════════════════════════════════════════════════════════
-- §2: Verify sizeOf lemmas exist
-- ═══════════════════════════════════════════════════════════════════

#check @List.sizeOf_lt_of_mem
#check @Array.sizeOf_lt_of_mem
#check @Prod.mk.sizeOf_spec

-- Prod sizeOf decomposition
example (p : YamlValue × YamlValue) : sizeOf p = 1 + sizeOf p.1 + sizeOf p.2 := by
  cases p; simp [Prod.mk.sizeOf_spec]

-- ═══════════════════════════════════════════════════════════════════
-- §3: List helper lemmas (independent of contentEq equation generation)
-- ═══════════════════════════════════════════════════════════════════

/-- `contentEqList` is reflexive given an induction hypothesis on elements. -/
theorem contentEqList_refl (vs : List YamlValue)
    (ih : ∀ v, v ∈ vs → contentEq v v = true) :
    contentEq.contentEqList vs vs = true := by
  induction vs with
  | nil => simp [contentEq.contentEqList]
  | cons hd tl ihtl =>
    simp [contentEq.contentEqList]
    exact ⟨ih hd (.head tl), ihtl (fun v hv => ih v (.tail hd hv))⟩

/-- `contentEqPairList` is reflexive given an induction hypothesis on pairs. -/
theorem contentEqPairList_refl (ps : List (YamlValue × YamlValue))
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

-- ═══════════════════════════════════════════════════════════════════
-- §4: Verify `show` approach works for each match branch
-- ═══════════════════════════════════════════════════════════════════

-- Scalar branch: show exposes the BEq on content
example (s : Scalar) : contentEq (.scalar s) (.scalar s) = true := by
  show (s.content == s.content) = true
  exact beq_self_eq_true s.content

-- Sequence branch: show exposes size check + contentEqList
example (style : CollectionStyle) (items : Array YamlValue) (tag : Option String) :
    contentEq (.sequence style items tag) (.sequence style items tag) = true := by
  show (items.size == items.size && contentEq.contentEqList items.toList items.toList) = true
  simp
  sorry -- needs contentEqList_refl with recursive IH

-- Mapping branch: show exposes size check + contentEqPairList
example (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue)) (tag : Option String) :
    contentEq (.mapping style pairs tag) (.mapping style pairs tag) = true := by
  show (pairs.size == pairs.size && contentEq.contentEqPairList pairs.toList pairs.toList) = true
  simp
  sorry -- needs contentEqPairList_refl with recursive IH
