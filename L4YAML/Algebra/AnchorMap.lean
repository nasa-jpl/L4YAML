/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Spec.Types

/-! # AnchorMap Algebra  (Algebra Item 12)

The `AnchorMap` is the alias-resolution coalgebra that realises
**Item 6 — graph isomorphism (anchors/aliases)** concretely. It
associates anchor names with their resolved L1 values and
satisfies the standard get-after-set / non-interference / empty
laws of a finite map.

## Algebraic content (the three laws)

- **`find?_insert`** — get-after-set:
  `find? (insert m k v) k = some v`.
- **`find?_insert_ne`** — non-interference:
  `k ≠ k' → find? (insert m k v) k' = find? m k'`.
- **`find?_empty`** — `find? empty _ = none`.

Together these are the universal property of the free finite map
on `String → YamlValue` — every `AnchorMap` operation downstream
factors through them.

## Closure (Guardrail 2)

This file introduces no new algebraic content beyond Item 12.
The auxiliary lemma `list_findSome?_filter_preserves` is a *proof
obligation* of `find?_insert_ne`, not a standalone item.

## Provenance

Migrated from `L4YAML/Spec/Types.lean:630–721` during Initiative 4
Phase 2 (D4: one file per item-cluster). No semantic change;
namespace move only — `L4YAML.AnchorMap` becomes
`L4YAML.Algebra.AnchorMap`. Existing call sites import this file
and drop their `open L4YAML` qualifier in favour of
`open L4YAML.Algebra`.

The Phase 4 parser cutover will additionally generalise
`AnchorMap` to `AnchorMap input` (parameterised by the source
string, mirroring `RepGraph input range`); the Item 12 laws lift
to that indexed form unchanged because `String` keys are
input-independent.
-/

set_option autoImplicit false

namespace L4YAML.Algebra

/-- Anchor map: associates anchor names with their resolved values.
    `abbrev` so `Array` methods (`filter`, `push`, `findSome?`) resolve
    without manual coercion, keeping both code and proofs short. -/
abbrev AnchorMap := Array (String × YamlValue)

namespace AnchorMap

/-- The empty anchor map. -/
def empty : AnchorMap := #[]

/-- Insert or replace a binding.
    Removes any prior binding for `name`, then appends `(name, val)`,
    maintaining the unique-key invariant. -/
def insert (m : AnchorMap) (name : String) (val : YamlValue) : AnchorMap :=
  (m.filter (fun (n, _) => n != name)).push (name, val)

/-- Look up an anchor by name.
    Returns the value if the anchor is defined, `none` otherwise. -/
def find? (m : AnchorMap) (name : String) : Option YamlValue :=
  m.findSome? (fun (n, v) => if n == name then some v else none)

/-! ### Algebraic Laws

These theorem statements document the essential contracts that
verification proofs will use. They are the specification of
`AnchorMap` — any correct implementation must satisfy them.
-/

/-- Auxiliary: filtering by `n != name` preserves `findSome?` for `name' ≠ name`.
    Elements removed by the filter have `n = name ≠ name'`, so `f` returns
    `none` for them and the `findSome?` result is unchanged. -/
theorem list_findSome?_filter_preserves
    (xs : List (String × YamlValue)) (name name' : String)
    (hne : name ≠ name') :
    List.findSome? (fun (n, v) => if n == name' then some v else none)
      (xs.filter (fun (n, _) => n != name))
    = List.findSome? (fun (n, v) => if n == name' then some v else none) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨n, v⟩ := x
    simp only [List.filter_cons]
    split
    · -- filter keeps element: (n != name) = true
      simp only [List.findSome?_cons]
      split
      · rfl
      · exact ih
    · -- filter drops element: n = name
      next hdrop =>
      have hEqName : n = name := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hdrop; exact hdrop
      have hNe : (n == name') = false := by
        rw [hEqName]; exact beq_eq_false_iff_ne.mpr hne
      simp only [List.findSome?_cons, hNe, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- **Get-after-set**: looking up a just-inserted key returns the inserted value. -/
theorem find?_insert (m : AnchorMap) (name : String) (val : YamlValue) :
    AnchorMap.find? (AnchorMap.insert m name val) name = some val := by
  simp only [AnchorMap.find?, AnchorMap.insert]
  rw [Array.findSome?_push]
  simp only [beq_self_eq_true, ↓reduceIte]
  -- Show filter part = none, then none.or (some val) = some val
  suffices h : Array.findSome? _ (Array.filter _ m) = none by
    rw [h, Option.none_or]
  rw [← Array.findSome?_toList, Array.toList_filter, List.findSome?_eq_none_iff]
  intro ⟨n, v⟩ hmem
  have hfilt := (List.mem_filter.mp hmem).2
  simp only [bne_iff_ne, ne_eq, beq_iff_eq] at hfilt ⊢
  exact if_neg hfilt

/-- **Non-interference**: inserting under `k` does not affect lookups for `k' ≠ k`. -/
theorem find?_insert_ne (m : AnchorMap) (name name' : String) (val : YamlValue)
    (h : name ≠ name') :
    AnchorMap.find? (AnchorMap.insert m name val) name' = AnchorMap.find? m name' := by
  simp only [AnchorMap.find?, AnchorMap.insert]
  rw [Array.findSome?_push]
  -- The pushed element (name, val) doesn't match name'
  have hpush : (fun (n, v) => if n == name' then some v else none) (name, val) = none := by
    simp [beq_eq_false_iff_ne.mpr h]
  simp only [hpush, Option.or_none]
  -- Filtering by n != name preserves findSome? for name' ≠ name
  rw [← Array.findSome?_toList, Array.toList_filter, ← Array.findSome?_toList]
  exact list_findSome?_filter_preserves m.toList name name' h

/-- **Empty**: no key is found in an empty map. -/
theorem find?_empty (name : String) :
    AnchorMap.find? AnchorMap.empty name = none := by
  rfl

end AnchorMap

end L4YAML.Algebra
