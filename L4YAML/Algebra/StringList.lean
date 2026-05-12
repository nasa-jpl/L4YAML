/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # List/String Algebra  (Algebra Items 9 + 22)

Foundational list/string decomposition algebra used by whitespace
handling, scalar lexing, and character-class predicates in the YAML
parser.

- **Item 9 — character/string decomposition**. `String.toList`,
  `++`, prefix/suffix laws. Re-states the core `List` monoid laws
  under the algebra namespace, plus a few `String ↔ List Char`
  bridge lemmas that recur throughout the parser/scanner.
- **Item 22(a)** — `dropWhile_idempotent`: dropping the same prefix
  twice = once.
- **Item 22(b)** — `reverse_dropWhile_reverse_idempotent`: the
  reverse-trim-reverse pattern is idempotent.

## Closure (Guardrail 2)

The Item 9 lemmas here are all (a) free-monoid laws on `List` /
`String`, or (b) the `String.toList` / `String.length` /
`String.append` bridge equations that `String` instances satisfy
in core Lean. No content beyond the algebra inventory is added.

## Provenance

Item 22 lemmas migrated from
`L4YAML/Proofs/Foundation/StringProperties.lean:71–91` during
Initiative 4 Phase 2 (D4: one file per item-cluster). Item 9
lemmas are new content (re-stating core Lean laws under this
file's namespace so the algebra layer is self-describing).

The remainder of `StringProperties.lean` (FoldResult,
validPlainFirst preservation, etc.) is *not* part of the algebra
inventory and stays in `Proofs/Foundation/` for now.
-/

namespace L4YAML.Algebra.StringList

/-! ## Item 9 — List free-monoid laws -/

/-- **List left identity**: `[] ++ xs = xs`. -/
@[simp] theorem list_nil_append {α : Type _} (xs : List α) :
    [] ++ xs = xs := List.nil_append xs

/-- **List right identity**: `xs ++ [] = xs`. -/
@[simp] theorem list_append_nil {α : Type _} (xs : List α) :
    xs ++ [] = xs := List.append_nil xs

/-- **List associativity**: `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)`. -/
theorem list_append_assoc {α : Type _} (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := List.append_assoc xs ys zs

/-! ## Item 9 — Prefix / suffix decomposition

    `xs <+: ys ↔ ∃ zs, ys = xs ++ zs` is the canonical
    decomposition lemma. `List.prefix_iff_eq_append` (core Lean)
    provides this; we re-state it here so the algebra layer is the
    one-stop reference. -/

/-- A prefix decomposes the underlying list as `xs ++ zs`. -/
theorem prefix_iff_exists_append {α : Type _} {xs ys : List α} :
    xs <+: ys ↔ ∃ zs, ys = xs ++ zs := by
  constructor
  · rintro ⟨zs, rfl⟩; exact ⟨zs, rfl⟩
  · rintro ⟨zs, rfl⟩; exact ⟨zs, rfl⟩

/-- Every list is a prefix of itself appended to anything. -/
theorem prefix_append_right {α : Type _} (xs ys : List α) :
    xs <+: xs ++ ys := ⟨ys, rfl⟩

/-! ## Item 9 — `String ↔ List Char` bridge -/

/-- **String append distributes over `toList`**:
    `(s ++ t).toList = s.toList ++ t.toList`. (Re-export of
    core Lean's `String.toList_append`.) -/
theorem toList_append (s t : String) :
    (s ++ t).toList = s.toList ++ t.toList :=
  String.toList_append

/-- **String length is list length**:
    `(s ++ t).length = s.length + t.length`. -/
theorem length_append (s t : String) :
    (s ++ t).length = s.length + t.length := by
  simp [String.length_append]

/-! ## Item 22 — `dropWhile` idempotence -/

/-- `dropWhile p` on a list starting with an element where `p` is false
    returns the entire list. -/
theorem dropWhile_cons_false {α : Type} (p : α → Bool) (x : α) (xs : List α)
    (h : p x = false) : (x :: xs).dropWhile p = x :: xs := by
  simp [List.dropWhile, h]

/-- **Item 22(a) — list-level idempotence**: After dropping elements
    matching `p`, applying `dropWhile p` again is a no-op. -/
theorem dropWhile_idempotent {α : Type} (p : α → Bool) (xs : List α) :
    (xs.dropWhile p).dropWhile p = xs.dropWhile p := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.dropWhile]
    split
    · -- p y = true, so head is dropped
      exact ih
    · -- p y = false, head stays, and dropWhile (y :: ys) = y :: ys
      rename_i h
      simp [List.dropWhile, h]

/-- **Item 22(b) — reverse-trim-reverse idempotent**:
    Applying the full trim operation twice is the same as once,
    at the list level. -/
theorem reverse_dropWhile_reverse_idempotent {α : Type} (p : α → Bool) (xs : List α) :
    ((xs.reverse.dropWhile p).reverse.reverse.dropWhile p).reverse
    = (xs.reverse.dropWhile p).reverse := by
  rw [List.reverse_reverse]
  congr 1
  exact dropWhile_idempotent p xs.reverse

end L4YAML.Algebra.StringList
