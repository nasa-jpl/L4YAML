/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # List/String Algebra  (Algebra Item 22)

Foundational `List.dropWhile` algebra used by whitespace handling
in the YAML parser:

- **Item 22(a)** — `dropWhile_idempotent`: dropping the same prefix
  twice = once.
- **Item 22(b)** — `reverse_dropWhile_reverse_idempotent`: the
  reverse-trim-reverse pattern is idempotent.

This file is a sub-piece of Algebra Item 9 (character/string
decomposition); the larger `Item 9` ─ string/list decomposition
algebra (`String.toList`, `++`, prefix/suffix laws) ─ will be added
to this file in Phase 2 §3.

## Provenance

Migrated from `L4YAML/Proofs/Foundation/StringProperties.lean:71–91`
during Initiative 4 Phase 2 (D4: one file per item-cluster). No
semantic change; namespace move only. The remainder of
`StringProperties.lean` (FoldResult, validPlainFirst preservation,
etc.) is *not* part of the algebra inventory and stays in
`Proofs/Foundation/` for now.
-/

namespace L4YAML.Algebra.StringList

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
