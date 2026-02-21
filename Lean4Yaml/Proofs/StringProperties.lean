/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Parser.Scalar

/-!
# Pure String and List Properties (Layer 1b + 1d)

Standalone proofs about pure helper functions used in the YAML parser.
These have **zero** lean4-parser dependency — they reason only about
`List`, `String`, and the pure datatypes `FoldResult`.

## Groups

1. **§1 Whitespace trimming** (Layer 1b) — idempotence via `List.dropWhile`.
2. **§2 FoldResult invariants** (Layer 1d) — construction, matching,
   the `folded`/`forbidden` contract.
3. **§3 List.dropWhile properties** — auxiliary lemmas used by §1.

## Strategy

The trim functions in `Scalar.lean` are local `where` definitions.
We prove properties about the underlying `List.dropWhile` operations
that constitute their implementation.
-/

namespace Lean4Yaml.Proofs.StringProperties

open Lean4Yaml
open Lean4Yaml.Parse (FoldResult)

/-! ## §3  Auxiliary List Lemmas -/

/-- Whitespace predicate matching the parser's trim implementations. -/
def isTrailingWs (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- `dropWhile` on a list where the predicate holds for all elements
    returns the empty list. -/
theorem dropWhile_nil_of_all_true {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = true) : xs.dropWhile p = [] := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [List.dropWhile]
    have hy : p y = true := h y List.mem_cons_self
    simp [hy]
    exact ih (fun x hx => h x (List.mem_cons_of_mem y hx))

/-- `dropWhile p` on a list starting with an element where `p` is false
    returns the entire list. -/
theorem dropWhile_cons_false {α : Type} (p : α → Bool) (x : α) (xs : List α)
    (h : p x = false) : (x :: xs).dropWhile p = x :: xs := by
  simp [List.dropWhile, h]

/-! ## §1  Whitespace Trimming (List-Level)

The YAML parser's trim functions work by:
1. Convert string to `List Char`
2. Reverse
3. `dropWhile isTrailingWs`
4. Reverse back

We prove properties at the list level, which is the core algorithm.
-/

/-- **Idempotence (list level)**: After dropping elements matching `p`,
    applying `dropWhile p` again is a no-op. -/
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

/-- **Reverse-trim-reverse idempotent**:
    Applying the full trim operation twice is the same as once, at the list level. -/
theorem reverse_dropWhile_reverse_idempotent {α : Type} (p : α → Bool) (xs : List α) :
    ((xs.reverse.dropWhile p).reverse.reverse.dropWhile p).reverse
    = (xs.reverse.dropWhile p).reverse := by
  rw [List.reverse_reverse]
  congr 1
  exact dropWhile_idempotent p xs.reverse

/-- **Empty list**: trimming the empty list returns the empty list. -/
theorem dropWhile_empty {α : Type} (p : α → Bool) : ([] : List α).dropWhile p = [] := by
  rfl

/-- **All matching**: if all chars match, the trim removes everything. -/
theorem reverse_dropWhile_reverse_all_ws (cs : List Char)
    (h : ∀ c ∈ cs, isTrailingWs c = true) :
    (cs.reverse.dropWhile isTrailingWs).reverse = [] := by
  have hrev : ∀ c ∈ cs.reverse, isTrailingWs c = true :=
    fun c hc => h c (List.mem_reverse.mp hc)
  rw [dropWhile_nil_of_all_true _ _ hrev]
  rfl

/-- **No trailing ws**: if the last element doesn't match, trim is identity. -/
theorem reverse_dropWhile_reverse_noop (cs : List Char) (c : Char)
    (hNe : cs ≠ [])
    (hLast : cs.getLast hNe = c)
    (hNotWs : isTrailingWs c = false) :
    (cs.reverse.dropWhile isTrailingWs).reverse = cs := by
  have hHead : cs.reverse ≠ [] := by
    intro h; exact hNe (List.reverse_eq_nil_iff.mp h)
  obtain ⟨y, ys, hrs⟩ := List.exists_cons_of_ne_nil hHead
  have hEq : y = c := by
    have h1 : cs.reverse.head? = cs.getLast? := List.head?_reverse
    rw [hrs] at h1; simp at h1
    rw [List.getLast?_eq_some_getLast hNe, hLast] at h1
    exact Option.some.inj h1
  rw [hrs, hEq, dropWhile_cons_false _ _ _ hNotWs]
  -- Goal: (c :: ys).reverse = cs
  have hrs' : cs.reverse = c :: ys := by rw [hrs, hEq]
  rw [← hrs', List.reverse_reverse]

/-! ## §2  FoldResult Invariants (Layer 1d)

`FoldResult` is a two-valued type from `Parser/Scalar.lean` that
distinguishes between successful folding and fatal boundary detection.

The structural proofs are already in `Validation.lean`
(`foldResult_forbidden_ne_folded`, `foldResult_exhaustive`).
Here we prove additional content-level properties.
-/

/-- A folded result always carries a string payload. -/
theorem folded_payload (s : String) :
    ∃ (t : String), FoldResult.folded s = FoldResult.folded t :=
  ⟨s, rfl⟩

/-- The string extracted from a `folded` result equals what was put in. -/
theorem folded_content_roundtrip (s : String) :
    match (FoldResult.folded s) with
    | .folded t => t = s
    | .forbidden _ => False := by
  rfl

/-- A forbidden result carries an error message. -/
theorem forbidden_has_message (msg : String) :
    match (FoldResult.forbidden msg) with
    | .folded _ => False
    | .forbidden m => m = msg := by
  rfl

/-- Fold results are determined by their constructor: matching on the
    result always classifies correctly. -/
theorem foldResult_classification (r : FoldResult) :
    (∃ s, r = .folded s ∧ match r with | .folded _ => True | .forbidden _ => False) ∨
    (∃ m, r = .forbidden m ∧ match r with | .folded _ => False | .forbidden _ => True) := by
  match r with
  | .folded s => exact Or.inl ⟨s, rfl, trivial⟩
  | .forbidden m => exact Or.inr ⟨m, rfl, trivial⟩

/-- `FoldResult.folded` is injective. -/
theorem folded_injective (s t : String) :
    FoldResult.folded s = FoldResult.folded t → s = t := by
  intro h; exact FoldResult.folded.inj h

/-- `FoldResult.forbidden` is injective. -/
theorem forbidden_injective (s t : String) :
    FoldResult.forbidden s = FoldResult.forbidden t → s = t := by
  intro h; exact FoldResult.forbidden.inj h

end Lean4Yaml.Proofs.StringProperties
