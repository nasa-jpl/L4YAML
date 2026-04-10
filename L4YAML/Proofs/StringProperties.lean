/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Grammar

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

namespace L4YAML.Proofs.StringProperties

open L4YAML
open L4YAML.Grammar (FoldResult)
open L4YAML.CharPredicates

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

/-! ## §4  Trim Preservation (Layer 1b+)

`trimTrailingWS` is `String.ofList (l.reverse.dropWhile p).reverse`, which
produces a **prefix** of the original list.  Properties closed under prefix
(no adjacent bad‐pairs, no flow indicators, validPlainFirst) are therefore
preserved.
-/

/-- The reverse‑dropWhile‑reverse operation produces a prefix of the original. -/
theorem reverse_dropWhile_reverse_isPrefix (p : Char → Bool) (cs : List Char) :
    ∃ suf, cs = (cs.reverse.dropWhile p).reverse ++ suf := by
  have := @List.takeWhile_append_dropWhile _ p cs.reverse
  refine ⟨(cs.reverse.takeWhile p).reverse, ?_⟩
  calc cs = cs.reverse.reverse := (List.reverse_reverse cs).symm
    _ = (List.takeWhile p cs.reverse ++ List.dropWhile p cs.reverse).reverse := by rw [this]
    _ = (List.dropWhile p cs.reverse).reverse ++ (List.takeWhile p cs.reverse).reverse :=
        List.reverse_append ..

/-- `hasAdjacentChars` is false on a prefix when it is false on the whole list. -/
theorem hasAdjacentChars_false_of_append (a b : Char) (xs ys : List Char)
    (h : hasAdjacentChars a b (xs ++ ys) = false) :
    hasAdjacentChars a b xs = false := by
  rw [Bool.eq_false_iff] at h ⊢
  intro h'
  exact h ((hasAdjacentChars_append a b xs ys).mpr (Or.inl h'))

/-- Trimming trailing whitespace preserves `noColonSpaceProp`. -/
theorem trim_preserves_noColonSpace (p : Char → Bool) (cs : List Char)
    (h : noColonSpaceProp (String.ofList cs)) :
    noColonSpaceProp (String.ofList (cs.reverse.dropWhile p).reverse) := by
  obtain ⟨suf, hsuf⟩ := reverse_dropWhile_reverse_isPrefix p cs
  rw [← noColonSpace_iff] at h ⊢
  simp only [noColonSpaceBool, String.toList_ofList] at h ⊢
  rw [hsuf] at h
  simp [hasAdjacentChars_false_of_append ':' ' ' _ suf (Bool.not_inj h)]

/-- Trimming trailing whitespace preserves `noSpaceHashProp`. -/
theorem trim_preserves_noSpaceHash (p : Char → Bool) (cs : List Char)
    (h : noSpaceHashProp (String.ofList cs)) :
    noSpaceHashProp (String.ofList (cs.reverse.dropWhile p).reverse) := by
  obtain ⟨suf, hsuf⟩ := reverse_dropWhile_reverse_isPrefix p cs
  rw [← noSpaceHash_iff] at h ⊢
  simp only [noSpaceHashBool, String.toList_ofList] at h ⊢
  rw [hsuf] at h
  simp [hasAdjacentChars_false_of_append ' ' '#' _ suf (Bool.not_inj h)]

/-- Trimming trailing whitespace preserves `noFlowIndicatorsProp`. -/
theorem trim_preserves_noFlowIndicators (p : Char → Bool) (cs : List Char)
    (h : noFlowIndicatorsProp (String.ofList cs)) :
    noFlowIndicatorsProp (String.ofList (cs.reverse.dropWhile p).reverse) := by
  obtain ⟨suf, hsuf⟩ := reverse_dropWhile_reverse_isPrefix p cs
  intro c hc
  simp only [String.toList_ofList] at hc
  exact h c (by simp only [String.toList_ofList]; rw [hsuf]; exact List.mem_append_left _ hc)

/-- Trimming preserves `validPlainFirstProp` when the result has ≥ 2 characters.
    (When the first char is `-`/`?`/`:`, `canStartPlainScalarProp c none` is `False`,
    so a single-char result would not inherit `validPlainFirstProp` from the original.) -/
theorem trim_preserves_validPlainFirst (p : Char → Bool) (cs : List Char)
    (inFlow : Bool) (h : validPlainFirstProp (String.ofList cs) inFlow)
    (hge2 : (cs.reverse.dropWhile p).reverse.length ≥ 2) :
    validPlainFirstProp (String.ofList (cs.reverse.dropWhile p).reverse) inFlow := by
  obtain ⟨suf, hsuf⟩ := reverse_dropWhile_reverse_isPrefix p cs
  -- Extract two elements from the length-≥-2 trimmed prefix
  obtain ⟨x, y, rest', htrim⟩ : ∃ x y rest',
      (cs.reverse.dropWhile p).reverse = x :: y :: rest' := by
    match htr : (cs.reverse.dropWhile p).reverse, hge2 with
    | a :: b :: tl, _ => exact ⟨a, b, tl, rfl⟩
  -- Derive concrete decomposition: cs = x :: y :: (rest' ++ suf)
  have hcs : cs = x :: y :: (rest' ++ suf) := by
    rw [hsuf, htrim]; simp [List.cons_append]
  -- Rewrite h with the concrete decomposition, then unfold
  rw [hcs] at h
  simp only [validPlainFirstProp, String.toList_ofList] at h ⊢
  rw [htrim]
  exact h

end L4YAML.Proofs.StringProperties
