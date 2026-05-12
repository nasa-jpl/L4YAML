/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Surface.Combinators

/-! # Surface Grammar Combinator Algebra  (Algebra Item 14)

The surface-syntax combinators in `L4YAML/Surface/Combinators.lean`
encode YAML 1.2.2 productions as relations
`SurfPos → SurfPos → Prop`. This file names the Kleene-like laws
those combinators already satisfy by construction:

* sequential composition (`GSeq`) is associative, and `GEps` is its
  two-sided identity;
* alternation (`GAlt`) is commutative, associative, and idempotent;
* `GStar` is idempotent under self-composition and admits the
  standard unfolding `s = s' ∨ ∃ s'', P s s'' ∧ GStar P s'' s'`;
* `GPlus P` decomposes as `GSeq P (GStar P)`;
* `GOpt P` is the alternation with epsilon: `GAlt P GEps`;
* the ternary `GSeq3` reduces to a right-associated `GSeq` pair;
* `GEps s s' ↔ s = s'`.

Equality of relations on `SurfPos × SurfPos` is stated pointwise
as an `Iff` at each pair of positions, which is the form downstream
proofs need when rewriting one combinator into another.

## Closure (Guardrail 2)

This file introduces no new algebra beyond Item 14. Each law is a
direct case-split over the inductive `GSeq`/`GAlt`/`GStar` /
`GPlus`/`GOpt`/`GSeq3`/`GEps` constructors plus `Iff.intro`. The
laws are stated abstractly over arbitrary relations
`P Q R : SurfPos → SurfPos → Prop`; no production-specific facts
appear.

## Provenance

New content. The surface combinators (`GSeq`, `GAlt`, `GStar`,
`GPlus`, `GOpt`, `GEps`, `GSeq3`, `GChar`, `GLit`, `GConsumeAll`,
`GNot`, `atEnd`) are already defined in
`L4YAML/Surface/Combinators.lean`; this file consumes that namespace
through `L4YAML.Surface.Combinators` and adds only equational content.

## Proof style

The proofs case-split on the inductive constructors using
term-mode `match`. This avoids the small ambiguity in how the
`cases` and `rcases`/`obtain` tactics handle indexed inductives
whose indices unify with goal-context variables. Term-mode `match`
binds constructor arguments positionally, so each pattern literally
mirrors the constructor's signature.
-/

set_option autoImplicit false

namespace L4YAML.Algebra.Combinators

open L4YAML.Surface

variable {P Q R : SurfPos → SurfPos → Prop}

/-! ## Item 14(a) — `GEps` is the position-equality relation

    `GEps` has a single constructor `mk (s : SurfPos)` building
    `GEps s s`, so it is exactly the equality relation on
    `SurfPos`. This characterisation is used by every subsequent
    law that involves `GEps`. -/

/-- **Epsilon iff equality**: `GEps s s'` holds iff `s = s'`. -/
theorem eps_iff_eq (s s' : SurfPos) :
    GEps s s' ↔ s = s' :=
  ⟨fun h => match h with | .mk _ => rfl,
   fun h => h ▸ GEps.mk s⟩

/-! ## Item 14(b) — sequential composition: associativity + identity

    `GSeq` is associative: a witness for `(P; Q); R` and a witness
    for `P; (Q; R)` decompose into the same three sub-witnesses
    and three intermediate positions, just re-bracketed. `GEps`
    is the two-sided identity. -/

/-- **`GSeq` associativity**, stated pointwise as an `Iff` at each
    pair of positions. -/
theorem seq_assoc (s s' : SurfPos) :
    GSeq (GSeq P Q) R s s' ↔ GSeq P (GSeq Q R) s s' :=
  ⟨fun h => match h with
    | .mk _ s₃ _ (.mk _ s₂ _ hp hq) hr =>
      .mk s s₂ s' hp (.mk s₂ s₃ s' hq hr),
   fun h => match h with
    | .mk _ s₂ _ hp (.mk _ s₃ _ hq hr) =>
      .mk s s₃ s' (.mk s s₂ s₃ hp hq) hr⟩

/-- **Left identity of `GSeq`**: `GEps; P = P`. -/
theorem eps_seq (s s' : SurfPos) :
    GSeq GEps P s s' ↔ P s s' :=
  ⟨fun h => match h with | .mk _ _ _ (.mk _) hp => hp,
   fun hp => .mk s s s' (GEps.mk s) hp⟩

/-- **Right identity of `GSeq`**: `P; GEps = P`. -/
theorem seq_eps (s s' : SurfPos) :
    GSeq P GEps s s' ↔ P s s' :=
  ⟨fun h => match h with | .mk _ _ _ hp (.mk _) => hp,
   fun hp => .mk s s' s' hp (GEps.mk s')⟩

/-! ## Item 14(c) — alternation: commutative idempotent semilattice

    `GAlt` is a commutative idempotent semilattice operation on
    relations. Each law unfolds the constructors `left`/`right` and
    re-injects on the opposite side. -/

/-- **`GAlt` commutativity**. -/
theorem alt_comm (s s' : SurfPos) :
    GAlt P Q s s' ↔ GAlt Q P s s' :=
  ⟨fun h => match h with
    | .left _ _ hp => .right s s' hp
    | .right _ _ hq => .left s s' hq,
   fun h => match h with
    | .left _ _ hq => .right s s' hq
    | .right _ _ hp => .left s s' hp⟩

/-- **`GAlt` associativity**. -/
theorem alt_assoc (s s' : SurfPos) :
    GAlt (GAlt P Q) R s s' ↔ GAlt P (GAlt Q R) s s' :=
  ⟨fun h => match h with
    | .left _ _ (.left _ _ hp) => .left s s' hp
    | .left _ _ (.right _ _ hq) => .right s s' (.left s s' hq)
    | .right _ _ hr => .right s s' (.right s s' hr),
   fun h => match h with
    | .left _ _ hp => .left s s' (.left s s' hp)
    | .right _ _ (.left _ _ hq) => .left s s' (.right s s' hq)
    | .right _ _ (.right _ _ hr) => .right s s' hr⟩

/-- **`GAlt` idempotence**: `P | P = P`. -/
theorem alt_idem (s s' : SurfPos) :
    GAlt P P s s' ↔ P s s' :=
  ⟨fun h => match h with
    | .left _ _ hp => hp
    | .right _ _ hp => hp,
   fun hp => .left s s' hp⟩

/-! ## Item 14(d) — Kleene closures: `GStar`, `GPlus`, `GOpt`

    Three laws name the Kleene structure:

    * **`GStar` self-idempotence**: `(P*)* = P*`. Star of star is
      just star — folding a sequence of star-runs back into a single
      star-run.
    * **`GPlus` decomposition**: `P⁺ = P; P*`. By construction, a
      `GPlus.mk` packs exactly that pair, so the law is `rfl` modulo
      constructor packaging.
    * **`GOpt` decomposition**: `P? = P | ε`. Holds by re-injecting
      `none`↔`right(GEps.mk)` and `some`↔`left`. -/

/-- Helper: appending two `GStar P` runs gives a single `GStar P`
    run. Used in the forward direction of `star_star`. -/
private theorem star_append {s₁ s₂ s₃ : SurfPos}
    (h₁ : GStar P s₁ s₂) (h₂ : GStar P s₂ s₃) :
    GStar P s₁ s₃ := by
  induction h₁ with
  | nil _ => exact h₂
  | cons _ sm _ hstep _ ih => exact GStar.cons _ sm _ hstep (ih h₂)

/-- **`GStar` self-idempotence**: `GStar (GStar P) = GStar P`. The
    forward direction collapses a star-of-stars chain by appending
    each inner `GStar P` run; the backward direction wraps a single
    `GStar P` run inside a one-step star-of-stars chain. -/
theorem star_star (s s' : SurfPos) :
    GStar (GStar P) s s' ↔ GStar P s s' := by
  constructor
  · intro h
    induction h with
    | nil _ => exact GStar.nil _
    | cons _ _ _ hP _ ih => exact star_append hP ih
  · intro h
    exact GStar.cons s s' s' h (GStar.nil s')

/-- **`GPlus` decomposition**: `P⁺ = P; P*`. -/
theorem plus_iff_seq_star (s s' : SurfPos) :
    GPlus P s s' ↔ GSeq P (GStar P) s s' :=
  ⟨fun h => match h with
    | .mk _ s₂ _ hp hstar => .mk s s₂ s' hp hstar,
   fun h => match h with
    | .mk _ s₂ _ hp hstar => .mk s s₂ s' hp hstar⟩

/-- **`GOpt` decomposition**: `P? = P | ε`. The `.none`/`.right`
    branches rely on tactic-mode `cases` to unify the two `GOpt`
    indices (resp. unfold `GEps`), which term-mode `match` does
    not propagate into the goal type automatically. -/
theorem opt_iff_alt_eps (s s' : SurfPos) :
    GOpt P s s' ↔ GAlt P GEps s s' := by
  constructor
  · intro h
    cases h with
    | none => exact GAlt.right s s (GEps.mk s)
    | some _ hp => exact GAlt.left s s' hp
  · intro h
    cases h with
    | left hp => exact GOpt.some s s' hp
    | right he => cases he; exact GOpt.none s

/-! ## Item 14(e) — `GStar` unfolding

    A `GStar P` run is either zero steps (`s = s'`) or one `P`-step
    followed by another `GStar P` run. This is the standard
    one-step unfolding rule for Kleene star, and it is the form
    Phase 3 / Phase 4 proofs rewrite onto when peeling off a
    leading match. -/

/-- **`GStar` one-step unfold**. -/
theorem star_unfold (s s' : SurfPos) :
    GStar P s s' ↔ s = s' ∨ ∃ s'', P s s'' ∧ GStar P s'' s' :=
  ⟨fun h => match h with
    | .nil _ => Or.inl rfl
    | .cons _ s₂ _ hp hstar => Or.inr ⟨s₂, hp, hstar⟩,
   fun h => match h with
    | Or.inl heq => heq ▸ GStar.nil s
    | Or.inr ⟨s₂, hp, hstar⟩ => GStar.cons s s₂ s' hp hstar⟩

/-! ## Item 14(f) — `GSeq3` reduces to a `GSeq` pair

    `GSeq3 P Q R` packages three witnesses with two intermediate
    positions; right-associating those as `GSeq P (GSeq Q R)` is a
    direct constructor re-shuffle. -/

/-- **`GSeq3` reduces to right-associated `GSeq`**. -/
theorem seq3_iff_seq_seq (s s' : SurfPos) :
    GSeq3 P Q R s s' ↔ GSeq P (GSeq Q R) s s' :=
  ⟨fun h => match h with
    | .mk _ s₂ s₃ _ hp hq hr =>
      .mk s s₂ s' hp (.mk s₂ s₃ s' hq hr),
   fun h => match h with
    | .mk _ s₂ _ hp (.mk _ s₃ _ hq hr) =>
      .mk s s₂ s₃ s' hp hq hr⟩

end L4YAML.Algebra.Combinators
