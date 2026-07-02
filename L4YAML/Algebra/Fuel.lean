/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Parse-side Fuel Algebra  (Algebra Item 11)

The fuel parameter used by the recursive-descent parser
(`Parser/Fuel.lean`, `Parser/TokenParser.lean`) is a natural-number
counter that decreases by 1 at each function entry. The
**abstract** algebraic content of fuel is the additive monoid
`(Nat, 0, (+))`: composition of two fuel-bounded iterations equals
a single iteration with summed fuel.

This file states that monoid + iteration composition law abstractly,
parameterised over an arbitrary state type `α` and step function
`step : α → α` (total) or `step : α → Option α` (partial). The
concrete `parseNode`/`parseBlockSequenceLoop`/… cutover lands in
Phase 4; this file gives the parser a named equational kernel it
can rewrite onto.

## Why a separate file?

`Parser/Fuel.lean` defines the concrete `initialFuel : Array … → Nat`
heuristic used by `parseDocument`. The algebra states the laws
that any fuel-bounded recursion satisfies, independently of which
heuristic chose the initial value. This is the same separation
that Items 7 (`Position.lean`) and 8 (`Indent.lean`) made: the
algebra lives in `L4YAML/Algebra/`, the concrete consumer in
`Scanner/` or `Parser/`.

## "Modulo termination" — the Phase 1 caveat

The Phase 1 inventory wording said `parseLoop n ∘ parseLoop m =
parseLoop (n + m)` *modulo termination*. The qualifier covers
the partial case where `step` may fail mid-iteration (returning
`none`); in that case, total-step composition has to be replaced
by `Option`-monadic chaining. Both variants land here:

- `iterate_add` for total `step : α → α` — unconditional.
- `iterateOpt_add` for partial `step : α → Option α` —
  conditional via `Option.bind`.

The conditional law states "if the prefix succeeds, the
composition equals the partial suffix run on its result; if the
prefix fails, the whole composition fails". It does *not* assume
that intermediate states satisfy any side-condition — that level
of guarantee is the job of Phase 4's per-rule progress lemmas,
not the algebra.

## Closure (Guardrail 2)

This file introduces no new algebra beyond Item 11. The monoid
laws are `Nat`-level facts (`Nat.zero_add`, `Nat.add_zero`,
`Nat.add_assoc`, `Nat.add_comm`); the iteration composition law
is the standard `Nat.iterate` decomposition. No content beyond
the inventory.

## Provenance

New content (no migration). The blueprint estimate of ~80 LOC
holds.
-/

set_option autoImplicit false

namespace L4YAML.Algebra.Fuel

universe u

/-- Fuel: a natural-number recursion budget. Forms an additive
    monoid under `+` with identity `0`. -/
abbrev Fuel : Type := Nat

namespace Fuel

/-! ## Item 11(a) — additive monoid laws on `Fuel`

    These are core `Nat` facts; re-stated under the `Fuel`
    namespace so downstream proofs can rewrite by
    `Fuel.zero_add` / `Fuel.add_assoc` etc. without exposing the
    underlying `Nat` to the equational layer. -/

/-- The identity fuel. -/
def zero : Fuel := 0

/-- **Left identity**: `0 + n = n`. -/
@[simp] theorem zero_add (n : Fuel) : zero + n = n := Nat.zero_add n

/-- **Right identity**: `n + 0 = n`. -/
@[simp] theorem add_zero (n : Fuel) : n + zero = n := Nat.add_zero n

/-- **Associativity**: `(a + b) + c = a + (b + c)`. -/
theorem add_assoc (a b c : Fuel) : (a + b) + c = a + (b + c) :=
  Nat.add_assoc a b c

/-- **Commutativity**: `a + b = b + a`. The parser doesn't rely
    on commutativity (iteration composition is generically
    non-commutative), but it holds on the underlying carrier and
    is useful for normalising fuel arithmetic. -/
theorem add_comm (a b : Fuel) : a + b = b + a := Nat.add_comm a b

end Fuel

/-! ## Item 11(b) — total fuel-bounded iteration

    Given a total `step : α → α`, `iterate step n x` applies `step`
    exactly `n` times to `x`. The composition law `iterate step
    (n + m) x = iterate step m (iterate step n x)` makes
    `iterate step` a monoid action of `(Nat, 0, +)` on `α`. -/

/-- Apply `step` exactly `n` times. -/
def iterate {α : Type u} (step : α → α) : Fuel → α → α
  | 0,     x => x
  | n + 1, x => iterate step n (step x)

variable {α : Type u}

/-- **Identity action**: zero fuel applies `step` zero times. -/
@[simp] theorem iterate_zero (step : α → α) (x : α) :
    iterate step 0 x = x := rfl

/-- **Successor unfold**: `iterate step (n+1) x = iterate step n (step x)`. -/
theorem iterate_succ (step : α → α) (n : Fuel) (x : α) :
    iterate step (n + 1) x = iterate step n (step x) := rfl

/-- **Fuel-additive composition** (Item 11 capstone, total form):
    running for `n + m` steps equals running for `n` steps then
    `m` more. -/
theorem iterate_add (step : α → α) (n m : Fuel) (x : α) :
    iterate step (n + m) x = iterate step m (iterate step n x) := by
  induction n generalizing x with
  | zero => simp [iterate]
  | succ k ih =>
    show iterate step (k + 1 + m) x = iterate step m (iterate step (k + 1) x)
    rw [Nat.succ_add]
    show iterate step (k + m + 1) x = iterate step m (iterate step (k + 1) x)
    rw [iterate_succ, iterate_succ, ih]

/-! ## Item 11(c) — partial fuel-bounded iteration ("modulo termination")

    Given a partial `step : α → Option α`, `iterateOpt step n x`
    applies `step` up to `n` times, threading `Option` and
    short-circuiting on `none`. The composition law states that
    fuel splits additively *if and only if* the prefix succeeds.

    This is the form that matches `parseNode` / `parseBlockSequence`
    after stripping `ParseState` and `Except`: each Phase-4 rule
    is a partial step. -/

/-- Apply partial `step` up to `n` times, short-circuiting on
    `none`. Returns the final state, or `none` if any step in the
    chain failed. -/
def iterateOpt (step : α → Option α) : Fuel → α → Option α
  | 0,     x => some x
  | n + 1, x => (step x).bind (iterateOpt step n)

/-- **Identity (partial)**: zero fuel succeeds trivially. -/
@[simp] theorem iterateOpt_zero (step : α → Option α) (x : α) :
    iterateOpt step 0 x = some x := rfl

/-- **Successor unfold (partial)**. -/
theorem iterateOpt_succ (step : α → Option α) (n : Fuel) (x : α) :
    iterateOpt step (n + 1) x = (step x).bind (iterateOpt step n) := rfl

/-- **Fuel-additive composition** (Item 11 capstone, partial form):
    running for `n + m` partial steps equals running for `n` steps
    then `m` more. The right-hand side `Option.bind` is the
    "modulo termination" caveat from the inventory: if the prefix
    fails, the whole composition fails. -/
theorem iterateOpt_add (step : α → Option α) (n m : Fuel) (x : α) :
    iterateOpt step (n + m) x =
      (iterateOpt step n x).bind (iterateOpt step m) := by
  induction n generalizing x with
  | zero => simp [iterateOpt]
  | succ k ih =>
    show iterateOpt step (k + 1 + m) x =
      ((iterateOpt step (k + 1) x).bind (iterateOpt step m))
    rw [Nat.succ_add]
    show iterateOpt step (k + m + 1) x =
      ((iterateOpt step (k + 1) x).bind (iterateOpt step m))
    rw [iterateOpt_succ, iterateOpt_succ]
    cases h : step x with
    | none => simp
    | some y => simp [ih]

end L4YAML.Algebra.Fuel
