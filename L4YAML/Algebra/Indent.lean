/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Indent-stack Algebra  (Algebra Item 8)

The indent stack is the **free monoid** on indentation entries:
`(IndentStack α, [], (· ++ ·))` is a monoid; `push`, `pop`, and
`top?` are derived operations. The push/pop laws make stack
manipulation amenable to equational reasoning.

## Choice of representation

We model the stack as `List α` rather than `Array α`. The free-monoid
laws are immediate from `List.append_assoc` / `List.nil_append`,
and `List.cons` is the natural push. The scanner's concrete state
(`L4YAML.Scanner.IndentEntry`-array) is *isomorphic* to a
`List` under reverse — but Phase 2 keeps the algebra abstract and
parameterises over the entry type `α`.

## Closure (Guardrail 2)

This file introduces no new algebra beyond Item 8. Every theorem
is either a free-monoid law (`++`, `[]`) or a stack law
(`push`/`pop`/`top?`).

## Provenance

New content (no migration). The blueprint estimate of ~50 LOC
holds.
-/

set_option autoImplicit false

namespace L4YAML.Algebra.Indent

universe u

/-- An indent stack over an arbitrary entry type `α`. The top of
    the stack is the **head** of the list — `push` is `cons`. -/
abbrev IndentStack (α : Type u) : Type u := List α

namespace IndentStack

variable {α : Type u}

/-- The empty stack. -/
def empty : IndentStack α := []

/-- Push an entry onto the top of the stack. -/
@[inline] def push (s : IndentStack α) (a : α) : IndentStack α := a :: s

/-- Pop the top entry, if any. Returns the popped stack and the
    removed entry. -/
def pop : IndentStack α → IndentStack α
  | []      => []
  | _ :: rest => rest

/-- Peek at the top entry, if any. -/
def top? : IndentStack α → Option α
  | []     => none
  | x :: _ => some x

/-! ## Item 8(a) — free-monoid laws

    The carrier `(IndentStack α, [], (· ++ ·))` is a monoid:
    these three laws are the standard `List` monoid laws,
    re-stated under the algebra namespace so downstream files
    can reason via the `IndentStack` API. -/

/-- **Left identity**: `[] ++ s = s`. -/
@[simp] theorem nil_append (s : IndentStack α) :
    (empty : IndentStack α) ++ s = s := List.nil_append s

/-- **Right identity**: `s ++ [] = s`. -/
@[simp] theorem append_nil (s : IndentStack α) :
    s ++ (empty : IndentStack α) = s := List.append_nil s

/-- **Associativity**: `(a ++ b) ++ c = a ++ (b ++ c)`. -/
theorem append_assoc (a b c : IndentStack α) :
    (a ++ b) ++ c = a ++ (b ++ c) := List.append_assoc a b c

/-! ## Item 8(b) — push/pop laws -/

/-- **Pop after push**: pushing then popping recovers the
    original stack. -/
@[simp] theorem pop_push (s : IndentStack α) (a : α) :
    (push s a).pop = s := rfl

/-- **Top after push**: peeking after pushing returns the pushed
    entry. -/
@[simp] theorem top?_push (s : IndentStack α) (a : α) :
    (push s a).top? = some a := rfl

/-- **Top of empty**: peeking the empty stack returns `none`. -/
@[simp] theorem top?_empty :
    (empty : IndentStack α).top? = none := rfl

/-- **Pop of empty**: popping the empty stack is a no-op (returns
    the empty stack). This makes `pop` total — the scanner's
    sentinel-bottom convention is enforced *separately* via a
    well-formedness invariant, not by giving `pop` a non-empty
    precondition. -/
@[simp] theorem pop_empty :
    (empty : IndentStack α).pop = empty := rfl

/-- **Push as cons**: relates the stack API to the underlying
    list constructor. Useful for switching between `push`/`pop`
    reasoning and induction on `List`. -/
theorem push_eq_cons (s : IndentStack α) (a : α) :
    push s a = a :: s := rfl

end IndentStack

end L4YAML.Algebra.Indent
