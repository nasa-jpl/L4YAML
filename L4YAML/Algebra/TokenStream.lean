/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Token-stream Algebra  (Algebra Item 10)

The L2 token stream is the **free monoid** on a token type `τ`:
`(TokenList τ, [], (· ++ ·))` is a monoid; `singleton`, `cons`,
`snoc`, and `length` are derived operations. The free-monoid laws
make scanner-side reasoning amenable to equational rewriting —
in particular, a token-emitting scan `step : Char → α → α × List τ`
factors through `foldl` (Phase 3 cutover).

## Choice of representation

Following the Item 8 (`Indent.lean`) precedent, the algebra is
stated on `List τ` rather than `Array τ`. The free-monoid laws
reduce to core Lean's `List.append_assoc` / `List.nil_append` /
`List.append_nil`, with no `Array`-specific reasoning. The
scanner's concrete `Array (Positioned YamlToken)` and the
indexed `TokenStream input` (in `L4YAML/Indexed/TokenStream.lean`)
are isomorphic to `List` via `Array.toList`/`Array.mk`, and Phase 3's
scanner cutover bridges the two via that trivial isomorphism.

## Closure (Guardrail 2)

This file introduces no new algebra beyond Item 10. Every theorem
is either a free-monoid law (`++`, `[]`) or a `length`/`singleton`
lemma that follows directly from `List`-level identities. The
`fold_append` lemma is the equational kernel of "`scan` as `foldM`
over chars" (per the inventory wording) and is stated abstractly
on the underlying `foldl`; the scanner-specific instance lands in
Phase 3.

## Provenance

New content (no migration). The blueprint estimate of ~70 LOC
holds.
-/

set_option autoImplicit false

namespace L4YAML.Algebra.TokenStream

universe u v

/-- A token list over an arbitrary token type `τ`. The **head** of
    the list is the **first-emitted** token; concatenation appends
    token streams in emission order. -/
abbrev TokenList (τ : Type u) : Type u := List τ

namespace TokenList

variable {τ : Type u} {α : Type v}

/-- The empty token stream. -/
def empty : TokenList τ := []

/-- A single-token stream. -/
@[inline] def singleton (t : τ) : TokenList τ := [t]

/-- Prepend a token to the front of the stream. The scanner uses
    `snoc` (appending at the end) at the call site; `cons` is
    provided here so equational reasoning can flip orientation
    when convenient. -/
@[inline] def cons (t : τ) (ts : TokenList τ) : TokenList τ := t :: ts

/-- Append a token at the end of the stream. -/
@[inline] def snoc (ts : TokenList τ) (t : τ) : TokenList τ := ts ++ [t]

/-- The number of tokens in the stream. -/
@[inline] def length (ts : TokenList τ) : Nat := List.length ts

/-! ## Item 10(a) — free-monoid laws

    The carrier `(TokenList τ, [], (· ++ ·))` is a monoid. These
    three laws are the standard `List` monoid laws, re-stated under
    the algebra namespace so downstream files reason via the
    `TokenList` API rather than reaching through to `List`. -/

/-- **Left identity**: `[] ++ ts = ts`. -/
@[simp] theorem nil_append (ts : TokenList τ) :
    (empty : TokenList τ) ++ ts = ts := List.nil_append ts

/-- **Right identity**: `ts ++ [] = ts`. -/
@[simp] theorem append_nil (ts : TokenList τ) :
    ts ++ (empty : TokenList τ) = ts := List.append_nil ts

/-- **Associativity**: `(a ++ b) ++ c = a ++ (b ++ c)`. -/
theorem append_assoc (a b c : TokenList τ) :
    (a ++ b) ++ c = a ++ (b ++ c) := List.append_assoc a b c

/-! ## Item 10(b) — singleton/cons/snoc bridge laws -/

/-- **Singleton via cons**: `singleton t = t :: []`. -/
theorem singleton_eq_cons (t : τ) :
    singleton t = cons t empty := rfl

/-- **Cons as append**: relating `cons` to the monoid op. -/
theorem cons_eq_append (t : τ) (ts : TokenList τ) :
    cons t ts = singleton t ++ ts := rfl

/-- **Snoc as append**: relating `snoc` to the monoid op. -/
theorem snoc_eq_append (ts : TokenList τ) (t : τ) :
    snoc ts t = ts ++ singleton t := rfl

/-! ## Item 10(c) — length is a monoid homomorphism

    `length : TokenList τ → Nat` carries the free-monoid structure
    to `(Nat, 0, (+))`. Useful in scanner termination proofs that
    measure progress in tokens emitted. -/

/-- **Length of empty**: `length [] = 0`. -/
@[simp] theorem length_empty : length (empty : TokenList τ) = 0 := rfl

/-- **Length is additive**: `length (a ++ b) = length a + length b`. -/
@[simp] theorem length_append (a b : TokenList τ) :
    length (a ++ b) = length a + length b := List.length_append

/-- **Length of singleton**: `length (singleton t) = 1`. -/
@[simp] theorem length_singleton (t : τ) :
    length (singleton t) = 1 := rfl

/-! ## Item 10(d) — fold homomorphism

    The inventory wording "`scan` as `foldM` over chars" reduces,
    after stripping the monad, to the standard `List.foldl` /
    `List.foldr` decomposition over `++`. We state both directions
    so a Phase 3 scanner formulated in either orientation can
    rewrite onto the monoid laws without case-splitting on the
    accumulator shape. -/

/-- **Left-fold over append**: folding the concatenation equals
    folding the suffix on top of the prefix's fold. -/
theorem foldl_append (f : α → τ → α) (z : α) (a b : TokenList τ) :
    (a ++ b).foldl f z = b.foldl f (a.foldl f z) := List.foldl_append

/-- **Right-fold over append**: folding from the right factors
    through the prefix. -/
theorem foldr_append (f : τ → α → α) (z : α) (a b : TokenList τ) :
    (a ++ b).foldr f z = a.foldr f (b.foldr f z) := List.foldr_append

end TokenList

end L4YAML.Algebra.TokenStream
