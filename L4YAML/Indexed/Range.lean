/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `Range input` — half-open byte interval indexed by the source string

A `Range input` denotes the byte interval `[start, stop)` within
`input`, with the well-formedness constraint `start ≤ stop ≤ input.utf8ByteSize`.

This is the substrate on which `RepGraph input range` and `TokenStream input`
are indexed (D1 from Blueprint 08).

## Phase 2 scope

Type signature only. Operations (membership, intersection, sub-range
relation, monotonicity lemmas) are Phase 3+ as the scanner/parser
need them. Algebra Item 7 (position monoid) and Item 13 (YamlPos
total order) live in `L4YAML/Algebra/Position.lean`, not here.

## Notation

We use byte offsets (UTF-8) rather than character offsets, matching
`YamlPos.offset` in `Spec/Types.lean`. The bound `input.utf8ByteSize`
is a function on `String` — the constraint is propositional, so
`Range input` is decidable when needed.
-/

namespace L4YAML.Indexed

/-- A half-open byte interval `[start, stop)` in `input`.

    Type-level disjointness is the point: a `Range input₁` and a
    `Range input₂` with `input₁ ≠ input₂` are different types,
    so they cannot be confused at any stage boundary. -/
structure Range (input : String) where
  start : Nat
  stop  : Nat
  startLEStop : start ≤ stop
  stopLEInput : stop ≤ input.utf8ByteSize
  deriving Repr

namespace Range

/-- The byte length of the range. -/
@[inline] def byteSize {input : String} (r : Range input) : Nat :=
  r.stop - r.start

/-- The empty range at offset `0` (the canonical "empty prefix"). -/
def empty (input : String) : Range input where
  start := 0
  stop  := 0
  startLEStop := Nat.le_refl 0
  stopLEInput := Nat.zero_le _

/-- The whole-input range `[0, input.utf8ByteSize)`. -/
def full (input : String) : Range input where
  start := 0
  stop  := input.utf8ByteSize
  startLEStop := Nat.zero_le _
  stopLEInput := Nat.le_refl _

end Range

end L4YAML.Indexed
