/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `Range input` — half-open byte interval indexed by the source string

A `Range input` denotes the byte interval `[start, stop)` within
`input`, with the well-formedness constraint `start ≤ stop ≤ input.utf8ByteSize`.

This is the substrate on which `RepGraph input range` and `TokenStream input`
are indexed (D1 from Blueprint 08).

## Phase 2 → Phase 3 evolution

Phase 2 landed signatures only. Phase 3 Step 1 adds the byte-level
operations the scanner needs:

- `byteSize`, `isEmpty` (size predicates),
- `point` (a 0-width range at a given offset),
- `extend` (extend a range's `stop` forward, with proof obligation),
- `before` / `after` (positional predicates),
- `Contains` (sub-range relation).

Algebra Item 7 (position monoid) and Item 13 (YamlPos total order)
live in `L4YAML/Algebra/Position.lean`, not here.

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

/-- A zero-width range at offset `n` (the "point" range used as a
    cursor position witness). Requires `n ≤ input.utf8ByteSize`. -/
def point (input : String) (n : Nat) (h : n ≤ input.utf8ByteSize) :
    Range input where
  start := n
  stop  := n
  startLEStop := Nat.le_refl n
  stopLEInput := h

/-- Whether the range has byte length zero. -/
@[inline] def isEmpty {input : String} (r : Range input) : Bool :=
  r.start == r.stop

/-- Extend a range's `stop` forward to `stop'`, preserving the
    invariants. The witness `r.stop ≤ stop'` discharges
    `start ≤ stop'` via transitivity. -/
def extend {input : String} (r : Range input) (stop' : Nat)
    (hStop : r.stop ≤ stop') (hBound : stop' ≤ input.utf8ByteSize) :
    Range input where
  start := r.start
  stop  := stop'
  startLEStop := Nat.le_trans r.startLEStop hStop
  stopLEInput := hBound

/-- Build a range from two raw offsets, with explicit bound proofs. -/
def mk' (input : String) (start stop : Nat)
    (hOrder : start ≤ stop) (hBound : stop ≤ input.utf8ByteSize) :
    Range input where
  start := start
  stop  := stop
  startLEStop := hOrder
  stopLEInput := hBound

/-- `r` lies entirely before offset `n` (its `stop` does not pass `n`). -/
@[inline] def endsBefore {input : String} (r : Range input) (n : Nat) : Bool :=
  r.stop ≤ n

/-- `r` lies entirely after offset `n` (its `start` does not precede `n`). -/
@[inline] def startsAfter {input : String} (r : Range input) (n : Nat) : Bool :=
  n ≤ r.start

/-- `r₁` is a sub-range of `r₂`: same input, `r₂.start ≤ r₁.start` and
    `r₁.stop ≤ r₂.stop`. The relation is propositional (decidable). -/
def Contains {input : String} (r₂ r₁ : Range input) : Prop :=
  r₂.start ≤ r₁.start ∧ r₁.stop ≤ r₂.stop

instance {input : String} (r₂ r₁ : Range input) :
    Decidable (Range.Contains r₂ r₁) := by
  unfold Contains; exact inferInstance

/-- Reflexivity of `Contains`. -/
@[simp] theorem Contains.refl {input : String} (r : Range input) :
    Range.Contains r r :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Transitivity of `Contains`. -/
theorem Contains.trans {input : String} {r₃ r₂ r₁ : Range input}
    (h₁ : Range.Contains r₃ r₂) (h₂ : Range.Contains r₂ r₁) :
    Range.Contains r₃ r₁ :=
  ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₂.2 h₁.2⟩

/-- The empty range at offset `0` is contained in every range. -/
theorem empty_contained {input : String} (r : Range input) :
    Range.Contains (full input) r :=
  ⟨Nat.zero_le _, r.stopLEInput⟩

/-- `byteSize` of the empty range is zero. -/
@[simp] theorem byteSize_empty (input : String) :
    byteSize (empty input) = 0 := rfl

/-- `byteSize` of a `point` is zero. -/
@[simp] theorem byteSize_point {input : String} (n : Nat) (h : n ≤ input.utf8ByteSize) :
    byteSize (point input n h) = 0 := by
  simp [byteSize, point]

/-- `byteSize` of the full range equals the input's UTF-8 byte size. -/
@[simp] theorem byteSize_full (input : String) :
    byteSize (full input) = input.utf8ByteSize := by
  simp [byteSize, full]

end Range

end L4YAML.Indexed
