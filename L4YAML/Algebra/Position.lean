/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Spec.Types

/-! # Position Algebra  (Algebra Items 7 + 13)

Algebraic structure on `YamlPos`:

- **Item 7 — Position monoid (ordered)**. `YamlPos` carries a
  componentwise-additive monoid structure. The identity is
  `YamlPos.zero = ⟨0, 0, 0⟩`; the operation is `YamlPos.add`,
  which adds offsets, lines, and columns componentwise. The
  monoid laws (`zero_add`, `add_zero`, `add_assoc`) are stated
  here.
- **Item 13 — `YamlPos` total order**. The `Ord`, `LT`, `LE`
  instances on `YamlPos` (defined by `compare a.offset b.offset`
  in `Spec/Types.lean:127–134`) form a decidable linear order.
  Reflexivity, transitivity, antisymmetry, and totality of `≤`
  are stated here, together with the bridge `LE / LT` lemmas.

Combined, Items 7 + 13 form an *ordered monoid*: `≤` respects
componentwise addition on offsets.

## Why a separate file?

The instances themselves stay in `Spec/Types.lean` so that every
existing consumer (scanner, parser, output) continues to compile
unchanged. This file *names* the algebraic laws those instances
satisfy, so Phase 3+ proofs can rewrite by `add_assoc`,
`zero_add`, `le_trans`, etc. without proving them inline.

## Algebra Item closure (Guardrail 2)

This file introduces no new algebraic content beyond Items 7 + 13.
The `add` operation is the natural componentwise monoid on the
underlying `Nat × Nat × Nat`; the order is the existing
`compare … .offset`. Every theorem here is a statement about
those two structures, not an extension of them.
-/

set_option autoImplicit false

namespace L4YAML

namespace YamlPos

/-! ## Item 7 — Position monoid -/

/-- The identity position `⟨0, 0, 0⟩`. Coincides with `default`
    from the `Inhabited` instance derived in `Spec/Types.lean`. -/
def zero : YamlPos := ⟨0, 0, 0⟩

/-- Componentwise addition of two `YamlPos` values. The monoid
    operation: `(a + b).offset = a.offset + b.offset`, and likewise
    for `line` and `col`.

    *Note*: this is the **abstract** monoid op on the underlying
    `Nat × Nat × Nat`. Concrete advancement of the scanner (which
    must reset `col` after a newline) is a *different* operation
    in `Scanner/State.lean` and is not the algebra Item 7 op. -/
def add (a b : YamlPos) : YamlPos :=
  { offset := a.offset + b.offset
    line   := a.line   + b.line
    col    := a.col    + b.col }

/-- **Item 7(a)** — left identity: `zero + p = p`. -/
@[simp] theorem zero_add (p : YamlPos) : add zero p = p := by
  simp [add, zero]

/-- **Item 7(b)** — right identity: `p + zero = p`. -/
@[simp] theorem add_zero (p : YamlPos) : add p zero = p := by
  simp [add, zero]

/-- **Item 7(c)** — associativity: `(a + b) + c = a + (b + c)`. -/
theorem add_assoc (a b c : YamlPos) :
    add (add a b) c = add a (add b c) := by
  simp [add, Nat.add_assoc]

/-- Componentwise commutativity (the underlying `Nat` add is
    commutative, so the `YamlPos` monoid is commutative). -/
theorem add_comm (a b : YamlPos) : add a b = add b a := by
  simp [add, Nat.add_comm]

/-! ## Item 13 — Total order on `YamlPos` -/

/-- **Reflexivity** of `≤` (delegates to `Nat`). -/
theorem le_refl (p : YamlPos) : p ≤ p := Nat.le_refl _

/-- **Transitivity** of `≤` (delegates to `Nat`). -/
theorem le_trans {a b c : YamlPos} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Nat.le_trans hab hbc

/-- **Antisymmetry** of `≤` on `offset`: equal offsets imply equal
    offsets (line/col may still differ — this is antisymmetry of the
    *order*, not equality of the values). -/
theorem offset_antisymm {a b : YamlPos}
    (hab : a ≤ b) (hba : b ≤ a) : a.offset = b.offset :=
  Nat.le_antisymm hab hba

/-- **Totality** of `≤` (delegates to `Nat`). -/
theorem le_total (a b : YamlPos) : a ≤ b ∨ b ≤ a :=
  Nat.le_total a.offset b.offset

/-- **Decidability** of `≤`. -/
instance : DecidableRel (α := YamlPos) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.offset ≤ b.offset))

/-- **Decidability** of `<`. -/
instance : DecidableRel (α := YamlPos) (· < ·) := fun a b =>
  inferInstanceAs (Decidable (a.offset < b.offset))

/-- `<` ↔ `≤ ∧ ≠ on offsets` — the standard bridge between strict
    and non-strict order. -/
theorem lt_iff_le_and_offset_ne {a b : YamlPos} :
    a < b ↔ a ≤ b ∧ a.offset ≠ b.offset := by
  constructor
  · intro h
    refine ⟨Nat.le_of_lt h, Nat.ne_of_lt h⟩
  · intro ⟨hle, hne⟩
    exact Nat.lt_of_le_of_ne hle hne

/-! ## Items 7 + 13 combined — ordered monoid

    The componentwise-add monoid is *order-preserving* on offsets:
    adding the same `c` on the right preserves `≤`.
-/

theorem add_le_add_right {a b : YamlPos} (h : a ≤ b) (c : YamlPos) :
    add a c ≤ add b c := by
  show a.offset + c.offset ≤ b.offset + c.offset
  exact Nat.add_le_add_right h _

theorem add_le_add_left {a b : YamlPos} (h : a ≤ b) (c : YamlPos) :
    add c a ≤ add c b := by
  show c.offset + a.offset ≤ c.offset + b.offset
  exact Nat.add_le_add_left h _

end YamlPos

end L4YAML
