/-!
# Reflection 298 — a window-absolute gate makes the carrier a subset restriction

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`SeqInteriorSeparators` and its `_narrow`/`_descend`/`_advance` edges: when a guard conjunct must
quantify over sub-windows `[a,b) ⊆ [lo,hi)` under a gate, push the outer window origin OUT of the
quantifier body and into the domain bounds.

* If the body is **window-absolute** — every gate condition and asserted fact is keyed only on the
  sub-window endpoints `a,b`, never on the outer origin `lo`/`hi` — then narrowing `[lo,hi)` to any
  sub-interval reuses the body verbatim and only shrinks the domain. A SINGLE monotonicity lemma is
  the entire descend/advance edge.
* If the body is **origin-relative** — it re-bases some fact on `lo` (`a - lo`, balance from `lo`,
  …) — narrowing flips that re-basing and the carrier BREAKS, even though the gate itself is
  absolute. This is the `ref-non-restriction-residual-root-seed` failure: a depth-`0`-from-origin
  fact goes silent across descent.

Toy: a gated position `gate a := a % 2 = 0` (window-absolute). The window-absolute fact
`factAbs a := a % 2 = 0` survives narrowing; the origin-relative fact `factRel lo a := (a-lo) % 2 = 0`
holds at origin `0` (offset = position) but FAILS once the origin moves to `1` (offset parity flips)
even though the SAME gated positions are spoken of.
-/

namespace Tests.Reflections.WindowAbsoluteGateSubsetRestriction

set_option autoImplicit false

/-! ## Abstract: the monotonicity lemma IS the descend/advance edge (window-absolute body) -/

/-- A window-absolute gate: keyed only on the sub-window start `a`. -/
def gate (a : Nat) : Prop := a % 2 = 0

/-- A window-absolute fact: keyed only on `a` (no outer origin). -/
def factAbs (a : Nat) : Prop := a % 2 = 0

/-- An origin-relative fact: re-bases the offset on the outer origin `lo`. -/
def factRel (lo a : Nat) : Prop := (a - lo) % 2 = 0

/-- Window-absolute carrier: the body mentions `lo`/`hi` ONLY through the domain bounds. -/
def CarrierAbs (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → gate a → factAbs a

/-- Origin-relative carrier: the body re-bases `factRel` on `lo`. -/
def CarrierRel (lo hi : Nat) : Prop :=
  ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → gate a → factRel lo a

/-- POSITIVE — the window-absolute carrier restricts to any sub-interval by ONE monotonicity lemma
    (two `Nat.le_trans`): this is the entire descend/advance edge of `SeqInteriorSeparators`. -/
theorem carrierAbs_narrow {lo hi lo' hi' : Nat} (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi)
    (h : CarrierAbs lo hi) : CarrierAbs lo' hi' := by
  intro a b ha hab hb hg
  exact h a b (Nat.le_trans h_lo ha) hab (Nat.le_trans hb h_hi) hg

/-! ## Concrete: absolute survives narrowing, origin-relative breaks it -/

/-- Decidable model of `CarrierAbs lo hi` over positions `[0, hi]`: `gate a → factAbs a`. -/
def carrierAbsB (lo hi : Nat) : Bool :=
  (List.range (hi + 1)).all fun a =>
    (List.range (hi + 1)).all fun b =>
      !(decide (lo ≤ a) && decide (a ≤ b) && decide (b ≤ hi) && decide (a % 2 = 0))
        || decide (a % 2 = 0)

/-- Decidable model of `CarrierRel lo hi`: same gate, but the fact re-bases on `lo`. -/
def carrierRelB (lo hi : Nat) : Bool :=
  (List.range (hi + 1)).all fun a =>
    (List.range (hi + 1)).all fun b =>
      !(decide (lo ≤ a) && decide (a ≤ b) && decide (b ≤ hi) && decide (a % 2 = 0))
        || decide ((a - lo) % 2 = 0)

/-- POSITIVE — the window-absolute carrier survives narrowing the origin `0 → 1`. -/
theorem abs_survives_narrowing : carrierAbsB 0 4 = true ∧ carrierAbsB 1 4 = true := by decide

/-- NEGATIVE — the origin-relative carrier HOLDS at origin `0` (offset = position, even on the gated
    even positions `{0,2,4}`) but FAILS once the origin moves to `1` (the SAME gated positions
    `{2,4}` now have odd offsets `{1,3}`): narrowing the origin breaks an origin-relative body. -/
theorem rel_breaks_under_narrowing : carrierRelB 0 4 = true ∧ carrierRelB 1 4 = false := by decide

-- The mechanism, position by position: gated (even) positions in `[0,4]` are `{0,2,4}`.
#guard carrierAbsB 0 4            -- absolute: parities {0,2,4} all even
#guard carrierAbsB 1 4            -- absolute: window [1,4], gated {2,4}, parities still even
#guard carrierRelB 0 4            -- origin 0: offsets {0,2,4} even — holds
#guard !carrierRelB 1 4           -- origin 1: gated {2,4}, offsets {1,3} odd — FAILS
#guard ((2 - 0) % 2 == 0)         -- origin 0: position 2 has even offset
#guard ((2 - 1) % 2 == 1)         -- origin 1: SAME position 2 now has odd offset — the re-basing flip

end Tests.Reflections.WindowAbsoluteGateSubsetRestriction
