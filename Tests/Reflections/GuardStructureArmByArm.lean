/-
Reflection 367 — a self-contained toy of building a recursion GUARD structure ARM-BY-ARM.

When a recursion's per-window guard `G` is pinned as a `structure`, ship only the fields whose
CONSUMER ARM has landed, and DEFER a field a not-yet-landed arm needs as an additive extension of the
new own-type.  The deferral is a de-risk (the arm proof pins the field's exact form) and free (the
guard is your own type).  No project deps — a `Nat`-only toy of `SeqLocateGuard` /
`nestedSeq_recseqentry_locate_step_leaf` (`SeqInteriorSeparators.lean`, R367).
-/

namespace Tests.Reflections.GuardStructureArmByArm

set_option autoImplicit false

/-! ## The toy deliverable — a fixed target `t`, a walking window `off`. -/

/-- The base arm's deliverable: the window contains the target within a fixed span. -/
abbrev Deliv (t off : Nat) : Prop := off ≤ t ∧ t < off + 100

/-! ## Step 1 (this increment) — the guard carries ONLY the BASE arm's fields. -/

/-- The guard as first shipped: exactly the two fields the BASE arm consumes.  NOTE a field named
    `rec` would collide with the auto-generated `GuardBase.rec` recursor (and cascade into every
    projection failing) — so a real field of that meaning is named e.g. `recBody`, never `rec`. -/
structure GuardBase (t off : Nat) : Prop where
  /-- the target is past (or at) the walking origin. -/
  f_lo : off ≤ t
  /-- the target is within the fixed span. -/
  f_hi : t < off + 100

/-- **BASE projection (positive)** — the guard projects to the base deliverable, PINNING `f_lo`/`f_hi`
    against a real proof.  This is the toy of `nestedSeq_recseqentry_locate_step_leaf`: landing the
    simplest arm's projection first commits the shared field set while the simplest arm validates it. -/
theorem step_base (t off : Nat) (g : GuardBase t off) : Deliv t off :=
  ⟨g.f_lo, g.f_hi⟩

-- A concrete satisfiable base window `off = 3` against target `t = 5`.
theorem gBase : GuardBase 5 3 := ⟨by decide, by decide⟩

#guard decide (Deliv 5 3)              -- the base deliverable holds at the base window
#guard decide ((3 : Nat) ≤ 5)          -- f_lo at off = 3
#guard decide ((5 : Nat) < 3 + 100)    -- f_hi at off = 3

/-! ## Step 2 (a LATER increment, when the recursive arm lands) — ADDITIVE extension. -/

/-- When the recursive arm lands, its proof DICTATES the new field's exact form; only THEN is it added,
    as a free additive extension of the own-type `GuardBase`.  The base projection still type-checks
    unchanged through the extension (via the auto-generated `toGuardBase` coercion). -/
structure GuardFull (t off : Nat) : Prop extends GuardBase t off where
  /-- the field only the RECURSIVE arm needs — pinned by ITS proof, deferred until that arm lands. -/
  f_strict : off + 1 ≤ t

/-- The base projection survives the extension unchanged — the deferred field cost nothing. -/
theorem step_base_via_full (t off : Nat) (g : GuardFull t off) : Deliv t off :=
  step_base t off g.toGuardBase

theorem gFull : GuardFull 5 3 := ⟨gBase, by decide⟩

#guard decide (Deliv 5 3)              -- still projects through GuardFull

/-! ## NEGATIVE — front-loading a GUESSED field makes the guard unsatisfiable at the base window. -/

/-- A guard that PREMATURELY front-loads the recursive arm's field with a WRONG (too-strong) precondition
    `2 ≤ off` — the toy of guessing `FlowBodyWindow`'s `2 ≤ lo` before the ADVANCE arm confirms it. -/
structure GuardGuessed (t off : Nat) : Prop where
  f_lo : off ≤ t
  /-- a guessed precondition, NOT validated by any landed arm. -/
  guessed : 2 ≤ off

/-- **At the base window `off = 0` the guessed guard is UNSATISFIABLE** — even though the real base fact
    `off ≤ t` holds there — because the guessed precondition `2 ≤ 0` is false.  So front-loading a field
    no arm has pinned is unsound: it narrows the guard's domain below where the base arm must fire.  This
    is why R367 DEFERS `FlowBodyWindow` rather than guessing it now. -/
theorem guessed_unsat_at_base (t : Nat) : ¬ GuardGuessed t 0 := by
  intro g
  have h := g.guessed
  omega

#guard decide ((2 : Nat) ≤ 0) == false  -- the guessed precondition fails at the base window off = 0
#guard decide ((0 : Nat) ≤ 5)           -- yet the real base fact f_lo DOES hold there

end Tests.Reflections.GuardStructureArmByArm
