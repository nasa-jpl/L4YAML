/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # A widened slot stays pinned by its sibling conjunct (Reflection 619)

An accumulation invariant carried two conjuncts about the SAME pair of positions
`(sp_flow, sp_scan)` — the accumulator's endpoint and the scanner's cursor:

    PendingNode false sp_start sp_flow sp_scan                      -- (P)
    sc.flowLevel ≥ 1 → GStar SSWhite sp_flow sp_scan ∧ …            -- (W)

(W) was added FOR ONE PURPOSE: a flow-interior plain scalar ends its production
before the trailing whitespace `collectPlainScalarLoop` then consumes, so inside
a flow collection the accumulator legitimately sits a whitespace run behind the
cursor.  (W) is exactly the room for that run.

It never held anything.  (P) is a sibling conjunct on the same two positions,
and inside an open flow collection its ONLY derivable constructor is
`noPending`, whose type is `PendingNode false sp_start sp sp` — the two
positions are one.  Every other constructor demands a stream- or
document-level witness AT `sp_flow`, and inside an unclosed flow collection
there is none to build.  So (W) was provably always `GStar.nil`: every producer
discharged it that way, and the one arm that needed room — the plain-scalar arm
of `accum_step_content` at depth ≥ 1 — could not be written at all.

**The lesson.**  Widening one conjunct of a conjunctive invariant buys nothing
while a sibling conjunct still constrains the same variables.  After widening a
slot, enumerate the siblings that mention BOTH of its endpoints and ask what
each still admits — here, "which `PendingNode` constructors are inhabited at
depth ≥ 1?", answered by reading the constructors, not by trying the proof.

**And the repair has a shape.**  The pinning conjunct was not wrong; it was
over-scoped.  (P) is about the BLOCK level, and at depth ≥ 1 no step reads it —
`accum_step_flow`'s entire depth-≥1 branch never mentions `h_pending`.  A
hypothesis that no branch reads is a hypothesis in the wrong place: guarding it
on `flowLevel = 0` frees the slot and loses nothing.  §5 is that argument in the
abstract, and §6 is the cheap way to have SEEN it — grep the branch for the
hypothesis's name before believing the conjunct is load-bearing.

L4YAML DOCS item 10 (β.3), 2026-08-08.
-/

namespace Tests.Reflections.WidenedSlotPinnedBySibling

/-! ## §0  The substrate

`Pos` is a surface position, `d` a flow depth.  `Pend d p q` is the toy
`PendingNode`: the gap `p → q` at depth `d`.  Its constructors mirror the real
one's availability, which is the only feature that matters here:

* `noPending` is always available and forces `p = q`;
* every other constructor needs a stream/document witness at `p`, which exists
  only outside an open flow collection — modelled by the premise `d = 0`. -/

abbrev Pos := Nat

inductive Pend : Nat → Pos → Pos → Prop where
  /-- No gap.  Available at every depth, and it EQUATES the endpoints. -/
  | noPending (d : Nat) (p : Pos) : Pend d p p
  /-- Stands for `pendingContent` / `pendingFlow` / `pendingBlock` / … — every
      constructor whose closure needs a stream at `p`.  Inside an open flow
      collection there is no such stream, so the constructor is INDEXED at
      depth 0: that unavailability is the whole content of the model. -/
  | closeable (p q : Pos) : Pend 0 p q

/-- The widened slot: room for a whitespace run between the accumulator's
    endpoint and the cursor. -/
def Gap (p q : Pos) : Prop := p ≤ q

/-! ## §1  The pin

Nothing about `Gap` is at fault.  The equality comes from the sibling. -/

theorem pend_pins_the_endpoints {d p q : Pos} (h_pos : 0 < d) (h : Pend d p q) :
    p = q := by
  revert h_pos
  cases h with
  | noPending => intro _; rfl
  | closeable => intro h_pos; exact absurd h_pos (Nat.lt_irrefl 0)

/-- …and the pin is a property of the CONSTRUCTORS, not of the proof attempt:
    at positive depth exactly one of the two is inhabited. -/
theorem only_noPending_at_depth {d p : Pos} (h_pos : 0 < d) :
    Pend d p p ∧ ∀ q, Pend d p q → q = p :=
  ⟨.noPending d p, fun _ h => (pend_pins_the_endpoints h_pos h).symm⟩

/-! ## §2  The invariant as it stood, and why the widening was dead

`Inv` is the conjunction actually threaded.  `Gap` is stated only at depth ≥ 1
— the widening — and `Pend` is stated unconditionally. -/

def Inv (d : Nat) (p q : Pos) : Prop := Pend d p q ∧ (0 < d → Gap p q)

/-- The widened slot admits nothing the un-widened one did not: under the
    invariant, at every depth where `Gap` is even stated, the two positions are
    already equal. -/
theorem widened_slot_is_dead {d p q : Pos} (h_pos : 0 < d) (h : Inv d p q) :
    p = q :=
  pend_pins_the_endpoints h_pos h.1

/-- The consumer that motivated the widening — a step whose token ends its
    production strictly before the cursor — is therefore unwritable, and this is
    the form the failure actually took: not a hard goal, an EMPTY hypothesis. -/
theorem no_room_for_the_step : ¬ ∃ d p q, 0 < d ∧ Inv d p q ∧ p < q := by
  rintro ⟨d, p, q, h_pos, h_inv, h_lt⟩
  have h_eq : p = q := widened_slot_is_dead h_pos h_inv
  exact absurd h_eq (Nat.ne_of_lt h_lt)

/-! ## §3  The repair: scope the pinning conjunct to where it is read

`Inv'` differs from `Inv` in one place — `Pend` is now stated only at depth 0. -/

def Inv' (d : Nat) (p q : Pos) : Prop := (d = 0 → Pend d p q) ∧ (0 < d → Gap p q)

/-- The slot is alive: a genuine gap at positive depth. -/
theorem gap_is_alive : ∃ d p q, 0 < d ∧ Inv' d p q ∧ p < q :=
  ⟨1, 0, 1, Nat.zero_lt_one,
   ⟨fun h => absurd h Nat.one_ne_zero, fun _ => show (0 : Pos) ≤ 1 from Nat.zero_le 1⟩,
   Nat.zero_lt_one⟩

/-- …and it is alive by exactly the width of the widening: `Inv'` still forces
    `Gap`, so nothing weaker than a whitespace run gets in. -/
theorem gap_still_constrains {d p q : Pos} (h_pos : 0 < d) (h : Inv' d p q) :
    Gap p q := h.2 h_pos

/-! ## §4  Nothing is lost, because nothing read it

At depth 0 — the only place any consumer looks at the pending — the two
invariants are interchangeable.  This is the whole soundness argument for the
re-scoping, and it is one line. -/

theorem same_at_depth_zero (p q : Pos) : Inv' 0 p q ↔ Inv 0 p q := by
  constructor
  · rintro ⟨hp, hg⟩; exact ⟨hp rfl, hg⟩
  · rintro ⟨hp, hg⟩; exact ⟨fun _ => hp, hg⟩

/-- And `Inv'` is genuinely weaker at positive depth — the re-scoping is a real
    change, not a rename.  (Compare Reflection 617's `inv'_is_strictly_stronger`:
    there the invariant had to GROW to imply a new guard; here it SHRINKS to stop
    implying an old equation.) -/
theorem strictly_weaker_at_depth : ∃ d p q, 0 < d ∧ Inv' d p q ∧ ¬ Inv d p q := by
  refine ⟨1, 0, 1, Nat.zero_lt_one,
    ⟨fun h => absurd h Nat.one_ne_zero, fun _ => show (0 : Pos) ≤ 1 from Nat.zero_le 1⟩, ?_⟩
  intro h
  have h_eq : (0 : Pos) = 1 := widened_slot_is_dead Nat.zero_lt_one h
  exact absurd h_eq (by decide)

/-! ## §5  The diagnostic, in the abstract

A conjunct is safe to re-scope to a region `R` exactly when no consumer outside
`R` reads it.  `reads` below is the consumer table; `Step` is a step function's
demand.  The point of stating it this way is that the check is a SEARCH over the
consumers, not a proof about the invariant. -/

inductive Site where
  | depth0Block | depth0Content | flowInterior
  deriving DecidableEq, Repr, BEq

def allSites : List Site := [.depth0Block, .depth0Content, .flowInterior]

/-- Which sites are at depth 0. -/
def atDepthZero : Site → Bool
  | .flowInterior => false
  | _             => true

/-- Which sites READ the pending conjunct.  In the real file this is the result
    of one grep for `h_pending` inside each branch. -/
def readsPending : Site → Bool
  | .flowInterior => false
  | _             => true

/-- The re-scoping is sound exactly because the two tables agree: every reader
    is inside the region the conjunct is being restricted to. -/
theorem rescoping_is_sound : ∀ s, readsPending s = true → atDepthZero s = true := by
  intro s; cases s <;> decide

/-- The tell.  A conjunct stated everywhere but read nowhere in one region is
    a conjunct in the wrong place — and this witness is the flow-interior branch
    of `accum_step_flow`, which is fully proven and never mentions `h_pending`. -/
theorem there_is_a_non_reading_site : ∃ s, readsPending s = false :=
  ⟨.flowInterior, by decide⟩

/-! ## §6  The sweep

Computed, not recalled: the reader table and the depth table, and the single
site where they differ from "everything, everywhere". -/

#guard allSites.length == 3
#guard (allSites.filter fun s => readsPending s) == [Site.depth0Block, Site.depth0Content]
#guard (allSites.filter fun s => !readsPending s) == [Site.flowInterior]
#guard (allSites.filter fun s => readsPending s != atDepthZero s) == ([] : List Site)
#guard (allSites.filter fun s => !atDepthZero s) == [Site.flowInterior]

/-! ## §7  Axiom pins

The two load-bearing claims — the slot is dead, and the step that motivated it is
therefore unwritable — are axiom-FREE: they are `cases` on a two-constructor
inductive, which is the point.  The pin was not hard to see; it was never
looked at. -/

/-- info: 'Tests.Reflections.WidenedSlotPinnedBySibling.widened_slot_is_dead' does not depend on any axioms -/
#guard_msgs in
#print axioms widened_slot_is_dead

/-- info: 'Tests.Reflections.WidenedSlotPinnedBySibling.no_room_for_the_step' does not depend on any axioms -/
#guard_msgs in
#print axioms no_room_for_the_step

/-- info: 'Tests.Reflections.WidenedSlotPinnedBySibling.gap_is_alive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gap_is_alive

/-- info: 'Tests.Reflections.WidenedSlotPinnedBySibling.rescoping_is_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms rescoping_is_sound

end Tests.Reflections.WidenedSlotPinnedBySibling

end Blanket
