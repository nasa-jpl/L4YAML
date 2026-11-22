/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 665 — a punt may be the BOUNDARY, not debt

**The rule.**  An optional field's `True`s read as a list of producers you did
not reach ([[PuntMayBeALostProjection]] sorts them into lost projection,
unstated lemma and different production — three kinds, all of them work).  There
is a fourth, and it is not work: a site where the datum is FALSE.  The input
reaches it, the runtime serves it, and the fact the pack would carry is
refutable there — so the punt is where the family ENDS, and closing it would be
unsound rather than expensive.

**How to tell it from the other three.**  Two questions, in this order.  Does
any input reach the site?  If none does, the branch is a phantom and retires
([[PhantomBranchNotADeferral]]).  If some does, try to prove the datum's
NEGATION at that input.  If it goes through, you have the boundary; every
attempt to strengthen the producer will fail, and it should.  This is
[[VacuityIsAClaimAboutTheRuntime]]'s experiment run on the other side: there the
cheap test refuted "this branch is unreachable", here it confirms "this branch
is unpayable".

**Where the boundary is already written down.**  In the side condition of the
route the site would have to build.  A frame lemma that takes `n ≤ k` has said,
before any producer exists, which landings it serves and which it does not — so
the punt list is DERIVED from the side condition rather than discovered by
trying arms one at a time ([[EqualityGateHidesTwoOrders]] is the same arithmetic
read one step earlier, when the gate is still an equality).

Concretely (L4YAML item 39): `nestedBlockMap`'s side condition is `n ≤ k`, the
enclosing entry's index against the column the key landed at.  At the root
value (`n = 0`) it is vacuous and `k:⏎  a: 1` composes.  At an INDENTED
`pendingMapValue` a landing can be a dedent — `  : v⏎a: 1` — and there `n ≤ k`
is false, because the enclosing entry has ended and there is no value left to
nest inside.  That LANDING keeps its `True` permanently, and the input is still
served: it takes the deferral, which is what the deferral is for.

**Read §1's `reaches .indented` with [[PuntTheShapeNotTheSite]].**  Item 39 gave
the whole indented arm the boundary's `True`, and item 40 found that the two
questions below have a third answer at that site: landings of BOTH kinds reach
it, so the arm is mixed and the punt belongs to the dedent rather than to the
arm.  Everything this file proves still holds — a refuting input exists, and
`closing_the_boundary_is_refutable` says no total producer can exist — but the
classification is per LANDING, which is what `every_landing_is_served` was
already modelling one section further down.

§1 three punts of one type.  §2 the two questions that separate them.  §3 what
closing the boundary would cost.  §4 the side condition IS the punt list.
§5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.PuntMayBeTheBoundary

/-! ## §1  Three punts, one type

A landing is what the step measured: the index the pending carries and the
column the content arrived at.  The frame the route builds exists exactly when
the column is at or beyond the index — the whole content of `n ≤ k`, and the
whole difference between a nested collection and a dedent. -/

/-- `n` — the enclosing entry's index; `k` — the column the key landed at. -/
structure Landing where
  n : Nat
  k : Nat
deriving DecidableEq

/-- The route's side condition, and so the frame's existence. -/
def Nests (l : Landing) : Prop := l.n ≤ l.k

/-- Three sites that all park the same optional field. -/
inductive Site where
  | root      -- the root value: every landing has `n = 0`
  | indented  -- an indented value: the landing may be a dedent
  | phantom   -- a branch the dispatch cannot take
deriving DecidableEq

/-- Which landings actually reach each site. -/
def reaches : Site → Landing → Prop
  | .root, l => l.n = 0
  | .indented, _ => True
  | .phantom, _ => False

/-- The field, as every producer writes it: the fact, or `True`. -/
def Punt (s : Site) : Prop := (∀ l, reaches s l → Nests l) ∨ True

/-- **The type cannot tell the three apart**, which is the point of it — one
    carrier, and the consumer's route is the same whichever arm supplies it. -/
theorem the_type_cannot_tell : Punt .root ∧ Punt .indented ∧ Punt .phantom :=
  ⟨Or.inr trivial, Or.inr trivial, Or.inr trivial⟩

/-! ## §2  The two questions

Reachability first, because it decides whether there is anything to ask about;
then the datum's negation, because that is the cheap experiment. -/

/-- The phantom: no input reaches it at all. -/
theorem phantom_has_no_input : ∀ l, ¬ reaches .phantom l := fun _ h => h

/-- The debt: inputs reach it and the datum HOLDS at every one of them, so the
    punt is a producer that was not written. -/
theorem root_is_debt : ∀ l, reaches .root l → Nests l := by
  intro l h
  have hn : l.n = 0 := h
  show l.n ≤ l.k
  omega

/-- …and writing it is exactly this, which is why the root arm stopped
    punting. -/
theorem root_punt_is_closable : Punt .root := Or.inl root_is_debt

/-- The boundary: inputs reach it, and at one of them the datum is FALSE. -/
theorem indented_is_a_boundary : ∃ l, reaches .indented l ∧ ¬ Nests l :=
  ⟨⟨2, 0⟩, trivial, by intro h; exact absurd (show (2 : Nat) ≤ 0 from h) (by omega)⟩

/-- The classification is not a reading of the field — all three punts are the
    same term — but of the SITE. -/
theorem classification_is_a_site_reading :
    (∀ l, ¬ reaches .phantom l) ∧
    (∀ l, reaches .root l → Nests l) ∧
    (∃ l, reaches .indented l ∧ ¬ Nests l) :=
  ⟨phantom_has_no_input, root_is_debt, indented_is_a_boundary⟩

/-! ## §3  What closing the boundary would cost

Strengthening the indented arm means supplying the fact for every landing that
reaches it.  There is no such function, at any price. -/

theorem closing_the_boundary_is_refutable :
    ¬ (∀ l, reaches .indented l → Nests l) := by
  intro h
  exact absurd (show (2 : Nat) ≤ 0 from h ⟨2, 0⟩ trivial) (by omega)

/-- And the input is still SERVED — the deferral takes it, which is what makes
    the punt a boundary rather than a hole.  (Modelled: a landing outside the
    family is handled by the other route, so coverage of the two together is
    total.) -/
def servedByRoute (l : Landing) : Bool := decide (l.n ≤ l.k)
def servedByDeferral (l : Landing) : Bool := ! servedByRoute l

theorem every_landing_is_served (l : Landing) :
    servedByRoute l = true ∨ servedByDeferral l = true := by
  unfold servedByDeferral
  cases h : servedByRoute l
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## §4  The side condition IS the punt list

Nothing about the punts had to be found by trying arms: the route's side
condition partitions the landings, and both halves are decidable. -/

theorem the_side_condition_is_the_family : ∀ l, Nests l ↔ l.n ≤ l.k :=
  fun _ => Iff.rfl

/-- The root's half is vacuous — which is why item 39's producer exists only
    there. -/
theorem the_root_half_is_free : ∀ k, Nests ⟨0, k⟩ := fun k => Nat.zero_le k

/-- The punts are computed, not discovered. -/
theorem punts_are_computed :
    servedByDeferral ⟨2, 0⟩ = true ∧ servedByDeferral ⟨0, 2⟩ = false ∧
    servedByDeferral ⟨2, 2⟩ = false := by decide

/-! ## §5  What item 39 shipped -/

/-- Kinds in the punt taxonomy: lost projection, unstated lemma, different
    production (Reflection 655) — and the boundary. -/
def taxonomyKindsBefore : Nat := 3
def taxonomyKindsAfter : Nat := 4
/-- Routes into the stream from a finished `[188]` entry: root, compact, and
    the value's. -/
def routesBefore : Nat := 2
def routesAfter : Nat := 3
/-- Producers of the one implicit-key pack. -/
def packProducersBefore : Nat := 3
def packProducersAfter : Nat := 4
/-- Frame lemmas whose general form was recovered from an inlined `n = 0`
    instance (`rootBlockMap` → `nestedBlockMap`). -/
def frameLemmasGeneralized : Nat := 1
/-- Changes to the pack, to the key head, or to the arm that fires it. -/
def consumerEditsRequired : Nat := 0
/-- Runtime files edited: none.  Proof shape only. -/
def runtimeFilesEdited : Nat := 0
/-- Escape sites: unmoved again — what moves is the domain. -/
def escapeSitesBefore : Nat := 6
def escapeSitesAfter : Nat := 6

theorem shipped :
    taxonomyKindsAfter = taxonomyKindsBefore + 1 ∧
    routesAfter = routesBefore + 1 ∧
    packProducersAfter = packProducersBefore + 1 ∧
    frameLemmasGeneralized = 1 ∧ consumerEditsRequired = 0 ∧
    runtimeFilesEdited = 0 ∧ escapeSitesAfter = escapeSitesBefore := by
  decide

end L4YAML.Tests.Reflections.PuntMayBeTheBoundary

end Blanket
