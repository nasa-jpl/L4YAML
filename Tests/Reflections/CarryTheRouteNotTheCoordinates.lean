/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 664 — carry the route, not the coordinates

**The rule.**  When a carried datum is written as the COORDINATES one producer
happens to have, it admits exactly that producer.  Write it as the CONCLUSION
every producer would reach with them — a function into the goal — and the
datum admits every producer that can reach the goal at all, while the consumer
gets shorter rather than longer.  The coordinates are not lost: they are spent,
once, at the producer that has them.

**And it is NOT the opposite of [[ProjectAtTheConsumer]].**  That rule says: do
not weaken a fact at the producer, because the consumer may ask a question the
weakened form cannot answer.  This one says: do not carry a fact the consumer
never asks about.  The discriminator is whether EVERY producer can supply the
strong form.  If they can, carry it — a projection thrown away early is a
question you cannot ask later.  If the strong form names a construct only one
producer has, it is not a stronger version of what the consumer needs, it is
one route to it, and carrying it is what keeps the second producer out.

**How to tell which you are looking at.**  Try to state the datum without
naming any construct outside the consumer's own vocabulary.  A projection
(662) survives the test — the stop set is about characters, which is what the
consumer reads.  Coordinates do not: "a column-0 line start" is a fact about
the SHAPE of one derivation, and the consumer only ever turned it into a
stream.

Concretely (L4YAML): `ImplicitKeyPack` carried a column-0 landing, the stream
closed there, and `[63] s-indent(k)` in front of the key, because the producer
items 15–25 built had all three.  `- a: 1` has none of them — its key is on the
same line as the `-`, so `[79] s-l-comments` has no occurrence to match and the
landing does not exist — yet it reaches the SAME `[188]` entry through
`[185] s-l+block-indented`'s compact alternative.  Replacing the three fields
with `∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v` made
that a second producer of one pack, and the consumer lost the four lines that
rebuilt the root frame.

§1 the two producers.  §2 the route forgets, and that is the point.  §3 what
moved and what did not.  §4 the head was never the problem.  §5 the shipped
counts.
-/

namespace L4YAML.Tests.Reflections.CarryTheRouteNotTheCoordinates

/-! ## §1  Two producers, one consumer

`Entry` is the finished thing the consumer holds; `Goal` is what it must
produce.  A `Route` is the only use it ever has for the coordinates. -/

abbrev Entry : Type := Nat
abbrev Goal : Type := Nat
abbrev Route : Type := Entry → Goal

/-- Producer A's coordinates: a landing and the width in front of the key. -/
structure Coords where
  landing : Nat
  width : Nat
deriving DecidableEq

def routeOfCoords (c : Coords) : Route := fun e => c.landing + c.width + e

/-- Producer B — a compact entry — has the ENCLOSING closure and a width, and
    no landing at all: its key shares a line with the indicator that opened
    the entry. -/
structure Compact where
  close : Nat → Goal
  width : Nat

def routeOfCompact (c : Compact) : Route := fun e => c.close (c.width + e)

inductive Producer where
  | root
  | compact
deriving DecidableEq

/-- The asymmetry that the coordinate encoding turns into an exclusion. -/
def landing? : Producer → Option Nat
  | .root => some 0
  | .compact => none

/-- Both producers have a route. -/
def routeOf : Producer → Route
  | .root => routeOfCoords ⟨0, 1⟩
  | .compact => routeOfCompact ⟨fun x => x + 1, 0⟩

/-- **A pack that demands coordinates admits one producer; a pack that demands
    a route admits both.**  Note the failure is not "unproved": the compact
    producer has no landing to name, so the field has no value to take. -/
def PackCoords (p : Producer) : Prop := (landing? p).isSome = true
def PackRoute (_p : Producer) : Prop := True

theorem the_pack_widened :
    (PackCoords .root ∧ ¬ PackCoords .compact) ∧ (PackRoute .root ∧ PackRoute .compact) :=
  ⟨⟨rfl, fun h => Bool.noConfusion h⟩, ⟨trivial, trivial⟩⟩

/-! ## §2  The route FORGETS, and that is exactly what admits the second
producer

A route is a function into the goal, so it cannot be asked which derivation
built it.  Under the coordinate encoding that question was answerable and the
answer was load-bearing — which is another way of saying the pack named a
construct its consumer had no use for. -/

/-- Two different coordinate sets, one route. -/
theorem route_forgets :
    (⟨0, 3⟩ : Coords) ≠ ⟨3, 0⟩ ∧ routeOfCoords ⟨0, 3⟩ = routeOfCoords ⟨3, 0⟩ :=
  ⟨by decide, by funext e; simp [routeOfCoords]⟩

/-- …and the forgetting is total across producers: the two routes agree
    wherever they agree, with nothing in the type to distinguish them.  At
    `e = 4` both reach 5. -/
theorem the_producers_are_indistinguishable_here :
    routeOf .root 4 = 5 ∧ routeOf .compact 4 = 5 ∧
    routeOf .root 4 = routeOf .compact 4 := ⟨rfl, rfl, rfl⟩

/-- The one-way conversion.  Coordinates DETERMINE a route; no function goes
    back, which is why the route is the honest carrier. -/
def routeOfPack : Coords → Route := routeOfCoords

theorem conversion_is_one_way :
    (∀ c : Coords, routeOfPack c = routeOfCoords c) ∧
    ¬ (∀ r : Route, ∃ c : Coords, routeOfCoords c = r) := by
  refine ⟨fun _ => rfl, fun h => ?_⟩
  -- No `Coords` route is constant: every one of them is `· + e`, so it grows.
  obtain ⟨c, hc⟩ := h (fun _ => 0)
  have h0 : c.landing + c.width + 0 = 0 := congrFun hc 0
  have h1 : c.landing + c.width + 1 = 0 := congrFun hc 1
  omega

/-! ## §3  What moved, and what did not

The frame did not get cheaper — it moved to the producer, where the
coordinates are.  What the move buys is the second producer, and a consumer
that no longer knows what a document is. -/

/-- Frame steps: reflexive `s-l-comments`, `[187] l+block-mapping`, the bare
    document, `[211]`'s continuation. -/
def frameStepsBefore : Nat := 4
def frameStepsAfter : Nat := 4

theorem the_work_moved_it_did_not_vanish : frameStepsAfter = frameStepsBefore := rfl

/-- The consumer's share of them, before and after. -/
def consumerFrameStepsBefore : Nat := 4
def consumerFrameStepsAfter : Nat := 0

theorem the_consumer_stopped_naming_the_frame :
    consumerFrameStepsAfter < consumerFrameStepsBefore := by decide

/-! ## §4  The head was never the problem

`[193] ns-s-implicit-yaml-key` and `[194] c-s-implicit-json-key` take no indent
— the spec writes `n/a` — so the four arms that read the key (alias,
double-quoted, single-quoted, plain) are the same at either anchor.  The
entanglement was in the writing, not in the grammar: one producer wrote head
and frame together, so the head looked anchor-specific. -/

def headArms : Producer → Nat
  | .root => 4
  | .compact => 4

def headArmsAddedForTheSecondProducer : Nat := 0

theorem the_head_did_not_move :
    (∀ p q, headArms p = headArms q) ∧ headArmsAddedForTheSecondProducer = 0 := by
  refine ⟨fun p q => ?_, rfl⟩
  cases p <;> cases q <;> rfl

/-! ## §5  What item 38 shipped -/

/-- Conjuncts inside the pack, before and after. -/
def packConjunctsBefore : Nat := 6
def packConjunctsAfter : Nat := 4
/-- Existential witnesses it binds. -/
def packWitnessesBefore : Nat := 4
def packWitnessesAfter : Nat := 3
/-- Producers of the pack: the content dispatch and the props run — plus the
    compact entry. -/
def packProducersBefore : Nat := 2
def packProducersAfter : Nat := 3
/-- Fields added to a `PendingNode` constructor (`pendingBlockContent.h_key`). -/
def pendingFieldsAdded : Nat := 1
/-- Grammar productions given their FIRST producer: `[195]
    ns-l-compact-mapping`. -/
def productionsInstantiated : Nat := 1
/-- Runtime files edited: none.  Proof shape only. -/
def runtimeFilesEdited : Nat := 0
/-- Escape sites: unmoved, as with item 37 — what moves is the domain. -/
def escapeSitesBefore : Nat := 6
def escapeSitesAfter : Nat := 6

theorem shipped :
    packConjunctsAfter < packConjunctsBefore ∧
    packWitnessesAfter < packWitnessesBefore ∧
    packProducersAfter = packProducersBefore + 1 ∧
    pendingFieldsAdded = 1 ∧ productionsInstantiated = 1 ∧
    runtimeFilesEdited = 0 ∧ escapeSitesAfter = escapeSitesBefore := by
  decide

end L4YAML.Tests.Reflections.CarryTheRouteNotTheCoordinates

end Blanket
