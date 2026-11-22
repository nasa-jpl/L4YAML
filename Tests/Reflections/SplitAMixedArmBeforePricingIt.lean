/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # Split a mixed arm before pricing it (Reflection 618)

An unclosable proof arm was filed with a plan: "reachable only by an inline flow
open after an unclosed same-line construct (`"foo" [a]`), which is invalid YAML,
so refute it with a `PendingNode`-shape ↔ `simpleKey` coupling."  Every clause
of that is checkable, and the first one is false.  The arm is also reached by

    &a [b]        !t {a: b}        &a !!seq [b]

which are valid YAML and which the shipped pipeline parses correctly.  A
refutation would have to reject them, so no scanner fact — no coupling, no
lookback, nothing — can ever close that arm.  What it needs is vocabulary.

The arm was **mixed**: part legal-and-needs-a-construction, part
illegal-and-needs-a-guard.  Until it is split, both plans are wrong, and neither
half can even be priced.  §3 is the formal version: any guard that fires on the
arm's own condition rejects a legal input, so the mixedness is not an accident
of how the guard is written — it is a property of the arm.

**What produced the wrong plan** is §5: a single witness.  `"foo" [a]` really is
an inhabitant and really is invalid, and from one such witness the arm looks
vacuous.  But a witness is not a set: the set is whatever the arm's *condition*
admits, and the condition here is "a closeable pending, then a flow open, same
line, column ≠ 0" — which says nothing about legality.  Inhabitants have to be
generated from the condition, not recalled.

**The diagnostic**, once inhabitants are in hand, is the shipped pipeline's own
verdict on each (§4):

| pipeline says | destination |
|---|---|
| rejects it | refutable — transport the guard |
| accepts, parses correctly | vocabulary — the deliverable must be built for it |
| accepts, parses wrongly | a defect — fix the code first |

That is a fourth destination for Reflection 612's three (caller fact / threaded
invariant / the arm really fires, a defect), and it is the one that is not about
proof technique at all — 612's third destination assumed an arm is uniform, and
this one is not.

Sequel to Reflection 617, which prices a guard once you know you want one.  This
one is upstream of it: *what is the guard even for, and is a guard the right
shape of answer?*  Running 617's producer sweep on a guard that must not exist
is a wasted sweep.

L4YAML DOCS item 9h, 2026-08-08.  `accum_flow_open_depth0`'s `col ≠ 0`,
no-break arm.  The split cost one scanner check: the alias was the one
block-context node kind with no trailing-content validation, so `k: *a [b]`
scanned clean in both pipelines while its quoted-scalar sibling `k: "v" [b]` did
not.  The legal half — a property run before a flow open — is unchanged, and now
sits alone.
-/

namespace Tests.Reflections.SplitAMixedArmBeforePricingIt

/-! ## §0  The substrate

What can precede the arm's flow open on the same line, at column ≠ 0.  These are
exactly the constructs that leave a closeable pending: a quoted scalar, a closed
flow collection, a document-end marker, an alias node, and a property run. -/

inductive Pred where
  | quoted      -- `"foo" [a]`
  | flowClose   -- `[a] [b]`
  | docEnd      -- `... [a]`
  | alias       -- `*a [b]`
  | props       -- `&a [b]`
  deriving DecidableEq, Repr, BEq

def allPreds : List Pred := [.quoted, .flowClose, .docEnd, .alias, .props]

/-- The arm's condition, verbatim: a closeable pending, then a flow open, same
    line, column ≠ 0.  It is satisfied by *every* predecessor — which is the
    whole point.  The condition knows nothing about legality. -/
def reaches (_ : Pred) : Bool := true

/-- Is the resulting document valid?  Only the property run: `&a [b]` is ONE
    anchored node, whereas the other four put two nodes in one slot. -/
def legal : Pred → Bool
  | .props => true
  | _      => false

/-! ## §1  The scanner, before and after the split

Three of the four illegal predecessors were already rejected — a quoted scalar
by `validateTrailingContent`, a flow close by `validateFlowClose`, a `...` by
`trailingContentAfterDocEnd`.  The alias had no such check. -/

def guardedBefore : Pred → Bool
  | .quoted => true | .flowClose => true | .docEnd => true
  | .alias  => false | .props => false

/-- After item 9h: the alias gets the check its siblings already had. -/
def guardedAfter : Pred → Bool
  | .alias => true
  | p      => guardedBefore p

/-! ## §2  The arm is mixed

Not vacuous (a legal inhabitant survives every guard) and not uniformly legal
(an illegal inhabitant reached it).  Both halves are non-empty, which is exactly
the situation in which a single plan cannot be right. -/

theorem arm_has_a_legal_inhabitant :
    ∃ p, reaches p = true ∧ legal p = true ∧ guardedBefore p = false :=
  ⟨.props, by decide⟩

theorem arm_has_an_illegal_inhabitant :
    ∃ p, reaches p = true ∧ legal p = false ∧ guardedBefore p = false :=
  ⟨.alias, by decide⟩

/-! ## §3  Therefore no guard on the arm's condition is sound

The filed plan was to refute the arm — to find a scanner fact false at every
input reaching it.  Any such fact rejects `&a [b]`.  This is stated for an
ARBITRARY guard, so it is not a claim about the particular coupling that was
proposed; it rules out the whole shape of answer. -/

theorem no_refutation_of_this_arm_is_sound
    (g : Pred → Bool) (h_fires : ∀ p, reaches p = true → g p = true) :
    ∃ p, legal p = true ∧ g p = true :=
  ⟨.props, by decide, h_fires .props (by decide)⟩

/-- The contrapositive, in the form the scanner has to satisfy: a sound guard
    (one that never rejects a legal document) cannot fire on the whole arm. -/
theorem sound_guard_leaves_the_arm_inhabited
    (g : Pred → Bool) (h_sound : ∀ p, legal p = true → g p = false) :
    ∃ p, reaches p = true ∧ g p = false :=
  ⟨.props, by decide, h_sound .props (by decide)⟩

/-! ## §4  The three destinations, read off the shipped pipeline

`verdict` is what the pipeline does with each inhabitant TODAY; `destination` is
what that implies about the work.  The table is the diagnostic: it is computed
from observations, not from how hard the arm looks. -/

inductive Verdict where
  | rejects | acceptsCorrect | acceptsWrong
  deriving DecidableEq, Repr, BEq

inductive Destination where
  | refute | vocabulary | defect
  deriving DecidableEq, Repr, BEq

/-- The pipeline's verdict, given which guards are live.  An unguarded illegal
    input is `acceptsWrong` at the scanner — the parser catches these a layer
    later, which is why they were never a shipped over-acceptance and why only
    the accumulation proof noticed. -/
def verdict (guarded : Pred → Bool) (p : Pred) : Verdict :=
  if guarded p then .rejects
  else if legal p then .acceptsCorrect
  else .acceptsWrong

def destination : Verdict → Destination
  | .rejects        => .refute
  | .acceptsCorrect => .vocabulary
  | .acceptsWrong   => .defect

/-- Before the split the arm mapped to two destinations at once — the reason no
    single plan for it could be right. -/
theorem before_the_split_two_destinations :
    (allPreds.map fun p => destination (verdict guardedBefore p))
      = [.refute, .refute, .refute, .defect, .vocabulary] := by decide

/-- After it, one: every surviving inhabitant is a construction. -/
theorem after_the_split_one_destination :
    (allPreds.filter fun p => guardedAfter p = false).map
        (fun p => destination (verdict guardedAfter p))
      = [.vocabulary] := by decide

/-- The homogeneity that makes the construction well-posed: everything still
    reaching the arm is legal. -/
theorem remaining_inhabitants_all_legal :
    ∀ p, reaches p = true → guardedAfter p = false → legal p = true := by
  intro p; cases p <;> decide

/-- …and the new guard is sound: it fires on no legal document. -/
theorem the_split_guard_is_sound : ∀ p, legal p = true → guardedAfter p = false := by
  intro p; cases p <;> decide

/-! ## §5  Why the wrong plan looked right: a witness is not a set

`quoted` is a genuine inhabitant and is genuinely illegal.  From that single
observation the arm looks vacuous — and it is not, because `reaches` is constant
while `legal` is not.  The two facts below are the whole trap: they are both
true, and the first does not imply the second's negation being false. -/

theorem the_witness_that_was_used : reaches .quoted = true ∧ legal .quoted = false := by decide

theorem the_witness_underdetermines :
    ∃ p q, reaches p = reaches q ∧ legal p ≠ legal q :=
  ⟨.quoted, .props, by decide, by decide⟩

/-- Stated as the inference that was actually made, and is invalid: "some
    inhabitant is illegal" does not give "every inhabitant is illegal". -/
theorem some_illegal_does_not_give_all_illegal :
    (∃ p, reaches p = true ∧ legal p = false) ∧
    ¬(∀ p, reaches p = true → legal p = false) := by
  refine ⟨⟨.quoted, by decide⟩, fun h => ?_⟩
  exact absurd (h .props (by decide)) (by decide)

/-! ## §6  The sweep

Generated from the condition, not recalled: every predecessor, its verdict
before and after.  One row changed, and it is the row that turned a mixed arm
into a homogeneous one. -/

#guard allPreds.length == 5
#guard (allPreds.filter fun p => legal p) == [Pred.props]
#guard (allPreds.filter fun p => verdict guardedBefore p == .acceptsWrong) == [Pred.alias]
#guard (allPreds.filter fun p => verdict guardedAfter p == .acceptsWrong) == ([] : List Pred)
#guard (allPreds.filter fun p => verdict guardedBefore p != verdict guardedAfter p)
        == [Pred.alias]
#guard (allPreds.filter fun p => guardedAfter p).length == 4

/-! ## §7  Axiom pins

The load-bearing claims are decidable facts about a five-element type; the
`∀`/`∃` statements go through `propext` only. -/

/-- info: 'Tests.Reflections.SplitAMixedArmBeforePricingIt.no_refutation_of_this_arm_is_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms no_refutation_of_this_arm_is_sound

/-- info: 'Tests.Reflections.SplitAMixedArmBeforePricingIt.remaining_inhabitants_all_legal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms remaining_inhabitants_all_legal

/-- info: 'Tests.Reflections.SplitAMixedArmBeforePricingIt.some_illegal_does_not_give_all_illegal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms some_illegal_does_not_give_all_illegal

end Tests.Reflections.SplitAMixedArmBeforePricingIt

end Blanket
