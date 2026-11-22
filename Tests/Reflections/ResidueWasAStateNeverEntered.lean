/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 661 — the residue was a state the machine never enters

**The rule.**  There are three ways to empty a deferred arm, and the third is
the one that gets missed.  You can DERIVE the shape it stands for (a missing
production), you can REFUTE it from what the machine did (a fact about the
scan) — or you can find that the arm describes a state the machine never
enters.  The third needs nothing about the input at all.  What blocks it is
that the case carrying the arm names no state: a constructor with no fields is
a claim that something is absent, and absence supports neither a derivation nor
a refutation.  Give it the one fact it stands for and the arm has no inhabitant
left.

**And a vacuous slot filled with a dummy is where that work lands.**  While the
case is evidence-free, ANY inhabitant satisfies it, so producers that reach the
slot under an impossible hypothesis fill it with the cheapest one to hand and
the impossibility goes unrecorded.  Nothing is wrong until the type gets
stronger; then every dummy becomes an obligation, and the ones that were
vacuous all along are discharged by saying so.  That is not a cost of the
field — it is the field collecting a debt.  Prefer `nofun` to a dummy at an
unreachable slot: it is the same length and it states the fact.

**The base case is a specification of the entry point.**  A field the seed
cannot discharge is a claim about the initial state, and the initial state is
CODE.  So the failure has two readings — the field is wrong, or the entry point
is — and they are distinguished by asking what the field means, not by asking
which is easier to change.

Concretely (L4YAML): `PendingNode.noPending` carried nothing, so the inline
residue at the block-dispatch arm — an indicator reached from a park that
crossed no break and sits off column 0 — could be neither produced nor refuted.
It also had no inhabitant: with nothing pending and no flow open the machine
parks at a line start.  Adding `sp.col = 0 ∨ sc.inFlow = true` emptied the arm;
fourteen dummies in flow producers became twelve `nofun`s and two depth
arguments; and the SEED could not discharge it, because the scan spent a
column on the byte order mark (§5.2 says it spends none) — so `﻿a: 1⏎b: 2`
dedented below its own mapping and `﻿---` was not at column 0 to be read as
`[203] c-directives-end`.  The invariant found a runtime defect at the one
place a runtime defect can hide from every test that starts at column 0.

§1 the evidence-free case, and the field that names the state.  §2 the dummy
and the vacuity.  §3 the seed as a specification.  §4 the disjunction is two
families named, not a weakening.  §5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.ResidueWasAStateNeverEntered

/-! ## §1  A case that carries nothing says nothing

`Park` is where the machine stopped.  `atLineStart` is the fact the arm turns
on.  The evidence-free constructor admits both answers, so the arm about it is
open at any price in grammar. -/

structure Park where
  col : Nat
deriving DecidableEq

/-- The arm's own question: did the step land at a line start? -/
def atLineStart (p : Park) : Bool := p.col == 0

/-- **Evidence-free: both answers are constructible.**  Nothing about the input
    settles which park is in hand, because the case did not say. -/
theorem the_evidenceless_case_says_nothing :
    (∃ p : Park, atLineStart p = true) ∧ (∃ p : Park, atLineStart p = false) :=
  ⟨⟨⟨0⟩, rfl⟩, ⟨⟨3⟩, rfl⟩⟩

/-- The field, as the two families that actually park: a block-context stop is
    a line start; a flow-context stop is anywhere. -/
def Named (p : Park) (inFlow : Bool) : Prop := p.col = 0 ∨ inFlow = true

/-- **Named: the arm has no inhabitant.**  The consumer already holds
    `inFlow = false` — that is what selects the block dispatch — so the
    residue's own premise contradicts the field. -/
theorem named_state_empties_the_arm {p : Park} (h : Named p false)
    (h_mid : p.col ≠ 0) : False :=
  h_mid (h.resolve_right (by decide))

/-- …and it is not that the fact is strong; it is that it exists.  The same
    park in flow context is untouched. -/
theorem the_flow_family_is_untouched : Named ⟨3⟩ true := Or.inr rfl

/-! ## §2  The dummy in the vacuous slot

A producer that reaches the slot under an impossible hypothesis.  While the
case is free, the cheapest inhabitant does; once the case carries a fact, the
dummy owes it — and cannot pay, because the dummy was never a real park. -/

/-- A producer's obligation, guarded by a depth that is never zero here. -/
def Guarded (depth : Nat) (α : Type) : Type := depth = 0 → α

/-- The dummy: any inhabitant, chosen because the type asked for one. -/
def dummyPark : Park := ⟨3⟩

/-- **With no field, the dummy is fine.** -/
def producer_with_dummy (depth : Nat) : Guarded depth Park := fun _ => dummyPark

/-- **With the field, the dummy owes a fact it has not got** — the slot it
    fills is off a line start and there is no flow to appeal to. -/
theorem the_dummy_cannot_pay : ¬ Named dummyPark false := by
  rintro (h | h) <;> exact absurd h (by decide)

/-- **The vacuity pays instead, and says what was true all along.**  This is
    `nofun` written out: the hypothesis is the contradiction. -/
def producer_by_vacuity (depth : Nat) (h_pos : 1 ≤ depth) :
    Guarded depth (PLift (Named dummyPark false)) :=
  fun h => absurd h (by omega)

/-- The count that matters: strengthening the case did not add work at the
    vacuous producers, it CONVERTED work that was already owed. -/
def dummiesFound : Nat := 14
def dummiesDischargedByVacuity : Nat := 12
def dummiesNeedingAnArgument : Nat := 2

theorem the_field_collected_a_debt :
    dummiesDischargedByVacuity + dummiesNeedingAnArgument = dummiesFound := by decide

/-! ## §3  The seed is a specification of the entry point

The one producer that is not vacuous is the initial state, and it is not a
proof — it is the code that starts the scan.  Here that code spent a column on
a marker that spends none, and the field is what asked. -/

/-- What the entry point charges for the byte order mark. -/
def seedCol (bomCost : Nat) : Nat := bomCost

/-- The field, read at the seed. -/
def seedNamed (bomCost : Nat) : Prop := seedCol bomCost = 0

/-- **The field is exactly the defect's negation.**  It cannot be discharged
    while the marker costs a column, and it is immediate once it does not. -/
theorem seed_discharges_iff_free : seedNamed 0 ∧ ¬ seedNamed 1 :=
  ⟨rfl, fun h => Nat.succ_ne_zero 0 h⟩

/-- The first consequence: with the first line one deeper than the rest, a
    sibling at the same indentation reads as a DEDENT. -/
def laterLineCol : Nat := 0
def dedents (bomCost : Nat) : Bool := laterLineCol < seedCol bomCost

theorem a_column_of_drift_dedents : dedents 1 = true ∧ dedents 0 = false := by
  exact ⟨rfl, rfl⟩

/-- The second: a marker whose whole reading is "at column 0" is not read at
    all.  Two unrelated-looking failures, one arithmetic. -/
def markerRead (bomCost : Nat) : Bool := seedCol bomCost == 0

theorem the_marker_is_lost_by_the_same_one :
    markerRead 1 = false ∧ markerRead 0 = true := by
  exact ⟨rfl, rfl⟩

/-- And the reason a test suite can miss it for a whole campaign: every input
    that does not carry the marker is at cost 0 already. -/
def carriesMarker (bomCost : Nat) : Bool := bomCost != 0

theorem unmarked_inputs_cannot_see_it (_h : carriesMarker 0 = false) :
    seedNamed 0 := rfl

/-! ## §4  A disjunction can be two families named

`p.col = 0 ∨ inFlow = true` looks like a weakening — the shape a field takes
when it cannot be proved.  It is not: the two disjuncts are the two producer
families, each discharging its own, and the consumer holds the fact that picks
one ([[OptionalFieldBuysDomain]] is the case where producers genuinely differ;
this is the case where they differ and both are total). -/

inductive Family where
  | block
  | flow
deriving DecidableEq

def parksAt : Family → Park
  | .block => ⟨0⟩
  | .flow => ⟨3⟩

def inFlowOf : Family → Bool
  | .block => false
  | .flow => true

/-- Every producer discharges the field — from its own side. -/
theorem every_family_discharges (f : Family) : Named (parksAt f) (inFlowOf f) := by
  cases f
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- …and the consumer's own hypothesis selects the side it needs, so the
    disjunction costs it nothing. -/
theorem consumer_reads_one_side {f : Family} (h : inFlowOf f = false) :
    (parksAt f).col = 0 := by
  cases f
  · rfl
  · exact absurd h (by decide)

/-! ## §5  What item 35 shipped -/

/-- Fields added to the evidence-free case: one, required. -/
def fieldsAdded : Nat := 1
/-- Producers touched (the fourteen dummies plus the seed). -/
def producersTouched : Nat := 15
/-- Grammar productions added: none.  One production's INDEX was corrected —
    the BOM's own — which is a defect fixed, not a construct built. -/
def newProductions : Nat := 0
def grammarIndicesCorrected : Nat := 1
/-- Runtime files edited: the two scan entry points and their two states. -/
def runtimeFilesEdited : Nat := 4
/-- Documents the runtime accepted wrongly, before and after: `﻿a: 1⏎b: 2`
    refused, `﻿---` misread.  Both pipelines, identically. -/
def bomShapesBroken : Nat := 2
def bomShapesBrokenAfter : Nat := 0
/-- The escape's call sites, before and after. -/
def escapeSitesBefore : Nat := 7
def escapeSitesAfter : Nat := 6
/-- `scannerDrop` — a different obstruction, untouched. -/
def scannerDropBefore : Nat := 4
def scannerDropAfter : Nat := 4

theorem shipped :
    fieldsAdded = 1 ∧ producersTouched = 15 ∧ newProductions = 0 ∧
    grammarIndicesCorrected = 1 ∧ runtimeFilesEdited = 4 ∧
    bomShapesBrokenAfter < bomShapesBroken ∧
    escapeSitesAfter < escapeSitesBefore ∧
    scannerDropBefore = scannerDropAfter := by
  decide

end L4YAML.Tests.Reflections.ResidueWasAStateNeverEntered

end Blanket
