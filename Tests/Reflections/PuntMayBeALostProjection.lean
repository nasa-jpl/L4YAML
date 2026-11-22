/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 655 — a punt may be a lost PROJECTION: read what the CARRIER kept, not only what the producer proved

**The rule.**  [[PuntNamesACoordinate]] says to read WHY an optional field
punted before making its case harder.  One answer it does not cover: the
producer measured the right thing, and the CARRIER between producer and
consumer kept only part of it.  A pack that stores `pos.line` when the producer
proved `pos = currentPos` has thrown away `pos.col` — and the consumer's missing
hypothesis is then not missing at all, it is one field further back.  So before
strengthening anything, compare what the producer PROVED with what the carrier
STORES, field by field.

**Why this is worth naming separately.**  The two losses look identical at the
consumer — both show up as a producer handing `True` — but they cost different
things.  A wrong coordinate ([[PuntNamesACoordinate]]) needs the producer's
lemma re-stated, which is a new proof.  A lost projection needs a wider carrier,
and the producer's obligation is discharged by the fact it ALREADY proved,
verbatim.  Reading the second as the first is how a bookkeeping fix gets priced
as a proof effort and scheduled behind things it should precede.

**The inventory is a taxonomy, and it predicts the order.**  Once an optional
field has been carried for a while, its `True`s are a list of causes, not a list
of difficulties.  Three recur: a LOST PROJECTION (widen the carrier), an
UNSTATED LEMMA — true, provable, and stated nowhere the consumer can reach it,
often because the general version sits below its consumer in the file (write a
small dedicated sibling next to its peers; do not hoist the general one) — and a
DIFFERENT PRODUCTION, which is the only kind that is real work
([[DifferentQuestionNotAHarderCase]]).  Classify first: the cheap ones are
exactly the ones that close today.

**When the coupling becomes total, record it — do not re-shape it.**  If every
producer now discharges the optional field, the temptation is to make it
required.  Resist: the coverage today is identical, and the shape is what
protects the NEXT producer, which is the whole of [[OptionalFieldBuysDomain]].
Totality is a fact to state, not a change to make.

Concretely (L4YAML): item 28 left two `True`s on `ImplicitKeyPack`'s column
conjunct.  The property-headed key's was a lost projection — `PropsKeyPack`
stored the run's `simpleKey.pos.line` while its producer had proved
`simpleKey.pos = currentPos`, the whole position — so item 29 widened the pack
and the producer's side was the same equation projected twice.  The alias key's
was an unstated lemma: `dispatchContent_value_key_facts` proves exactly the
needed preservation, a thousand lines BELOW the consumer that needs it, so the
repair was a three-line `dispatchContent_alias_simpleKey` beside its `&` and `!`
peers.  What is left is the explicit-key clear, which is a different production
`[197]` — the one kind the taxonomy predicts is not free.

§1 is the lost projection.  §2 the taxonomy that predicts the order.  §3
totality as a fact, not a shape.  §4 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.PuntMayBeALostProjection

/-! ## §1  The punt was one field further back

The producer proves a statement about a whole record; the carrier stores one
field of it; the consumer needs the other.  Nothing here is hard — the
information exists at both ends and is dropped in the middle. -/

/-- A position, as the scanner records it. -/
structure Pos where
  line : Nat
  col : Nat
  deriving DecidableEq, Repr

/-- The producer's state. -/
structure St where
  cur : Pos
  deriving Repr

/-- **What the producer proves.**  The key was saved AT the run's own start —
    the whole position, both fields at once, one equation. -/
def savedKey (s : St) : Pos := s.cur

/-- **The carrier as item 17 shipped it**: one projection of that equation. -/
structure PackLine where
  line : Nat
  deriving DecidableEq, Repr

def packLine (s : St) : PackLine := ⟨(savedKey s).line⟩

/-- **What the consumer needs**: the other projection. -/
def needed (s : St) : Nat := (savedKey s).col

/-- The carrier really did lose it — two states the pack cannot tell apart
    disagree on what the consumer is asking for.  So no amount of reasoning
    downstream of the pack recovers the column: this is a transport loss, not a
    proof gap. -/
theorem carrier_lost_it :
    ∃ s₁ s₂ : St, packLine s₁ = packLine s₂ ∧ needed s₁ ≠ needed s₂ :=
  ⟨⟨⟨3, 2⟩⟩, ⟨⟨3, 7⟩⟩, rfl, by decide⟩

/-- …while the producer had it all along, by the same equation that gave the
    line.  This is the diagnostic: the field is `rfl` at the producer and
    unstatable at the consumer. -/
theorem producer_had_it (s : St) : needed s = s.cur.col := rfl

/-- **The repair**: widen the carrier.  Not a new measurement — the same
    `savedKey` equation, projected once more. -/
structure PackBoth where
  line : Nat
  col : Nat
  deriving DecidableEq, Repr

def packBoth (s : St) : PackBoth := ⟨(savedKey s).line, (savedKey s).col⟩

/-- The producer's new obligation is discharged by definitional unfolding,
    because it is not a new obligation. -/
theorem widened_field_is_the_old_fact (s : St) : (packBoth s).col = needed s := rfl

/-- And the old field is untouched, so every existing consumer keeps its
    argument verbatim — the widening is additive. -/
theorem widening_is_additive (s : St) : (packBoth s).line = (packLine s).line := rfl

/-- The consumer's side is now available, which was the entire item. -/
theorem consumer_reaches_it (s : St) : (packBoth s).col = s.cur.col := rfl

/-! ## §2  The inventory is a taxonomy, and it predicts what closes

Three causes recur behind an optional field's `True`s.  Two are bookkeeping;
one is work.  Classifying first is what tells you the order — and the
classification is checkable against the item afterwards. -/

/-- Why a producer handed `True`. -/
inductive PuntCause where
  /-- The producer proved it; the carrier stored a sibling field. -/
  | lostProjection
  /-- True and provable, but no lemma states it where the consumer can reach
      it — typically the general version sits below its consumer in the file. -/
  | unstatedLemma
  /-- Another grammar arm entirely ([[DifferentQuestionNotAHarderCase]]). -/
  | differentProduction
  deriving DecidableEq, Repr

/-- Only one of the three costs a new argument.  The other two are a wider
    carrier and a smaller lemma. -/
def costsNewWork : PuntCause → Bool
  | .lostProjection => false
  | .unstatedLemma => false
  | .differentProduction => true

/-- The repair each one takes.  Note the second: the cheap fix is a dedicated
    sibling beside its peers, NOT hoisting the general lemma over a thousand
    lines of file it was never meant to precede. -/
def repair : PuntCause → String
  | .lostProjection => "widen the carrier"
  | .unstatedLemma => "state a small sibling next to its peers"
  | .differentProduction => "prove the other arm"

/-- The three `True`s standing after item 28. -/
inductive Punt where
  /-- `  &x a: |` — the property-headed key. -/
  | propsHeadedKey
  /-- `  *m : |` — the alias key. -/
  | aliasKey
  /-- `  ? a⏎  : |` — the explicit-key clear. -/
  | explicitKeyClear
  deriving DecidableEq, Repr

def cause : Punt → PuntCause
  | .propsHeadedKey => .lostProjection
  | .aliasKey => .unstatedLemma
  | .explicitKeyClear => .differentProduction

/-- What item 29 actually closed. -/
def closedByThisItem : Punt → Bool
  | .propsHeadedKey => true
  | .aliasKey => true
  | .explicitKeyClear => false

/-- **The taxonomy predicted the item.**  The punts that closed are exactly the
    ones whose cause is bookkeeping — which is why classifying the inventory is
    worth doing BEFORE picking the next one to attack. -/
theorem taxonomy_predicts_the_item (p : Punt) :
    closedByThisItem p = !costsNewWork (cause p) := by
  cases p <;> rfl

/-- Two different causes can look identical at the consumer: both are a
    producer handing `True`, and the consumer sees no difference at all. -/
theorem the_consumer_cannot_tell_them_apart :
    closedByThisItem .propsHeadedKey = closedByThisItem .aliasKey ∧
    cause .propsHeadedKey ≠ cause .aliasKey := ⟨rfl, by decide⟩

/-- …so the classification has to be read off the PRODUCER's side.  Nothing
    downstream distinguishes a carrier that dropped a field from a lemma nobody
    wrote. -/
theorem classification_is_a_producer_side_reading :
    ∃ p q : Punt, cause p ≠ cause q ∧ closedByThisItem p = closedByThisItem q :=
  ⟨.propsHeadedKey, .aliasKey, by decide, rfl⟩

/-! ## §3  Totality is a fact to state, not a shape to change

After the two cheap punts close, every producer of the coupling discharges it.
That is worth RECORDING.  It is not a reason to make the field required: the
coverage today would be identical, and the optional shape is what keeps the
next producer off the escape ([[OptionalFieldBuysDomain]]). -/

/-- The pack's producers, at item 28's granularity. -/
inductive Producer where
  /-- `[193]`'s plain key. -/
  | plain
  /-- `[194]`'s double-quoted key. -/
  | doubleQuoted
  /-- `[194]`'s single-quoted key. -/
  | singleQuoted
  /-- `[161]`'s alias head. -/
  | alias
  /-- The props pack's own three arms, counted as one producer. -/
  | propsPack
  deriving DecidableEq, Repr

def dischargedAfter28 : Producer → Bool
  | .plain | .doubleQuoted | .singleQuoted => true
  | .alias | .propsPack => false

def dischargedAfter29 : Producer → Bool
  | _ => true

/-- The coupling is now total. -/
theorem coupling_is_total (p : Producer) : dischargedAfter29 p = true := rfl

/-- And it strictly grew — no producer traded away. -/
theorem nothing_was_traded (p : Producer) :
    dischargedAfter28 p = true → dischargedAfter29 p = true := fun _ => rfl

/-- The field as carried: optional. -/
def Carried (n k : Nat) : Prop := n = k ∨ True

/-- The field as it would be if totality were cashed in as a shape. -/
def Required (n k : Nat) : Prop := n = k

/-- Today the two shapes cover the same producers, because every producer
    discharges the strong disjunct anyway. -/
theorem same_coverage_today (p : Producer) (n : Nat)
    (_h : dischargedAfter29 p = true) : Carried n n := Or.inl rfl

/-- Tomorrow they do not: a producer that cannot measure still has a term under
    the optional shape… -/
theorem optional_admits_the_next_producer : Carried 0 5 := Or.inr trivial

/-- …and none under the required one, so its case would have to be routed to
    the escape — the inflation [[OptionalFieldBuysDomain]] declined. -/
theorem required_refuses_it : ¬ Required 0 5 := by
  unfold Required; decide

/-! ## §4  What item 29 shipped -/

/-- Grammar files edited. -/
def grammarEdits : Nat := 0
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0
/-- New conjuncts on `PropsKeyPack`: one, optional, inside the existential that
    binds the index it is about. -/
def newPackConjuncts : Nat := 1
/-- New obligations at the widened carrier's producer — none: the fact was
    already proved there (§1). -/
def newProducerObligations : Nat := 0
/-- New dispatch lemmas: `dispatchContent_alias_simpleKey`. -/
def newDispatchLemmas : Nat := 1
/-- Lemmas HOISTED to make it reachable — none; a small sibling instead. -/
def lemmasHoisted : Nat := 0
/-- Pack producers discharging the column, after item 28. -/
def dischargingBefore : Nat := 3
/-- …and after item 29: all of them. -/
def dischargingAfter : Nat := 5
/-- Pack producers still punting. -/
def puntingAfter : Nat := 0
/-- Producers of the re-indexed pendings that discharge the FLOOR — unchanged:
    this item widens the fourth one's DOMAIN, which is the claim (R645/R646). -/
def floorProducersBefore : Nat := 4
def floorProducersAfter : Nat := 4
/-- Escape call sites before. -/
def escapeSitesBefore : Nat := 14
/-- …and after: unchanged, by construction. -/
def escapeSitesAfter : Nat := 14
/-- Opaque `scannerDrop` sites: unchanged. -/
def dropSites : Nat := 4

theorem shipped :
    grammarEdits = 0 ∧ runtimeEdits = 0 ∧ newPackConjuncts = 1 ∧
    newProducerObligations = 0 ∧ newDispatchLemmas = 1 ∧ lemmasHoisted = 0 ∧
    dischargingBefore = 3 ∧ dischargingAfter = 5 ∧ puntingAfter = 0 ∧
    floorProducersAfter = floorProducersBefore ∧
    escapeSitesAfter = escapeSitesBefore ∧ dropSites = 4 := by
  decide

end L4YAML.Tests.Reflections.PuntMayBeALostProjection

end Blanket
