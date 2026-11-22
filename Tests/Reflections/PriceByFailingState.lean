/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 630 — price a threaded datum by where its invariant FAILS

**The rule.** When a plan prices "thread this new datum through the tower", it
counts CONSUMPTION SITES — the places that will have to read it. That number is
almost always wrong, and always too big. A threaded datum is carried by an
INVARIANT, and the invariant already holds nearly everywhere; what the work
actually costs is the handful of STATES where it fails. Price those.

**The corollary that makes it cheap.** At a state where the carrying invariant
fails, the datum is usually DEAD — that is generally *why* the machine was
allowed to leave it in a shape the invariant rejects. A dead value can be
normalized without changing behaviour, and that normalization, not the
threading, is the whole discharge.

**The instance (L4YAML item 9p).** Item 9o priced the `:` step's residual as one
datum. Building it found the datum needs a `simpleKey.tokenIndex` reading at the
emitter's `:` step, and `grep` said sixteen gateway call sites. Seven of the
eight pair-list assemblers already carry the saved-key take-side re-anchor, so
one bridge lemma (`savedKeyAtEntryBoundary_of_take`) discharges all fourteen of
their calls in one line each. The eighth scans its keys with the plain
`EmitScansInFlow`, which exposes no reservation index — and switching it to the
saved-key substrate is blocked at exactly ONE state: its own recursion's tail,
after the `,`, where `scanFlowEntry` leaves `simpleKey.possible = true` pointing
at the *previous value's* reservation. Every prefix-preservation lemma in the
tower goes through `SimpleKeyAboveFloor`, whose first component is exactly "a
pending key points at or above the incoming array's end" — false there, and
nowhere else.

That stale key is dead: `scanFlowEntry` sets `simpleKeyAllowed := true` and
`explicitKeyLine := none`, so preprocessing's `saveSimpleKey` overwrites it
before any dispatch can read it. Clearing it at the `,` is behaviour-preserving
(351/351 suite sources byte-identical in both pipelines), and it is the whole
unblocking move.

Self-contained: models the two pricings over the shipped instance's shape and
pins that they differ by a factor of sixteen.
-/

namespace L4YAML.Tests.Reflections.PriceByFailingState

/-- The eight pair-list assemblers that reach the `:` gateway. -/
inductive Assembler where
  | nonempty | keyshape | tokvals | recmapbody | recmapbodyDeep
  | blockNonempty | safebody | allScalarBody
  deriving DecidableEq, Repr

/-- The two states a pair-list assembler starts a pair in. -/
inductive PairState where
  /-- Right after the opening `{` or `[`. -/
  | pairStart
  /-- Right after the `,` that ended the previous entry. -/
  | tailStart
  deriving DecidableEq, Repr

open Assembler PairState

def assemblers : List Assembler :=
  [nonempty, keyshape, tokvals, recmapbody, recmapbodyDeep,
   blockNonempty, safebody, allScalarBody]

def states : List PairState := [pairStart, tailStart]

/-- Each assembler visits the gateway twice: once for a singleton pair list, once
    for the head of a `cons`. That doubling is what a `grep` for the gateway
    counts, and it is the number a consumption-priced plan writes down. -/
def gatewayCallsPer : Nat := 2

/-- Does this assembler's key scan already expose the reservation index (the
    saved-key substrate's take-side re-anchor)? -/
def carriesReservationIndex : Assembler → Bool
  | nonempty => false
  | _ => true

/-- Does the carrying invariant (`SimpleKeyAboveFloor` at the incoming array's
    end) hold in this state? -/
def invariantHolds : PairState → Bool
  | pairStart => true
  | tailStart => false

/-- Is the pending simple key LIVE in this state — can any dispatch read it
    before it is overwritten? -/
def valueLive : PairState → Bool
  | pairStart => true
  | tailStart => false

/-- The state the one uncarried assembler's own recursion re-enters at. -/
def reentersAt : Assembler → PairState
  | keyshape => pairStart   -- delegates its tail to `nonempty`, never to itself
  | _ => tailStart

/-- Pricing the work by counting what will CONSUME the datum. -/
def priceByConsumption : Nat := assemblers.length * gatewayCallsPer

/-- Pricing the work by counting the states where the CARRYING INVARIANT fails. -/
def priceByFailure : Nat := (states.filter (fun s => !invariantHolds s)).length

/-- The assemblers a bridge lemma settles outright. -/
def carried : List Assembler := assemblers.filter carriesReservationIndex

/-- The assemblers that are actually work. -/
def uncarried : List Assembler := assemblers.filter (fun a => !carriesReservationIndex a)

-- ═══ §1 The shape of the instance ═══

-- Eight assemblers, sixteen gateway calls: the number `grep` reports.
#guard assemblers.length == 8
#guard priceByConsumption == 16

-- Seven of the eight already carry the datum; one bridge lemma settles them.
#guard carried.length == 7
#guard uncarried == [Assembler.nonempty]

-- ═══ §2 The two pricings differ by the factor the plan got wrong ═══

#guard priceByFailure == 1
#guard priceByConsumption == 16 * priceByFailure

-- The failing state is a STATE, not a site: no assembler is singled out by it.
#guard (states.filter (fun s => !invariantHolds s)) == [PairState.tailStart]

-- ═══ §3 The corollary: the invariant fails exactly where the value is dead ═══

-- Not a coincidence — the machine was allowed to leave the key in a
-- floor-violating shape precisely BECAUSE nothing reads it there.
#guard states.all (fun s => invariantHolds s == valueLive s)

-- So the fix is a normalization at one state, not a threading through sixteen.
#guard (states.filter (fun s => !valueLive s)).length == 1

-- ═══ §4 Why the one uncarried assembler is the one that is blocked ═══

-- It is blocked because its own recursion re-enters at the failing state; the
-- assembler that does NOT re-enter there needs no normalization at all.
#guard uncarried.all (fun a => reentersAt a == PairState.tailStart)
#guard (assemblers.filter (fun a => reentersAt a == PairState.pairStart))
        == [Assembler.keyshape]

-- And `keyshape` — which already carries the datum AND avoids the failing state
-- — is the existence proof that the substrate works: the discharge is not
-- blocked on the datum, only on the one state.
#guard carriesReservationIndex Assembler.keyshape
        && (reentersAt Assembler.keyshape == PairState.pairStart)

-- ═══ §5 What a consumption-priced plan would have bought ═══

-- Threading at every call site: sixteen edits, all of them redundant with the
-- bridge, and none of them touching the one thing that is actually blocked.
#guard priceByConsumption - carried.length * gatewayCallsPer == 2
#guard (uncarried.length * gatewayCallsPer) == 2

-- The honest budget: one bridge lemma, two of the sixteen calls, one
-- normalization — and the normalization is the only part that is not mechanical.
#guard priceByFailure + uncarried.length == 2

end L4YAML.Tests.Reflections.PriceByFailingState

end Blanket
