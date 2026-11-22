/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # Cross the indices, and price the residual by DATUM (Reflection 629)

Reflection 628 split a blocked step by its index and found four classes at what
it recorded as three prices: two total-receptive (free), one total-refutable
(wanting a guard), one mixed (wanting a discriminator).  Two of those classes
stayed open, and the plan carried them as TWO obligations because their KINDS
differed — a refutable class asks for a refutation, a mixed one asks for a
producer plus a discriminator, and those read like different work.

They were one obligation.  This file is the two corrections (§3, §4) and the
rule they compose into (§5).

**The kind is not the price.**  A class's kind says what SHAPE its obligation
has; what it COSTS is the datum that decides it.  Two classes of different kinds
can read the same datum, and then they are one piece of work — which the plan
will not say unless the residual is grouped by datum (§3).  The trap is that a
refutable class always admits *some* refuting guard, so a plausible per-class
answer is always available, and finding one ends the search before the question
"does a neighbour's datum already cover this?" is ever asked.

**A second index re-classifies the first.**  The step here has two indices, and
crossing them is cheap: the same tail is MIXED in one row and NOT A STATE in the
other, because the second index constrains reachability (§4).  Cells handed back
that way cost nothing — the refutation is a guard that shipped nine items
earlier, and the invariant already carries it as a field.

L4YAML DOCS items 9n and 9o, 2026-08-09.  Row `white` is an empty interior gap,
row `props` a held `[96] c-ns-properties` run; the residual datum is the
scanner's pending-simple-key reservation slot, and the shipped one is item 9b's
flow-adjacency guard.
-/

namespace Tests.Reflections.CrossIndicesPriceByDatum

/-! ## §0  Two indices, and the cells they make -/

inductive Tail where
  | sep | question | colon | value
  deriving DecidableEq, Repr, BEq

/-- The second index: what the step is holding when it fires. -/
inductive Gap where
  | white   -- nothing held
  | props   -- a scanned-but-unattached property run
  deriving DecidableEq, Repr, BEq

abbrev Cell := Gap × Tail

def allTails : List Tail := [.sep, .question, .colon, .value]
def allGaps : List Gap := [.white, .props]
def allCells : List Cell := allGaps.flatMap (fun g => allTails.map (fun t => (g, t)))

#guard allCells.length == 8

/-! ## §1  Each cell's kind

`unreachable` is the kind that only appears once there is a second index: the
cell is not inhabited at all, so it is neither work nor a refutation to write. -/

inductive Kind where
  | receptive      -- every frame here takes the step: write it, free
  | refutable      -- no frame here takes it: refute it
  | mixed          -- some do, some do not: the hard one
  | unreachable    -- no such state
  deriving DecidableEq, Repr, BEq

def kindAt : Cell → Kind
  | (.white, .sep) | (.white, .question) => .receptive
  | (.white, .colon) => .refutable
  | (.white, .value) => .mixed
  | (.props, .sep) | (.props, .question) => .receptive
  | (.props, .colon) => .refutable
  | (.props, .value) => .unreachable

/-! ## §2  Each cell's datum, and whether it is already in hand -/

inductive Datum where
  | adjacency    -- "a property may not follow a completed value" (already shipped)
  | entryStart   -- the machine's pending-key reservation slot (not yet paid for)
  deriving DecidableEq, Repr, BEq

/-- What decides the cell — `none` when nothing does, because it is total. -/
def datumAt : Cell → Option Datum
  | (.white, .sep) | (.white, .question) => none
  | (.white, .colon) | (.white, .value) => some .entryStart
  | (.props, .sep) | (.props, .question) => none
  | (.props, .colon) => some .entryStart
  | (.props, .value) => some .adjacency

/-- A datum already available costs nothing to use. -/
def shipped : Datum → Bool
  | .adjacency => true
  | .entryStart => false

def settled (c : Cell) : Bool :=
  match datumAt c with
  | none => true
  | some d => shipped d

def openCells : List Cell := allCells.filter (fun c => !settled c)

/-- Order-preserving duplicate removal (no Mathlib here). -/
def dedup {α : Type} [BEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

-- The classification is honest: nothing needs a datum unless it is a cell the
-- step cannot take blind, and that is exactly the non-receptive cells.
#guard allCells.all (fun c => (datumAt c == none) == (kindAt c == Kind.receptive))

#guard (allCells.filter settled).length == 5
#guard openCells.length == 3

/-! ## §3  The correction that matters: group the residual by DATUM

By kind the residual is two things — a refutation and a discriminated producer.
By datum it is one.  Counting the kinds is what put "two prices" in the plan;
counting the data is what takes it out. -/

def kindsOpen : List Kind := dedup (openCells.map kindAt)

def dataOpen : List Datum := dedup (openCells.filterMap datumAt)

#guard kindsOpen.length == 2          -- refutable AND mixed: two shapes…
#guard dataOpen.length == 1           -- …one datum: ONE obligation
#guard dataOpen == [Datum.entryStart]

-- The refutable cells and the mixed cell read the SAME datum.  That is the whole
-- correction, and it is invisible to any grouping by kind.
#guard openCells.all (fun c => datumAt c == some Datum.entryStart)
#guard (openCells.filter (fun c => kindAt c == Kind.refutable)).length == 2
#guard (openCells.filter (fun c => kindAt c == Kind.mixed)).length == 1

/-! ## §4  …and the second index re-classified the first

The `.value` tail is the mixed class on one row and not a state at all on the
other.  So a kind belongs to a CELL, never to an index value: reading it off the
first index alone is what makes a solved cell look like open work. -/

def kindsOfTail (t : Tail) : List Kind := allGaps.map (fun g => kindAt (g, t))

#guard kindsOfTail Tail.value == [Kind.mixed, Kind.unreachable]
#guard (allTails.filter (fun t => (dedup (kindsOfTail t)).length > 1)).length == 1

-- The cell the crossing handed back is settled by a datum that already exists —
-- no guard was designed for it, and none had to be.
#guard (allCells.filter (fun c => kindAt c == Kind.unreachable)) == [(Gap.props, Tail.value)]
#guard datumAt (Gap.props, Tail.value) == some Datum.adjacency
#guard shipped Datum.adjacency

/-! ## §5  The payoff

Crossing doubled the cells and did not double the work: four receptive cells
instead of two, one handed back for free, and a residual that shrank from two
named obligations to one. -/

#guard (allCells.filter (fun c => kindAt c == Kind.receptive)).length == 4

-- Read on the first index alone — the `white` row standing for the whole step —
-- there are 4 classes, 2 of them settled, and a residual of 2 classes.
#guard (allTails.filter (fun t => settled (Gap.white, t))).length == 2
#guard (allTails.filter (fun t => !settled (Gap.white, t))).length == 2

-- Crossed: twice the cells, but the settled ones more than doubled and the
-- residual grew by one CELL while shrinking to one DATUM.
#guard (allCells.filter settled).length == 5
#guard dataOpen.length == 1

-- The honest statement of what is left, and it is a single sentence:
-- every open cell wants the entry-start pointer, and nothing else.
#guard openCells.all (fun c => datumAt c == some Datum.entryStart)
#guard !(openCells.any (fun c => datumAt c == some Datum.adjacency))

end Tests.Reflections.CrossIndicesPriceByDatum

end Blanket
