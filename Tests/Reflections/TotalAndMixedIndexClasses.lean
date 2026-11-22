/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # Split the index before pricing the transition (Reflection 628)

A state family indexed by a coarse class, and a new transition to write over it.
The instinct is to price the transition as one thing — "the `:` arm is blocked" —
and to look for one fact that unblocks it.  Split by the index first and the arm
stops being one thing:

* some index values are inhabited **only** by receptive constructors.  The
  transition is TOTAL there and costs nothing but the writing (§2);
* some are inhabited **only** by refutable ones.  Also total — in the refuting
  direction — and what it needs is a guard, not a producer (§3);
* and some are MIXED, and that is the only class that is actually hard (§4).

§5 is why the mixed class does not yield to a better reading of the same data.
The two `.value` frames differ by *where the current entry started*, and an
entry's key may be a whole bracketed collection, so the boundary sits at an
unbounded distance: no last-token reading and no bounded lookback separates
them.  What does separate them is an INDEX the machine already keeps —
`simpleKey.tokenIndex`, the slot the pending key reserved — because a machine
that resolves a decision retroactively ("this scalar becomes a key if a `:`
arrives") has to remember WHERE, not just what.  Sibling of Reflection 624: that
one reads a machine's flag as a witness to its history, this one reads a
machine's POINTER as a witness to a boundary.

§6 is the payoff: the split is what turns "the arm is blocked" into "one of four
index values is blocked, by a named datum" — and the two total classes land
meanwhile, purely additively.

L4YAML DOCS item 9n, 2026-08-09.  `FlowOpenStack.receiveColonSep` (tail `.sep`)
and `receiveColonQuestion` (tail `.question`) are both total and both landed;
the `.colon` class wants a last-real-token guard and the `.value` class wants
the scanner's pending simple key.
-/

namespace Tests.Reflections.TotalAndMixedIndexClasses

/-! ## §0  The frames, their index, and which of them take the step -/

inductive Tail where
  | sep | colon | question | value
  deriving DecidableEq, Repr, BEq

inductive Frame where
  | betweenEmpty | betweenHeld              -- `[`  /  `[a,`
  | midQuestion                             -- `[? `
  | midNode | midExplicitKey                -- `[a` / `[? a`
  | betweenEntries                          -- `[a: b`  ← the one that blocks
  | midColon | midEmptyColon
  | midExplicitColon | midQuestionEmptyColon
  deriving DecidableEq, Repr, BEq

def tailOf : Frame → Tail
  | .betweenEmpty | .betweenHeld => .sep
  | .midQuestion => .question
  | .midNode | .midExplicitKey | .betweenEntries => .value
  | .midColon | .midEmptyColon | .midExplicitColon | .midQuestionEmptyColon => .colon

/-- Does a `:` continue this frame?  `betweenEntries` is the interesting `false`:
    the entry it holds is already complete, so a second `:` has no derivation. -/
def takesColon : Frame → Bool
  | .betweenEmpty | .betweenHeld | .midQuestion | .midNode | .midExplicitKey => true
  | _ => false

def allFrames : List Frame :=
  [.betweenEmpty, .betweenHeld, .midQuestion, .midNode, .midExplicitKey,
   .betweenEntries, .midColon, .midEmptyColon, .midExplicitColon, .midQuestionEmptyColon]

def allTails : List Tail := [.sep, .colon, .question, .value]

def framesAt (t : Tail) : List Frame := allFrames.filter (fun f => tailOf f == t)

#guard allFrames.length == 10
#guard (allFrames.filter takesColon).length == 5

/-! ## §1  The classification

Three kinds, and only one of them is work. -/

inductive Kind where
  | totalReceptive | totalRefutable | mixed
  deriving DecidableEq, Repr, BEq

def kindAt (t : Tail) : Kind :=
  let g := framesAt t
  let r := g.filter takesColon
  if r.length == g.length then .totalReceptive
  else if r.length == 0 then .totalRefutable
  else .mixed

#guard kindAt Tail.sep == Kind.totalReceptive
#guard kindAt Tail.question == Kind.totalReceptive
#guard kindAt Tail.colon == Kind.totalRefutable
#guard kindAt Tail.value == Kind.mixed

#guard (allTails.filter (fun t => kindAt t == Kind.mixed)).length == 1

/-! ## §2  The total-receptive classes are free

Nothing to refute and nothing to discriminate: every frame the index admits has
a target, so the transition is a plain `cases` with one arm each. -/

#guard (framesAt Tail.sep).length == 2
#guard (framesAt Tail.sep).all takesColon
#guard (framesAt Tail.question).length == 1
#guard (framesAt Tail.question).all takesColon

/-! ## §3  The total-refutable class needs a guard, not a producer

Four frames, none receptive — so the whole class is dead input, and closing it
means proving it unreachable rather than building anything. -/

#guard (framesAt Tail.colon).length == 4
#guard (framesAt Tail.colon).all (fun f => !takesColon f)

/-! ## §4  …and exactly one class is mixed

Two of its three frames continue, one does not — so neither a producer nor a
refutation covers it, and the index as it stands cannot say which. -/

#guard (framesAt Tail.value).length == 3
#guard ((framesAt Tail.value).filter takesColon).length == 2
#guard ((framesAt Tail.value).filter (fun f => !takesColon f)).length == 1

/-! ## §5  Why a finer reading of the same data does not help

Model what each class's frames leave in the token history.  A `.colon` frame is
separated from everything else by its LAST token (a value indicator), so a
one-token reading decides it.  The two `.value` frames both end in whatever
ended their node — and a node may be a bracketed collection, so the token that
would tell them apart is at an unbounded distance.  The separating datum is the
entry's START, which the history keeps as an INDEX and not as a value. -/

inductive Datum where
  | lastToken        -- readable from the token history in O(1)
  | entryStartIndex  -- the machine's pending-key reservation slot
  deriving DecidableEq, Repr, BEq

/-- What is needed to decide the class — `none` when nothing is (it is total). -/
def discriminator : Tail → Option Datum
  | .sep | .question => none
  | .colon => some .lastToken
  | .value => some .entryStartIndex

#guard (allTails.filter (fun t => discriminator t == none)).length == 2
#guard (allTails.filter (fun t => discriminator t == some Datum.lastToken)).length == 1
#guard (allTails.filter (fun t => discriminator t == some Datum.entryStartIndex)).length == 1

-- The classes needing NO datum are exactly the ones that are total.
#guard allTails.all (fun t =>
  (discriminator t == none) == (kindAt t == Kind.totalReceptive))

-- …and the class needing the machine's index is exactly the mixed one.
#guard allTails.all (fun t =>
  (discriminator t == some Datum.entryStartIndex) == (kindAt t == Kind.mixed))

/-! ## §6  The payoff of splitting first

Five of the ten frames take the step, and the two total-receptive classes cover
three of those five — landed for the price of writing them.  What is left is not
"the transition" but two named obligations with two different prices. -/

def landed : List Frame :=
  (framesAt Tail.sep ++ framesAt Tail.question).filter takesColon

#guard landed.length == 3
#guard landed.all takesColon
#guard ((allFrames.filter takesColon).filter (fun f => !(landed.contains f))).length == 2

-- The residual, priced: one class per remaining datum, never more.
#guard (allTails.filter (fun t => discriminator t != none)).length == 2

end Tests.Reflections.TotalAndMixedIndexClasses

end Blanket
