/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # A soundness gate names ONE sufficient context (Reflection 623)

A guard reads a lookback and concludes something about structure.  It is sound
only where the lookback means what the guard thinks it means — so it gets a
**gate**, and the gate is written down with the counterexamples that forced it.

The trap is then reading the gate as *the premise*.  It is not: it is one
**sufficient context** for the premise, and there can be others, logically
independent of it.  Ungating is unsound and stays unsound — but *disjoining* a
second sufficient context is free, because the old disjunct is untouched, so
every proof that consumed the gated guard still consumes it unchanged.

And the second disjunct is not hard to find, because **it is hiding in the
counterexamples that justified the gate**.  Those inputs are the boundary of the
premise.  Whatever separates them from the shapes the guard should reject is,
by construction, another condition under which the premise holds.

Here: a guard rejects two adjacent property tokens as "one node with two
anchors".  It is unsound in block context because a block collection opens
**without emitting a token**.  The gate was `inFlow`.  But the two
counterexamples that forced it both put their tokens on *different lines* — and
that is not luck: a block collection's properties are followed by `s-l-comments`,
which requires a break.  So `sameLine` is a second sufficient context, and §3
shows the two are incomparable: each catches inputs the other cannot see.

L4YAML DOCS items 9e (the gate) and 9k (the second disjunct), 2026-08-08.
-/

namespace Tests.Reflections.GateIsOneSufficientContext

/-! ## §0  The toy language

A source is a list of "atoms".  `prop` and `item` emit a token; `vopen` opens a
collection and emits NOTHING — it is the whole reason a lookback can be wrong.
`br` is a line break, which emits nothing either but is visible in the
positions. -/

inductive Atom where
  | prop | item | vopen | br
  deriving DecidableEq, Repr, BEq

/-- The two contexts a `vopen` may legally appear in.  In `flow` it may not
    appear at all; in `block` it may, but only directly after a break — that is
    the toy's stand-in for `[200]`'s mandatory `s-l-comments`. -/
inductive Ctx where
  | flow | block
  deriving DecidableEq, Repr, BEq

/-- Well-formedness of a source in a context: `flow` admits no `vopen`, `block`
    admits one only right after a `br`. -/
def wellFormed : Ctx → Option Atom → List Atom → Bool
  | _, _, [] => true
  | .flow, _, .vopen :: _ => false
  | c, prev, a :: rest => (a != .vopen || prev == some .br) && wellFormed c (some a) rest

/-- **The spec.**  Two `prop`s belong to one node unless a `vopen` separates
    them; a node may carry at most one, so a source derives iff no two `prop`s
    are separated by no `vopen`.  Walk left to right carrying "a `prop` is
    outstanding". -/
def derives (as : List Atom) : Bool := go false as
where
  go : Bool → List Atom → Bool
    | _, [] => true
    | held, .prop :: rest => !held && go true rest
    | _, .vopen :: rest => go false rest      -- a new node starts
    | _, .item :: rest => go false rest       -- an item ends the node
    | held, .br :: rest => go held rest       -- a break alone changes nothing

/-! ## §1  The lookback, and the two contexts in which it is sound

The guard has no access to `vopen` — that is the point; it sees only the emitted
tokens and their line numbers.  `lastProp?` is what it can read: whether the
previous token was a `prop`, and which line it was on. -/

/-- Line numbers of the atoms, counting `br`. -/
def lines (as : List Atom) : List Nat := go 0 as
where
  go : Nat → List Atom → List Nat
    | _, [] => []
    | n, .br :: rest => n :: go (n + 1) rest
    | n, _ :: rest => n :: go n rest

/-- Was the atom before position `i` a `prop`, and on what line?  `vopen` and
    `br` are invisible to the token stream, so they are skipped — exactly the
    blindness that makes the guard need a gate. -/
def lastPropLine? (as : List Atom) (i : Nat) : Option Nat :=
  let ls := lines as
  let before := (List.range i).reverse.filter (fun j =>
    match as[j]? with | some .prop => true | some .item => true | _ => false)
  match before with
  | j :: _ => match as[j]? with
              | some .prop => ls[j]?
              | _ => none
  | [] => none

/-- **Disjunct A (the gate, item 9e).**  In flow context no `vopen` exists, so
    adjacency means one node at any distance. -/
def gateFlow (c : Ctx) : Bool := c == .flow

/-- **Disjunct B (item 9k).**  On one line no `vopen` can have intervened,
    because a `vopen` is legal only after a break. -/
def gateSameLine (as : List Atom) (i : Nat) : Bool :=
  match lastPropLine? as i, (lines as)[i]? with
  | some pl, some here => pl == here
  | _, _ => false

/-! ## §2  Three guards

`fires` says the guard rejects at position `i`: a `prop` whose lookback already
shows a `prop`, in a context the guard trusts. -/

def rejectsAt (trust : List Atom → Nat → Bool) (as : List Atom) (i : Nat) : Bool :=
  match as[i]? with
  | some .prop => (lastPropLine? as i).isSome && trust as i
  | _ => false

def rejects (trust : List Atom → Nat → Bool) (as : List Atom) : Bool :=
  (List.range as.length).any (rejectsAt trust as)

/-- The shipped guard: trust the flow context only.  (`c` is threaded in by the
    caller below, which is why `trust` takes the source and index alone.) -/
def trustFlow (c : Ctx) : List Atom → Nat → Bool := fun _ _ => gateFlow c

/-- The second disjunct alone. -/
def trustLine : List Atom → Nat → Bool := gateSameLine

/-- Both, disjoined — the shape item 9k shipped. -/
def trustBoth (c : Ctx) : List Atom → Nat → Bool :=
  fun as i => gateFlow c || gateSameLine as i

/-! ## §3  The two disjuncts are incomparable

All four cells of the 2×2 are inhabited, so neither search finds the other.  The
witnesses are the shapes the real items argue about. -/

-- `[&a &b …]` — in flow AND on one line: both trust it.
#guard gateFlow .flow && gateSameLine [.prop, .prop] 1

-- `[&a⏎&b …]` — in flow, across a break: the GATE trusts it, the line test
-- cannot see it.  This is the run item 9k gives up.
#guard gateFlow .flow && !gateSameLine [.prop, .br, .prop] 2

-- `&a &b …` in block — the LINE test trusts it, the gate does not.  This is
-- item 9k's whole yield.
#guard !gateFlow .block && gateSameLine [.prop, .prop] 1

-- `&a⏎&b …` in block — neither, and rightly: a `vopen` may sit in the gap.
#guard !gateFlow .block && !gateSameLine [.prop, .br, .prop] 2

/-! ## §4  The sweep

Every source up to length 5, in both contexts.  Only well-formed ones count —
an ill-formed source is not the guard's problem. -/

def alphabet : List Atom := [.prop, .item, .vopen, .br]

def wordsOfLen : Nat → List (List Atom)
  | 0 => [[]]
  | n + 1 => (wordsOfLen n).flatMap (fun as => alphabet.map (fun a => a :: as))

def corpus (c : Ctx) : List (List Atom) :=
  ((List.range 6).flatMap wordsOfLen).filter (wellFormed c none)

/-- Sources a guard rejects that DO derive — unsoundness, the thing a gate
    exists to prevent. -/
def overRejects (c : Ctx) (trust : List Atom → Nat → Bool) : List (List Atom) :=
  (corpus c).filter (fun as => rejects trust as && derives as)

/-- Sources a guard accepts that do NOT derive — the coverage it is missing. -/
def overAccepts (c : Ctx) (trust : List Atom → Nat → Bool) : List (List Atom) :=
  (corpus c).filter (fun as => !rejects trust as && !derives as)

-- The corpus is not vacuous, and `block` is the bigger one because `vopen` is
-- only legal there.
#guard (corpus .flow).length == 364
#guard (corpus .block).length == 516

-- **Both disjuncts are sound, separately and together** — nothing that derives
-- is ever rejected.  This is what "the gate is a SUFFICIENT context" means: it
-- is not the only way to be sure.
#guard overRejects .flow (trustFlow .flow) == []
#guard overRejects .block trustLine == []
#guard overRejects .flow (trustBoth .flow) == []
#guard overRejects .block (trustBoth .block) == []

-- **…and ungating is not.**  Trusting the lookback unconditionally in block
-- context rejects sources that derive — the 26DV shape, in miniature.
#guard (overRejects .block (fun _ _ => true)).length == 7

-- **Why nobody looked further.**  Where the gate DOES apply it is not merely
-- sound, it is exact — zero over-acceptances in flow.  A guard that is perfect
-- inside its gate reads as finished.
#guard overAccepts .flow (trustFlow .flow) == []

-- **The second disjunct is pure yield.**  In block context the gate alone
-- rejects nothing at all; adding the line test closes 124 of the 152 gaps
-- without opening one.
#guard (corpus .block).filter (rejects (trustFlow .block)) == []
#guard (overAccepts .block (trustFlow .block)).length == 152
#guard (overAccepts .block (trustBoth .block)).length == 28

-- **And it costs the gated context nothing**, because the old disjunct is
-- untouched: in flow the two guards are the same function.
#guard (corpus .flow).all (fun as => rejects (trustFlow .flow) as == rejects (trustBoth .flow) as)

/-! ## §5  The counterexamples were the map

The inputs that forced the gate are exactly the ones the second disjunct also
refuses to trust.  So the residual — what is still missed after both disjuncts —
is *contained in* the counterexample set, and reading that set is how the second
disjunct was found in the first place. -/

/-- The gate's counterexample: two props with a `vopen` between them, which the
    lookback cannot see.  Legal, and neither disjunct trusts it. -/
def counterexample : List Atom := [.prop, .br, .vopen, .prop, .item]

#guard wellFormed .block none counterexample
#guard derives counterexample
#guard !gateFlow .block && !gateSameLine counterexample 3

/-- Its one-break-shorter twin: the SAME token stream, one line.  No `vopen` can
    be there, so it does not derive — and the second disjunct catches it. -/
def sameLineTwin : List Atom := [.prop, .prop, .item]

#guard wellFormed .block none sameLineTwin
#guard !derives sameLineTwin
#guard gateSameLine sameLineTwin 1
#guard rejects (trustBoth .block) sameLineTwin

-- Every source the widened guard still misses in block context contains a
-- `br` between the two properties — the residual is exactly the shape the
-- counterexample has, and telling it from the counterexample needs the
-- machinery the gate was avoiding, not another lookback.
#guard (overAccepts .block (trustBoth .block)).all (fun as => as.contains .br)

end Tests.Reflections.GateIsOneSufficientContext

end Blanket
