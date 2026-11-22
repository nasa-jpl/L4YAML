/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # A guard you wrote to REFUTE also PRODUCES (Reflection 627)

A strictening lands, and its first consumer is always a refutation: some arm has
to die, so the lemma that gets written concludes `tl ≠ X`.  Do that a few times
and the file's whole vocabulary of couplings is `≠`-shaped — which is fine until
an arm has to CONSTRUCT rather than eliminate, and then the fact it needs is the
same table read forward, three lines away, and nobody wrote it.

Two things make this worth naming rather than noticing.

1. **The two readings are not equally strong.**  §2: "the last token is not one
   of the three" leaves the frame tail in a set of THREE; "the last token IS one
   of them" pins it to ONE.  §3 is why that matters: a constructor is a function
   of the tail, so it needs the singleton.  Refuting knowledge cannot call it —
   not because it is wrong, but because it is not a value.
2. **Only a guard whose condition is POSITIVE has the strong reading at all.**
   Most scanner guards say "the previous token does not complete a value" and
   invert to a denial.  This one says "the previous token opens an entry", and
   inverting it hands back a token.  When an arm will not build, the question to
   ask of every guard already protecting it is which shape its condition has.

§4 is why the imbalance is structural rather than an oversight: of the five
flow-interior arms, four need a refutation and one needs a production, so a file
grown one arm at a time writes four `≠` lemmas before the first `=` is asked for.

§5 is the second payment, and the sharper one.  A held property run is a state
every sibling arm RESOLVES — flushed as an empty-node's properties, or wrapped
into the node that follows.  The producing arm neither flushes nor wraps: the
same guard refutes it, because a property opens no entry.  And the `≠` readings
are blind to that — a property passes BOTH of them — so nothing in the
refutation-shaped world could have told you the case was impossible.

L4YAML DOCS item 10, 2026-08-08.  Item 9g added `flowKeyPredecessorOk` to reject
`[? ? a]`, `[: ?]` and `[&a ? b]`; nine items later the `?` arm of
`accum_step_block` was built from it, via a new `tailOf_eq_sep` sitting beside
the file's two pre-existing `tailOf_ne_value` / `tailOf_ne_sep`.  The held-run
case is closed by `opensFlowEntry_false_of_isNodeProperty`, one `cases` over the
token type.
-/

namespace Tests.Reflections.GuardWrittenToRefuteAlsoProduces

/-! ## §0  The token table both readings come from

One classifier, `tailOf`, mapping the last real token to the frame class it puts
the accumulator in.  Everything below is a reading of this one function. -/

inductive Tok where
  | oseq | omap | comma        -- `[`, `{`, `,` — these OPEN an entry
  | key                        -- `?`
  | colon                      -- `:`
  | scalar | cseq | cmap       -- these COMPLETE a value
  | anchor | tag               -- `[96] c-ns-properties`
  deriving DecidableEq, Repr, BEq

inductive Tail where
  | sep | colon | question | value
  deriving DecidableEq, Repr, BEq

/-- The guard's condition.  Note its shape: a POSITIVE statement about the last
    token, which is the whole reason the strong reading exists. -/
def opensEntry : Tok → Bool
  | .oseq | .omap | .comma => true
  | _ => false

def completesValue : Tok → Bool
  | .scalar | .cseq | .cmap => true
  | _ => false

def isProperty : Tok → Bool
  | .anchor | .tag => true
  | _ => false

def tailOf : Tok → Tail
  | .oseq | .omap | .comma => .sep
  | .key => .question
  | t => if completesValue t then .value else .colon

def allToks : List Tok :=
  [.oseq, .omap, .comma, .key, .colon, .scalar, .cseq, .cmap, .anchor, .tag]

def allTails : List Tail := [.sep, .colon, .question, .value]

def imp (a b : Bool) : Bool := !a || b

def dedup {α : Type} [BEq α] : List α → List α
  | [] => []
  | a :: as => let r := dedup as; if r.contains a then r else a :: r

#guard allToks.length == 10

/-! ## §1  One table, two readings, both true

The refuting reading is what a strictening's first consumer needs, so it is the
one that gets written.  The producing reading is the same table and costs
nothing — it just has to be asked for. -/

#guard allToks.all (fun t => imp (!opensEntry t) (tailOf t != Tail.sep))
#guard allToks.all (fun t => imp (opensEntry t) (tailOf t == Tail.sep))

/-! ## §2  …and they are not equally strong

Refuting narrows the tail to a SET.  Producing pins it to a POINT. -/

def tailsWhen (p : Tok → Bool) : List Tail := dedup ((allToks.filter p).map tailOf)

#guard (tailsWhen (fun t => !opensEntry t)).length == 3
#guard (tailsWhen opensEntry).length == 1
#guard tailsWhen opensEntry == [Tail.sep]

/-! ## §3  Why the difference is the whole obstruction

A frame constructor is a FUNCTION of the tail.  Knowing what the tail is not
does not supply an argument to it — the four-way `cases` a refutation prunes
still has more than one arm left, and only one of them builds. -/

inductive Frame where
  | midQuestion
  deriving Repr, BEq

def receiveQuestion? : Tail → Option Frame
  | .sep => some .midQuestion
  | _ => none

-- `tl ≠ .value` is what the NODE-receiving arm is given; it admits three tails
-- and two of them have no frame at all.
#guard (allTails.filter (fun tl => tl != Tail.value)).length == 3
#guard ((allTails.filter (fun tl => tl != Tail.value)).filter
          (fun tl => (receiveQuestion? tl).isNone)).length == 2

-- `tl ≠ .sep` — the OTHER refuting lemma the file already had — is worse than
-- useless here: it admits exactly the tails that cannot build.
#guard (allTails.filter (fun tl => tl != Tail.sep)).all
         (fun tl => (receiveQuestion? tl).isNone)

-- The producing reading admits one tail, and it builds.
#guard (allTails.filter (fun tl => tl == Tail.sep)).all
         (fun tl => (receiveQuestion? tl).isSome)

/-! ## §4  Why the imbalance is structural, not an oversight

Four of the five flow-interior arms need to eliminate a frame shape; one needs to
construct one.  A file grown one arm at a time therefore writes four `≠` lemmas
before anything asks for an `=`, and by then the `≠` shape reads as "how
couplings are stated here". -/

inductive Arm where
  | push | close | comma | content | question
  deriving Repr, BEq

inductive Need where
  | refute | produce
  deriving Repr, BEq

def needs : Arm → Need
  | .push | .close | .comma | .content => .refute
  | .question => .produce

def allArms : List Arm := [.push, .close, .comma, .content, .question]

#guard (allArms.filter (fun a => needs a == Need.refute)).length == 4
#guard (allArms.filter (fun a => needs a == Need.produce)).length == 1

/-! ## §5  The second payment: a state the siblings resolve and this arm refutes

Every sibling arm HANDLES a held property run — flushes it as an empty node's
properties, or wraps it into the node that follows.  The producing arm does
neither, and does not have to: the guard's own table says a property opens no
entry.

The last four guards are the sharp part.  A property passes BOTH refuting
readings, so `≠`-shaped knowledge leaves the held run perfectly consistent — two
of the seven tokens it admits are properties.  The positive reading excludes it
outright: none of the three.  Nothing in the refutation-shaped world could have
told you this case was impossible. -/

#guard (allToks.filter isProperty).length == 2
#guard (allToks.filter isProperty).all (fun t => !opensEntry t)
#guard (allToks.filter (fun t => opensEntry t && isProperty t)).length == 0

#guard (allToks.filter isProperty).all
         (fun t => tailOf t != Tail.sep && tailOf t != Tail.value)

#guard (allToks.filter (fun t => tailOf t != Tail.sep)).length == 7
#guard ((allToks.filter (fun t => tailOf t != Tail.sep)).filter isProperty).length == 2
#guard (allToks.filter (fun t => tailOf t == Tail.sep)).length == 3
#guard ((allToks.filter (fun t => tailOf t == Tail.sep)).filter isProperty).length == 0

end Tests.Reflections.GuardWrittenToRefuteAlsoProduces

end Blanket
