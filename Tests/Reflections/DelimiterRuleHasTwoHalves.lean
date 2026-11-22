/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # A delimiter rule has two halves (Reflection 622)

A production of the shape

    pair ::= "?" sep entry

sitting as one alternative of a list gives the scanner **two** context
obligations, not one:

* **left** — where may a `pair` START?  Only where the list is about to read a
  fresh element.  That is a *lookback*, over the emitted TOKENS.
* **right** — what must immediately follow the `"?"`?  A `sep`, which is
  non-empty.  That is a *lookahead*, over the raw CHARACTERS.

The previous pass found the left half, shipped it, and declared the arm clean.
It was not: the right half was still missing, and `[?]`, `[?,a]`, `{?}` — none of
which has a derivation — still scanned clean in both pipelines.  Worse, the
pass's own guard suite *pinned* one of them (`[?, ? a]`) as an input that must be
ACCEPTED, so the regression net certified the gap.

The reason one search does not surface the other is in the two bullets above:
they read **disjoint parts of the state**, in opposite directions, and a
lookback sweep never touches the lookahead.  §3 makes that concrete — the two
guards are logically independent, all four cells of their 2×2 inhabited.

The rule this leaves: when a strictening comes from a production of the form
`X sep Y`, the production names two obligations.  Ship one and you have half a
rule.  **Read the production in both directions before calling the arm clean.**

L4YAML DOCS items 9g (left) and 9j (right), 2026-08-08.
-/

namespace Tests.Reflections.DelimiterRuleHasTwoHalves

/-! ## §0  The toy language

`Ch` is a five-character alphabet: an entry separator, a close, the pair
indicator, a separation character, and a plain item.  The production under test
is `pair ::= '?' ' '+ item?`, one alternative of a comma-separated list. -/

inductive Ch where
  | comma | close | q | sp | item
  deriving DecidableEq, Repr, BEq

/-- Does the string derive?  This is the SPEC: a whitespace-tolerant list of
    entries, closed.  Every call decrements `fuel`, so the recursion is
    structural on it; `2 * length + 2` covers the two non-consuming transitions.

    Note `.q :: .sp :: rest` in `entry` — the separation after the indicator is
    mandatory and non-empty, exactly as `[150] ns-flow-pair` demands, and it is
    the ONLY thing this spec says about `?` that a lookback could not. -/
def derives (cs : List Ch) : Bool := entries (2 * cs.length + 2) cs
where
  /-- at an element position -/
  entries : Nat → List Ch → Bool
    | 0, _ => false
    | f + 1, cs => match cs with
      | .sp :: rest => entries f rest
      | .close :: rest => rest.isEmpty
      | _ => entry f cs
  /-- one entry: a plain item, or `'?' sep` and an explicit one -/
  entry : Nat → List Ch → Bool
    | 0, _ => false
    | f + 1, cs => match cs with
      | .item :: rest => tail f rest
      | .q :: .sp :: rest => afterSep f rest
      | _ => false
  /-- after `? ` — more separation, then an OPTIONAL key (`e-node` is legal) -/
  afterSep : Nat → List Ch → Bool
    | 0, _ => false
    | f + 1, cs => match cs with
      | .sp :: rest => afterSep f rest
      | .item :: rest => tail f rest
      | _ => tail f cs
  /-- between entries -/
  tail : Nat → List Ch → Bool
    | 0, _ => false
    | f + 1, cs => match cs with
      | .sp :: rest => tail f rest
      | .comma :: rest => entries f rest
      | .close :: rest => rest.isEmpty
      | _ => false

/-! ## §1  The two guards

Both are read at the `'?'`.  `predOk` looks BACK at what the dispatcher last
emitted; `follOk` looks FORWARD at the next raw character.  They share no
input. -/

/-- The tokens a dispatcher emits — the lookback's data. -/
inductive Tok where
  | opened | sepd | keyed | valued
  deriving DecidableEq, Repr, BEq

/-- **Left half (item 9g).**  A `pair` is an ELEMENT, so it starts only where the
    list is about to read one: right after the open or a `,`. -/
def predOk : Option Tok → Bool
  | some .opened => true
  | some .sepd => true
  | _ => false

/-- **Right half (item 9j).**  `'?' sep` — the separation is mandatory, so the
    next character is a separator (or the input ends and a later check owns the
    error). -/
def follOk : Option Ch → Bool
  | some .sp => true
  | some _ => false
  | none => true

/-! ## §2  Two dispatchers: one half, and both

`scanWith` walks the string, taking the `'?'` arm only when its guards pass; a
`'?'` that fails falls through and is an error, exactly as in the real
dispatcher.  The leading `Tok.opened` stands for the `[` the caller already
consumed.

The `,` and `item` arms carry the two guards that were already in place before
either half of the `?` rule — no leading or consecutive `,`
(`scanFlowEntry`/`invalidFlowEntry`) and no two adjacent items
(`checkFlowAdjacency`).  They are here so that the ONLY difference between the
two dispatchers below is the half under study. -/

def scanWith (guardsOk : Option Tok → Option Ch → Bool) : Option Tok → List Ch → Bool
  | _, [] => false
  | _, .close :: rest => rest.isEmpty
  | last, .comma :: rest =>
      (last == some .valued || last == some .keyed) && scanWith guardsOk (some .sepd) rest
  | last, .sp :: rest => scanWith guardsOk last rest
  | last, .item :: rest =>
      last != some .valued && scanWith guardsOk (some .valued) rest
  | last, .q :: rest => guardsOk last rest.head? && scanWith guardsOk (some .keyed) rest

/-- The dispatcher the previous pass shipped: the LEFT half only. -/
def scanLeft (cs : List Ch) : Bool :=
  scanWith (fun t _ => predOk t) (some .opened) cs

/-- …and with the right half added. -/
def scanBoth (cs : List Ch) : Bool :=
  scanWith (fun t n => predOk t && follOk n) (some .opened) cs

/-! ## §3  The two halves are independent

All four cells of the 2×2 are inhabited, which is why finding one says nothing
about the other. -/

-- `? a]` — both guards pass, and it derives.
#guard predOk (some .opened) && follOk (some .sp)

-- `?]` — the LEFT guard passes and the RIGHT one fails.  This is the whole gap:
-- the shipped dispatcher accepted it.
#guard predOk (some .opened) && !follOk (some .close)

-- `a ? b` — the RIGHT guard passes and the LEFT one fails (item 9g's case).
#guard !predOk (some .valued) && follOk (some .sp)

-- …and both can fail at once.
#guard !predOk (some .valued) && !follOk (some .close)

/-! ## §4  The sweep

Enumerate every string over the alphabet up to length 4 and compare each
dispatcher against the spec.  The left-half-only dispatcher over-accepts; both
halves together are exact — in both directions. -/

def alphabet : List Ch := [.comma, .close, .q, .sp, .item]

def wordsOfLen : Nat → List (List Ch)
  | 0 => [[]]
  | n + 1 => (wordsOfLen n).flatMap (fun cs => alphabet.map (fun c => c :: cs))

def corpus : List (List Ch) := (List.range 5).flatMap wordsOfLen

/-- Strings a dispatcher accepts that have NO derivation. -/
def overAccepts (scanner : List Ch → Bool) : List (List Ch) :=
  corpus.filter (fun cs => scanner cs && !derives cs)

/-- Strings a dispatcher rejects that DO have a derivation. -/
def overRejects (scanner : List Ch → Bool) : List (List Ch) :=
  corpus.filter (fun cs => !scanner cs && derives cs)

-- The corpus is big enough to be evidence, and the spec is not vacuous.
#guard corpus.length == 781
#guard (corpus.filter derives).length == 20

-- **The left half alone over-accepts** — 13 of the 781, and every witness
-- contains a `?` whose mandatory separation is missing.
#guard (overAccepts scanLeft).length == 13
#guard (overAccepts scanLeft).all (fun cs => cs.contains .q)

-- **Both halves together are exact on the corpus**, in both directions.
#guard overAccepts scanBoth == []
#guard overRejects scanBoth == []

-- …and the left half was never wrong in the OTHER direction, which is exactly
-- why a rejection-only regression suite could not see the gap: nothing it
-- accepted got rejected, so nothing it pinned ever went red.
#guard overRejects scanLeft == []

/-! ## §5  The suite that pinned the bug

The previous pass's guard file asserted `[?, ? a]` — a `?` with no separation —
as an input that must be ACCEPTED.  A suite is only as good as the spec it was
written against: this one is satisfied by the incomplete dispatcher and refuted
by the correct one. -/

/-- `?,? a]` — the shape the old suite pinned as accepted. -/
def oldSuiteCase : List Ch := [.q, .comma, .q, .sp, .item, .close]

#guard scanLeft oldSuiteCase          -- the old suite passed…
#guard !derives oldSuiteCase          -- …on a string with no derivation…
#guard !scanBoth oldSuiteCase         -- …so the corrected rule retracts it.

/-- Its one-character repair — the separation restored — derives, and both
    dispatchers accept it. -/
def repairedCase : List Ch := [.q, .sp, .comma, .q, .sp, .item, .close]

#guard derives repairedCase
#guard scanLeft repairedCase && scanBoth repairedCase

end Tests.Reflections.DelimiterRuleHasTwoHalves

end Blanket
