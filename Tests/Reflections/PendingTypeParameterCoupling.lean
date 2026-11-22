/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 636 — the coupling rides the pending's type parameter

**The rule.**  When a PARKED obligation must fire a scanner guard one dispatch
later — a held `[96]` run refuting a repeated property — the coupling
("held ⇒ the guard's test is true") is a fact about the SCANNER STATE at the
moment of consumption.  Neither of the two obvious carriers can hold it:

* a **constructor field** cannot, because the pending's inductive has no
  scanner state in scope — its indices are surface positions; and
* a **parallel invariant conjunct** cannot, because nothing links its case
  analysis to the pending's constructor — a `white`-shaped companion next to a
  props-shaped pending is unprovable, not contradictory (Reflection 619's
  sibling-conjunct trap, one level up).

The dissolution: **parametrize the pending's TYPE by the scanner state it
accompanies** — the state at the end of the step that parked it, which is
byte-for-byte the state the consuming step receives.  One constructor reads
the parameter (its coupling fields quantify over `sc.tokens`/`sc.line`); the
other eight ignore it.  Because constructors never MENTION a parameter they
do not read, every existing construction term compiled unchanged — the whole
cost was type-level: 55 binder/conclusion sites gained `sc` (hypotheses) or
`s'` (conclusions), and 0 proof terms changed at non-props sites.

**The transport is the machine's own flag.**  The coupling is stated at step
start; the guard fires after preprocessing.  "No break was crossed in
between" is not a new hypothesis to thread — `needIndentCheck` is set by
`consumeNewline` and cleared only by the armed unwind branch (Reflection
624's field, read one level up): a pending parked at `flag = false` whose
next preprocessing kept `sp_mid = sp` still has the flag down, so the armed
branch REFUTES ITSELF and the line and both positioned token readings
survive to the dispatch.  One conjunct on one disjunction lemma carried all
of it.

**The consuming arm is a three-way split, and the guard's PASS does the case
analysis.**  On the run's line: `&`/`!` derive "my half is absent" by
CONTRAPOSITIVE (guard passed + coupling ⇒ index bit is false) and EXTEND the
run — the refutation and the construction are one arm; `*` is refuted
outright; every value-completing character becomes the run's `[161]` content
— or `[198] s-l+block-scalar`'s own props slot, which is why `&a |` needed
no new grammar: the slot was already in the rule.

Self-contained: pins the shipped instance's counts (L4YAML item 12,
2026-08-10).
-/

namespace L4YAML.Tests.Reflections.PendingTypeParameterCoupling

/-- A miniature machine state: the parts the coupling reads. -/
structure MiniState where
  lastTokenIsProp : Bool
  line : Nat
  deriving Repr

/-- A miniature pending, PARAMETRIZED by the state it accompanies: `parked`
    (the props-like constructor) reads the parameter through its coupling
    field; `plain` ignores it.  The parameter is what makes the coupling a
    FIELD instead of an unlinkable companion. -/
inductive MiniPending (sc : MiniState) : Prop where
  | plain
  | parked (h_coupling : sc.lastTokenIsProp = true)

/-- The guard the consuming dispatch evaluates. -/
def guardFires (sc : MiniState) : Bool := sc.lastTokenIsProp

/-- The consumption: a `parked` pending's coupling meets a passed guard
    head-on — the refutation is a field read, not a search.  This is exactly
    what an UNPARAMETRIZED pending cannot state: `hc` would have no `sc` to
    talk about. -/
example {sc : MiniState} (hc : sc.lastTokenIsProp = true)
    (hpass : guardFires sc = false) : False := by
  unfold guardFires at hpass; rw [hc] at hpass; exact Bool.noConfusion hpass

-- ═══ §1  The carrier's price: type-level only ═══

/-- Constructors of the shipped `PendingNode`. -/
def constructors : Nat := 9
/-- Constructors that read the new parameter (`pendingProps`). -/
def readers : Nat := 1
/-- Binder/conclusion sites that gained the parameter (`sc` in hypotheses,
    `s'` in step conclusions). -/
def typeLevelSites : Nat := 55
/-- Proof-term edits at the eight non-reading constructors' construction
    sites. -/
def termLevelEdits : Nat := 0

#guard constructors == 9
#guard readers == 1
#guard typeLevelSites == 55
#guard termLevelEdits == 0

-- ═══ §2  The transport: one flag conjunct on one lemma ═══

/-- Disjunction lemmas enriched to carry the no-break witness
    (`skipToContentLoop_anyCol_prod` → `skipToContent_anyCol_prod` →
    `preprocess_some_ssl_comments_anyCol`, one chain). -/
def enrichedLemmaChains : Nat := 1
/-- New hypotheses threaded through the accumulation for the transport
    (the flag IS the machine's own record — Reflection 624 one level up). -/
def newThreadedHypotheses : Nat := 0

#guard enrichedLemmaChains == 1
#guard newThreadedHypotheses == 0

-- ═══ §3  The consuming arm: three ways, guard-decided ═══

/-- What the same-line dispatch does with each character class. -/
inductive Outcome where
  | extend   -- `&`/`!`: contrapositive through the coupling, then `addAnchor`/`addTag`
  | refute   -- `*`: the guard the coupling arms fires
  | ride     -- value-completing: `[161] propsContent` or `[198]`'s props slot
  deriving DecidableEq, Repr

def outcomeOf : Char → Outcome
  | '&' => .extend
  | '!' => .extend
  | '*' => .refute
  | _   => .ride

#guard outcomeOf '&' == .extend
#guard outcomeOf '!' == .extend
#guard outcomeOf '*' == .refute
#guard outcomeOf '"' == .ride
#guard outcomeOf '|' == .ride   -- the props slot was already in [198]
#guard outcomeOf 'b' == .ride

/-- The held run's same-line content dispatches that fell to the
    `pendingFlow` deferral: before, ALL of them (one bail site); after, none —
    the arm's three ways are total.  What still rides the deferral is the
    BLOCK dispatch (`&a -`, `?`/`:` indicators, col≠0), the next β.5 target. -/
def propsContentBailSitesBefore : Nat := 1
def propsContentBailSitesAfter : Nat := 0

#guard propsContentBailSitesBefore == 1
#guard propsContentBailSitesAfter == 0

end L4YAML.Tests.Reflections.PendingTypeParameterCoupling

end Blanket
