/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 645 — an escape hatch's CALL-SITE count is not its coverage; report which inputs it still owns, and widen a gate rather than copy an arm

**The rule.**  Progress against a deferral, a `sorry`, or any other escape
hatch is a claim about its DOMAIN — which inputs still take it.  What is easy
to count is its SITES — how many times it is written in the source.  These move
together often enough to feel like the same number, and they are independent in
both directions: a copied arm composes strictly more input while the site count
rises, and an extracted helper drops the site count with nothing composed at
all.  Report the domain; use the site count only as a tripwire that asks *which
kind of edit did I just make?*

**And the answer to that tripwire is usually actionable.**  When a new case
wants an arm whose body it would share verbatim, widen that arm's GATE to a
disjunction instead of writing a second copy.  The same inputs leave, the body
stays single-sourced, and the two measures agree again.

Concretely (L4YAML): item 19 MERGED two producers of one package behind a
single gate, and `block_dispatch_deferred` fell from 22 call sites to 18 — the
number moved the way the progress did, which is exactly what makes it feel
trustworthy.  Item 20 then wanted the `?` indicator on an arm whose body the
`:` already had.  Copying that branch into all four block-dispatch lemmas
compiled first try and composed a whole new family of input — and pushed the
count back to **22**.  Widening the branch's condition from `c = ':'` to
`c = ':' ∨ c = '?'` instead (dispatching on the disjunct inside one join
lemma) composed the identical inputs at **18**.

§1 is the model and the two independence witnesses.  §2 is the honest measure.
§3 is the craft move — widen dominates copy, strictly.  §4 the shipped numbers,
including the one worth keeping: across items 19 and 20 the count went
22 → 18 → 18 while two whole input families left the deferral, so it moved once
in three edits.

Self-contained: the two measures, both independence witnesses, the dominance of
gate-widening over arm-copying, and the counts.
-/

namespace L4YAML.Tests.Reflections.CoverageNotCallSites

/-! ## §1  Two measures of one escape hatch -/

/-- A family of inputs the dispatch may receive. -/
abbrev Input := Nat

/-- The escape hatch, measured both ways at once. -/
structure Escape where
  /-- **Semantic**: the input families it still owns.  This is the claim. -/
  domain : List Input
  /-- **Syntactic**: how many times it is written in the source.  This is what
      is easy to count. -/
  sites : Nat
  deriving DecidableEq

/-- Block dispatch reached across a line break (`- a⏎- b` and its family). -/
def breakCrossed : Input := 1
/-- The explicit `?` key. -/
def question : Input := 2
/-- The indent machinery: whites before the indicator, `n ≠ 0`, col ≠ 0. -/
def indented : Input := 3

/-- Where item 19 opened: three families deferred, 22 call sites. -/
def start : Escape := ⟨[breakCrossed, question, indented], 22⟩

/-- **Merge** — join two producers of one package behind a single gate.  A
    family leaves AND the duplicated sites collapse: both measures fall. -/
def merge (e : Escape) : Escape :=
  ⟨e.domain.filter (· != breakCrossed), e.sites - 4⟩

/-- **Copy an arm** — give the new case its own branch beside the old one.  A
    family leaves; each copy brings its own else-branch, so the sites RISE. -/
def copyArm (e : Escape) : Escape :=
  ⟨e.domain.filter (· != question), e.sites + 4⟩

/-- **Widen the gate** — let the existing branch's condition admit the new case
    too.  The same family leaves, and no branch is written twice. -/
def widenGate (e : Escape) : Escape :=
  ⟨e.domain.filter (· != question), e.sites⟩

/-- **Extract a helper** — pure refactoring.  Sites fall, nothing composes. -/
def extract (e : Escape) : Escape := ⟨e.domain, e.sites - 3⟩

/-- Item 19 as shipped. -/
def afterItem19 : Escape := merge start
/-- Item 20's first attempt (built, measured, discarded). -/
def afterCopy : Escape := copyArm afterItem19
/-- Item 20 as shipped. -/
def afterWiden : Escape := widenGate afterItem19

#guard start.sites == 22
#guard afterItem19.sites == 18
#guard afterCopy.sites == 22
#guard afterWiden.sites == 18
-- The two item-20 routes compose exactly the same inputs.
#guard afterCopy.domain == afterWiden.domain

/-- **The number moves the right way on a merge** — which is precisely why it
    looks like a measure of progress. -/
theorem count_agrees_on_a_merge :
    afterItem19.domain.length < start.domain.length ∧
    afterItem19.sites < start.sites := by decide

/-- **First independence witness: the count inverts on a split.**  The copied
    arm composes strictly more input and reports a strictly worse number. -/
theorem count_inverts_on_a_split :
    afterCopy.domain.length < afterItem19.domain.length ∧
    afterItem19.sites < afterCopy.sites := by decide

/-- **Second witness, the other direction: the count falls with no progress.**
    Extracting a helper is invisible to the domain. -/
theorem count_falls_without_progress :
    (extract afterItem19).domain = afterItem19.domain ∧
    (extract afterItem19).sites < afterItem19.sites := by decide

/-- Together: neither implication holds, so the site count is not a proxy for
    coverage in either direction — only a tripwire. -/
theorem neither_implication_holds :
    ((extract afterItem19).sites < afterItem19.sites ∧
      ¬ ((extract afterItem19).domain.length < afterItem19.domain.length)) ∧
    (afterCopy.domain.length < afterItem19.domain.length ∧
      ¬ (afterCopy.sites < afterItem19.sites)) := by decide

/-! ## §2  The honest measure

  Which inputs the escape still owns — nothing about how its callers are
  spelled. -/

/-- Progress: strictly fewer input families deferred. -/
def coverageProgress (before after : Escape) : Bool :=
  after.domain.length < before.domain.length

#guard coverageProgress start afterItem19
#guard coverageProgress afterItem19 afterCopy
#guard coverageProgress afterItem19 afterWiden
#guard !coverageProgress afterItem19 (extract afterItem19)

/-- The measure is invariant under how the arms are spelled: two edits that
    compose the same families are equal progress, whatever they do to the
    source. -/
theorem progress_ignores_spelling :
    coverageProgress afterItem19 afterCopy = coverageProgress afterItem19 afterWiden := by
  decide

/-! ## §3  Widen the gate, do not copy the arm

  When the new case would share the old arm's body verbatim, the disjunction
  is strictly better: identical coverage, fewer sites, one body. -/

theorem widen_dominates_copy :
    afterWiden.domain = afterCopy.domain ∧ afterWiden.sites < afterCopy.sites := by
  decide

/-- Bodies written for the two indicators, when the branch is copied… -/
def bodiesIfCopied : Nat := 2
/-- …and when its gate is widened: the join dispatches on the disjunct, so the
    arm's body is authored once. -/
def bodiesIfWidened : Nat := 1

#guard bodiesIfWidened < bodiesIfCopied

/-! ## §4  The shipped numbers (items 19–20, 2026-08-11) -/

/-- `block_dispatch_deferred` call sites when item 19 opened. -/
def sitesAtItem19Start : Nat := 22
/-- After item 19's merge. -/
def sitesAfterMerge : Nat := 18
/-- What item 20 would have reported had the branch been copied (built and
    measured, then discarded). -/
def sitesIfCopied : Nat := 22
/-- What item 20 shipped, composing the identical inputs. -/
def sitesAsShipped : Nat := 18
/-- Input families that left the deferral across items 19 and 20. -/
def familiesComposed : Nat := 2

#guard sitesAtItem19Start == 22
#guard sitesAfterMerge == 18
#guard sitesIfCopied == sitesAtItem19Start
#guard sitesAsShipped == 18
#guard familiesComposed == 2
-- The keeper: two whole families left the deferral and the count moved ONCE in
-- three edits — 22 → 18 → 18.  Reporting it alone would have said nothing
-- about item 20 at all.
#guard sitesAfterMerge == sitesAsShipped

end L4YAML.Tests.Reflections.CoverageNotCallSites

end Blanket
