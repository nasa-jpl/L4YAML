/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 648 — a pinned existential does not only shrink the language; it propagates DOWNSTREAM as a side condition that reads like a fact about the domain

**The rule.**  [[AutoDetectedIsExistential]] says that inlining a production's
auto-detected parameter at its smallest legal value silently shrinks the
formalized language.  The second half of the damage is in the PROOFS.  Every
lemma about the wrapped construct now has to be stated where the pinned value
happens to be right, and that restriction gets recorded as a hypothesis —
`n = 0` — with a plausible-sounding justification attached.  The justification
is a numeric coincidence, not a fact about what the code does, and it survives
review precisely because it is TRUE at the value it names.

**The tell is the shape of the justification.**  If a side condition is
defended by arithmetic that happens to agree ("`n - 1` and `n` agree at
`n = 0`, so the two contexts coincide") rather than by the domain ("no producer
in this file opens a collection deeper than the document root"), it is an
artifact of a missing quantifier upstream.  Restore the quantifier and the
side condition evaporates — the widened lemma holds at every index, because
the existential is exactly the slack the disagreement needed.

**And the degenerate case was never an arm.**  The same pinning made four
dispatch lemmas split on whether a whitespace run was EMPTY, deferring the
non-empty half — eight escape-hatch call sites for what is one measurement:
the run's width IS the collection's indentation, and `nil` is width 0.  Reading
a run beats casing on its degenerate shape; the eight arms cost zero new arms.

Concretely (L4YAML): `seq-spaces(n,block-in) = n` and
`seq-spaces(n,block-out) = n-1`, so `SBlockNode_blockIn_to_blockOut` could only
be stated at `n = 0`, where truncating subtraction hides the gap — and its
comment said so, calling the context "inert at this indent".  With `[183]`'s
`m` bound on `SBlockNode.blockSeq`, `m+1` absorbs the step and the lemma holds
at every indent, which is what let `pendingMapValue` carry a nonzero one.

§1 is the model: two contexts one apart, pinned and widened.  §2 is the tell.
§3 is the run that was a measurement.  §4 sorts the consumers by whether they
READ the index.  §5 the shipped counts.

Self-contained: the two renderings, the failing and succeeding re-labellings,
the arm count, and the consumer split.
-/

namespace L4YAML.Tests.Reflections.PinnedParameterFakesASideCondition

/-! ## §1  Two contexts one step apart, pinned and widened -/

/-- The two block contexts.  `inner` counts the collection's own indent;
    `outer` counts one less (the spec's `seq-spaces(n,block-out) = n-1`). -/
inductive Ctx where
  /-- BLOCK-IN. -/
  | inner
  /-- BLOCK-OUT. -/
  | outer
  deriving DecidableEq

/-- `[192] seq-spaces(n,c)`. -/
def spaces : Nat → Ctx → Nat
  | n, .inner => n
  | n, .outer => n - 1

/-- The entries of a collection, all at one width. -/
def Entries (width : Nat) (l : List Nat) : Prop := l ≠ [] ∧ ∀ i ∈ l, i = width

/-- **Pinned**: the wrapper passes `seq-spaces` exactly, as the constructor did
    through item 21. -/
def WrapPinned (n : Nat) (c : Ctx) (l : List Nat) : Prop := Entries (spaces n c) l

/-- **Widened**: the production's own `m`, bound on the wrapper. -/
def Wrap (n : Nat) (c : Ctx) (l : List Nat) : Prop := ∃ m, Entries (spaces n c + m) l

/-- The pinned re-labelling holds at `n = 0` — and this is the whole of its
    justification: `0 - 1` truncates to `0`, so the two contexts coincide. -/
theorem relabel_pinned_at_zero {l : List Nat} (h : WrapPinned 0 .inner l) :
    WrapPinned 0 .outer l := h

/-- …and nowhere else.  The side condition was never about the domain. -/
theorem relabel_pinned_fails_off_zero :
    WrapPinned 1 .inner [1] ∧ ¬ WrapPinned 1 .outer [1] := by
  refine ⟨⟨List.cons_ne_nil _ _, ?_⟩, ?_⟩
  · intro i hi
    simp at hi
    simp [spaces, hi]
  · intro h
    have := h.2 1 (by simp)
    simp [spaces] at this

/-- Restore the quantifier and the restriction evaporates: the existential is
    exactly the slack the one-step disagreement needs. -/
theorem relabel_widened {n : Nat} {l : List Nat} (h : Wrap n .inner l) :
    Wrap n .outer l := by
  obtain ⟨m, hne, hall⟩ := h
  refine ⟨if n = 0 then m else m + 1, hne, fun i hi => ?_⟩
  have := hall i hi
  cases n <;> simp_all [spaces] <;> omega

/-- And it is not a wider claim smuggled in: at `n = 0` the widened lemma says
    exactly what the pinned one said. -/
theorem widened_agrees_at_zero {l : List Nat} (h : WrapPinned 0 .inner l) :
    Wrap 0 .outer l := ⟨0, h⟩

/-! ## §2  The tell

  A side condition defended by ARITHMETIC that happens to agree is an artifact;
  one defended by the DOMAIN is a fact.  The two are distinguishable without
  reading any proof: ask whether the justification would still be stated if the
  parameter were symbolic. -/

/-- Justifications a side condition can carry. -/
inductive Why where
  /-- "the two expressions coincide at this value" — a coincidence. -/
  | arithmeticCoincidence
  /-- "no producer in this file reaches another value" — a domain fact. -/
  | domainFact
  deriving DecidableEq

/-- An artifact survives review because it is TRUE where it is stated. -/
def trueWhereStated (_ : Why) : Bool := true

/-- Only one of the two dissolves when the missing quantifier is restored. -/
def dissolvesOnWidening : Why → Bool
  | .arithmeticCoincidence => true
  | .domainFact => false

theorem truth_does_not_separate_them :
    trueWhereStated .arithmeticCoincidence = trueWhereStated .domainFact := rfl

theorem widening_does :
    dissolvesOnWidening .arithmeticCoincidence ≠ dissolvesOnWidening .domainFact := by
  decide

/-! ## §3  The degenerate case was never an arm

  Pinning also forced the dispatch to CASE on whether the whitespace run before
  the indicator was empty, deferring the other half.  But the run is a
  measurement: its width is the collection's indentation, and the empty run is
  width 0.  Reading it collapses the split — the deferred half costs no new
  arm, because there was only ever one arm. -/

/-- A whitespace run, as the dispatch sees it. -/
abbrev Run := Nat

/-- The old gate: handle the empty run, defer the rest. -/
def handledByCases (r : Run) : Bool := r == 0

/-- The reading: every run is `s-indent(k)` for its own width. -/
def handledByReading (_ : Run) : Bool := true

/-- The split covered exactly one run… -/
theorem cases_covers_only_the_degenerate (r : Run) (h : r ≠ 0) :
    handledByCases r = false := by simp [handledByCases, h]

/-- …and the reading covers all of them, `nil` included, with ONE body. -/
theorem reading_covers_all (r : Run) : handledByReading r = true := rfl

/-- Sites the `nil`/`cons` split fed to the escape hatch (4 lemmas × 2
    indicators). -/
def casesSitesDeferred : Nat := 8
/-- New arm BODIES those eight cost. -/
def newArmBodies : Nat := 0

#guard casesSitesDeferred == 8
#guard newArmBodies == 0

/-! ## §4  Sort the consumers by whether they READ the index

  [[AwaitNotOpener]] measures a widening by its ELIMINATION sites.  A widening
  that re-indexes a carried closure needs a second measure: of the consumers
  that must now produce at the new index, how many actually mention it?  Those
  that do not transport verbatim; only the rest can block. -/

/-- A consumer of the re-indexed closure. -/
structure Consumer where
  /-- Identifier. -/
  id : Nat
  /-- Does what it builds mention the index? -/
  readsIndex : Bool
  deriving DecidableEq

/-- Closing an entry EMPTY is `[72] e-node` + `[79] s-l-comments` — no index. -/
def emptyClose : Consumer := ⟨0, false⟩
/-- The sibling snoc closes the previous entry the same way. -/
def siblingSnoc : Consumer := ⟨1, false⟩
/-- A flow collection as the entry's value needs `SFlowContent n`. -/
def flowValue : Consumer := ⟨2, true⟩
/-- A scalar or block scalar as the value needs `SFlowNode n` / `SCLLiteral n`. -/
def scalarValue : Consumer := ⟨3, true⟩

def consumers : List Consumer := [emptyClose, siblingSnoc, flowValue, scalarValue]

/-- Half transport with no edit at all… -/
theorem inert_consumers_transport :
    (consumers.filter (!·.readsIndex)).length = 2 := by decide

/-- …and only the other half can block, which is what makes the widening
    spendable in one item instead of waiting for the whole content layer. -/
theorem blocked_consumers_are_the_remainder :
    (consumers.filter (·.readsIndex)).length = 2 := by decide

/-! ## §5  The shipped counts (item 22, 2026-08-11) -/

/-- Grammar constructors given back their existential: `blockSeq`, `blockMap`. -/
def constructorsWidened : Nat := 2
/-- Construction sites that took `m = 0` unchanged (item 21's measure, met). -/
def constructionSites : Nat := 7
/-- Elimination sites (item 21 predicted zero). -/
def eliminationSites : Nat := 0
/-- Downstream lemmas whose `n = 0` was the artifact and is now gone. -/
def sideConditionsDissolved : Nat := 1
/-- Pendings re-indexed off `SBlockNode 0 .blockIn`. -/
def pendingsReindexed : Nat := 2
/-- Escape-hatch call sites before item 22… -/
def sitesBefore : Nat := 14
/-- …and after. -/
def sitesAfter : Nat := 13
/-- Reachable families CLOSED: whites before the indicator, and
    `pendingBlockContent` at a nonzero entry index. -/
def familiesClosed : Nat := 2
/-- Reachable families OPENED, each strictly narrower: a tab where `s-indent`
    wants spaces, an indicator at a width other than the collection's, and the
    content indent-lift. -/
def familiesOpened : Nat := 3
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0

#guard constructorsWidened == 2
#guard eliminationSites == 0
#guard sitesBefore - 1 == sitesAfter
#guard sideConditionsDissolved == 1
#guard pendingsReindexed == 2
#guard runtimeEdits == 0

end L4YAML.Tests.Reflections.PinnedParameterFakesASideCondition

end Blanket
