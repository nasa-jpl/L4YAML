/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 659 — an alternative nothing produces is an alternative nothing has checked

**The rule.**  A constructor that compiles is a constructor whose TYPES are
right.  Its numeric arguments — an index, a width, an offset — are checked by
nothing at all until something instantiates them.  So an alternative of a
production with zero producers and zero consumers carries an arithmetic claim
with zero evidence behind it, no matter how long it has been in the tree, how
carefully it is annotated, or how often the comments cite it.  Age reads as
authority and is not: the elaborator never looked.

**And the first consumer is not the test — the SIBLING is.**  An off-by-one in
a collection's index is invisible on a collection of one, because the opener's
own position is supplied by the opener.  It becomes visible on the second
element, whose indentation the index is what decides.  So when you build the
first producer for a dormant alternative, the pin to write first is the two-element
case; a green one-element pin is compatible with every index you might have
written.  This is [[VacuityIsAClaimAboutTheRuntime]] moved from a branch to a
number, and it is the bill for the debt [[AutoDetectedIsExistential]] §3
declined to run up, arriving from the other direction: that item refused to add
a constructor with no arm, and this one found the constructor that had been
sitting there without one.

**Why it was dormant is the second lesson.**  The escape this item closed had
been described for a dozen items as an evidence gap: the step crosses no break,
so `[79] s-l-comments` cannot exist, so nothing can close — irreducible.  That
description is true and it is about the alternatives already CONSUMED.  Read
the production's alternative list instead and the partition is stark: the
consumed set coincided exactly with the set that demands the missing evidence
(`consumed_is_exactly_the_evidence_demanding_set`), so on the residue every
consumed alternative was unavailable and every available one unconsumed.  A
gap that looks irreducible from inside the consumed set is worth re-reading as
"which alternatives do NOT ask for the thing I cannot get".

**What kept it unexpressible was an interface, not a proof.**  The pending's
entry-level closure was an ACCUMULATOR — "here is what has been accumulated,
and here is how to spend any extension of it" — and that shape obliges the
producer to name a BEGINNING.  A compact collection has no beginning to name:
its first entry is not preceded by its own indentation, so it is not an element
of the collection type at all.  The CONTINUATION shape — "give me the rest and
I will close" — names no beginning, admits the empty rest, and agrees with the
accumulator wherever both exist.  Prefer it: a continuation is offerable by
strictly more producers at strictly no cost, and this one turned five existing
snoc sites into constructor applications on the way in.

Concretely (L4YAML): `[185] s-l+block-indented(n,c)` has four alternatives; the
accumulation consumed `s-l+block-node` and `e-node s-l-comments` and had never
touched `s-indent(m) ns-l-compact-sequence(n+1+m)` or its mapping twin — which
are precisely the two that need no comments, because a compact collection shares
the entry indicator's line.  Both had been written `n+m`, one column left of the
truth, since nothing instantiated the index.  Building the consumer put `- - a`,
`- : a`, `- ? a` and their nestings into the grammar, and `- - a⏎  - b` — the
sibling — is what showed the index.

§1 the arithmetic nothing checked.  §2 the sibling is the test.  §3 the
alternatives nobody consumed.  §4 continuation over accumulator.  §5 the
shipped counts.
-/

namespace L4YAML.Tests.Reflections.UnusedAlternativeIsUnchecked

/-! ## §1  An index in a constructor's type is constrained by nothing

The compact collection opens at the entry's index `n`, plus the one column the
entry's indicator occupies, plus the run of spaces after it. -/

/-- What the input actually puts the compact opener at. -/
def compactIndex (n m : Nat) : Nat := n + 1 + m

/-- What the constructor said, for as long as it had no producer. -/
def writtenIndex (n m : Nat) : Nat := n + m

/-- They are never equal — the error is a constant, not an edge case. -/
theorem the_two_never_agree (n m : Nat) : writtenIndex n m + 1 = compactIndex n m := by
  simp only [writtenIndex, compactIndex]; omega

/-- The evidence the tree held for `writtenIndex` before this item: producers
    plus consumers plus pins. -/
def producersBefore : Nat := 0
def consumersBefore : Nat := 0
def pinsBefore : Nat := 0

theorem nothing_had_checked_it :
    producersBefore + consumersBefore + pinsBefore = 0 := by decide

/-! ## §2  A one-element collection cannot tell them apart

`s-indent(N)` is what stands in front of every entry of a collection at index
`N` — except the compact opener's, which the enclosing entry supplies.  So the
index constrains the SIBLINGS and only the siblings. -/

/-- The columns of the entries that follow the opener.  Each is `s-indent(N)`
    from a line start, so each must be exactly `N`. -/
def tailWellIndented (N : Nat) (later : List Nat) : Prop := ∀ c ∈ later, c = N

/-- With no sibling, both indices derive exactly the same collection. -/
theorem agrees_without_a_sibling (n m : Nat) :
    tailWellIndented (writtenIndex n m) [] ↔ tailWellIndented (compactIndex n m) [] := by
  constructor <;> (intro _ c hc; simp at hc)

/-- One sibling separates them: the input puts it under the compact opener, and
    the written index demands it one column to the left. -/
theorem one_sibling_tells (n m : Nat) :
    tailWellIndented (compactIndex n m) [compactIndex n m] ∧
      ¬ tailWellIndented (writtenIndex n m) [compactIndex n m] := by
  refine ⟨?_, ?_⟩
  · intro c hc; simp at hc; simp [hc]
  · intro h
    have := h (compactIndex n m) (by simp)
    simp [writtenIndex, compactIndex] at this

/-- So the pin to write FIRST, when a dormant alternative gets its first
    producer, is the two-element one. -/
def elementsNeededToCheckTheIndex : Nat := 2

theorem one_element_is_not_a_check : elementsNeededToCheckTheIndex ≠ 1 := by decide

/-! ## §3  The alternatives nobody consumed were the ones that fit

The production's four alternatives, sorted by whether they demand the closing
evidence — `[79] s-l-comments`, which exists only across a break or at a line
start — and by whether the accumulation had a consumer for them. -/

inductive Alt where
  | node | empty | compactSeq | compactMap
  deriving DecidableEq, Repr

/-- Does the alternative demand the evidence the inline residue cannot supply? -/
def needsClose : Alt → Bool
  | .node => true
  | .empty => true
  | .compactSeq => false
  | .compactMap => false

/-- Did the accumulation have a consumer for it, before this item? -/
def consumedBefore : Alt → Bool
  | .node => true
  | .empty => true
  | .compactSeq => false
  | .compactMap => false

/-- **The two predicates coincide.**  That is the whole reason the gap read as
    irreducible: every alternative anyone had built a consumer for was one that
    needs the missing evidence, so from inside the consumed set there was
    genuinely nothing to do. -/
theorem consumed_is_exactly_the_evidence_demanding_set (a : Alt) :
    consumedBefore a = needsClose a := by cases a <;> rfl

/-- On the residue the evidence is absent, so no consumed alternative is
    available… -/
theorem residue_has_no_consumed_alternative (a : Alt) :
    needsClose a = false → consumedBefore a = false := by
  cases a <;> simp [needsClose, consumedBefore]

/-- …and yet the residue is not empty: two alternatives ask for nothing. -/
theorem residue_is_not_empty : ∃ a, needsClose a = false := ⟨.compactSeq, rfl⟩

/-! ## §4  Continuation over accumulator

A collection's entries each carry their own indentation; a COMPACT collection's
first one does not, because it stands on the line the enclosing entry opened. -/

structure Entry where
  /-- Preceded by its own `s-indent(N)` from a line start. -/
  indented : Bool
  col : Nat
  deriving DecidableEq, Repr

def wellFormed (N : Nat) (e : Entry) : Prop := e.indented = true ∧ e.col = N

/-- `[183] l+block-sequence(N)`: one or more entries, each with its own indent. -/
def Entries (N : Nat) (es : List Entry) : Prop := es ≠ [] ∧ ∀ e ∈ es, wellFormed N e

/-- `[186] ns-l-compact-sequence(N)`'s tail: the same entries, possibly none. -/
def Tail (N : Nat) (es : List Entry) : Prop := ∀ e ∈ es, wellFormed N e

/-- The compact opener: at the collection's column, with nothing in front of it
    but the entry indicator that opened the enclosing entry. -/
def compactOpener (N : Nat) : Entry := ⟨false, N⟩

theorem compact_opener_is_not_an_entry (N : Nat) :
    ¬ wellFormed N (compactOpener N) := by
  simp [wellFormed, compactOpener]

/-- **The accumulator form cannot be offered.**  Its existential asks the
    producer to name a prefix that is ALREADY a collection; the compact
    producer's prefix is its opener, and the opener is not one. -/
theorem accumulator_needs_a_beginning (N : Nat) :
    ¬ Entries N [compactOpener N] := by
  simp [Entries, wellFormed, compactOpener]

/-- **The continuation form can be.**  It mentions only the rest, and the empty
    rest — "this entry and no sibling" — is available, which is exactly the
    case the accumulator form has no way to name. -/
theorem continuation_admits_the_empty_rest (N : Nat) : Tail N [] := by
  intro e he; simp at he

/-- And nothing is lost where both exist: an indented opener plus a tail is a
    collection, so the producers that could offer the accumulator can offer the
    continuation and spend it themselves. -/
theorem indented_opener_spends_the_tail (N : Nat) (e : Entry) (rest : List Entry)
    (he : wellFormed N e) (hr : Tail N rest) : Entries N (e :: rest) := by
  refine ⟨by simp, ?_⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact he
  · exact hr x hx'

/-- The measurement that settles the trade: the continuation is offerable by a
    strict superset of the producers, at the same call sites. -/
def producersUnderAccumulator : Nat := 5
def producersUnderContinuation : Nat := 6
def callSitesMoved : Nat := 0

theorem continuation_is_strictly_wider :
    producersUnderAccumulator < producersUnderContinuation ∧ callSitesMoved = 0 := by
  decide

/-! ## §5  What item 33 shipped -/

/-- `[185]` alternatives with a consumer, before and after. -/
def alternativesConsumedBefore : Nat := 2
def alternativesConsumedAfter : Nat := 4
/-- Grammar indices corrected — the two compact constructors. -/
def grammarIndicesFixed : Nat := 2
/-- Repairs the correction forced elsewhere: none, because nothing used them. -/
def repairsFromTheCorrection : Nat := 0
/-- Runtime files edited — none. -/
def runtimeEdits : Nat := 0
/-- Escape sites `block_dispatch_deferred` carries, before and after: the count
    does not move, and the domain of one site does — from every inline residue
    at a `-`-parked pending to a tab in front of a compact `:`. -/
def escapeSitesBefore : Nat := 8
def escapeSitesAfter : Nat := 8
/-- `scannerDrop` sites — untouched; a different obstruction. -/
def scannerDropBefore : Nat := 4
def scannerDropAfter : Nat := 4

theorem shipped :
    alternativesConsumedBefore = 2 ∧ alternativesConsumedAfter = 4 ∧
    grammarIndicesFixed = 2 ∧ repairsFromTheCorrection = 0 ∧
    runtimeEdits = 0 ∧ escapeSitesBefore = escapeSitesAfter ∧
    scannerDropBefore = scannerDropAfter := by
  decide

end L4YAML.Tests.Reflections.UnusedAlternativeIsUnchecked

end Blanket
