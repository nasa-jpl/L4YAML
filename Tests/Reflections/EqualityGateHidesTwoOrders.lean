/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 656 — an EQUALITY gate on an ordered index hides two constructs, and one of them is already written next door

**The rule.**  When an arm is gated on `k = n` for an ordered `k` and `n`, its
escape holds at least two cases by construction — `n < k` and `k < n` — and on
an ordered quantity those are usually different CONSTRUCTS, not a harder and an
easier instance of one.  So split the negation before pricing the item.  The
split is free: it is `Nat.lt_or_ge`, and the side condition each half needs is
the same arithmetic that decides which construct it is.

**Why the equality hides it so well.**  `k ≠ n` reads like one condition, it
costs one `by_cases`, and it routes to one escape with one argument list —
every surface an arm presents says "one case".  The tell is the GATE's type,
not the arm's body: an equality between two members of an ordered set has an
asymmetric negation, and if the thing being compared indexes a production whose
parameter is a DIFFERENCE, the two orders differ in whether that difference
exists at all.  Here `[183] l+block-sequence`'s auto-detected `m` is `k - n`
over `Nat`: at `n ≤ k` it is the extra indentation, and below that there is no
`m` to choose.  Truncating subtraction will not tell you — `n + (k - n) = k`
holds exactly on the half where the construct exists (`difference_exists_iff`,
`truncation_is_silent`), so the side condition the wrap lemma needs IS the case
split, arriving for free from the arithmetic rather than as an extra hypothesis
to go and find ([[SideConditionNeedsItsQuantity]] is the case where it does not
arrive for free).

**Then check the SIBLING arms before writing a body.**  An escape arm's
neighbours in the same case split are the first place to look for its body.  A
dispatch usually has several arms over the same state, and when one of them
defers on a condition the others never even test, that asymmetry is a bug
report rather than a design: the case has a body, sitting in the same file,
already reached by a sibling.  Delegating to it is a line, and the coverage it
buys is real (`sibling_already_covers_it`, `delegation_is_the_siblings_body`,
which is `rfl`).  The consequence for planning: the cases behind one escape do
not cost the same, so the item's price is not the number of them
(`cost_is_not_uniform`).

**And the split's ARITY belongs to the state, not to the gate.**  The same
`k = n` gate appears in two lemmas here and splits 2-and-1, not 2-and-2,
because what admits the nested reading is the PENDING's shape: an entry still
awaiting its node can have that node be the inner collection, and an entry that
already has one cannot (`awaiting_admits_nested`, `completed_admits_neither`).
Read the state, not the gate, to find out how many bodies you owe.

Concretely (L4YAML): `accum_block_on_pendingBlock` and
`accum_block_on_pendingBlockContent` both gated their `-` arm on `k = n` and
deferred the rest as one case.  Item 30 splits it: `n < k` on the AWAITING
pending is a nested `[199] s-l+block-collection` at `m = k - n`
(`nestedBlockSeq`, and the new pending is an ordinary `pendingBlock` at the
inner index, so nesting composes to any depth); every other combination takes
`accum_block_on_closeThenBlock`, which the `:` and `?` arms of those same two
lemmas have used at every width since item 13.  Escape sites 14 → 12.

§1 is the ordered negation and its free side condition.  §2 the sibling arm.
§3 the arity that belongs to the state.  §4 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.EqualityGateHidesTwoOrders

/-! ## §1  The negation of an equality on an ordered index is two cases

And the production parameter that distinguishes them is a DIFFERENCE, so one
half has it and the other does not. -/

/-- `[183]`'s auto-detected extra indentation, as the wrap lemma must choose
    it: the inner collection's width minus the outer entry's. -/
def extra (n k : Nat) : Nat := k - n

/-- The wrap is well-formed exactly when the difference reconstructs the inner
    index — which is exactly one side of the order. -/
theorem difference_exists_iff (n k : Nat) : n + extra n k = k ↔ n ≤ k := by
  unfold extra; omega

/-- **The trap.**  Truncating subtraction does not complain on the wrong side:
    `extra` is total, so the wrap's `m` still elaborates at `k < n` and simply
    names the wrong collection.  Nothing in the arm's shape reports it; only
    the equation above does. -/
theorem truncation_is_silent : extra 4 2 = 0 ∧ 4 + extra 4 2 ≠ 2 := by decide

/-- The split itself is free, and it is the same inequality the wrap needs —
    the side condition is not an extra obligation, it is the discriminator. -/
theorem the_gate_splits (n k : Nat) (h : ¬ k = n) : n < k ∨ k < n := by omega

/-- …and the composable half is picked out by the wrap's own hypothesis, with
    nothing left to establish separately. -/
theorem composable_half_needs_nothing_new (n k : Nat) (h : n < k) :
    n + extra n k = k := (difference_exists_iff n k).2 (Nat.le_of_lt h)

/-! ## §2  The sibling arm already has the body

The `-` arm deferred on a width mismatch; the `:` and `?` arms of the same
dispatch never tested the width at all.  One of them is wrong, and it is not
the two that cover more. -/

/-- The three block indicators. -/
inductive Indicator where
  | dash | colon | question
  deriving DecidableEq, Repr

/-- Which widths an arm accepted, BEFORE the item: the mapping indicators take
    any width through the shared close-and-reopen body; the `-` demanded the
    pending's own. -/
def acceptedBefore : Indicator → Nat → Nat → Bool
  | .dash, k, n => k == n
  | .colon, _, _ | .question, _, _ => true

/-- The shared body both mapping arms already routed to. -/
def sharedFallback (k : Nat) : Nat := k

/-- The `-` arm's mismatched case, once written, IS that body — the delegation
    is definitional, not an analogy. -/
theorem delegation_is_the_siblings_body (k : Nat) : sharedFallback k = k := rfl

/-- So the deferred case was covered all along, one arm over. -/
theorem sibling_already_covers_it :
    acceptedBefore .dash 0 2 = false ∧ acceptedBefore .colon 0 2 = true := by decide

/-- The asymmetry is what makes it findable: the arms of ONE dispatch disagree
    about which inputs they handle, on a condition two of them never mention. -/
theorem the_asymmetry_is_the_report :
    ∃ k n, acceptedBefore .dash k n ≠ acceptedBefore .colon k n :=
  ⟨0, 2, by decide⟩

/-- The two halves the gate was hiding: `n < k` on an entry awaiting its node
    (which wants a new grammar wrap) and everything else (which delegates). -/
inductive Half where
  | nestedOpen | mismatchElsewhere
  deriving DecidableEq, Repr

/-- **The planning consequence.**  The cases behind one escape do not cost the
    same, so the item's price is not their number: one half wanted a new
    grammar wrap and the other wanted a line. -/
def newLemmasFor : Half → Nat
  | .nestedOpen => 1
  | .mismatchElsewhere => 0

theorem cost_is_not_uniform :
    newLemmasFor .nestedOpen ≠ newLemmasFor .mismatchElsewhere := by decide

/-! ## §3  How many bodies you owe is a fact about the STATE

The same gate sits in two lemmas.  It splits into two live cases in one of them
and one in the other, because the nested reading needs a node-shaped HOLE to
fill and only one of the two pendings has one. -/

/-- The two block-sequence pendings. -/
inductive Pending where
  /-- The entry's `-` was consumed; its node is still awaited. -/
  | awaitingNode
  /-- The entry's node is already there; the entries are complete. -/
  | nodeComplete
  deriving DecidableEq, Repr

/-- Whether the deeper `-` can be read as the awaited node's own collection. -/
def admitsNested : Pending → Bool
  | .awaitingNode => true
  | .nodeComplete => false

theorem awaiting_admits_nested : admitsNested .awaitingNode = true := rfl

/-- A completed entry admits NEITHER order: there is no hole for the nested
    reading and no frame for the dedent, so its whole mismatch is one case. -/
theorem completed_admits_neither : admitsNested .nodeComplete = false := rfl

/-- Live bodies owed per lemma — read off the state, not off the gate. -/
def bodiesOwed (p : Pending) : Nat := if admitsNested p then 2 else 1

theorem arity_differs : bodiesOwed .awaitingNode ≠ bodiesOwed .nodeComplete := by decide

/-- And what the DEDENT lacks is not strength but a frame: the pending carries
    one index, so the collection a dedent lands back in has no accumulator to
    resume.  Recorded, not attempted — a stack of frames is its own item. -/
def indicesCarriedByPending : Nat := 1
def indicesADedentNeeds : Nat := 2

theorem dedent_wants_a_frame : indicesCarriedByPending < indicesADedentNeeds := by decide

/-! ## §4  What item 30 shipped -/

/-- Grammar files edited. -/
def grammarEdits : Nat := 0
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0
/-- New grammar-wrap lemmas: `nestedBlockSeq`, which `rootBlockSeq` then
    becomes an instance of. -/
def newWrapLemmas : Nat := 1
/-- Wrap lemmas RETIRED by it — none; `rootBlockSeq` keeps its name and its
    call sites, and loses only its body. -/
def wrapLemmasRetired : Nat := 0
/-- Arms closed by delegating to a sibling's body. -/
def delegatedArms : Nat := 2
/-- Arms closed by a new derivation. -/
def composedArms : Nat := 1
/-- Escape call sites before. -/
def escapeSitesBefore : Nat := 14
/-- …and after: the whole family is gone. -/
def escapeSitesAfter : Nat := 12
/-- Opaque `scannerDrop` sites: unchanged. -/
def dropSites : Nat := 4

theorem shipped :
    grammarEdits = 0 ∧ runtimeEdits = 0 ∧ newWrapLemmas = 1 ∧
    wrapLemmasRetired = 0 ∧ delegatedArms = 2 ∧ composedArms = 1 ∧
    escapeSitesBefore = 14 ∧ escapeSitesAfter = 12 ∧ dropSites = 4 := by
  decide

end L4YAML.Tests.Reflections.EqualityGateHidesTwoOrders

end Blanket
