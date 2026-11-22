/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 652 — removing a pin returns a side condition, and a side condition is only as available as the quantity it names

**The rule.**  Un-pinning a parameter does not hand you the general statement.
It hands you the general statement PLUS a side condition — the arithmetic that
the constant used to satisfy for free.  So price the item by that side
condition's VOCABULARY, not by the widening: if it names quantities your
invariant already threads, the item finishes; if it names one the invariant has
never carried, the widening lands, the case still defers, and the remaining work
is a threading job in a different layer than the one you were looking at.

**How to see it before starting.**  Write the side condition down and grep your
invariant for each name in it.  A name with zero occurrences in *code* — prose
mentions do not count, and are in fact the warning sign, since a quantity gets
described in comments precisely when it is doing work nothing states — is the
whole remaining item.

**The corollary that scheduled this one.**  A diagnosis recorded by ANALOGY to
the previous item ("this is the last item's shape, one level down") is the
cheapest kind to write and the least likely to survive contact.  Check that the
construct actually has the defect the analogy attributes to it: an auto-detected
extra indent that the CONSTRUCTOR binds admits every index below the detected
value, while one INLINED at its smallest legal value admits exactly one.  From
outside they are described by the same sentence; they are opposite.  When the
analogy is wrong, the fix it prescribes has already been done, and the real
residue sits one layer further out than the analogy can see
([[DifferentQuestionNotAHarderCase]] is the same failure at the level of cases).

Concretely (L4YAML): item 23 filed the indented block scalar under
[[AutoDetectedIsExistential]] — `[170] c-l+literal(n)`'s content indent, pinned
by a reading at 0 exactly as inlining `m` pinned `[183] l+block-sequence(n)`.
But `SCLLiteral`'s constructor binds its `m`; there was no production to widen.
The pin was in the PRODUCTION LEMMA, which measured the scanner's detected
indent and threw it away by concluding at 0 — [[ConstantPreconditionIsUnmeasuredQuantity]],
one file over.  Keeping it costs nothing and leaves `n ≤ d`, an inequality true
of every accepted input (an entry sits at `currentIndent`; the body's floor is
`currentIndent + 1`) and underivable from an invariant in which `currentIndent`
occurs zero times.

§1 is bound-versus-inlined, the distinction the analogy erased.  §2 is the
side condition the widening returns.  §3 is why its vocabulary, not its
difficulty, is what prices it.  §4 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.SideConditionNeedsItsQuantity

/-! ## §1  Bound by the constructor versus inlined at its smallest value

Both are "an auto-detected extra indent".  One admits every index below the
detected value; the other admits exactly one.  The analogy that carried item 23's
diagnosis forward could not tell them apart, because the sentence describing them
is the same. -/

/-- `[170] c-l+literal(n)`-shaped: the construct at index `n` over a body
    collected at `d` exists exactly when some `m` closes the gap.  The `m` is a
    CONSTRUCTOR argument, so it is existential by construction. -/
inductive Bound (d : Nat) : Nat → Prop where
  | mk (n m : Nat) (h : n + m = d) : Bound d n

/-- `[183] l+block-sequence(n)`-shaped BEFORE item 22: the extra indent inlined
    at its smallest legal value, so the construct exists at one index only. -/
inductive Inlined (d : Nat) : Nat → Prop where
  | mk : Inlined d d

/-- The bound form reads at every index below the detected value — no
    induction, no lift, just the arithmetic the constructor already asks for. -/
theorem bound_reads_below (d n : Nat) (h : n ≤ d) : Bound d n :=
  Bound.mk n (d - n) (by omega)

/-- …and only there. -/
theorem bound_only_below (d n : Nat) (h : Bound d n) : n ≤ d := by
  cases h with | mk m hm => omega

/-- The inlined form reads at exactly one index, whatever `d` is. -/
theorem inlined_reads_at_one (d n : Nat) (h : Inlined d n) : n = d := by
  cases h; rfl

/-- So the analogy is not merely imprecise, it is inverted: what the widening
    was supposed to buy, the bound form already had. -/
theorem the_analogy_inverts_them (d : Nat) (hd : 0 < d) :
    Bound d 0 ∧ ¬ Inlined d 0 :=
  ⟨bound_reads_below d 0 (Nat.zero_le d),
   fun h => by have := inlined_reads_at_one d 0 h; omega⟩

/-! ## §2  What the widening actually returns

Not `∀ n, Construct n` — that is false, and it is false for a reason the
grammar is right about.  What it returns is `∀ n, n ≤ d → Construct n`, and the
consumer's obligation is the antecedent. -/

/-- The production lemma as it stood: it HELD the measured `d` and answered at
    one index.  Sound, and useless to a consumer whose index is not that one. -/
def pinnedAnswer (d : Nat) : Prop := Bound d 0

/-- The same proof with the measurement kept. -/
def keptAnswer (d : Nat) : Prop := ∀ n, n ≤ d → Bound d n

/-- Keeping it is strictly stronger… -/
theorem kept_gives_pinned (d : Nat) (h : keptAnswer d) : pinnedAnswer d :=
  h 0 (Nat.zero_le d)

/-- …and the pinned form cannot be recovered from itself: `Bound d 0` is
    information-free, since every `d` has it. -/
theorem pinned_is_free (d : Nat) : pinnedAnswer d := bound_reads_below d 0 (Nat.zero_le d)

/-- The consumer does not want the general statement; it wants ONE instance, and
    what stands between it and that instance is the antecedent. -/
theorem consumer_needs_the_antecedent (d k : Nat) (h : keptAnswer d) (hk : k ≤ d) :
    Bound d k := h k hk

/-! ## §3  The antecedent's vocabulary is what prices the item

The obligation `k ≤ d` is true of every state the scanner reaches, and the proof
is one line — but it goes through a quantity the invariant does not carry, and an
invariant cannot discharge an obligation it cannot mention. -/

/-- Three numbers: the scanner's own indent, the parked entry's index, and the
    indent the body was collected at. -/
structure World where
  /-- The scanner's indent stack top — the quantity the invariant never carried. -/
  scannerIndent : Nat
  /-- The index the accumulator parked with the entry. -/
  entryIndex : Nat
  /-- The indent the block-scalar body was collected at. -/
  bodyIndent : Nat

/-- What the scanner guarantees: an entry sits AT the current indent, and the
    body's floor is one deeper.  Both halves name `scannerIndent`. -/
def scannerGuarantee (w : World) : Prop :=
  w.entryIndex = w.scannerIndent ∧ w.scannerIndent + 1 ≤ w.bodyIndent

/-- Given the guarantee, the obligation is immediate — this is the whole of the
    missing proof, and it is one `omega`. -/
theorem obligation_holds (w : World) (h : scannerGuarantee w) :
    w.entryIndex ≤ w.bodyIndent := by
  obtain ⟨h1, h2⟩ := h
  rw [h1]; omega

/-- What the accumulation invariant says about a parked entry today: that it has
    an index.  Nothing ties it to the scanner's stack. -/
def invariant (_w : World) : Prop := True

/-- So the invariant admits a state the guarantee excludes, and in that state the
    obligation is false.  The widening is complete and the case still defers —
    not because the reading is missing, but because the vocabulary is. -/
theorem invariant_admits_a_counterexample :
    invariant ⟨0, 5, 3⟩ ∧ ¬ scannerGuarantee ⟨0, 5, 3⟩ ∧ ¬ (5 ≤ 3) := by
  refine ⟨True.intro, ?_, by omega⟩
  simp [scannerGuarantee]

/-- The pre-flight check the rule prescribes, as a statement rather than a grep:
    the obligation is derivable exactly when the guarantee is available, so the
    item's remaining cost is the cost of carrying `scannerIndent`. -/
theorem cost_is_the_missing_quantity :
    (∀ w : World, scannerGuarantee w → w.entryIndex ≤ w.bodyIndent) ∧
    ¬ (∀ w : World, invariant w → w.entryIndex ≤ w.bodyIndent) :=
  ⟨obligation_holds, fun h => by have hbad := h ⟨0, 5, 3⟩ True.intro; simp at hbad⟩

/-! ## §4  What item 26 shipped -/

/-- Grammar files edited.  None — `[170]`/`[174]` already bound their `m`, which
    is the finding. -/
def grammarEdits : Nat := 0
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0
/-- Scanner-side lemmas the floor needed that did not already exist.  None:
    `autoDetectBlockScalarIndent_ge_min` and `parseBlockHeaderLoop_offset_preserves`
    were both in the tree, unread by the production lemma above them. -/
def newScannerLemmas : Nat := 0
/-- New proof lemmas: the body's floor, the reading at every admitted index, and
    the dispatcher wrapper. -/
def newProofLemmas : Nat := 3
/-- A vacuous lemma deleted — `∃ m, m ≥ 1`, the pre-item-26 attempt at the floor,
    true of everything and cited by nothing. -/
def vacuousLemmasDeleted : Nat := 1
/-- Consumers that now build `[198]`'s block scalar at the entry's index. -/
def consumersComposed : Nat := 3
/-- Escape call sites: UNCHANGED.  The guard is asked inside the shared question
    rather than at each consumer, which is what keeps three negative answers from
    becoming three extra call sites ([[WideningIsAnOccurrenceQuestion]] §4). -/
def escapeSitesBefore : Nat := 14
/-- See `escapeSitesBefore`. -/
def escapeSitesAfter : Nat := 14
/-- Opaque `scannerDrop` sites: unchanged. -/
def dropSites : Nat := 4
/-- Negative answers of the shared question: unchanged at three — but the third
    went from a CONSTRUCT ("a block scalar") to an INEQUALITY ("an entry deeper
    than the body's floor"), which no count can report. -/
def negativeAnswersBefore : Nat := 3
/-- See `negativeAnswersBefore`. -/
def negativeAnswersAfter : Nat := 3
/-- Occurrences of the missing quantity in the invariant's code, before and
    after — the number that says the item is not finished. -/
def quantityOccurrences : Nat := 0

theorem shipped :
    grammarEdits = 0 ∧ runtimeEdits = 0 ∧ newScannerLemmas = 0 ∧
    newProofLemmas = 3 ∧ vacuousLemmasDeleted = 1 ∧ consumersComposed = 3 ∧
    escapeSitesAfter = escapeSitesBefore ∧ dropSites = 4 ∧
    negativeAnswersAfter = negativeAnswersBefore ∧ quantityOccurrences = 0 := by
  decide

end L4YAML.Tests.Reflections.SideConditionNeedsItsQuantity

end Blanket
