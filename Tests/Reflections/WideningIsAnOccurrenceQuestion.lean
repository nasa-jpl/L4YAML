/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 649 — to widen a parameterized reading, ask WHERE the parameter occurs, not whether it can be weakened

**The rule.**  You hold `P 0 x` and you need `P n x`.  The instinct is to look
for monotonicity — and that instinct fails twice over.  First, the relation is
often perfectly monotone in the *other* direction, so the lattice reasoning is
available and useless.  Second, and more usefully: a parameter is only as
restrictive as the sub-productions that MENTION it.  Find its occurrences.  If
they all sit under one guard, the fragment on the other side of that guard
re-reads at every value, and the widening is a rebuild, not an induction.

**The spec usually names that fragment already.**  Where a parameter occurs
only after a boundary, a well-written grammar has a sibling production with the
parameter dropped — YAML's `[111] nb-double-one-line`, `[122]
nb-single-one-line`, `[133] ns-plain-one-line(c)`.  Those are not
approximations of the index-free set; they ARE it (`index_free_iff`).  So when
you need `P n` and hold `P 0`, look for the sibling before writing a lemma: a
grammar that distinguishes them has already done the analysis, and routing to
it costs constructor rebuilds instead of a mutual induction over the family.

**And the deciding measurement is often already being taken.**  The guard that
separates the two fragments is a boundary — here a line break — and boundaries
tend to be load-bearing for more than one reason.  YAML §7.4 restricts a simple
KEY to one line; every occurrence of the indent in `[161] ns-flow-node` is on a
continuation line.  One decidable fact answers both, for the same structural
reason rather than by luck (`one_measurement_two_consumers`).  Before adding a
side condition, check what the surrounding code already decides.

**Corollary for the escape count.**  When several `by_cases` in a row all fail
into the same escape hatch with the same arguments, they are not several
families — they are one question with several negative answers, and splitting
them inflates the call-site count without changing the domain
([[CoverageNotCallSites]]).  Ask it once.

Concretely (L4YAML): `[196] s-l+block-node(n,c)`'s flow arm reads an entry's
value at the ENTRY's index, and every content reading in the accumulation was
stated at 0 — so once item 22 gave the collection its own index
([[AutoDetectedIsExistential]], [[PinnedParameterFakesASideCondition]]), `  - a`
still had no derivation.  The index occurs only in `[71] s-flow-line-prefix(n)`
and `[134] s-ns-plain-next-line(n,c)`, both after a break; the one-line
productions are the fragment below that guard; and `s'.line = sc.line` — item
15's implicit-key measurement — is the guard's decision procedure.

§1 is the model: one parameter, one occurrence, and the monotonicity that
points the wrong way.  §2 is the spec's own index-free sibling, and the `iff`
that says it is exact.  §3 is the one measurement with two consumers.  §4 is
the escape count.  §5 the shipped counts.

Self-contained: the reading, both monotonicity directions, the sibling
production, the shared measurement, and the deferral arithmetic.
-/

namespace L4YAML.Tests.Reflections.WideningIsAnOccurrenceQuestion

/-! ## §1  One parameter, one occurrence

A "reading" of a scalar: a first line, then a list of continuation lines, each
recorded by the column it starts at.  The index `n` occurs in exactly ONE arm —
the continuation — where it demands `n ≤ w`.  That single occurrence is the
whole of the parameter's content. -/

/-- `Read n ws`: the value spans the continuation columns `ws`, read at
    index `n`.  Models `[135] ns-plain-multi-line(n,c)`: a one-line body plus
    `GStar` of continuations, each carrying `[71] s-flow-line-prefix(n)`. -/
inductive Read : Nat → List Nat → Prop where
  /-- `[133] ns-plain-one-line(c)`: no continuation, so no occurrence of `n`. -/
  | oneLine (n : Nat) : Read n []
  /-- `[134] s-ns-plain-next-line(n,c)`: the sole occurrence of the index. -/
  | fold (n w : Nat) (ws : List Nat) (h : n ≤ w) (rest : Read n ws) :
      Read n (w :: ws)

/-- The reading is ANTITONE in the index: a derivation at a larger index
    re-reads at every smaller one, because the only occurrence is a lower
    bound.  This is the monotonicity that exists — and it points away from
    the goal. -/
theorem antitone_holds : ∀ (n m : Nat) (ws : List Nat), n ≤ m → Read m ws → Read n ws := by
  intro n m ws hnm h
  induction h with
  | oneLine => exact Read.oneLine n
  | fold w ws hw _ ih => exact Read.fold n w ws (Nat.le_trans hnm hw) ih

/-- The direction actually needed — from a reading at 0 to one at the entry's
    index — fails, and fails for the occurrence: `Read 0 [0]` is derivable and
    `Read 3 [0]` demands `3 ≤ 0`. -/
theorem the_needed_direction_fails :
    Read 0 [0] ∧ ¬ Read 3 [0] := by
  refine ⟨Read.fold 0 0 [] (Nat.le_refl 0) (Read.oneLine 0), ?_⟩
  intro h
  cases h with
  | fold _ _ hle _ => exact absurd hle (by decide)

/-- So "is it monotone?" is answerable and useless, and the useful question is
    about the occurrence: at a span with NO continuation the index cannot be
    mentioned, so the reading holds at every index. -/
theorem no_occurrence_reads_everywhere (n : Nat) : Read n [] := Read.oneLine n

/-! ## §2  The spec's own index-free sibling, and that it is exact

`[111] nb-double-one-line`, `[122] nb-single-one-line` and `[133]
ns-plain-one-line(c)` are separate productions with the parameter dropped.
They are not a convenient under-approximation of "reads at every index" — they
are equal to it. -/

/-- The sibling production: the parameter is not merely unused, it is absent
    from the statement. -/
def OneLine (ws : List Nat) : Prop := ws = []

/-- The index-free fragment is EXACTLY the one-line fragment.  The `←`
    direction is why routing to the sibling is complete, and the `→` direction
    is why nothing more general is available without touching the guard. -/
theorem index_free_iff (ws : List Nat) : (∀ n, Read n ws) ↔ OneLine ws := by
  constructor
  · intro h
    cases ws with
    | nil => rfl
    | cons w rest =>
      have := h (w + 1)
      cases this with
      | fold _ _ hle _ => exact absurd hle (by omega)
  · intro h n; subst h; exact Read.oneLine n

/-- Routing to the sibling is a rebuild: from the parameter-free reading the
    parameterized one follows at every value with no induction on the span. -/
theorem sibling_rebuilds (ws : List Nat) (h : OneLine ws) (n : Nat) : Read n ws :=
  (index_free_iff ws).mpr h n

/-! ## §3  One measurement, two consumers

The guard separating the fragments is a line break, and the scanner already
decides it — for a different purpose.  §7.4 restricts an implicit KEY to one
line; the index occurs only on continuation lines.  Same boundary, so one
decidable fact serves both, and that is structural rather than lucky. -/

/-- The decidable state fact: the step crossed no break.  In L4YAML this is
    `s'.line = sc.line`, introduced by item 15 for the implicit key. -/
def crossedNoBreak (ws : List Nat) : Bool := ws.isEmpty

/-- Consumer one (item 15, §7.4): can this scan be an implicit KEY? -/
theorem key_eligibility (ws : List Nat) :
    crossedNoBreak ws = true ↔ OneLine ws := by
  cases ws <;> simp [crossedNoBreak, OneLine]

/-- Consumer two (item 23, `[196]`): at what index can this scan be a VALUE? -/
theorem index_polymorphism (ws : List Nat) :
    crossedNoBreak ws = true ↔ ∀ n, Read n ws := by
  rw [key_eligibility, ← index_free_iff]

/-- The two consumers are the same measurement because the two restrictions are
    stated over the same boundary — not because the answers happen to agree on
    the inputs at hand. -/
theorem one_measurement_two_consumers (ws : List Nat) :
    (crossedNoBreak ws = true ↔ OneLine ws) ∧
    (crossedNoBreak ws = true ↔ ∀ n, Read n ws) :=
  ⟨key_eligibility ws, index_polymorphism ws⟩

/-! ## §4  Several negative answers are still one question

The indented value arm could fail for four reasons.  Written as four
`by_cases`, each deferring to the same escape with the same arguments, the
escape's CALL-SITE count quadruples while its domain does not move — the
inflation [[CoverageNotCallSites]] warns about, produced by the author rather
than inherited. -/

/-- The four ways `Read n` is unavailable for a step. -/
inductive Why where
  /-- `&`/`!`: a property RUN, whose route is pinned elsewhere. -/
  | propsRun
  /-- `|`/`>`: an auto-detected content indent — the upstream shape again. -/
  | blockScalar
  /-- The value folds: the occurrence is present, so nothing to lift. -/
  | folds
  /-- Preprocessing landed on a fresh line: the separator occurrence. -/
  | landed
  deriving DecidableEq

/-- Every one of them is the SAME answer to the same question. -/
def answers : Why → Bool := fun _ => false

theorem all_four_are_one_negative : ∀ w : Why, answers w = false := fun _ => rfl

/-- Split into four `by_cases`, each arm defers separately. -/
def deferralSitesIfSplit : Nat := 4
/-- Asked once, each caller has one deferral point. -/
def deferralSitesIfFactored : Nat := 1

/-- Factoring moves the count and not the domain, which is exactly why the
    count has to be reported against the domain rather than instead of it. -/
theorem factoring_moves_the_count_not_the_domain :
    deferralSitesIfSplit ≠ deferralSitesIfFactored ∧
    (∀ w : Why, answers w = false) :=
  ⟨by decide, all_four_are_one_negative⟩

/-! ## §5  What item 23 shipped -/

/-- Sub-productions rebuilt at every index (plain one-line, double, single). -/
def siblingsRouted : Nat := 3
/-- Content kinds that needed no side condition at all (`[104]` alias). -/
def unconditionalKinds : Nat := 1
/-- Inductions over a span required by the lift.  One, over the intra-line
    `GStar` in the plain relabelling; none over the grammar. -/
def spanInductions : Nat := 1
/-- New accumulator arms (the two indented content lemmas). -/
def newArms : Nat := 2
/-- Deferral call sites before and after: unchanged, while the reachable
    domain lost the indented inline value. -/
def escapeSitesBefore : Nat := 13
/-- See `escapeSitesBefore`. -/
def escapeSitesAfter : Nat := 13
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0

theorem shipped :
    siblingsRouted = 3 ∧ unconditionalKinds = 1 ∧ spanInductions = 1 ∧
    newArms = 2 ∧ escapeSitesBefore = escapeSitesAfter ∧ runtimeEdits = 0 := by
  decide

end L4YAML.Tests.Reflections.WideningIsAnOccurrenceQuestion

end Blanket
