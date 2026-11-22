/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 650 — a case that lands in the escape may be a DIFFERENT question, not a harder instance of yours

**The rule.**  When you ask a question of every case and route the negative
answers to one escape, check that each negative case is even an INSTANCE of
the question.  A case that is not — a step of another shape, a construct from
another production — has not answered "no"; it has failed to be asked.  Filing
it under the negative is not wrong, but it records the wrong obstruction, and
the wrong obstruction is what schedules the next item.

**Why it hides.**  The bundling is invisible from the escape, because the
escape's argument list is the same either way, and it is invisible from the
test suite, because the input is accepted either way.  It is visible in one
place only: the PROSE at the deferral site, which has to say why each family
is there.  When two families in that list have justifications of different
kinds — "this reading genuinely mentions the index" beside "this isn't a
reading" — the second is a different question wearing the first's clothes.

**Why it pays.**  The question you were not asking may have a much better
answer.  [[WideningIsAnOccurrenceQuestion]] says a widening costs whatever the
parameter's occurrences cost; the strongest possible answer is that there are
NO occurrences, and that is exactly what a freshly opened construct tends to
have — it has not yet reached the sub-production the parameter lives in.

**And the honest measure moves sideways.**  Splitting a negative into its own
positive arm keeps each caller at one escape, but the escape can still gain a
site elsewhere, and here it did (13 → 14).  What actually improved is
narrower and more useful: the residues that remain now CONVERGE on fewer
distinct causes (§4).  Counting inputs or call sites misses that; counting
causes is what tells you whether the next item is one item or three
([[CoverageNotCallSites]]).

Concretely (L4YAML): item 23 asked "does this content step read at every
index?" and recorded four negatives, the first being a property run
(`  - &a v`).  But `&` completes no value — it opens `[96] c-ns-properties`,
which the accumulator PARKS, and the pinned 0 was in the pending's route, one
step upstream of the reading.  Re-indexing that route needed no lift at all: a
fresh run is single-half, and `[96]`'s only occurrence of the index is the
separator inside its optional SECOND half.

§1 is the misfiled negative and what it costs.  §2 is the three-answer
refinement and why the escape count does not move at the caller.  §3 is the
occurrence structure of the construct that was never being asked.  §4 is the
convergence of causes.  §5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.DifferentQuestionNotAHarderCase

/-! ## §1  A negative answer that was never an instance

The accumulator sees one step at a time.  Some steps complete a VALUE; one
opens a DECORATION that awaits a value on a later step.  The question "does
this value read at every index?" applies only to the first kind. -/

/-- A content step, by what it does rather than by which character it was. -/
inductive Step where
  /-- A value; `folds` records that its reading crossed a line break. -/
  | value (folds : Bool)
  /-- A value whose own content indent is auto-detected (`|`, `>`). -/
  | blockScalar
  /-- `&`/`!`: not a value at all — a `[96]` run awaiting one. -/
  | decoration
  deriving DecidableEq

/-- The question's DOMAIN: the steps it is about. -/
def isValue : Step → Bool
  | .value _ => true
  | .blockScalar => true
  | .decoration => false

/-- The two-answer form: everything that is not a clean reading is "no". -/
def readsAtEvery : Step → Bool
  | .value folds => !folds
  | .blockScalar => false
  | .decoration => false

/-- Inside the domain, the two-answer form is right — which is why it survives
    review, and why the test suite cannot see the problem. -/
theorem sound_on_the_domain (s : Step) (h : isValue s = true) :
    readsAtEvery s = true ↔ (s = .value false) := by
  cases s with
  | value folds => cases folds <;> simp [readsAtEvery]
  | blockScalar => simp [readsAtEvery]
  | decoration => simp [isValue] at h

/-- Outside it, the "no" is not an answer: the step was never asked. -/
theorem the_misfiled_case :
    readsAtEvery .decoration = false ∧ isValue .decoration = false := ⟨rfl, rfl⟩

/-! ## §2  Three answers, and the caller still has one escape

Splitting the misfiled case out is not a new branch for the CALLER — it is a
third arm of the same disjunction, so each call site keeps exactly one route
to the escape.  What changes is the domain. -/

inductive Answer where
  /-- The value reads at every index: build it. -/
  | reads
  /-- Not a value: park the decoration at the index instead. -/
  | decorates
  /-- Genuinely unavailable. -/
  | unavailable
  deriving DecidableEq

def classify : Step → Answer
  | .value false => .reads
  | .value true => .unavailable
  | .blockScalar => .unavailable
  | .decoration => .decorates

/-- One escape before, one escape after: the refinement moves an input out of
    the escape's domain without adding a route into it. -/
def escapeRoutesPerCaller : Nat := 1

/-- The domain of the escape, as a predicate on steps. -/
def escaped (f : Step → Bool) : Step → Bool := fun s => !f s

theorem refinement_shrinks_the_domain :
    escaped readsAtEvery .decoration = true ∧
    (classify .decoration ≠ .unavailable) := ⟨rfl, by decide⟩

/-- …and leaves the genuine negatives exactly where they were. -/
theorem genuine_negatives_unmoved :
    classify (.value true) = .unavailable ∧ classify .blockScalar = .unavailable :=
  ⟨rfl, rfl⟩

/-! ## §3  The question that was never asked, and its best possible answer

`[96] c-ns-properties(n,c)` is `( tag | anchor ) ( s-separate(n,c) ( anchor |
tag ) )?`.  The index occurs in ONE place: the separator inside the optional
second half.  A freshly opened run has not got there. -/

/-- How a separator was built.  `inline` is `[66] s-separate-in-line` — whites
    only, no occurrence of the index; `lines w` crossed a break and landed at
    column `w`, which is where the index bites. -/
inductive SepKind where
  | inline
  | lines (w : Nat)
  deriving DecidableEq

/-- `s-separate(n,c)` as a fact about the index. -/
def Sep (n : Nat) : SepKind → Prop
  | .inline => True
  | .lines w => n ≤ w

/-- `[96]`, indexed by which halves are present and by how the internal
    separator (if any) was built. -/
inductive Props : Nat → Bool → Bool → Option SepKind → Prop where
  | anchor (n : Nat) : Props n true false none
  | tag (n : Nat) : Props n false true none
  | anchorThenTag (n : Nat) (k : SepKind) (h : Sep n k) : Props n true true (some k)
  | tagThenAnchor (n : Nat) (k : SepKind) (h : Sep n k) : Props n true true (some k)

/-- **The best possible answer to the occurrence question: no occurrence.**  A
    fresh run is single-half, so it reads at every index by construction — no
    lift, no side condition, not even a one-line hypothesis. -/
theorem fresh_run_reads_everywhere (n : Nat) : Props n true false none :=
  Props.anchor n

/-- The extension is the only place the index can bite, and the accumulator
    builds its separator from the preprocessing's residual WHITES — so it does
    not bite there either. -/
theorem extension_by_whites_reads_everywhere (n : Nat) :
    Props n true true (some .inline) :=
  Props.anchorThenTag n .inline True.intro

/-- And that is not vacuous: an extension across a BREAK does pin the index,
    which is what makes the whites-built separator the load-bearing fact. -/
theorem extension_across_a_break_pins :
    Props 0 true true (some (.lines 0)) ∧ ¬ Props 3 true true (some (.lines 0)) := by
  refine ⟨Props.anchorThenTag 0 (.lines 0) (Nat.le_refl 0), ?_⟩
  intro h
  cases h with
  | anchorThenTag _ hs => have hle : (3 : Nat) ≤ 0 := hs; omega
  | tagThenAnchor _ hs => have hle : (3 : Nat) ≤ 0 := hs; omega

/-! ## §4  What actually improved: the causes were re-attributed, and converged

The escape gained a site and the drop kept its four, so neither count is the
result.  Nor is the number of distinct causes, which is 2 both before and
after.  What improved is what each cause is TRUE of: three shapes were filed
under the route, and only one of them was actually the route's — the other two
belong to obstructions that already had other inhabitants, so a residue of
four shapes became three, and the two flow shapes now share one cause instead
of standing apart.  That is the fact that says the next item is one item. -/

inductive Cause where
  /-- The parked pending's route was typed at one index. -/
  | routePin
  /-- The flow resume's argument type is fixed at one index. -/
  | resumePin
  /-- `[170]`/`[174]` auto-detect a content indent the reading already pinned. -/
  | contentIndent
  /-- The step crossed a line break, where the index genuinely occurs. -/
  | crossedBreak
  deriving DecidableEq

/-- The four indented shapes that did not compose before this item. -/
inductive Shape where
  | propsValue      -- `  - &a v`
  | propsFlow       -- `  - &a [b]`
  | bareFlow        -- `  - [1]`
  | propsBlockScalar -- `  - &a |`
  deriving DecidableEq

def causeBefore : Shape → Cause
  | .propsValue => .routePin
  | .propsFlow => .routePin
  | .bareFlow => .resumePin
  | .propsBlockScalar => .routePin

def causeAfter : Shape → Cause
  | .propsValue => .routePin        -- …and it is gone: see `composed_now`
  | .propsFlow => .resumePin
  | .bareFlow => .resumePin
  | .propsBlockScalar => .contentIndent

/-- The one shape that leaves the residue entirely. -/
def composed_now : Shape → Bool
  | .propsValue => true
  | _ => false

/-- Two shapes that were blocked for different reasons are now blocked for the
    same one — which is what says the next item is ONE item. -/
theorem causes_converge :
    causeBefore .propsFlow ≠ causeBefore .bareFlow ∧
    causeAfter .propsFlow = causeAfter .bareFlow := ⟨by decide, rfl⟩

/-- …and the third was never the route's fault either; it is the same
    auto-detected content indent the undecorated block scalar has. -/
theorem block_scalar_reclassified :
    causeBefore .propsBlockScalar = .routePin ∧
    causeAfter .propsBlockScalar = .contentIndent := ⟨rfl, rfl⟩

/-! ## §5  What item 24 shipped -/

/-- Lifts the property route needed.  None: the run had no occurrence. -/
def liftsWritten : Nat := 0
/-- Carried indices added (`pendingProps`' route). -/
def pendingIndicesAdded : Nat := 1
/-- Construction sites of the re-indexed constructor. -/
def constructionSites : Nat := 8
/-- Elimination sites of it. -/
def eliminationSites : Nat := 4
/-- New readings, one production lower than item 23's (`[156]` not `[161]`). -/
def contentReadingsAdded : Nat := 3
/-- Escape call sites: UP by one, at the props consumer's nonzero side. -/
def escapeSitesBefore : Nat := 13
/-- See `escapeSitesBefore`. -/
def escapeSitesAfter : Nat := 14
/-- Opaque `scannerDrop` sites: unchanged, because the nonzero flow-open arm
    shares the deferred state's resume rather than writing its own. -/
def dropSitesBefore : Nat := 4
/-- See `dropSitesBefore`. -/
def dropSitesAfter : Nat := 4
/-- Indented shapes in the residue, before and after. -/
def shapesBefore : Nat := 4
/-- See `shapesBefore`. -/
def shapesAfter : Nat := 3
/-- Distinct causes among them: UNCHANGED, which is why the useful measure is
    what each cause is true of, not how many there are. -/
def causesBefore : Nat := 2
/-- See `causesBefore`. -/
def causesAfter : Nat := 2
/-- Shapes misattributed to the route before this item (`  - &a [b]` and
    `  - &a |`), now filed with the obstructions that really hold them. -/
def reattributed : Nat := 2
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0

theorem shipped :
    liftsWritten = 0 ∧ pendingIndicesAdded = 1 ∧ constructionSites = 8 ∧
    eliminationSites = 4 ∧ contentReadingsAdded = 3 ∧
    escapeSitesAfter = escapeSitesBefore + 1 ∧ dropSitesBefore = dropSitesAfter ∧
    shapesAfter < shapesBefore ∧ causesAfter = causesBefore ∧ reattributed = 2 ∧
    runtimeEdits = 0 := by
  decide

end L4YAML.Tests.Reflections.DifferentQuestionNotAHarderCase

end Blanket
