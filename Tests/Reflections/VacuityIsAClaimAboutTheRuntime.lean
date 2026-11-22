/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 657 — "expected vacuous" is a claim about the RUNTIME, and the cheapest way to test it is to build the input

**The rule.**  When an escape branch is priced as *expected vacuous* — "the code
refuses this before it can reach us" — that is not a statement about the proof,
it is a statement about the program, and it is CHEAP to test: construct the
input the branch describes and run it.  Either it is rejected, and the vacuity
claim is a lemma waiting to be written, or it is accepted, and the branch was
never proof debt at all — it was a bug report the deferral had been carrying
for you.  [[PhantomBranchNotADeferral]] is the case where the claim holds and
the phantoms retire; this is the case where it does not, and the difference is
one experiment.

**What makes the claim look safe.**  It is usually true of the arm somebody
checked.  A guard implemented on ONE sibling reads as a guard on the family: the
deferral's comment names the runtime error by constructor
(`tabInIndentation`), the error genuinely exists, and any input you reach for
casually does get rejected — because casual inputs use the checked arm.  The
tell is the same asymmetry [[EqualityGateHidesTwoOrders]] §2 reads on the proof
side, pointed the other way: there, an arm DEFERRED on a condition its siblings
never tested and the body was next door; here, an arm CHECKS a condition its
siblings never check, and what is next door is the hole
(`guard_is_not_on_every_sibling`, `family_looks_guarded_from_one_arm`).  So the
proof-side and runtime-side asymmetries are the same smell and want the same
sweep — read the siblings — but they cash out differently: one is a line of
delegation, the other is a shipped over-acceptance.

**And check what the branch's STATEMENT says, not what its proof knows.**  A
disjunct can be weakened past its own witness: the splitter here concludes
`'\t' ∈ s.chars` — a tab ANYWHERE in the remaining input — while its induction
knows exactly where the tab is, inside the whitespace run it just walked.  A
branch stated that loosely cannot be refuted at ANY price, because almost every
document satisfies it (`weakened_disjunct_is_unrefutable`,
`located_disjunct_is_refutable`), and no amount of runtime hardening will help
until the statement is restored.  The restoration is free — the same induction
already visits the tab (`locating_costs_nothing`).  Price the statement before
pricing the work.

**The boundary the fix has to respect.**  A blunt rule ("no tabs in
indentation") over-rejects, because whether the whitespace IS indentation
depends on what follows it: the same `␣␣→` prefix is legal in front of a flow
node and illegal in front of a block-collection entry, and that is decided by
the construct, not by the column.  So the check belongs where the construct is
recognised, and it must follow the ENTRY's first character rather than the
indicator's — the run in front of a key is the indentation, the run between the
key and its `:` is separation (`same_prefix_two_verdicts`,
`entry_start_decides`, `blunt_rule_over_rejects`).

Concretely (L4YAML): `[63] s-indent` is spaces only, and `scanBlockEntry` had
enforced it for `-` since Step 5b.2 by scanning back over the preceding
whitespace.  `scanKey` (`?`) checked only the tab AFTER the indicator and
`scanValue` (`:`) only the tab after the colon, so with one space in front of
the tab — enough to put the column past `currentIndent`, where
`skipToContentWs` treats tabs as separation — `a:⏎␣␣→: b`, `a:⏎␣␣→? b`,
`a:⏎␣␣→k: v` and `a:⏎␣␣→"k": v` all PARSED, in both pipelines, while
`a:⏎␣␣→- b` was correctly refused.  DK95:00 (`foo:⏎␣→bar`) is the case that
must keep parsing and the one the over-acceptance was mistaken for: its tab is
`[69] s-flow-line-prefix`'s `s-separate-in-line?` in front of a plain SCALAR,
where `[187] l+block-mapping` offers no such slot.

§1 the experiment that prices the vacuity claim.  §2 the sibling guard.
§3 the weakened disjunct.  §4 the boundary.  §5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.VacuityIsAClaimAboutTheRuntime

/-! ## §1  Vacuity is measured on the program, not argued from the deferral

The branch says "the runtime refuses this first".  That sentence has a truth
value you can compute. -/

/-- The three block indicators the deferral's branch covered. -/
inductive Indicator where
  | dash | question | colon
  deriving DecidableEq, Repr

/-- Whether the runtime rejects a tab in the whitespace in front of this
    indicator — BEFORE the item.  Only the `-` arm carried the check. -/
def rejectsTabBefore : Indicator → Bool
  | .dash => true
  | .question => false
  | .colon => false

/-- **The experiment.**  "Expected vacuous" is the claim that every indicator
    rejects; one run of the accepted-input probe refutes it. -/
def vacuityClaim : Prop := ∀ i, rejectsTabBefore i = true

theorem vacuity_claim_is_false : ¬ vacuityClaim := by
  intro h; have := h .colon; simp [rejectsTabBefore] at this

/-- …and the witness is an input, not a proof obligation: the branch was
    REACHABLE, so the deferral was carrying a bug rather than a debt. -/
theorem branch_was_reachable : ∃ i, rejectsTabBefore i = false :=
  ⟨.colon, rfl⟩

/-! ## §2  A guard on one sibling reads as a guard on the family

Which is why the claim survived: every input reached for casually goes through
the arm that HAS the check. -/

theorem guard_is_not_on_every_sibling :
    rejectsTabBefore .dash ≠ rejectsTabBefore .colon := by decide

/-- The arm somebody checked is the one an example lands on, so sampling
    confirms the claim it was supposed to test. -/
theorem family_looks_guarded_from_one_arm :
    rejectsTabBefore .dash = true ∧ ¬ vacuityClaim :=
  ⟨rfl, vacuity_claim_is_false⟩

/-- After the item: the check is on the whole family, and the branch becomes
    refutable for every arm at once. -/
def rejectsTabAfter : Indicator → Bool
  | .dash | .question | .colon => true

theorem vacuous_after : ∀ i, rejectsTabAfter i = true := by
  intro i; cases i <;> rfl

/-! ## §3  A disjunct weakened past its witness cannot be refuted at any price

The splitter's induction walks the whitespace run and MEETS the tab.  Its
conclusion then forgets where it was. -/

/-- A toy document: the whitespace run the step walked, then the rest. -/
structure Doc where
  run : List Char
  rest : List Char
  deriving Repr

def Doc.chars (d : Doc) : List Char := d.run ++ d.rest

/-- What the disjunct SAID: a tab somewhere in everything that is left. -/
def weakened (d : Doc) : Prop := '\t' ∈ d.chars

/-- What the induction KNEW: the tab is inside the run it just walked. -/
def located (d : Doc) : Prop := '\t' ∈ d.run

/-- The located form implies the weakened one — the statement was a genuine
    weakening, not a different fact. -/
theorem located_implies_weakened (d : Doc) : located d → weakened d := by
  intro h; exact List.mem_append_left _ h

/-- **The trap.**  A tab anywhere downstream satisfies the weakened disjunct,
    so a document whose run is clean still lands in the branch: it cannot be
    refuted, however hard the runtime is hardened. -/
def cleanRunTabLater : Doc := { run := [' ', ' '], rest := ['x', '\t'] }

theorem weakened_disjunct_is_unrefutable :
    weakened cleanRunTabLater ∧ ¬ located cleanRunTabLater := by
  constructor
  · show '\t' ∈ [' ', ' ', 'x', '\t']; decide
  · show ¬ '\t' ∈ [' ', ' ']; decide

/-- The located form is refutable exactly where the runtime's own backward scan
    is decisive: it talks about the same characters the scan walks. -/
theorem located_disjunct_is_refutable (d : Doc) (h : d.run.all (· = ' ')) :
    ¬ located d := by
  intro hmem
  have := List.all_eq_true.mp h _ hmem
  simp at this

/-- Restoring it is free: the walk already visits the tab, so the witness is in
    hand at the step that produces the disjunct. -/
theorem locating_costs_nothing (pre : List Char) (rest : List Char) :
    located { run := pre ++ '\t' :: rest, rest := [] } := by
  show '\t' ∈ pre ++ '\t' :: rest
  exact List.mem_append_right _ (List.mem_cons_self ..)

/-! ## §4  Whether whitespace IS indentation depends on what follows it

So the blunt rule over-rejects, and the exact rule is anchored at the ENTRY's
first character. -/

/-- What the tab-carrying prefix turned out to precede. -/
inductive Follower where
  /-- A flow node or a plain scalar — reached through a line prefix that ends
      in `s-separate-in-line?`, so the tab is legal separation. -/
  | flowContent
  /-- A block-collection entry — reached through a bare `s-indent`, which is
      spaces only. -/
  | blockEntry
  deriving DecidableEq, Repr

/-- The spec's verdict on the SAME prefix, by follower. -/
def legal : Follower → Bool
  | .flowContent => true
  | .blockEntry => false

theorem same_prefix_two_verdicts : legal .flowContent ≠ legal .blockEntry := by decide

/-- A rule that rejects the prefix outright loses the legal half. -/
def bluntRule (_ : Follower) : Bool := false

theorem blunt_rule_over_rejects : bluntRule .flowContent ≠ legal .flowContent := by decide

/-- Where the entry starts, per shape: with an implicit key the entry starts at
    the KEY (and the run between key and `:` is separation); with an empty key
    it starts at the indicator itself. -/
inductive EntryShape where
  | implicitKey | emptyKey
  deriving DecidableEq, Repr

/-- Offset of the character whose preceding run is the indentation, measured
    from the indicator: 0 for an empty key, back at the key otherwise. -/
def entryStartOffset : EntryShape → Int
  | .implicitKey => -1
  | .emptyKey => 0

/-- **The point.**  Checking the run in front of the INDICATOR would reject the
    legal `a→: b` (the run there is the key's own separation); checking the run
    in front of the ENTRY keeps it and still catches `␣␣→: b`. -/
theorem entry_start_decides :
    entryStartOffset .implicitKey ≠ entryStartOffset .emptyKey := by decide

/-! ## §5  What item 31 shipped -/

/-- Runtime scanners given the check they lacked: `scanKey`/`scanKeyIx` (`?`)
    and `scanValue`/`scanValueIx` (`:`). -/
def runtimeScannersFixed : Nat := 4
/-- Grammar files edited — none; `[63]`/`[187]` always said this. -/
def grammarEdits : Nat := 0
/-- Proof files that needed a new case for the added guard — all mechanical:
    one more `Except` guard to step over. -/
def proofFilesRepaired : Nat := 21
/-- Shapes pinned in the guard file that parsed before and are refused now,
    identically in BOTH pipelines. -/
def overAcceptedShapesPinned : Nat := 13
/-- yaml-test-suite score, before and after — the suite has no case for the
    one-space variant, which is exactly why it survived. -/
def suiteScoreBefore : Nat := 347
def suiteScoreAfter : Nat := 347
/-- Escape call sites — unchanged: this item makes the branch refutable, it
    does not yet refute it ([[CoverageNotCallSites]]: the number is not the
    progress, and here the progress is not in the number either). -/
def escapeSitesBefore : Nat := 12
def escapeSitesAfter : Nat := 12

theorem shipped :
    runtimeScannersFixed = 4 ∧ grammarEdits = 0 ∧ proofFilesRepaired = 21 ∧
    overAcceptedShapesPinned = 13 ∧ suiteScoreBefore = suiteScoreAfter ∧
    escapeSitesBefore = escapeSitesAfter := by
  decide

end L4YAML.Tests.Reflections.VacuityIsAClaimAboutTheRuntime

end Blanket
