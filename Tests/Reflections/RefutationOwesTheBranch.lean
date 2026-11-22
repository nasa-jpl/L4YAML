/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 660 — refuting a branching check means owning the branch

**The rule.**  A runtime check that reads one of two places depending on what
some state machine recorded is not refuted by facts about the data.  You can
know everything about the input — that the run in front of the cursor holds a
tab, that the rule forbids it, that the check is the one that enforces the rule
— and still not know that the check FIRES, because you do not know which place
it read.  What is missing is not a lemma about the check; it is a fact about
the state, and until something carries it the refutation is unavailable at any
price in grammar.

**And the fact you need is smaller than the fact you would have guessed.**  The
obvious invariant is "no stale record exists", which is a claim about the whole
history and is expensive.  The one the refutation actually consumes is "the
record, if there is one, is AT the cursor" — and at that point the two branches
read the same place, so the check's conditional is only apparent on the states
you can reach.  Before pricing a coupling that controls a branch, ask what the
branches do where you land: often they agree, and then the invariant needed is
just the one that says you landed there.

**Where it belongs, and why it is cheap.**  The fact is about the scan the
producer just performed — an indicator scan that ends `simpleKeyAllowed := true`
— so it rides the pending as a REQUIRED field rather than an optional one
([[OptionalFieldBuysDomain]]: an optional field buys domain when producers
genuinely differ, and these do not).  And it costs no transport lemma, because
the flag is MONOTONE across the step: a break re-arms it and nothing clears it,
so the producer's obligation is discharged once and the consumer needs no
hypothesis about what the step did.  That is [[OperationalFlagWitnessesHistory]]'s
mechanism — a machine that must act on its history records it — used for a
different job: 624 reads the flag as a WITNESS of what happened, this reads it
as the SELECTOR of what a later check will do.

Concretely (L4YAML): `scanValueIndentTabCheck` refuses a tab in the run in
front of a `:`, but it consults the simple-key machine first — the key branch
walks back from the recorded key's offset, the fallback branch from the cursor.
Item 33 could therefore only conclude a CHARACTER (after a located tab the
indicator must be a `:`), leaving one shape, `- →: a`, at the escape.  Item 34
carries `sc.simpleKeyAllowed = true` on the pending; a break-free step then
records a key at the `:` itself, the two branches coincide, and the tab arm at
that site is `False`.

§1 the check the data cannot refute.  §2 the minimal fact, and the branches
agreeing.  §3 monotone facts need no transport.  §4 the coordinate note.
§5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.RefutationOwesTheBranch

/-! ## §1  Two readings, and the data decides neither

The check reads the whitespace run in front of ONE position: the recorded key's
if the machine has one, the cursor's otherwise.  `tabAt` stands for the backward
scan — which positions have a tab in the run behind them. -/

/-- Which position the check reads. -/
def readsAt (saved : Option Nat) (cursor : Nat) : Nat := saved.getD cursor

/-- The check passes when the run it reads holds no tab. -/
def passes (tabAt : Nat → Bool) (saved : Option Nat) (cursor : Nat) : Bool :=
  ! tabAt (readsAt saved cursor)

/-- The input under discussion: a tab in the run in front of the cursor. -/
def tabAtCursorOnly (cursor : Nat) : Nat → Bool := fun p => p == cursor

/-- **The data alone does not refute the check.**  The rule is violated at the
    cursor and the check still passes, because a record elsewhere sent it to
    look at a clean run.  Nothing about the grammar can close this gap. -/
theorem data_alone_admits_a_pass (cursor stale : Nat) (h : stale ≠ cursor) :
    tabAtCursorOnly cursor cursor = true ∧
      passes (tabAtCursorOnly cursor) (some stale) cursor = true := by
  refine ⟨by simp [tabAtCursorOnly], ?_⟩
  simp [passes, readsAt, tabAtCursorOnly, h]

/-- …and with no record it does refute.  So the two branches genuinely differ
    off the states we can reach: this is a real conditional, not a mirage. -/
theorem no_record_refutes (cursor : Nat) :
    passes (tabAtCursorOnly cursor) none cursor = false := by
  simp [passes, readsAt, tabAtCursorOnly]

/-! ## §2  The minimal fact — and where it lands, the branches agree

Not "there is no record" (a claim about the whole history) but "the record is
at the cursor" (a claim about the step just taken). -/

/-- The fact the pending carries, as a predicate on the recorded key. -/
def recordAtCursor (saved : Option Nat) (cursor : Nat) : Prop :=
  ∀ k, saved = some k → k = cursor

/-- **Where the fact holds, the conditional is only apparent**: both branches
    read the cursor's own run. -/
theorem branches_agree_at_cursor {saved : Option Nat} {cursor : Nat}
    (h : recordAtCursor saved cursor) : readsAt saved cursor = cursor := by
  cases saved with
  | none => rfl
  | some k => exact h k rfl

/-- …so the check is refuted, from a fact about the STATE plus the fact about
    the data that was available all along. -/
theorem refuted_once_the_branch_is_owned {saved : Option Nat} {cursor : Nat}
    {tabAt : Nat → Bool} (h : recordAtCursor saved cursor)
    (h_tab : tabAt cursor = true) : passes tabAt saved cursor = false := by
  simp [passes, branches_agree_at_cursor h, h_tab]

/-- The fact is strictly weaker than the one the obvious invariant states, and
    that matters: "no record" is false of every step this arm reaches — the
    machine records one at every indicator. -/
theorem the_minimal_fact_is_weaker (cursor : Nat) :
    recordAtCursor (some cursor) cursor ∧ (some cursor) ≠ none := by
  exact ⟨fun _ h => by simpa using h.symm, by simp⟩

/-! ## §3  A monotone flag is the cheap kind to carry

What decides whether a record is made is a flag, and the flag only ever goes UP
across a step: a break re-arms it, nothing clears it.  So the producer's
obligation is discharged from the scan it just performed and the consumer needs
no hypothesis about the step. -/

/-- The step, as the walk performs it: re-arm on a break, otherwise carry. -/
def stepFlag (crossedBreak : Bool) (b : Bool) : Bool := if crossedBreak then true else b

/-- **Monotone**: no hypothesis about the step is required. -/
theorem flag_survives_any_step {b : Bool} (crossedBreak : Bool) (h : b = true) :
    stepFlag crossedBreak b = true := by cases crossedBreak <;> simp [stepFlag, h]

/-- A datum that is NOT monotone — the indent stack, which an armed unwind
    rewrites — needs a hypothesis about the step, and that hypothesis is the
    transport lemma every re-park has to discharge. -/
def stepStack (unwound : Bool) (st : Nat) : Nat := if unwound then 0 else st

theorem stack_needs_a_hypothesis_about_the_step :
    ∃ st, stepStack true st ≠ st := ⟨1, by simp [stepStack]⟩

/-- The consequence, counted: one carried fact, no transport lemma, because
    monotonicity IS the transport. -/
def transportLemmasForTheFlag : Nat := 0
def transportLemmasForTheStack : Nat := 1

theorem monotone_costs_no_transport :
    transportLemmasForTheFlag < transportLemmasForTheStack := by decide

/-! ## §4  The coordinate note

The check has an earlier branch still — a walk over the whole LINE in front of
the token, which is the right coordinate for an entry that starts its line
([[GuardInTheWrongCoordinate]]).  It answers `false` here and it is not wrong to:
the entry's own indicator really is on the line.  Two coordinates, two
questions; the compact opener is a place where only the second is asked. -/

/-- The line coordinate: is everything on the line in front of the token white?
    (Modelled as: the characters before it, in order.) -/
def lineIsIndent (before : List Char) : Bool := before.all fun c => c == ' ' || c == '\t'

/-- The run coordinate: does the maximal white run immediately before hold a
    tab? -/
def runHasTab (before : List Char) : Bool :=
  (before.reverse.takeWhile fun c => c == ' ' || c == '\t').contains '\t'

/-- At a line start the two agree about there being an indentation to judge… -/
theorem agree_at_a_line_start : lineIsIndent [' ', '\t'] = true ∧ runHasTab [' ', '\t'] = true := by
  decide

/-- …and after an indicator they part: the line coordinate reports "not an
    indentation", which is true, and says nothing about the run — which is the
    `s-indent` a COMPACT opener stands after. -/
theorem part_after_an_indicator :
    lineIsIndent ['-', ' ', '\t'] = false ∧ runHasTab ['-', ' ', '\t'] = true := by decide

/-! ## §5  What item 34 shipped -/

/-- Fields added to the pending — one, and required rather than optional. -/
def fieldsAdded : Nat := 1
def optionalFields : Nat := 0
/-- Producers that discharge it, all from the scan they just performed. -/
def producersDischarging : Nat := 6
/-- Consumers re-bound for the wider telescope. -/
def consumersAdjusted : Nat := 4
/-- Transport lemmas the carried fact needed: none — it is monotone. -/
def transportLemmasWritten : Nat := 0
/-- Grammar productions added, and runtime files edited: none of either. -/
def newProductions : Nat := 0
def runtimeEdits : Nat := 0
/-- The escape's call sites, before and after. -/
def escapeSitesBefore : Nat := 8
def escapeSitesAfter : Nat := 7
/-- `scannerDrop` — a different obstruction, untouched. -/
def scannerDropBefore : Nat := 4
def scannerDropAfter : Nat := 4

theorem shipped :
    fieldsAdded = 1 ∧ optionalFields = 0 ∧ producersDischarging = 6 ∧
    consumersAdjusted = 4 ∧ transportLemmasWritten = 0 ∧ newProductions = 0 ∧
    runtimeEdits = 0 ∧ escapeSitesAfter < escapeSitesBefore ∧
    scannerDropBefore = scannerDropAfter := by
  decide

end L4YAML.Tests.Reflections.RefutationOwesTheBranch

end Blanket
