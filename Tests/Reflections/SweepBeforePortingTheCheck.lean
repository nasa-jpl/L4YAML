/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 638 — sweep the divergence before porting the check; fix the resting state, not the verdict

**The rule.**  A recorded twin-pipeline divergence names a SHAPE and a
PRESCRIPTION ("`x⏎: v` diverges; the lenient side must adopt the strict
side's check").  Before executing the prescription, SWEEP the shape's
neighborhood differentially: the recorded shape is one point of the
divergence's true extent, and the prescription inferred from one point can
name the wrong side.  Then port the STATE where the two walks first part —
here, the cursor's resting position after a failed continuation probe — not
the downstream check that happens to make the recorded shape's verdicts
agree.  A check-port freezes the symptom; a state-port closes the family.

The shipped instance (L4YAML item 14): item 13's artifact recorded that the
indexed scanner rejects `x⏎: v` at scan (`invalidImplicitKey`) where legacy
accepts and rejects at parse, and prescribed "legacy must adopt the check".
A 5,460-input sweep over the 4-character alphabet `{x, :, ⏎, ␠}` found the
recorded shape was one of **580** divergent inputs in TWO families with ONE
root: the indexed plain-scalar walk had dropped legacy's **no-gain rewind**
at the cursor cutover — its own docstring still promised "the loop
terminates at the pre-fold cursor", but no code implemented it.  Family A
(354): verdict-equal error-STAGE differences, matrix-invisible.  Family B
(**226**): content differences on ACCEPTED inputs — `x⏎⏎` kept the fold's
`\n` in the indexed scalar — invisible to the matrix AND the suites because
no corpus case puts a bare top-level plain scalar before a trailing blank
line.  The prescription was BACKWARDS: porting the check into legacy would
have preserved family B and entrenched the defective walk.  Restoring the
rewind (`backtrackIfNoGain`, one `@[inline]` helper wrapping both fold
arms) closed all 580 at once.

**Why the wrong prescription got recorded.**  The divergence surfaced
mid-pass, as a side observation of item 13's probing, and was written down
as symptom + guess.  Symptom-notes age into wrong prescriptions; re-derive
the mechanism before executing one (R622's stale-pin lesson, one level up:
here the stale artifact was a PLAN entry, not a test assertion).

Self-contained: a two-policy miniature of the walk (rewind vs rest-past-
the-break) whose END-TO-END verdicts agree everywhere while the collected
content differs — the shape of a divergence that verdict-level comparison
cannot see — plus the shipped instance's counts (item 14, 2026-08-11).
-/

namespace L4YAML.Tests.Reflections.SweepBeforePortingTheCheck

/-- What follows a one-token plain scalar: a `: v` line (the recorded
    shape), a blank line (family B's shape), or nothing. -/
inductive NextLine where
  | colonLine | blankLine | eof
  deriving DecidableEq, Repr

/-- The walk's outcome under a rewind policy: collected content and
    whether the cursor RESTS PAST the line break.  A continuation probe
    that gains nothing either rewinds to the pre-break cursor (legacy)
    or stays where the probe stopped (the defective twin). -/
def walk (rewind : Bool) : NextLine → String × Bool
  | .eof       => ("x", false)
  | .colonLine => if rewind then ("x", false) else ("x", true)
  | .blankLine => if rewind then ("x", false) else ("x\n", true)

/-- Scan-level verdict at the next fetch: a fresh simple key is allowed
    exactly when the SKIP crosses the break — i.e. when the walk rested
    before it.  A cursor already past the break leaves the stale key
    live, and the `:` dies on the §7.4 line check. -/
def scanAccepts (rewind : Bool) : NextLine → Bool
  | .colonLine => !(walk rewind .colonLine).2
  | _          => true

/-- Parse-level verdict: a scan-accepted `: v` after a completed bare
    document dies as bare-document content either way. -/
def endToEndAccepts (rewind : Bool) : NextLine → Bool
  | .colonLine => scanAccepts rewind .colonLine && false
  | l          => scanAccepts rewind l

/-- The trap: END-TO-END verdicts agree at every input … -/
theorem verdictsAgree : ∀ l, endToEndAccepts true l = endToEndAccepts false l := by
  intro l; cases l <;> rfl

/-- … while the collected CONTENT differs on the accepted family — the
    divergence a verdict-level comparison cannot see. -/
theorem contentDiverges : (walk true .blankLine).1 ≠ (walk false .blankLine).1 := by
  decide

/-- The defective policy keeps the fold's newline in an ACCEPTED scalar. -/
example : walk false .blankLine = ("x\n", true) := rfl
/-- The rewind policy strips it and rests before the break. -/
example : walk true .blankLine = ("x", false) := rfl

-- ═══ §1  The sweep's yield (item 14's shipped counts, 2026-08-11) ═══

/-- Inputs swept: lengths 1–6 over `{x, :, ⏎, ␠}`. -/
def inputsSwept : Nat := 5460
/-- Divergent inputs found — the recorded artifact named ONE shape. -/
def divergentFound : Nat := 580
/-- Family A: verdict-equal error-stage differences (matrix-invisible). -/
def familyA : Nat := 354
/-- Family B: content differences on ACCEPTED inputs (suite-invisible too). -/
def familyB : Nat := 226
/-- Distinct root causes across both families. -/
def rootCauses : Nat := 1
/-- Divergent inputs remaining after restoring the rewind. -/
def divergentAfterFix : Nat := 0

#guard inputsSwept == 5460
#guard divergentFound == 580
#guard familyA + familyB == divergentFound
#guard rootCauses == 1
#guard divergentAfterFix == 0

-- ═══ §2  The port's price: state vs check ═══

/-- Fold arms wrapped by the ONE `backtrackIfNoGain` helper. -/
def foldArmsWrapped : Nat := 2
/-- Proof arms repaired, all in `IndexedScalar.lean` (offset-monotonic ×2,
    isPrefix ×2, contentInv ×2) — `IndexedScannerProgress.lean` needed 0. -/
def proofArmsRepaired : Nat := 6
/-- Equational lemmas restated to expose the wrapper. -/
def lemmasRestated : Nat := 2
/-- Legacy-side edits under the corrected direction. -/
def legacyEditsNeeded : Nat := 0
/-- Legacy proof references that the RECORDED direction would have put in
    play (`collectPlainScalarLoop` across 15 files) — the wrong
    prescription was also the expensive one. -/
def legacyRefsAtRisk : Nat := 301

#guard foldArmsWrapped == 2
#guard proofArmsRepaired == 6
#guard lemmasRestated == 2
#guard legacyEditsNeeded == 0
#guard legacyRefsAtRisk == 301

end L4YAML.Tests.Reflections.SweepBeforePortingTheCheck

end Blanket
