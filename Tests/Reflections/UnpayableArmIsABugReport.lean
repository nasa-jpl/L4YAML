/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 682 — an unpayable arm is a bug report

**The rule.**  A deferred arm has a fourth way out, and it is the one nobody
looks for: the arm is INHABITED, the specification has no derivation for it,
and therefore the MACHINE is wrong.  Reflection 661 named three exits —
derive the shape, refute it from what the machine did, or find the arm
describes a state never entered.  All three leave the runtime alone.  The
fourth changes it, and it is the only exit available when the arm's inputs
exist, reach the arm, and are accepted: no derivation can be written (the
grammar has no production), no refutation can be written (the scan really did
take that branch), and the arm is not vacuous (a three-line input reaches it).
What remains is that the accepter accepts something the grammar does not
generate — a soundness bug, reported by the proof rather than by a test.

**Why it stays hidden.**  The arm is only a bug report when it is LOCATED.
`∨ True` says "some blank line was not readable" and admits every diagnosis,
including "the proof is too weak"; the located form names the coordinate — `j`
spaces, then a tab, at column `j` — and that is simultaneously the missing
derivation, the input that exhibits it, and the condition a runtime check
would test.  §3 is the point: an unlocated arm is CONSISTENT with a correct
machine, so it cannot be a bug report; the located one is not.

**And the fix has a shape.**  Because the located arm is exactly the check's
firing condition, narrowing the runtime does not merely make the arm
unreachable — it makes the arm's own hypothesis contradictory, so the residue
DELETES rather than shrinking, and the disjunction goes with it (§4).  A
runtime check bolted on for other reasons would not do this; the check has to
be the arm read as a predicate.

**The instance** (item 62).  `[70] l-empty(n,c)` opens with `s-line-prefix`
or `[64] s-indent-lt(n)`, both beginning in `[63] s-indent`, which is spaces;
a tab is admitted only by `[69] s-flow-line-prefix(n)`'s trailing
`s-separate-in-line?`, i.e. only past the `n`th space.  A blank fold line with
fewer than `n` spaces and then a tab therefore has no reading — and both
pipelines scanned `k:⏎  - "a⏎<TAB>⏎    b"` clean.  Six items had carried the
arm as "a future runtime check refuses it".  The check is one conjunction, the
fold's own §6.1 gate read one line earlier, and with it
`foldQuotedNewlinesLoop_prod_at` loses its disjunction outright.

§1 the three exits of R661 and why each is unavailable here; §2 the fourth;
§3 unlocated vs located; §4 the narrowing empties the arm. -/

namespace L4YAML.Tests.Reflections.UnpayableArmIsABugReport

/-- A line's white run, as much of it as the question needs: how many spaces
    before the first tab, and whether a tab follows them at all. -/
structure Run where
  spaces : Nat
  tab : Bool
deriving Repr, DecidableEq

/-- §1 The specification: which runs the grammar reads at index `n`.
    `s-flow-line-prefix(n)` needs the `n` spaces first (then a tab is fine);
    `s-indent-lt(n)` needs a short run and NO tab. -/
def readable (n : Nat) (r : Run) : Bool :=
  (n ≤ r.spaces) || !r.tab

/-- The machine, before item 62: every all-white line folds. -/
def acceptsBefore (_n : Nat) (_r : Run) : Bool := true

/-- The machine, after: the fold stops where a tab precedes the floor. -/
def acceptsAfter (n : Nat) (r : Run) : Bool :=
  !(r.tab && decide (r.spaces < n))

/-- The witness the campaign actually ran: `<TAB>` on a blank line inside an
    entry whose content indent is 4. -/
def theInput : Run := ⟨0, true⟩

/-- §1a Exit one — DERIVE it — is unavailable: the grammar says no. -/
theorem cannot_derive : readable 4 theInput = false := rfl

/-- §1b Exit two — REFUTE it from what the machine did — is unavailable: the
    machine accepted. -/
theorem cannot_refute : acceptsBefore 4 theInput = true := rfl

/-- §1c Exit three — the arm is a state never entered — is unavailable: the
    arm's own condition holds of an input that exists. -/
theorem not_vacuous : theInput.tab = true ∧ theInput.spaces < 4 := by decide

/-- §2 So the fourth exit is forced, and it is a statement about the MACHINE:
    on this input, acceptance and readability disagree. -/
theorem the_machine_is_wrong :
    acceptsBefore 4 theInput = true ∧ readable 4 theInput = false := by decide

/-- The bug is not "the machine accepts too much" in general — everywhere
    else the two agree, so the delta is exactly the located arm. -/
theorem delta_is_the_arm (n : Nat) (r : Run) :
    (acceptsBefore n r = readable n r) ↔ ¬(r.tab = true ∧ r.spaces < n) := by
  cases hb : r.tab <;> simp [hb, acceptsBefore, readable] <;> omega

/-- §3 The same residue UNLOCATED — "some line in the run was not readable" —
    mentions no machine at all.  It is a statement about the GRAMMAR, true of
    a corrected scanner and a broken one alike, so nothing in it can be
    tested. -/
def someUnreadable (n : Nat) (rs : List Run) : Bool := rs.any (fun r => !readable n r)

theorem unlocated_mentions_no_machine (n : Nat) (rs : List Run) :
    someUnreadable n rs = rs.any (fun r => !readable n r) := rfl

/-- The located residue, by contrast, IS the check's firing condition — the
    same conjunction, read as a predicate on the state the scanner is in. -/
theorem located_is_the_check (n : Nat) (r : Run) :
    (r.tab = true ∧ r.spaces < n) ↔ acceptsAfter n r = false := by
  cases hb : r.tab <;> simp [hb, acceptsAfter] <;> omega

/-- …so it discriminates: the two machines differ exactly there. -/
theorem located_discriminates :
    acceptsBefore 4 theInput ≠ acceptsAfter 4 theInput := by decide

/-- §4 With the narrowing, the arm's hypothesis is contradictory on every
    input the machine still folds — the residue DELETES rather than
    shrinking, and the disjunction goes with it. -/
theorem arm_empties (n : Nat) (r : Run) (h : acceptsAfter n r = true) :
    readable n r = true := by
  cases hb : r.tab <;> simp [acceptsAfter, hb] at h <;> simp [readable, hb] <;> omega

/-- The narrowing moved only the arm: every readable run is accepted exactly
    as before. -/
theorem narrowing_keeps_the_readable (n : Nat) (r : Run) (h : readable n r = true) :
    acceptsAfter n r = acceptsBefore n r := by
  cases hb : r.tab <;> simp [readable, hb] at h <;>
    simp [acceptsAfter, acceptsBefore, hb] <;> omega

end L4YAML.Tests.Reflections.UnpayableArmIsABugReport

end Blanket
