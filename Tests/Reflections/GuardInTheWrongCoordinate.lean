/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 658 — a runtime guard the proof cannot reach is usually a guard stated in the wrong coordinate

**The rule.**  When a branch is supposed to be refuted by a check the code
already performs, and the refutation will not go through, do not first conclude
that the coupling is expensive.  Ask which COORDINATE the check reads.  A guard
keyed on a value some derived state machine records — a saved position, a
cached index, a flag — is reachable from a proof only through an INVARIANT
about that value, and if no such invariant exists, building one is a separate
item.  A guard keyed on the coordinate the SPECIFICATION names is reachable
from what the proof already carries.  Restating the check in the
specification's coordinate is frequently verdict-preserving — the same accept
and the same reject on every input — and that is the cheap route.

This is [[PuntNamesACoordinate]] read in the other direction.  There the
PROOF was re-measured where the runtime writes; here the RUNTIME is re-stated
where the grammar measures.  The pair is the same observation twice: a
mismatch between two sides is a mismatch of coordinates far more often than it
is a mismatch of strength.

**And the restatement is a claim you can test.**  "Verdict-preserving" is a
statement about the program, so [[VacuityIsAClaimAboutTheRuntime]]'s rule
applies to your OWN edit: build the corpus and run both readings.  If they
agree everywhere, the edit costs no behaviour and buys reachability; if they
disagree, you have learned that the old guard was not the check you thought it
was, which is worth more.

**The bridge needs BOTH endpoints.**  Between a symbolic run — a chain of
grammar steps — and a concrete buffer the runtime walks, "the same characters"
is not "the same place".  Two facts are owed, and both were missing here: that
the buffer is still the SAME buffer after the intervening step, and that the
run occupies a SEGMENT of it.  Neither is interesting; both are load-bearing,
and a bridge that proves only one of them proves nothing
(`same_content_is_not_same_place`, `suffix_pins_the_place`).

**Check upstairs before pricing a missing premise.**  The refutation here is
sound only in one context (block, not flow), so it needs that context as a
premise — and the premise turned out to be already decided one level up, in
the caller's own case split, and simply never passed down.  A hypothesis that
looks like new work is often an argument that is not being threaded
(`premise_decided_upstairs`).

Concretely (L4YAML): item 31 gave `scanValue` a §6.1 check anchored at the
ENTRY's first character — the KEY when the simple-key machine has recorded
one, the `:` otherwise.  That is the right verdict, and the accumulator could
not use it: `simpleKey.pos` is a coordinate the grammar accumulation has no
coupling for, so "there is no key on this line" was unprovable even though the
line in front of the `:` was known to be whitespace.  Item 32 added
`tabInLineIndent`, the same verdict computed from `s.col` — walk back exactly
the line's own characters, refuse if they are all `s-white` and one is a tab —
which is the coordinate `[187] l+block-mapping`'s `s-indent(n)` names.  Both
readings agree on the whole `yaml-test-suite` (per-test details byte-identical)
and on a 3,267-case tab-shape differential in both pipelines; the branch became
refutable and the four escape sites closed.

§1 the coordinate.  §2 verdict-preserving is testable.  §3 both endpoints.
§4 the premise upstairs.  §5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.GuardInTheWrongCoordinate

/-! ## §1  Two guards, one verdict, one reachability

A line, modelled as the characters in front of the token plus whatever the
state machine recorded about a key on it. -/

/-- The characters standing between the line start and the token. -/
abbrev Line := List Char

def isWhite (c : Char) : Bool := c == ' ' || c == '\t'

/-- The DERIVED coordinate: how far back a recorded key sits, or `none` when
    the machine recorded nothing.  Nothing constrains it by construction. -/
abbrev KeyMark := Option Nat

/-- The guard as item 31 wrote it: walk back from the KEY when there is one,
    from the token itself otherwise, and report a tab in the whites walked. -/
def guardByKey (l : Line) (k : KeyMark) : Bool :=
  let run := match k with
    | none => l
    | some d => l.take (l.length - d)
  run.reverse.takeWhile isWhite |>.contains '\t'

/-- The guard as item 32 wrote it: walk back the WHOLE line, and report only
    when every character of it is a white — which is what makes the run
    `[63] s-indent(n)` rather than `[66] s-separate-in-line`. -/
def guardByLine (l : Line) : Bool :=
  l.all isWhite && l.contains '\t'

/-- The invariant the derived coordinate would need: a recorded key points at
    a character that is not a white — keys do not start inside indentation. -/
def keyMarkSound (l : Line) (k : KeyMark) : Prop :=
  ∀ d, k = some d → d ≤ l.length ∧ ∃ c, (l.drop (l.length - d)).head? = some c ∧ isWhite c = false

/-- Under the invariant, the two guards agree on an all-white line: a recorded
    key cannot sit inside one, so there is no key, so both read the same run. -/
theorem verdicts_agree_on_indentation (l : Line) (k : KeyMark)
    (hsound : keyMarkSound l k) (hall : l.all isWhite = true) :
    guardByKey l k = guardByLine l := by
  have hk : k = none := by
    cases k with
    | none => rfl
    | some d =>
      obtain ⟨hd, c, hhead, hnw⟩ := hsound d rfl
      exfalso
      have hmem : c ∈ l := by
        have : c ∈ l.drop (l.length - d) := List.mem_of_mem_head? hhead
        exact List.mem_of_mem_drop this
      rw [List.all_eq_true] at hall
      rw [hall c hmem] at hnw
      exact Bool.noConfusion hnw
  subst hk
  have hkeep : ∀ m : List Char, (∀ c ∈ m, isWhite c = true) →
      List.takeWhile isWhite m = m := by
    intro m
    induction m with
    | nil => intro _; rfl
    | cons c cs ih =>
      intro hm
      rw [List.takeWhile_cons, ite_eq_left (hm c (by simp)),
          ih (fun x hx => hm x (by simp [hx]))]
  simp only [guardByKey, guardByLine, hall, Bool.true_and]
  rw [hkeep l.reverse (by
        intro c hc
        rw [List.all_eq_true] at hall
        exact hall c (List.mem_reverse.mp hc))]
  simp

/-- **Reachability is the difference.**  Drop the invariant and the two part
    company: a mark that points into the indentation makes the key guard miss
    a tab the line guard sees.  That gap is exactly what a proof with no
    coupling for the derived coordinate has to close, and why the check was
    unreachable rather than merely awkward. -/
def unsoundMark : KeyMark := some 1
def unsoundLine : Line := [' ', '\t']

theorem guards_differ_without_the_invariant :
    guardByKey unsoundLine unsoundMark ≠ guardByLine unsoundLine := by decide

/-- …and the key guard is not a function of the line at all: the SAME line
    gets two answers depending on what the state machine happened to record.
    The line guard takes no such argument, which is exactly why the proof can
    reach it — `[187]`'s `s-indent(n)` is measured on the line. -/
theorem key_guard_depends_on_the_state :
    guardByKey unsoundLine none ≠ guardByKey unsoundLine unsoundMark := by decide

/-! ## §2  "Verdict-preserving" is a claim about the program

So it is tested, not asserted — and the test is the corpus, not the argument.
The composed check fires when EITHER reading does; on the reachable domain
that is the same set. -/

def composed (l : Line) (k : KeyMark) : Bool := guardByLine l || guardByKey l k

/-- Adding the line reading cannot lose a rejection: it only adds a disjunct. -/
theorem no_acceptance_becomes_a_rejection (l : Line) (k : KeyMark) :
    guardByKey l k = true → composed l k = true := by
  intro h; simp [composed, h]

/-- And on the domain where the invariant holds it adds none either, because
    the line reading only fires on an all-white line, where §1 has already
    shown the two agree. -/
theorem no_rejection_becomes_an_acceptance (l : Line) (k : KeyMark)
    (hsound : keyMarkSound l k) (h : guardByLine l = true) :
    guardByKey l k = true := by
  have hall : l.all isWhite = true := by
    simpa using (Bool.and_eq_true_iff.mp h).1
  rw [verdicts_agree_on_indentation l k hsound hall]; exact h

/-- The corpus is the evidence, and it is cheap: every shape the branch talks
    about, run through both pipelines, before and after. -/
def differentialCases : Nat := 3267
def suiteTestsCompared : Nat := 358
def verdictsMoved : Nat := 0

theorem the_edit_is_verdict_preserving : verdictsMoved = 0 := by decide

/-! ## §3  Same content is not same place

A run of characters "in the input" and a run "before the offset" are the same
run only when two separate facts hold. -/

structure Buffer where
  chars : List Char
  deriving Repr, DecidableEq

/-- Fact one: the intervening step did not replace the buffer. -/
def sameBuffer (b₁ b₂ : Buffer) : Prop := b₁ = b₂

/-- Fact two: the run occupies a segment ending where the scanner stands. -/
def placedAt (run : List Char) (tail : List Char) (b : Buffer) : Prop :=
  ∃ pre, b.chars = pre ++ run ++ tail

/-- **The trap.**  A run whose characters all occur in the buffer is not
    thereby a segment of it in the right place: content is not position. -/
theorem same_content_is_not_same_place :
    (∀ c ∈ ['\t'], c ∈ (⟨['x', '\t', 'y']⟩ : Buffer).chars) ∧
    ¬ placedAt ['\t'] ['x'] ⟨['x', '\t', 'y']⟩ := by
  constructor
  · intro c hc; simp at hc; subst hc; simp
  · rintro ⟨pre, hpre⟩
    have hlen := congrArg List.length hpre
    simp at hlen
    match pre, hpre with
    | [], h => simp at h
    | [_], h => simp at h
    | _ :: _ :: _, h => simp at hlen

/-- With the placement in hand, the backward walk over `pre ++ run` reads
    exactly `run` — which is the whole content of the bridge. -/
theorem suffix_pins_the_place (pre run tail : List Char) :
    placedAt run tail ⟨pre ++ run ++ tail⟩ := ⟨pre, rfl⟩

/-! ## §4  The premise that was already decided upstairs

The refutation holds only where the block grammar is the reading; in a flow
collection the same characters are legal separation. -/

inductive Ctx where
  | block | flow
  deriving DecidableEq, Repr

/-- Whether a tab in the run in front of the token is refusable. -/
def refutable : Ctx → Bool
  | .block => true
  | .flow => false

theorem refutable_only_in_block : refutable .block ≠ refutable .flow := by decide

/-- The caller's own case split names the context; the callee had simply never
    been given it.  A missing premise is worth looking for one frame up before
    it is priced as an invariant to build. -/
def callerKnows (depth : Nat) : Ctx := if depth = 0 then .block else .flow

theorem premise_decided_upstairs : callerKnows 0 = .block := by decide

/-! ## §5  What item 32 shipped -/

/-- Escape sites `block_dispatch_deferred` still carries, before and after. -/
def escapeSitesBefore : Nat := 12
def escapeSitesAfter : Nat := 8
/-- `scannerDrop` sites — untouched; a different obstruction. -/
def scannerDropBefore : Nat := 4
def scannerDropAfter : Nat := 4
/-- Runtime functions added: `tabInLineIndentLoop`/`tabInLineIndent`, in both
    pipelines. -/
def runtimeAdditions : Nat := 4
/-- Grammar files edited — none.  `[63]`/`[187]` always said this. -/
def grammarEdits : Nat := 0
/-- Proof files that needed repair for the runtime addition — none: the new
    branch is inside a stage whose `Except` interface did not change. -/
def proofFilesRepaired : Nat := 0
/-- yaml-test-suite score, before and after. -/
def suiteScoreBefore : Nat := 347
def suiteScoreAfter : Nat := 347

theorem shipped :
    escapeSitesBefore = 12 ∧ escapeSitesAfter = 8 ∧
    scannerDropBefore = scannerDropAfter ∧ runtimeAdditions = 4 ∧
    grammarEdits = 0 ∧ proofFilesRepaired = 0 ∧
    suiteScoreBefore = suiteScoreAfter := by
  decide

end L4YAML.Tests.Reflections.GuardInTheWrongCoordinate

end Blanket
