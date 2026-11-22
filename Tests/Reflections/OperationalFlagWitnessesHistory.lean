/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # An operational flag already witnesses the history (Reflection 624)

A guard reads a piece of state.  To *use* it downstream you need a fact about
what the machine did between two points — "no line break was crossed", "no
indent was popped", "nothing was emitted".  That is a **history** fact, and the
reflex is to go get it: thread a new invariant, or reach for the correspondence
relation and find the field is not there.

DOCS priced exactly that and gave up:

> the guard reads `s.line`, and "preprocessing crossed no break, so the line is
> unchanged" is a fact about `skipToContentLoop` that no existing lemma
> provides.  `ScannerSurfCorr` cannot supply it either — `SurfPos` carries
> `chars` and `col`, and no line at all.

Both halves are true and the conclusion was still wrong.  A machine that *acts*
on its history usually has to **record** it, for its own operational reasons, in
an ordinary field — and that field is a witness, sound for free.  Here
`consumeNewline` sets `needIndentCheck := true` on every break it consumes,
because the next dispatch must re-run the indent check.  Nothing in the loop
clears it.  So the flag on the loop's output *is* "a break was crossed", and the
transport is a two-lemma induction with no character-level reasoning at all.

The two questions to ask, in this order:

1. **Does the machine act on this history?**  If it does, it has recorded it.
2. **Is the record monotone over the region I care about?**  Set-and-never-cleared
   makes the witness sound with one induction; anything else needs the region's
   endpoints pinned too.

§3's `flag` is that field; §4 is the correspondence relation that cannot answer,
which is the trap: a relation designed to project *positions* will never carry
*history*, and its absence reads as "the fact is unavailable".

L4YAML DOCS item 9k / `Proofs/Scanner/ScannerLinePreservation.lean`, 2026-08-08.
-/

namespace Tests.Reflections.OperationalFlagWitnessesHistory

/-! ## §0  A machine with a line counter and an operational flag -/

inductive Ch where
  | sp | br | other
  deriving DecidableEq, Repr, BEq

/-- The machine's state.  `flag` is not there for us: it is the toy's
    `needIndentCheck` — the next step has to re-check indentation after a break,
    so the machine has to remember that one happened. -/
structure St where
  line : Nat
  col : Nat
  flag : Bool
  deriving Repr, BEq, DecidableEq

/-- One step.  A break moves the line, resets the column, and **raises the flag**
    — the only place any of the three happens. -/
def step (s : St) : Ch → St
  | .br => { line := s.line + 1, col := 0, flag := true }
  | _ => { s with col := s.col + 1 }

def run (s : St) (cs : List Ch) : St :=
  cs.foldl step s

/-! ## §1  The flag is monotone, and that is the whole proof

Set-and-never-cleared: no arm of `step` writes `false`. -/

theorem step_flag_mono (s : St) (c : Ch) (h : s.flag = true) : (step s c).flag = true := by
  cases c <;> simp [step] <;> exact h

theorem run_flag_mono (s : St) (cs : List Ch) (h : s.flag = true) :
    (run s cs).flag = true := by
  induction cs generalizing s with
  | nil => simp [run]; exact h
  | cons c rest ih => exact ih (step s c) (step_flag_mono s c h)

/-! ## §2  …so a clear flag on the way out is "no break", and the line is intact

This is the shape of `skipToContentLoop_line_eq_of_needIndentCheck`: the break
branch is *refuted* by the flag rather than excluded by a hypothesis nobody had. -/

theorem run_line_eq_of_flag (s : St) (cs : List Ch) (h : (run s cs).flag = false) :
    (run s cs).line = s.line := by
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih =>
    cases c with
    | br =>
      -- the flag went up here and never comes down, contradicting `h`
      exact absurd (run_flag_mono (step s .br) rest rfl) (by simp [run] at h ⊢; simp [h])
    | sp => simpa [run, step] using ih (step s .sp) (by simpa [run, step] using h)
    | other => simpa [run, step] using ih (step s .other) (by simpa [run, step] using h)

/-! ## §3  The flag is exactly the expensive oracle

`crossed` is what the reflex reaches for: walk the characters that were consumed
and look for a break.  In the real setting that walk is the one thing the
correspondence relation cannot support.  On a clear entry state the flag answers
the same question, and it is a field read. -/

def crossed (cs : List Ch) : Bool := cs.contains .br

def alphabet : List Ch := [.sp, .br, .other]

def wordsOfLen : Nat → List (List Ch)
  | 0 => [[]]
  | n + 1 => (wordsOfLen n).flatMap (fun cs => alphabet.map (fun c => c :: cs))

def corpus : List (List Ch) := (List.range 7).flatMap wordsOfLen

def start : St := { line := 0, col := 0, flag := false }

#guard corpus.length == 1093

-- The flag and the walk agree on every input, from a clear start.
#guard corpus.all (fun cs => (run start cs).flag == crossed cs)

-- And the fact they jointly certify: no break ⟹ the line never moved.
#guard corpus.all (fun cs => !(run start cs).flag || (run start cs).line != start.line)
#guard corpus.all (fun cs => (run start cs).flag || (run start cs).line == start.line)

-- Entry matters only in ONE direction, which is why the lemma above is stated on
-- the OUTPUT flag: from a state that already has it up, the flag over-reports…
#guard (corpus.filter (fun cs => (run { start with flag := true } cs).flag != crossed cs)).length == 127

-- …but the conclusion still holds, because a raised flag concludes nothing.
#guard corpus.all (fun cs =>
  (run { start with flag := true } cs).flag ||
  (run { start with flag := true } cs).line == start.line)

/-! ## §4  Why the correspondence relation was the wrong place to look

The projection the coupling layer carries is `(col, remaining input)` — positions,
not history.  Two runs can agree on it exactly and disagree on the line, so no
lemma over that projection can decide the question.  Its silence is a property of
what it was built to say, not evidence that the fact is unavailable. -/

/-- What the correspondence relation projects: a column and how much input is
    left.  No line. -/
def surf (s : St) (remaining : Nat) : Nat × Nat := (s.col, remaining)

/-- Three spaces: no break. -/
def noBreak : List Ch := [.sp, .sp, .sp]

/-- Content, a break, then three spaces: the same column, and a different line. -/
def withBreak : List Ch := [.other, .br, .sp, .sp, .sp]

#guard surf (run start noBreak) 0 == surf (run start withBreak) 0
#guard (run start noBreak).line != (run start withBreak).line

-- The flag separates them; the projection cannot.
#guard (run start noBreak).flag == false
#guard (run start withBreak).flag == true

end Tests.Reflections.OperationalFlagWitnessesHistory

end Blanket
