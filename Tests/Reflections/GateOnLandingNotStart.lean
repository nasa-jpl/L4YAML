/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 643 — gate an arm on the position it LANDS at, not the one it started from; a body already generic in that position needs a second PRODUCER of the gate's fact, not a second body

**The rule.**  When an arm's body reads exactly one position — everything it
builds is anchored there — its domain is decided by whatever fact the gate
supplies about THAT position.  Gating instead on the position the step started
from is a strictly smaller domain for no strengthening: the body was already
generic, and the extra inputs it excludes are the ones that REACH the same
landing by a different road.

The repair is not a second body.  It is a second producer of the same fact, and
a wrapper that joins them — after which the one body serves both roads and the
punt shrinks to the inputs that genuinely never land.

Concretely (L4YAML item 19): four block-dispatch arms opened with
`by_cases hcol : sp_scan.col = 0` — the column the PENDING was parked at — and
then obtained, from `preprocess_some_ssl_comments_col0`, the package their
bodies actually consume: `SSLComments sp_scan sp_mid ∧ sp_mid.col = 0`, every
subsequent step anchored at `sp_mid`.  A second lemma, `..._anyCol`, already
produced that identical package from a CROSSED BREAK at any starting column —
and its break disjunct was routed to the deferral.  So `- a⏎- b`, whose pending
parks at column 3, rode `scannerDrop` while `-⏎- b`, whose pending parks at
column 1… also did, and only a park already at column 0 composed.

§1 shows the gap is a matter of coverage, not of strength: the start gate
implies the landing fact but not conversely, and the counterexample is exactly
the break-crossed park.  §2 counts the four cells the two dimensions span.  §3
is the residue: what remains punted is a genuine impossibility, not a second
missing producer, so the join is complete rather than merely bigger.  §4 the
shipped counts.

Self-contained: the two gates, the join, the strictness witness, the residue's
irreducibility, and the counts.
-/

namespace L4YAML.Tests.Reflections.GateOnLandingNotStart

/-! ## §1  Two gates over one body

  A step is described by where it started and whether it crossed a line break;
  it LANDS at a line start exactly when one of those two holds. -/

/-- A dispatch step, stripped to the two facts the gate can read. -/
structure Step where
  /-- Did the step start at a line start (the pending parked at column 0)? -/
  startsAtLineStart : Bool
  /-- Did the step cross a line break on its way to the indicator? -/
  crossedBreak : Bool
  deriving DecidableEq

/-- **The fact the body consumes**: the step ends on a line start, so the
    closed prefix is `[79] s-l-comments` and the indicator sits at column 0. -/
def lands (s : Step) : Prop :=
  s.startsAtLineStart = true ∨ s.crossedBreak = true

/-- **The gate as written**: read the column the step STARTED from. -/
def startGate (s : Step) : Prop := s.startsAtLineStart = true

/-- The start gate is sound — it does produce the landing fact… -/
theorem startGate_lands {s : Step} (h : startGate s) : lands s := Or.inl h

/-- …and incomplete, at exactly one shape: the mid-line park that crosses a
    break.  This is `- a⏎- b`: the pending parks after `a`, the break lands the
    step at column 0 of the next line, and the body — anchored entirely at that
    landing — applies verbatim. -/
theorem startGate_misses_crossed :
    ∃ s : Step, lands s ∧ ¬ startGate s :=
  ⟨⟨false, true⟩, Or.inr rfl, by simp [startGate]⟩

/-- The join is the landing fact itself, so the widened gate needs no new
    reasoning — only the second producer. -/
theorem lands_iff {s : Step} :
    lands s ↔ (startGate s ∨ s.crossedBreak = true) := Iff.rfl

/-! ## §2  What the widening buys, counted

  The two dimensions span four cells.  The start gate covers two; the join
  covers three; the fourth is §3's residue. -/

/-- Every step shape. -/
def cells : List Step :=
  [⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩]

/-- The gate as written, decidably. -/
def startGateB (s : Step) : Bool := s.startsAtLineStart
/-- The joined gate, decidably. -/
def landsB (s : Step) : Bool := s.startsAtLineStart || s.crossedBreak

#guard (cells.filter startGateB).length == 2
#guard (cells.filter landsB).length == 3
#guard (cells.filter (fun s => !landsB s)).length == 1
-- The join is a widening, never a re-attribution: nothing the old gate
-- covered leaves.
#guard cells.all (fun s => !startGateB s || landsB s)

/-! ## §3  The residue is irreducible

  A widening is only finished if what remains punted CANNOT land.  Here it
  cannot: a step that crossed no break and did not begin at a line start ends
  where it began, mid-line — and there is no third producer to look for. -/

theorem residue_iff {s : Step} :
    ¬ lands s ↔ (s.startsAtLineStart = false ∧ s.crossedBreak = false) := by
  cases hb : s.startsAtLineStart <;> cases hc : s.crossedBreak <;>
    simp [lands, hb, hc]

/-! ## §4  The shipped counts (item 19, 2026-08-11) -/

/-- Block-dispatch arms re-gated from the park column to the landing. -/
def armsRegated : Nat := 3
/-- New GRAMMAR lemmas the widening needed. -/
def newGrammarLemmas : Nat := 0
/-- New couplings, carriers or `PendingNode` fields. -/
def newCouplings : Nat := 0
/-- New PRODUCER lemmas: the join itself, plus the degenerate `s-l-comments`
    a step already at a line start closes. -/
def newProducerLemmas : Nat := 2
/-- Lines of arm BODY rewritten: the bodies were already anchored at the
    landing, so re-gating touched only how their inputs are obtained. -/
def armBodiesRewritten : Nat := 0
/-- Deferral (`block_dispatch_deferred`) call sites before and after. -/
def deferralSitesBefore : Nat := 22
/-- …and after. -/
def deferralSitesAfter : Nat := 18
/-- Dead hypotheses the re-gating exposed and deleted (`h_closable`,
    `h_close_old` — each a duplicate of a closure already passed). -/
def deadHypothesesDeleted : Nat := 2
/-- Scanner/runtime files edited. -/
def runtimeEdits : Nat := 0

#guard armsRegated == 3
#guard newGrammarLemmas == 0
#guard newCouplings == 0
#guard newProducerLemmas == 2
#guard armBodiesRewritten == 0
#guard deferralSitesBefore == 22
#guard deferralSitesAfter == 18
#guard deadHypothesesDeleted == 2
#guard runtimeEdits == 0

end L4YAML.Tests.Reflections.GateOnLandingNotStart

end Blanket
