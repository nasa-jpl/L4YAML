/-!
# Reflection 255 — reconcile an *unbounded* consumer quantifier with a *bounded* producer by recovering the missing bounds from the enclosing context's own boundary tokens

Self-contained core-Lean toy (no `L4YAML` import) for the principle: **a
consumer-joint-before-producer move has *two* boundaries.  When the consumer quantifies a window
*unboundedly* but the producer (and the assembler that consumes it) needs positional *bounds* on
that window, do not push the bound-recovery into the future per-window recursion — hoist it into one
joint that recovers the bounds *once* from boundary invariants the enclosing context already owns.**

In L4YAML this is the locate's input boundary.  `FlowSubrangesOk.seq` quantifies over **all**
`lo hi` with only the bracket guards (`tokens[hi] = .flowSequenceEnd`, `tokens[lo-1] =
.flowSequenceStart`, balanced between), but the R254 outer assembler `seqLocated_of_recseqbody_outer`
needs `2 ≤ lo` and `hi ≤ size - 2` (to instantiate `LO = 2`, `HI = size - 2`, the body-interior span
the structure proof already has `WellTyped` for).  Those bounds are *forced* by the stream's boundary
tokens — `tokens[0] = .streamStart` rules out `lo ≤ 1` (both make `lo - 1 = 0`), and
`tokens[size-1] = .streamEnd` rules out `hi = size - 1` — so `seqLocator_of_window_recseqbody`
recovers them per window and collapses the unbounded locator to the *bounded* per-window `RecSeqBody`
producer the value-driven recursion will deliver.

Toy model: a "stream" is a `List Tok` framed by `SS` (stream-start) … `SE` (stream-end), with `OB`/
`CB` the open/close brackets and `A` the content.  The "target" produced at a window `[lo,hi)` is a
toy `RecBody` (here: the window content is all `A`).

* `bound_lo` — the load-bearing recovery: from `toks[0]! = SS` and the opener guard
  `toks[lo-1]! = OB`, derive `2 ≤ lo` (the `OB ≠ SS` constructor-distinctness rules out `lo ≤ 1`,
  where `lo - 1 = 0`).  Toy of the real lemma's first `exfalso`/`omega`/`decide` argument.
* `bound_hi` — symmetric: from `toks[length-1]! = SE`, `toks[hi]! = CB`, `hi < length`, derive
  `hi ≤ length - 2` (the `CB ≠ SE` distinctness rules out `hi = length - 1`).
* `locator_of_window_recbody` — the joint: takes the two boundary tokens and the **bounded**
  per-window producer `h_rec` (`2 ≤ lo → hi ≤ length - 2 → … → RecBody window`, the recursion's
  still-owed deliverable), recovers the bounds per window via `bound_lo`/`bound_hi`, and emits the
  **unbounded** locator (no `2 ≤ lo` / `hi ≤ length-2` hypotheses).  Toy of
  `seqLocator_of_window_recseqbody`.

Witnesses (positive *and* negative):

* positive — on `good = [SS, OB, A, CB, SE]` the opener guard holds only at `lo = 2` and the closer
  only at `hi = 3`, and `bound_lo`/`bound_hi` recover `2 ≤ 2` / `3 ≤ 3`; `recBody [A]` holds, so the
  target window is inhabited.
* negative — the boundary tokens are *load-bearing*: on `bad = [OB, A, CB]` (no `SS` frame) the
  opener guard is satisfied at `lo = 1` (`bad[0]! = OB`) yet `2 ≤ 1` is false — exactly the window
  the missing `SS` boundary token would have excluded.  So without the boundary invariant the bound
  is *not* recoverable and the unbounded quantifier is *not* safe.
-/

namespace Tests.Reflections.BoundaryBoundRecovery

inductive Tok | SS | OB | CB | SE | A
  deriving DecidableEq, Inhabited, Repr

open Tok

/-- Toy "produced target" at a window: the window content is all `A` (decidable). -/
def recBody (w : List Tok) : Bool := w.all (· == Tok.A)

/-- The consumer's per-window target (the toy `SeqBodyProps`). -/
abbrev SeqProps (toks : List Tok) (lo hi : Nat) : Prop :=
  recBody ((toks.take hi).drop lo) = true

/-- **Lower-bound recovery** — from the stream-start boundary token, the opener guard forces
    `2 ≤ lo`.  Toy of the real joint's first `exfalso`/`omega`/`decide` argument. -/
theorem bound_lo (toks : List Tok) (lo : Nat)
    (h_t0 : toks[0]! = Tok.SS) (h_open : toks[lo - 1]! = Tok.OB) : 2 ≤ lo := by
  rcases Nat.lt_or_ge lo 2 with hlt | hge
  · exfalso
    have h0 : lo - 1 = 0 := by omega
    rw [h0, h_t0] at h_open
    exact absurd h_open (by decide)
  · exact hge

/-- **Upper-bound recovery** — from the stream-end boundary token, the closer guard forces
    `hi ≤ length - 2`.  Toy of the real joint's second `exfalso`/`omega`/`decide` argument. -/
theorem bound_hi (toks : List Tok) (hi : Nat)
    (h_tlast : toks[toks.length - 1]! = Tok.SE) (h_hi_sz : hi < toks.length)
    (h_close : toks[hi]! = Tok.CB) : hi ≤ toks.length - 2 := by
  rcases Nat.lt_or_ge hi (toks.length - 1) with hlt | hge
  · omega
  · exfalso
    have heq : hi = toks.length - 1 := by omega
    rw [heq, h_tlast] at h_close
    exact absurd h_close (by decide)

/-- **The boundary-anchoring locator joint** (toy of `seqLocator_of_window_recseqbody`).  The
    consumer quantifies the window *unboundedly*; the bounded producer `h_rec` is the recursion's
    owed deliverable.  The joint recovers `2 ≤ lo` / `hi ≤ length - 2` *once per window* from the
    boundary tokens and hands the bounded producer the bounds it needs — collapsing the unbounded
    locator to the bounded per-window producer.  Verified-but-unconsumed: `h_rec` (the recursion)
    does not exist yet, exactly as in L4YAML. -/
theorem locator_of_window_recbody (toks : List Tok)
    (h_t0 : toks[0]! = Tok.SS)
    (h_tlast : toks[toks.length - 1]! = Tok.SE)
    (h_rec : ∀ lo hi, 2 ≤ lo → hi ≤ toks.length - 2 → lo ≤ hi → hi < toks.length →
      toks[hi]! = Tok.CB → toks[lo - 1]! = Tok.OB → SeqProps toks lo hi) :
    ∀ lo hi, lo ≤ hi → hi < toks.length →
      toks[hi]! = Tok.CB → toks[lo - 1]! = Tok.OB → SeqProps toks lo hi := by
  intro lo hi h_lo_hi h_hi_sz h_close h_open
  exact h_rec lo hi (bound_lo toks lo h_t0 h_open)
    (bound_hi toks hi h_tlast h_hi_sz h_close) h_lo_hi h_hi_sz h_close h_open

/-! ## Positive witnesses — `good = [SS, OB, A, CB, SE]` -/

def good : List Tok := [SS, OB, A, CB, SE]

-- boundary tokens present
#guard good[0]! == Tok.SS
#guard good[good.length - 1]! == Tok.SE
-- the opener guard holds only at `lo = 2`, the closer only at `hi = 3`
#guard good[2 - 1]! == Tok.OB
#guard good[3]! == Tok.CB
-- the bounds are genuinely recovered at that window
theorem pos_lo : 2 ≤ 2 := bound_lo good 2 (by decide) (by decide)
theorem pos_hi : 3 ≤ good.length - 2 := bound_hi good 3 (by decide) (by decide) (by decide)
-- the produced target at the body-interior window is inhabited (`(take 3).drop 2 = [A]`)
#guard recBody ((good.take 3).drop 2)
#guard ((good.take 3).drop 2) == [Tok.A]

/-! ## Negative witnesses — the boundary token is load-bearing (`bad = [OB, A, CB]`, no `SS` frame) -/

def bad : List Tok := [OB, A, CB]

-- the stream-start boundary token is ABSENT (so `bound_lo`'s hypothesis is unmet)
#guard (bad[0]! == Tok.SS) == false
-- yet the opener guard is satisfied at `lo = 1` …
#guard bad[1 - 1]! == Tok.OB
-- … and that window violates the bound the missing boundary token would have enforced
#guard decide (2 ≤ 1) == false

/-- Made concrete: for `bad` there is no proof of `2 ≤ lo` at `lo = 1` from the opener guard,
    precisely because the `SS` boundary hypothesis `bad[0]! = SS` is false — so `bound_lo` is
    inapplicable.  Without the boundary invariant, the unbounded quantifier is unsafe. -/
theorem neg_no_ss : bad[0]! ≠ Tok.SS := by decide

end Tests.Reflections.BoundaryBoundRecovery
