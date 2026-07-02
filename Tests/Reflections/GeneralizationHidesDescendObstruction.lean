/-!
# Reflection 444 — a "trivial parametric generalization" of a recursive producer can hide a DESCEND-EDGE
# interface obstruction: the new bound re-establishes free at the recursion's monotone (advance) edge but
# is UNPROVABLE at the descend edge, because the descend adapter exposes only the WIDTH-DECREASE, not the
# CONTAINMENT the bound needs.  A LEAF consumer (no edges) always generalizes freely — so split the brick.

Self-contained (core Lean, no `L4YAML` import) toy of the R444 finding — STEP D continued: the queued
"generalize `seqWindowRecSeqBody`'s carrier span from the root `[2, size-2)` to the window's own enclosing
span `[lo0, hi0]`" sub-brick.

Context.  The R443 blueprint Next step called this generalization a "pure generalization with a confirmed
cheap core … a one-parameter swap with the narrow bound widened, no proof restructuring."  Reading the
recursion refuted the "no restructuring" claim.  The parametric carrier `SeqInteriorSeparators tokens lo0 hi0`
must be NARROWED to each window the recursion visits, which needs the bounds `lo0 ≤ lo ∧ hi ≤ hi0`.  The
recursion (`windowWidth_strongRecOn` inside `seqWindowRecSeqBody`) has two edges:

* ADVANCE `(lo,hi) → (m+1, hi)` — `seqWindowRecSeqBody`'s tail step.  Re-establishing `lo0 ≤ m+1 ∧ hi ≤ hi0`
  is FREE: `lo0 ≤ lo ≤ m < m+1` by `omega` from the threaded invariant, `hi` unchanged.  The EASY edge.
* DESCEND `(lo,hi) → (lo', hi')` — into a nested bracket, via the dispatch's IH adapter
  (`recseqentry_window_dispatch`'s `h_ih`).  Its type exposes ONLY `hi' - lo' < hi - lo` (width-decrease) and
  the window facts — NOT the containment `lo ≤ lo' ∧ hi' ≤ hi`.  The descended window really IS
  `[lo+1, j) ⊆ [lo, hi)` (the oracle knows it internally), but that fact is HIDDEN behind the IH callback's
  weaker summary.  From width-decrease alone the bound `lo0 ≤ lo'` is UNPROVABLE — there is a countermodel
  (`descend_obstruction` below).  The HARD edge, masked by the easy one.

The LEAF projector `seqWindow_flowBodyContent` has NO recursion edge — it narrows the carrier to one window
and stops.  So it generalizes FREELY: one `SeqInteriorSeparators_narrow` with the bounds supplied as
hypotheses (R444 LANDED `seqWindow_flowBodyContent_general` / `_seq_general`, the root-span lemmas now thin
instances reading the bounds off `FlowBodyWindow.lo_ge`/`hi_le`).  This is the genuine smallest-first half.

The reusable rule.  When a generalization adds a parametric bound that a RECURSION must maintain as an
invariant, the bound re-establishes for free at edges whose adapter EXPOSES the structural relation it needs
(advance: monotone, `omega`-derivable) but is STUCK at edges whose adapter HIDES that relation behind a
weaker summary (descend: only width-decrease surfaced, containment hidden).  Before generalizing a recursive
producer, check EACH recursion edge's adapter interface for the relation the new bound needs.  A leaf
consumer (no edges) always generalizes freely — land it now.  Two routes clear the stuck edge:

* ROUTE A — strengthen the adapter interface to expose the hidden relation (here: add `lo ≤ lo' ∧ hi' ≤ hi`
  to `recseqentry_window_dispatch`'s `h_ih`; the oracle already holds both, so the supply is two `omega`s).
  Costly only because the IH-callback shape threads through the whole descent plumbing (oracle, dispatch,
  `seqChild_safeBodyUnit`, their callers).
* ROUTE B — re-architect so the bound's consumer sits OUTSIDE the recursion: don't re-run
  `seqWindowRecSeqBody`'s self-contained inner recursion (which re-narrows the carrier on descend); INLINE the
  single dispatch step driven by the co-construction's OUTER width-IH (whose width-decrease shape already
  MATCHES the dispatch's `h_ih`), consuming the window-local carrier ONLY at the current window for its
  `FlowBodyContent` — never narrowed to a child.  The descend goes through `h_ih`, so the edge that needed
  containment is dissolved.

This toy models: the two edge re-establishments (`covers_advance` free; `descend_obstruction` a refutation
from width-decrease alone), the leaf's free narrow (`leaf_narrows_freely` — the shape of
`seqWindow_flowBodyContent_general`), and ROUTE A's repair (`covers_descend_with_containment`: expose
containment and the bound follows by two `Nat.le_trans`).  All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.GeneralizationHidesDescendObstruction

/-! ## The parametric bound the generalized carrier must maintain across the recursion.

`Covers lo0 hi0 lo hi` models `lo0 ≤ lo ∧ hi ≤ hi0` — the hypotheses
`seqWindow_flowBodyContent_general` consumes to narrow `SeqInteriorSeparators tokens lo0 hi0` down to
`[lo, hi)`.  In the generalized `seqWindowRecSeqBody` this would be threaded as a recursion invariant. -/
def Covers (lo0 hi0 lo hi : Nat) : Prop := lo0 ≤ lo ∧ hi ≤ hi0

/-! ## The EASY edge — ADVANCE.  `(lo, hi) → (lo+1, hi)`.  The bound re-establishes for free: the monotone
    relation `lo ≤ lo+1` is structural, so `lo0 ≤ lo+1` follows by transitivity and `hi ≤ hi0` is
    unchanged.  Models `seqWindowRecSeqBody`'s advance step, where `lo ≤ m+1` is the `omega` of the
    threaded invariant.  This is the edge a "trivial generalization" claim implicitly checks. -/
theorem covers_advance {lo0 hi0 lo hi : Nat} (h : Covers lo0 hi0 lo hi) :
    Covers lo0 hi0 (lo + 1) hi :=
  ⟨Nat.le_trans h.1 (Nat.le_succ lo), h.2⟩

/-! ## The LEAF — no recursion edge.  The bound is SUPPLIED; the carrier narrows once and stops.  Models
    `seqWindow_flowBodyContent_general`: a single `SeqInteriorSeparators_narrow h_lo0 h_hi0 h_carrier0`.
    No edge means nothing to re-establish, so the leaf generalizes FREELY — the genuine smallest-first
    half landed this round. -/
theorem leaf_narrows_freely {lo0 hi0 lo hi : Nat}
    {C : Nat → Nat → Nat → Nat → Prop}
    (narrow : ∀ {a b : Nat}, lo0 ≤ a → b ≤ hi0 → C lo0 hi0 lo0 hi0 → C lo0 hi0 a b)
    (h : Covers lo0 hi0 lo hi) (carrier : C lo0 hi0 lo0 hi0) : C lo0 hi0 lo hi :=
  narrow h.1 h.2 carrier

/-! ## The HARD edge — DESCEND, the OBSTRUCTION.  The descend adapter exposes only the width-decrease
    `hi' - lo' < hi - lo`.  From that ALONE the bound is NOT re-establishable: a descend can decrease the
    width yet ESCAPE the span.  Countermodel — `[lo0,hi0] = [5,10]`, window `[5,10]` (covered), descend to
    `[0,1]` (width `1 < 5`) but `5 ≤ 0` is false.  This is exactly why the parametric carrier cannot ride
    `seqWindowRecSeqBody`'s recursion as-is: at the dispatch's `h_ih` adapter the narrow's `lo0 ≤ lo'`
    premise has no source. -/
theorem descend_obstruction :
    ¬ (∀ lo0 hi0 lo hi lo' hi' : Nat,
        Covers lo0 hi0 lo hi → hi' - lo' < hi - lo → Covers lo0 hi0 lo' hi') := by
  intro H
  have h : (5 : Nat) ≤ 0 := (H 5 10 5 10 0 1 ⟨by decide, by decide⟩ (by decide)).1
  exact absurd h (by decide)

/-! ## ROUTE A — strengthen the adapter to EXPOSE the containment.  Once the descend adapter also hands
    `lo ≤ lo' ∧ hi' ≤ hi` (both of which the seq-bracket oracle already holds internally — `lo ≤ lo+1`,
    `j < hi`), the bound re-establishes by two `Nat.le_trans`.  The cost is not the proof but the ripple:
    the IH-callback shape threads through the whole descent plumbing.  Contrast `descend_obstruction`:
    SAME conclusion, the only difference is the two containment hypotheses — so the obstruction is purely
    an INTERFACE gap, not a mathematical one. -/
theorem covers_descend_with_containment {lo0 hi0 lo hi lo' hi' : Nat}
    (h : Covers lo0 hi0 lo hi) (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi) :
    Covers lo0 hi0 lo' hi' :=
  ⟨Nat.le_trans h.1 h_lo, Nat.le_trans h_hi h.2⟩

/-- The finding in one proposition: the SAME descend re-establishment is FALSE given only width-decrease
    yet TRUE given containment — so a recursive producer's parametric-bound generalization is sound iff
    every edge's adapter exposes the relation the bound needs.  The leaf is the degenerate case (no edge),
    always free. -/
theorem r444_finding :
    (¬ ∀ lo0 hi0 lo hi lo' hi' : Nat,
        Covers lo0 hi0 lo hi → hi' - lo' < hi - lo → Covers lo0 hi0 lo' hi')
    ∧ (∀ lo0 hi0 lo hi lo' hi' : Nat,
        Covers lo0 hi0 lo hi → lo ≤ lo' → hi' ≤ hi → Covers lo0 hi0 lo' hi') :=
  ⟨descend_obstruction, fun _ _ _ _ _ _ h h_lo h_hi => covers_descend_with_containment h h_lo h_hi⟩

end Tests.Reflections.GeneralizationHidesDescendObstruction
