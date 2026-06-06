/-!
# Reflection 322 — import-forced parametricity: thread an UPSTREAM lemma's IH over an ABSTRACT guard `Q`, bind the concrete guard only at the downstream fixpoint

Self-contained (core Lean) toy of the R322 `Q`-parametric IH re-versioning across the seq descent
chain (`recseqentry_seqbracket_oracle` / `recseqentry_window_dispatch` / `seqChild_safeBodyUnit` /
`seqDescent_provider_of_located`).

The real situation: the seq `windowWidth_strongRecOn` recursion must thread a THIRD guard conjunct
`SeqEnclosed tokens lo` through its induction hypothesis.  The IH-supplying oracle/dispatch live in
`NonemptyStructure.lean`, which is UPSTREAM of `SeqEnclosed` (`SeqInteriorSeparators.lean` imports
`NonemptyStructure`) — so the oracle CANNOT name `SeqEnclosed`.  The naive "add `→ SeqEnclosed lo'`
to the IH type in place" edit is impossible (import cycle); and a "drop the guard" adapter cannot
reconstruct it (the oracle's recursive call genuinely needs the guard at the descended window, and a
general-`lo'` closure cannot manufacture it because the guard is not universally true).

**Resolution — import-forced parametricity.**  Make the upstream lemma PARAMETRIC over an abstract
predicate `Q : Nat → Prop` on the recursion variable, taking the guard's descend-output `Q (lo+1)` as
an OPAQUE hypothesis.  The upstream lemma never learns what `Q` is.  The concrete guard
`Q := RealGuard` is bound only at the DOWNSTREAM fixpoint (which sits after the guard's definition).
The import boundary that BLOCKS the naive edit is exactly what parametricity SATISFIES.

This file models the two-module split with two namespaces: `Upstream` (declared FIRST, parametric over
`Q`, mentions no concrete guard) and `Downstream` (the concrete guard `Enc`, its descend lemma, and the
fixpoint that instantiates `Q := Enc`).  POSITIVE: the fixpoint builds the deliverable end-to-end.
NEGATIVE: the guard is not universally true, so a guard-blind adapter cannot invent `Q lo'` — the guard
MUST be threaded, not dropped.

Sharpens `ParametricAssemblerExtraction`-style lifting (here the universal is over the GUARD predicate,
forced by imports); complements `AdditiveParallelTypeOverSharedEdit` (don't structurally edit the
shared/upstream thing — GENERALIZE it over an abstract predicate instead).  The descend output is the
`PushBlindFramePreserveDependent` (R321) edge supplied at the instantiation site.
-/

namespace Tests.Reflections.ImportForcedParametricGuard

set_option autoImplicit false

-- ════════════════════ The deliverable (toy of `RecSeqBody` over a window `[lo, hi)`) ════════════════════
-- A node descends into `[lo+1, hi)` (the bracket interior); a narrow window is a leaf.
inductive RecBody : Nat → Nat → Prop where
  | leaf {lo hi : Nat} (h : hi ≤ lo + 1) : RecBody lo hi
  | node {lo hi : Nat} (h : lo + 1 < hi) (child : RecBody (lo + 1) hi) : RecBody lo hi

-- ════════════════════ A self-contained width-recursion combinator (toy of `windowWidth_strongRecOn`) ═══
theorem widthRec {P : Nat → Nat → Prop}
    (step : ∀ lo hi, (∀ lo' hi', hi' - lo' < hi - lo → P lo' hi') → P lo hi) :
    ∀ lo hi, P lo hi := by
  have key : ∀ w, ∀ lo hi, hi - lo = w → P lo hi := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ihw =>
      intro lo hi hwlo
      subst hwlo
      exact step lo hi (fun lo' hi' hlt => ihw (hi' - lo') hlt lo' hi' rfl)
  intro lo hi
  exact key (hi - lo) lo hi rfl

-- ════════════════════ UPSTREAM module — declared FIRST, PARAMETRIC over `Q`, names no concrete guard ═══
namespace Upstream

/-- The UPSTREAM oracle (toy of `recseqentry_seqbracket_oracle`).  It lives "before" the concrete
    guard, so it is PARAMETRIC over an abstract `Q : Nat → Prop`.  Its single descend call needs the
    guard at the child window `lo+1`, supplied as the OPAQUE hypothesis `h_q_succ : Q (lo + 1)`; its IH
    carries a `Q lo'` premise.  It never learns what `Q` is. -/
theorem oracle (Q : Nat → Prop) (lo hi : Nat) (h : lo + 1 < hi)
    (h_q_succ : Q (lo + 1))
    (ih : ∀ lo' hi', hi' - lo' < hi - lo → Q lo' → RecBody lo' hi') :
    RecBody lo hi :=
  RecBody.node h (ih (lo + 1) hi (by omega) h_q_succ)

/-- The UPSTREAM dispatch (toy of `recseqentry_window_dispatch`).  It fires the descend CONDITIONALLY,
    so it takes the descend STEP `h_q_descend : C → Q (lo + 1)` (here the toy "opener" condition is
    `lo + 1 < hi`) and forwards it to the oracle.  Still parametric over `Q`. -/
theorem dispatch (Q : Nat → Prop) (lo hi : Nat)
    (h_q_descend : lo + 1 < hi → Q (lo + 1))
    (ih : ∀ lo' hi', hi' - lo' < hi - lo → Q lo' → RecBody lo' hi') :
    RecBody lo hi := by
  by_cases h : lo + 1 < hi
  · exact oracle Q lo hi h (h_q_descend h) ih
  · exact RecBody.leaf (by omega)

end Upstream

-- ════════════════════ DOWNSTREAM module — the concrete guard, its descend, and the fixpoint ══════════
namespace Downstream

/-- The concrete guard (toy of `SeqEnclosed`).  `Enc n := 1 ≤ n` — true at every real window start
    (`2 ≤ lo`), but NOT universally true (`Enc 0` is false). -/
def Enc (n : Nat) : Prop := 1 ≤ n

/-- The descend edge (toy of `seqEnclosed_descend`).  PUSH-blind: it needs nothing of the parent
    (`Enc (lo+1)` holds outright), the R321 push edge. -/
theorem enc_descend (lo : Nat) (_h : Enc lo) : Enc (lo + 1) := by unfold Enc; omega

/-- **The downstream fixpoint** (toy of `seqWindowRecSeqBody`).  Here — and ONLY here — the abstract
    `Q` is bound to the concrete `Enc`, and the opaque descend hypothesis is filled by `enc_descend`.
    The step's own width-IH is re-packaged into the dispatch's `Q`-parametric IH verbatim. -/
theorem fixpoint : ∀ lo hi, Enc lo → RecBody lo hi := by
  refine widthRec (P := fun lo hi => Enc lo → RecBody lo hi) ?_
  intro lo hi ih h_enc
  exact Upstream.dispatch Enc lo hi
    (fun _ => enc_descend lo h_enc)        -- the descend output, bound at the instantiation site
    (fun lo' hi' hlt h_q => ih lo' hi' hlt h_q)

-- POSITIVE: the fixpoint builds the deliverable end-to-end at a genuine window `[2, 5)` (`Enc 2` holds).
example : RecBody 2 5 := fixpoint 2 5 (by unfold Enc; omega)

-- NEGATIVE: the guard is NOT universally true, so a guard-BLIND adapter cannot invent `Q lo'` for a
-- general `lo'` — the guard must be THREADED through the IH (as `fixpoint` does via `h_enc`/`enc_descend`),
-- never manufactured inside the upstream lemma.
theorem enc_not_universal : ¬ (∀ n, Enc n) := by
  intro h
  have := h 0
  unfold Enc at this
  omega

-- The descend edge IS the only way the guard reaches the child — and it is available downstream:
example : Enc 3 := enc_descend 2 (by unfold Enc; omega)

end Downstream

end Tests.Reflections.ImportForcedParametricGuard
