/-
# Reflection 286 — the single-named "strongRecOn width-metric driver" is TWO bricks entangled; cut the grammar-free recursion plumbing off as an abstract width-metric combinator

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflection 286 (and memory `ref-width-recursion-combinator-before-grammar-step`).

**The principle.** A producer that recurses on a window-width metric `hi - lo` (here the real
`windowWidth_strongRecOn`, the loop-closing wrapper of the locate driver) is *named* as one thing —
"the `Nat.strongRecOn` width-metric driver" — but is in fact TWO things entangled:

  1. the **recursion plumbing** — set up the well-founded descent on the `Nat` metric and, at each
     window, hand the per-window worker an oracle for every strictly-narrower sub-window;
  2. the **per-window grammar step** — the actual content work (read the head shape, classify the
     item, assemble the deliverable), which *consumes* that oracle but does no recursion itself.

The plumbing knows nothing about the deliverable: abstract it over the per-window deliverable `P`
and guard `G` and it becomes `widthRec` below — pure strong recursion on a `Nat`. Cutting it off
(a) **pins the per-window step's inductive-hypothesis interface** exactly
(`hi' - lo' < hi - lo → G lo' hi' → P lo' hi'`), so the step, when written, is a *non-recursive*
lemma carrying none of the well-founded-recursion risk; and (b) because it **names no
collection-specific deliverable type**, it does NOT re-split across the seq/map axis — *one* proof
drives *both* (the mirror discriminator of `ref-entry-boundary-input-shape-split`). Below, the single
`widthRec` drives two structurally-different toy deliverables (`Reach`, descending from `lo`;
`Reach2`, descending from `hi`) verbatim.

**The guard is load-bearing (the R285 echo).** `widthRec`'s guard `G` is exactly the region where the
deliverable is inhabitable. The toy `Reach lo hi` exists only for `lo ≤ hi` (`reach_le`), so the
guard `G := (· ≤ ·)` keeps the recursion inside the inhabitable region — outside it (`Reach 3 0`) the
deliverable is uninhabited (`not_reach_3_0`), exactly the empty-window peel R285 had to perform so
the driver's interface was satisfiable in the first place.

**What this demo asserts (fails the build if it ever drifts):**
  * POSITIVE — `widthRec` (proved via the codebase's span-bound `Nat.strongRecOn` idiom) drives a
    *genuinely recursive* deliverable whose per-window step REQUIRES the IH (`reach_all`, `reach2_all`),
    and the SAME combinator drives both axes (`Reach` and `Reach2`) from one proof.
  * NEGATIVE — outside the guard the deliverable is uninhabited (`not_reach_3_0`), and the per-window
    step's recursive call genuinely DECREASES the width metric (the `#guard`s on `hi' - lo' < hi - lo`).
-/

namespace Tests.Reflections.WidthRecursionCombinator

/-! ## The combinator — the grammar-free half (drives both axes)

`widthRec` is the verbatim core of the real `windowWidth_strongRecOn`: abstract over the per-window
deliverable `P` and guard `G`, recursion on the width metric `hi - lo`, proved by the codebase's
span-bound strong-induction idiom (`∀ n, ∀ lo hi, hi - lo ≤ n → …`, `induction n using
Nat.strongRecOn`). The per-window `step` is handed an oracle for every strictly-narrower window. -/
theorem widthRec {P : Nat → Nat → Prop} (G : Nat → Nat → Prop)
    (step : ∀ lo hi, G lo hi →
      (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → P lo' hi') →
      P lo hi) :
    ∀ lo hi, G lo hi → P lo hi := by
  have key : ∀ n : Nat, ∀ lo hi : Nat, hi - lo ≤ n → G lo hi → P lo hi := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro lo hi h_span h_g
      -- any sub-window of strictly smaller width has width `< n` (since `hi - lo ≤ n`), so the
      -- strong-recursion IH discharges it; the step never sees the recursion, only this oracle.
      exact step lo hi h_g (fun lo' hi' h_lt h_g' =>
        IH (hi' - lo') (by omega) lo' hi' (Nat.le_refl _) h_g')
  intro lo hi h_g
  exact key (hi - lo) lo hi (Nat.le_refl _) h_g

/-! ## Axis 1 — a genuinely recursive deliverable whose per-window step needs the IH

`Reach lo hi` is inhabited iff `lo ≤ hi`, but ONLY constructively by descending `lo` one step at a
time — so proving it at width `w` genuinely calls the proof at width `< w`. This is the toy of
`RecSeqBody`: a recursive deliverable the width-recursion must build, not a fact `omega` closes. -/
inductive Reach : Nat → Nat → Prop where
  | refl (n : Nat) : Reach n n
  | step {lo hi : Nat} (h : Reach (lo + 1) hi) : Reach lo hi

/-- The per-window grammar STEP (toy): non-recursive, consumes the combinator's oracle `ih`.
    TERMINATE at `lo = hi` (the base constructor `Reach.refl`); ADVANCE at `lo < hi` by calling the
    oracle on the strictly-narrower `[lo+1, hi]` and lifting with `Reach.step`. No `Nat.strongRecOn`
    here — all recursion risk lives in `widthRec`. -/
theorem reachStep : ∀ lo hi, lo ≤ hi →
    (∀ lo' hi', hi' - lo' < hi - lo → lo' ≤ hi' → Reach lo' hi') → Reach lo hi := by
  intro lo hi h_le ih
  rcases Nat.lt_or_ge lo hi with h_lt | h_ge
  · -- ADVANCE: the oracle on `[lo+1, hi]` (width strictly smaller) + `Reach.step`.
    exact Reach.step (ih (lo + 1) hi (by omega) (by omega))
  · -- TERMINATE: `lo = hi`, the base constructor.
    have h_eq : lo = hi := Nat.le_antisymm h_le h_ge
    rw [← h_eq]; exact Reach.refl lo

/-- Instantiate the combinator: `P := Reach`, `G := (· ≤ ·)`, `step := reachStep`. -/
theorem reach_all : ∀ lo hi, lo ≤ hi → Reach lo hi :=
  widthRec (fun lo hi => lo ≤ hi) reachStep

-- POSITIVE: the driven producer fires inside the guard.
theorem reach_0_3 : Reach 0 3 := reach_all 0 3 (by decide)
theorem reach_5_5 : Reach 5 5 := reach_all 5 5 (by decide)

/-! ## Axis 2 — the SAME combinator drives a structurally-different deliverable (no re-split)

`Reach2` descends from the `hi` side instead of `lo` — a different recursion shape, the toy of the
seq→map mirror. The point: `widthRec` is reused VERBATIM (same `G`, same proof), only `P` and the
per-window `step` change. An abstract-`P` combinator does not re-split across axes. -/
inductive Reach2 : Nat → Nat → Prop where
  | refl (n : Nat) : Reach2 n n
  | step {lo hi : Nat} (h : Reach2 lo (hi - 1)) (hlt : lo < hi) : Reach2 lo hi

theorem reach2Step : ∀ lo hi, lo ≤ hi →
    (∀ lo' hi', hi' - lo' < hi - lo → lo' ≤ hi' → Reach2 lo' hi') → Reach2 lo hi := by
  intro lo hi h_le ih
  rcases Nat.lt_or_ge lo hi with h_lt | h_ge
  · exact Reach2.step (ih lo (hi - 1) (by omega) (by omega)) h_lt
  · have h_eq : lo = hi := Nat.le_antisymm h_le h_ge
    rw [← h_eq]; exact Reach2.refl lo

theorem reach2_all : ∀ lo hi, lo ≤ hi → Reach2 lo hi :=
  widthRec (fun lo hi => lo ≤ hi) reach2Step

theorem reach2_0_3 : Reach2 0 3 := reach2_all 0 3 (by decide)

/-! ## Negatives — the guard is load-bearing, and the metric genuinely decreases -/

/-- `Reach` is inhabited only inside the guard `lo ≤ hi`. -/
theorem reach_le {lo hi : Nat} (h : Reach lo hi) : lo ≤ hi := by
  induction h with
  | refl n => exact Nat.le_refl n
  | step _ ih => omega

/-- NEGATIVE: outside the guard the deliverable is uninhabited — the empty (degenerate) window region
    the R285 peel routes AWAY from the recursion, so the driver's interface is satisfiable. -/
theorem not_reach_3_0 : ¬ Reach 3 0 := fun h => absurd (reach_le h) (by decide)

-- NEGATIVE: the per-window step's recursive call genuinely DECREASES the width metric (the IH
-- interface `hi' - lo' < hi - lo` is real, not vacuous). Axis 1 advances `[0,3] ↦ [1,3]`; axis 2
-- advances `[0,3] ↦ [0,2]`; both shrink width `3 ↦ 2`.
#guard (3 - (0 + 1)) < (3 - 0)
#guard ((3 - 1) - 0) < (3 - 0)
-- and the metric is the SAME (`hi - lo`) for both axes — what makes one combinator suffice.
#guard (3 - 0) == (3 - 0)

end Tests.Reflections.WidthRecursionCombinator
