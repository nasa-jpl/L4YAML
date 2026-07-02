/-
# Reflection 287 — the per-window `step` has a *guard-threading skeleton* below its grammar core

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflection 287 (and memory `ref-guard-threading-skeleton-before-grammar`).

**The principle.** A metric-recursion combinator (Reflection 286's `windowWidth_strongRecOn`, demoed in
`WidthRecursionCombinator.lean`) is abstract over a guard `G : Nat → Nat → Prop` (the inhabitable
region) and a deliverable `P`. To *drive* it on a real recursion, both must be made concrete. `P` is
the obvious deliverable (here a `RecSeqBody`/`RecMapBody`); `G` is NOT obvious — it is the bundle of
invariants a sub-window must carry to be a legitimate recursion instance. And before the per-window
step's grammar-bearing core (the head-shape classification) can run at all, the step must invoke the
combinator's IH on its sub-windows — which requires `G` to be (a) NAMED concretely and (b) shown
PRESERVED across each recursion edge (ADVANCE to the tail, DESCEND into a nested bracket). That layer
is grammar-free, and — because a well-chosen `G` names no collection-specific deliverable type — it is
SHARED across both axes. So the order of attack within the step is: define `G` → per-edge preservation
→ *then* the head-shape bridge.

`BodyWin` below is the toy of the real `FlowBodyWindow` (frame bounds + non-emptiness + balanced/Dyck
+ a content predicate `wt`), and `bodyWin_advance` is the toy of `flowBodyWindow_advance` — its proof
is the real one verbatim (re-base each tail prefix to the outer origin, then close `Dyck` by the outer
`Dyck`; transport the content predicate down to the subrange).

**What this demo asserts (fails the build if it ever drifts):**
  * POSITIVE — `bodyWin_advance` transports the WHOLE guard from `[lo, hi)` to the tail `[m+1, hi)`
    given only the separator's transport certificates (`bodyWin_advance`, `adv_concrete`), and the SAME
    guard gates two structurally-different deliverables (`feedSeq`, `feedMap`) — one guard, both axes.
  * NEGATIVE — the non-emptiness field `lo < hi` is LOAD-BEARING (the R285 echo): the guard EXCLUDES the
    empty window, so the deliverable it gates is never asked for an uninhabited window
    (`not_bodyWin_empty`); and the ADVANCE edge strictly narrows the window (`#guard`).
-/

namespace Tests.Reflections.GuardThreadingSkeleton

/-! ## The guard — collection-free, hence shared across axes

`BodyWin` is parametrized only by an abstract balance `bal` and content predicate `wt` (the toys of
`flowBracketBalance` and `WellTyped`); it mentions NO deliverable type. That is what lets one guard,
and one preservation lemma, serve both the seq and the map body recursion. -/
structure BodyWin (bal : Nat → Nat → Int) (wt : Nat → Nat → Prop) (size lo hi : Nat) : Prop where
  lo_ge     : 2 ≤ lo
  lo_lt     : lo < hi               -- non-emptiness: the R285 peel — EXCLUDES the empty window from `G`
  hi_lt     : hi < size
  balanced  : bal lo hi = 0
  dyck      : ∀ i, lo ≤ i → i ≤ hi → bal lo i ≥ 0
  wellTyped : wt lo hi

/-! ## The ADVANCE guard-preservation — the verbatim core of `flowBodyWindow_advance`

Given the guard on `[lo, hi)` and the separator's three transport certificates — the tail is balanced
(`h_tail_bal`), depths re-base to the outer origin (`h_rebase`, the toy of `advanceTail_invariant`'s
re-basing), and the content predicate carries to the subrange (`h_wt_sub`, the toy of
`WellTyped_subrange`) — the tail `[m+1, hi)` still satisfies the guard. NO head-shape grammar enters;
the non-emptiness premise `m+1 < hi` (no trailing separator) is DEFERRED to the caller. -/
theorem bodyWin_advance
    (bal : Nat → Nat → Int) (wt : Nat → Nat → Prop) (size lo m hi : Nat)
    (h : BodyWin bal wt size lo hi)
    (h_lo_m : lo ≤ m) (h_m1_hi : m + 1 < hi)
    (h_tail_bal : bal (m + 1) hi = 0)
    (h_rebase : ∀ p, m + 1 ≤ p → p ≤ hi → bal lo p = bal (m + 1) p)
    (h_wt_sub : wt lo hi → wt (m + 1) hi) :
    BodyWin bal wt size (m + 1) hi := by
  obtain ⟨h_lo2, _h_lo_hi, h_hi, _h_bal, h_dyck, h_wt⟩ := h
  refine ⟨by omega, h_m1_hi, h_hi, h_tail_bal, ?_, h_wt_sub h_wt⟩
  -- the Dyck field is the only non-trivial one: re-base each tail prefix to `lo`, then the outer Dyck.
  intro i hi1 hi2
  rw [← h_rebase i hi1 hi2]
  exact h_dyck i (by omega) hi2

/-! ## One guard, both axes — the collection-free guard gates two different deliverables

`feedSeq`/`feedMap` stand for "produce a `RecSeqBody`" / "produce a `RecMapBody`": two
structurally-different deliverables, both gated by the SAME `BodyWin`. The guard (and `bodyWin_advance`)
is written once and reused for both — the point of keeping `G` deliverable-agnostic. -/
def feedSeq {bal wt size lo hi} (_h : BodyWin bal wt size lo hi) : Nat := hi - lo
def feedMap {bal wt size lo hi} (_h : BodyWin bal wt size lo hi) : Nat := hi - lo

/-! ## Positives — a concrete instance, and the ADVANCE step firing on it -/

/-- A concrete guard at `[2, 6)` over the trivial balance/content (everything balanced, `wt = True`). -/
theorem win_2_6 : BodyWin (fun _ _ => 0) (fun _ _ => True) 8 2 6 :=
  ⟨by decide, by decide, by decide, rfl, fun _ _ _ => by decide, trivial⟩

/-- POSITIVE: ADVANCE past a depth-`0` separator at `m = 3` yields the guard on the tail `[4, 6)`. The
    three transport certificates are trivial for the zero balance / `True` content. -/
theorem win_4_6 : BodyWin (fun _ _ => 0) (fun _ _ => True) 8 4 6 :=
  bodyWin_advance (fun _ _ => 0) (fun _ _ => True) 8 2 3 6 win_2_6
    (by decide) (by decide) rfl (fun _ _ _ => rfl) (fun h => h)

-- POSITIVE: the same guard feeds both axes' deliverables.
#guard feedSeq win_2_6 == 4
#guard feedMap win_2_6 == 4

/-! ## Negatives — the guard's non-emptiness is load-bearing, and the edge strictly narrows -/

/-- NEGATIVE: the guard EXCLUDES the empty window — its `lo < hi` field is unsatisfiable at `lo = hi`,
    so the deliverable it gates is never asked for an uninhabited window (the R285 peel). -/
theorem not_bodyWin_empty (bal : Nat → Nat → Int) (wt : Nat → Nat → Prop) (size : Nat) :
    ¬ BodyWin bal wt size 3 3 :=
  fun h => absurd h.lo_lt (by decide)

-- NEGATIVE: the ADVANCE edge strictly NARROWS the window (origin moves `lo ↦ m+1 > lo`), so the
-- combinator's width metric `hi - lo` genuinely decreases — `[2,6)` advances to `[4,6)`, width `4 ↦ 2`.
#guard (6 - (3 + 1)) < (6 - 2)

end Tests.Reflections.GuardThreadingSkeleton
