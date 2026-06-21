/-!
# Reflection 476 — the load-bearing containment `lo ≤ p` of an enclosing-locate residual
# falls out of a BALANCE-ADDITIVITY contradiction against the LOCATOR's OWN Dyck floor —
# no content structure, no close location.

Self-contained (core Lean, no `L4YAML` import) toy recording the brick R476 landed:
`seqLocatedOpener_within_body`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the FIRST sub-piece of the
(α) `enclosingLocate` residual that `seqWidthEnc_of_enclosingLocate_and_recIH` (R475) lifts.

**The setup.**  The joint induction's per-window deliverable needs, for a nested gate `[a, b)` inside
the body window `[lo, hi)`, the enclosing frame `[p, hiE)` to be CONTAINED in the body (`lo ≤ p`,
`hiE ≤ hi`) — those two containments are exactly what make R475's inner frame-width IH dischargeable
from the outer body-width IH (see `ContainedFrameIHFromOuterIH`).  This toy isolates the LOWER one.

**The bridge — a floor conflict at DIFFERENT origins.**  Model `flowBracketBalance tokens` as an
abstract additive `bal : Nat → Nat → Int` whose ONLY law is interval composition
`bal lo hi = bal lo mid + bal mid hi`.  Two floors are in hand, keyed on DIFFERENT origins:

  * the body window's Dyck floor gives `bal lo a ≥ 0`, and the gate's `≠ 0` lifts it to `bal lo a ≥ 1`
    (the nested start `a` sits at depth ≥ 1 relative to `lo`);
  * the backward-locator delivers its OWN interior floor `bal (p+1) i ≥ 0` for `i ∈ [p+1, a]`, plus
    the balanced body `bal (p+1) a = 0`.

If the opener escaped the window (`p < lo`, i.e. `p + 1 ≤ lo ≤ a`), composing the located body balance
at the cut point `lo` gives `0 = bal (p+1) a = bal (p+1) lo + bal lo a`, so
`bal (p+1) lo = -(bal lo a) ≤ -1 < 0` — but the locator's floor says `bal (p+1) lo ≥ 0`.  Contradiction.
So `lo ≤ p`: the locator's interior floor FORBIDS the opener from sitting before the window start,
because doing so would force the segment `[p+1, lo)` to "pay back" the positive nested depth and dip
below the floor.  The whole proof is one composition + `omega` — no content structure, no close
location, no `FlowBodyWindow`/content construction.

This toy reproduces the three reusable facts.
-/

namespace ContainmentFromFloorConflict

set_option autoImplicit false

/-- **The structural heart** — the lower containment `lo ≤ p` from the two floors.  `bal` stands for
    `flowBracketBalance tokens`; its sole law is interval composition.  No content structure and no
    close location is involved — purely the locator's interior floor contradicting the positive
    body-relative depth.  Mirrors `seqLocatedOpener_within_body`. -/
theorem opener_within_window
    (bal : Nat → Nat → Int)
    (bal_compose : ∀ lo mid hi, lo ≤ mid → mid ≤ hi → bal lo hi = bal lo mid + bal mid hi)
    (lo a p : Nat)
    (h_lo_a : lo ≤ a)
    (h_depth_pos : bal lo a ≥ 1)
    (h_body_bal : bal (p + 1) a = 0)
    (h_loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → bal (p + 1) i ≥ 0) :
    lo ≤ p := by
  cases Nat.lt_or_ge p lo with
  | inl h_lt =>
    -- `p < lo`, i.e. `p + 1 ≤ lo`, is the case to refute.
    have h_p1_lo : p + 1 ≤ lo := by omega
    -- Split the located body balance at the cut point `lo`.
    have h_comp : bal (p + 1) a = bal (p + 1) lo + bal lo a :=
      bal_compose (p + 1) lo a h_p1_lo h_lo_a
    -- The locator's own floor at `lo` forbids the negative segment forced above.
    have h_floor_lo : bal (p + 1) lo ≥ 0 := h_loc_floor lo h_p1_lo h_lo_a
    omega
  | inr h_ge => exact h_ge

/-- **The `≥ 1` step** — the body Dyck floor (`≥ 0`) plus the gate's `≠ 0` give the strict positive
    depth the conflict needs.  This is the only place the gate's nonzero-balance hypothesis is used,
    and it lifts a ≥0 floor to a ≥1 strict gap purely by `omega`. -/
theorem depth_pos_of_floor_and_ne
    (bal : Nat → Nat → Int) (lo a : Nat)
    (h_floor : bal lo a ≥ 0) (h_ne : bal lo a ≠ 0) :
    bal lo a ≥ 1 := by omega

/-- **The locator floor is LOAD-BEARING** — drop it and the containment is FALSE.  Without
    `bal (p+1) i ≥ 0`, the opener `p` can sit before `lo`: a `bal` with `bal 5 10 = 1`, `bal 1 10 = 0`
    admits `lo = 5`, `a = 10`, `p = 0` with `lo ≤ a`, `bal lo a ≥ 1`, `bal (p+1) a = 0` all true yet
    `lo ≤ p` (`5 ≤ 0`) false.  (Such a `bal` necessarily violates the floor at `i = 5`, which is
    exactly the fact the real locator delivers and this counterexample lacks.)  So the interior floor
    is not bookkeeping — it is what makes the descent well-founded. -/
theorem needs_locator_floor :
    ¬ (∀ (bal : Nat → Nat → Int) (lo a p : Nat),
        lo ≤ a → bal lo a ≥ 1 → bal (p + 1) a = 0 → lo ≤ p) := by
  intro h
  have key : (5 : Nat) ≤ 0 :=
    h (fun i j => if i = 5 ∧ j = 10 then (1 : Int) else 0) 5 10 0
      (by omega) (by decide) (by decide)
  omega

/-- CONCRETE, non-vacuous — the heart runs end-to-end on a genuine potential-difference `bal`
    (`bal i j = j - i`, automatically additive), with a CONTAINED opener (`lo = 2 ≤ p = 3`).  All
    premises are simultaneously satisfiable with the conclusion true, so the heart is not vacuous. -/
example : (2 : Nat) ≤ 3 :=
  opener_within_window (fun i j => (j : Int) - (i : Int))
    (by intro lo mid hi _ _; omega)
    2 4 3
    (by omega)
    (by omega)
    (by omega)
    (by intro i h1 h2; omega)

/-! ## The END-dual — the UPPER containment `hiE ≤ hi`

The second of R475's two load-bearing containments mirrors the first to the window's END.  Where the
LOWER containment `lo ≤ p` (`opener_within_window`) conflicts the OPENER-locator's interior floor
(over `[p+1, a]`) with the body window's depth at the nested start, the UPPER containment `hiE ≤ hi`
conflicts the CLOSE-locator's interior floor (over `[p+1, hiE]`) with the enclosing window's balance:
the enclosing window has already paid back the opener's `+1` by `hi`, so the located frame's interior
cannot still be ≥ 0 there unless its close `hiE` came first.  Same floor-conflict shape, other end.

The reusable sub-lesson: this inner floor is the close-locator's SILENTLY-DROPPED output.
`flowBracketBalance_matching_close_seq` computes both `j < hi` and the interior floor, but
`seqClose_of_located_and_enclosing`'s return type erases both — so the UPPER containment needs no new
machinery, only the re-threaded floor.  Mirrors `seqLocatedClose_within_body`. -/

/-- **The END-dual heart** — the upper containment `hiE ≤ hi` from the close-locator's interior floor
    against the enclosing window's balance + Dyck floor + opener delta.  One composition pair +
    `omega`; no content structure, no separate close arithmetic.  Mirrors `seqLocatedClose_within_body`. -/
theorem close_within_window
    (bal : Nat → Nat → Int)
    (bal_compose : ∀ lo mid hi, lo ≤ mid → mid ≤ hi → bal lo hi = bal lo mid + bal mid hi)
    (lo hi p hiE : Nat)
    (h_lo_p : lo ≤ p)
    (h_p_hi : p < hi)
    (h_win_floor : ∀ i, lo ≤ i → i ≤ hi → bal lo i ≥ 0)
    (h_total : bal lo hi = 0)
    (h_open : bal p (p + 1) = 1)
    (h_inner_floor : ∀ i, p + 1 ≤ i → i ≤ hiE → bal (p + 1) i ≥ 0) :
    hiE ≤ hi := by
  cases Nat.lt_or_ge hi hiE with
  | inl h_gt =>
    -- `hi < hiE`, i.e. `p + 1 ≤ hi ≤ hiE`, is the case to refute.
    have h_p1_hi : p + 1 ≤ hi := by omega
    -- The close-locator's interior floor at `hi` (which lies in `[p+1, hiE]`).
    have h_floor_hi : bal (p + 1) hi ≥ 0 := h_inner_floor hi h_p1_hi (by omega)
    -- The enclosing window's Dyck floor at `p`.
    have h_floor_p : bal lo p ≥ 0 := h_win_floor p h_lo_p (by omega)
    -- Split the enclosing total across `p`, then across `p + 1`.
    have h_comp1 : bal lo hi = bal lo p + bal p hi := bal_compose lo p hi h_lo_p (by omega)
    have h_comp2 : bal p hi = bal p (p + 1) + bal (p + 1) hi :=
      bal_compose p (p + 1) hi (by omega) h_p1_hi
    omega
  | inr h_ge => exact h_ge

/-- **The inner floor is LOAD-BEARING** — drop it and the upper containment is FALSE.  Without
    `bal (p+1) i ≥ 0`, the matching close `hiE` can sit past `hi`: a `bal` representing the window
    `[ ]` (`bal 0 1 = 1`, `bal 0 2 = 0`) admits `lo = 0`, `hi = 2`, `p = 0`, `hiE = 3` with `lo ≤ p`,
    `p < hi`, `bal lo hi = 0`, `bal p (p+1) = 1` all true yet `hiE ≤ hi` (`3 ≤ 2`) false.  (Such a
    `bal` necessarily lacks the close-locator's interior floor past the real close at index 1.)  So the
    interior floor is what pins the close inside the enclosing window. -/
theorem needs_inner_floor :
    ¬ (∀ (bal : Nat → Nat → Int) (lo hi p hiE : Nat),
        lo ≤ p → p < hi → bal lo hi = 0 → bal p (p + 1) = 1 → hiE ≤ hi) := by
  intro h
  have key : (3 : Nat) ≤ 2 :=
    h (fun i j => if i = 0 ∧ j = 1 then (1 : Int) else 0) 0 2 0 3
      (by omega) (by omega) (by decide) (by decide)
  omega

/-- CONCRETE, non-vacuous — the END-dual heart runs end-to-end on a genuine balanced bracket window
    `[ ]` modelled by an abstract depth `g` (`g 0 = 0`, `g 1 = 1`, `g 2 = 0`, so `bal i j = g j - g i`
    is automatically additive), with the matching close CONTAINED at `hiE = 1 ≤ hi = 2`.  All premises
    are simultaneously satisfiable with the conclusion true, so the heart is not vacuous. -/
example (g : Nat → Int) (hg0 : g 0 = 0) (hg1 : g 1 = 1) (hg2 : g 2 = 0) :
    (1 : Nat) ≤ 2 :=
  close_within_window (fun i j => g j - g i)
    (by intro a b c _ _; omega)
    0 2 0 1
    (by omega)
    (by omega)
    (by intro i _ h2
        have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hcase with rfl | rfl | rfl <;> omega)
    (by omega)
    (by show g 1 - g 0 = 1; omega)
    (by intro i h1 h2
        have : i = 1 := by omega
        subst this; show g 1 - g 1 ≥ 0; omega)

end ContainmentFromFloorConflict
