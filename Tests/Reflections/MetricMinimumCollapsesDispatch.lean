/-!
# Reflection 380 — a metric-keyed dispatch DEGENERATES at the metric's minimum; the boundary brick
that guards exhaustiveness in the generic case is the lever that LINEARIZES the degenerate one

Self-contained core-Lean toy of L4YAML BRICK D's scalar-head CONS cell
(`nestedSeq_recseqentry_locate_scalar_cons_step`).

A bottom-up locator dispatches with `move_trichotomy off e.length a` — a pure length-arithmetic 3-way
split keyed on the head ENTRY's METRIC `L = e.length`: LEAF (`a = off+1`) / DESCEND
(`off+1 < a < off+L`) / ADVANCE (`off+L < a`), exhaustive GIVEN the boundary exclusion
`h_ne : a ≠ off+L`.  The reachable-arm count is a DECREASING function of `L`:

* `L ≥ 3` (nonempty seq): all THREE arms reachable.
* `L = 2` (empty seq `[op,cl]`): DESCEND interval `(off+1, off+2)` is EMPTY → LEAF + ADVANCE only.
* `L = 1` (bare scalar `[t]`, the MINIMUM): LEAF position `off+1` COINCIDES with the boundary
  `off+L = off+1`, so the boundary exclusion `a ≠ off+1` ALSO kills LEAF → ADVANCE only, STRAIGHT-LINE.

The lever is the SAME boundary brick the generic case uses for exhaustiveness; at the minimum it does
double duty (excluding the boundary also excludes the LEAF).  Don't replicate the generic N-arm
`rcases` for a minimal-metric element — write it straight-line.
-/

namespace Tests.Reflections.MetricMinimumCollapsesDispatch

set_option autoImplicit false

/-- **The metric-keyed 3-way dispatch** (the toy `move_trichotomy`).  Given the lower bound
    `off+1 ≤ a` and the boundary exclusion `a ≠ off+L`, the target `a` lands in exactly one of
    LEAF / DESCEND / ADVANCE — for ANY `L`, pure `omega`. -/
theorem trichotomy (off L a : Nat) (h_lo : off + 1 ≤ a) (h_ne : a ≠ off + L) :
    (a = off + 1) ∨ (off + 1 < a ∧ a < off + L) ∨ (off + L < a) := by omega

/-! ## POSITIVE (generic, `L = 4`) — all three arms are inhabited. -/

/-- LEAF is reachable at `L = 4` (off = 4, a = 5). -/
theorem generic_leaf : (5 : Nat) = 4 + 1 := by omega
/-- DESCEND is reachable at `L = 4` (a = 6 ∈ (5, 8)). -/
theorem generic_descend : (4 + 1 < 6 ∧ (6 : Nat) < 4 + 4) := by omega
/-- ADVANCE is reachable at `L = 4` (a = 9 > 8). -/
theorem generic_advance : (4 + 4 < (9 : Nat)) := by omega

/-! ## DEGENERATE (`L = 1`, the metric minimum) — the dispatch LINEARIZES to a single ADVANCE arm. -/

/-- The straight-line collapse: at `L = 1` the lower bound `off+1 ≤ a` PLUS the boundary exclusion
    `a ≠ off+1` (= `a ≠ off+L`) force `off+1 < a` — the ADVANCE region — with NO case split.  This is
    the scalar-head CONS cell's whole dispatch: `g.win_lo` + `…cons_boundary_delta` → ADVANCE. -/
theorem degenerate_advance_only (off a : Nat) (h_lo : off + 1 ≤ a) (h_ne : a ≠ off + 1) :
    off + 1 < a := by omega

/-! ## NEGATIVE — why LEAF and DESCEND are not merely unused but UNREACHABLE at the minimum. -/

/-- At `L = 1` the LEAF position `a = off+1` and the boundary `a = off+L` are the SAME point, so the
    boundary exclusion makes the LEAF arm contradictory — unreachable, not just unused.  (Contrast the
    generic case where LEAF and boundary are distinct points.) -/
theorem degenerate_leaf_is_boundary (off a : Nat) (h_leaf : a = off + 1) (h_ne : a ≠ off + 1) :
    False := by omega

/-- The DESCEND interval empties already at `L = 2` (and a fortiori at `L = 1`): `(off+1, off+2)` has
    no integer interior, so the DESCEND arm is vacuous below `L = 3`. -/
theorem descend_empty_at_2 (off a : Nat) (h : off + 1 < a ∧ a < off + 2) : False := by omega
theorem descend_empty_at_1 (off a : Nat) (h : off + 1 < a ∧ a < off + 1) : False := by omega

/-- The reachable-arm count as a function of the metric `L` — a DECREASING function, not a constant 3.
    `L ≥ 3 → 3` (LEAF+DESCEND+ADVANCE), `L = 2 → 2` (LEAF+ADVANCE), `L = 1 → 1` (ADVANCE). -/
def reachableArms (L : Nat) : Nat := if L = 1 then 1 else if L = 2 then 2 else 3

#guard reachableArms 1 == 1    -- scalar: straight-line ADVANCE
#guard reachableArms 2 == 2    -- empty seq: LEAF + ADVANCE (DESCEND vacuous)
#guard reachableArms 3 == 3    -- minimal nonempty seq: all three
#guard reachableArms 4 == 3    -- nonempty seq: all three
#guard !decide (reachableArms 1 == 3)    -- the minimum is NOT the generic arm-count

end Tests.Reflections.MetricMinimumCollapsesDispatch
