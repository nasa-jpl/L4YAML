/-!
# Reflection 490 — a guard RE-SCOPE that demotes a PROJECTED field to a UNIFIED residual can SIMPLIFY the
downstream consumer: the unified residual routes through ONE invariant the consumer already holds, shedding
the strong twin's boundary-specific hypothesis.

Self-contained (core Lean, no `L4YAML` import) toy recording the discharge structure that step γ′ surfaced
while landing `flowBodyContent_child_bracket_seq` (the content child-bracket `_seq` twin of
`flowBodyContent_child_bracket`, consuming R489's `flowBodyContentDeepSeq_child_bracket` +
`flowBodyContent_of_deepSeq`).

**The setup.**  Continuing the `_seq` re-thread ([[RethreadStaysInWeakerTwinFamily]], R489): the seq carrier
chain is seeded with the root-TRUE weaker guard `FlowBodyContentDeepSeq`, so each child producer needs a
`_seq` twin.  This turn's twin assembles the depth-`0` `FlowBodyContent` at the child bracket from that weaker
guard via `flowBodyContent_of_deepSeq`.

**The find — the re-scope SIMPLIFIES the consumer.**  The STRONG assembler `flowBodyContent_of_deep` SPLITS
the per-separator obligation into an INTERIOR branch (projected straight off the guard's all-depth,
unguarded `feContentStart`) and a BOUNDARY branch (a named residual `noTrailingSep`, discharged at the window
CLOSE).  The re-scoped guard's `feContentStart` is GATED (`tokens[k+1] ≠ .key`), so the consumer cannot
project the interior either — and `flowBodyContent_of_deepSeq` therefore UNIFIES both into a SINGLE residual
`feContent` (interior AND boundary, carrying the `balance = 0` premise).

This looks like an added consumer burden (an unprojectable interior).  But at THIS consumer — the child
bracket `[k, j+1)` — the unified residual routes through ONE invariant the consumer ALREADY holds: the
child-bracket FLOOR `balance k i ≥ 1` for `k+1 ≤ i ≤ j`.  The floor's range REACHES the close position `j`,
so it kills EVERY balance-`0` separator with `k' > k` (interior AND boundary), and the typed opener kills
`k' = k`.  The boundary CLOSE-contradiction the strong twin needed is SUBSUMED by the floor — so the close
hypothesis (`h_jclose`) is REDUNDANT and DROPPED from the twin's signature.

**The transferable rule.**  When a guard re-scope demotes a guard-PROJECTED field to a UNIFIED named residual
(merging cases the strong form split), check whether the consumer holds a SINGLE invariant strong enough to
discharge the whole residual.  If so, the re-scope is not a complication but a SIMPLIFICATION: routing the
unified residual through that one invariant DECOUPLES the discharge from the per-case hypotheses the split
required (the guard projection AND the boundary marker), letting you SHED the boundary-specific hypothesis.
The re-scope's apparent cost is paid by an invariant the consumer holds anyway — and the payment is cheaper
than the strong split.

This toy models a child bracket `[k, j+1) = [0, 4)` (opener `0`, close `j = 3`), the floor the consumer
holds (range `[1, 3]`, REACHING the close), the STRONG split discharge (interior via a guard projection,
boundary via a close marker — both consumed), and the WEAK unified discharge (the whole residual killed by
the floor + opener — NEITHER the guard projection NOR the close marker consumed).
-/

namespace UnifiedResidualRoutesThroughOneInvariant

set_option autoImplicit false

/-! ### The toy child bracket `[k, j+1) = [0, 4)`: opener at `0`, close at `j = 3`. -/

/-- toy "balance from the child origin `k = 0`": `0` at the origin, `≥ 1` strictly inside `[1, 3]` (the
    floor's range — note it REACHES the close position `3`), `0` again past the close. -/
def bal (i : Nat) : Int := if 1 ≤ i ∧ i ≤ 3 then 1 else 0

/-- toy "position `k'` is a separator" (`tokens[k'] = .flowEntry`).  Concretely position `7` — i.e. NOTHING
    in the window `[0, 4)` is a separator, so every residual clause discharges vacuously. -/
abbrev Sep (k' : Nat) : Prop := k' = 7

/-- toy per-separator conclusion "content-start at `k'+1`" — ARBITRARY (never reached under the floor). -/
abbrev CS (n : Nat) : Prop := n = 99

/-! ### The ONE invariant the consumer holds: the child-bracket FLOOR. -/

/-- The child-bracket floor: strictly inside `[k+1, j] = [1, 3]`, balance `≥ 1`.  Its range REACHES the
    close position `j = 3` — the fact that lets it subsume the boundary case and shed the close marker. -/
theorem floor : ∀ i, 1 ≤ i → i ≤ 3 → bal i ≥ 1 := by
  intro i h1 h2
  have : bal i = 1 := if_pos (And.intro h1 h2)   -- constructive `if_pos`, no `Classical`
  omega

/-- The typed opener `tokens[0] = .flowSequenceStart` is NOT a separator. -/
theorem opener_not_sep : ¬ Sep 0 := by decide

/-! ### STRONG split — the original `flowBodyContent_of_deep` shape.
    Interior separators are PROJECTED from a guard; the boundary separator `k' = j` needs a CLOSE marker. -/

/-- A guard projection the STRONG consumer holds (toy `FlowBodyContentDeep.feContentStart`, all-depth and
    UNgated) — covers the INTERIOR `k' < j` only. -/
abbrev GuardProj : Prop := ∀ k', 0 ≤ k' → k' < 3 → Sep k' → CS (k' + 1)

/-- The CLOSE marker the STRONG consumer needs for the BOUNDARY case `k' = j` (`tokens[j]` is the close, not
    a separator). -/
abbrev Close : Prop := ¬ Sep 3

/-- STRONG discharge: interior `k' < 3` via the guard projection, boundary `k' = 3` via the close marker.
    BOTH `gp` and `cl` are consumed. -/
theorem strong_feContent (gp : GuardProj) (cl : Close) :
    ∀ k', 0 ≤ k' → k' < 4 → Sep k' → CS (k' + 1) := by
  intro k' h0 h4 hsep
  rcases Nat.lt_or_ge k' 3 with h | h
  · exact gp k' h0 h hsep            -- interior: the guard projection
  · have : k' = 3 := by omega
    subst this
    exact absurd hsep cl             -- boundary: the close marker

/-! ### WEAK unified — the re-scoped `flowBodyContent_of_deepSeq` shape.
    The gated guard is UNprojectable, so interior + boundary MERGE into one residual that also carries the
    `bal k' = 0` premise — and the consumer routes the WHOLE thing through the FLOOR, dropping `gp` AND `cl`. -/

/-- **THE BRICK (toy).**  WEAK discharge: the unified residual (interior AND boundary, plus the `bal k' = 0`
    premise) is killed by ONE invariant — the floor for `k' ≥ 1` (range `[1, 3]`, REACHING the close `3`),
    the opener for `k' = 0`.  Needs NEITHER the guard projection NOR the close marker: the floor's reach over
    the close position is exactly what sheds the boundary hypothesis the strong twin required. -/
theorem weak_feContent :
    ∀ k', 0 ≤ k' → k' < 4 → Sep k' → bal k' = 0 → CS (k' + 1) := by
  intro k' h0 h4 hsep hbal
  rcases Nat.lt_or_ge 0 k' with h | h
  · -- k' ≥ 1: the floor (reaching the close `3`) gives `bal k' ≥ 1`, contradicting `bal k' = 0`.
    have hf := floor k' (by omega) (by omega)
    exfalso; omega
  · -- k' = 0: the typed opener is not a separator.
    have : k' = 0 := by omega
    subst this
    exact absurd hsep opener_not_sep

/-- The shedding made explicit: the WEAK discharge holds with NO guard projection and NO close marker in
    scope — the unified residual is fully discharged by the floor + opener the consumer already holds. -/
example : ∀ k', 0 ≤ k' → k' < 4 → Sep k' → bal k' = 0 → CS (k' + 1) := weak_feContent

end UnifiedResidualRoutesThroughOneInvariant
