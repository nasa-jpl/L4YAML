/-!
# Reflection 545 companion — `omega` on a NON-arithmetic goal silently pulls `Classical.choice`

Self-contained demo of the axiom-hygiene lesson [[ref-omega-nonarith-goal-pulls-classical]], surfaced
while probing the R545 strict→robust map connector.

When the local hypotheses are arithmetically CONTRADICTORY, `omega` can close ANY goal — including one
that is not itself an arithmetic comparison — by deriving `False`. But when the goal it must produce is
NOT arithmetic, the proof term `omega` builds reaches for `Classical.choice`. Routing the same
contradiction through `absurd h (by omega)` — let `omega` prove only the *arithmetic* negation, let
`absurd`/`False.elim` fill the opaque goal — keeps the proof axiom-clean.

The practical upshot (R545): the non-vacuity probe for the map connector closed an
`isFlowContentStart …` goal from a refuted window-close-escape hypothesis. With `omega` the audit read
`[propext, Classical.choice, Quot.sound]`; with `absurd hesc (by omega)` it dropped to
`[propext, Quot.sound]` — which also CERTIFIED the connector itself was axiom-clean, since the only
`Classical` in the chain was the avoidable `omega`-on-`Prop`. Read the audit, then minimise the tactic.

This file imports nothing from the project — it is the principle in the small, on a bare opaque `Prop`.
-/

namespace OmegaNonArithGoalPullsClassical

/-- **The avoidable-`Classical` path.** The goal `Q` is an opaque `Prop` (not an arithmetic
    comparison), and the hypothesis `h : n + 5 ≤ n + 2` is arithmetically false. Closing the goal with
    `omega` directly works — but the proof term depends on `Classical.choice`, because `omega` must
    fabricate an inhabitant of the non-arithmetic `Q` from the contradiction. -/
theorem closeViaOmega (Q : Prop) (n : Nat) (h : n + 5 ≤ n + 2) : Q := by
  omega

/-- **The axiom-clean path.** Same hypotheses, same goal — but `omega` is asked only for the
    *arithmetic* fact it is good at (the negation `¬ (n + 5 ≤ n + 2)`), and `absurd` does the
    constructive goal-filling via `False.elim`. No `Classical.choice`. -/
theorem closeViaAbsurd (Q : Prop) (n : Nat) (h : n + 5 ≤ n + 2) : Q :=
  absurd h (by omega)

-- The two audits, side by side: the only difference is the tactic that closes the opaque goal.
-- `omega` fabricates the opaque `Q` via `Classical.choice`; `absurd` sheds it (the residual
-- `[propext, Quot.sound]` is `omega`'s own Nat/Int machinery for the arithmetic negation).
/-- info: 'OmegaNonArithGoalPullsClassical.closeViaOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms closeViaOmega

/-- info: 'OmegaNonArithGoalPullsClassical.closeViaAbsurd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms closeViaAbsurd

end OmegaNonArithGoalPullsClassical
