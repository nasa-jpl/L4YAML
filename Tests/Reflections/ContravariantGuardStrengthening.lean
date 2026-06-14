/-!
# Reflection 434 — a refutation-driven guard-strengthening threads contravariantly: producer-first

Self-contained (core Lean, no `L4YAML` import) toy of the R434 step.

Context.  R433 refuted a per-window universal `∀ window, (guards) → Deliverable window` by exhibiting a
guard-satisfying window the deliverable can't inhabit; the fix is to ADD a guard `H` (the Dyck floor) that
excludes it.  That universal flows across a PRODUCER → CONSUMER boundary: a producer CONCLUDES it (from its
own `windowFacts`-style hypothesis), a consumer HYPOTHESIZES it (and instantiates it at located windows).

The finding.  The added guard must be applied at BOTH ends, and the two ends have OPPOSITE cost, by the
contravariance of `→`:

* PRODUCER (concludes `∀ x, G x → Deliv x`): adding `H` to the conclusion is FREE.  The producer RECEIVES
  the new premise `H x` on its conclusion side and passes it straight to its own hypothesis (which also
  gains `H`).  Pure threading — no new proof obligation.
* CONSUMER (hypothesizes `∀ x, G x → Deliv x`): adding `H` makes the hypothesis WEAKER, so at every
  instantiation the consumer must now SUPPLY `H x`.  That is the real work.

So do the PRODUCER side first (free — it pins the guard's exact shape), then pay for the CONSUMER side.

The toy below: a producer that threads the new guard `H` for free, and a consumer that must manufacture
`H 3` to instantiate the strengthened hypothesis.
-/

namespace Tests.Reflections.ContravariantGuardStrengthening

set_option autoImplicit false

/-- The original guard. -/
abbrev G (x : Nat) : Prop := 1 ≤ x
/-- The ADDED guard (the toy of the Dyck floor that excludes the cross-matched false window). -/
abbrev H (x : Nat) : Prop := x ≤ 10
/-- The per-window deliverable. -/
abbrev Deliv (x : Nat) : Prop := x * x ≤ 100

/-! ## Producer side — adding the guard is FREE (pure threading). -/

/-- **Producer, strengthened.**  Concludes the FLOORED universal `∀ x, G x → H x → Deliv x` from a floored
    `windowFacts`-style hypothesis.  The new guard `hh : H x` arrives on the conclusion side and is passed
    straight to `wf` — no new obligation.  (Toy of `seqRec_of_carrier_and_windowFacts_seq`'s floor: `intro
    … hopen hfloor; … windowFacts … hfloor`.) -/
theorem producer_floored (wf : ∀ x, G x → H x → Deliv x) :
    ∀ x, G x → H x → Deliv x :=
  fun x hg hh => wf x hg hh

/-! ## Consumer side — adding the guard COSTS (must supply it at each instantiation). -/

/-- **Consumer, strengthened.**  Hypothesizes the FLOORED universal; to instantiate it at `x = 3` it must
    now MANUFACTURE `H 3` (`3 ≤ 10`) in addition to `G 3`.  That extra `(by decide : H 3)` is the cost the
    contravariant guard pushes onto the consumer — the real work the next brick pays for at
    `flowSubrangesOk_of_window_producers` / `seqLocator_of_window_recseqbody`. -/
theorem consumer_floored (hyp : ∀ x, G x → H x → Deliv x) : Deliv 3 :=
  hyp 3 (by decide) (by decide)

/-- The asymmetry made concrete: the producer NEVER constructs an `H`; the consumer MUST supply BOTH
    guards at the instantiation point.  These are exactly the obligations `consumer_floored` discharges. -/
theorem consumer_obligations : G 3 ∧ H 3 := ⟨by decide, by decide⟩

end Tests.Reflections.ContravariantGuardStrengthening
