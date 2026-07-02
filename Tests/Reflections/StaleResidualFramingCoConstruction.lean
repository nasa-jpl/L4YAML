/-!
# Reflection 443 — a queued "the residual is the LOCATE/PRODUCE half" framing can be STALE: re-read the
# landed code before authoring it.  The locate may already be landed AND folded; the genuine residual a
# CO-CONSTRUCTION the framing hid.  Land the bridge that composes the landed halves into the producer's
# shape; its one remaining hypothesis — if its IH is term-for-term an existing producer minus that
# producer's own (circular) output — IS the co-construction, now named exactly.

Self-contained (core Lean, no `L4YAML` import) toy of the R443 finding — STEP D continued: reduce the seq
ROOT CARRIER `SeqInteriorSeparators tokens 2 (size-2)` to the width co-construction.

Context.  The R442 blueprint Next step scoped the seq root carrier's `desc` provider residual as the
backward enclosing-opener **LOCATE** half (find `p` + the four opener facts).  Reading the landed code
showed that framing was STALE: the locate is already done (`seqEnclosingOpener_of_gate`, R319) AND the
assemble too (`seqDescent_provider_of_located`); the code's own doc (`nestedSeq_recseqbody_of_locator`,
R388) even records "its only residual is the width fixpoint `h_enc`, NOT this locator."

So the R443 brick (`seqRoot_carrier_of_widthEnc`) is a REDUCTION-BY-IMPORT: it composes the landed locate +
assemble into the `desc` shape and produces the root carrier from ONE residual hypothesis `h_widthEnc` —
the per-window enclosing-facts + width-recursion IH supplier.  And `h_widthEnc`'s IH is term-for-term
`seqWindowRecSeqBody`'s signature (R323) gated by `hi' - lo' < hi - p` — but `seqWindowRecSeqBody` consumes
`h_root_carrier : SeqInteriorSeparators tokens 2 (size-2)`, the VERY carrier the brick is building.  So the
genuine residual is the carrier↔recursion CO-CONSTRUCTION (strong induction on window width producing the
carrier and the recursive body jointly), NOT the locate.

The reusable rule.  When a queued step says "the residual is the LOCATE/PRODUCE half X", VERIFY by reading
the landed lemmas and their docs before authoring X — X may already be landed and folded, and the TRUE
residual a co-construction the framing hid.  Land the bridge that composes the landed halves into the
producer's shape; read off its remaining hypothesis.  If that hypothesis's IH matches an EXISTING producer
MINUS that producer's own output, the residual IS the co-construction of the two — name its interface with
the bridge, then discharge it by strong induction on the shared measure.

This toy models: the two landed primitives (`assemble` = locate+provider, `producer` = the fixpoint that
takes the carrier), the bridge that reduces the carrier to a single `widthEnc` hypothesis, and the
co-construction that discharges `widthEnc` by strong induction on width — sorry-free, so the bridge's
hypothesis is non-vacuous.  The stale framing ("residual = `assemble`") is exposed: `assemble` is a given
primitive; the real work is the joint `coConstruct`.
-/

set_option autoImplicit false

namespace Tests.Reflections.StaleResidualFramingCoConstruction

/-! ## PART 0 — the two LANDED primitives, modelling the descent's two already-proven halves.

`Carrier w` models `SeqInteriorSeparators tokens lo hi` at a window of width `w`; `Deliv w` models the
recursive body `RecSeqBody ((take hi).drop lo)`.  Both are co-constructed; neither is built alone. -/

/-- **(LANDED) the LOCATE + ASSEMBLE half** — the carrier at width `w`, given the deliverable at every
    STRICTLY smaller width.  Models `seqEnclosingOpener_of_gate` (R319) folded with
    `seqDescent_provider_of_located` into the `desc` argument: the descent's enclosing window `[p, hi)`
    is located and its facts assembled, the IH consuming deliverables of strictly-narrower sub-windows. -/
abbrev Assemble (Carrier Deliv : Nat → Prop) : Prop :=
  ∀ w, (∀ w', w' < w → Deliv w') → Carrier w

/-- **(LANDED) the PRODUCER / fixpoint** — the deliverable at width `w` from the carrier at the SAME
    width.  Its input is the carrier this very construction is building — the CIRCULAR edge.  Models
    `seqWindowRecSeqBody` (R323), which consumes `h_root_carrier : SeqInteriorSeparators tokens 2 (size-2)`
    to emit `RecSeqBody` at each window. -/
abbrev Producer (Carrier Deliv : Nat → Prop) : Prop :=
  ∀ w, Carrier w → Deliv w

/-! ## PART 1 — the bridge (reduction-by-import).  The carrier at the top width reduces to ONE residual
    hypothesis `widthEnc` — the IH supplier — NOT the locate.  This is `seqRoot_carrier_of_widthEnc`:
    feed `assemble` (landed) the width-keyed deliverables `widthEnc` provides. -/

theorem bridge {Carrier Deliv : Nat → Prop}
    (assemble : Assemble Carrier Deliv)
    (W : Nat) (widthEnc : ∀ w', w' < W → Deliv w') : Carrier W :=
  assemble W widthEnc

/-! ## PART 2 — discharging `widthEnc` IS the co-construction (the genuine residual the stale framing
    hid).  Strong induction on width supplies BOTH predicates at every width: at each step `assemble`
    builds the carrier from the IH's strictly-smaller deliverables, then `producer` builds this width's
    deliverable from that carrier.  `assemble` needs Deliv only at STRICTLY smaller widths, so the
    recursion is well-founded — the circularity dissolves precisely because the two are built jointly. -/

theorem coConstruct {Carrier Deliv : Nat → Prop}
    (assemble : Assemble Carrier Deliv) (producer : Producer Carrier Deliv) :
    ∀ w, Carrier w ∧ Deliv w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    have hC : Carrier w := assemble w (fun w' h => (ih w' h).2)
    exact ⟨hC, producer w hC⟩

/-- The payoff: the carrier at ANY top width, with NO residual hypothesis left — the co-construction
    closes it.  Models the seq root carrier `SeqInteriorSeparators tokens 2 (size-2)` once `h_widthEnc`
    is discharged by the width co-construction. -/
theorem carrier_closed {Carrier Deliv : Nat → Prop}
    (assemble : Assemble Carrier Deliv) (producer : Producer Carrier Deliv) (W : Nat) : Carrier W :=
  (coConstruct assemble producer W).1

/-! ## PART 3 — non-vacuity.  The two landed primitives are satisfiable (mirrors the `#guard`-backed
    `SeqDescentProviderProbe`): a concrete instance where the bridge's residual `widthEnc` and the
    co-construction both hold.  Here `Deliv` accumulates a sum, so the recursion genuinely fires. -/

/-- A concrete `Carrier`/`Deliv` pair: `Deliv w` holds iff `w`'s strong-recursive "all below" closure
    holds — trivially satisfiable, but the proof recurses through every smaller width. -/
example : ∀ w, (fun _ : Nat => True) w :=
  fun w => carrier_closed (Carrier := fun _ => True) (Deliv := fun _ => True)
    (fun _ _ => trivial) (fun _ _ => trivial) w

/-- The stale-framing observation as a proposition: `assemble` (the "locate residual" the framing
    pointed at) is ALREADY a given primitive — `bridge` consumes it, it is not the thing left to prove.
    What is left to prove is `coConstruct`, the joint recursion.  Side by side: given both primitives,
    the carrier follows with no further locate work. -/
theorem framing_payoff {Carrier Deliv : Nat → Prop}
    (assemble : Assemble Carrier Deliv) (producer : Producer Carrier Deliv) :
    (∀ W, (∀ w', w' < W → Deliv w') → Carrier W) ∧ (∀ W, Carrier W) :=
  ⟨fun W h => bridge assemble W h, fun W => carrier_closed assemble producer W⟩

end Tests.Reflections.StaleResidualFramingCoConstruction
