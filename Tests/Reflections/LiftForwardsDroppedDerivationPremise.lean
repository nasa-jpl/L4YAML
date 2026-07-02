/-!
# Reflection 494 — a transporting LIFT's re-key cost is #(guard-keyed child names) PLUS the child
twin's DROPPED-DERIVATION premise.  When the weaker guard can no longer SELF-DERIVE a fact the strong
guard gave for free, the leaf twin takes that fact as a new premise — and every LIFT above it must
FORWARD the premise, because the leaf cannot SOURCE it locally.

Self-contained (core Lean, no `L4YAML` import) toy recording the structure step surfaced while landing
`seqChild_safeBodyUnit_seq` — the `FlowBodyContentDeepSeq`-keyed twin of `seqChild_safeBodyUnit`, the
bottom-most missing link of the `_seq` re-thread's CONSUMER chain
(`seqLocalCarrier_of_widthEnc → seqDescent_provider_of_located → seqChild_safeBodyUnit →
recseqentry_seqbracket_oracle`), below the width-enc producer LIFT `seqWidthEnc_of_recIH_seq` (R493).

**The setup.**  The `_seq` re-thread ([[RethreadStaysInWeakerTwinFamily]], R489; seeded per
[[RootSeedNeedsRootTrueGuard]], R488) re-keys the seq carrier chain off the root-FALSE strong content
guard `FlowBodyContentDeep` onto its root-TRUE weaker twin `FlowBodyContentDeepSeq`.  R493
([[LiftRekeysByGuardKeyedChildNames]]) priced a LIFT's re-key at #(guard-keyed child names it invokes):
a transporting child's call still swaps its NAME at the parent, because a name is a guard-typed
reference.  `seqChild_safeBodyUnit` is exactly such a transporting LIFT — its body is ONE call to
`recseqentry_seqbracket_oracle` then `.1.toSafeBodyUnit`, reading no deep field.  By R493 its twin
should cost ONE name swap.  It does — PLUS one thing R493 did not yet name.

**The find — the weaker twin's DROPPED self-derivation climbs the whole lift chain.**  The strong leaf
`recseqentry_seqbracket_oracle` SELF-DERIVED interior non-emptiness (`tokens[lo+1] ≠ .flowSequenceEnd`)
from `FlowBodyContentDeep.openerContentStart`, which fires at EVERY delta-`1` opener.  The weaker
`FlowBodyContentDeepSeq.openerContentStart` is GUARDED by that very non-emptiness, so the leaf twin
`recseqentry_seqbracket_oracle_seq` (R415) cannot self-derive it and takes it as a SUPPLIED premise
`h_ne` — a STRICTLY LARGER signature.  A LIFT that calls the leaf twin must therefore FORWARD `h_ne`.
So the re-key cost gains a second term:

  cost(re-key a LIFT) = #(guard-keyed child names)  +  #(child-twin premises the weaker guard FORCED
                        that this lift must forward).         [R494: 1 keyed name + 1 forwarded `h_ne`]

**Why the premise CLIMBS — the leaf cannot SOURCE it.**  The degenerate input (the empty seq `[]`:
`j = p+1`, `tokens[p+1]! = .flowSequenceEnd`) satisfies EVERY non-`h_ne` hypothesis of the leaf, so no
local fact refutes it and `h_ne` is genuinely un-derivable at the leaf.  It propagates up the lift chain
until an ancestor knows the body is a GENUINE (gated, non-empty) seq and can source it
([[PrefixGateReconstructedFromBoundary]] / the dropped-derivation analogue of the reconstruct-in-place
discharge).  Below: `WeakG 0` holds (its field is the trivial `NE 0 → NE 0`) while `NE 0` is FALSE —
so no `WeakG`-only proof yields `h_ne`; the strong guard, by contrast, self-derives it.
-/

namespace LiftForwardsDroppedDerivationPremise

set_option autoImplicit false

/-! ### The non-emptiness fact, the deliverable, and the two guard families. -/

/-- The non-emptiness fact the strong guard self-derives (toy `tokens[lo+1]! ≠ .flowSequenceEnd`). -/
abbrev NE (n : Nat) : Prop := 1 ≤ n
/-- The leaf oracle's deliverable (toy `RecSeqBody`). -/
abbrev Deliverable (n : Nat) : Prop := 0 < n
/-- The lift's packaged deliverable (toy `SafeBodyUnit`); the wrapper is a guard-neutral projection. -/
abbrev Packaged (n : Nat) : Prop := 0 < n

/-- The STRONG guard (toy `FlowBodyContentDeep`): its opener field fires UNCONDITIONALLY, so it
    SELF-DERIVES non-emptiness with no extra premise. -/
structure StrongG (n : Nat) : Prop where
  /-- the all-depth opener field — gives `NE` for free. -/
  opener : 2 ≤ n

/-- The WEAK seq-gated guard (toy `FlowBodyContentDeepSeq`): its opener field is GUARDED by the very
    non-emptiness it would conclude (`NE → NE`), so it CANNOT self-derive `NE`. -/
structure WeakG (n : Nat) : Prop where
  /-- the seq-gated opener field — `NE` in ⇒ `NE` out; useless for DERIVING `NE`. -/
  openerGated : NE n → NE n

/-! ### The leaf oracle: strong self-derives NE; weak takes it as a premise (the larger signature). -/

/-- **Strong leaf** (toy `recseqentry_seqbracket_oracle`).  Derives `NE` internally from the strong
    guard's unconditional opener field, so it needs NO `h_ne`. -/
theorem oracle_strong (n : Nat) (hg : StrongG n) : Deliverable n :=
  Nat.le_of_succ_le hg.opener

/-- **Weak leaf** (toy `recseqentry_seqbracket_oracle_seq`, R415).  The gated guard cannot self-derive
    `NE`, so non-emptiness is a SUPPLIED premise `h_ne` — the strictly-larger signature. -/
theorem oracle_seq (n : Nat) (_hg : WeakG n) (h_ne : NE n) : Deliverable n := h_ne

/-! ### The guard-neutral wrapper (toy `.1.toSafeBodyUnit`) — identical in both lift versions. -/

/-- Guard-neutral post-processing: projects the oracle's `Deliverable` to the lift's `Packaged` form;
    touches no guard, so it is character-for-character the same in the twin. -/
theorem wrap (n : Nat) (h : Deliverable n) : Packaged n := h

/-! ### The LIFT and its twin — ONE name swap + FORWARD the dropped-derivation premise. -/

/-- **The strong LIFT** (toy `seqChild_safeBodyUnit`).  Pure transport: ONE call to the leaf oracle,
    then the guard-neutral wrapper.  Reads NO guard field — `hg` is passed straight through. -/
theorem lift_strong (n : Nat) (hg : StrongG n) : Packaged n :=
  wrap n (oracle_strong n hg)

/-- **THE BRICK** (toy `seqChild_safeBodyUnit_seq`, R494).  The `_seq` re-key.  TWO edits:
    (1) the ONE guard-keyed child name `oracle_strong ↦ oracle_seq` (R493);
    (2) FORWARD the new `h_ne` premise the weak leaf demands (the dropped self-derivation, R494).
    The guard-neutral `wrap` call is verbatim. -/
theorem lift_seq (n : Nat) (hg : WeakG n) (h_ne : NE n) : Packaged n :=
  wrap n (oracle_seq n hg h_ne)

/-! ### Why the forwarded premise is genuine: the leaf cannot SOURCE it. -/

/-- The STRONG guard self-derives `NE` (no premise) — the capability the weak twin lost. -/
theorem strongG_derives_ne (n : Nat) (hg : StrongG n) : NE n := Nat.le_of_succ_le hg.opener

/-- **The leaf cannot SOURCE `h_ne`** — the degenerate input (toy empty seq `[]`) where the lift's
    guard holds but `NE` FAILS.  `WeakG 0` holds (its field is the trivial `NE 0 → NE 0`), yet `NE 0`
    is FALSE — so no `WeakG`-only proof yields `h_ne`; it must be forwarded until an ancestor that knows
    the body is non-empty can source it. -/
theorem weakG_holds_but_ne_fails : WeakG 0 ∧ ¬ NE 0 :=
  ⟨⟨id⟩, Nat.not_succ_le_zero 0⟩

/-- The count made explicit: re-keying `lift_strong` to `lift_seq` swapped ONE guard-keyed child name
    and FORWARDED ONE new premise the weaker leaf forced; the guard-neutral `wrap` was free.
    cost = 1 keyed name + 1 forwarded premise. -/
example (n : Nat) (hg : WeakG n) (h_ne : NE n) : Packaged n :=
  lift_seq n hg h_ne

end LiftForwardsDroppedDerivationPremise
