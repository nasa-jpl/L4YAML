/-!
# Reflection 496 — the climbing dropped-derivation premise (R494) does NOT re-emerge above its
case-split terminus (R495): the terminating ancestor is an ABSORPTION boundary, so the lift ABOVE it
reverts to a pure guard-keyed-name re-key — premise-free, no case split.

Self-contained (core Lean, no `L4YAML` import) toy recording the structure step surfaced while landing
`seqLocalCarrier_of_widthEnc_seq` — the `FlowBodyContentDeepSeq`-keyed twin of
`seqLocalCarrier_of_widthEnc`, the consumer-chain link ABOVE the R495 descent provider twin
`seqDescent_provider_of_located_seq` in the `_seq` re-thread
(`seqLocalCarrier_of_widthEnc → seqDescent_provider_of_located → seqChild_safeBodyUnit →
recseqentry_seqbracket_oracle`).

**The setup (R494/R495 recap).**  Re-keying the seq consumer chain off the root-FALSE strong content
guard `FlowBodyContentDeep` onto its root-TRUE weaker twin `FlowBodyContentDeepSeq`, a non-emptiness
fact `h_ne` (which the strong guard self-derived but the weak guard takes as a premise) CLIMBED the lift
chain ([[LiftForwardsDroppedDerivationPremise]], R494) and TERMINATED at a CASE SPLIT
([[ClimbingPremiseTerminatesAtCaseSplit]], R495): the terminating ancestor `seqDescent_provider_of_located_seq`
case-splits on the discriminator the strong guard had encoded (`p + 1 < j`), sources `h_ne` on the
non-degenerate arm, and produces the deliverable VACUOUSLY on the degenerate empty-seq arm the weaker
guard admits.

**The find — the terminus is an ABSORPTION boundary; the lift above it is CLEAN again.**  The key fact
about a case-split terminus is that its CONCLUSION is premise-FREE: having internalised the case split,
`seqDescent_provider_of_located_seq` produces the descent existential from `WeakG`-family hypotheses
alone, with NO `h_ne` in its signature.  So the lift ABOVE it (`seqLocalCarrier_of_widthEnc_seq`) sees a
clean premise-free interface — it has NO `h_ne` to forward and NO degenerate case to restore.  The lift
therefore reverts to the pure [[LiftRekeysByGuardKeyedChildNames]] form (R493): one NAME swap per
guard-KEYED child (`seqDescent_provider_of_located ↦ _seq`, the lone guard-keyed call; the locate and
the `SeqEnclosed (p+1)` seed are guard-neutral), with the body otherwise term-for-term the strong
parent.  The climbing premise does NOT propagate past the terminus — that is exactly the VALUE of the
terminus: it RESTORES a clean interface upward.

So a climbing dropped-derivation premise has a single ABSORPTION point (its case-split terminus), below
which the chain forwards it and above which the chain is premise-free.  Once you have located the
terminating ancestor, you can STOP tracking the premise upward.

Below, the strong family (`StrongG`, `terminate_strong`, `localCarrier_strong`) and the seq family
(`WeakG`, `terminate_seq`, `localCarrier_seq`) are built in parallel.  `terminate_seq` is the R495
absorbing terminus (case-splits, premise-free conclusion); `localCarrier_seq` is THE BRICK — the strong
carrier with one guard-keyed name swap and the guard re-keyed `StrongG ↦ WeakG`, NO `h_ne` premise, NO
case split.  `degenerate_flows_through_clean_carrier` re-exhibits R494's un-sourceability witness
(`WeakG 0` holds while `NE 0` fails) AND shows the carrier still produces `Goal 0` premise-free — the
degenerate input reaches the carrier yet the carrier is clean, because the terminus absorbed it.

Axiom note: every theorem here is `[propext, Quot.sound]` at most (the discriminator `D` is DECIDABLE so
`by_cases` adds no `Classical.choice`; `propext`/`Quot.sound` come from `omega`), strictly LIGHTER than
the real lemma's `[propext, Classical.choice, Quot.sound]`.  As in R495 the real lemma's
`Classical.choice` is INHERITED from the deeper locator machinery it transports, not from this lift's own
(absent) case split — the lift adds neither a branch nor an axiom over its descent child.
-/

namespace PremiseAbsorbedAboveTerminusCleanLift

set_option autoImplicit false

/-! ### The deliverable, the two guards, and the dropped-derivation premise (carried from R494/R495). -/

/-- The non-emptiness fact (toy `tokens[p+1]! ≠ .flowSequenceEnd`): the strong guard self-derives it, the
    weak twin takes it as a premise. -/
abbrev NE (n : Nat) : Prop := 1 ≤ n
/-- The leaf oracle's packaged per-element fact (toy `SafeBodyUnit` content). -/
abbrev Packaged (n : Nat) : Prop := 0 < n
/-- The windowed deliverable (toy provider existential's separator facts): VACUOUS for `n < 2`. -/
abbrev Goal (n : Nat) : Prop := ∀ k, k + 1 < n → Packaged n

/-- STRONG guard (toy `FlowBodyContentDeep`): the opener fires UNCONDITIONALLY, self-deriving `NE`;
    root-FALSE for the degenerate input (no `StrongG 0`). -/
structure StrongG (n : Nat) : Prop where
  /-- the unconditional opener field. -/
  opener : NE n
/-- WEAK seq-gated guard (toy `FlowBodyContentDeepSeq`): the opener field is GATED by the very
    non-emptiness it would conclude, so it holds EVEN for the degenerate input (`WeakG 0`). -/
structure WeakG (n : Nat) : Prop where
  /-- the seq-gated opener field — `NE` in ⇒ `NE` out; useless for DERIVING `NE`. -/
  openerGated : NE n → NE n

/-! ### The two terminating ancestors — both produce `Goal` PREMISE-FREE (R495's absorption). -/

/-- STRONG terminating ancestor (toy `seqDescent_provider_of_located`): the strong opener self-derives
    `NE`, so it produces `Goal` directly — premise-free, NO case split (the strong guard excludes the
    degenerate input the case split would handle). -/
theorem terminate_strong (n : Nat) (hg : StrongG n) : Goal n :=
  fun _ _ => hg.opener

/-- The internal discriminator the STRONG guard had ENCODED — toy `p + 1 < j` (the enclosing seq is
    non-empty).  The weak terminus RE-DISCOVERS it and case-splits on it. -/
abbrev D (n : Nat) : Prop := 2 ≤ n
/-- The discriminator SOURCES the climbing premise on the non-degenerate arm. -/
theorem ne_of_D (n : Nat) (h : D n) : NE n := Nat.le_of_succ_le h

/-- WEAK (seq) terminating ancestor (toy `seqDescent_provider_of_located_seq`, R495).  ABSORBS the
    climbing premise by CASE-SPLITTING on `D`: sources `NE` on the non-degenerate arm, produces `Goal`
    VACUOUSLY on the degenerate arm.  Crucially its CONCLUSION is premise-FREE — SAME `(hg : WeakG n) :
    Goal n` interface as the strong terminus, no `h_ne` argument.  THIS is the absorption boundary. -/
theorem terminate_seq (n : Nat) (_hg : WeakG n) : Goal n := by
  by_cases hD : D n
  · -- non-degenerate: source the premise on the discriminator.
    exact fun _ _ => ne_of_D n hD
  · -- degenerate (`n < 2`): `Goal` vacuous; the leaf is bypassed.
    intro k hk
    omega

/-! ### The lift ABOVE the terminus — a CLEAN re-key (R496, THE BRICK). -/

/-- The window-local plumbing the carrier carries (toy `h_safe`) — guard-NEUTRAL, transported verbatim. -/
abbrev Safe (_n : Nat) : Prop := True

/-- STRONG local carrier (toy `seqLocalCarrier_of_widthEnc`): a LIFT that transports its guard to the
    strong terminus.  The lone guard-KEYED child is `terminate_strong`; `Safe` is guard-neutral. -/
theorem localCarrier_strong (n : Nat) (_h_safe : Safe n) (hg : StrongG n) : Goal n :=
  terminate_strong n hg

/-- **THE BRICK** (toy `seqLocalCarrier_of_widthEnc_seq`, R496).  The SEQ local carrier is the strong
    carrier with ONE guard-keyed name swap (`terminate_strong ↦ terminate_seq`) and the guard re-keyed
    `StrongG ↦ WeakG`.  There is NO `h_ne` premise to forward and NO case split HERE — the terminus
    `terminate_seq` already ABSORBED the climbing premise, so it presents a clean premise-free interface
    upward.  The lift is a pure [[LiftRekeysByGuardKeyedChildNames]] re-key: its signature matches
    `localCarrier_strong` exactly but for the guard name.  (That this typechecks taking only `WeakG`,
    with no `NE` argument, IS the proof the premise did not re-emerge.) -/
theorem localCarrier_seq (n : Nat) (_h_safe : Safe n) (hg : WeakG n) : Goal n :=
  terminate_seq n hg

/-! ### Why the lift stays clean: the degenerate input reaches the carrier, yet no premise is owed. -/

/-- The degenerate input the WEAK guard ADMITS (R494's un-sourceability witness): `WeakG 0` holds, yet
    `NE 0` is FALSE.  It reaches the carrier through `terminate_seq` — and the carrier STILL produces
    `Goal 0`, premise-free, because the terminus absorbed the case split.  This is the absorption
    boundary made concrete: below it the premise is forwarded, AT it the premise is discharged by a case
    split, ABOVE it (here) the interface is clean. -/
theorem degenerate_flows_through_clean_carrier : WeakG 0 ∧ ¬ NE 0 ∧ Goal 0 :=
  ⟨⟨id⟩, Nat.not_succ_le_zero 0, localCarrier_seq 0 trivial ⟨id⟩⟩

/-- The seq carrier on a non-degenerate input — `Goal` through the (absorbed) terminus, the carrier
    itself adding nothing. -/
example : Goal 3 := localCarrier_seq 3 trivial ⟨id⟩

/-- And the strong carrier, for the parallel: the SAME lift shape, one name + guard swap away. -/
example : Goal 3 := localCarrier_strong 3 trivial ⟨Nat.le_of_succ_le (by omega)⟩

end PremiseAbsorbedAboveTerminusCleanLift
