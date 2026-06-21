/-!
# Reflection 495 — the climbing dropped-derivation premise (R494) terminates at a CASE SPLIT, not a
single discharge, because the weaker guard ADMITS the degenerate input to the terminating ancestor too.

Self-contained (core Lean, no `L4YAML` import) toy recording the structure step surfaced while landing
`seqDescent_provider_of_located_seq` — the `FlowBodyContentDeepSeq`-keyed twin of
`seqDescent_provider_of_located`, the consumer-chain link ABOVE the R494 leaf lift
`seqChild_safeBodyUnit_seq` in the `_seq` re-thread
(`seqLocalCarrier_of_widthEnc → seqDescent_provider_of_located → seqChild_safeBodyUnit →
recseqentry_seqbracket_oracle`).

**The setup (R494 recap).**  Re-keying the seq consumer chain off the root-FALSE strong content guard
`FlowBodyContentDeep` onto its root-TRUE weaker twin `FlowBodyContentDeepSeq`, the strong leaf
SELF-DERIVED interior non-emptiness `h_ne` (its opener field fires UNCONDITIONALLY), whereas the weak
leaf's field is GUARDED by that very non-emptiness, so the leaf twin takes `h_ne` as a SUPPLIED premise.
[[LiftForwardsDroppedDerivationPremise]] (R494) showed the intermediate lift `seqChild_safeBodyUnit_seq`
FORWARDS `h_ne` (it cannot source it: the degenerate input satisfies the gate but not `NE`), so the
premise CLIMBS the lift chain "until an ancestor that knows the structure is non-degenerate can source
it."

**The find — the climb terminates at a CASE SPLIT, not a discharge.**  The ancestor predicted to SOURCE
the premise (`seqDescent_provider_of_located_seq`) cannot source it UNCONDITIONALLY, because the weaker
guard ADMITS the very degenerate input the strong guard's unconditional field excluded — an empty
enclosing seq `[ … [] … ]`, whose inner empty seq's gated window has `j = p+1` and `tokens[p+1]! =
.flowSequenceEnd` ⇒ `h_ne` is FALSE — and the dispatcher hands the descent provider windows with `a ≤ b`
(NOT `a < b`), so that degenerate input REACHES this ancestor.  The premise therefore terminates at a
CASE SPLIT on the discriminator the strong guard had ENCODED (`p + 1 < j`, the enclosing seq is
non-empty):

* non-degenerate (`p + 1 < j`): SOURCE `h_ne` from the re-discovered discriminator, then route through
  the R494 lift;
* degenerate (`j = p+1`): the gated window collapses to empty, the deliverable's facts are VACUOUS, so
  produce them DIRECTLY — BYPASSING the leaf the premise could not feed.

So the terminus of a climbing dropped-derivation premise is the first ancestor that can DISTINGUISH the
degenerate case, and distinguishing means HANDLING BOTH branches (source-in-non-degenerate +
vacuous-in-degenerate), not a single discharge.

Below, the toy ancestor `terminate` case-splits on the discriminator `D`; the non-degenerate branch
routes through the R494 lift `lift_seq` (which needs `h_ne`, sourced from `D`), and the degenerate
branch produces the (vacuous) `Goal` directly.  `degenerate_reaches_ancestor` re-exhibits R494's
un-sourceability witness (`WeakG 0` holds while `NE 0` fails), proving the degenerate input genuinely
reaches `terminate` and genuinely needs the bypass.  Axiom note: this toy's `terminate` is
`[propext, Quot.sound]` (the discriminator `D` is DECIDABLE, so `by_cases` uses the decidable instance —
no `Classical.choice`; `propext`/`Quot.sound` come from `omega`), strictly LIGHTER than the real lemma's
`[propext, Classical.choice, Quot.sound]`.  This is itself accurate to the architecture: the real
ancestor's `Classical.choice` does NOT come from its OWN case split (the discriminator `p + 1 < j` is
decidable too) — it is INHERITED from the deeper locator machinery the lemma transports (the
matching-close locator's `split`/`if` skeletons), the same `Classical.choice` its strong parent already
carries.  The case split adds a reachable branch, not an axiom.
-/

namespace ClimbingPremiseTerminatesAtCaseSplit

set_option autoImplicit false

/-! ### The non-emptiness premise, the deliverable, and the weak gate (carried from R494). -/

/-- The non-emptiness fact the strong guard self-derived; the weak twin takes it as a premise (toy
    `tokens[p+1]! ≠ .flowSequenceEnd`). -/
abbrev NE (n : Nat) : Prop := 1 ≤ n
/-- The leaf oracle's packaged deliverable (toy `SafeBodyUnit` of the genuine body). -/
abbrev Packaged (n : Nat) : Prop := 0 < n

/-- The WEAK seq-gated guard (toy `FlowBodyContentDeepSeq`): holds EVEN for the degenerate input
    (`WeakG 0`), because its opener field is gated by the very non-emptiness it would conclude. -/
structure WeakG (n : Nat) : Prop where
  /-- the seq-gated opener field — `NE` in ⇒ `NE` out; useless for DERIVING `NE`. -/
  openerGated : NE n → NE n

/-! ### The leaf and the intermediate lift (both forward `h_ne` — R415 / R494). -/

/-- **The leaf oracle twin** (toy `recseqentry_seqbracket_oracle_seq`, R415): the gated guard cannot
    self-derive `NE`, so non-emptiness is a SUPPLIED premise `h_ne`. -/
theorem oracle_seq (n : Nat) (_hg : WeakG n) (h_ne : NE n) : Packaged n := h_ne

/-- **The intermediate LIFT twin** (toy `seqChild_safeBodyUnit_seq`, R494): FORWARDS `h_ne` — it cannot
    source it locally (the degenerate input satisfies the gate but not `NE`), so the premise climbs. -/
theorem lift_seq (n : Nat) (hg : WeakG n) (h_ne : NE n) : Packaged n :=
  oracle_seq n hg h_ne

/-! ### The terminating ancestor (toy `seqDescent_provider_of_located_seq`, R495). -/

/-- The internal discriminator the STRONG guard had ENCODED — toy `p + 1 < j` (the enclosing seq is
    non-empty).  The terminating ancestor RE-DISCOVERS it from its own facts and case-splits on it. -/
abbrev D (n : Nat) : Prop := 2 ≤ n

/-- The discriminator SOURCES the climbing premise: a non-empty enclosing seq has non-empty interior
    (toy of "`p + 1 < j` ⇒ `tokens[p+1]! ≠ .flowSequenceEnd`" via the interior floor). -/
theorem ne_of_D (n : Nat) (h : D n) : NE n := Nat.le_of_succ_le h

/-- The ancestor's windowed deliverable (toy provider existential's separator facts): VACUOUS on the
    degenerate input — for `n < 2` there is no `k` with `k + 1 < n`, so it holds with NO premise. -/
abbrev Goal (n : Nat) : Prop := ∀ k, k + 1 < n → Packaged n

/-- **THE BRICK** (toy `seqDescent_provider_of_located_seq`, R495).  The climbing dropped-derivation
    premise `h_ne` (R494) terminates HERE — not at a single discharge, but at a CASE SPLIT, because the
    weaker `WeakG` admits the degenerate input (`WeakG 0` holds — R494's un-sourceability witness) all
    the way to this ancestor.  So the ancestor:
    * on `D n` (NON-degenerate): SOURCES `h_ne := ne_of_D` on the re-discovered discriminator, then routes
      through the R494 lift `lift_seq`;
    * on `¬ D n` (degenerate): produces `Goal n` DIRECTLY (vacuously), BYPASSING the leaf the premise
      could not feed. -/
theorem terminate (n : Nat) (hg : WeakG n) : Goal n := by
  by_cases hD : D n
  · -- non-degenerate: source the premise on the discriminator, route through the R494 lift.
    have h_ne : NE n := ne_of_D n hD
    exact fun _ _ => lift_seq n hg h_ne
  · -- degenerate: `n < 2`, the window is empty, `Goal n` is vacuous; the leaf is BYPASSED.
    intro k hk
    omega

/-! ### Why the degenerate branch is genuine: the weak gate reaches it, the lift cannot serve it. -/

/-- The degenerate input the WEAK guard ADMITS (R494's `weakG_holds_but_ne_fails`): `WeakG 0` holds,
    yet `NE 0` is FALSE — so `lift_seq 0` is UNFEEDABLE, which is precisely why `terminate` must BYPASS
    it on this input rather than discharge the premise. -/
theorem degenerate_reaches_ancestor : WeakG 0 ∧ ¬ NE 0 :=
  ⟨⟨id⟩, Nat.not_succ_le_zero 0⟩

/-- The terminating ancestor nonetheless produces `Goal 0` — via the vacuous (degenerate) branch, with
    NO `h_ne`.  The case split pays off: the premise climbed precisely because some ancestor had to
    handle the input the leaf could not. -/
example : Goal 0 := terminate 0 ⟨id⟩

/-- And on a non-degenerate input it produces `Goal` through the R494 lift, `h_ne` sourced from `D`. -/
example : Goal 3 := terminate 3 ⟨id⟩

end ClimbingPremiseTerminatesAtCaseSplit
