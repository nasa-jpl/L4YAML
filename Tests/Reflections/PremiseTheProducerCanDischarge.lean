/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 683 — state the premise the producer can always discharge

**The rule.**  A runtime fact often holds under either of two conditions, and
the instinct is to pick the one the site in front of you happens to have.  Do
not.  Pick the DISJUNCTION — not as a hedge, but because it is the only form
that survives the induction that has to carry it.  A recursive producer can
discharge one of the two out of the step it just took, and never has to know
which of the two its own caller had; the base case discharges the other; and
the consumer, which has neither in general, discharges it by CASES, because the
branch it cannot discharge is the branch a different arm already serves.

**Why picking one fails, in both directions.**  Pick the ENTRY condition and
the fact dies at the consumer, whose own hypothesis supplies its negation, so
the carried implication is vacuous — it proves anything, including `False`
(§2).  Pick the LANDING condition — "we got here by taking a step" — and the
fact dies in the recursion, which cannot see whether the *inner* call will take
one; the inner instance comes back vacuous and the outer goal still needs the
fact (§3).  The disjunction composes in one line (§4), because the step being
taken is itself a discharge of the inner premise.

**And it is not a weakening.**  `A ∨ B → P` implies both `A → P` and `B → P`,
so the disjunctive form is the STRONGEST of the three, not a compromise (§6).
The thing that got wider is the entry condition, not the conclusion.

**Why the fact was missing in the first place.**  A hop that returns only the
run it walked is satisfied by a machine whose gate never fires and by one whose
gate fires on every line — the run is the same either way — so no consumer
downstream of such a hop can tell them apart (§7).  The gate has to RIDE the
hop; there is nowhere else to get it.  That is why a check present in the
scanner since the beginning can be invisible to a proof chain for eight items.

**The instance** (item 64).  §6.1's tab check runs only on a line
`skipToContentLoop` ARRIVED at — so the fact "no tab sits at or left of
`currentIndent` on the final line" holds if the loop was entered with
`needIndentCheck` armed, or if it crossed a break to get there.  Stated under
the first alone it is useless to the accumulation, whose `IndentFloor` supplies
`needIndentCheck = false`; under the second alone it cannot cross the loop's own
recursion.  Stated as `LandingTabFacts` — `(nic = true ∨ sp_mid ≠ sp) →
NoLandingTabAt …` — every iteration discharges it with the break it just
consumed, and the consumer splits: the branch where the landing never left the
line is exactly the INLINE separator arm, which reads that run without the fact
at all.

§1 the fact and its two sufficient conditions; §2 entry-only is vacuous at the
consumer; §3 landing-only does not compose; §4 the disjunction composes; §5 the
consumer is total; §6 it is the strongest of the three; §7 why a run-only hop
hides it. -/

namespace L4YAML.Tests.Reflections.PremiseTheProducerCanDischarge

/-- §1 The walk, as much of it as the question needs: the check's flag on
    entry, and how many breaks were crossed before the final line.  The gate
    runs on the final line exactly when one of the two holds — a break re-arms
    the flag, so any positive number of them is as good as entering armed. -/
def gateRanOnFinalLine (armed : Bool) : Nat → Bool
  | 0 => armed
  | _ + 1 => true

/-- The fact and its two sufficient conditions, in one biconditional. -/
theorem fact_iff (armed : Bool) (k : Nat) :
    gateRanOnFinalLine armed k = true ↔ (armed = true ∨ 0 < k) := by
  cases k with
  | zero => cases armed <;> simp [gateRanOnFinalLine]
  | succ _ => simp [gateRanOnFinalLine]

/-- The three ways a lemma could carry `P` out of the walk. -/
def UnderEntry (armed : Bool) (_k : Nat) (P : Prop) : Prop := armed = true → P
def UnderLanding (_armed : Bool) (k : Nat) (P : Prop) : Prop := 0 < k → P
def UnderEither (armed : Bool) (k : Nat) (P : Prop) : Prop :=
  (armed = true ∨ 0 < k) → P

/-- §2 The consumer's own state is `armed = false` — its floor says so — and it
    crossed a break.  The ENTRY form is then vacuous there: it proves `False`,
    which is to say it proves nothing at all. -/
theorem entry_alone_is_vacuous_at_the_consumer : UnderEntry false 1 False := by
  simp [UnderEntry]

/-- …while the fact itself is perfectly true at that same state. -/
theorem the_fact_holds_there : gateRanOnFinalLine false 1 = true := rfl

/-- §3 The LANDING form does not compose.  A recursive step must build the
    outer instance from the inner one, and the inner call's own `k` is not
    something the step can see; when it is zero the inner instance is vacuous
    and the outer goal still wants `P`.  Machine-checked by deriving `False`
    from the composition rule itself. -/
theorem landing_alone_does_not_compose :
    ¬ (∀ (P : Prop) (armed : Bool) (k : Nat),
        UnderLanding true k P → UnderLanding armed (k + 1) P) := by
  intro h
  exact h False false 0 (by simp [UnderLanding]) (by omega)

/-- §4 The disjunctive form composes in one line, and the discharge is the
    step itself: the break just consumed re-armed the flag, so the inner
    premise is `Or.inl rfl` no matter what the inner `k` turns out to be. -/
theorem either_composes (P : Prop) (armed : Bool) (k : Nat) :
    UnderEither true k P → UnderEither armed (k + 1) P :=
  fun h _ => h (Or.inl rfl)

/-- …and it survives the base case, where no break was crossed and the flag
    the walk was entered with is all there is. -/
theorem either_at_the_base (P : Prop) (armed : Bool) (h : armed = true → P) :
    UnderEither armed 0 P := by
  rintro (ha | hk)
  · exact h ha
  · omega

/-- §5 The consumer is TOTAL on it, without either condition: it splits, and
    the branch it cannot discharge is the one where no break was crossed. -/
theorem consumer_splits (P : Prop) (armed : Bool) (k : Nat)
    (h : UnderEither armed k P) : k = 0 ∨ P := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl rfl
  · exact Or.inr (h (Or.inr hk))

/-- And that branch costs nothing, because it is not a landing at all: a walk
    that crossed no break has its run still on the entry line, which is the
    INLINE arm the consumer already carries. -/
def inlineArmServes (k : Nat) : Prop := k = 0

theorem consumer_is_total (P : Prop) (armed : Bool) (k : Nat)
    (h : UnderEither armed k P) : inlineArmServes k ∨ P :=
  consumer_splits P armed k h

/-- §6 Widening the entry condition is not a weakening: the disjunctive form
    implies both single-premise forms, so it is the strongest of the three. -/
theorem either_implies_entry (P : Prop) (armed : Bool) (k : Nat) :
    UnderEither armed k P → UnderEntry armed k P :=
  fun h ha => h (Or.inl ha)

theorem either_implies_landing (P : Prop) (armed : Bool) (k : Nat) :
    UnderEither armed k P → UnderLanding armed k P :=
  fun h hk => h (Or.inr hk)

/-- …and neither single form implies the other, so there is no "obvious"
    choice to have made. -/
theorem entry_does_not_imply_landing :
    ¬ (∀ (P : Prop) (armed : Bool) (k : Nat),
        UnderEntry armed k P → UnderLanding armed k P) := by
  intro h
  exact h False false 1 (by simp [UnderEntry]) (by omega)

theorem landing_does_not_imply_entry :
    ¬ (∀ (P : Prop) (armed : Bool) (k : Nat),
        UnderLanding armed k P → UnderEntry armed k P) := by
  intro h
  exact h False true 0 (by simp [UnderLanding]) rfl

/-- §7 Why the fact was not there to begin with.  Two machines: one whose gate
    runs on an arrived-at line, one whose gate never runs at all. -/
def gateNeverRuns (_armed : Bool) (_k : Nat) : Bool := false

/-- A hop that returns only the RUN it walked observes the same thing under
    both — the spaces are the spaces either way… -/
def obsRun (_gate : Bool → Nat → Bool) (k : Nat) : Nat := k

theorem run_observation_is_gate_blind (k : Nat) :
    obsRun gateRanOnFinalLine k = obsRun gateNeverRuns k := rfl

/-- …so a chain of such hops cannot separate a machine that checks §6.1 from
    one that does not, and a check present all along stays invisible to it.
    An observation that carries the gate does separate them. -/
def obsFact (gate : Bool → Nat → Bool) (k : Nat) : Bool := gate false k

theorem fact_observation_separates :
    obsFact gateRanOnFinalLine 1 ≠ obsFact gateNeverRuns 1 := by decide

end L4YAML.Tests.Reflections.PremiseTheProducerCanDischarge

end Blanket
