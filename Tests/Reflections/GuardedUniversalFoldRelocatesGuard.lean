/-!
# Reflection 301 — the consumer fold collapses a GUARDED universal to a single provider, and the guard relocates: producer's gift, consumer's debt

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`seqInteriorSeparators_of_safebody_provider`, the first brick of `(i'-b-descend-root)`.

A carrier is a GUARDED universal `Carrier lo hi := ∀ n, lo ≤ n → n ≤ hi → Gate n → Fact n`. The
per-element discharge `factOfUnit : Unit n → Fact n` (the R299 analog: one deliverable yields the
asserted fact) folds under the `∀` into `carrier_of_provider`, whose sole hypothesis `provider`
(deliver `Unit` at each gated `n`) IS the producer's remaining contract.

The decisive point the fold exposes: the gate `Gate n` is the carrier body's **antecedent**, so
proving the carrier `intro`s it — the producer CONSUMES the gate, never produces it. The gate is the
producer's GIFT (a narrower domain: elements where `Fact` would fail are gated OUT, never reaching
the provider — `gate_gifts_narrower_domain`), and the consumer's DEBT (instantiating the carrier at
a point requires SUPPLYING the gate — `consume_needs_gate`).

Toy substrate: `Gate` = even (the "seq-typed" context gate), `Unit` = `∃ m, n = m + m` (the
provider's deliverable, "SafeBodyUnit"), `Fact` = `∃ m, n = 2 * m` (the asserted "separator fact").
-/

namespace Tests.Reflections.GuardedUniversalFoldRelocatesGuard

set_option autoImplicit false

/-- The context GATE (toy of `SeqTypedInterior`'s seq-typed-ness): `n` is even. -/
def Gate (n : Nat) : Prop := n % 2 = 0

/-- The provider's DELIVERABLE (toy of the windowed `SafeBodyUnit ContentStartTok …`). -/
def Unit (n : Nat) : Prop := ∃ m, n = m + m

/-- The asserted FACT (toy of `bodySuccFact ∧ noTrailingSepFact`). -/
def Fact (n : Nat) : Prop := ∃ m, n = 2 * m

/-- **The per-element discharge** (toy of R299's `seqSeparatorFacts_of_windowed_safebodyunit`): one
    deliverable `Unit n` yields the asserted `Fact n`. -/
theorem factOfUnit {n : Nat} (h : Unit n) : Fact n := by
  obtain ⟨m, hm⟩ := h; exact ⟨m, by omega⟩

/-- **The guarded universal carrier** (toy of `SeqInteriorSeparators tokens lo hi`): over the window
    `[lo,hi]`, every GATED `n` satisfies `Fact`. The gate is the body's ANTECEDENT. -/
def Carrier (lo hi : Nat) : Prop :=
  ∀ n, lo ≤ n → n ≤ hi → Gate n → Fact n

/-- **The consumer fold** (faithful mirror of `seqInteriorSeparators_of_safebody_provider`): the
    carrier reduces to a single `provider` hypothesis. Proving it `intro`s the gate `hg` — the
    producer CONSUMES the gate — and feeds the provided `Unit` through `factOfUnit`. `provider`'s
    signature IS the producer's remaining contract. -/
theorem carrier_of_provider {lo hi : Nat}
    (provider : ∀ n, lo ≤ n → n ≤ hi → Gate n → Unit n) :
    Carrier lo hi :=
  fun n h1 h2 hg => factOfUnit (provider n h1 h2 hg)

/-- **The provider, discharged on a concrete window** (toy of the root instance — emission delivers
    the `SafeBodyUnit` directly): every even `n ≤ 6` has `Unit n` (`m := n / 2`). -/
theorem provider_concrete : ∀ n, 0 ≤ n → n ≤ 6 → Gate n → Unit n :=
  fun n _ _ hg => ⟨n / 2, by unfold Gate at hg; omega⟩

/-- **POSITIVE — the carrier on the concrete window**, by folding the concrete provider. -/
theorem carrier_concrete : Carrier 0 6 := carrier_of_provider provider_concrete

/-- **The gate is the producer's GIFT — a narrower domain.** `3` lies in the window `[0,6]` and
    `Fact 3` FAILS (no `m` with `3 = 2 * m`), yet `Carrier 0 6` holds: the gate `Gate 3` is false, so
    the carrier never asserts `Fact` at `3`. The off-gate failure is gated OUT — exactly why the
    provider (which only delivers at gated points) suffices. (Mirrors the R297 map-window where
    `bodySucc` FAILS but the seq-typed gate excludes it.) -/
theorem gate_gifts_narrower_domain : ¬ Gate 3 ∧ ¬ Fact 3 ∧ Carrier 0 6 := by
  refine ⟨?_, ?_, carrier_concrete⟩
  · unfold Gate; decide
  · rintro ⟨m, hm⟩; omega

/-- **The gate is the consumer's DEBT.** To instantiate the carrier at a concrete point `4`, the
    consumer must SUPPLY `Gate 4` (and the bounds). This is where R300's `seqTypedInterior_of_opener`
    lives — at the consume/`assemble` site that instantiates the whole carrier, NOT in the root seed
    that proves it. -/
theorem consume_needs_gate (h : Carrier 0 6) : Gate 4 → Fact 4 :=
  fun hg => h 4 (by omega) (by omega) hg

/-! ## Decidable witnesses -/

-- ON-gate points (even) — the provider must, and does, deliver here.
#guard (4 % 2 == 0) && (6 % 2 == 0)
-- OFF-gate point (odd `3` ∈ [0,6]) — gated OUT, so its `Fact`-failure never reaches the carrier.
#guard 3 % 2 == 1
-- The provider's deliverable `Unit` at the on-gate point `4`: `4 = 2 + 2`.
#guard (decide (∃ m, m ≤ 4 ∧ 4 = m + m))

/-- POSITIVE (decidable-ish): the fold's two endpoints — concrete carrier holds, and the
    consume-site instantiation at `4` succeeds once the gate is supplied. -/
theorem fold_endpoints : Carrier 0 6 ∧ Fact 4 :=
  ⟨carrier_concrete, consume_needs_gate carrier_concrete (by unfold Gate; decide)⟩

end Tests.Reflections.GuardedUniversalFoldRelocatesGuard
