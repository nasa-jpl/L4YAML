import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Reflection 541 — INHABITATION PROBE for the boundary-robust map carrier `MapInteriorSeparators'`

This file is the inhabitation test the [[feedback-inhabitation-debt-validate-target-defs]] discipline
demands, applied to the NEW boundary-robust carrier landed in
`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean` (R541). Unlike the abstract
companion `BoundaryRobustVsFragileFact.lean` (the principle in the small), this file imports the REAL
defs and probes them. It lives under `Tests/` — NOT inline in the source — so the carrier's
inhabitation is a build-time REGRESSION test, kept separate from the library definition (the
discipline's "write the inhabitation tests in `tests/`" rule).

## What R540 caught, and what this probes

R540 found the STRICT carrier `MapInteriorSeparators` UNPROVABLE: its `MapGrammarFacts` is
boundary-FRAGILE — at a window that ends one past a `flowBracketDelta`-`0` `.key`/`.value` marker
(`b = k + 1`), conjunct 1 demands `k + 1 < b`, i.e. `b < b`, FALSE. The strict carrier had been
surrounded by ~8 consumers before anyone checked it was inhabited (the inhabitation DEBT).

The robust replacement `MapGrammarFacts'` adds a window-close escape `b ≤ <position>` to each fragile
conjunct. This file PROBES, against the REAL defs, the exact boundary the strict form died on
(inhabitation-debt rule 2 — instantiate the universal at the DEGENERATE/EDGE window `b = a` / `b = a + 1`,
never the comfortable interior):

* `mapGrammarFacts'_degenerate` — the robust facts hold on EVERY window-close window `[k, k+1)`, for
  EVERY stream, UNCONDITIONALLY. This is the boundary the strict facts are refuted on.
* `mapGrammarFacts_degenerate_key_false` — the STRICT facts are REFUTED on that same window whenever
  the trigger is a `.key`. This is the one-line probe that, run at the strict carrier's birth, would
  have caught the bug before any consumer was built on top.
* `mapInteriorSeparators'_unit` — the robust CARRIER itself holds on a unit span `[lo, lo+1)`, for
  EVERY stream (every gated sub-window has width ≤ 1, so the empty-window and window-close cases cover
  it). The strict carrier `MapInteriorSeparators tokens lo (lo+1)` is NOT provable this way.
-/

namespace MapCarrierRobustInhabitation

open L4YAML
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.EmitterScannability

/-- The robust facts hold on the EMPTY window `[a, a)` — every conjunct's `a ≤ k → k < a` premise
    pair is contradictory, so all six are vacuous. -/
theorem mapGrammarFacts'_empty (tokens : Array (Positioned YamlToken)) (a : Nat) :
    MapGrammarFacts' tokens a a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k h1 h2; exact absurd h2 (by omega)
  · intro k h1 h2; exact absurd h2 (by omega)
  · intro k h1 h2; exact absurd h2 (by omega)
  · intro k h1 h2; exact absurd h2 (by omega)
  · intro k j h1 h2; exact absurd h2 (by omega)
  · intro k j h1 h2; exact absurd h2 (by omega)

/-- **The robust facts SURVIVE the window-close boundary** — `MapGrammarFacts' tokens k (k+1)` holds
    for EVERY stream and EVERY `k`. The only candidate trigger position is `k` itself, and every
    fragile conjunct's escape `b ≤ <position>` fires there (`k + 1 ≤ k + 1`, `k + 1 ≤ k + 2`);
    conjuncts 5/6 are vacuous (no room for an interior closer `j` with `k + 1 < j < k + 1`). This is
    exactly the boundary the strict `MapGrammarFacts` is refuted on. -/
theorem mapGrammarFacts'_degenerate (tokens : Array (Positioned YamlToken)) (k : Nat) :
    MapGrammarFacts' tokens k (k + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k' h1 h2 _ _; exact Or.inl (by omega)
  · intro k' h1 h2 _ _ _; exact Or.inl (by omega)
  · intro k' h1 h2 _ _; exact Or.inl (by omega)
  · intro k' h1 h2 _ _ _; exact Or.inl (by omega)
  · intro k' j h1 h2 _ _ h3 h4 _ _; exact absurd h4 (by omega)
  · intro k' j h1 h2 _ _ h3 h4 _ _; exact absurd h4 (by omega)

/-- **The STRICT facts are REFUTED on the same window** when the trigger is a `.key`: conjunct 1
    demands `k + 1 < k + 1`. This is the one-line, `decide`-cheap probe that — owed at the strict
    carrier's BIRTH — would have exposed the inhabitation bug R540 only found after ~8 consumers had
    been built on top. -/
theorem mapGrammarFacts_degenerate_key_false (tokens : Array (Positioned YamlToken)) (k : Nat)
    (hk : tokens[k]!.val = .key) : ¬ MapGrammarFacts tokens k (k + 1) := by
  intro h
  obtain ⟨h1, _⟩ := h
  have hbal : flowBracketBalance tokens k k = 0 := by simp [flowBracketBalance]
  have hcontra := (h1 k (Nat.le_refl k) (by omega) hbal hk).1
  omega

/-- **The robust CARRIER is inhabited on a unit span** `[lo, lo+1)` — for EVERY stream. Every gated
    sub-window `[a,b) ⊆ [lo, lo+1)` has width `b - a ≤ 1`, so it is either the empty window
    (`mapGrammarFacts'_empty`) or a window-close window (`mapGrammarFacts'_degenerate`). The strict
    carrier `MapInteriorSeparators tokens lo (lo+1)` is NOT provable this way — its facts are refuted
    at the very window-close window this one survives (R540's `{a:1}` cut window `[1,2)`). -/
theorem mapInteriorSeparators'_unit (tokens : Array (Positioned YamlToken)) (lo : Nat) :
    MapInteriorSeparators' tokens lo (lo + 1) := by
  intro a b ha hab hb _hgate
  rcases Nat.lt_or_ge a b with hLt | hGe
  · have hb1 : b = a + 1 := by omega
    rw [hb1]; exact mapGrammarFacts'_degenerate tokens a
  · have hEq : a = b := by omega
    rw [← hEq]; exact mapGrammarFacts'_empty tokens a

-- Axiom audit — the carrier inhabitation and the boundary-survival probe lean only on core.
/-- info: 'MapCarrierRobustInhabitation.mapInteriorSeparators'_unit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapInteriorSeparators'_unit

/-- info: 'MapCarrierRobustInhabitation.mapGrammarFacts'_degenerate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mapGrammarFacts'_degenerate

end MapCarrierRobustInhabitation
