/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Reflection 406 — a per-item predicate carrying field `F` does NOT make an
aggregating producer OUTPUT `F`

Self-contained toy for [[ref-predicate-field-not-producer-output]].

After a big "touch every predicate" threading pass (the L4YAML R405 atomic step put
`OpenerAdj` on all five flow-block predicates *and* co-produced it on the RECURSIVE
aggregator), it is tempting to treat the field as "available everywhere."  It is not.
A downstream consumer's facts come ONLY from the conclusion of the producer that feeds
its frame — never from the per-item predicate that producer happened to consume.  So if
the SORRY's consumer is fed by a DIFFERENT (here: the flat/`SafeBody`) aggregator than
the one where the field was co-produced (the recursive aggregator), the field must be
co-produced AGAIN on that flat aggregator — re-threaded through its OWN induction with
the SAME seam glue (the seam is shared between parallel producers because they share the
cons append shape) — and re-projected as a new output conjunct of its characterization.

The toy strips this to its bones.  Items are `Nat`s.  The per-item predicate `ItemP n`
bundles a CORE fact (`n` even — the aggregators always deliver this) AND an orthogonal
field `F` (`0 < n`).  Two PARALLEL aggregators fold a list of items:

  * `aggCore`  — its conclusion lists ONLY the core aggregate.  `F` is DROPPED.
  * `aggCoreF` — its conclusion ALSO lists the `F` aggregate (co-produced from the same
                  per-item hypothesis).

POSITIVE: a consumer fed by `aggCoreF` reads `F` straight off the output.
NEGATIVE: a consumer fed by `aggCore` is STUCK even though every `ItemP` carries `F` —
`aggCore`'s conclusion is *satisfied by data with `F` false* (the witness `[0]`: even,
but not positive), so it cannot entail `F`.  The fix is never "the predicate carries it";
it is "re-list and re-thread `F` in THIS producer's conclusion." -/

namespace Tests.Reflections.PredicateFieldNotProducerOutput

/-- Per-item predicate: carries the CORE the aggregators always deliver (`even`) AND the
    orthogonal field `F` (`positive`).  The L4YAML analogue: `EmitScansInFlowBlock` carries
    `WellBracketed`/… (core) AND `OpenerAdj` (the field `F`). -/
structure ItemP (n : Nat) : Prop where
  even : n % 2 = 0
  pos  : 0 < n

/-- **Core-only aggregator.**  Conclusion lists ONLY the core aggregate; `F` is dropped.
    The L4YAML analogue BEFORE step (b): `emitList_scans_safebody` outputs the flat bracket
    facts but NOT `OpenerAdj`, even though its per-item `EmitScansInFlowBlock` carries it. -/
theorem aggCore (xs : List Nat) (h : ∀ x ∈ xs, ItemP x) :
    ∀ x ∈ xs, x % 2 = 0 :=
  fun x hx => (h x hx).even

/-- **Strengthened aggregator.**  Conclusion ALSO outputs the `F` aggregate, co-produced
    from the SAME per-item hypothesis — no new algebra, just re-listing `F`.  The L4YAML
    analogue AFTER step (b): `emitList_scans_safebody` now outputs `∧ OpenerAdj block`. -/
theorem aggCoreF (xs : List Nat) (h : ∀ x ∈ xs, ItemP x) :
    (∀ x ∈ xs, x % 2 = 0) ∧ (∀ x ∈ xs, 0 < x) :=
  ⟨fun x hx => (h x hx).even, fun x hx => (h x hx).pos⟩

/-- **POSITIVE.**  A consumer fed by the STRENGTHENED aggregator reads `F` directly off
    its conclusion — the only place a downstream consumer can get it. -/
theorem consumer_reads_F (xs : List Nat) (h : ∀ x ∈ xs, ItemP x) :
    ∀ x ∈ xs, 0 < x :=
  (aggCoreF xs h).2

/-- **NEGATIVE.**  The core-only aggregator's CONCLUSION does not entail `F`.  Witnessed by
    `[0]`: it satisfies the core aggregate (`0` is even) yet `F` fails (`0` is not positive).
    So a consumer reading only `aggCore`'s output type CANNOT recover `F`, EVEN THOUGH every
    `ItemP` carries it — because the producer never re-listed `F` in its conclusion.  (This is
    the model fact: `aggCore`'s conclusion is a strictly weaker proposition than `F`'s.) -/
theorem aggCore_concl_does_not_entail_F :
    (∀ x ∈ ([0] : List Nat), x % 2 = 0) ∧ ¬ (∀ x ∈ ([0] : List Nat), 0 < x) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx; decide
  · intro hF
    exact absurd (hF 0 (by simp)) (by decide)

/-! The negative witness `[0]` separates the core aggregate (holds) from `F` (fails). -/

-- core holds for the negative witness …
#guard (0 % 2 == 0)
-- … but the field `F` fails for it, so the core conclusion cannot entail `F`.
#guard (decide (0 < 0) == false)

end Tests.Reflections.PredicateFieldNotProducerOutput
