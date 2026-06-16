/-!
# Reflection 463 — before threading a recursive-deliverable PRODUCER to emit a STRONGER (deep)
# structure, land the producer's DELIVERABLE CONTRACT first: the additive parallel deliverable
# PREDICATE (flat producer predicate with its lone structural conjunct swapped to the deep
# refinement) + the strong→weak COERCION back to the flat predicate.  The coercion is near-free
# (project the ONE differing conjunct, pass every scan-invariant conjunct verbatim) and PROVABLE
# TODAY — before any producer body exists — and it is load-bearing: it proves the deep deliverable
# LOSES NOTHING, so the producer can be upgraded brick-by-brick with EVERY existing consumer untouched.

Self-contained (core Lean, no `L4YAML` import) toy executing STEP D step 8's FIRST brick.  The deep
four-inductive family was AUTHORED (`[[ref-deep-family-mirrors-full-mutual-group]]`,
`[[ref-parallel-family-sheds-orthogonal-field]]`) and PROJECTS to the flat family.  Now the PRODUCER
must be threaded to BUILD the deep family on the emit feed — a large mutual recursion mirroring the
flat producer trio.  Rather than start with the (heavy) producer body, the smallest landable brick is
the producer's *deliverable contract*:

* The flat per-entry producer predicate `EmitScansInFlowRecEntry v` is a big
  `∀ inputs, preconditions → ∃ block, [≈25 scan invariants] ∧ RecSeqEntry block ∧ [more]`.
* The DEEP producer will deliver the SAME predicate with the lone structural conjunct
  `RecSeqEntry block` REPLACED by the severance-free `RecEntryDeep block` — every scan invariant is
  identical (the deep family is purely structural).  That is a new ADDITIVE parallel predicate
  `EmitScansInFlowRecEntryDeep` (never an edit to the shared flat one).
* The STRONG→WEAK coercion `EmitScansInFlowRecEntryDeep v → EmitScansInFlowRecEntry v` projects the ONE
  differing conjunct via the already-proven `RecEntryDeep.toFlat`, passing every other conjunct through
  verbatim.  It proves the deep deliverable loses nothing: wherever the producer currently emits the
  flat predicate, a future deep-emitting producer's output is still consumable by EVERY existing flat
  consumer (`emitList_scans_recseqbody`, `emitPairList_scans_recmapbody`, …) via the coercion.

This toy mirrors that exactly, scaled down:

* `F` / `D` — the flat structural deliverable and its deep refinement, with the projection `D.toF`
  (mirror `RecSeqEntry` / `RecEntryDeep` + `RecEntryDeep.toFlat`).
* `Inv1`/`Inv2` — stand-ins for the ≈25 scan-state invariants the producer predicate also carries.
* `PFlat v` / `PDeep v` — the flat producer-deliverable predicate and its deep parallel; they differ
  by EXACTLY the one structural conjunct (`F out` vs `D out`).
* `PDeep.toFlat` — the strong→weak coercion: projects the one conjunct, passes the invariants verbatim.
* `consumer_uses_flat` / `consumer_fires_on_deep` — the SAME downstream consumer, fired first on the
  flat predicate and then on the deep one via the coercion, UNCHANGED.
* `deliverable_contract_before_producer_body` — the finding in one proposition, with NO producer of
  `PDeep` anywhere (the contract is landable before the producer body).

All sorry-free; the contract theorems depend on no axioms.
-/

set_option autoImplicit false

namespace Tests.Reflections.DeliverableContractBeforeProducerBody

/-- Toy alphabet. -/
inductive Tok where
  | a | op | cl
deriving DecidableEq

/-- The FLAT structural deliverable (mirror `RecSeqEntry`) — "severed": the wrapper stores only the
    non-emptiness of its interior, with no recursive body. -/
inductive F : List Tok → Prop where
  | leaf : F [Tok.a]
  | wrap (interior : List Tok) (hne : interior ≠ []) : F (Tok.op :: (interior ++ [Tok.cl]))

/-- The DEEP refinement (mirror `RecEntryDeep`) — the wrapper carries the recursive body itself. -/
inductive D : List Tok → Prop where
  | leaf : D [Tok.a]
  | wrap (interior : List Tok) (h : D interior) : D (Tok.op :: (interior ++ [Tok.cl]))

/-- Every `D` is non-empty (each constructor's index is `[a]` or `op :: …`). -/
theorem D.ne_nil : {l : List Tok} → D l → l ≠ []
  | _, .leaf => by simp
  | _, .wrap _ _ => by simp

/-- **The projection** `D x → F x` (mirror `RecEntryDeep.toFlat`): the deep `wrap` re-materializes the
    severed family's `hne` field from its recursive body via `D.ne_nil`.  This is the *already-proven*
    projection the deliverable-contract coercion calls on its one structural conjunct. -/
theorem D.toF : {l : List Tok} → D l → F l
  | _, .leaf => F.leaf
  | _, .wrap interior h => F.wrap interior (D.ne_nil h)

/-! ## Stand-ins for the producer predicate's many scan-state invariants. -/

/-- A scan-state-style invariant (stand-in for `WellBracketed`/`WellTyped`/`EntrySafe`/… — there are
    ≈25 of these in the real predicate). -/
def Inv1 (l : List Tok) : Prop := l = l
/-- A second invariant (stand-in). -/
def Inv2 (l : List Tok) : Prop := l ++ [] = l

/-! ## The producer's DELIVERABLE PREDICATE — flat and its deep parallel.
    They differ by EXACTLY the lone structural conjunct (`F out` vs `D out`); every invariant is
    identical (mirror `EmitScansInFlowRecEntry` vs `EmitScansInFlowRecEntryDeep`). -/

/-- The FLAT producer-deliverable predicate: under a precondition, produce some `out` carrying the scan
    invariants AND the flat structural deliverable `F out`. -/
def PFlat (_v : Nat) : Prop :=
  ∀ (pre : Prop), pre → ∃ out, Inv1 out ∧ Inv2 out ∧ F out ∧ Inv1 out

/-- The DEEP producer-deliverable predicate: the additive parallel of `PFlat`, with the lone
    structural conjunct `F out` swapped to the deep refinement `D out`.  (Never an edit to `PFlat` —
    a new parallel def.) -/
def PDeep (_v : Nat) : Prop :=
  ∀ (pre : Prop), pre → ∃ out, Inv1 out ∧ Inv2 out ∧ D out ∧ Inv1 out

/-- **The strong→weak coercion** `PDeep v → PFlat v` (mirror `EmitScansInFlowRecEntryDeep.toFlat`).
    Project the ONE differing conjunct via the proven projection `D.toF`; pass every scan-invariant
    conjunct through verbatim.  Provable TODAY — no producer of `PDeep` need exist. -/
theorem PDeep.toFlat {v : Nat} (h : PDeep v) : PFlat v := by
  intro pre hp
  obtain ⟨out, i1, i2, hd, i1'⟩ := h pre hp
  exact ⟨out, i1, i2, D.toF hd, i1'⟩

/-! ## A downstream consumer fires on the DEEP deliverable UNCHANGED, via the coercion. -/

/-- A consumer that reads the flat producer's deliverable. -/
theorem consumer_uses_flat {v : Nat} (h : PFlat v) : ∃ out, F out := by
  obtain ⟨out, _, _, hf, _⟩ := h True trivial
  exact ⟨out, hf⟩

/-- The SAME consumer fires on the DEEP deliverable — no re-proof, just the coercion.  This is why the
    producer can be upgraded to emit `PDeep` brick-by-brick with consumers untouched. -/
theorem consumer_fires_on_deep {v : Nat} (h : PDeep v) : ∃ out, F out :=
  consumer_uses_flat (PDeep.toFlat h)

/-! ## The producer asymmetry — the deep producer is heavier, but the contract neutralises it. -/

/-- Building the FLAT deliverable requires supplying the flat structural `F out`. -/
theorem flat_producer_supplies_F (_v : Nat) (out : List Tok)
    (hi1 : Inv1 out) (hi2 : Inv2 out) (hf : F out) : ∃ o, Inv1 o ∧ Inv2 o ∧ F o ∧ Inv1 o :=
  ⟨out, hi1, hi2, hf, hi1⟩

/-- Building the DEEP deliverable requires supplying the STRONGER structural `D out` (the future
    producer's extra work: thread the recursion).  But by `PDeep.toFlat` this output is still
    consumable everywhere the flat one is. -/
theorem deep_producer_supplies_D (_v : Nat) (out : List Tok)
    (hi1 : Inv1 out) (hi2 : Inv2 out) (hd : D out) : ∃ o, Inv1 o ∧ Inv2 o ∧ D o ∧ Inv1 o :=
  ⟨out, hi1, hi2, hd, hi1⟩

/-- **The finding in one proposition.**  (1) the deep deliverable projects to the flat one (`D.toF`);
    (2) the deep producer-predicate coerces to the flat one (`PDeep.toFlat`), differing by exactly the
    one structural conjunct; (3) every flat consumer fires on the deep deliverable via the coercion,
    unchanged.  So the producer's deliverable CONTRACT — the additive parallel predicate + the
    strong→weak coercion — is landable BEFORE the producer body exists, and guarantees the producer can
    be threaded to emit the deep structure brick-by-brick with consumers untouched.  Sharpens
    `[[ref-coerce-to-weaker-reuse-wrapper]]` (consume-side strong→weak reuse) to the PRODUCER's
    deliverable predicate, via `[[ref-additive-parallel-type-over-shared-edit]]` (parallel predicate,
    not a shared edit) and `[[ref-fold-consumer-chain-to-producer-contract]]` (the predicate IS the
    producer's contract). -/
theorem deliverable_contract_before_producer_body :
    (∀ l, D l → F l)
    ∧ (∀ v, PDeep v → PFlat v)
    ∧ (∀ v, PDeep v → ∃ out, F out) :=
  ⟨fun _l h => D.toF h,
   fun _v h => PDeep.toFlat h,
   fun _v h => consumer_fires_on_deep h⟩

end Tests.Reflections.DeliverableContractBeforeProducerBody
