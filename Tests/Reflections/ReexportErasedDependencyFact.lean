/-!
# Reflection 478 — RE-EXPORT, don't re-derive: a downstream consumer that ERASES a fact its OWN
# dependency already computed forces a parallel wrapper that RE-RUNS the dependency keeping the
# dropped binder; consuming the sibling brick proven for the erased fact forces placement AFTER it.

Self-contained (core Lean, no `L4YAML` import) toy recording the brick R478 landed:
`seqClose_of_located_and_enclosing_within`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the α.1-remaining sub-piece
of the (α) `enclosingLocate` residual that `seqWidthEnc_of_enclosingLocate_and_recIH` (R475) lifts.

**The setup.**  `seqClose_of_located_and_enclosing` locates a matching close by calling
`flowBracketBalance_matching_close_seq`, which delivers BOTH the close bound `j < hi` AND the located
interior's own Dyck floor `∀ i ∈ [p+1, j], flowBracketBalance tokens (p+1) i ≥ 0`.  But the locator
`_`-DROPS the floor and OMITS `j < hi` from its return type — re-exporting only `a ≤ hiS`, `b ≤ hiS`,
`hiS ≤ size`, the inner balance, the typed close.  The (α) `enclosingLocate` existential R475 consumes
still owes the UPPER containment `hiE ≤ hi` and the interior floor — both of which the dependency
ALREADY computed and the consumer threw away.

**The brick — re-export, don't re-derive.**  Rather than re-derive the dropped facts from scratch,
RE-RUN the dependency in a NEW parallel locator (per [[ref-additive-parallel-type-over-shared-edit]]:
the original is consumed by `seqEnclosingFacts_provider_of_located`, so we add a sibling, not edit it)
that keeps the dropped binder.  The upper containment is then discharged by R477
(`seqLocatedClose_within_body`, the floor→containment brick), which CONSUMES R477
([[ref-reduction-by-import]]: the wiring retypes the residual — the retype is the progress).  Consuming
R477 forces the new locator to sit AFTER R477 in the file — a forward reference Lean rejects (the real
turn hit `unknownIdentifier` placing it next to its sibling locator, which precedes R477).

This toy reproduces the four reusable facts, abstracted away from the bracket-balance specifics.
-/

namespace ReexportErasedDependencyFact

set_option autoImplicit false

/-- **The consumer ERASES `Q`.**  Models `seqClose_of_located_and_enclosing`, whose return type drops
    the interior floor and `j < hi`, re-exporting only the payload `P` from the dependency's `P ∧ Q`.
    (The dependency `∃ w, P w ∧ Q w` is taken as a hypothesis the way the real
    `flowBracketBalance_matching_close_seq` is a proven lemma.) -/
theorem consumer_erases {P Q : Nat → Prop} (dep : ∃ w, P w ∧ Q w) : ∃ w, P w := by
  obtain ⟨w, hP, _hQ⟩ := dep
  exact ⟨w, hP⟩

/-- **RE-EXPORT, don't re-derive (the structural heart).**  The strengthened wrapper RE-RUNS the
    dependency KEEPING the dropped binder `Q`, then applies the sibling — recovering `R` AND
    re-exporting `Q` itself.  Mirrors `seqClose_of_located_and_enclosing_within`, which re-runs
    `flowBracketBalance_matching_close_seq` keeping the floor and discharges the upper containment via
    the sibling brick R477.  Note it consumes `sibling`. -/
theorem reexport {P Q R : Nat → Prop} (sibling : ∀ w, Q w → R w) (dep : ∃ w, P w ∧ Q w) :
    ∃ w, P w ∧ Q w ∧ R w := by
  obtain ⟨w, hP, hQ⟩ := dep
  exact ⟨w, hP, hQ, sibling w hQ⟩

/-- **The erasure is GENUINE — `R` is NOT recoverable from the consumer's erased output `∃ w, P w`.**
    The consumer's witness DOES satisfy `Q`/`R` (it is the dependency's own `w`), but its RETURN TYPE
    forgot them, so a downstream caller holding only `∃ w, P w` cannot reconstruct `R`.  Take
    `P := True`, `Q := R := False` (`sibling : False → False` holds trivially), so `∃ w, P w` holds
    (`w = 0`) yet `∃ w, P w ∧ R w` is FALSE.  Hence re-running the dependency (re-export) is NECESSARY;
    you cannot re-derive `Q`/`R` from `P` alone. -/
theorem erasure_is_genuine :
    ¬ (∀ (P Q R : Nat → Prop), (∀ w, Q w → R w) → (∃ w, P w) → ∃ w, P w ∧ R w) := by
  intro h
  obtain ⟨_w, _hP, hR⟩ :=
    h (fun _ => True) (fun _ => False) (fun _ => False) (fun _ hw => hw) ⟨0, trivial⟩
  exact hR

/-- A CONCRETE sibling, proven for the erased fact (mirrors R477's containment-from-floor brick). -/
theorem sibling_le (w : Nat) (hQ : w = 2) : w ≤ 4 := by omega

/-- **The placement is FORCED by consumption.**  `reexport_concrete` CALLS `sibling_le` BY NAME, so it
    must be defined AFTER it — the file-order consequence of consuming the sibling brick, exactly why
    `seqClose_of_located_and_enclosing_within` lives after R477 rather than beside its sibling locator
    (which precedes R477). -/
theorem reexport_concrete {P : Nat → Prop} (dep : ∃ w, P w ∧ w = 2) :
    ∃ w, P w ∧ w = 2 ∧ w ≤ 4 := by
  obtain ⟨w, hP, hQ⟩ := dep
  exact ⟨w, hP, hQ, sibling_le w hQ⟩

/-- CONCRETE, non-vacuous — the generic `reexport` runs end-to-end with `R` derived from `Q` via the
    parametric sibling (`P := (· < 5)`, `Q := (· = 2)`, `R := (· ≤ 4)`, witness `w = 2`). -/
example : ∃ w, w < 5 ∧ w = 2 ∧ w ≤ 4 :=
  reexport (P := fun w => w < 5) (Q := fun w => w = 2) (R := fun w => w ≤ 4)
    (fun _w hw => by omega) ⟨2, by omega, rfl⟩

/-- CONCRETE, non-vacuous — `reexport_concrete` (the by-name, placement-forcing variant) on the same
    witness, confirming the consumed sibling really fires. -/
example : ∃ w, w < 5 ∧ w = 2 ∧ w ≤ 4 :=
  reexport_concrete (P := fun w => w < 5) ⟨2, by omega, rfl⟩

end ReexportErasedDependencyFact
