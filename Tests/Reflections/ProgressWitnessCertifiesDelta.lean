/-!
# Reflection 423 — derive a recursion-seam side-condition from the PROGRESS WITNESS, not a new field

Self-contained (core Lean, no `L4YAML` import) toy of the R423 seam-nonemptiness layer.  The
field-(i) `lastNonSep` threading (the R421 separator-tail mirror of `lastNonOpener`) must construct
`lastNonSep (block₁ ++ [feTok] ++ block_rest)` at the seq-body cons seam, via
`lastNonSep_append_right … block_rest hb h_lns_rest` — whose `hb : block_rest ≠ []` is REAL
(R421 restricted the tail bridge to `rest ≠ []` because the seam token `feTok = .flowEntry` IS the
separator, so an empty tail would make the whole block end in `.flowEntry` and falsify the field).
`block_rest` is the recursion's per-step delta, and the carrier predicate does NOT expose its
nonemptiness.

Two options, only one sound:

* **Thread a `block ≠ []` carrier field — UNSOUND.**  The carrier `EmitListScansInFlowBlock` serves
  BOTH the empty input (`emitList []`, empty block) and nonempty inputs, so `block ≠ []` cannot be
  an unconditional conjunct.  It is true ONLY at the recursive seam.
* **Derive it from the PROGRESS WITNESS — free and sound.**  The recursion advances by strict
  filtered-token growth: at the seam the recursive chain `ScanChainGrew … (n+1) …` (⇒ count grows by
  `≥ n+1`, `ScanChainGrew_filtered_grows`) composed with the delta equation
  `s'.filtered = s.filtered ++ delta` forces `delta.length ≥ n+1 ≥ 1`.  The growth that DRIVES the
  recursion certifies its delta is nonempty (`block_ne_nil_of_chainGrew`).

Position-match: the side-condition arises only where the progress witness is in scope, so no field
need carry it across the degenerate case.

The toy makes the asymmetry literal:

* `Grew` / `grew_ge` — the progress witness (a strict-growth chain) and its length lower bound
  (model of `ScanChainGrew` / `ScanChainGrew_filtered_grows`).
* `delta_ne_nil_of_grew` — **POSITIVE**: derive `delta ≠ []` from a `≥ 1`-step `Grew` + the delta
  equation, no carrier field (model of `block_ne_nil_of_chainGrew`).
* `cannot_thread_unconditional` — **NEGATIVE**: the would-be carrier field
  `∀ run, delta run ≠ []` is FALSE on the zero-step / empty degenerate run, so threading it is
  unsound — the fact must be derived at the seam, not carried.

Complementary pair with `SourceGateCollapseBlocksMirror` (R422): there a content/GATE obligation
must be THREADED (the recursive carrier owes a new gate-shaped field); here a NONEMPTINESS / measure
side-condition is DERIVED from progress.  Don't-thread-a-new-field sibling of
`ref-non-restriction-residual-root-seed`.
-/

namespace Tests.Reflections.ProgressWitnessCertifiesDelta

set_option autoImplicit false

/-- Toy "scanner state": just a filtered-token count. -/
structure St where
  count : Nat

/-- Toy strict-growth chain (model of `ScanChainGrew`): each step strictly increases `count`. -/
inductive Grew : St → Nat → St → Prop where
  | zero {s : St} : Grew s 0 s
  | step {s s_mid s' : St} {n : Nat} :
      s.count < s_mid.count →
      Grew s_mid n s' →
      Grew s (n + 1) s'

/-- Growth lower bound (model of `ScanChainGrew_filtered_grows`): `n` steps grow `count` by `≥ n`. -/
theorem grew_ge {s s' : St} {n : Nat} (h : Grew s n s') : s'.count ≥ s.count + n := by
  induction h with
  | zero => omega
  | @step s s_mid s' n hlt _hrest ih => omega

/-- Toy per-step delta equation (model of the filtered-block equation
    `s'.filtered.toList = s.filtered.toList ++ block`): the new count is the old plus the delta
    length. -/
def DeltaEq (s s' : St) (delta : List Nat) : Prop := s'.count = s.count + delta.length

/-! ## POSITIVE — derive the seam side-condition from the progress witness. -/

/-- **POSITIVE** — `delta ≠ []` from a `≥ 1`-step `Grew` + the delta equation; no carrier field.
    Model of `block_ne_nil_of_chainGrew`. -/
theorem delta_ne_nil_of_grew {s s' : St} {n : Nat} {delta : List Nat}
    (h_chain : Grew s (n + 1) s') (h_eq : DeltaEq s s' delta) :
    delta ≠ [] := by
  have h_grow := grew_ge h_chain
  intro h_nil
  simp only [DeltaEq, h_nil, List.length_nil] at h_eq
  omega

/-- A concrete `≥ 1`-step run with a nonempty delta — the positive case the seam actually faces. -/
theorem example_seam : ([7] : List Nat) ≠ [] :=
  delta_ne_nil_of_grew (s := ⟨0⟩) (s' := ⟨1⟩) (n := 0) (delta := [7])
    (.step (by decide) .zero) (by simp [DeltaEq])

/-! ## NEGATIVE — the unconditional carrier field is unsound. -/

/-- The would-be carrier field: "every run's delta is nonempty", UNCONDITIONALLY over all runs
    (model of threading `block ≠ []` as a carrier conjunct). -/
def DeltaAlwaysNonempty : Prop :=
  ∀ (s s' : St) (delta : List Nat), DeltaEq s s' delta → delta ≠ []

/-- **NEGATIVE** — the unconditional carrier field is FALSE: the zero-step / degenerate run
    (`s = s'`, empty delta) satisfies the delta equation yet has an EMPTY delta.  So threading
    `delta ≠ []` as a carrier conjunct is UNSOUND — the fact holds only at the `≥ 1`-step seam,
    where the progress witness supplies it (`delta_ne_nil_of_grew`), not as a carried field. -/
theorem cannot_thread_unconditional : ¬ DeltaAlwaysNonempty := by
  intro h
  have hde : DeltaEq ⟨0⟩ ⟨0⟩ [] := by simp [DeltaEq]
  exact (h ⟨0⟩ ⟨0⟩ [] hde) rfl

#guard ([7] : List Nat).length == 1        -- the nonempty seam delta
#guard ([] : List Nat).length == 0          -- the degenerate run's empty delta (carrier would lie)

end Tests.Reflections.ProgressWitnessCertifiesDelta
