/-!
# Reflection 468 — a `native_decide`/`#guard` satisfiability PROBE of `P(concrete)` whose proof factors
# as `general_reduction (concrete_fact)` is itself a TEMPLATE for the general producer: only the
# `native_decide` leaf is example-specific, so promote the probe by replacing that ONE leaf with a
# structural derivation of the single fact it localized, reusing the generic reduction VERBATIM.

Self-contained (core Lean, no `L4YAML` import) toy modelling the seq-side residual-(2) discharge.

Context (the real situation).  `seqFoldTotal_satisfiable_on_real_output` (R441) was a *satisfiability
probe* — it proved the deferred universal `∀ m, ∃ s, btFold (some []) (tokens.toList.take m) = some s`
on ONE concrete scanned stream, by `native_decide`.  But its proof did NOT `native_decide` the universal
directly: it `native_decide`d the single whole-object fact `WellTyped tokens.toList`
(`btFold (some []) tokens.toList = some []`) and then derived the `∀ m` form GENERICALLY via
`WellTyped_prefix_some` (every prefix of a `WellTyped` list folds to `some`, because `none` is absorbing).

So the probe's proof already factored as `general_reduction (concrete_fact)`, with ONLY the
`WellTyped tokens.toList` leaf example-specific.  Promoting it to the GENERAL, axiom-clean producer
(`seqFoldTotal_of_context`, retiring residual (2) of `seqHRec_of_root_and_context`) was therefore NOT a
new proof: it was replacing the one `native_decide` leaf with a STRUCTURAL derivation of
`WellTyped tokens.toList` (`seqWholeStreamWellTyped` — fold the whole stream
`streamStart :: [ :: interior ++ ] :: streamEnd` piecewise, the interior framing back via
`WellTyped_frame`) and reusing `WellTyped_prefix_some` verbatim.  The probe LOCALIZED exactly which
sub-fact needed generalizing — and was the template for doing it.

This toy reproduces the STRUCTURE:

* `step`/`foldFrom` — a fold with an absorbing failure (`none` on underflow), the `btStep`/`btFold` analog.
* `Whole l` — the whole-object fact (`foldFrom (some 0) l = some 0`), DECIDABLE on a concrete list, so the
  PROBE discharges it with `decide` (the `native_decide` stand-in).
* `AllPrefixesFold l` — the per-prefix deliverable (`∀ m, ∃ s, foldFrom (some 0) (l.take m) = some s`),
  the fold-totality analog.
* `allPrefixesFold_of_whole` — THE GENERAL REDUCTION (`Whole l → AllPrefixesFold l`), producer-AGNOSTIC
  (it consumes only `Whole l`, blind to how it was obtained), the `WellTyped_prefix_some` analog.
* `probe_concrete` — the PROBE: `allPrefixesFold_of_whole concrete (by decide)`.  The `decide` is the lone
  example-specific leaf; the reduction is generic.
* `general_producer` — the GENERAL producer: `allPrefixesFold_of_whole l h_struct`, the SAME reduction,
  with the leaf now a structural `Whole l` (here a hypothesis standing in for `seqWholeStreamWellTyped`).
* `probe_is_producer_at_decide_leaf` — the probe IS the general producer instantiated at the concrete
  list with the `decide`-leaf: same reduction term, differing only in the `Whole` leaf.
-/

namespace ProbeProofFactorsGeneralReduction

set_option autoImplicit false

/-- A fold step that FAILS (`none`) on underflow — `none` is absorbing under `bind`, the `btStep` analog. -/
def step (acc x : Int) : Option Int := if acc + x < 0 then none else some (acc + x)

/-- A fold from a starting accumulator — the `btFold` analog. -/
def foldFrom (s0 : Option Int) (l : List Int) : Option Int :=
  l.foldl (fun a x => a.bind (fun acc => step acc x)) s0

/-- `none` is absorbing — a fold that has already failed stays failed (mirrors `btFold_none`). -/
theorem foldFrom_none (l : List Int) : foldFrom none l = none := by
  induction l with
  | nil => rfl
  | cons x rest ih => show foldFrom none rest = none; exact ih

/-- The fold splits over an append (mirrors `btFold_append`). -/
theorem foldFrom_append (s0 : Option Int) (a b : List Int) :
    foldFrom s0 (a ++ b) = foldFrom (foldFrom s0 a) b := by
  simp [foldFrom, List.foldl_append]

/-- **The WHOLE-OBJECT fact** (toy analog of `WellTyped tokens.toList`): the whole list folds to
    `some 0`.  DECIDABLE on a concrete list — so the PROBE discharges it by `decide` (`@[reducible]` so
    instance resolution sees the underlying `DecidableEq (Option Int)`). -/
@[reducible] def Whole (l : List Int) : Prop := foldFrom (some 0) l = some 0

/-- **The PER-PREFIX DELIVERABLE** (toy analog of fold-totality `∀ m, ∃ s, btFold … = some s`). -/
def AllPrefixesFold (l : List Int) : Prop := ∀ m, ∃ s, foldFrom (some 0) (l.take m) = some s

/-- **THE GENERAL REDUCTION** — `Whole l → AllPrefixesFold l` (toy analog of `WellTyped_prefix_some`).
    Producer-AGNOSTIC: it consumes only `Whole l`, blind to HOW it was obtained.  Because `none` is
    absorbing, a `some`-folding whole forces every prefix to fold to `some`.  THIS is the generic tail
    the probe already had — and that the general producer reuses verbatim. -/
theorem allPrefixesFold_of_whole (l : List Int) (h : Whole l) : AllPrefixesFold l := by
  intro m
  have h2 : foldFrom (some 0) (l.take m ++ l.drop m) = some 0 := by
    rw [List.take_append_drop]; exact h
  rw [foldFrom_append] at h2
  cases hp : foldFrom (some 0) (l.take m) with
  | none => rw [hp, foldFrom_none] at h2; exact absurd h2 (by simp)
  | some s => exact ⟨s, rfl⟩

/-- **THE SATISFIABILITY PROBE** — proves the deliverable on a CONCRETE witness.  Its proof factors as
    `allPrefixesFold_of_whole concrete (decide-leaf)`: the `Whole` leaf is `by decide` (example-specific,
    the `native_decide`/`#guard` analog); the reduction is GENERIC. -/
theorem probe_concrete : AllPrefixesFold [1, -1, 1, -1] :=
  allPrefixesFold_of_whole [1, -1, 1, -1] (by decide)

/-- **THE GENERAL PRODUCER** — proves the deliverable for ANY list, GIVEN the whole-object fact derived
    STRUCTURALLY (here a hypothesis standing in for `seqWholeStreamWellTyped`).  It reuses the SAME
    reduction `allPrefixesFold_of_whole`; only the `Whole` leaf changed from a `decide` to a structural
    proof — exactly the probe→producer promotion. -/
theorem general_producer (l : List Int) (h_struct : Whole l) : AllPrefixesFold l :=
  allPrefixesFold_of_whole l h_struct

/-- **The probe IS the general producer at the `decide`-leaf.**  Instantiating the general producer at
    the concrete list with the `decide` leaf reproduces the probe term: same reduction, differing only in
    the `Whole` leaf.  The probe's proof STRUCTURE localized the lone fact to generalize. -/
theorem probe_is_producer_at_decide_leaf :
    probe_concrete = general_producer [1, -1, 1, -1] (by decide) := rfl

/-- POSITIVE — the whole-object fact holds on the balanced concrete witness (the `decide` leaf). -/
example : Whole [1, -1, 1, -1] := by decide

/-- POSITIVE — a single concrete prefix of the deliverable, `#guard`-checked. -/
example : foldFrom (some 0) (([1, -1, 1, -1] : List Int).take 3) = some 1 := by decide

/-- NEGATIVE — the reduction's whole-object fact is GENUINELY load-bearing: an UNDERFLOWING list
    (`[-1, …]`) is not `Whole` (the first prefix already folds to `none`), so the deliverable cannot be
    produced for it — the probe's `decide` leaf is not a free pass, it asserts real structure. -/
example : ¬ Whole [-1, 1] := by decide

/-- NEGATIVE — and for that underflowing list the deliverable itself FAILS at the `take 1` prefix
    (`foldFrom (some 0) [-1] = none`, so no `s` makes it `some s`), confirming `AllPrefixesFold` is not
    vacuously true: the reduction really needs `Whole`. -/
example : foldFrom (some 0) (([-1, 1] : List Int).take 1) = none := by decide

end ProbeProofFactorsGeneralReduction
