import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 582 — BIRTH PROBE for Front B's brick-3 producer first sub-link (§5.12)

Reflections 579–581 landed the *consumer* side of brick 3's content half: the step algebra (§5.9), the
loop-result append scaffold (§5.10), and the pointwise → fold assembly joint (§5.11). What remains is
the genuinely *hard* PRODUCER — the span-locality / compositionality bridge that supplies, for each `k`,
`contentEq items[k] extra[k] = true` by showing the loop's `k`-th `parseNode` consumes exactly the
sub-span `emit items[k]` of the whole emitted stream. **Reflection 582 lands that producer's FIRST
sub-link** — `emitList_eq_intercalate` / `emitPairList_eq_intercalate` (`ContentFidelity.lean` §5.12):
the purely *emission-structural* fact that the body string `emit.emitList items` IS the per-element
emissions `emit items[k]` glued by the literal separator `", "`:

  `emit.emitList l = ", ".intercalate (l.map emit)`

plus the bracketed whole-`emit` corollaries `emit (.sequence …) = "[" ++ ", ".intercalate … ++ "]"`.
This is exactly the char-list split currently *inlined ad-hoc* inside `emitList_scans_nonempty`
(`ScanChainGrowth.lean:222`), finally factored as a reusable lemma. The scanner-side token-span
decomposition the producer ultimately needs (each inter-`flowEntry` segment of `scanFiltered (emit …)`
equals `scanFiltered (emit items[k])`) cannot even be *stated* until the emitted string is known to be
literally this per-element concatenation.

## Why this probe (inhabitation debt for a VERIFIED-BUT-UNCONSUMED producer sub-link)

The §5.12 lemmas are equations, so they carry no inhabitation debt of their own — Lean verifies them.
But the discipline still bites in two ways for a *verified-but-unconsumed* artifact whose only future
role is to be CONSUMED by the span-locality producer:
1. **Rule 2 (boundary AND non-degenerate).** An emission decomposition that holds only on the empty /
   singleton body — where the separator `", "` never appears — would be a vacuous restatement, useless
   to a producer that must localize each of *several* elements. So probe the boundary (`[]`, `[v]`) AND
   a non-degenerate `≥ 2`-element body where the separators genuinely appear (`emitList_three_*`,
   `emitPairList_two_*`).
2. **Rule 5 (ground against real emission).** A closed form that did not match what `emit` actually
   produces would let the producer localize sub-spans that aren't there. The `*_concrete` /
   `*_per_element_glued` probes `native_decide` the real strings — `emit (.sequence .flow #[a,b,c]) =
   "[a, b, c]"` and, fully expanded, `= "[" ++ emit a ++ ", " ++ emit b ++ ", " ++ emit c ++ "]"` — so
   the per-element sub-spans the producer will split on are exhibited literally.

The lemmas are then APPLIED end-to-end (boundary, non-degenerate, whole-`emit` bracket form, abstract
`*_retype_shape` contract), proving the first sub-link is genuinely consumable, not orphan scaffolding.

The `#print axioms` audits certify the four source lemmas land at `[propext, Classical.choice,
Quot.sound]` — sorry-free. `Classical.choice` appears even though §5.12 is pure list structural
induction with NO `Except` monad: it is pulled by the core `String.intercalate` simp lemmas / `simp`
machinery. Same lesson as §5.11 — a sorry-free structural lemma is routinely choice-dependent;
`#print axioms` it, never assume.
-/

namespace EmissionIntercalate

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: plain scalars and key/value pairs (so `emit` is the bare content string). -/

def a : YamlValue := .scalar { content := "a", style := .plain }
def b : YamlValue := .scalar { content := "b", style := .plain }
def c : YamlValue := .scalar { content := "c", style := .plain }

def ka : YamlValue := .scalar { content := "k1", style := .plain }
def va : YamlValue := .scalar { content := "v1", style := .plain }
def kb : YamlValue := .scalar { content := "k2", style := .plain }
def vb : YamlValue := .scalar { content := "v2", style := .plain }

/-! ## Concrete grounding (rule 5): the closed form IS the real emission — `emit a = "a"` (plain), so
    the intercalation literally produces the comma-space body. -/

theorem emitList_three_concrete : emit.emitList [a, b, c] = "\"a\", \"b\", \"c\"" := by native_decide
theorem emit_seq3_concrete : emit (.sequence .flow #[a, b, c]) = "[\"a\", \"b\", \"c\"]" := by native_decide
theorem emitPairList_two_concrete :
    emit.emitPairList [(ka, va), (kb, vb)] = "\"k1\": \"v1\", \"k2\": \"v2\"" := by native_decide
theorem emit_map2_concrete :
    emit (.mapping .flow #[(ka, va), (kb, vb)]) = "{\"k1\": \"v1\", \"k2\": \"v2\"}" := by native_decide

/-! ## Boundary (rule 2): empty and singleton bodies — the separator `", "` never appears, the closed
    form degenerates correctly (`[] → ""`, `[v] → emit v`). -/

theorem emitList_empty_assembled :
    emit.emitList ([] : List YamlValue) = ", ".intercalate [] :=
  emitList_eq_intercalate []

theorem emitList_singleton_assembled :
    emit.emitList [a] = ", ".intercalate [emit a] :=
  emitList_eq_intercalate [a]

/-! ## Non-degenerate (rule 2): `≥ 2`-element bodies — the separators genuinely appear, so the closed
    form is NOT a vacuous restatement of the empty case. The lemma is APPLIED on real data. -/

theorem emitList_three_assembled :
    emit.emitList [a, b, c] = ", ".intercalate [emit a, emit b, emit c] :=
  emitList_eq_intercalate [a, b, c]

theorem emitPairList_two_assembled :
    emit.emitPairList [(ka, va), (kb, vb)]
      = ", ".intercalate [emit ka ++ ": " ++ emit va, emit kb ++ ": " ++ emit vb] :=
  emitPairList_eq_intercalate [(ka, va), (kb, vb)]

/-! ## The producer-facing closed form: the WHOLE emitted stream, expressed per-element — the exact
    shape the span-locality producer consumes. `emit (.sequence …)` IS its body intercalation bracketed. -/

theorem seq3_bracket_form :
    emit (.sequence .flow #[a, b, c])
      = "[" ++ ", ".intercalate ((#[a, b, c] : Array YamlValue).toList.map emit) ++ "]" :=
  emit_sequence_eq_bracket_intercalate .flow #[a, b, c] none none

theorem map2_bracket_form :
    emit (.mapping .flow #[(ka, va), (kb, vb)])
      = "{" ++ ", ".intercalate ((#[(ka, va), (kb, vb)] : Array (YamlValue × YamlValue)).toList.map
          (fun p => emit p.1 ++ ": " ++ emit p.2)) ++ "}" :=
  emit_mapping_eq_bracket_intercalate .flow #[(ka, va), (kb, vb)] none none

/-! ## The decomposition is genuine, not vacuous: the whole emit is literally the per-element emits
    glued by the `", "` separator the producer splits on (here fully expanded). This is the producer's
    target — `emit a`, `emit b`, `emit c` appear as contiguous sub-spans separated by `", "`. -/

theorem seq3_per_element_glued :
    emit (.sequence .flow #[a, b, c])
      = "[" ++ emit a ++ ", " ++ emit b ++ ", " ++ emit c ++ "]" := by native_decide

/-! ## Abstract residual contract: the producer's first sub-link, for ANY list — the whole emitted
    sequence/mapping body decomposes into per-element emissions joined by `", "`. -/

theorem emitList_retype_shape (l : List YamlValue) :
    emit.emitList l = ", ".intercalate (l.map emit) :=
  emitList_eq_intercalate l

theorem emitPairList_retype_shape (l : List (YamlValue × YamlValue)) :
    emit.emitPairList l = ", ".intercalate (l.map (fun p => emit p.1 ++ ": " ++ emit p.2)) :=
  emitPairList_eq_intercalate l

/-! ## Axiom audit: the four §5.12 lemmas are sorry-free (`[propext, Classical.choice, Quot.sound]`).
    `Classical.choice` enters via the core `String.intercalate` simp lemmas even though §5.12 is pure
    structural induction with NO `Except` monad — `#print axioms` it, never assume. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.emitList_eq_intercalate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms emitList_eq_intercalate

/-- info: 'L4YAML.Proofs.EmitterScannability.emitPairList_eq_intercalate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emitPairList_eq_intercalate

/-- info: 'L4YAML.Proofs.EmitterScannability.emit_sequence_eq_bracket_intercalate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emit_sequence_eq_bracket_intercalate

/-- info: 'L4YAML.Proofs.EmitterScannability.emit_mapping_eq_bracket_intercalate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emit_mapping_eq_bracket_intercalate

end EmissionIntercalate
