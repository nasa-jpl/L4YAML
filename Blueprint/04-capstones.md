# Capstone theorems

The top-down specification of what L4YAML guarantees. Every lemma
in the repository must justify its existence by traceable use
(transitively) in one of the theorems below.

**Status legend**
- ✅ proved (no `sorry`, kernel-checked)
- 🧩 proved conditional on an unproved hypothesis
- 🚧 partially proved (contains `sorry`s but not abandoned)
- ⏳ planned, not started
- 📝 stated only in a docstring/comment; not yet declared as a Lean theorem
- ❓ stated but possibly unsound — needs audit
- 🗑 deletion candidate (see [`05-current-state.md`](05-current-state.md))

Each capstone entry shows: **Module** · **Status** · **One-line
meaning**. Where relevant, **Depends on** names the immediate
predecessors in the dependency DAG.

---

## Group 1 — Pipeline composition

The scanner and parser compose to `parseYaml`. These theorems nail
down how the layers fit together.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 1.1 | `parseYaml_pipeline` | [`Composition`](../L4YAML/Proofs/Composition.lean) | ✅ |
| 1.2 | `parseYamlRaw_pipeline` | `Composition` | ✅ |
| 1.3 | `parseYamlRaw_ok_decompose` | `Composition` | ✅ |
| 1.4 | `parseYaml_of_parseYamlRaw_ok` | `Composition` | ✅ |
| 1.5 | `parseYaml_ok_iff` | [`Completeness`](../L4YAML/Proofs/Completeness.lean) | ✅ |
| 1.6 | error-propagation theorems (`parseYamlRaw_scan_error`, `parseYamlRaw_parse_error`) | `Composition` | ✅ |

**Role**: these are the "plumbing" theorems — they say that if
`scanFiltered` succeeds with tokens *T* and `parseStream T` succeeds
with docs *D*, then `parseYaml` succeeds with `D.map compose`. No
soundness or completeness claims here, just compositional decomposition.

---

## Group 2 — Scanner correctness

Lexical-layer guarantees: every output token is well-formed, positions
are monotonic, termination is certified.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 2.1 | `scan_produces_valid_tokens` | [`ScannerCorrectness`](../L4YAML/Proofs/ScannerCorrectness.lean) | 🚧 (3 `sorry`s) |
| 2.2 | `advance_offset_lt` | [`ScannerProgress`](../L4YAML/Proofs/ScannerProgress.lean) | ✅ |
| 2.3 | `scanLoop_success_emits_streamEnd` | `ScannerCorrectness` | ✅ |
| 2.4 | `scanNextToken_preserves_bound` | [`ScannerBound`](../L4YAML/Proofs/ScannerBound.lean) | ✅ |
| 2.5 | `advance_preserves_wellFormed` | [`ScannerLoopInvariant`](../L4YAML/Proofs/ScannerLoopInvariant.lean) | ✅ |
| 2.6 | `scan_full_consumption` | [`ScanStrictCoupling`](../L4YAML/Proofs/ScanStrictCoupling.lean) | ✅ |
| 2.7 | Simple-key lifecycle: `saveSimpleKey_*`, `scanKey`, `scanValue` preserve `WellFormed` | [`ScannerSimpleKey`](../L4YAML/Proofs/ScannerSimpleKey.lean) | ✅ |
| 2.8 | Dispatch preservation: `scanNextToken` branches preserve `WellFormed` | [`ScannerDispatch`](../L4YAML/Proofs/ScannerDispatch.lean) | ✅ |
| 2.9 | Document-marker WF: `scanDirective`, `scanDocumentStart`, `scanDocumentEnd` preserve `WellFormed` | [`ScannerDocument`](../L4YAML/Proofs/ScannerDocument.lean) | ✅ |

**Depends on**: surface coupling (Group 8).

---

## Group 3 — Parser correctness

Syntactic-layer guarantees: parser output corresponds to a valid
grammar derivation; anchors grow; aliases resolve; anchors are
well-formed.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 3.1 | `parseStream_sound` | [`ParserSoundness`](../L4YAML/Proofs/ParserSoundness.lean) | ✅ |
| 3.2 | `yamlValue_has_witness` (mutual recursion with `Classical.choice`) | `ParserSoundness` | ✅ |
| 3.3 | `parseNode_anchors_grow` | [`ParserAnchorProofs`](../L4YAML/Proofs/ParserAnchorProofs.lean) / [`ParserNodeProofs`](../L4YAML/Proofs/ParserNodeProofs.lean) | ✅ |
| 3.4 | `parseNode_aliases_resolve'` | `ParserAnchorProofs` / `ParserNodeProofs` | ✅ |
| 3.5 | `parseDocument_aliases_resolve` | `ParserAnchorProofs` | ✅ |
| 3.6 | `parseStream_output_aliases_resolve` | `ParserAnchorProofs` | ✅ |
| 3.7 | `parseStream_output_anchors_wellformed` | [`ParserWfaProofs`](../L4YAML/Proofs/ParserWfaProofs.lean) | ✅ |
| 3.8 | `parseStream_output_grammable` | [`ParserGrammable`](../L4YAML/Proofs/ParserGrammable.lean) | ✅ |
| 3.9 | `parseYaml_produces_valid_nodes` | `ParserGrammable` | ✅ |
| 3.10 | `parseStream_respects_grammar` | [`ParserCorrectness`](../L4YAML/Proofs/ParserCorrectness.lean) | 🧩 (conditional) |
| 3.11 | `parseStream_respects_grammar_unconditional` | [`EndToEndCorrectness`](../L4YAML/Proofs/EndToEndCorrectness.lean) | ✅ |
| 3.12 | `grammar_value_roundtrip` (completeness direction) | [`ParserCompleteness`](../L4YAML/Proofs/ParserCompleteness.lean) | ✅ (noncomputable) |
| 3.13 | `parseStream_complete` | `ParserCompleteness` | ✅ (noncomputable, conditional on grammability) |
| 3.14 | `soundness_completeness_compose` | `ParserCompleteness` | ✅ |

**Depends on**: Group 2 (scanner). The "unconditional" suffix
(theorem 3.11) means the grammability hypothesis has been
discharged via Group 3.8.

---

## Group 4 — End-to-end correctness

Top-level guarantees on `parseYaml`. These are the public promises.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 4.1 | `parse_sound` | [`EndToEndCorrectness`](../L4YAML/Proofs/EndToEndCorrectness.lean) | ✅ |
| 4.2 | `parse_sound_documents` | `EndToEndCorrectness` | ✅ |
| 4.3 | `parse_complete` | `EndToEndCorrectness` | ✅ |
| 4.4 | `parse_produces_valid_yaml` | `EndToEndCorrectness` | ✅ |
| 4.5 | `parse_produces_valid_documents` | `EndToEndCorrectness` | ✅ |
| 4.6 | `parse_produces_valid_stream` | `EndToEndCorrectness` | ✅ |
| 4.7 | `parse_deterministic` | `EndToEndCorrectness` | ✅ |
| 4.8 | `parse_respects_eq` | `EndToEndCorrectness` | ✅ |
| 4.9 | `parseYaml_implies_validYaml` | `EndToEndCorrectness` | ✅ |
| 4.10 | `parseYaml_implies_valid_token_stream` | `EndToEndCorrectness` | ✅ |
| 4.11 | `parseYaml_implies_valid_document` | `EndToEndCorrectness` | ✅ |
| 4.12 | `parseYaml_implies_valid_stream` | `EndToEndCorrectness` | ✅ |

**Claim**: after the blueprint pivot, these twelve are the **target
set** of user-facing guarantees. Every other theorem either feeds
one of these or is a candidate for deletion.

**Depends on**: Groups 1–3.

---

## Group 5 — Value semantics (soundness at the runtime-value level)

The AST-to-value conversion faithfully implements the Core Schema.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 5.1 | `toYamlValue_correct` | [`Soundness`](../L4YAML/Proofs/Soundness.lean) | 🚧 (1 `sorry`) |
| 5.2 | `nodeToValue_total` | `Soundness` | ✅ |
| 5.3 | `nodeToValue_deterministic` | `Soundness` | ✅ |
| 5.4 | `scalar_content_preserved` | `Soundness` | ✅ |
| 5.5 | `validYaml_construct` | `Soundness` | ✅ |
| 5.6 | `isNull_*`, `isBool_*`, `isInt_*`, `isFloat_*` correctness (§10.3) | [`SchemaResolution`](../L4YAML/Proofs/SchemaResolution.lean) | ✅ |
| 5.7 | `resolveImplicit_completeness` | `SchemaResolution` | ✅ |
| 5.8 | `resolve_structural_preservation` | `SchemaResolution` | ✅ |

**Depends on**: Group 3 (parser correctness).

---

## Group 6 — Round-trip properties

`parseYaml ∘ emit` and `parseYaml ∘ dump` recover content-equivalent
values.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 6.1 | `contentEq_refl` | [`RoundTrip`](../L4YAML/Proofs/RoundTrip.lean) | ✅ |
| 6.2 | `contentEq_symm` | `RoundTrip` | ✅ |
| 6.3 | `contentEq_trans` | `RoundTrip` | ✅ |
| 6.4 | `emit_content_invariant` | [`ScannerEmitBridge`](../L4YAML/Proofs/ScannerEmitBridge.lean) | ✅ |
| 6.5 | `escapeTag_roundtrip` | `RoundTrip` | ✅ |
| 6.6 | `resolve_eq_of_resolveEq` (mutual) | [`RoundTripComposition`](../L4YAML/Proofs/RoundTripComposition.lean) | ✅ |
| 6.7 | `resolve_eq_of_contentEq_noTags` | `RoundTripComposition` | ✅ |
| 6.8 | `emit_roundtrip_content_eq` (canonical-emitter closure) | [`EmitterScannability`](../L4YAML/Proofs/EmitterScannability.lean) | 🚧 (15 `sorry`s) |
| 6.9 | `universal_roundtrip` | `EmitterScannability` | 🚧 |
| 6.10 | Phase-E universal round-trip: `∀ v, Grammable v false → ∃ docs, parseYaml (emit v) = .ok docs ∧ docs.size = 1 ∧ contentEq v docs[0]!.value = true` | (in docstring of `Completeness`, `RoundTrip`) | 📝 (aspirational, not declared) |
| 6.11 | `dumpTyped_*`, `contentRoundTrips_*` | [`SchemaDump`](../L4YAML/Proofs/SchemaDump.lean), [`DumpRoundTrip`](../L4YAML/Proofs/DumpRoundTrip.lean) | ✅ for concrete instances |
| 6.12 | `resolve_toYaml_*`, `fromYaml_toYaml_*` type round-trips | [`SchemaComposition`](../L4YAML/Proofs/SchemaComposition.lean) | ✅ for concrete instances |

**The gap**: capstone 6.10 is the *universal* (∀ v) round-trip and
currently lives only in docstrings. Proving it discharges
the emitter's left-inverse property at the value level and closes
the round-trip story.

**Depends on**: Group 4 (parse), Group 5 (values).

---

## Group 7 — Grammar-production derivations

Decomposes every scanner output as a full YAML 1.2.2 grammar
derivation tree — the structural form of Group 2.1.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 7.1 | `scan_content_gives_stream_v2` (full SLYamlStream derivation) | [`StreamAccum`](../L4YAML/Proofs/StreamAccum.lean) | 🚧 (28 `sorry`s, 5 architectural) |
| 7.2 | `scanLoop_grammar_prod` | `StreamAccum` | 🚧 |
| 7.3 | Per-function `*_prod` theorems (flow/block/document start/end, anchor/alias, tag, directive) | [`StructureProduction`](../L4YAML/Proofs/StructureProduction.lean) / [`DocumentProduction`](../L4YAML/Proofs/DocumentProduction.lean) / [`ScalarProduction`](../L4YAML/Proofs/ScalarProduction.lean) / [`NodeProduction`](../L4YAML/Proofs/NodeProduction.lean) | 🚧 (3, 3, 5, 0 `sorry`s resp.) |
| 7.4 | `parseYaml_implies_valid_token_stream` (bridge to Group 4) | `EndToEndCorrectness` | ✅ |

**Note**: Group 7 is the *strongest* form of scanner correctness —
not "output is well-formed" but "output = a specific derivation tree
in the YAML 1.2.2 grammar." Its sorries cluster at composition
boundaries.

**Depends on**: Group 2 (scanner), Group 8 (coupling).

---

## Group 8 — Surface coupling (character ↔ implementation)

Shows every scanner step's character-level behavior matches a
surface-syntax predicate.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 8.1 | `SIndent_*`, `GChar_*` character-level predicates | [`SurfaceCoupling`](../L4YAML/Proofs/SurfaceCoupling.lean) | ✅ |
| 8.2 | `scanFlowSequenceStart/End_corr`, `scanFlowMappingStart/End_corr` | [`StructureCoupling`](../L4YAML/Proofs/StructureCoupling.lean) | ✅ |
| 8.3 | `scanDirective_corr`, `scanAnchorOrAlias_corr`, `scanTag_corr` | `StructureCoupling` | ✅ |
| 8.4 | `scanBlockScalar_corr`, `collectDoubleQuotedLoop_corr`, `collectPlainScalarLoop_corr` | [`ScalarCoupling`](../L4YAML/Proofs/ScalarCoupling.lean) | ✅ |
| 8.5 | `skipSpacesLoop_corr`, `consumeNewline` coupling | [`ScannerCoupling`](../L4YAML/Proofs/ScannerCoupling.lean) | ✅ |

**Role**: these are the "bridge from characters to tokens" theorems —
the conscience of the scanner.

---

## Decomposition: what is *not* a capstone

The following are **infrastructure**, not capstones. They exist to
support the theorems above and should be deletable if unused:

- `parser_fuel_mono_succ` and its 24 sub-theorems (`_mono_step`,
  `_mono_zero`) — currently support only one concrete use at
  `ParserWellBehaved.lean:7265`. See
  [`05-current-state.md`](05-current-state.md) for disposition.
- `parseNode_fuel_mono_succ`, `parseSinglePairMapping_fuel_mono_succ` —
  declared but have **zero external callers** (grep-verified).
  **Deletion candidates**.
- `parseFlowSequenceLoop_fuel_mono` — has exactly one caller; should
  be proved directly as a specialized lemma without the full
  `parser_fuel_mono_succ` machinery.
- All per-function `_mono_step` / `_mono_zero` / `Parse*_succ`
  abbreviations — internal scaffolding for `parser_fuel_mono_succ`.
  Fate tied to that theorem.
- All `_ag`, `_aar`, `_wfa` per-function lemmas in
  `ParserNodeProofs`, `ParserAnchorProofs`, `ParserWfaProofs` — these
  are the mutual-induction scaffolding for capstones 3.3, 3.4, 3.7.
  Keep; they genuinely contribute.

---

## Adversarial-instantiation coverage

**Which capstones have a computational-check test in
[`Tests/AdversarialInstantiation.lean`](../Tests/AdversarialInstantiation.lean)?**

| Priority | Coverage | Capstones exercised |
| -------- | -------- | ------------------- |
| 1 | 9g, 9h filtered characterization | 6.8 partial |
| 2 | 9c, 9d emit round-trip content-eq | 6.4, 6.8 |
| 3 | 9a, 9b parser fuel sufficiency | 4.1 (indirect) |
| 4 | 9e scanner prefix invariant | 2.1, 8.* |
| 5 | BoundInv preservation | 2.4 |
| 6 | ScanChain_filtered_prefix, flow-parser helpers | 2.*, 3.* |
| 7 | `handleBlockMappingKeyEntry_mono_step` | *no capstone* — helper only |

**Gaps**:
- No adversarial coverage for Group 4 (end-to-end) as a whole.
- No adversarial coverage for Group 5 (value semantics).
- No adversarial coverage for Group 6.10 (universal round-trip —
  natural, since it's only aspirational).
- No adversarial coverage for `parser_fuel_mono_succ` or any of its
  24 sub-parts — which is how `parseBlockSequence_mono_zero`'s
  unsoundness escaped review.

Address in [`06-discipline.md`](06-discipline.md).
