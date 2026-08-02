# L4YAML Documentation Index

One line per kept document, so the corpus has a navigable map
(Blueprint/06-discipline.md Rule 4: one source of truth per claim —
each entry names its role; status claims live in the SSOT it points at).

Status tags: **[LIVE]** governs current work · **[REF]** maintained
reference · **[PLAN]** open plan.

## Front door

- [README.md](README.md) [LIVE] — project overview, build/test, matrix, current work plan
- [SUMMARY.md](SUMMARY.md) [REF] — JPL-facing pitch narrative
- [Blueprint/](Blueprint/README.md) [LIVE] — methodology + strategy; start at Blueprint/README.md
  (01 terminology · 02 architecture · 03 code map · **04 capstones = proof-status SSOT** ·
  06 discipline rulebook · 07/08 initiative records, closed)
- [DOCS.md](DOCS.md) — this index

## Open issues & plans

- [NS-CHAR-PREDICATE-GAP.md](NS-CHAR-PREDICATE-GAP.md) [LIVE] — the one open spec-fidelity gap
  (`ns-char` printable/BOM under-approximation) + fix plan
- [VERSION-0.4.8.md](VERSION-0.4.8.md) [PLAN] — grammar completeness (`parse_iff_grammar`,
  capstone row 7.7) roadmap; unblocked since the 0.4.7 closure
- [YAML_MERGE.md](YAML_MERGE.md) [PLAN] — algebraic merge-key design; input to
  `DuplicateKeyPolicy.merge`

## Reference (design & API)

- [LIMITS.md](LIMITS.md) [REF] — DoS threat model, `ParserLimits` presets, tag security
- [C_PYTHON_RUST_APIs.md](C_PYTHON_RUST_APIs.md) [REF] — FFI design + v0.5.0 completion
  record, fixed-pool memory
- [L4YAML/YAML_PRODUCTIONS.md](L4YAML/YAML_PRODUCTIONS.md) [REF] — production cross-reference
  (machine-checked coverage: `Tests/ProductionCoverage.lean`)
- [STRICTNESS.md](STRICTNESS.md) [REF] — Surface layer / `SurfPos` design;
  `parse_strict` & `scan_strict` (proven)
- [SPEC-GAP-ANALYSIS.md](SPEC-GAP-ANALYSIS.md) [REF] — anchor/alias pipeline design
  rationale: why `addAnchor` runs `adaptForFlowContext`, the shape of the
  `WellFormedAnchors` capstone, and the precise scanner-level §7.1 scoping fact
- [YAML_MATRIX_COMPARISON.md](YAML_MATRIX_COMPARISON.md) [REF] — 20-processor comparison;
  **score-provenance SSOT** for the README/SUMMARY matrix claims (builds,
  denominators, comparison-strictness caveats, reproduction commands)

## Methodology essays

- [INTERACTIONS.md](INTERACTIONS.md) [REF] — six proof-breaking code patterns,
  the proof-breakage predictor, `try`-goal-corruption lesson, guard-refactoring log
- [ADVERSARIAL_INSTANTIATION.md](ADVERSARIAL_INSTANTIATION.md) [REF] — refute-before-prove
  method (Blueprint Rule 2) + campaign record
- [MISMATCH.md](MISMATCH.md) [REF] — code/proof architecture-mismatch essay; the design
  rationale for `StreamAccum.lean`'s lagging-accumulator invariant (cited from code)

## History

The development-history corpus (`docs.internal/` and the root campaign
logs: `PROGRESS.md`, `VERSION-0.4.6.md`, `VERSION-0.4.7.md`,
`PARSER_WELLBEHAVED_PLAN.md`, `EMITTER_SCANNABILITY_PLAN.md`,
`FLOW_BALANCED_CHAIN_RESTRICTION.md`, `YAML_MATRIX_100PCT_ASSESSMENT.md`,
`DUPLICATE_KEYS.md`, `EXCEPTIONS.md`) was **deleted on 2026-08-01** after
folding the surviving content into the Blueprint (02 architecture: error
model, scanner-level validation, token-write taxonomy · 04: re-landed
flow-acceptance pointers · 06: `unified-dep-table` retirement sweep ·
08: LoadConfig duplicate-key rationale, BRIDGING risk-callout quotes)
and INTERACTIONS.md. Everything is recoverable from git history
(deletion commit: see `git log -- docs.internal`).
