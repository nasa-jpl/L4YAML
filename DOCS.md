# L4YAML Documentation Index

One line per kept document, so the corpus has a navigable map
(Blueprint/06-discipline.md Rule 4: one source of truth per claim —
each entry names its role; status claims live in the SSOT it points at).

Status tags: **[LIVE]** governs current work · **[REF]** maintained
reference · **[PLAN]** open plan · **[CLOSED]** finished-campaign
record · **[HIST]** archived history (`docs.internal/`).

## Front door

- [README.md](README.md) [LIVE] — project overview, build/test, matrix, current work plan
- [SUMMARY.md](SUMMARY.md) [REF] — JPL-facing pitch narrative
- [Blueprint/](Blueprint/README.md) [LIVE] — methodology + strategy; start at Blueprint/README.md
  (01 terminology · 02 architecture · 03 code map · **04 capstones = proof-status SSOT** ·
  06 discipline rulebook · 07/08 initiative records [CLOSED])
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
- [EXCEPTIONS.md](EXCEPTIONS.md) [CLOSED] — error-hierarchy design + retrospective
- [L4YAML/YAML_PRODUCTIONS.md](L4YAML/YAML_PRODUCTIONS.md) [REF] — production cross-reference
  (machine-checked coverage: `Tests/ProductionCoverage.lean`)
- [STRICTNESS.md](STRICTNESS.md) [REF] — Surface layer / `SurfPos` design;
  `parse_strict` & `scan_strict` (proven)
- [SPEC-GAP-ANALYSIS.md](SPEC-GAP-ANALYSIS.md) [CLOSED] — anchor/alias gap rationale
- [DUPLICATE_KEYS.md](DUPLICATE_KEYS.md) [CLOSED] — superseded design; landed form =
  `DuplicateKeyPolicy`/`LoadConfig`

## Methodology essays

- [MISMATCH.md](MISMATCH.md) [CLOSED] — code/proof architecture-mismatch essay
- [INTERACTIONS.md](INTERACTIONS.md) [REF] — six proof-breaking code patterns +
  guard-refactoring log
- [ADVERSARIAL_INSTANTIATION.md](ADVERSARIAL_INSTANTIATION.md) [REF] — refute-before-prove
  method (Blueprint Rule 2) + campaign record

## Campaign records (root)

- [PROGRESS.md](PROGRESS.md) [CLOSED, frozen 2026-03-19] — WFA/well-behavedness log
- [VERSION-0.4.6.md](VERSION-0.4.6.md) / [VERSION-0.4.7.md](VERSION-0.4.7.md) [CLOSED] —
  strictness & universal-round-trip campaigns
- [EMITTER_SCANNABILITY_PLAN.md](EMITTER_SCANNABILITY_PLAN.md) /
  [FLOW_BALANCED_CHAIN_RESTRICTION.md](FLOW_BALANCED_CHAIN_RESTRICTION.md) [CLOSED] —
  tactical proof-campaign logs
- [PARSER_WELLBEHAVED_PLAN.md](PARSER_WELLBEHAVED_PLAN.md) [CLOSED] — superseded plan;
  the Blueprint Rule-5 case study
- [YAML_MATRIX_COMPARISON.md](YAML_MATRIX_COMPARISON.md) [CLOSED] — 20-processor comparison,
  score-provenance SSOT
- [YAML_MATRIX_100PCT_ASSESSMENT.md](YAML_MATRIX_100PCT_ASSESSMENT.md) [CLOSED] —
  100%-matrix campaign log

## Archive — docs.internal/ [HIST]

Thread terminals kept as history (satellite progress notes were deleted
2026-08-01; each terminal carries a status banner):
[README-historical.md](docs.internal/README-historical.md) ·
[BRIDGING.md](docs.internal/BRIDGING.md) (line-pinned by Blueprint/08; append-only) ·
[ANALYSIS.md](docs.internal/ANALYSIS.md) ·
P10.11 terminals (FINAL-STATUS, a-REFLECTION, b/c-SUMMARY, d-FINAL, d-ATTEMPT-LOG,
CASCADE-COMPLETE, COMPLETE-JOURNEY, OPTION2-FINAL-COMPLETE, PROGRESS-UPDATE,
REFACTORING-COMPLETE, SCAN-FIRST-COMPLETE, SCANNEXTTOKEN-ANALYSIS,
PLAN-scanNextToken-ScanInv) ·
[OPTION-A-FINAL-ASSESSMENT.md](docs.internal/OPTION-A-FINAL-ASSESSMENT.md) ·
[STRUCTURAL-THEOREMS-FINAL-STATUS.md](docs.internal/STRUCTURAL-THEOREMS-FINAL-STATUS.md)
