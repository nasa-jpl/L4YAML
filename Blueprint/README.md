# L4YAML Blueprint

A top-down specification of L4YAML: what it **is**, what it **guarantees**,
and how those guarantees decompose into modules and theorems.

This blueprint was introduced on 2026-04-21 after a bottom-up proof
effort (`parser_fuel_mono_succ` and related `_mono_zero` theorems)
exposed that the repository was accumulating theorems without a
top-down anchor. Specifically:

- `parseBlockSequence_mono_zero` (and siblings) turned out to be
  **unsound as stated** — the statement was written by analogy with
  flow-sequence monotonicity without reference to a caller's need.
- The enclosing `parser_fuel_mono_succ` machinery (~500 LoC, 24
  sub-theorems, 28 `sorry`s) was built to unlock **one** downstream
  call site, and its two documented consumer wrappers
  (`parseNode_fuel_mono_succ`, `parseSinglePairMapping_fuel_mono_succ`)
  have **zero** callers outside their own definitions.
- The companion adversarial-instantiation suite (1,827 lines, 7
  priorities) does **not** exercise any of the 24 fuel-monotonicity
  parts; its "Priority 7 audit" only covers a lifted helper.

The purpose of this blueprint is to make the proof effort
**goal-driven** rather than **accumulation-driven**: every lemma
should justify itself by traceable use in a capstone theorem, and
every capstone theorem should be declared *before* its proof is
attempted.

## How to read this blueprint

Read in order on first visit:

1. [`01-terminology.md`](01-terminology.md) — what the domain words
   mean in L4YAML. Establishes shared vocabulary.
2. [`02-architecture.md`](02-architecture.md) — the pipeline, data
   flow, and module boundaries.
3. [`03-code-organization.md`](03-code-organization.md) — proposed
   folder layout (code first; proofs to follow).
4. [`04-capstones.md`](04-capstones.md) — the complete list of
   capstone theorems, grouped by guarantee category, with current
   status (✅ proved / ⏳ planned / 🚧 partial / ❓ unsound /
   🗑 deletion candidate).
5. [`05-current-state.md`](05-current-state.md) — honest accounting
   of where we are: sorry count, deletion candidates, claims that
   need reconciling against reality (`Overview.lean` says "Zero
   `sorry`" — that is aspirational; actual grep shows ~100).
6. [`06-discipline.md`](06-discipline.md) — the discipline going
   forward: blueprint-first theorem proposals, adversarial
   instantiation before proof, sorry policy.

## Relationship to existing documentation

This blueprint **does not replace** the Verso-based manual at
[`doc/Doc/L4YAML/`](../doc/Doc/L4YAML/). That manual is a
published-audience document. This blueprint is an **internal
working document** that drives the proof backlog. Eventually
(per point (b) of the pivot conversation), the blueprint may be
refactored using `verso-blueprint` so that capstones can be
cross-linked with their Lean definitions directly; until then,
markdown is the medium.

## Relationship to existing plan docs

[`../PARSER_WELLBEHAVED_PLAN.md`](../PARSER_WELLBEHAVED_PLAN.md),
[`../EMITTER_SCANNABILITY_PLAN.md`](../EMITTER_SCANNABILITY_PLAN.md),
and similar plan documents at the repository root are **tactical**
plans tied to specific proof files. The blueprint is **strategic**:
it says *which properties matter* and *why*, from which the tactical
plans derive. When a tactical plan's premise no longer aligns with
the blueprint (as happened with `parser_fuel_mono_succ`), the
blueprint wins.

## Contributor workflow

Before proposing a new theorem:

1. Locate (or add) a capstone in [`04-capstones.md`](04-capstones.md)
   that needs this theorem as a dependency.
2. Add the theorem's statement to the relevant module's section in
   that file *before* attempting the proof.
3. Add an adversarial-instantiation test that would refute the
   statement if false, *before* attempting the proof.
4. Prove it; update status in [`05-current-state.md`](05-current-state.md).

This sequence catches statement errors at step 3 (cheap) rather
than step 4 (expensive).

## Recommended work plan

The blueprint as written (2026-04-21) is a *description* of the
target state. This section lays out the concrete initiatives that
move the repository toward it. Two initiatives run in parallel: a
**code reorganization** driven by
[`03-code-organization.md`](03-code-organization.md), and a
**mechanical capstone verification** that cross-checks
[`04-capstones.md`](04-capstones.md) against the actual Lean
dependency graph.

### Initiative 1 — Code reorganization

Goal: make every terminology entry in
[`01-terminology.md`](01-terminology.md) findable in ≤ 2 clicks
from the top of `L4YAML/`. Four phases; each phase is one PR,
each PR ends on a green build.

**Phase 1 — Non-code moves (risk: low) ✅ done 2026-04-21**

Landed as `ad12e204` (12 top-level files into
`Spec/`, `Parser/`, `Output/`, `Config/`, `FFI/`, `Token/`,
`Scanner/`) and `573fa76e` (Phase 1b — `Schema.lean` and
`Surface.lean` moved into their folders as
`Schema/Schema.lean` / `Surface/Surface.lean` for symmetry).

- **Tooling used**: `git mv` for each file; one `sed` pass over
  `^import L4YAML.Foo$` for imports; `lake build` gate.
- **Scripts**:
  [`scripts/refactor-phase-1.sh`](../scripts/refactor-phase-1.sh),
  [`scripts/refactor-phase-1b.sh`](../scripts/refactor-phase-1b.sh)
  — reversible via commit revert.
- **Acceptance**: `lake build` passes 429/429 with only the
  expected baseline sorry warnings; smoke tests green.
- **Blast radius (observed)**: ~110 files touched across `L4YAML/`,
  `Tests/`, `L4YAML.lean`, `gen-suite-guards.py`. `L4YAML.FGM` and
  the Doc/Verso files had no direct imports of the moved modules
  and did not need updates.

**Phase 2 — Scanner split (risk: medium) ✅ done 2026-04-21**

Broke monolithic `L4YAML/Scanner/Scanner.lean` (~2761 LoC, not the
~920 LoC originally estimated) into seven submodules:
[`State.lean`](../L4YAML/Scanner/State.lean),
[`Whitespace.lean`](../L4YAML/Scanner/Whitespace.lean),
[`Indent.lean`](../L4YAML/Scanner/Indent.lean),
[`Document.lean`](../L4YAML/Scanner/Document.lean),
[`NodeProperties.lean`](../L4YAML/Scanner/NodeProperties.lean),
[`Scalar.lean`](../L4YAML/Scanner/Scalar.lean),
[`SimpleKey.lean`](../L4YAML/Scanner/SimpleKey.lean).
[`Scanner/Scanner.lean`](../L4YAML/Scanner/Scanner.lean) (~560 LoC)
became the dispatch umbrella owning flow-collection indicator
scanners and the `scanNextToken` / `scan` / `scanLoop` main loop.
The blueprint originally listed six submodules; `NodeProperties.lean`
was added to give YAML §6.9 (anchors + aliases + tags) its own home,
matching the spec-section pattern used by the other submodules
(`Whitespace` ≈ §6.1–§6.7, `Document` ≈ §6.8 + §9.1.2,
`Scalar` ≈ §7.3 + §8.1, `SimpleKey` ≈ §7.4 + §8.2).

- **Tooling used**: `Write` for the seven new files; `Edit` for the
  blueprint and Verso-doc cross-references; `lake build` gate.
- **Acceptance met**: `lake build` 443/443 (warnings only on
  pre-existing `sorry`s in `ParserWellBehaved.lean` and
  `EmitterScannability.lean` baselines); `scannertests` 32/32,
  `scannerspecexamples` 132/132, `validationtests` 84/84,
  `rawparsetests` 29/29; `Architecture.lean` updated to list all
  seven submodules.
- **Blast radius**: zero changes to consumers — every submodule
  declares `namespace L4YAML.Scanner`, and `Scanner/Scanner.lean`
  re-imports them, so `import L4YAML.Scanner.Scanner` continues to
  see the same public API.  ~28 importing files unchanged.
- **Annotations added**: while splitting, defs that implement a
  named YAML 1.2.2 production but lacked `@[yaml_spec ...]` were
  tagged: `collectCommentTextLoop`, `skipBlankLinesLoop`,
  `collectPlainScalar_terminates?`, `collectPlainScalar_handleBlockLineBreak`,
  `consumeExactSpaces`, `collectLineContentLoop`,
  `autoDetectBlockScalarIndent*`, `validateTrailingContent`,
  `skipDocEndWhitespace`, `skipTrailingSpaces`, `isBlockEntryCandidate`,
  `isKeyCandidate`, `scanNextToken_dispatch{Structural,FlowIndicators,
  BlockIndicators,Content}`, `scanNextToken_preprocess`,
  `scanNextToken_checkBlockFlowIndent`, `scanFiltered`, `scanLoopFull`,
  `scanWithComments`, plus the `Loop`-suffixed helpers for spec
  productions whose terminating wrapper was already tagged.

**Phase 3 — Parser split (risk: medium) ✅ done 2026-04-21**

Broke monolithic `L4YAML/Parser/TokenParser.lean` (~1191 LoC) into
four files along its existing logical seams:
[`State.lean`](../L4YAML/Parser/State.lean) (~285 LoC) holds
`ParseState`, the navigation/consumption accessors,
`NodeProperties`, `parseNodeProperties`, `resolveTag`, `emptyNode`,
`applyNodeFinalization`, and `validateNodeProps` — everything the
mutual block touches but that doesn't itself recurse.
[`Fuel.lean`](../L4YAML/Parser/Fuel.lean) (~50 LoC) factors out the
`initialFuel := 4 * tokens.size + 4` formula referenced by
`parseDocument` and proof capstones.
[`TokenParser.lean`](../L4YAML/Parser/TokenParser.lean) (~535 LoC)
keeps the 14-function mutually-recursive block plus
`StreamState` / `validNextToken`, `parseDirectives`,
`prepareDocumentState`, `parseDocument`, and `parseStream` — i.e.
everything that depends on the recursive descent and the document
boundary table.
[`Composition.lean`](../L4YAML/Parser/Composition.lean) (~205 LoC)
is the new umbrella holding the user-facing pipeline: `scanAndParse`,
`parseYaml{,Raw,Single,SingleRaw}`, the comment classifiers
(`classifyCommentPosition`, `classifyDocumentComments`,
`partitionCommentsByDocument`), and `parseYamlWithComments`.

- **Tooling used**: `Write` for the four files; bulk `Python`
  substitution to redirect 48 importers from
  `import L4YAML.Parser.TokenParser` to
  `import L4YAML.Parser.Composition` (transitive imports keep the
  `L4YAML.TokenParser.foo` API surface intact); `Edit` for the
  blueprint and Verso-doc cross-references; `lake build` gate.
- **Acceptance met**: `lake build` 449/449 (warnings only on
  pre-existing `sorry`s in `ParserWellBehaved.lean` and
  `EmitterScannability.lean` baselines).  Test suites observed:
  `rawparsetests` 29/29, `validationtests` 84/84, `flowtests` 88/88,
  `explicitkeytests` 149/149, `scannertests` 32/32,
  `scannerspecexamples` 132/132, `dumproundtrip` 117/117,
  `specexamples` 132/132, `propertytests` 124/124,
  `productioncoverage` 26/26, `adversarialinstantiation`
  2455/2473 (the 18 failures are the same pre-existing semantic-gap
  baseline, unchanged by the refactor).
  `Architecture.lean` updated to list all four files.
- **Blast radius**: 49 importing files updated by a one-line
  substitution; no behavioural changes. The only file that still
  imports `L4YAML.Parser.TokenParser` directly is
  `L4YAML/Parser/Composition.lean` itself — by design, since
  Composition wraps the mutual block.
- **Why one umbrella, not the literal blueprint**: the original
  blueprint text envisioned `TokenParser.lean` keeping its public
  API; in practice `parseYaml*` had to move into Composition.lean to
  avoid a circular import (Composition needs `parseStream` from the
  mutual block).  Routing imports through Composition.lean keeps
  the user-facing API name stable (`L4YAML.TokenParser.parseYaml`)
  while honouring the file-layout intent.

**Phase 4 — Proofs reorganization (risk: low per-cluster)**

Move [`L4YAML/Proofs/*.lean`](../L4YAML/Proofs/) into role-named
subfolders (Foundation/, Errors/, Schema/, Contracts/, Production/,
Scanner/, Output/, Parser/, Coupling/, RoundTrip/). One cluster per
PR; each leaves build green.

- **Ordering principle**: Foundation/ first (low-level utilities,
  few inbound references), then clusters in order of coupling
  (Scanner/ before Parser/ before the Composition.lean capstone).
  Within that constraint, smaller/less-coupled clusters come first
  to keep risk monotonic.
- **Mechanical pattern** (established by PR 1): `git mv` + anchored
  `sed` over `^import L4YAML.Proofs.Foo$`. Namespaces stay at
  `L4YAML.Proofs.Foo` (no rename into the subcluster path) so
  consumer `open` statements work unchanged — same precedent as
  Phase 1.
- **Acceptance per PR**: `lake build` green; the
  capstone-regeneration pipeline from Initiative 2 still produces
  the same dependency graph before and after.
- **Overlap resolutions** (where the draft target layout in
  [`03-code-organization.md`](03-code-organization.md) listed a
  file under two subfolders):
    - `*Coupling.lean` files (SurfaceCoupling, ScalarCoupling,
      StructureCoupling) → **Coupling/** (role-based home). The
      `Surface/` subcluster is dropped — its only listed contents
      were these coupling files, and `Surface.lean` itself is code,
      not proofs.
    - `DumpRoundTrip.lean` → **Output/** (proof about the Dump
      function), not `Document/`.
    - `CommentProperties.lean` (unlisted in the draft) →
      **RoundTrip/**, paired with `CommentRoundTrip.lean`.
    - `ScannerPlainContent.lean` (unlisted) → **Scanner/**.
    - The draft's `Document/` subcluster is renamed to
      **Contracts/** and holds just the two contract files
      (`BlockScalarContracts`, `DocumentContracts`).

**Cluster roadmap (10 PRs, Foundation + 9 remaining)**

| PR | Cluster | Files | LoC (approx) | Capstone groups | Risk |
| -- | ------- | ----: | -----------: | --------------- | ---- |
| 1 | Foundation/ ✅ | 4 | ~1,100 | (infra only) | low |
| 2 | Errors/ ✅ | 3 | ~900 | — | low |
| 3 | Schema/ ✅ | 4 | ~850 | 5 (SchemaResolution), 6 (SchemaDump, SchemaComposition) | low |
| 4 | Contracts/ ✅ | 2 | ~500 | — | low |
| 5 | Production/ ✅ | 7 | ~7,500 | 7 (all production theorems) | medium |
| 6 | Scanner/ ✅ | 18 | ~9,700 | 2 (all scanner correctness), 6 partial, 7 partial | medium (size) |
| 7 | Output/ ✅ | 3 | ~11,000 | 6 (EmitterScannability, ScannerEmitBridge, DumpRoundTrip) | medium (EmitterScannability is ~10k LoC) |
| 8 | Parser/ ✅ | 9 | ~12,000 | 3 (all parser correctness) | medium (size + mutual-rec imports) |
| 9 | Coupling/ ✅ | 5 | ~2,400 | 8 (all surface coupling), 7 boundary | low |
| 10 | RoundTrip/ ✅ | 4 | ~2,200 | 6 (RoundTrip, RoundTripComposition, CommentRoundTrip) | low |

**Capstones that stay at `Proofs/` root** (not moved into subclusters
— they are the top-down anchors of
[`04-capstones.md`](04-capstones.md)):
[`Composition.lean`](../L4YAML/Proofs/Composition.lean),
[`Completeness.lean`](../L4YAML/Proofs/Completeness.lean),
[`Soundness.lean`](../L4YAML/Proofs/Soundness.lean),
[`EndToEndCorrectness.lean`](../L4YAML/Proofs/EndToEndCorrectness.lean).

**Final target layout** (post-PR-10):
```
L4YAML/Proofs/
├── Foundation/   CharClass, LawfulBEq, StringProperties, ValueAlgebra
├── Errors/       ErrorProperties, EscapeResolution, FoldNewlines
├── Schema/       SchemaResolution, SchemaComposition, SchemaDump, TagResolution
├── Contracts/    BlockScalarContracts, DocumentContracts
├── Production/   StreamAccum, StructureProduction, ScalarProduction,
│                 DocumentProduction, NodeProduction, PreprocessProduction,
│                 ScannerPlainScalarValid
├── Scanner/      ScannerCorrectness, ScannerProgress, ScannerBound,
│                 ScannerDispatch, ScannerDocument, ScannerSimpleKey,
│                 ScannerLoopInvariant, ScannerContracts, ScannerWhitespace,
│                 ScannerPlainScalar, ScannerPlainContent, ScannerDoubleQuoted,
│                 ScannerScalar, ScannerFlowCollection, ScannerIndentStack,
│                 ScannerIndent, ScannerProofs, ScanStrictCoupling
├── Output/       EmitterScannability, ScannerEmitBridge, DumpRoundTrip
├── Parser/       ParserSoundness, ParserCompleteness, ParserCorrectness,
│                 ParserNodeProofs, ParserAnchorProofs, ParserWfaProofs,
│                 ParserWellBehaved, ParserGrammable, ParserGrammableBase
├── Coupling/     CouplingBridge, ScannerCoupling, SurfaceCoupling,
│                 StructureCoupling, ScalarCoupling
├── RoundTrip/    RoundTrip, RoundTripComposition, CommentRoundTrip,
│                 CommentProperties
│
├── Composition.lean         -- capstone (Group 1 pipeline composition)
├── Completeness.lean        -- capstone (Group 1 + Group 3.12–3.14)
├── Soundness.lean           -- capstone (Group 5 value semantics)
└── EndToEndCorrectness.lean -- capstone (Group 4 public guarantees)
```

**Phase 4 · Foundation/ ✅ done 2026-04-21**

Moved four low-level utility proofs into
[`L4YAML/Proofs/Foundation/`](../L4YAML/Proofs/Foundation/):
[`CharClass.lean`](../L4YAML/Proofs/Foundation/CharClass.lean),
[`LawfulBEq.lean`](../L4YAML/Proofs/Foundation/LawfulBEq.lean),
[`StringProperties.lean`](../L4YAML/Proofs/Foundation/StringProperties.lean),
[`ValueAlgebra.lean`](../L4YAML/Proofs/Foundation/ValueAlgebra.lean).

- **Tooling used**: `git mv` for each file; one anchored `sed` pass
  over `^import L4YAML.Proofs.Foo$` for imports. Namespaces left
  untouched (same precedent as Phase 1 — files continue to declare
  `namespace L4YAML.Proofs.CharClass` etc., so `open` lines in
  consumers work unchanged).
- **Script**:
  [`scripts/refactor-phase-4-foundation.sh`](../scripts/refactor-phase-4-foundation.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (warnings only on the
  pre-existing `sorry`s in `EmitterScannability.lean` baseline).
- **Blast radius**: 4 renames + 5 touched importers
  (`L4YAML.lean`, `ParserAnchorProofs.lean`, `ParserWfaProofs.lean`,
  `ScannerPlainScalar.lean`, `StructureProduction.lean`) +
  narrative references in `README.md`, `L4YAML/Proofs/README.md`,
  `FoldNewlines.lean`, `Completeness.lean`.

**Phase 4 · Errors/ ✅ done 2026-04-22**

Moved three error-domain proofs into
[`L4YAML/Proofs/Errors/`](../L4YAML/Proofs/Errors/):
[`ErrorProperties.lean`](../L4YAML/Proofs/Errors/ErrorProperties.lean),
[`EscapeResolution.lean`](../L4YAML/Proofs/Errors/EscapeResolution.lean),
[`FoldNewlines.lean`](../L4YAML/Proofs/Errors/FoldNewlines.lean).

- **Tooling used**: same pattern as the Foundation/ cluster —
  `git mv` + one anchored `sed` pass over `^import L4YAML.Proofs.Foo$`.
  Namespaces left untouched.
- **Script**:
  [`scripts/refactor-phase-4-errors.sh`](../scripts/refactor-phase-4-errors.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (same pre-existing
  `sorry` warnings as the prior cluster).
- **Blast radius**: 3 renames + 3 touched importers
  (`L4YAML.lean`, `Tests/Guards/Proofs/EscapeResolution.lean`,
  `Tests/Guards/Proofs/FoldNewlines.lean`) + one narrative
  reference in `EXCEPTIONS.md`.

**Phase 4 · Schema/ ✅ done 2026-04-22**

Moved four schema-domain proofs into
[`L4YAML/Proofs/Schema/`](../L4YAML/Proofs/Schema/):
[`SchemaComposition.lean`](../L4YAML/Proofs/Schema/SchemaComposition.lean),
[`SchemaDump.lean`](../L4YAML/Proofs/Schema/SchemaDump.lean),
[`SchemaResolution.lean`](../L4YAML/Proofs/Schema/SchemaResolution.lean),
[`TagResolution.lean`](../L4YAML/Proofs/Schema/TagResolution.lean).

- **Tooling used**: same pattern as the Foundation/ and Errors/
  clusters — `git mv` + one anchored `sed` pass over
  `^import L4YAML.Proofs.Foo$`. Namespaces left untouched.
- **Script**:
  [`scripts/refactor-phase-4-schema.sh`](../scripts/refactor-phase-4-schema.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (same pre-existing
  `sorry` warnings as the prior clusters).
- **Blast radius**: 4 renames + 4 touched importers
  (`L4YAML.lean`, `Tests/Guards/Proofs/SchemaComposition.lean`,
  `Tests/Guards/Proofs/SchemaDump.lean`,
  `Tests/Guards/Proofs/SchemaResolution.lean`) + narrative
  references in `README.md`, `Blueprint/01-terminology.md`,
  `Blueprint/04-capstones.md`, and `EXCEPTIONS.md`.

**Phase 4 · Contracts/ ✅ done 2026-04-22**

Moved two contract proofs into
[`L4YAML/Proofs/Contracts/`](../L4YAML/Proofs/Contracts/):
[`BlockScalarContracts.lean`](../L4YAML/Proofs/Contracts/BlockScalarContracts.lean),
[`DocumentContracts.lean`](../L4YAML/Proofs/Contracts/DocumentContracts.lean).

- **Tooling used**: same pattern as the Foundation/, Errors/, and
  Schema/ clusters — `git mv` + one anchored `sed` pass over
  `^import L4YAML.Proofs.Foo$`. Namespaces left untouched.
- **Script**:
  [`scripts/refactor-phase-4-contracts.sh`](../scripts/refactor-phase-4-contracts.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (same pre-existing
  `sorry` warnings as the prior clusters).
- **Blast radius**: 2 renames + 1 touched importer (`L4YAML.lean`,
  two import lines) + narrative references in
  `Blueprint/03-code-organization.md` and `Blueprint/README.md`.
  No test guards exist for these contract proofs, and no other
  in-repo narrative docs reference them by path.

**Phase 4 · Production/ ✅ done 2026-04-22**

Moved seven production-theorem proofs into
[`L4YAML/Proofs/Production/`](../L4YAML/Proofs/Production/):
[`StreamAccum.lean`](../L4YAML/Proofs/Production/StreamAccum.lean),
[`StructureProduction.lean`](../L4YAML/Proofs/Production/StructureProduction.lean),
[`ScalarProduction.lean`](../L4YAML/Proofs/Production/ScalarProduction.lean),
[`DocumentProduction.lean`](../L4YAML/Proofs/Production/DocumentProduction.lean),
[`NodeProduction.lean`](../L4YAML/Proofs/Production/NodeProduction.lean),
[`PreprocessProduction.lean`](../L4YAML/Proofs/Production/PreprocessProduction.lean),
[`ScannerPlainScalarValid.lean`](../L4YAML/Proofs/Production/ScannerPlainScalarValid.lean).

- **Tooling used**: same pattern as the Foundation/, Errors/,
  Schema/, and Contracts/ clusters — `git mv` + one anchored `sed`
  pass over `^import L4YAML.Proofs.Foo$`. The seven-way internal
  cross-imports among production files were rewritten in-place by
  the same sed pass. Namespaces left untouched.
- **Script**:
  [`scripts/refactor-phase-5-production.sh`](../scripts/refactor-phase-5-production.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (same pre-existing
  `sorry` warnings as the prior clusters).
- **Blast radius**: 7 renames + 6 external importers touched
  (`L4YAML.lean` seven import lines; `L4YAML/Surface/Surface.lean`
  one line; `ParserAnchorProofs.lean`, `ParserGrammableBase.lean`,
  `ParserGrammable.lean`, `ParserWellBehaved.lean` one line each)
  + internal cross-imports among the moved files + narrative
  references in `Blueprint/README.md` and
  `Blueprint/03-code-organization.md`. No test-guard files import
  these production proofs directly.

**Phase 4 · Scanner/ ✅ done 2026-04-22**

Moved eighteen scanner-correctness proofs into
[`L4YAML/Proofs/Scanner/`](../L4YAML/Proofs/Scanner/):
[`ScannerCorrectness.lean`](../L4YAML/Proofs/Scanner/ScannerCorrectness.lean),
[`ScannerProgress.lean`](../L4YAML/Proofs/Scanner/ScannerProgress.lean),
[`ScannerBound.lean`](../L4YAML/Proofs/Scanner/ScannerBound.lean),
[`ScannerDispatch.lean`](../L4YAML/Proofs/Scanner/ScannerDispatch.lean),
[`ScannerDocument.lean`](../L4YAML/Proofs/Scanner/ScannerDocument.lean),
[`ScannerSimpleKey.lean`](../L4YAML/Proofs/Scanner/ScannerSimpleKey.lean),
[`ScannerLoopInvariant.lean`](../L4YAML/Proofs/Scanner/ScannerLoopInvariant.lean),
[`ScannerContracts.lean`](../L4YAML/Proofs/Scanner/ScannerContracts.lean),
[`ScannerWhitespace.lean`](../L4YAML/Proofs/Scanner/ScannerWhitespace.lean),
[`ScannerPlainScalar.lean`](../L4YAML/Proofs/Scanner/ScannerPlainScalar.lean),
[`ScannerPlainContent.lean`](../L4YAML/Proofs/Scanner/ScannerPlainContent.lean),
[`ScannerDoubleQuoted.lean`](../L4YAML/Proofs/Scanner/ScannerDoubleQuoted.lean),
[`ScannerScalar.lean`](../L4YAML/Proofs/Scanner/ScannerScalar.lean),
[`ScannerFlowCollection.lean`](../L4YAML/Proofs/Scanner/ScannerFlowCollection.lean),
[`ScannerIndentStack.lean`](../L4YAML/Proofs/Scanner/ScannerIndentStack.lean),
[`ScannerIndent.lean`](../L4YAML/Proofs/Scanner/ScannerIndent.lean),
[`ScannerProofs.lean`](../L4YAML/Proofs/Scanner/ScannerProofs.lean),
[`ScanStrictCoupling.lean`](../L4YAML/Proofs/Scanner/ScanStrictCoupling.lean).

- **Tooling used**: same pattern as the Foundation/, Errors/,
  Schema/, Contracts/, and Production/ clusters — `git mv` + one
  anchored `sed` pass over `^import L4YAML.Proofs.Foo$`.  The dense
  internal cross-imports among the eighteen scanner proofs were
  rewritten in-place by the same sed pass.  Namespaces left untouched.
- **Script**:
  [`scripts/refactor-phase-6-scanner.sh`](../scripts/refactor-phase-6-scanner.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (same pre-existing
  `sorry` warnings as the prior clusters).
- **Note on count**: the roadmap row above was drafted as 17 files;
  the target layout in `03-code-organization.md` and the detailed
  bullet list in this README both enumerate 18 (including
  `ScannerPlainContent.lean`, which was added to the Scanner/ cluster
  during the preliminary survey at line 258 of this README).  The
  row is now ✅ at 18.
- **Blast radius**: 18 renames + many external importers rewritten
  (`L4YAML.lean` seventeen import lines; `EndToEndCorrectness.lean`
  one line; `ParserCorrectness.lean` one line; `EmitterScannability.lean`
  two lines; `Production/DocumentProduction.lean`,
  `Production/StreamAccum.lean`, `Production/ScalarProduction.lean`,
  `Production/ScannerPlainScalarValid.lean` — four files with one or
  more lines each; fourteen `Tests/Guards/Proofs/Scanner*.lean`
  guard files — one line each) + internal cross-imports among the
  moved files + narrative references in `Blueprint/README.md` and
  `Blueprint/03-code-organization.md`.

**Phase 4 · Output/ ✅ done 2026-04-22**

Moved three emitter/dumper-correctness proofs into
[`L4YAML/Proofs/Output/`](../L4YAML/Proofs/Output/):
[`EmitterScannability.lean`](../L4YAML/Proofs/Output/EmitterScannability.lean),
[`ScannerEmitBridge.lean`](../L4YAML/Proofs/Output/ScannerEmitBridge.lean),
[`DumpRoundTrip.lean`](../L4YAML/Proofs/Output/DumpRoundTrip.lean).

- **Tooling used**: same pattern as the Foundation/, Errors/,
  Schema/, Contracts/, Production/, and Scanner/ clusters —
  `git mv` + one anchored `sed` pass over
  `^import L4YAML.Proofs.Foo$`.  The one internal cross-import
  (`EmitterScannability` → `ScannerEmitBridge`) was rewritten
  in-place by the same sed pass.  Namespaces left untouched.
- **Script**:
  [`scripts/refactor-phase-7-output.sh`](../scripts/refactor-phase-7-output.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (same pre-existing
  `sorry` warnings in `EmitterScannability.lean` — seven
  declarations at lines 8169, 8665, 8757, 8839, 9057, 9773, 9812
  of the moved file — carried over unchanged from the baseline).
- **Blast radius**: 3 renames + external importers rewritten
  (`L4YAML.lean` three import lines; `Tests/DumpRoundTrip.lean`
  one line; `Tests/Guards/Proofs/DumpRoundTrip.lean` and
  `Tests/Guards/Proofs/ScannerEmitBridge.lean` one line each) +
  one internal cross-import + narrative references in
  `Blueprint/README.md` and `Blueprint/03-code-organization.md`.

**Phase 4 · Parser/ ✅ done 2026-04-22**

Moved nine parser-correctness proofs into
[`L4YAML/Proofs/Parser/`](../L4YAML/Proofs/Parser/):
[`ParserSoundness.lean`](../L4YAML/Proofs/Parser/ParserSoundness.lean),
[`ParserCompleteness.lean`](../L4YAML/Proofs/Parser/ParserCompleteness.lean),
[`ParserCorrectness.lean`](../L4YAML/Proofs/Parser/ParserCorrectness.lean),
[`ParserNodeProofs.lean`](../L4YAML/Proofs/Parser/ParserNodeProofs.lean),
[`ParserAnchorProofs.lean`](../L4YAML/Proofs/Parser/ParserAnchorProofs.lean),
[`ParserWfaProofs.lean`](../L4YAML/Proofs/Parser/ParserWfaProofs.lean),
[`ParserWellBehaved.lean`](../L4YAML/Proofs/Parser/ParserWellBehaved.lean),
[`ParserGrammable.lean`](../L4YAML/Proofs/Parser/ParserGrammable.lean),
[`ParserGrammableBase.lean`](../L4YAML/Proofs/Parser/ParserGrammableBase.lean).

- **Tooling used**: same pattern as the Foundation/, Errors/,
  Schema/, Contracts/, Production/, Scanner/, and Output/ clusters —
  `git mv` + one anchored `sed` pass over
  `^import L4YAML.Proofs.Foo$`.  The cluster's mutual-recursion
  internal imports (seven cross-import lines across
  `ParserWellBehaved`, `ParserAnchorProofs`, `ParserGrammable`,
  `ParserWfaProofs`, `ParserNodeProofs`, `ParserCorrectness`, and
  `ParserCompleteness`) were rewritten in-place by the same sed
  pass.  Namespaces left untouched.
- **Script**:
  [`scripts/refactor-phase-8-parser.sh`](../scripts/refactor-phase-8-parser.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (same pre-existing
  `sorry` warnings in `Output/EmitterScannability.lean` carried
  over unchanged from the baseline — no new warnings or failures
  introduced by this cluster).
- **Blast radius**: 9 renames + external importers rewritten
  (`L4YAML.lean` nine import lines;
  `L4YAML/Proofs/EndToEndCorrectness.lean` three lines;
  `L4YAML/Proofs/Foundation/ValueAlgebra.lean` one line;
  `L4YAML/Proofs/Output/ScannerEmitBridge.lean` two lines;
  `L4YAML/Proofs/Output/EmitterScannability.lean` one line;
  `Tests/AdversarialInstantiation.lean` one line;
  `Tests/Guards/Proofs/ParserCorrectness.lean` one line) +
  seven internal mutual-recursion cross-imports + narrative
  references in `Blueprint/README.md` and
  `Blueprint/03-code-organization.md`.

**Phase 4 · Coupling/ ✅ done 2026-04-22**

Moved five scanner↔surface↔grammar coupling proofs into
[`L4YAML/Proofs/Coupling/`](../L4YAML/Proofs/Coupling/):
[`CouplingBridge.lean`](../L4YAML/Proofs/Coupling/CouplingBridge.lean),
[`ScannerCoupling.lean`](../L4YAML/Proofs/Coupling/ScannerCoupling.lean),
[`SurfaceCoupling.lean`](../L4YAML/Proofs/Coupling/SurfaceCoupling.lean),
[`StructureCoupling.lean`](../L4YAML/Proofs/Coupling/StructureCoupling.lean),
[`ScalarCoupling.lean`](../L4YAML/Proofs/Coupling/ScalarCoupling.lean).

- **Tooling used**: same pattern as the Foundation/, Errors/,
  Schema/, Contracts/, Production/, Scanner/, Output/, and Parser/
  clusters — `git mv` + one anchored `sed` pass over
  `^import L4YAML.Proofs.Foo$`.  Three internal cross-import lines
  (`ScannerCoupling` → `CouplingBridge`, `ScalarCoupling` →
  `ScannerCoupling`, `StructureCoupling` → `ScalarCoupling`) were
  rewritten in-place by the same sed pass.  Namespaces left untouched.
- **Script**:
  [`scripts/refactor-phase-9-coupling.sh`](../scripts/refactor-phase-9-coupling.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (same pre-existing
  `sorry` warnings in `Output/EmitterScannability.lean` carried
  over unchanged from the baseline — no new warnings or failures
  introduced by this cluster).
- **Note on count**: the roadmap row above was drafted as 6 files;
  the target layout in this README and in `03-code-organization.md`
  both enumerate 5.  The row is now ✅ at 5 — the sixth file in the
  original draft never existed in the flat layout.
- **Blast radius**: 5 renames + external importers rewritten
  (`L4YAML.lean` five import lines;
  `L4YAML/Proofs/Production/StructureProduction.lean` one line;
  `L4YAML/Proofs/Production/PreprocessProduction.lean` one line;
  `L4YAML/Proofs/Production/ScalarProduction.lean` one line;
  `L4YAML/Proofs/Scanner/ScanStrictCoupling.lean` one line;
  `L4YAML/Proofs/Output/EmitterScannability.lean` two lines) +
  three internal cross-imports + narrative references in
  `Blueprint/README.md` and `Blueprint/03-code-organization.md`.

**Phase 4 · RoundTrip/ ✅ done 2026-04-22**

Moved the four round-trip and comment-channel proofs into
[`L4YAML/Proofs/RoundTrip/`](../L4YAML/Proofs/RoundTrip/):
[`RoundTrip.lean`](../L4YAML/Proofs/RoundTrip/RoundTrip.lean),
[`RoundTripComposition.lean`](../L4YAML/Proofs/RoundTrip/RoundTripComposition.lean),
[`CommentRoundTrip.lean`](../L4YAML/Proofs/RoundTrip/CommentRoundTrip.lean),
[`CommentProperties.lean`](../L4YAML/Proofs/RoundTrip/CommentProperties.lean).
This closes **Initiative 1 Phase 4** — every non-umbrella proof file
now lives inside a role-named subfolder.

- **Tooling used**: same pattern as the nine preceding clusters —
  `git mv` + one anchored `sed` pass over `^import L4YAML.Proofs.Foo$`.
  No intra-cluster imports existed among the four files (pure renames,
  100% similarity).  Namespaces left untouched.
- **Script**:
  [`scripts/refactor-phase-10-roundtrip.sh`](../scripts/refactor-phase-10-roundtrip.sh)
  — reversible via commit revert.
- **Acceptance met**: `lake build` 449/449 (same pre-existing
  `sorry` warnings in `Output/EmitterScannability.lean` carried
  over unchanged from the baseline — no new warnings or failures
  introduced by this cluster).
- **Blast radius**: 4 renames + external importers rewritten
  (`L4YAML.lean` four import lines;
  `L4YAML/Proofs/Scanner/ScannerDoubleQuoted.lean` one line;
  `L4YAML/Proofs/Output/ScannerEmitBridge.lean` one line;
  `L4YAML/Proofs/Output/EmitterScannability.lean` one line;
  `Tests/Guards/Proofs/RoundTrip.lean` one line;
  `Tests/Guards/Proofs/RoundTripComposition.lean` one line) +
  narrative references in `Blueprint/README.md` and
  `Blueprint/03-code-organization.md`.

**Overall exit criterion for Initiative 1**: `Architecture.lean`
can be regenerated from the actual folder layout instead of
hand-maintained; no top-level `.lean` file in `L4YAML/` besides
the `L4YAML.lean` umbrella (i.e. the repo-root library entry
point that re-exports submodules) — every other file lives inside
a role-named folder.

---

### Initiative 2 — Mechanical capstone verification

Goal: compare the human-written [`04-capstones.md`](04-capstones.md)
against Lean's actual dependency DAG. Catch three classes of drift:

- **Proved capstones that depend on `sorry`** (status should be
  🚧, not ✅).
- **Theorems claimed as capstones that no one actually uses**
  (deletion or downgrade candidates).
- **Proved theorems reachable from multiple capstones that are
  missing from the blueprint** (missing capstones).

**Available tooling** (surveyed 2026-04-21):

| Tool | Repo | Toolchain | Fit |
| ---- | ---- | --------- | --- |
| `theoremgraph` | [`L4YAML.FGM`](../../L4YAML.FGM) (sibling checkout) | Lean 4.30.0-rc1 — matches L4YAML (4.30.0-rc2) closely | **Best fit now.** Already works. Supports `--list`, `--dot`, `--chain`, `--coverage`. Consumes `@[key_theorem "desc"]` attribute (from FGM). |
| `importGraph` | [`leanprover-community/import-graph`](https://github.com/leanprover-community/import-graph), pinned v4.29.0 in L4YAML's lakefile | Already imported | Module-level only; doesn't give theorem-level DAG directly but has the Lean APIs we'd need. |
| `DocVerificationBridge` | `doc-verification-bridge.ghe/DocVerificationBridge` | Lean ≤ 4.29.0 | **Not directly usable yet** — toolchain mismatch (L4YAML is on 4.30.0-rc2). Worth adopting later for the Four-Category Ontology classification. See Phase D. |
| `FGM.KeyTheorem` | [`FGM`](../../FGM) (sibling checkout) | Matches `L4YAML.FGM` | Source of the `@[key_theorem]` attribute. |
| Ad-hoc Lean script using `ConstantInfo.getUsedConstants` | — | any | Fallback if the above fall over. |

**Current coverage**:
[`L4YAML.FGM/KeyTheoremAnnotations.lean`](../../L4YAML.FGM/KeyTheoremAnnotations.lean)
tags only **6 theorems** with `@[key_theorem]`. The blueprint
lists ~45 capstones across 8 groups. The 39-theorem gap is the
immediate tagging backlog.

**Phase A — Tag all capstones (risk: low)**

Extend
[`KeyTheoremAnnotations.lean`](../../L4YAML.FGM/KeyTheoremAnnotations.lean)
with one `attribute [key_theorem "..."] ...` line per ✅ capstone
in [`04-capstones.md`](04-capstones.md). Groups 1–8.

- **Acceptance**: `lake build -p L4YAML.FGM` passes;
  `lake exe theoremgraph --list` outputs ≥ 45 theorem names
  (matches the blueprint count for ✅ rows).
- **Status source-of-truth**: the attribute text is authoritative
  for the theorem's public description; the blueprint mirrors it.

**Phase B — Diff tool (risk: low)**

Add a `scripts/check-capstones.py` (or `.sh`) that:

1. Runs `lake exe theoremgraph --list` and parses the output into
   a set of `{theorem_name, description}`.
2. Parses [`04-capstones.md`](04-capstones.md) for rows of the
   form `| # | `\`theorem_name\`` | module | status |`.
3. Prints the **set difference** in both directions:
   - **In blueprint, not in theoremgraph**: missing `@[key_theorem]`
     attribute.
   - **In theoremgraph, not in blueprint**: missing from blueprint
     or added without a blueprint entry.
4. Exit non-zero if either difference is non-empty.

- **Integration**: run in CI; `make check-blueprint` target; link
  from [`06-discipline.md`](06-discipline.md) Rule 4.
- **Acceptance**: PR adding a theorem either updates the blueprint
  and the annotation, or fails CI.

**Phase C — Sorry-reachability audit (risk: medium)**

For each capstone in
[`04-capstones.md`](04-capstones.md), use
`lake exe theoremgraph --dot <name>` to extract the dependency
DAG, then check whether any transitive dependency contains
`sorry`. Downgrade status from ✅ to 🚧 for any capstone that does.

- **Tooling choices**:
  - Simplest: run `theoremgraph --dot` per capstone, grep each
    output for dependency names that also show up in
    [`05-current-state.md`](05-current-state.md)'s sorry table.
  - Better: extend `theoremgraph` with a `--reaches-sorry` mode
    that classifies capstones as "kernel-checked" vs
    "transitively-conditional-on-sorry".
- **Acceptance**: the ✅ rows in [`04-capstones.md`](04-capstones.md)
  are the minimal set whose proofs are kernel-checked without
  `sorry` in any dependency. This catches the silent drift where
  a capstone's proof is green but a helper it depends on has
  regressed to `sorry`.

**Phase D — DocVerificationBridge integration (risk: high, defer)**

Adopt DocVerificationBridge's Four-Category Ontology once the
toolchain mismatch is resolved. Two routes:

- Wait for DocVerificationBridge to support 4.30.0+ (watch
  [`Experiments/ExperimentsCore.lean:maxSupportedVersion`](../../doc-verification-bridge.ghe/Experiments/Experiments/ExperimentsCore.lean)).
- Or: temporarily branch L4YAML to 4.29.0 for one analysis run,
  record the classification output as a baseline, then rebase
  forward. Only worth doing if the ontology gives us something
  `theoremgraph` doesn't.

The Four-Category value proposition for L4YAML: cleanly separates
**spec-side** (Grammar, Surface, Production — "mathematical
abstractions") from **impl-side** (Scanner, Parser, Emitter —
"computational operations") with **coupling theorems** as the
ontological glue. That mirrors the trust-boundary structure in
[`02-architecture.md`](02-architecture.md). So integration is
valuable long-term, but not blocking.

**Overall exit criterion for Initiative 2**: a CI job runs on
every PR, asserts that every ✅ capstone in the blueprint has
(a) a matching `@[key_theorem]` attribute, (b) a kernel-checked
proof with no `sorry` in its transitive dependency tree, and
(c) a dependency graph that's a subset of other capstones +
acknowledged infrastructure. A failing job points at which of
the three checks broke.

---

### Sequencing

Initiative 2 Phase A (tag all capstones) should go **first** —
it's low-risk, it unlocks the diff tool (Phase B) that catches
drift during Initiative 1's moves, and it validates the
[`04-capstones.md`](04-capstones.md) inventory while the blueprint
is still fresh in memory. Initiative 1 Phase 1 (folder moves) can
run in parallel once Phase A is in place, since the capstone
names don't change during folder moves.

Concrete 1-week target:

1. Day 1–2: Initiative 2 Phase A (tag the remaining ~39
   capstones).
2. Day 2: Initiative 2 Phase B (diff script, wire into CI).
3. Day 3: Run Phase B against current state; reconcile any
   mismatch between blueprint and attributes.
4. Day 4: Initiative 2 Phase C (sorry-reachability audit); update
   ✅/🚧 statuses in [`04-capstones.md`](04-capstones.md).
5. Day 5: Start Initiative 1 Phase 1.
6. Following weeks: Initiative 1 Phases 2, 3, 4 as separate PRs.

Initiative 2 Phase D (DocVerificationBridge) is deferred — revisit
once DVB supports 4.30.0 or after 1–3 land and the rest of the
blueprint is stable.
