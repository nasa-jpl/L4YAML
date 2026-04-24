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

<details>
<summary>

Goal: make every terminology entry in
[`01-terminology.md`](01-terminology.md) findable in ≤ 2 clicks
from the top of `L4YAML/`. Four phases; each phase is one PR,
each PR ends on a green build.

</summary>

#### **Phase 1 — Non-code moves (risk: low) ✅ done 2026-04-21**

<details>

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

</details>

#### **Phase 2 — Scanner split (risk: medium) ✅ done 2026-04-21**

<details>

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

</details>

#### **Phase 3 — Parser split (risk: medium) ✅ done 2026-04-21**

<details>

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

</details>

#### **Phase 4 — Proofs reorganization (risk: low per-cluster)**

<details>

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

</details>

#### **Cluster roadmap (10 PRs, Foundation + 9 remaining)**

<details>

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

</details>

#### **Phase 4 · Foundation/ ✅ done 2026-04-21**

<details>

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

</details>

#### **Phase 4 · Errors/ ✅ done 2026-04-22**

<details>

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

</details>

#### **Phase 4 · Schema/ ✅ done 2026-04-22**

<details>

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
  
</details>

#### **Phase 4 · Contracts/ ✅ done 2026-04-22**

<details>

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

</details>

#### **Phase 4 · Production/ ✅ done 2026-04-22**

<details>

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

</details>

#### **Phase 4 · Scanner/ ✅ done 2026-04-22**

<details>

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

</details>

#### **Phase 4 · Output/ ✅ done 2026-04-22**

<details>

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

</details>

#### **Phase 4 · Parser/ ✅ done 2026-04-22**

<details>

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
  
</details>

#### **Phase 4 · Coupling/ ✅ done 2026-04-22**

<details>

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

</details>

#### **Phase 4 · RoundTrip/ ✅ done 2026-04-22**

<details>

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

</details>

</details>

---

### Initiative 2 — Mechanical capstone verification

<details>
<summary>

Goal: compare the human-written [`04-capstones.md`](04-capstones.md)
against Lean's actual dependency DAG. Catch three classes of drift:

</summary>

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
| `DocVerificationBridge` | `doc-verification-bridge.ghe/DocVerificationBridge` | Lean ≤ 4.29.0 | **Not directly usable yet** — toolchain mismatch (L4YAML is on 4.30.0-rc2). Worth adopting later for the Four-Category Ontology classification. See Phase E. |
| `FGM.KeyTheorem` | [`FGM`](../../FGM) (sibling checkout) | Matches `L4YAML.FGM` | Source of the `@[key_theorem]` attribute. |
| Ad-hoc Lean script using `ConstantInfo.getUsedConstants` | — | any | Fallback if the above fall over. |

**Current coverage**:
[`L4YAML.FGM/KeyTheoremAnnotations.lean`](../../L4YAML.FGM/KeyTheoremAnnotations.lean)
tags only **6 theorems** with `@[key_theorem]`. The blueprint
lists ~45 capstones across 8 groups. The 39-theorem gap is the
immediate tagging backlog.

#### **Phase A — Tag all capstones (risk: low)**

<details>
<summary>

Extend
[`KeyTheoremAnnotations.lean`](../../L4YAML.FGM/KeyTheoremAnnotations.lean)
with one `attribute [key_theorem "..."] ...` line per ✅ capstone
in [`04-capstones.md`](04-capstones.md). Groups 1–8.

</summary>

- **Acceptance**: `lake build -p L4YAML.FGM` passes;
  `lake exe theoremgraph --list` outputs ≥ 45 theorem names
  (matches the blueprint count for ✅ rows).
- **Status source-of-truth**: the attribute text is authoritative
  for the theorem's public description; the blueprint mirrors it.

</details>

#### **Phase B — Diff tool (risk: low)**

<details>
<summary>

`lake exe check-capstones` (in
[`L4YAML.FGM/tools/CheckCapstones.lean`](../../L4YAML.FGM/tools/CheckCapstones.lean))

</summary>

Written in Lean rather than Python so the catalogue is consumed
as typed data (`KeyTheoremCatalogue.entries : Array (Name × KeyAnnotation)`)
instead of by scraping the `theoremgraph --list` output.

1. Loads the authoritative `@[key_theorem]` set from
   `KeyTheoremCatalogue.entries` — the single source of truth;
   source-level elaboration also populates the env extension so
   `#key_theorems` and all downstream widgets see the same set.
2. Parses [`04-capstones.md`](04-capstones.md) for rows of the form
   `| # | `\`theorem_name\`` | module | status |`. Supports
   `foo_*` suffix wildcards inside backticks for bundle-representative
   rows.
3. Prints the **set difference** in both directions:
   - **Missing**: ✅ blueprint rows whose backtick names have no
     matching catalogue entry.
   - **Extra**: catalogue entries not named by any blueprint row.
4. Exits non-zero on drift (1) or CLI/file errors (2).

Flags:
- `--blueprint <path>` — override default path
  (`../lean4-yaml-verified/Blueprint/04-capstones.md`).
- `--include-partial` — also require annotations for 🚧 / 🧩 rows
  (default: ✅ only).
- `--show-ambiguous` — list rows with no parseable backtick
  identifier (informational).

**Integration**: run in CI (L4YAML.FGM `.github/workflows/`); link
from [`06-discipline.md`](06-discipline.md) Rule 4.

**Acceptance**: PR adding a theorem either updates the blueprint
and `KeyTheoremCatalogue.entries`, or fails CI.

</details>

#### **Phase C — Narrative & tiering (risk: low-medium)**

<details>
<summary>

Turn the flat capstone list into a top-down story with 5–8
headline results and a hierarchical index. Runs **before** the
sorry audit (Phase D) because tiering prunes and reorganises the
capstone set — auditing first would waste effort on entries that
later get demoted.

</summary>

Phase B's diff gate enforces *internal* consistency between the
blueprint and the catalogue. Phase C is about *external*
comprehensibility: someone encountering L4YAML for the first time
shouldn't have to read 50+ rows of `04-capstones.md` to learn what
L4YAML actually proves. They should see a handful of headline
results, each with a plain-English summary and a link to its
supporting theorems.

**The problem we're solving**:

- `04-capstones.md` is organized by **topic** (scanner, parser,
  end-to-end, ...) — useful as a reference, useless as an
  introduction.
- `tmp/graphs/index.html` currently lists all ~400 bipartite
  + chain graphs in arbitrary order, making it practically unusable.
- `theorem-graphs.tar.gz` (published by L4YAML.FGM CI and consumed
  by L4YAML's doc build) contains ~840 SVGs when what the docs
  actually need is a small headline subset — everything else is
  reference material that should live behind a "show all" link, not
  eagerly embedded.
- There is no single pointer that answers "what are the public
  guarantees?" — the answer is spread across Group 4, Group 6,
  Group 7, and parts of Group 3.

**1. Tier types in `FGM.KeyAnnotation`** — ✅ *shipped*

`KeyAnnotation` gains an optional `tier : Option Tier` field.
The design splits what the draft modelled as a flat enum into two
orthogonal axes — a narrative `Role` and an optional bundle
membership — because "which theorem represents a family" and
"where the theorem sits in the narrative" are independent concerns
and a flat enum would need a cross-product of constructors to
cover both.

```lean
inductive Role
  | headline
  | categoryCapstone
  | support
  deriving DecidableEq, Hashable

structure BundleRef where
  name  : String      -- scoped within the annotation's `category`
  isRep : Bool        -- exactly one rep per (category, name)
  deriving DecidableEq, Hashable

structure Tier where
  role   : Role
  bundle : Option BundleRef := none
  deriving DecidableEq, Hashable
```

The existing `category : Option String` field doubles as the
"group" scope — no separate group field was needed. Bundle names
like `mono` can therefore be reused across categories without
prefixing (`parser/mono` vs. `emitter/mono` are distinct by virtue
of their enclosing category).

**Promotional rule**: `headline` subsumes `categoryCapstone`. A
headline is always its category's lead, so a category with a
headline needs no separate `categoryCapstone` entry. This avoids
forcing an artificial second-place pick when the headline already
leads the category. The `KeyAnnotation.isCategoryCapstone`
accessor encodes this — it returns `true` for both `headline` and
`categoryCapstone` roles.

**Invariants** (to be enforced by `check-capstones` in step 6):

1a. Every `category` in use has **at least one** theorem with
    `role ∈ {headline, categoryCapstone}` (so every category has a
    lead).
1b. Every `category` has **at most one** theorem with
    `role = categoryCapstone` (the "promoted" slot; headlines
    subsume it, so a category with ≥1 headline is allowed to have
    zero `categoryCapstone` entries). Headlines themselves are
    **uncapped per category** — a category with multiple first-class
    public promises (e.g. Group 4 with soundness + completeness +
    determinism) can name all of them as headlines.
2. Total theorems with `role = headline` across the catalogue: 5–8
   (soft cap; the front page has a reader-attention budget).
3. For every `(category, bundle.name)` pair, exactly one entry has
   `bundle.isRep = true`.
4. `role ∈ {headline, categoryCapstone}` → `category` is `some _`.
5. Siblings sharing `bundle.name` must share `category`.

**Attribute syntax** (migrated from `(str)? (str)?` to `(str)*`):

```lean
-- Legacy forms still work:
@[key_theorem "parser" "Scanner terminates on well-formed tokens"]
@[key_theorem "Some description only"]

-- New key=value form — auto-detected when the first string begins
-- with `<ident>+=`:
@[key_theorem "cat=parser" "desc=..." "role=categoryCapstone"]
@[key_theorem "cat=parser" "desc=..." "role=support" "bundle=mono"]
@[key_theorem "cat=parser" "desc=..." "role=support" "bundle=mono:rep"]
@[key_theorem "cat=parser" "desc=..." "role=headline" "bundle=mono:rep"]
```

Recognised keys: `cat`/`category`, `desc`/`description`, `role`,
`bundle`. Unknown keys, malformed values, and `bundle` without
`role` are silently dropped (consistent with the legacy parser's
tolerance for missing args). Role is required to form a `Tier`;
bundle is optional.

Also shipped: accessor helpers on `KeyAnnotation` — `role?`,
`bundle?`, `bundleName?`, `isBundleRep`, `isHeadline`,
`isCategoryCapstone`. `#key_theorems` now displays tier info when
present.

**2. Headline slate** — ✅ *shipped*

Seven headlines tagged in
[`L4YAML.FGM/KeyTheoremCatalogue.lean`](../../L4YAML.FGM/KeyTheoremCatalogue.lean)
with `tier := some { role := .headline }` and an explicit
`category`. Group 4 carries three headlines (soundness,
completeness, determinism) — admissible under Invariant 1b's
"headlines are uncapped per category" clause, since all three are
genuinely first-class public promises.

| # | Headline | Category | Status | Why experts expect it | Plain-English summary |
|---|----------|----------|--------|-----------------------|-----------------------|
| 3.1 | `parseStream_respects_grammar_unconditional` | `parser` | ✅ | spec conformance | "parser output matches the written YAML 1.2.2 grammar" |
| 4.1 | `parse_sound`                                | `end-to-end` | ✅ | soundness | "if we accept, the result is well-formed" |
| 4.2 | `parse_complete`                             | `end-to-end` | ✅ | completeness | "every well-formed YAML is accepted" |
| 4.3 | `parse_deterministic`                        | `end-to-end` | ✅ | functionality | "the parser is a function, not a relation" |
| 5.1 | `validYaml_construct`                        | `values` | ✅ | value-level soundness | "every successful parse yields a `ValidYaml`" |
| 6.1 | `universal_roundtrip`                        | `roundtrip` | 🚧 (sorry via 6.9) | round-trip | "emit then parse gives back the same content" |
| 7.1 | `parse_strict_proof`                         | `grammar-production` | 🚧 (sorry via 7.2, 7.6) | strictness | "we never accept ill-formed input" |

5 of 7 are ✅. The two 🚧 entries are front-page-admissible per
the rule below, with their open sorry sites named in the status
column and the description string.

**Categories without a headline** (Groups 1 pipeline, 2 scanner,
8 surface-coupling) need a `role = categoryCapstone` pick in
step 3 (backfill) to satisfy Invariant 1a.

Each headline will eventually get:
- A 1-sentence plain-English summary (non-expert-readable).
- The formal statement in full.
- A 1-paragraph "what this means in practice" block.
- A pointer to supporting theorems (for the expert reader).

Headlines that are 🚧/🧩 are allowed on the front page *iff* the
open conditions or remaining sorry sites are clearly stated in the
plain-English summary. Headlines that regress drop off the front
page until they recover.

**3. Tier-filtered graph generation + hierarchical `index.html`** — ✅ *shipped*

[`L4YAML.FGM/tools/TheoremGraph.lean`](../../L4YAML.FGM/tools/TheoremGraph.lean)
now accepts two filter flags:

- `--tier <csv>` — emit only entries whose `tier.role` matches the
  CSV list (e.g. `headline`, `headline,categoryCapstone`). Unknown
  values exit non-zero with a diagnostic.
- `--category <csv>` — emit only entries whose `cat=...` annotation
  matches the CSV list (e.g. `parser,end-to-end`). Combines with
  `--tier`.

Emission now writes a **four-layer hierarchy** into the output tree:

1. `index.html` — **Front page.** Each headline's chain graph
   embedded inline (via `<object data=…>`) plus its plain-English
   summary, a link to its blueprint group page, and a preview of
   the first 12 module pages.
2. `group/<category>.html` — **Group pages.** One per blueprint
   category, listing headlines / category capstone / supports in
   priority order with links to the bipartite and chain SVGs.
3. `module/<module.path>.html` — **Module pages.** One per Lean
   file with at least one key theorem, organising its declarations
   in priority order. `modules.html` is a flat index of every
   module (alphabetical, with per-module entry counts). Useful
   when a reader is navigating from the file system — e.g. "what
   does `L4YAML/Proofs/Parser/ParserWellBehaved.lean` contribute?"
4. `all.html` — **Full catalogue.** A lightweight table (no
   embedded SVGs — the old SVG-per-row form crushed the browser
   with 800+ concurrent requests) that lists every entry in scope
   with its role, category, module, and direct SVG links.

The SVG output tree is also **module-based** now (was
namespace-based). A declaration in `L4YAML/Proofs/Parser/ParserWellBehaved.lean`
lands at `L4YAML/Proofs/Parser/ParserWellBehaved/<decl>.bipartite.dot`
regardless of its `namespace` declaration. This is a no-ops change
for files that follow the `L4YAML.Proofs.<Leaf>` convention, but
makes the output a faithful reflection of the source-file layout
for the handful of files that don't.

**Chain-depth classifier**: the chain renderer dispatches on four
`ChainDepth` classes before drawing:

- `deep` — the elaborated proof term cites ≥ 1 project theorem. The
  classic functorial-chain ladder (functions on the left,
  theorem-proof chain on the right) is rendered. This is ~56% of
  the current catalogue.
- `propBridge` — the proof term cites no project theorems, but the
  type syntactically mentions a `Prop`-typed def (e.g. `ValidYamlProp`,
  `ParseNodeFlowSeqOk`) whose body references additional functions.
  Rendered as the headline + an "About (direct)" cluster + an
  "About (via Prop-unfold)" cluster + a "Catalogue coverage" cluster
  that lists annotated theorems about any of the (direct or
  unfolded) about-functions. The coverage cluster is labelled
  explicitly `(NOT proof deps of the headline)` — it's a navigation
  aid, not a dependency claim.
- `weak` — no project-theorem citations and no extra structure
  revealed by `Prop`-unfolding. Structurally derivable: existence
  by construction (`⟨_, rfl, rfl, rfl⟩`), function-ness by
  injection, or similar. Rendered as one-node-with-about — makes
  visible *why* the chain is empty.
- `noAbout` — the type mentions no project functions at all.
  Rendered as a single node with a diagnostic label; flags likely
  mis-categorisations.

For the 7 headlines specifically this sorts as: 3 `deep`
(`parseStream_respects_grammar_unconditional`, `universal_roundtrip`,
`parse_strict_proof`), 2 `propBridge` (`parse_sound`, `parse_complete`
— both wrapped in `ValidYamlProp`), 2 `weak` (`parse_deterministic`
proves function-ness by `Except.ok.injEq`; `validYaml_construct` is
an existence tuple). Full-catalogue distribution (411 entries):
232 deep / 12 propBridge / 103 weak / 11 noAbout. The `weak` and
`noAbout` buckets are diagnostic signals worth periodic review.

Numbers from the current tree: `theoremgraph --tier headline`
emits 7 bipartite + 7 chain DOTs (one per headline, 14 files).
`--tier headline,categoryCapstone` emits 20 DOTs (7 headlines + 3
categoryCapstones in headline-less groups × 2 = 20). The full run
stays at 411 bipartite + 411 chain = 822 files (the extra vs. 56
annotated entries come from the in-degree ≥ 5 heuristic backfill).

The 30×-60× size reduction (14/822 for headlines, 40/822 for
headlines+capstones) is the wedge between "L4YAML doc page loads
in seconds" and "doc page times out." Step 4 lands the CI artifact
split that ships the trimmed tarball to the L4YAML doc build.

**4. L4YAML.FGM release artifact split**

The L4YAML.FGM CI workflow currently publishes a single
`theorem-graphs.tar.gz` containing every SVG. Update it to publish
two artifacts per release:

- `theorem-graphs-headlines.tar.gz` — `--tier headline,categoryCapstone`
  output. Small (~50 SVGs + the hierarchical index), always embedded
  by L4YAML's doc build.
- `theorem-graphs-all.tar.gz` — the full catalogue (today's tarball
  content). Downloaded on demand from the release page; not embedded.

L4YAML's doc build (in the L4YAML repo, not L4YAML.FGM) pulls only
the headlines tarball by default. A visitor who wants the full
catalogue follows a link on the narrative page to the GitHub
release asset. This keeps the default doc build fast and keeps the
exhaustive material one click away.

**5. Narrative file**

New `Blueprint/01-what-we-prove.md` (sits before `02-architecture.md`
in the reading order). Walks the headlines top-down, links each
to its row in `04-capstones.md` for the formal statement and to
the corresponding chain graph (served from the
`theorem-graphs-headlines.tar.gz` artifact L4YAML's doc build has
already unpacked). Written to be readable by a YAML user who is not
a formal-methods expert, but precise enough for the expert to follow
the links through.

**6. CI gates: `check-capstones` extension + `check-file-headers`**

Two companion CI gates.

*6a. `check-capstones --require-headlines-proven`*: fail CI if any
headline entry has status 🚧 (partial) or 🗑 (deletion candidate).
Stricter than the default ✅/🚧-agnostic check.

*6b. `check-file-headers`* — shipped as a new
[`lake exe check-file-headers`](../../L4YAML.FGM/tools/CheckFileHeaders.lean).
Scans `## Key Result` sections of every
`L4YAML/**/*.lean` docstring, extracts backticked identifiers, and
flags any that don't resolve to a declaration anywhere under the
scan root. Catches the common drift pattern where a "Key Result:
`foo_bar`" claim survives a rename/remove of `foo_bar` in the file
itself.

Scope is intentionally narrow (`## Key Result` only, not the full
docstring) because scanning the whole header produced ~600 false
positives from backticked Lean-core types (`Nat`, `Prop`) and
tactic names (`simp`, `native_decide`). A prose-variable and
keyword filter trims the remaining noise. Switch on `--scan-all-header`
for a noisy one-off audit.

Wired into
[`L4YAML.FGM/.github/workflows/generate-graphs.yml`](../../L4YAML.FGM/.github/workflows/generate-graphs.yml)
as a fail-fast gate after `check-capstones`. Four pre-existing
stale references were fixed in the same PR that introduced the
gate:

- `ScannerLoopInvariant.lean` → `advance_preserves_offset_bound` was
  renamed to `advance_preserves_wellFormed` (the actual theorem, now
  catalogued as capstone 2.6; `advance_offset_le` discharges the
  offset-bound sub-claim the old prose described).
- `EscapeResolution.lean` → `isValidChar` rewritten to point to the
  in-file wrapper `char_isValidChar` around Lean's core
  `UInt32.isValidChar`; `unicodeEscape` replaced with the actual
  scanner function `parseHexEscape`, and the FFFD-fallback prose
  corrected (no such fallback; out-of-range inputs produce
  `.unicodeOutOfRange`).
- `ScannerDoubleQuoted.lean` → `escapeTag_isSome_iff_isEscapedChar`
  renamed to `escapeTag_isSome_implies_isEscapedChar` (only the
  forward direction is proved, and the full iff is architecturally
  impossible: `isEscapedChar` also covers unnamed C0 controls that
  `escapeTag` doesn't witness).

**Acceptance**:

- Every headline has plain-English, formal, and practical
  descriptions in `01-what-we-prove.md`.
- `theorem-graphs-headlines.tar.gz` is under a small size budget
  (say 2 MB uncompressed, vs. today's ~30 MB) and contains only the
  headline + category-capstone SVGs plus the hierarchical index.
- L4YAML's doc build embeds the headlines tarball by default; the
  full catalogue is a one-click download from the release page.
- A reader new to the project can answer "what does L4YAML
  prove?" after 5 minutes of reading, without opening any `.lean`
  file.

**Risk**: the curation is a judgment call that changes as proofs
mature. Mitigation: headlines are declarative (tagged entries),
not code; they can be re-tiered in a single PR when the proof
state shifts.

</details>

#### **Phase D — Sorry-reachability audit (risk: medium)**

<details>
<summary>

For each capstone in
[`04-capstones.md`](04-capstones.md), use
`lake exe theoremgraph --dot <name>` to extract the dependency
DAG, then check whether any transitive dependency contains
`sorry`. Downgrade status from ✅ to 🚧 for any capstone that does.

</summary>

Runs after Phase C so the audit targets the tiered set (headlines
and category capstones first, supports last) — not a flat list that
Phase C would then reshuffle.

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

</details>

#### **Phase E — DocVerificationBridge integration (risk: high, defer)**

<details>
<summary>

Adopt DocVerificationBridge's Four-Category Ontology once the
toolchain mismatch is resolved. Two routes:

</summary>

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

</details>

</details>

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
   capstones). **Done 2026-04-22.**
2. Day 2: Initiative 2 Phase B (`lake exe check-capstones`, wire
   into CI). **Done 2026-04-23.**
3. Day 3: Run Phase B against current state; reconcile any
   mismatch between blueprint and attributes. **Done 2026-04-23
   (11 drift items resolved; catalogue pruned from 64 → 56
   entries).**
4. Day 4–5: Initiative 2 Phase C (narrative & tiering) — curate
   the headline slate, add the `Tier` enum, emit split tarballs,
   write `01-what-we-prove.md`. Ordered before Phase D because the
   tiering pass re-scopes the capstone set a sorry audit would
   otherwise waste effort on.
5. Day 6: Initiative 2 Phase D (sorry-reachability audit); update
   ✅/🚧 statuses in [`04-capstones.md`](04-capstones.md) against
   the tiered set.
6. Day 7: Start Initiative 1 Phase 1.
7. Following weeks: Initiative 1 Phases 2, 3, 4 as separate PRs.

Initiative 2 Phase E (DocVerificationBridge) is deferred — revisit
once DVB supports 4.30.0 or after A–D land and the rest of the
blueprint is stable.
