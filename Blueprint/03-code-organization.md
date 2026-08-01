# Code organization

The **folder-based** organization of the L4YAML code (proposed
2026-04-21 as a refactor; executed April 2026, extended through
July 2026). Guiding principle: *a newcomer should be able to find
the implementation of any terminology entry in ≤ 2 clicks from the
top of `L4YAML/`*.

## Current state (2026-07-31)

Regenerated from `find L4YAML -name '*.lean'`: **196 files** (65
implementation + 131 proof), toolchain `leanprover/lean4:v4.32.0`.

```
L4YAML/
├── Init.lean                    -- project prelude: the `lemma` command (imported everywhere)
├── CapstoneAttr.lean            -- @[capstone] attribute + #capstones + #assert_capstone_axioms
├── Capstones.lean               -- machine-pinned capstone registry (set + axiom profiles)
├── Spec/         (4)            -- CharPredicates, Grammar, Types, YamlSpec
├── Surface/      (6)            -- Basic, Combinators, Document, Node, Scalars, Surface (umbrella)
├── Token/        (1)            -- Token
├── Algebra/      (13)           -- law library (Initiative 4 Phase 2): AnchorMap, Combinators,
│                                --   Equivalence, Fuel, Idempotence, Indent, LawfulBEq, Position,
│                                --   Schema, StringList, Token, TokenStream, Value
├── Indexed/      (4)            -- intrinsic indexed core (Initiative 4 Phase 3): CharStream,
│                                --   Range, RepGraph, TokenStream
├── Scanner/      (12)           -- Scanner (dispatch umbrella), State, Whitespace, Indent,
│                                --   Document, NodeProperties, Scalar, SimpleKey
│                                -- + indexed twin: IndexedScanner, IndexedState,
│                                --   IndexedDispatch, IndexedPresenter
├── Parser/       (8)            -- TokenParser (18-function mutual block), State, Fuel, Composition
│                                -- + indexed twin: TokenParserIx, ParseStateIx, FuelIx,
│                                --   IndexedComposition (parseYamlSingleIx)
├── Schema/       (6)            -- Schema (umbrella), Api, Deriving, Dump, FromToYaml, Struct
├── Output/       (4)            -- Emitter, Dump, Events, Json
├── Config/       (3)            -- Config, Limits, LoadConfig
├── FFI/          (1)            -- FFI
├── YAML_PRODUCTIONS.md
└── Proofs/       (131)
    ├── Composition.lean / EndToEndCorrectness.lean /
    │   Completeness.lean / Soundness.lean
    │                            -- capstone umbrellas, at Proofs/ root by design
    ├── Foundation/  (2)         -- CharClass, StringProperties
    ├── Errors/      (3)         -- ErrorProperties, EscapeResolution, FoldNewlines
    ├── Schema/      (4)         -- SchemaComposition, SchemaDump, SchemaResolution, TagResolution
    ├── Contracts/   (2)         -- BlockScalarContracts, DocumentContracts
    ├── Production/  (8)         -- StreamAccum, StructureProduction, ScalarProduction,
    │                            --   DocumentProduction, NodeProduction, PreprocessProduction,
    │                            --   ScannerPlainScalarValid, IndexedScannerPlainScalarValid
    ├── Scanner/     (31)        -- 18 classic (ScannerCorrectness … ScanStrictCoupling)
    │                            --   + 13 indexed (IndexedScannerCorrectness hub + 6 submodules,
    │                            --   IndexedRoundtrip, IndexedWhitespace, IndexedIndent, …)
    ├── Parser/      (17)        -- 9 classic + FlowParserAcceptance
    │                            --   + 7 indexed twins (IndexedCompleteness, IndexedCorrectness, …)
    ├── Output/      (51)        -- EmitterScannability.lean (1,551-line hub) + EmitterScannability/
    │                            --   (20 modules); IndexedEmitterScannability.lean hub +
    │                            --   IndexedEmitterScannability/ (27 modules);
    │                            --   ScannerEmitBridge, DumpRoundTrip
    ├── Coupling/    (5)         -- CouplingBridge, ScannerCoupling, SurfaceCoupling,
    │                            --   StructureCoupling, ScalarCoupling
    └── RoundTrip/   (4)         -- RoundTrip, RoundTripComposition, CommentRoundTrip,
                                 --   CommentProperties
```

### Top-level exceptions: the keyword/registry layer

Three files sit at the top of `L4YAML/` outside any role folder —
the sanctioned exceptions to the "every file lives in a role-named
folder" rule (and to Initiative 1's exit criterion in
[`README.md`](README.md)):

- [`Init.lean`](../L4YAML/Init.lean) — the project prelude,
  imported (directly or transitively) by every library module.
  Provides the `lemma` command: per
  [`06-discipline.md`](06-discipline.md) Rule 7, the `theorem`
  keyword is reserved for `@[capstone]` declarations and every other
  proof is a `lemma`.
- [`CapstoneAttr.lean`](../L4YAML/CapstoneAttr.lean) — the
  `@[capstone]` attribute plus the `#capstones` and
  `#assert_capstone_axioms` commands.
- [`Capstones.lean`](../L4YAML/Capstones.lean) — imports the
  capstone-bearing modules and pins the tagged set and per-capstone
  axiom profiles (18 pure / 7 native) with `#guard_msgs`.

They bracket the role folders in the import order — the prelude
below everything, the registry above everything — which is why they
are top-level rather than foldered. CI gates:
[`scripts/check-theorem-keyword.sh`](../scripts/check-theorem-keyword.sh)
(whitelist [`scripts/capstones.txt`](../scripts/capstones.txt)) and
[`scripts/check-import-closure.sh`](../scripts/check-import-closure.sh)
(no orphan modules).

### File-size guideline

Proof modules should stay below roughly **10,000 lines**; past
that, split along lemma-cluster seams (the 2026-07
`EmitterScannability` split — a 1,551-line hub + 20 modules — is
the template). Current outliers, the standing future split
candidates (line counts as of 2026-07-31):

| File | Lines |
|------|------:|
| [`Proofs/Output/EmitterScannability/NonemptyStructure.lean`](../L4YAML/Proofs/Output/EmitterScannability/NonemptyStructure.lean) | 12,169 |
| [`Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`](../L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean) | 11,408 |
| [`Proofs/Scanner/ScannerCorrectness.lean`](../L4YAML/Proofs/Scanner/ScannerCorrectness.lean) | 10,519 |

## Reorganization log (April 2026, historical)

Phase 1 (`ad12e204`) + Phase 1b (`573fa76e`) landed on 2026-04-21.
What's done, what remains:

- **Done**: 14 top-level files collapsed into 9 role-named folders.
  Every top-level file sits inside its matching folder; no more
  orphan siblings. (Since 2026-07-31 there are three sanctioned
  top-level exceptions — `Init.lean`, `CapstoneAttr.lean`,
  `Capstones.lean`, the keyword/registry layer described above.)
- **Done**: `Schema/Dump.lean` vs. top-level `Dump.lean` shadow
  resolved — now `Output/Dump.lean` vs. `Schema/Dump.lean`.
- **Done (Phase 2, 2026-04-21)**: `Scanner/Scanner.lean` (~2761 LoC)
  split into seven submodules: `State.lean`, `Whitespace.lean`,
  `Indent.lean`, `Document.lean`, `NodeProperties.lean`, `Scalar.lean`,
  `SimpleKey.lean`.  `Scanner/Scanner.lean` is now the dispatch
  umbrella (~560 LoC).  The Verso manual at
  [`doc/Doc/L4YAML/Architecture.lean:140`](../doc/Doc/L4YAML/Architecture.lean#L140)
  was updated in lockstep.  Note: the blueprint originally listed six
  submodules; `NodeProperties.lean` was added during Phase 2 to give
  YAML §6.9 (anchors + aliases + tags) its own home, on the rationale
  that other submodules already mirror named spec sections.
- **Done (Phase 3, 2026-04-21)**: `Parser/TokenParser.lean` (~1191 LoC)
  split into four files: `State.lean` (ParseState + helpers),
  `Fuel.lean` (`initialFuel := 4*N+4`), `TokenParser.lean` (the
  then-14 — now 18 — mutually-recursive functions +
  `parseStream`/`parseDocument`), and
  `Composition.lean` (user-facing umbrella owning `parseYaml*`,
  `scanAndParse`, comment classification).  Importers redirected from
  `L4YAML.Parser.TokenParser` → `L4YAML.Parser.Composition` (49 files,
  one-line sed); the `L4YAML.TokenParser.foo` API surface is preserved
  via transitive imports.
- **Done (Phase 4)**: `Proofs/` reorganization is per-cluster.
  **Foundation/** cluster landed 2026-04-21 (4 files: `CharClass.lean`,
  `LawfulBEq.lean`, `StringProperties.lean`, `ValueAlgebra.lean`).
  **Errors/** cluster landed 2026-04-22 (3 files: `ErrorProperties.lean`,
  `EscapeResolution.lean`, `FoldNewlines.lean`).
  **Schema/** cluster landed 2026-04-22 (4 files: `SchemaComposition.lean`,
  `SchemaDump.lean`, `SchemaResolution.lean`, `TagResolution.lean`).
  **Contracts/** cluster landed 2026-04-22 (2 files:
  `BlockScalarContracts.lean`, `DocumentContracts.lean`).
  **Production/** cluster landed 2026-04-22 (7 files: `StreamAccum.lean`,
  `StructureProduction.lean`, `ScalarProduction.lean`, `DocumentProduction.lean`,
  `NodeProduction.lean`, `PreprocessProduction.lean`, `ScannerPlainScalarValid.lean`).
  **Scanner/** cluster landed 2026-04-22 (18 files: `ScannerCorrectness.lean`,
  `ScannerProgress.lean`, `ScannerBound.lean`, `ScannerDispatch.lean`,
  `ScannerDocument.lean`, `ScannerSimpleKey.lean`, `ScannerLoopInvariant.lean`,
  `ScannerContracts.lean`, `ScannerWhitespace.lean`, `ScannerPlainScalar.lean`,
  `ScannerPlainContent.lean`, `ScannerDoubleQuoted.lean`, `ScannerScalar.lean`,
  `ScannerFlowCollection.lean`, `ScannerIndentStack.lean`, `ScannerIndent.lean`,
  `ScannerProofs.lean`, `ScanStrictCoupling.lean`).
  **Output/** cluster landed 2026-04-22 (3 files:
  `EmitterScannability.lean`, `ScannerEmitBridge.lean`,
  `DumpRoundTrip.lean`).
  **Parser/** cluster landed 2026-04-22 (9 files:
  `ParserSoundness.lean`, `ParserCompleteness.lean`,
  `ParserCorrectness.lean`, `ParserNodeProofs.lean`,
  `ParserAnchorProofs.lean`, `ParserWfaProofs.lean`,
  `ParserWellBehaved.lean`, `ParserGrammable.lean`,
  `ParserGrammableBase.lean`).
  **Coupling/** cluster landed 2026-04-22 (5 files:
  `CouplingBridge.lean`, `ScannerCoupling.lean`, `SurfaceCoupling.lean`,
  `StructureCoupling.lean`, `ScalarCoupling.lean`).
  **RoundTrip/** cluster landed 2026-04-22 (4 files:
  `RoundTrip.lean`, `RoundTripComposition.lean`,
  `CommentRoundTrip.lean`, `CommentProperties.lean`) — closes Phase 4.
  The four remaining flat files at `Proofs/` root
  (`Composition.lean`, `EndToEndCorrectness.lean`, `Completeness.lean`,
  `Soundness.lean`) are the top-level capstone umbrellas and belong
  at `Proofs/` root by design per the target layout below.

## Proposed target layout (April-2026 draft)

> Retained for the record. The as-built layout — which additionally
> grew `Algebra/`, `Indexed/`, the indexed `Scanner`/`Parser`
> twins, `Output/{Events,Json}.lean`, `Config/LoadConfig.lean`, and
> the top-level keyword/registry layer — is in
> [Current state (2026-07-31)](#current-state-2026-07-31) above.

```
L4YAML/
├── L4YAML.lean                  -- umbrella module (unchanged)
│
├── Spec/                        -- the reference (trust boundary 2)
│   ├── CharPredicates.lean
│   ├── Grammar.lean
│   ├── YamlSpec.lean            -- named production predicates
│   └── Types.lean               -- YamlValue, YamlDocument, YamlPos
│
├── Surface/                     -- character-level syntax
│   ├── Basic.lean
│   ├── Combinators.lean
│   ├── Document.lean
│   ├── Node.lean
│   ├── Scalars.lean
│   └── Surface.lean             -- umbrella, shared namespace `L4YAML.Surface`
│
├── Token/                       -- token data type
│   └── Token.lean
│
├── Scanner/                     -- lexical layer
│   ├── Scanner.lean             -- umbrella: flow indicators + scanNextToken dispatch + scan/scanFiltered
│   ├── State.lean               -- ScannerState + WellFormed + accessors
│   ├── Whitespace.lean          -- s-white/s-space/s-l-comments + tab detection (§6.1–§6.7)
│   ├── Indent.lean              -- virtual BLOCK-* via unwindIndents/pushSequenceIndent/pushMappingIndent
│   ├── Document.lean            -- ---/... markers + %YAML/%TAG directives (§6.8, §9.1.2)
│   ├── NodeProperties.lean      -- anchors, aliases, tags (§6.9)
│   ├── Scalar.lean              -- escapes + quoted/plain/block scalars (§5.7, §6.5, §7.3, §8.1)
│   └── SimpleKey.lean           -- simple-key resolution + scanBlockEntry/Key/Value (§7.4, §8.2)
│
├── Parser/                      -- syntactic layer
│   ├── TokenParser.lean         -- the mutual block (now 18 functions)
│   ├── State.lean               -- ParseState + helpers
│   ├── Fuel.lean                -- fuel abstractions, default bound
│   └── Composition.lean         -- parseYaml / parseYamlRaw / compose
│
├── Schema/                      -- Core Schema
│   ├── Schema.lean              -- umbrella, resolution functions (§10.3)
│   ├── Api.lean                 -- user-facing converters
│   ├── Deriving.lean            -- macros/derives
│   ├── FromToYaml.lean
│   └── Struct.lean
│
├── Output/                      -- serialization
│   ├── Emitter.lean             -- canonical emit (was ./Emitter.lean)
│   └── Dump.lean                -- style-aware dump (was ./Dump.lean)
│
├── Config/                      -- runtime configuration
│   ├── Config.lean              -- ParserConfig + presets
│   └── Limits.lean              -- ParserLimits + default bounds
│
├── FFI/                         -- foreign bindings
│   ├── FFI.lean
│   └── (ffi/, python/, rust/ remain at repo root)
│
└── Proofs/                      -- see below
```

## `Proofs/` reorganization — as built

The April-2026 draft layout for `Proofs/` was executed (Phase 4,
clusters 1–10 below) with four deviations; the as-built tree is in
[Current state (2026-07-31)](#current-state-2026-07-31) above.
Deviations from the draft:

- **`Surface/` cluster dropped** — the character-level coupling
  proofs (`SurfaceCoupling.lean`, `ScalarCoupling.lean`,
  `StructureCoupling.lean`) live in `Proofs/Coupling/` alongside
  `CouplingBridge.lean` and `ScannerCoupling.lean`; no separate
  `Proofs/Surface/` folder was created.
- **`Document/` became `Contracts/`** — `BlockScalarContracts.lean`
  and `DocumentContracts.lean` landed in `Proofs/Contracts/`;
  `DumpRoundTrip.lean` went to `Proofs/Output/` with the other
  emitter/dumper proofs.
- **`Foundation/` shrank to 2 files** — `LawfulBEq.lean` and
  `ValueAlgebra.lean` were absorbed into the top-level algebra
  library (Initiative 4 Phase 2) as
  [`L4YAML/Algebra/LawfulBEq.lean`](../L4YAML/Algebra/LawfulBEq.lean)
  and [`L4YAML/Algebra/Value.lean`](../L4YAML/Algebra/Value.lean);
  `CharClass.lean` and `StringProperties.lean` remain.
- **The `ContentEqRefl.lean` move was abandoned** — it stays at
  [`Tests/ContentEqRefl.lean`](../Tests/ContentEqRefl.lean).

Post-April growth not in the draft: `Production/` gained
`IndexedScannerPlainScalarValid.lean`; `Scanner/` and `Parser/`
gained the indexed twins; `Parser/` gained
`FlowParserAcceptance.lean`; `Output/` gained the 2026-07
`EmitterScannability/` split (1,551-line hub + 20 modules) and the
`IndexedEmitterScannability/` cluster (hub + 27 modules). The four
capstone umbrellas (`Composition.lean`, `EndToEndCorrectness.lean`,
`Completeness.lean`, `Soundness.lean`) remain at `Proofs/` root by
design.

## Migration strategy

**Do not do all of this in one commit.** Suggested order (each
phase should leave the build green and the imports valid):

1. **Phase 1 — non-code moves** ✅ **done 2026-04-21** (`ad12e204`).
   Created `Spec/`, `Output/`, `Config/`, `FFI/`, `Token/`, `Parser/`
   folders and moved the 12 top-level files listed above.
   `Scanner.lean` moved to `Scanner/Scanner.lean` as an umbrella (no
   split yet). Import rewrites scripted in
   [`scripts/refactor-phase-1.sh`](../scripts/refactor-phase-1.sh).
   Build green, 429/429.
1b. **Phase 1b — Schema/Surface umbrellas** ✅ **done 2026-04-21**
   (`573fa76e`). `L4YAML/Schema.lean` and `L4YAML/Surface.lean`
   moved into their folders as `Schema/Schema.lean` and
   `Surface/Surface.lean` for symmetry with `Scanner/Scanner.lean`.
   Scripted in
   [`scripts/refactor-phase-1b.sh`](../scripts/refactor-phase-1b.sh).
2. **Phase 2 — Scanner split** ✅ **done 2026-04-21**.  Broke
   `Scanner/Scanner.lean` (~2761 LoC) into seven submodules:
   `State.lean`, `Whitespace.lean`, `Indent.lean`, `Document.lean`,
   `NodeProperties.lean`, `Scalar.lean`, `SimpleKey.lean`, with
   `Scanner.lean` (~560 LoC) as the dispatch umbrella.  The
   blueprint originally listed six submodules; `NodeProperties.lean`
   was added during execution to mirror YAML §6.9 as a named spec
   section, on the rationale that other submodules already align
   with sections (`Whitespace` ≈ §6.1–§6.7, `Document` ≈ §6.8 + §9.1.2,
   `Scalar` ≈ §7.3 + §8.1).  `lake build` 443/443; scanner tests
   32/32, spec examples 132/132, validation tests 84/84.
3. **Phase 3 — Parser split** ✅ **done 2026-04-21**.  Broke
   `Parser/TokenParser.lean` (~1191 LoC) into four files:
   `State.lean` (~285 LoC) holds `ParseState` + accessors +
   `NodeProperties` + `parseNodeProperties` + helpers; `Fuel.lean`
   (~50 LoC) factors out the `initialFuel := 4*N+4` formula;
   `TokenParser.lean` (~535 LoC) keeps the then-14-function (now
   18-function, ~834 LoC) mutual block
   + `StreamState`/`validNextToken` + `parseDirectives` +
   `prepareDocumentState` + `parseDocument` + `parseStream`;
   `Composition.lean` (~205 LoC) becomes the user-facing umbrella
   for `scanAndParse`, `parseYaml{,Raw,Single,SingleRaw}`,
   the comment classifiers, and `parseYamlWithComments`.
   Importers redirected from `L4YAML.Parser.TokenParser` →
   `L4YAML.Parser.Composition` via a one-line sed (49 files); the
   `L4YAML.TokenParser.foo` API surface is preserved via transitive
   imports. `lake build` 443/443; `flowtests`, `explicitkeytests`,
   `rawparsetests`, `dumproundtrip` all green.
4. **Phase 4 — Proofs reorganization** (large, per-folder):
   Move proof files into the subfolders above one cluster at a time.
   Each move is its own PR; build-green gate.
   - **Cluster 1 — Foundation/** ✅ **done 2026-04-21**. Moved
     `CharClass.lean`, `LawfulBEq.lean`, `StringProperties.lean`,
     `ValueAlgebra.lean` into `L4YAML/Proofs/Foundation/`.  Scripted in
     [`scripts/refactor-phase-4-foundation.sh`](../scripts/refactor-phase-4-foundation.sh);
     `lake build` 449/449.
   - **Cluster 2 — Errors/** ✅ **done 2026-04-22**. Moved
     `ErrorProperties.lean`, `EscapeResolution.lean`, `FoldNewlines.lean`
     into `L4YAML/Proofs/Errors/`.  Scripted in
     [`scripts/refactor-phase-4-errors.sh`](../scripts/refactor-phase-4-errors.sh);
     `lake build` 449/449.
   - **Cluster 3 — Schema/** ✅ **done 2026-04-22**. Moved
     `SchemaComposition.lean`, `SchemaDump.lean`, `SchemaResolution.lean`,
     `TagResolution.lean` into `L4YAML/Proofs/Schema/`.  Scripted in
     [`scripts/refactor-phase-4-schema.sh`](../scripts/refactor-phase-4-schema.sh);
     `lake build` 449/449.
   - **Cluster 4 — Contracts/** ✅ **done 2026-04-22**. Moved
     `BlockScalarContracts.lean`, `DocumentContracts.lean` into
     `L4YAML/Proofs/Contracts/`.  Scripted in
     [`scripts/refactor-phase-4-contracts.sh`](../scripts/refactor-phase-4-contracts.sh);
     `lake build` 449/449.
   - **Cluster 5 — Production/** ✅ **done 2026-04-22**. Moved
     `StreamAccum.lean`, `StructureProduction.lean`, `ScalarProduction.lean`,
     `DocumentProduction.lean`, `NodeProduction.lean`, `PreprocessProduction.lean`,
     `ScannerPlainScalarValid.lean` into `L4YAML/Proofs/Production/`.
     Scripted in
     [`scripts/refactor-phase-5-production.sh`](../scripts/refactor-phase-5-production.sh);
     `lake build` 449/449.
   - **Cluster 6 — Scanner/** ✅ **done 2026-04-22**. Moved the
     eighteen scanner-correctness proofs (`ScannerCorrectness.lean`,
     `ScannerProgress.lean`, `ScannerBound.lean`, `ScannerDispatch.lean`,
     `ScannerDocument.lean`, `ScannerSimpleKey.lean`,
     `ScannerLoopInvariant.lean`, `ScannerContracts.lean`,
     `ScannerWhitespace.lean`, `ScannerPlainScalar.lean`,
     `ScannerPlainContent.lean`, `ScannerDoubleQuoted.lean`,
     `ScannerScalar.lean`, `ScannerFlowCollection.lean`,
     `ScannerIndentStack.lean`, `ScannerIndent.lean`,
     `ScannerProofs.lean`, `ScanStrictCoupling.lean`) into
     `L4YAML/Proofs/Scanner/`.  Scripted in
     [`scripts/refactor-phase-6-scanner.sh`](../scripts/refactor-phase-6-scanner.sh);
     `lake build` 449/449.  Note: the roadmap row in
     `Blueprint/README.md` was drafted with 17 files; the detailed
     target layout enumerates 18 (including `ScannerPlainContent.lean`,
     flagged in that same README at the "unlisted" bullet).
   - **Cluster 7 — Output/** ✅ **done 2026-04-22**. Moved
     `EmitterScannability.lean`, `ScannerEmitBridge.lean`, and
     `DumpRoundTrip.lean` into `L4YAML/Proofs/Output/`.  Scripted in
     [`scripts/refactor-phase-7-output.sh`](../scripts/refactor-phase-7-output.sh);
     `lake build` 449/449 (pre-existing `sorry` warnings in
     `EmitterScannability.lean` carried over unchanged).
   - **Cluster 8 — Parser/** ✅ **done 2026-04-22**. Moved the nine
     parser-correctness proofs (`ParserSoundness.lean`,
     `ParserCompleteness.lean`, `ParserCorrectness.lean`,
     `ParserNodeProofs.lean`, `ParserAnchorProofs.lean`,
     `ParserWfaProofs.lean`, `ParserWellBehaved.lean`,
     `ParserGrammable.lean`, `ParserGrammableBase.lean`) into
     `L4YAML/Proofs/Parser/`.  The mutual-recursion cross-imports
     within the cluster were rewritten in-place by the same sed
     pass — no ordering hazard because sed runs after `git mv`.
     Scripted in
     [`scripts/refactor-phase-8-parser.sh`](../scripts/refactor-phase-8-parser.sh);
     `lake build` 449/449 (pre-existing `sorry` warnings in
     `Output/EmitterScannability.lean` carried over unchanged).
   - **Cluster 9 — Coupling/** ✅ **done 2026-04-22**. Moved the five
     scanner↔surface↔grammar coupling proofs (`CouplingBridge.lean`,
     `ScannerCoupling.lean`, `SurfaceCoupling.lean`,
     `StructureCoupling.lean`, `ScalarCoupling.lean`) into
     `L4YAML/Proofs/Coupling/`.  Three internal cross-imports
     (`ScannerCoupling` → `CouplingBridge`, `ScalarCoupling` →
     `ScannerCoupling`, `StructureCoupling` → `ScalarCoupling`)
     rewritten in-place by the same sed pass.  Note: the roadmap row
     in `Blueprint/README.md` was drafted with 6 files; the target
     layout enumerates 5 and that matches the flat layout — the row
     is now ✅ at 5.  Scripted in
     [`scripts/refactor-phase-9-coupling.sh`](../scripts/refactor-phase-9-coupling.sh);
     `lake build` 449/449 (pre-existing `sorry` warnings in
     `Output/EmitterScannability.lean` carried over unchanged).
   - **Cluster 10 — RoundTrip/** ✅ **done 2026-04-22** (closes
     Phase 4).  Moved the four round-trip and comment-channel proofs
     (`RoundTrip.lean`, `RoundTripComposition.lean`,
     `CommentRoundTrip.lean`, `CommentProperties.lean`) into
     `L4YAML/Proofs/RoundTrip/`.  No intra-cluster imports existed
     among the four files (pure renames, 100% similarity).  Scripted
     in
     [`scripts/refactor-phase-10-roundtrip.sh`](../scripts/refactor-phase-10-roundtrip.sh);
     `lake build` 449/449 (pre-existing `sorry` warnings in
     `Output/EmitterScannability.lean` carried over unchanged).
     Initiative 1 Phase 4 complete: only the four capstone umbrellas
     (`Composition.lean`, `EndToEndCorrectness.lean`, `Completeness.lean`,
     `Soundness.lean`) remain at `Proofs/` root — by design.

## Naming conventions

After the refactor, propose enforcing:

- **File name = namespace name = role**. `L4YAML/Scanner/SimpleKey.lean`
  opens namespace `L4YAML.Scanner.SimpleKey`.
- **Umbrella file convention: `Foo/Foo.lean`**. Every folder whose
  top-level content was previously a flat `L4YAML/Foo.lean` now has
  the file at `L4YAML/Foo/Foo.lean`, opening namespace `L4YAML.Foo`
  (not `L4YAML.Foo.Foo`). This is the one accepted
  file-name ≠ namespace exception: the umbrella collects content
  that spans the whole cluster and belongs in the cluster's
  top-level namespace. `L4YAML/Scanner/Scanner.lean`,
  `L4YAML/Parser/TokenParser.lean`, `L4YAML/Schema/Schema.lean`,
  `L4YAML/Surface/Surface.lean` are the live examples. Rejected
  alternatives:
    - `Foo/default.lean` — Lean 4 has no blessed default-module
      convention, and the filename carries no role information.
    - Keep `Foo.lean` at the top level as sibling of `Foo/` — legal
      but produces asymmetric navigation and obscures that `Foo.lean`
      belongs to the cluster.
- **No shadow names across folders**. Phase 1 resolved the previous
  `Dump.lean` / `Schema/Dump.lean` collision (→ `Output/Dump.lean` /
  `Schema/Dump.lean`).
- **Proof file names mirror their subject**. `Proofs/Scanner/X.lean`
  proves properties of `L4YAML/Scanner/X.lean`. Where a proof file
  covers multiple subjects (e.g., `StructureCoupling.lean` covers
  flow/block/document structure), keep it in the dominant cluster.
