# Code organization

A proposed **folder-based** refactor of the L4YAML code (not the
proofs — that's a separate follow-up). Guiding principle: *a
newcomer should be able to find the implementation of any
terminology entry in ≤ 2 clicks from the top of `L4YAML/`*.

## Current state (post-Phase-1b, 2026-04-21)

```
L4YAML/
├── Spec/
│   ├── CharPredicates.lean
│   ├── Grammar.lean
│   ├── Types.lean
│   └── YamlSpec.lean
├── Token/
│   └── Token.lean
├── Scanner/
│   ├── Scanner.lean             -- umbrella, dispatch + main loop
│   ├── State.lean               -- ScannerState + accessors
│   ├── Whitespace.lean          -- s-white/s-space, s-l-comments
│   ├── Indent.lean              -- virtual BLOCK-* generation
│   ├── Document.lean            -- ---/... markers + %YAML/%TAG directives
│   ├── NodeProperties.lean      -- anchors, aliases, tags (§6.9)
│   ├── Scalar.lean              -- escapes + quoted/plain/block scalars
│   └── SimpleKey.lean           -- simple-key resolution + scanBlockEntry/Key/Value
├── Parser/
│   ├── TokenParser.lean         -- mutual block + parseStream/parseDocument
│   ├── State.lean               -- ParseState + accessors + NodeProperties + helpers
│   ├── Fuel.lean                -- initialFuel := 4*N+4
│   └── Composition.lean         -- umbrella: parseYaml*, scanAndParse, comment classification
├── Output/
│   ├── Dump.lean
│   └── Emitter.lean
├── Schema/
│   ├── Api.lean
│   ├── Deriving.lean
│   ├── Dump.lean
│   ├── FromToYaml.lean
│   ├── Schema.lean              -- umbrella, shared namespace `L4YAML.Schema`
│   └── Struct.lean
├── Surface/
│   ├── Basic.lean
│   ├── Combinators.lean
│   ├── Document.lean
│   ├── Node.lean
│   ├── Scalars.lean
│   └── Surface.lean             -- umbrella, shared namespace `L4YAML.Surface`
├── Config/
│   ├── Config.lean
│   └── Limits.lean
├── FFI/
│   └── FFI.lean
├── YAML_PRODUCTIONS.md
└── Proofs/                      (2 flat + Foundation/ + Errors/ + Schema/ + Contracts/ + Production/ + Scanner/ + Output/ + Parser/ + Coupling/ + RoundTrip/ clusters; Phase 4 complete)
```

Phase 1 (`ad12e204`) + Phase 1b (`573fa76e`) landed on 2026-04-21.
What's done, what remains:

- **Done**: 14 top-level files collapsed into 9 role-named folders.
  Every top-level file sits inside its matching folder; no more
  orphan siblings.
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
  `Fuel.lean` (`initialFuel := 4*N+4`), `TokenParser.lean` (the 14
  mutually-recursive functions + `parseStream`/`parseDocument`), and
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

## Proposed target layout

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
│   ├── TokenParser.lean         -- the 14 mutually-recursive functions
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

## Proposed `Proofs/` reorganization (follow-up)

Not part of this refactor pass, but listed here so the direction is
clear:

```
L4YAML/Proofs/
├── Foundation/                  -- utilities used everywhere
│   ├── CharClass.lean
│   ├── LawfulBEq.lean
│   ├── StringProperties.lean
│   └── ValueAlgebra.lean
│
├── Surface/                     -- character-level coupling
│   ├── SurfaceCoupling.lean
│   ├── ScalarCoupling.lean
│   └── StructureCoupling.lean
│
├── Scanner/                     -- lexer correctness
│   ├── ScannerCorrectness.lean
│   ├── ScannerProgress.lean
│   ├── ScannerBound.lean
│   ├── ScannerDispatch.lean
│   ├── ScannerDocument.lean
│   ├── ScannerSimpleKey.lean
│   ├── ScannerLoopInvariant.lean
│   ├── ScannerContracts.lean
│   ├── Scanner{Whitespace,PlainScalar,DoubleQuoted,Scalar,FlowCollection,IndentStack,Indent}.lean
│   ├── ScannerProofs.lean
│   └── ScanStrictCoupling.lean
│
├── Parser/                      -- parser correctness
│   ├── ParserSoundness.lean
│   ├── ParserCompleteness.lean
│   ├── ParserCorrectness.lean
│   ├── ParserNodeProofs.lean
│   ├── ParserAnchorProofs.lean
│   ├── ParserWfaProofs.lean
│   ├── ParserWellBehaved.lean   (after de-cruft — see 05-current-state.md)
│   ├── ParserGrammable.lean
│   └── ParserGrammableBase.lean
│
├── Production/                  -- grammar-derivation composition
│   ├── StreamAccum.lean
│   ├── StructureProduction.lean
│   ├── ScalarProduction.lean
│   ├── DocumentProduction.lean
│   ├── NodeProduction.lean
│   ├── PreprocessProduction.lean
│   └── ScannerPlainScalarValid.lean
│
├── Schema/                      -- schema resolution
│   ├── SchemaResolution.lean
│   ├── SchemaComposition.lean
│   ├── SchemaDump.lean
│   └── TagResolution.lean
│
├── Output/                      -- emitter/dumper correctness
│   ├── EmitterScannability.lean
│   ├── ScannerEmitBridge.lean
│   └── DumpRoundTrip.lean
│
├── RoundTrip/                   -- content equivalence cycle
│   ├── ContentEqRefl.lean       (currently ContentEqRefl.lean is in Tests/)
│   ├── RoundTrip.lean
│   ├── RoundTripComposition.lean
│   └── CommentRoundTrip.lean
│
├── Coupling/                    -- scan ↔ surface ↔ grammar
│   ├── CouplingBridge.lean
│   ├── ScannerCoupling.lean
│   ├── SurfaceCoupling.lean
│   ├── StructureCoupling.lean
│   └── ScalarCoupling.lean
│
├── Errors/
│   ├── ErrorProperties.lean
│   ├── EscapeResolution.lean
│   └── FoldNewlines.lean
│
├── Document/
│   ├── BlockScalarContracts.lean
│   ├── DocumentContracts.lean
│   └── DumpRoundTrip.lean
│
├── Composition.lean             -- top-level pipeline
├── EndToEndCorrectness.lean     -- capstones
├── Completeness.lean            -- capstones
└── Soundness.lean               -- capstones
```

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
   `TokenParser.lean` (~535 LoC) keeps the 14-function mutual block
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
