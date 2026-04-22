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
│   └── Scanner.lean             (~920 LoC — still monolithic, Phase 2 splits)
├── Parser/
│   └── TokenParser.lean         (~800 LoC — Phase 3 splits)
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
└── Proofs/                      (61 files — flat, ~47,000 LoC; Phase 4 clusters)
```

Phase 1 (`ad12e204`) + Phase 1b (`573fa76e`) landed on 2026-04-21.
What's done, what remains:

- **Done**: 14 top-level files collapsed into 9 role-named folders.
  Every top-level file sits inside its matching folder; no more
  orphan siblings.
- **Done**: `Schema/Dump.lean` vs. top-level `Dump.lean` shadow
  resolved — now `Output/Dump.lean` vs. `Schema/Dump.lean`.
- **Pending (Phase 2)**: `Scanner/Scanner.lean` is still monolithic.
  The submodules referenced by
  [`doc/Doc/L4YAML/Architecture.lean:140`](../doc/Doc/L4YAML/Architecture.lean#L140)
  (`Scanner/Whitespace.lean`, `Scanner/Scalar.lean`, …) still
  **do not exist**. The Verso manual remains ahead of the code.
- **Pending (Phase 3)**: `Parser/TokenParser.lean` is still monolithic.
- **Pending (Phase 4)**: `Proofs/` is a flat directory of 61 files.

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
│   ├── Scanner.lean             -- top-level scanNextToken dispatch
│   ├── State.lean               -- ScannerState + WellFormed
│   ├── Whitespace.lean          -- (future: extracted from Scanner.lean)
│   ├── Scalar.lean              -- (future: extracted)
│   ├── Indent.lean              -- (future: extracted)
│   ├── SimpleKey.lean           -- (future: extracted)
│   └── Document.lean            -- (future: extracted)
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
2. **Phase 2 — Scanner split** (medium): Break
   `Scanner/Scanner.lean` into the submodules referenced by
   [`Architecture.lean:140`](../doc/Doc/L4YAML/Architecture.lean#L140).
   This lines up the code with the published documentation.
3. **Phase 3 — Parser split** (medium): Extract `Parser/State.lean`,
   `Parser/Fuel.lean`, `Parser/Composition.lean` from
   `Parser/TokenParser.lean`. The mutually-recursive block stays
   together in `TokenParser.lean`.
4. **Phase 4 — Proofs reorganization** (large, per-folder):
   Move proof files into the subfolders above one cluster at a time.
   Each move is its own PR; build-green gate.

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
