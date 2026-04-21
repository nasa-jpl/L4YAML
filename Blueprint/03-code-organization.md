# Code organization

A proposed **folder-based** refactor of the L4YAML code (not the
proofs — that's a separate follow-up). Guiding principle: *a
newcomer should be able to find the implementation of any
terminology entry in ≤ 2 clicks from the top of `L4YAML/`*.

## Current state

```
L4YAML/
├── CharPredicates.lean
├── Config.lean
├── Dump.lean
├── Emitter.lean
├── FFI.lean
├── Grammar.lean
├── Limits.lean
├── Scanner.lean                 (~920 LoC — flat file)
├── Schema.lean
├── Schema/
│   ├── Api.lean
│   ├── Deriving.lean
│   ├── Dump.lean                (! shadows top-level Dump.lean?)
│   ├── FromToYaml.lean
│   └── Struct.lean
├── Surface.lean
├── Surface/
│   ├── Basic.lean
│   ├── Combinators.lean
│   ├── Document.lean
│   ├── Node.lean
│   └── Scalars.lean
├── Token.lean
├── TokenParser.lean             (~800 LoC — flat file)
├── Types.lean
├── YAML_PRODUCTIONS.md
├── YamlSpec.lean
└── Proofs/                      (61 files — flat, ~47,000 LoC)
```

Observations:

- **14 top-level files mixed with 3 subdirectories** (`Proofs/`,
  `Schema/`, `Surface/`) — no discoverable grouping.
- Scanner and TokenParser are monolithic — the Scanner
  implementation subdirectory mentioned in
  [`doc/Doc/L4YAML/Architecture.lean:140`](../doc/Doc/L4YAML/Architecture.lean#L140)
  (`Scanner/Whitespace.lean`, `Scanner/Scalar.lean`, …) **does not
  exist** in the repo. The Verso manual is ahead of the code.
- `Schema/Dump.lean` and top-level `Dump.lean` coexist without a
  clear naming convention distinguishing them.
- `Proofs/` is a flat directory of 61 files — navigation hard; no
  visible grouping by capstone cluster.
- `Limits.lean` and `Config.lean` are siblings of top-level
  parser files — unclear which depends on which.

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
├── Surface/                     -- character-level syntax (unchanged)
│   ├── Basic.lean
│   ├── Combinators.lean
│   ├── Document.lean
│   ├── Node.lean
│   ├── Scalars.lean
│   └── (Surface.lean becomes Surface/default.lean or is deleted)
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
│   ├── Schema.lean              -- resolution functions (§10.3)
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

1. **Phase 1 — non-code moves** (cheap, low risk): Create the
   `Spec/`, `Output/`, `Config/`, `FFI/`, `Token/`, `Parser/`
   folders and move the files listed above. Update `import`
   statements with a scripted rename. Keep `Scanner.lean` monolithic
   for now. Single PR; build-green check.
2. **Phase 2 — Scanner split** (medium): Break `Scanner.lean` into
   the submodules referenced by
   [`Architecture.lean:140`](../doc/Doc/L4YAML/Architecture.lean#L140).
   This lines up the code with the published documentation.
3. **Phase 3 — Parser split** (medium): Extract `Parser/State.lean`,
   `Parser/Fuel.lean`, `Parser/Composition.lean` from
   `TokenParser.lean`. The mutually-recursive block stays together
   in `TokenParser.lean`.
4. **Phase 4 — Proofs reorganization** (large, per-folder):
   Move proof files into the subfolders above one cluster at a time.
   Each move is its own PR; build-green gate.

## Naming conventions

After the refactor, propose enforcing:

- **File name = namespace name = role**. `L4YAML/Scanner/SimpleKey.lean`
  opens namespace `L4YAML.Scanner.SimpleKey`.
- **No shadow names across folders**. The current
  `Dump.lean` / `Schema/Dump.lean` collision should resolve after
  Phase 1 (→ `Output/Dump.lean` / `Schema/Dump.lean` — now clearly
  distinguishable).
- **Proof file names mirror their subject**. `Proofs/Scanner/X.lean`
  proves properties of `L4YAML/Scanner/X.lean`. Where a proof file
  covers multiple subjects (e.g., `StructureCoupling.lean` covers
  flow/block/document structure), keep it in the dominant cluster.
