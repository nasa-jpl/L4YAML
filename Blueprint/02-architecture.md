# Architecture

> This document is the **canonical** architectural description and
> should be kept in sync with
> [`doc/Doc/L4YAML/Architecture.lean`](../doc/Doc/L4YAML/Architecture.lean)
> (which renders the published Verso manual). When they disagree, this
> document is authoritative for the blueprint; update the Verso copy
> to match.

## Data-flow pipeline

```
          String                 Array (Positioned YamlToken)
        ┌──────────┐    scan    ┌──────────────────────────────┐
Input ─▶│ Source   │ ──────────▶│ Tokens                       │
        └──────────┘            └──────────────────────────────┘
                                           │
                                           │ parseStream
                                           ▼
                                ┌──────────────────────────────┐
                                │ Array YamlDocument           │
                                │   (raw — scalars as strings) │
                                └──────────────────────────────┘
                                           │
                                           │ compose (schema resolution)
                                           ▼
                                ┌──────────────────────────────┐
                                │ Array YamlDocument           │
                                │   (resolved — typed scalars) │
                                └──────────────────────────────┘
                                           │
   ┌────────── emit ◀──────────────────────┘ (round-trip)
   ▼
 String (canonical)
```

The end-to-end function is

```
parseYaml : String → Except ScanError (Array YamlDocument)
parseYaml = compose ∘ parseStream ∘ scanFiltered
```

with the intermediate `parseYamlRaw = parseStream ∘ scanFiltered`
skipping schema resolution.

The reverse direction uses the **Emitter** (`emit`) or the **Dumper**
(`dump`); see [`01-terminology.md`](01-terminology.md) for the
distinction.

## Trust boundaries

L4YAML's verification story has three concentric trust boundaries:

1. **Lean kernel** — smallest, most trusted. The capstones carry a
   **two-tier axiom profile**, machine-pinned by
   `#assert_capstone_axioms` in
   [`L4YAML/Capstones.lean`](../L4YAML/Capstones.lean): 18 are
   **pure** — `propext`, `Quot.sound`, `Classical.choice` only (the
   latter used in `noncomputable def` witnesses in
   `ParserSoundness.lean`) — and 7 are **native** — additionally
   `Lean.ofReduceBool`/`Lean.ofReduceNat`/`Lean.trustCompiler`,
   backing `native_decide` reflected-decide leaves, which extends
   trust to the compiler for those capstones. Nothing else: any
   `sorryAx` or project-declared axiom fails the build.
2. **L4YAML spec layer** — definitions in `Spec/Grammar.lean`,
   `Spec/YamlSpec.lean`, `Spec/Types.lean`, `Token/Token.lean`, and
   `Surface/*`. These encode the YAML 1.2.2 specification as Lean
   inductives and predicates. **They must be read and believed**: a
   bug here is a bug in the reference against which the
   implementation is verified.
3. **L4YAML implementation** — `Scanner/Scanner.lean`,
   `Parser/TokenParser.lean`, `Schema/Schema.lean`,
   `Output/Emitter.lean`, `Output/Dump.lean`, `Config/Config.lean`,
   `Config/Limits.lean`; plus the indexed twins (`Indexed/*`,
   `Scanner/Indexed*`, `Parser/*Ix.lean`,
   `Parser/IndexedComposition.lean`) and the auxiliary emitters
   `Output/Events.lean` / `Output/Json.lean`. Under verification
   against the layer above.

Capstone theorems (see [`04-capstones.md`](04-capstones.md)) bridge
layers 2 and 3.

## Two-pass architecture

The scanner and parser are **separate passes**. This separation:

- **Mirrors the spec**: YAML 1.2.2 itself is layered (lexical
  productions §10.1-§10.2, syntactic productions §6-§9).
- **Enables independent verification**: scanner correctness (every
  emitted token is well-formed, positions monotone, stream
  bracketed) is proved without any parser reasoning.
- **Localizes termination**: scanner terminates by offset progress
  (`advance_offset_lt`); parser terminates by fuel (decreases in
  recursive calls). Proofs don't entangle.

## Append-only token stream

A design choice critical to the scanner's verifiability: **tokens
are appended, never inserted**. When the scanner encounters a
potential *simple key* (a plain scalar that might become a
mapping-entry key), it:

1. Pushes two **placeholder** tokens into the stream (reserving
   positions for future `key` and `blockMappingStart` indicators).
2. Records their indices.
3. On confirmation (a `:` at the correct column), **overwrites**
   the placeholders in place via `setIfInBounds`.
4. On non-confirmation, the placeholders remain and are **filtered
   out** before the stream is returned by `scanFiltered`.

This avoids `Array.insertAt`, which would shift indices and
invalidate previously-recorded positions — a property essential to
the monotonic-progress proof. See `ScannerProgress.lean`,
`ScannerSimpleKey.lean`.

## Mutual recursion in the parser

The 18 mutually recursive parser functions:

- `parseNode`, `parseNodeContent`
- `parseFlowSequence`, `parseFlowSequenceLoop`
- `parseFlowMapping`, `parseFlowMappingLoop`,
  `parseFlowMappingValue`, `parseExplicitKey`
- `parseBlockSequence`, `parseBlockSequenceLoop`
- `parseBlockMapping`, `parseBlockMappingLoop`,
  `parseBlockMappingEntryValue`, `handleBlockMappingKeyEntry`,
  `handleBlockMappingValueEntry`
- `parseImplicitBlockSequence`, `parseImplicitBlockSequenceLoop`
- `parseSinglePairMapping`

All live in one `mutual ... end` block in `TokenParser.lean`.
(`parseNodeProperties` is a plain `def` in `Parser/State.lean`, not
part of the mutual block.) Properties that must be proved by
simultaneous induction (e.g. `AnchorsGrow`, `AllAliasesResolve`,
`WellFormedAnchors`) follow the same mutual structure. See
`ParserNodeProofs.lean`, `ParserAnchorProofs.lean`,
`ParserWfaProofs.lean`, `ParserWellBehaved.lean`.

## Indexed twin pipeline, Algebra, and auxiliary outputs

Three later additions sit beside the classic pipeline (wired into
the library build on 2026-07-31; history in
[`08-initiative-4-intrinsic-foundations.md`](08-initiative-4-intrinsic-foundations.md)):

- **Indexed (intrinsic) twin pipeline** — a position-indexed
  re-implementation whose types carry the input string as an index:
  `Indexed/` (`CharStream`, `Range`, `RepGraph`, `TokenStream`) →
  `Scanner/IndexedScanner.lean` → `Parser/TokenParserIx.lean`
  (`parseStreamIx`) → `Parser/IndexedComposition.lean`
  (`parseYamlSingleIx`), with `Scanner/IndexedPresenter.lean`
  rendering token streams back to text. Its correctness proofs are
  the `Indexed*` twins under `Proofs/Scanner/` and `Proofs/Parser/`
  (capstoned: `IndexedCompleteness.lean`), plus
  `Proofs/Output/IndexedEmitterScannability/`.
- **`Algebra/`** — a 13-module cross-cutting law library
  (equivalence, idempotence, `LawfulBEq` instances,
  fuel/indent/position/token-stream algebra) consumed by both
  pipelines' proofs; factored out *before* the proofs that need it
  (Initiative 4's "algebra before threading").
- **`Output/Events.lean` and `Output/Json.lean`** — event-stream and
  JSON emitters used by the cross-processor test-matrix comparison.
  Auxiliary outputs outside the verified round-trip chain (together
  with `Config/Limits.lean` they contain the library's only
  `partial def`s).

## Module dependency sketch

```
                         ┌─────────────────┐
                         │ FFI             │  (C/Python/Rust bindings)
                         └────────┬────────┘
                                  │
                         ┌────────▼────────┐
                         │ Config          │  (limits, presets)
                         └────────┬────────┘
                                  │
                         ┌────────▼────────┐
                         │ Dump            │  (style-aware serializer)
                         └────────┬────────┘
                                  │
                         ┌────────▼────────┐
                         │ Emitter         │  (canonical serializer)
                         └────────┬────────┘
                                  │
                         ┌────────▼────────┐
                         │ Schema          │  (Core Schema resolution)
                         └────────┬────────┘
                                  │
                         ┌────────▼────────┐
                         │ TokenParser     │  (recursive descent)
                         └────────┬────────┘
                                  │
                         ┌────────▼────────┐
                         │ Scanner         │  (char → token)
                         └────────┬────────┘
                                  │
                         ┌────────▼────────┐
                         │ Token           │  (YamlToken inductive)
                         └────────┬────────┘
                                  │
                         ┌────────▼────────┐
                         │ CharPredicates  │
                         │ YamlSpec        │  (spec-side predicates)
                         │ Grammar         │  (spec-side inductives)
                         │ Types           │  (YamlValue, YamlDocument)
                         │ Surface         │  (char-level syntax)
                         └─────────────────┘
```

`lake exe graph` produces the authoritative graph.

## Proof dependency sketch (capstones)

The capstone theorems (detailed in [`04-capstones.md`](04-capstones.md))
form a DAG with `parse_sound_deep` / `parse_complete` at the top
(`parse_sound_shallow` sits alongside as the propBridge variant
covering only the top-level implication; `parse_sound_deep` is the
fibration canary that cites the pipeline lemmas directly):

```
                  parse_sound_deep / parse_complete / parse_produces_valid_yaml
                                    │
                   ┌────────────────┼────────────────┐
                   ▼                ▼                ▼
       parseYaml_pipeline    parseStream_sound    parseYaml_ok_iff
                   │                │
                   │        ┌───────┴───┐
                   ▼        ▼           ▼
       parseStream_output_grammable   parseStream_output_anchors_wellformed
                   │                    │
                   ▼                    ▼
       yamlValue_has_witness    parseNode_anchors_grow / _aliases_resolve'
                                        │
                                        ▼
                                  (mutual induction over the 18 mutual parsers)
```

Parallel DAGs exist for scanner correctness and round-trip
properties; see [`04-capstones.md`](04-capstones.md).
