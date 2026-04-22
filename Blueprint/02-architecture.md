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
Input ─▶│ Source   │ ─────────▶│ Tokens                       │
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

1. **Lean kernel** — smallest, most trusted. Includes `propext`,
   `Quot.sound`, `Classical.choice` (used in `noncomputable def`
   witnesses in `ParserSoundness.lean`). Nothing else.
2. **L4YAML spec layer** — definitions in `Spec/Grammar.lean`,
   `Spec/YamlSpec.lean`, `Spec/Types.lean`, `Token/Token.lean`, and
   `Surface/*`. These encode the YAML 1.2.2 specification as Lean
   inductives and predicates. **They must be read and believed**: a
   bug here is a bug in the reference against which the
   implementation is verified.
3. **L4YAML implementation** — `Scanner/Scanner.lean`,
   `Parser/TokenParser.lean`, `Schema/Schema.lean`,
   `Output/Emitter.lean`, `Output/Dump.lean`, `Config/Config.lean`,
   `Config/Limits.lean`. Under verification against the layer above.

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

The 14 mutually recursive parser functions:

- `parseNode`
- `parseFlowSequence`, `parseFlowSequenceLoop`
- `parseFlowMapping`, `parseFlowMappingLoop`
- `parseBlockSequence`, `parseBlockSequenceLoop`
- `parseBlockMapping`, `parseBlockMappingLoop`
- `parseImplicitBlockSequence`, `parseImplicitBlockSequenceLoop`
- `parseSinglePairMapping`
- `parseNodeProperties`, `parseNodeContent`

All live in one `mutual ... end` block in `TokenParser.lean`.
Properties that must be proved by simultaneous induction (e.g.
`AnchorsGrow`, `AllAliasesResolve`, `WellFormedAnchors`,
`parser_fuel_mono_succ` if retained) follow the same mutual
structure. See `ParserNodeProofs.lean`, `ParserAnchorProofs.lean`,
`ParserWfaProofs.lean`, `ParserWellBehaved.lean`.

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
form a DAG with `parse_sound` / `parse_complete` at the top:

```
                  parse_sound / parse_complete / parse_produces_valid_yaml
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
                                  (mutual induction over 14 parsers)
```

Parallel DAGs exist for scanner correctness and round-trip
properties; see [`04-capstones.md`](04-capstones.md).
