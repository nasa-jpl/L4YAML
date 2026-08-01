# STRICTNESS.md — Formalizing YAML 1.2.2 Surface Syntax

## TL;DR

This document describes the **acceptance strictness** formalization for v0.4.0:
encoding the YAML 1.2.2 surface syntax (productions [1]–[211]) as Lean 4
parameterized inductive predicates over positioned character streams, and the
target theorem `parse_strict : parseYaml s = .ok docs → InYamlLanguage s`.

**Status (2026-07-31)**: **Complete.** Surface syntax grammar formalized in 6
modules, 18 mutual inductives for the node/collection layer. The target
theorems `parse_strict` and `scan_strict` are **proven** (v0.4.6) as thin
wrappers in `L4YAML/Surface/Surface.lean` over the `@[capstone]` theorems
`parse_strict_proof` / `scan_strict_proof` in
`L4YAML/Proofs/Production/DocumentProduction.lean` — see
Blueprint/04-capstones.md, Group 7 (the proof-status SSOT). The build/test
counts originally quoted here (391 jobs; 869 passed / 0 failed / 151 skipped;
"~50 coupling theorems in 3 modules") were a v0.4.0 snapshot.

## Architecture

### Position Model

```lean
structure SurfPos where
  chars : List Char   -- remaining input
  col   : Nat         -- current column (0-based)
```

Each production is a relation `SurfPos → SurfPos → Prop` matching a prefix
of the input and advancing the position. Column resets to 0 on line breaks,
increments by 1 per consumed character. This models YAML's column-sensitive
indentation without carrying full (line, col) — column suffices since
productions only look at column alignment, not line numbers.

### Module Structure

| Module | Lines | Productions | Description |
|--------|-------|-------------|-------------|
| `Surface/Combinators.lean` | ~85 | — | `SurfPos`, `GChar`, `GLit`, `GSeq`, `GAlt`, `GStar`, `GPlus`, `GOpt`, `GEps`, `GNot` |
| `Surface/Basic.lean` | ~260 | [24]–[101] | Line breaks, whitespace, indentation, comments, separation, directives, node properties |
| `Surface/Scalars.lean` | ~300 | [104]–[175] | Double-quoted, single-quoted, plain scalars, alias nodes, block scalars |
| `Surface/Node.lean` | ~370 | [134]–[199] | 18 mutual inductives: flow/block collections + node dispatchers |
| `Surface/Document.lean` | ~140 | [200]–[211] | Document markers, document types, stream composition |
| `Surface.lean` | ~120 | — | `InYamlLanguage`, `parse_strict`, `scan_strict` |

### Mutual Inductive Design

Lean 4's kernel forbids nested inductives whose parameters contain local
variables from the same mutual block. This prevents using generic combinators
(`GAlt`, `GOpt`, `GStar`) to wrap mutually-defined types.

**Solution**: All combinator patterns wrapping mutual types are inlined as
explicit constructors. Non-mutual combinator usage is preserved.

Example — `GAlt (SBlockNode n .blockOut) (GSeq SENode SSLComments)` becomes:
```lean
| implicitKeyNode  : ... → SBlockNode n .blockOut s₂ s' → SBlockMapEntry n s s'
| implicitKeyEmpty : ... → SSLComments s₂ s'            → SBlockMapEntry n s s'
```

The 18 mutual inductives in `Node.lean`:
- `SBlockNode`, `SBlockIndented`, `SBlockSeqEntries`, `SBlockMapEntry`,
  `SBlockMapEntries`, `SCompactSeq`, `SCompactSeqTail`, `SCompactMap`,
  `SCompactMapTail`, `SImplicitKey`
- `SFlowNode`, `SFlowContent`, `SFlowSequence`, `SFlowSeqEntries`,
  `SFlowSeqEntry`, `SFlowMapping`, `SFlowMapEntries`, `SFlowMapEntry`

## Gap Analysis: Output Predicates ≠ Input Predicates

Grammar.lean's `ValidNode` captures output structure — "this parse tree
is a valid YAML value" — but NOT input acceptance — "this character
sequence conforms to the YAML syntax."

Concrete examples of the gap:
- `ValidNode.blockSeq 2 items` says the output is a 2-element block
  sequence, but NOT that the input has `-` at the correct column
  followed by correctly-indented content
- `ValidTokenStream` says tokens are ordered and stream-bounded, but
  NOT that inter-token whitespace/comments follow the grammar

The surface syntax predicates close this gap by specifying character-level
acceptance for every YAML production.

## Target Theorems

```lean
lemma parse_strict (input : String) (docs : Array YamlDocument)
    (h : parseYaml input = .ok docs) : InYamlLanguage input

lemma scan_strict (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) : InYamlLanguage input
```

Both are proven (see Status above); the `scan_strict` conclusion was later
strengthened from the originally planned `∃ s', SLYamlStream ⟨input.toList, 0⟩ s'`
to full `InYamlLanguage input`.

**Proof strategy** (bottom-up coupling):
1. Scanner coupling: each scanner function, when successful, advances
   through input matching the surface syntax productions it implements
2. Token parser coupling: token sequence consumption corresponds to
   node-level productions
3. Document composition: full pipeline produces `SLYamlStream`

## What Remains (resolved)

All items are complete as of v0.4.6 — see Blueprint/04-capstones.md, Group 7.
Where the work landed:

- Coupling theorems for the remaining scanner functions:
  `L4YAML/Proofs/Coupling/` (see table below).
- Grammar-production layer (scanner/parser → productions):
  `L4YAML/Proofs/Production/` — `NodeProduction.lean`,
  `StructureProduction.lean`, `PreprocessProduction.lean`,
  `ScalarProduction.lean`, with `StreamAccum.lean` composing the full
  `SLYamlStream` derivation.
- Proofs of `scan_strict` and `parse_strict`: `scan_strict_proof` /
  `parse_strict_proof` (`@[capstone]`) in
  `L4YAML/Proofs/Production/DocumentProduction.lean`.
- Production coverage against the YAML 1.2.2 spec numbering:
  machine-checked via `@[yaml_spec]` annotations, indexed in
  `Tests/ProductionCoverage.lean`.

The only open successor item is grammar completeness — the `parse_iff_grammar`
converse (Group 7.7; see VERSION-0.4.8.md).

## Coupling Proof Modules

The coupling modules now live under `L4YAML/Proofs/Coupling/` (post-reorg
paths; the theorem counts below are the v0.4.0 snapshot — the modules have
since grown, and two more were added):

| Module | Theorems | Sorry | Description |
|--------|----------|-------|-------------|
| `Proofs/Coupling/SurfaceCoupling.lean` | 20+ | 0 | Pure SurfPos-level properties: SIndent, SBBreak, SSWhite, GSeq, GStar, GOpt, comments, empty node |
| `Proofs/Coupling/CouplingBridge.lean` | 15+ | 0 | Scanner↔SurfPos bridge: `CharsFromOffset` inductive, `ScannerSurfCorr` struct, peek/eof/advance correspondence, production coupling, composition helpers |
| `Proofs/Coupling/ScannerCoupling.lean` | 8 | 0 | Scanner loop coupling: `skipSpacesLoop_corr` (induction on fuel → SIndent), `skipSpaces_corr` (top-level wrapper), `consumeNewline_{lf,crlf,cr}_corr` (line breaks → SBBreak), helper lemmas for peek/fuel budget |
| `Proofs/Coupling/ScalarCoupling.lean` | — | 0 | (added later) Scalar collection coupling: scanner scalar-scanning loops → surface syntax scalar productions |
| `Proofs/Coupling/StructureCoupling.lean` | — | 0 | (added later) Structure, document & directive coupling: flow/block indicators, node properties (anchors + tags), indentation management |

