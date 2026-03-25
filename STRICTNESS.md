# STRICTNESS.md — Formalizing YAML 1.2.2 Surface Syntax

## TL;DR

This document describes the **acceptance strictness** formalization for v0.4.0:
encoding the YAML 1.2.2 surface syntax (productions [1]–[211]) as Lean 4
parameterized inductive predicates over positioned character streams, and the
target theorem `parse_strict : parseYaml s = .ok docs → InYamlLanguage s`.

**Status**: Surface syntax grammar formalized in 6 modules (~1,100 lines),
18 mutual inductives for the node/collection layer. Build: 385 jobs.
Tests: 869 passed / 0 failed / 151 skipped (no regressions).
Target theorems stated with `sorry`; coupling proofs under construction.

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
| `Surface.lean` | ~120 | — | `InYamlLanguage`, `parse_strict`, `scan_strict` (sorry) |

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
theorem parse_strict (input : String) (docs : Array YamlDocument)
    (h : parseYaml input = .ok docs) : InYamlLanguage input

theorem scan_strict (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    ∃ s', SLYamlStream ⟨input.toList, 0⟩ s'
```

**Proof strategy** (bottom-up coupling):
1. Scanner coupling: each scanner function, when successful, advances
   through input matching the surface syntax productions it implements
2. Token parser coupling: token sequence consumption corresponds to
   node-level productions
3. Document composition: full pipeline produces `SLYamlStream`

## What Remains

- [ ] Coupling theorems for scanner functions → basic productions
- [ ] Coupling theorems for token parser → node productions
- [ ] Proof of `scan_strict` (scanner → surface syntax)
- [ ] Proof of `parse_strict` (full pipeline)
- [ ] Verify production coverage against YAML 1.2.2 spec numbering

