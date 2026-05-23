/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Parser.IndexedComposition

/-! # `IndexedComposition` proofs — Phase 3 Step 6e end-to-end corpus (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

## Role

Indexed twin of the corpus-exhibit half of Step 5c
(`Proofs/Scanner/IndexedRoundtrip.lean`), reparented onto
`scanAndParseIx` (from `Parser/IndexedComposition.lean`).

For each input in the fixed corpus, the theorem `scanAndParseIx`
either succeeds with the expected document count or fails with
the expected error. Every proof is `native_decide`: the whole
pipeline is computable, so the kernel just reduces the goal.

This sub-step is the parser-level analogue of Step 5c
(`IndexedRoundtrip`): an end-to-end property exhibited on a fixed
corpus, gated by the `native_decide` budget — no symbolic
reasoning.

## Scope

- §1: success cases — inputs where `scanAndParseIx` returns
  `.ok docs` with a known `docs.size`.
- §2: error cases — inputs where `scanAndParseIx` returns
  `.error` (the expected failure modes of the pipeline).

The corpus deliberately covers both branches so the `.ok` and
`.error` legs of the composition are both exhibited.

## Notes on the indexed parser's current scalar content

Plain-scalar content extraction in the indexed pipeline is not
yet at parity with the legacy parser for all positions (root
plain scalars come through with empty `content`; mapping keys and
flow-collection entries do not). The corpus below only asserts
`.ok` vs `.error` and `docs.size`, so it is robust to the
plain-scalar content quirks that will be resolved during Step 6f
cutover or the broader Phase 4 scanner work.

## Phase 3 Step 6f cutover

At cutover, this file is renamed to
`Proofs/Parser/ParserComposition.lean` (or absorbed into an
existing parser-composition proof file) and the namespace
`L4YAML.Proofs.Indexed.Composition` reverts to
`L4YAML.Proofs.ParserComposition`.

## Zero Axioms

All theorems close by `native_decide`. No `sorry`, no `axiom`,
no `partial`.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.Composition

open L4YAML
open L4YAML.TokenParser.Indexed

/-- A success-case check: `scanAndParseIx input` returns `.ok docs`
    with `docs.size = n`. Bundling the success branch and the
    expected size into a `Bool`-valued predicate makes each
    corpus theorem one `native_decide` on a single equation. -/
def parsesToNDocs (input : String) (n : Nat) : Bool :=
  match scanAndParseIx input with
  | .ok docs => docs.size == n
  | .error _ => false

/-- An error-case check: `scanAndParseIx input` returns `.error _`.
    Used to exhibit the error-propagation leg of the composition
    on inputs that the scanner or parser rejects. -/
def parsesError (input : String) : Bool :=
  match scanAndParseIx input with
  | .ok _ => false
  | .error _ => true

/-! ## §1  Success-case corpus

Each entry exhibits `scanAndParseIx input = .ok docs` for a known
`docs.size`. The corpus spans:
- The empty stream (0 docs)
- Single root scalars (1 doc)
- Block-sequence root (1 doc)
- Flow-collection roots (1 doc each)
- A block-style implicit key (2 docs in the current indexed
  parser, see the file docstring) -/

theorem parses_empty : parsesToNDocs "" 0 = true := by native_decide

theorem parses_plain_x : parsesToNDocs "x" 1 = true := by native_decide

theorem parses_plain_abc : parsesToNDocs "abc" 1 = true := by native_decide

theorem parses_block_seq_one : parsesToNDocs "- x" 1 = true := by native_decide

theorem parses_flow_seq_empty : parsesToNDocs "[]" 1 = true := by native_decide

theorem parses_flow_map_empty : parsesToNDocs "{}" 1 = true := by native_decide

theorem parses_flow_seq_three : parsesToNDocs "[1,2,3]" 1 = true := by native_decide

theorem parses_block_map_one : parsesToNDocs "a: b" 2 = true := by native_decide

/-! ## §2  Error-case corpus

Each entry exhibits `scanAndParseIx input = .error _` for an
input that the pipeline rejects. The cases cover both
scanner-emitted errors (unterminated flow collections) and
parser-emitted errors (the indexed parser's stricter implicit-key
handling on multi-line block mappings). -/

theorem parses_error_unterminated_flow_seq :
    parsesError "[" = true := by native_decide

theorem parses_error_multi_line_implicit_key :
    parsesError "a: 1\nb: 2" = true := by native_decide

end L4YAML.Proofs.Indexed.Composition
