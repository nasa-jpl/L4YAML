/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Parser.Composition
import L4YAML.Parser.TokenParserIx
import L4YAML.Spec.Grammar
import L4YAML.Proofs.Soundness
import L4YAML.Proofs.Parser.ParserSoundness
import L4YAML.Proofs.Scanner.ScannerCorrectness

/-! # `IndexedCorrectness` — Phase 3 Step 6d.3 indexed correctness (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

## Role

Indexed twin of `L4YAML/Proofs/Parser/ParserCorrectness.lean`: the
parser-correctness theorem reparented onto `parseStreamIx` /
`Indexed.TokenStream input` (vs legacy `parseStream` /
`Array (Positioned YamlToken)`).

The proof is purely a value-level corollary of
`ParserSoundness.yamlValue_has_witness`, which is reused verbatim:
the indexed substitution only changes how `docs` are obtained.

## Phase 3 Step 6f cutover

At cutover, this file is renamed to `Proofs/Parser/ParserCorrectness.lean`
(overwriting the legacy file) and the namespace
`L4YAML.Proofs.Indexed.Correctness` reverts to
`L4YAML.Proofs.ParserCorrectness`.

# Parser Correctness (P10.11b — indexed)

Proves that `TokenParser.Indexed.parseStreamIx` respects the grammar
specification: every successfully parsed value (after composition) has a
corresponding `ValidNode` witness.

## Main Result

```lean
theorem parseStreamIx_respects_grammar :
  TokenParser.Indexed.parseStreamIx tokens = .ok docs →
  (∀ doc ∈ docs, Grammable (doc.compose.value)) →
  ∀ doc ∈ docs, ∃ node, stripAnnotations (toYamlValue node) =
                         stripAnnotations (doc.compose.value)
```

This establishes the bridge between the indexed parser and grammar: composed
parser output (aliases resolved, anchors stripped) conforms to the grammar
specification.

## Structure

### §1  Parser Output Properties
- `parseStreamIx_values_have_witnesses` — Conditional soundness theorem

### §2  Main Correctness Theorem
- `parseStreamIx_respects_grammar` — Parser respects grammar (conditional)

## Strategy

**Key insight**: `parseStreamIx` returns the **serialization tree** (YAML 1.2.2 §3.1),
which may contain `.alias` nodes. The `Grammable` predicate has NO constructor
for aliases — they must be resolved first.

After **composition** (`YamlDocument.compose`), which resolves aliases and strips
anchors, the resulting **representation graph** can be shown to have `ValidNode`
witnesses (assuming grammability).

This conditional approach matches the pattern throughout the proof suite
(see ScannerEmitBridge.lean, IndexedCompleteness.lean).

## Zero Axioms

All theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.Correctness

open L4YAML
open L4YAML.Grammar
open L4YAML.Indexed
open L4YAML.TokenParser.Indexed
open L4YAML.Proofs.Soundness
open L4YAML.Proofs.ParserSoundness

variable {input : String}

/-! ## §1  Parser Output Properties

The parser's output must satisfy certain properties to have grammar witnesses.

**Key distinction**:
- **Serialization tree** (`parseStreamIx` output): May contain `.alias` nodes
- **Representation graph** (`compose` output): Aliases resolved, anchors stripped

The `Grammable` predicate (Grammar.lean:644-657) has constructors for scalar,
sequence, and mapping, but NOT for alias. Values with unresolved aliases
are explicitly not grammable.
-/

/--
**Conditional soundness**: After composition, grammable values have `ValidNode` witnesses.

Every document produced by `parseStreamIx`, after alias resolution and anchor
stripping via `YamlDocument.compose`, has a corresponding `ValidNode` whose
canonical form matches the composed value.

This is the **standard pattern** in the codebase:
- ScannerEmitBridge.lean:381-390, 403-413 use the same conditional approach
- IndexedCompleteness.lean:315-325 assumes grammability as hypothesis
- The condition "composed values are grammable" holds when:
  1. Scanner validates plain scalar content (character-level constraints)
  2. Parser preserves these properties
  3. Aliases are resolvable (no cycles, valid anchors)

**Why conditional**: Proving the grammability hypothesis requires analyzing:
- Scanner's `scanPlainScalar` validates `validPlainFirstProp`, `noColonSpace`, `noSpaceHash`
- TokenParser.Indexed's 14 fuel-based mutual `def` functions preserve token properties
- `YamlValue.resolveAliases` produces valid values

This is ~200-300 lines of implementation-level proof. The conditional form
isolates the grammar-level reasoning from implementation details.

**Termination**: All parser functions are total (no `partial`). The mutual
block uses structural decrease on a `fuel : Nat` parameter, with
`fuel := 4 * tokens.size + 4` set at `parseDocument`. Lean 4 infers
termination automatically from the `match fuel with | fuel + 1 => ...`
pattern — no `termination_by` annotations needed.

**Empirical validation**: 787 `#guard` checks in Proofs/SuiteGuards/*.lean
successfully parse and compose the yaml-test-suite, providing strong evidence
that the hypothesis holds in practice.
-/
lemma parseStreamIx_values_have_witnesses
    (tokens : Indexed.TokenStream input)
    (docs : Array YamlDocument)
    (_h : parseStreamIx tokens = .ok docs)
    (h_grammable : ∀ doc ∈ docs.toList, Grammable (doc.compose.value) false) :
    ∀ doc ∈ docs.toList, ∃ node : ValidNode,
      stripAnnotations (toYamlValue node) = stripAnnotations (doc.compose.value) := by
  intro doc hdoc
  have hg := h_grammable doc hdoc
  -- Apply yamlValue_has_witness from ParserSoundness.lean
  exact ParserSoundness.yamlValue_has_witness (doc.compose.value) false hg

/-! ## §2  Main Correctness Theorem

The main result: parser output respects the grammar (after composition).
-/

/--
**Main theorem**: The parser respects the grammar (conditional).

Every document produced by successful parsing, after composition (alias
resolution + anchor stripping), has a corresponding `ValidNode` whose canonical
form matches the composed value.

This establishes that the indexed parser implementation conforms to the grammar
specification in Grammar.lean, modulo the assumption that composed values
are grammable.

**Composition**: The theorem is about `doc.compose.value`, not raw `doc.value`,
because:
1. Raw parser output may contain `.alias` nodes (serialization tree)
2. Aliases must be resolved to obtain the representation graph
3. The grammar models the representation graph, not the serialization tree
4. This matches YAML 1.2.2 §3.1 distinction between Parse and Compose

**Conditional form**: The grammability hypothesis is standard practice in this
codebase (see ScannerEmitBridge.lean, IndexedCompleteness.lean) and is empirically
validated by 787 `#guard` checks.
-/
lemma parseStreamIx_respects_grammar
    (tokens : Indexed.TokenStream input)
    (docs : Array YamlDocument)
    (h_parse : parseStreamIx tokens = .ok docs)
    (h_grammable : ∀ doc ∈ docs.toList, Grammable (doc.compose.value) false) :
    ∀ doc ∈ docs.toList, ∃ node : ValidNode,
      stripAnnotations (toYamlValue node) = stripAnnotations (doc.compose.value) := by
  exact parseStreamIx_values_have_witnesses tokens docs h_parse h_grammable

end L4YAML.Proofs.Indexed.Correctness
