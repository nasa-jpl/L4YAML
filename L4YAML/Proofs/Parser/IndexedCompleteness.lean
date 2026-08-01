/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Spec.Types
import L4YAML.Spec.Grammar
import L4YAML.Parser.Composition
import L4YAML.Parser.TokenParserIx
import L4YAML.Proofs.Soundness
import L4YAML.Proofs.Parser.ParserSoundness

/-! # `IndexedCompleteness` — Phase 3 Step 6d.3 indexed completeness (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

## Role

Indexed twin of `L4YAML/Proofs/Parser/ParserCompleteness.lean`: the
parser-completeness theorems reparented onto `parseStreamIx` /
`Indexed.TokenStream input`.

§8 (annotation stripping idempotence) is pure value-level reasoning
and is reproduced verbatim from the legacy file. §9 (grammar roundtrip)
substitutes `parseStream` → `parseStreamIx` and
`Array (Positioned YamlToken)` → `Indexed.TokenStream input`.

## Phase 3 Step 6f cutover

At cutover, this file is renamed to `Proofs/Parser/ParserCompleteness.lean`
(overwriting the legacy file) and the namespace
`L4YAML.Proofs.Indexed.Completeness` reverts to
`L4YAML.Proofs.ParserCompleteness`.

# Parser Completeness (P10.8e — indexed)

This module proves the completeness direction of the grammar–value bridge:
given a grammable value, the soundness witness is itself well-formed,
and the annotation-stripping roundtrip is internally consistent.

Combined with `parseStreamIx_sound` (P10.8d), this establishes a full
bidirectional correspondence:

```
  Soundness  (P10.8d):  Grammable v inFlow  →  ∃ n, stripAnnotations (toYamlValue n) = stripAnnotations v
  Completeness (P10.8e): ∀ grammable v, ∃ n', stripAnnotations (toYamlValue n') = stripAnnotations v
```

Together these show the grammar is **roundtrip-complete** (the
soundness theorem can always recover a grammar witness for any
grammar-produced value).

**Note on junk-freeness**: With context-aware `Grammable` (B2), the
property `∀ n, Grammable (toYamlValue n) inFlow` cannot hold universally
because `ValidNode` does not enforce flow-context consistency (e.g.,
`.plainScalarBlock` inside `.flowSeq` is syntactically valid but not
flow-grammable). Witnesses constructed by `yamlValue_has_witness` ARE
context-consistent by construction, but this is not captured as a
separate theorem.

## Main Results

### §8: Annotation Stripping Properties
- `stripAnnotations_idempotent` — double-stripping equals single stripping
- `stripAnnotations_toYamlValue_scalar_content` — stripping a grammar scalar is identity-on-content

### §9: Grammar Roundtrip
- `grammar_value_roundtrip` — grammable `ValidNode` values have roundtrip witnesses
- `parseStreamIx_complete` — parser completeness conditioned on grammability
- `soundness_completeness_compose` — bidirectional bridge composition

### Scanner Contract Boundary

Full end-to-end completeness (`ValidNode → ∃ tokens, parseStreamIx tokens = .ok docs`)
requires **scanner correctness**: showing that `Scanner.Indexed.scanIx` produces a
token stream that `TokenParser.Indexed.parseStreamIx` accepts and reconstructs the
original grammar node.  This is a separate proof obligation of
unbounded scope (the scanner is ~2000 lines of Lean).

The grammar-level completeness proved here is the **maximal result
achievable without scanner correctness**.  It guarantees the grammar
is internally consistent and composes correctly with soundness.

## Zero Axioms

All theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.Completeness

open L4YAML
open L4YAML.Grammar
open L4YAML.Indexed
open L4YAML.TokenParser.Indexed

variable {input : String}

/-! ## §8  Annotation Stripping Properties

The idempotence proof requires mutual recursion between `YamlValue`
stripping and the list/pair helpers that handle collection elements.
-/

mutual
/-- List helper for idempotence. -/
theorem stripAnnotationsList_idempotent :
    (vs : List YamlValue) →
    stripAnnotations.stripAnnotationsList (stripAnnotations.stripAnnotationsList vs) =
      stripAnnotations.stripAnnotationsList vs
  | [] => rfl
  | v :: vs => by
      simp only [stripAnnotations.stripAnnotationsList]
      exact congr (congrArg List.cons (stripAnnotations_idempotent v))
        (stripAnnotationsList_idempotent vs)

/-- Pair list helper for idempotence. -/
theorem stripAnnotationsPairs_idempotent :
    (ps : List (YamlValue × YamlValue)) →
    stripAnnotations.stripAnnotationsPairs (stripAnnotations.stripAnnotationsPairs ps) =
      stripAnnotations.stripAnnotationsPairs ps
  | [] => rfl
  | (k, v) :: ps => by
      simp only [stripAnnotations.stripAnnotationsPairs]
      exact congr
        (congrArg List.cons
          (Prod.ext (stripAnnotations_idempotent k) (stripAnnotations_idempotent v)))
        (stripAnnotationsPairs_idempotent ps)

/--
**Annotation stripping is idempotent**: stripping twice is the same as
stripping once.

This is a natural property: once annotations are removed, there is
nothing left to strip.
-/
theorem stripAnnotations_idempotent :
    (v : YamlValue) →
    stripAnnotations (stripAnnotations v) = stripAnnotations v
  | .scalar _s => rfl
  | .sequence _style items _tag _anchor => by
      simp only [ParserSoundness.stripAnnotations_sequence]
      suffices h : stripAnnotations.stripAnnotationsList
          (stripAnnotations.stripAnnotationsList items.toList).toArray.toList =
          stripAnnotations.stripAnnotationsList items.toList by
        simp only [h]
      rw [List.toList_toArray]
      exact stripAnnotationsList_idempotent items.toList
  | .mapping _style pairs _tag _anchor => by
      simp only [ParserSoundness.stripAnnotations_mapping]
      suffices h : stripAnnotations.stripAnnotationsPairs
          (stripAnnotations.stripAnnotationsPairs pairs.toList).toArray.toList =
          stripAnnotations.stripAnnotationsPairs pairs.toList by
        simp only [h]
      rw [List.toList_toArray]
      exact stripAnnotationsPairs_idempotent pairs.toList
  | .alias _name => rfl
end

/--
Stripped `toYamlValue` for a scalar is just the content+style with no metadata.

This partial identity shows that `toYamlValue` already produces
annotation-free values for all scalar constructors (the block-scalar
metadata field `some ⟨chomp, indent⟩` is the only difference, and
`stripAnnotations` removes it).
-/
theorem stripAnnotations_toYamlValue_scalar_content (n : ValidNode) (s : Scalar)
    (h : toYamlValue n = .scalar s) :
    stripAnnotations (toYamlValue n) =
      .scalar ⟨s.content, s.style, none, none, none⟩ := by
  rw [h]; rfl

/-! ## §9  Grammar Roundtrip

The main completeness result: given a grammable `YamlValue`, the
soundness theorem can recover a grammar witness that roundtrips
through annotation stripping.

```
  YamlValue v ──Grammable v inFlow──→ ∃ n, stripAnnotations (toYamlValue n) = stripAnnotations v
```

This is a direct corollary of `yamlValue_has_witness` (P10.8d §7).

**Note**: With context-aware `Grammable` (B2), the unconditional property
`∀ n : ValidNode, Grammable (toYamlValue n) inFlow` no longer holds because
`ValidNode` does not enforce flow-context consistency. The roundtrip
theorem is therefore conditional on the value being grammable.
-/

/--
**Grammar roundtrip**: a grammable `ValidNode` value has a grammar witness
whose stripped canonical form matches.

This theorem closes the soundness–completeness loop at the grammar level:
- **Soundness** (P10.8d): every grammable value has a grammar witness
- **Roundtrip** (this theorem): composing soundness with grammability,
  every grammable grammar node has a canonical representative

The `inFlow` parameter and `Grammable` hypothesis are required because
context-aware `Grammable` cannot be proven universally for all `ValidNode`
values — only for those that are flow-context-consistent.
-/
@[capstone]
theorem grammar_value_roundtrip (n : ValidNode) (inFlow : Bool)
    (hg : Grammable (toYamlValue n) inFlow) :
    ∃ n' : ValidNode,
      stripAnnotations (toYamlValue n') = stripAnnotations (toYamlValue n) :=
  ParserSoundness.yamlValue_has_witness (toYamlValue n) inFlow hg

/--
**Parser completeness**: if `parseStreamIx` succeeds and every document
value is grammable, then for each document there exists a `ValidNode`
witness whose stripped form matches.

This is the conditional completeness theorem: it does not require
scanner correctness.  The full pipeline completeness
```
  ValidNode n → ∃ tokens docs, parseStreamIx tokens = .ok docs ∧ n ∈ docs
```
additionally requires showing that `Scanner.Indexed.scanIx (serialize n)` produces
tokens that `parseStreamIx` accepts — a separate (substantial) proof.

Instead, this theorem says: *once the parser has run and its output is
grammable, the grammar→value→grammar roundtrip is always available*.

Combined with `parseStreamIx_sound`:
```
  parseStreamIx ok ∧ Grammable docs[i].value false
    → ∃ n, stripAnnotations (toYamlValue n) = stripAnnotations docs[i].value   [soundness]
```
-/
theorem parseStreamIx_complete
    (tokens : Indexed.TokenStream input)
    (docs : Array YamlDocument)
    (_hparse : parseStreamIx tokens = Except.ok docs)
    (hgrammable : ∀ i : Fin docs.size, Grammable docs[i].value false) :
    ∀ i : Fin docs.size,
      ∃ n : ValidNode,
        stripAnnotations (toYamlValue n) = stripAnnotations docs[i].value :=
  fun i =>
    ParserSoundness.yamlValue_has_witness docs[i].value false (hgrammable i)

/--
**Soundness–completeness composition**: for any grammable value,
there exists a `ValidNode` witness whose stripped form matches.

This is the core bridge: the soundness direction (P10.8d) always finds
a witness `n` from a grammable value `v`.
-/
@[capstone]
theorem soundness_completeness_compose
    (v : YamlValue) (hg : Grammable v false) :
    ∃ n : ValidNode,
      stripAnnotations (toYamlValue n) = stripAnnotations v :=
  ParserSoundness.yamlValue_has_witness v false hg

end L4YAML.Proofs.Indexed.Completeness
