/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Grammar
import Lean4Yaml.TokenParser
import Lean4Yaml.Proofs.Soundness
import Lean4Yaml.Proofs.ParserSoundness

/-!
# Parser Completeness (P10.8e)

This module proves the completeness direction of the grammar–value bridge:
every `ValidNode` in the grammar produces a **grammable** `YamlValue`,
and the annotation-stripping roundtrip is internally consistent.

Combined with `parseStream_sound` (P10.8d), this establishes a full
bidirectional correspondence:

```
  Soundness  (P10.8d):  Grammable v  →  ∃ n, stripAnnotations (toYamlValue n) = stripAnnotations v
  Completeness (P10.8e): ∀ n,  toYamlValue n  is Grammable
                         ∧  ∃ n', stripAnnotations (toYamlValue n') = stripAnnotations (toYamlValue n)
```

Together these show the grammar is **junk-free** (every grammar node
produces a grammable value) and **roundtrip-complete** (the
soundness theorem can always recover a grammar witness for any
grammar-produced value).

## Main Results

### §8: Grammar Grammability
- `toYamlValue_grammable` — every `ValidNode` produces a grammable `YamlValue`

### §9: Annotation Stripping Properties
- `stripAnnotations_idempotent` — double-stripping equals single stripping
- `stripAnnotations_toYamlValue_scalar_content` — stripping a grammar scalar is identity-on-content

### §10: Grammar Roundtrip
- `grammar_value_roundtrip` — every `ValidNode` has a roundtrip witness
- `parseStream_complete` — parser completeness conditioned on grammability
- `soundness_completeness_compose` — bidirectional bridge composition

### Scanner Contract Boundary

Full end-to-end completeness (`ValidNode → ∃ tokens, parseStream tokens = .ok docs`)
requires **scanner correctness**: showing that `Scanner.scan` produces a
token stream that `TokenParser.parseStream` accepts and reconstructs the
original grammar node.  This is a separate proof obligation of
unbounded scope (the scanner is ~2000 lines of Lean).

The grammar-level completeness proved here is the **maximal result
achievable without scanner correctness**.  It guarantees the grammar
is internally consistent and composes correctly with soundness.

## Zero Axioms

All theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.ParserCompleteness

open Lean4Yaml
open Lean4Yaml.Grammar

/-! ## §8  Grammar Grammability

Every `ValidNode` produces a `YamlValue` (via `toYamlValue`) that
satisfies the `Grammable` predicate.  This means the grammar contains
no "junk" — every well-formed grammar node corresponds to a value
that the soundness theorem can process.

The proof is by structural recursion on `ValidNode`, matching the
structure of `toYamlValue` itself.
-/

/-- List helper: if every `ValidNode` in a list produces a grammable value,
    then the `toYamlValueList` result is element-wise grammable. -/
private theorem toYamlValueList_grammable
    (nodes : List ValidNode)
    (ih : ∀ (n : ValidNode), sizeOf n < sizeOf nodes → Grammable (toYamlValue n)) :
    ∀ (i : Nat) (hi : i < (toYamlValue.toYamlValueList nodes).length),
      Grammable ((toYamlValue.toYamlValueList nodes)[i]) := by
  rw [Soundness.toYamlValueList_eq_map]
  intro i hi
  simp only [List.length_map] at hi
  simp only [List.getElem_map]
  exact ih nodes[i] (List.sizeOf_lt_of_mem (List.getElem_mem hi))

/-- Pair list helper: if every `ValidNode` in a pair list produces grammable
    values, then the keys of `toYamlValuePairs` are grammable. -/
private theorem toYamlValuePairs_keys_grammable
    (entries : List (ValidNode × ValidNode))
    (ih : ∀ (n : ValidNode), sizeOf n < sizeOf entries → Grammable (toYamlValue n)) :
    ∀ (i : Nat) (hi : i < (toYamlValue.toYamlValuePairs entries).length),
      Grammable ((toYamlValue.toYamlValuePairs entries)[i].1) := by
  rw [Soundness.toYamlValuePairs_eq_map]
  intro i hi
  simp only [List.length_map] at hi
  simp only [List.getElem_map]
  apply ih entries[i].1
  have h1 := List.sizeOf_lt_of_mem (List.getElem_mem hi)
  have h2 : sizeOf entries[i] = 1 + sizeOf entries[i].1 + sizeOf entries[i].2 := by
    cases entries[i]; simp [Prod.mk.sizeOf_spec]
  omega

/-- Pair list helper: values of `toYamlValuePairs` are grammable. -/
private theorem toYamlValuePairs_vals_grammable
    (entries : List (ValidNode × ValidNode))
    (ih : ∀ (n : ValidNode), sizeOf n < sizeOf entries → Grammable (toYamlValue n)) :
    ∀ (i : Nat) (hi : i < (toYamlValue.toYamlValuePairs entries).length),
      Grammable ((toYamlValue.toYamlValuePairs entries)[i].2) := by
  rw [Soundness.toYamlValuePairs_eq_map]
  intro i hi
  simp only [List.length_map] at hi
  simp only [List.getElem_map]
  apply ih entries[i].2
  have h1 := List.sizeOf_lt_of_mem (List.getElem_mem hi)
  have h2 : sizeOf entries[i] = 1 + sizeOf entries[i].1 + sizeOf entries[i].2 := by
    cases entries[i]; simp [Prod.mk.sizeOf_spec]
  omega

/--
**Grammar grammability**: every `ValidNode` produces a grammable `YamlValue`.

This is the completeness kernel — it shows the grammar contains no junk.
Each `ValidNode` constructor carries exactly the proof obligations that
`Grammable` demands for the corresponding `YamlValue`.

- **Plain scalars** (block/flow): the `ValidNode` constructor already
  carries `validPlainFirst`, `noColonSpace`, `noSpaceHash` proofs;
  the `Grammable.scalar` hypothesis is satisfied directly.
- **Non-plain scalars**: `.singleQuoted`, `.doubleQuoted`, `.literal`,
  `.folded` — the `Grammable.scalar` hypothesis is vacuously true
  because `s.style ≠ .plain`.
- **Empty node**: `s.content = ""` so `s.content.length = 0`,
  making the hypothesis `s.content.length > 0 → ...` vacuously true.
- **Collections**: structural recursion through the list helpers above.
  Array size and indexing for `l.toArray` are definitionally equal to
  list length and indexing, so no conversion lemmas are needed.
-/
def toYamlValue_grammable : (n : ValidNode) → Grammable (toYamlValue n)
  | .plainScalarBlock content _hne hf hcs hsh =>
      .scalar ⟨content, .plain, none, none, none⟩ (fun _ _ => ⟨hf, hcs, hsh⟩)
  | .plainScalarFlow content _hne hf hcs hsh _ =>
      .scalar ⟨content, .plain, none, none, none⟩ (fun _ _ => ⟨hf, hcs, hsh⟩)
  | .singleQuoted content =>
      .scalar ⟨content, .singleQuoted, none, none, none⟩ (nofun)
  | .doubleQuoted content =>
      .scalar ⟨content, .doubleQuoted, none, none, none⟩ (nofun)
  | .literalScalar content indent chomp =>
      .scalar ⟨content, .literal, none, none, some ⟨chomp, some indent⟩⟩ (nofun)
  | .foldedScalar content indent chomp =>
      .scalar ⟨content, .folded, none, none, some ⟨chomp, some indent⟩⟩ (nofun)
  | .emptyNode =>
      .scalar ⟨"", .plain, none, none, none⟩
        (fun _ h => absurd h (Nat.not_lt.mpr (Nat.le.refl)))
  | .blockSeq _indent items =>
      .sequence .block _ none none (fun ⟨i, hi⟩ =>
        toYamlValueList_grammable items
          (fun n _hn => toYamlValue_grammable n) i hi)
  | .flowSeq items =>
      .sequence .flow _ none none (fun ⟨i, hi⟩ =>
        toYamlValueList_grammable items
          (fun n _hn => toYamlValue_grammable n) i hi)
  | .blockMap _indent entries =>
      .mapping .block _ none none
        (fun ⟨i, hi⟩ =>
          toYamlValuePairs_keys_grammable entries
            (fun n _hn => toYamlValue_grammable n) i hi)
        (fun ⟨i, hi⟩ =>
          toYamlValuePairs_vals_grammable entries
            (fun n _hn => toYamlValue_grammable n) i hi)
  | .flowMap entries =>
      .mapping .flow _ none none
        (fun ⟨i, hi⟩ =>
          toYamlValuePairs_keys_grammable entries
            (fun n _hn => toYamlValue_grammable n) i hi)
        (fun ⟨i, hi⟩ =>
          toYamlValuePairs_vals_grammable entries
            (fun n _hn => toYamlValue_grammable n) i hi)

/-! ## §9  Annotation Stripping Properties

The idempotence proof requires mutual recursion between `YamlValue`
stripping and the list/pair helpers that handle collection elements.
-/

mutual
/-- List helper for idempotence. -/
private def stripAnnotationsList_idempotent :
    (vs : List YamlValue) →
    stripAnnotations.stripAnnotationsList (stripAnnotations.stripAnnotationsList vs) =
      stripAnnotations.stripAnnotationsList vs
  | [] => rfl
  | v :: vs => by
      simp only [stripAnnotations.stripAnnotationsList]
      exact congr (congrArg List.cons (stripAnnotations_idempotent v))
        (stripAnnotationsList_idempotent vs)

/-- Pair list helper for idempotence. -/
private def stripAnnotationsPairs_idempotent :
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
def stripAnnotations_idempotent :
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

/-! ## §10  Grammar Roundtrip

The main completeness result: every `ValidNode` has a grammar witness
that roundtrips through annotation stripping.

```
  ValidNode n ──toYamlValue──→ YamlValue v ──stripAnnotations──→ stripped v
       ↑                                                              ‖
       └─── ∃ n' : ValidNode ────── toYamlValue n' ──strip──→ = stripped v
```

This is proved by composing `toYamlValue_grammable` (§8) with
`yamlValue_has_witness` (P10.8d §7).
-/

/--
**Grammar roundtrip**: every `ValidNode` has a grammar witness whose
stripped canonical form matches.

This theorem closes the soundness–completeness loop at the grammar level:
- **Soundness** (P10.8d): every grammable value has a grammar witness
- **Completeness** (P10.8e): every grammar node produces a grammable value
- **Roundtrip** (this theorem): composing the two, every grammar node
  has a canonical representative
-/
noncomputable def grammar_value_roundtrip (n : ValidNode) :
    ∃ n' : ValidNode,
      stripAnnotations (toYamlValue n') = stripAnnotations (toYamlValue n) :=
  ParserSoundness.yamlValue_has_witness (toYamlValue n) (toYamlValue_grammable n)

/--
**Parser completeness**: if `parseStream` succeeds and every document
value is grammable, then for each `ValidNode` appearing (up to
annotation stripping) in the parser output, there exists a `ValidNode`
witness that matches it.

This is the conditional completeness theorem: it does not require
scanner correctness.  The full pipeline completeness
```
  ValidNode n → ∃ tokens docs, parseStream tokens = .ok docs ∧ n ∈ docs
```
additionally requires showing that `Scanner.scan (serialize n)` produces
tokens that `parseStream` accepts — a separate (substantial) proof.

Instead, this theorem says: *once the parser has run and its output is
grammable, the grammar→value→grammar roundtrip is always available*.

Combined with `parseStream_sound`:
```
  parseStream ok ∧ Grammable docs[i].value
    → ∃ n, stripAnnotations (toYamlValue n) = stripAnnotations docs[i].value   [soundness]
    → Grammable (toYamlValue n)                                                 [completeness]
    → ∃ n', stripAnnotations (toYamlValue n') = stripAnnotations (toYamlValue n) [roundtrip]
```
-/
noncomputable def parseStream_complete
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (_hparse : TokenParser.parseStream tokens = Except.ok docs)
    (hgrammable : ∀ i : Fin docs.size, Grammable docs[i].value) :
    ∀ i : Fin docs.size,
      ∃ n : ValidNode, Grammable (toYamlValue n) ∧
        stripAnnotations (toYamlValue n) = stripAnnotations docs[i].value :=
  fun i =>
    let ⟨n, hn⟩ := ParserSoundness.yamlValue_has_witness docs[i].value (hgrammable i)
    ⟨n, toYamlValue_grammable n, hn⟩

/--
**Soundness–completeness composition**: for any grammable value, the
recovered grammar witness is itself grammable.

This is the key "no junk" property: the soundness direction (P10.8d)
finds a witness `n` from a value `v`, and completeness (P10.8e) guarantees
`toYamlValue n` is grammable — so the process can be iterated.
-/
noncomputable def soundness_completeness_compose
    (v : YamlValue) (hg : Grammable v) :
    ∃ n : ValidNode,
      stripAnnotations (toYamlValue n) = stripAnnotations v ∧
      Grammable (toYamlValue n) :=
  let ⟨n, hn⟩ := ParserSoundness.yamlValue_has_witness v hg
  ⟨n, hn, toYamlValue_grammable n⟩

end Lean4Yaml.Proofs.ParserCompleteness
