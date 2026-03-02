/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Grammar
import Lean4Yaml.TokenParser
import Lean4Yaml.Proofs.Soundness

/-!
# Parser Soundness (P10.8d)

This module proves the forward direction of the soundness theorem:
every *grammable* `YamlValue` (no aliases, valid plain scalar content)
has a corresponding `ValidNode` whose canonical form matches the
stripped value.

## Main Results

### §6: Annotation Stripping Properties
- `stripAnnotationsList_eq_map` — helper list agrees with `List.map`
- `stripAnnotationsPairs_eq_map` — helper pair list agrees with `List.map`

### §7: Value Witness Theorem
- `scalar_has_witness` — every scalar YamlValue has a ValidNode witness
- `yamlValue_has_witness` — **main theorem**: ∀ grammable v, ∃ ValidNode witness
- `parseStream_sound` — parser output, if grammable, has grammar witnesses

### Scanner Contract

Plain scalar character-level constraints (`validPlainFirst`, `noColonSpace`,
`noSpaceHash`) are guaranteed by the scanner, not the parser.  The
`Grammable` predicate captures this contract as a proof-time hypothesis.
Proving the scanner satisfies this contract is a separate obligation
(future work).

## Zero Axioms

All theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.ParserSoundness

open Lean4Yaml
open Lean4Yaml.Grammar

/-! ## §6  Annotation Stripping Properties

`stripAnnotations` (Grammar.lean) is defined via `where` helpers over
nested lists.  Lean 4's equation theorem generator does not support
this recursion pattern through `Array`, so we provide explicit
`@[simp]` unfolding lemmas.  Each is proved by `rfl` — definitional
unfolding in the kernel always works, even when the tactic-level
equation lemmas are absent.
-/

@[simp] theorem stripAnnotations_scalar (s : Scalar) :
    stripAnnotations (YamlValue.scalar s) =
      YamlValue.scalar ⟨s.content, s.style, none, none, none⟩ := rfl

@[simp] theorem stripAnnotations_sequence
    (style : CollectionStyle) (items : Array YamlValue)
    (tag : Option String) (anchor : Option String) :
    stripAnnotations (YamlValue.sequence style items tag anchor) =
      YamlValue.sequence style
        (stripAnnotations.stripAnnotationsList items.toList).toArray := rfl

@[simp] theorem stripAnnotations_mapping
    (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag : Option String) (anchor : Option String) :
    stripAnnotations (YamlValue.mapping style pairs tag anchor) =
      YamlValue.mapping style
        (stripAnnotations.stripAnnotationsPairs pairs.toList).toArray := rfl

@[simp] theorem stripAnnotations_alias (name : String) :
    stripAnnotations (YamlValue.alias name) = YamlValue.alias name := rfl

/--
`stripAnnotationsList` agrees with `List.map stripAnnotations`.
-/
theorem stripAnnotationsList_eq_map (vs : List YamlValue) :
    stripAnnotations.stripAnnotationsList vs = vs.map stripAnnotations := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp [stripAnnotations.stripAnnotationsList, List.map, ih]

/--
`stripAnnotationsPairs` agrees with `List.map` of the pair stripping.
-/
theorem stripAnnotationsPairs_eq_map (ps : List (YamlValue × YamlValue)) :
    stripAnnotations.stripAnnotationsPairs ps =
    ps.map fun ⟨k, v⟩ => (stripAnnotations k, stripAnnotations v) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp [stripAnnotations.stripAnnotationsPairs, List.map, ih]

/-- Array elements are strictly smaller than the array (for well-founded recursion). -/
private theorem array_sizeOf_getElem_lt {α : Type _} [SizeOf α] (a : Array α) (i : Nat)
    (hi : i < a.size) : sizeOf a[i] < sizeOf a := by
  have hil : i < a.toList.length := hi
  have hmem : a.toList[i] ∈ a.toList := List.getElem_mem hil
  have h1 := List.sizeOf_lt_of_mem hmem
  have h2 : a.toList[i]'hil = a[i] := Array.getElem_toList hi
  rw [h2] at h1
  have h3 : sizeOf a.toList < sizeOf a := by
    rcases a with ⟨l⟩; dsimp; omega
  omega

/-- First component of a pair is strictly smaller than the pair. -/
private theorem prod_fst_sizeOf_lt {α β : Type _} [SizeOf α] [SizeOf β]
    (p : α × β) : sizeOf p.1 < sizeOf p := by
  rcases p with ⟨a, b⟩; simp [Prod.mk.sizeOf_spec]; omega

/-- Second component of a pair is strictly smaller than the pair. -/
private theorem prod_snd_sizeOf_lt {α β : Type _} [SizeOf α] [SizeOf β]
    (p : α × β) : sizeOf p.2 < sizeOf p := by
  rcases p with ⟨a, b⟩; simp [Prod.mk.sizeOf_spec]; omega

/-! ## §7  Value Witness Theorem -/

/--
**Scalar Witness**: every scalar `YamlValue` satisfying the `Grammable`
scalar constraint has a `ValidNode` witness.

Pattern-matches on `Scalar.style` to choose the `ValidNode` constructor.
After expanding `stripAnnotations` and `toYamlValue` (both of which
zero out tags, anchors, and blockMeta), both sides are definitionally
equal — `rfl` closes every non-plain branch, and the plain-empty
branch closes after substituting `content = ""`.
-/
private def scalar_has_witness :
    (s : Scalar) →
    (s.style = .plain → s.content.length > 0 →
       validPlainFirst s.content ∧ noColonSpace s.content ∧ noSpaceHash s.content) →
    ∃ n : ValidNode,
      stripAnnotations (toYamlValue n) = stripAnnotations (YamlValue.scalar s)
  | ⟨content, .singleQuoted, _, _, _⟩, _ => ⟨.singleQuoted content, rfl⟩
  | ⟨content, .doubleQuoted, _, _, _⟩, _ => ⟨.doubleQuoted content, rfl⟩
  | ⟨content, .literal,     _, _, _⟩, _ => ⟨.literalScalar content 0 .clip, rfl⟩
  | ⟨content, .folded,      _, _, _⟩, _ => ⟨.foldedScalar content 0 .clip, rfl⟩
  | ⟨content, .plain,       _, _, _⟩, h => by
    by_cases hne : content.length > 0
    · have ⟨hf, hcs, hsh⟩ := h rfl hne
      exact ⟨.plainScalarBlock content hne hf hcs hsh, rfl⟩
    · have h0 : content.length = 0 := by omega
      have he : content = "" := by
        rw [String.ext_iff]
        simp only [String.length] at h0
        exact List.eq_nil_of_length_eq_zero h0
      exact ⟨.emptyNode, by subst he; rfl⟩

/-! ### List equality helpers -/

private theorem stripped_list_eq
    (nodes : List ValidNode) (items : Array YamlValue)
    (hlen : nodes.length = items.size)
    (helem : ∀ (i : Nat) (hi : i < items.size),
      stripAnnotations (toYamlValue (nodes.get ⟨i, by omega⟩)) =
        stripAnnotations items[i]) :
    (nodes.map toYamlValue).map stripAnnotations =
      items.toList.map stripAnnotations := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi₁ hi₂
  simp only [List.getElem_map]
  have hi : i < items.size := by simp at hi₂; omega
  exact helem i hi

private theorem stripped_pairs_eq
    (nodePairs : List (ValidNode × ValidNode))
    (pairs : Array (YamlValue × YamlValue))
    (hlen : nodePairs.length = pairs.size)
    (hkeys : ∀ (i : Nat) (hi : i < pairs.size),
      stripAnnotations (toYamlValue (nodePairs.get ⟨i, by omega⟩).1) =
        stripAnnotations pairs[i].1)
    (hvals : ∀ (i : Nat) (hi : i < pairs.size),
      stripAnnotations (toYamlValue (nodePairs.get ⟨i, by omega⟩).2) =
        stripAnnotations pairs[i].2) :
    (nodePairs.map fun ⟨k, v⟩ => (toYamlValue k, toYamlValue v)).map
      (fun ⟨k, v⟩ => (stripAnnotations k, stripAnnotations v)) =
    pairs.toList.map fun ⟨k, v⟩ => (stripAnnotations k, stripAnnotations v) := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi₁ hi₂
  simp only [List.getElem_map]
  have hi : i < pairs.size := by simp at hi₂; omega
  exact Prod.ext (hkeys i hi) (hvals i hi)

/--
**Value Witness Theorem**: every grammable `YamlValue` has a corresponding
`ValidNode` whose canonical form (after stripping annotations) matches.

`noncomputable` because `Classical.choice` is used to select witnesses.
-/
noncomputable def yamlValue_has_witness :
    (v : YamlValue) → Grammable v →
    ∃ n : ValidNode, stripAnnotations (toYamlValue n) = stripAnnotations v
  | YamlValue.scalar s, .scalar _ h => scalar_has_witness s h
  | YamlValue.sequence style items _tag _anchor, .sequence _ _ _ _ hchildren => by
    have ih : ∀ i : Fin items.size,
        ∃ n : ValidNode,
          stripAnnotations (toYamlValue n) = stripAnnotations items[i] :=
      fun i => yamlValue_has_witness items[i] (hchildren i)
    let nodes : List ValidNode :=
      (List.finRange items.size).map fun i => (ih i).choose
    have hNodesLen : nodes.length = items.size := by
      show ((List.finRange items.size).map _).length = items.size
      simp [List.length_map, List.length_finRange]
    have hNodesSpec : ∀ (i : Nat) (hi : i < items.size),
        stripAnnotations (toYamlValue (nodes.get ⟨i, by omega⟩)) =
          stripAnnotations items[i] := by
      intro i hi
      show stripAnnotations (toYamlValue
        (((List.finRange items.size).map (fun j => (ih j).choose)).get ⟨i, by
          rw [List.length_map, List.length_finRange]; omega⟩)) = _
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
      exact (ih ⟨i, hi⟩).choose_spec
    have hlist := stripped_list_eq nodes items hNodesLen hNodesSpec
    have hlistArr : ∀ s,
        YamlValue.sequence s
          (stripAnnotations.stripAnnotationsList
            (toYamlValue.toYamlValueList nodes)).toArray =
          YamlValue.sequence s
            (stripAnnotations.stripAnnotationsList items.toList).toArray := by
      intro s; congr 1
      rw [stripAnnotationsList_eq_map, Soundness.toYamlValueList_eq_map,
          stripAnnotationsList_eq_map]
      exact congrArg List.toArray hlist
    match style with
    | .block => exact ⟨.blockSeq 0 nodes, hlistArr .block⟩
    | .flow  => exact ⟨.flowSeq nodes, hlistArr .flow⟩
  | YamlValue.mapping style pairs _tag _anchor, .mapping _ _ _ _ hk hv => by
    have ihk : ∀ i : Fin pairs.size,
        ∃ n : ValidNode,
          stripAnnotations (toYamlValue n) = stripAnnotations pairs[i].1 :=
      fun i => yamlValue_has_witness pairs[i].1 (hk i)
    have ihv : ∀ i : Fin pairs.size,
        ∃ n : ValidNode,
          stripAnnotations (toYamlValue n) = stripAnnotations pairs[i].2 :=
      fun i => yamlValue_has_witness pairs[i].2 (hv i)
    let nodePairs : List (ValidNode × ValidNode) :=
      (List.finRange pairs.size).map fun i => ((ihk i).choose, (ihv i).choose)
    have hPairsLen : nodePairs.length = pairs.size := by
      show ((List.finRange pairs.size).map _).length = pairs.size
      simp [List.length_map, List.length_finRange]
    have hPairsKeys : ∀ (i : Nat) (hi : i < pairs.size),
        stripAnnotations (toYamlValue (nodePairs.get ⟨i, by omega⟩).1) =
          stripAnnotations pairs[i].1 := by
      intro i hi
      show stripAnnotations (toYamlValue
        (((List.finRange pairs.size).map (fun j =>
          ((ihk j).choose, (ihv j).choose))).get ⟨i, by
          rw [List.length_map, List.length_finRange]; omega⟩).1) = _
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
      exact (ihk ⟨i, hi⟩).choose_spec
    have hPairsVals : ∀ (i : Nat) (hi : i < pairs.size),
        stripAnnotations (toYamlValue (nodePairs.get ⟨i, by omega⟩).2) =
          stripAnnotations pairs[i].2 := by
      intro i hi
      show stripAnnotations (toYamlValue
        (((List.finRange pairs.size).map (fun j =>
          ((ihk j).choose, (ihv j).choose))).get ⟨i, by
          rw [List.length_map, List.length_finRange]; omega⟩).2) = _
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
      exact (ihv ⟨i, hi⟩).choose_spec
    have hplist := stripped_pairs_eq nodePairs pairs hPairsLen hPairsKeys hPairsVals
    have hplistArr : ∀ s,
        YamlValue.mapping s
          (stripAnnotations.stripAnnotationsPairs
            (toYamlValue.toYamlValuePairs nodePairs)).toArray =
          YamlValue.mapping s
            (stripAnnotations.stripAnnotationsPairs pairs.toList).toArray := by
      intro s; congr 1
      rw [stripAnnotationsPairs_eq_map, Soundness.toYamlValuePairs_eq_map,
          stripAnnotationsPairs_eq_map]
      exact congrArg List.toArray hplist
    match style with
    | .block => exact ⟨.blockMap 0 nodePairs, hplistArr .block⟩
    | .flow  => exact ⟨.flowMap nodePairs, hplistArr .flow⟩
termination_by v => sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (first
       | (have := array_sizeOf_getElem_lt items i.val i.isLt; omega)
       | (have h1 := array_sizeOf_getElem_lt pairs i.val i.isLt
          have h2 := prod_fst_sizeOf_lt (pairs[i.val])
          omega)
       | (have h1 := array_sizeOf_getElem_lt pairs i.val i.isLt
          have h2 := prod_snd_sizeOf_lt (pairs[i.val])
          omega))

/-! ### §7.1  Parser Soundness Corollary -/

/--
**Parser soundness**: if `parseStream` succeeds and every document value
is grammable (no aliases, valid plain scalars), then each document value
has a `ValidNode` witness in the grammar.

The `Grammable` hypothesis encodes the scanner contract.

```
  Scanner tokens ──→ parseStream ──→ YamlDocument[]
                         │
    Scanner contract     │    Grammable hypothesis
    (validPlainFirst,    │
     noColonSpace, etc.) ▼
                     ∃ ValidNode n,
              stripAnnotations (toYamlValue n)
            = stripAnnotations docs[i].value
```
-/
theorem parseStream_sound
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (_hparse : TokenParser.parseStream tokens = Except.ok docs)
    (hgrammable : ∀ i : Fin docs.size, Grammable docs[i].value) :
    ∀ i : Fin docs.size,
      ∃ n : ValidNode,
        stripAnnotations (toYamlValue n) = stripAnnotations docs[i].value :=
  fun i => yamlValue_has_witness docs[i].value (hgrammable i)

end Lean4Yaml.Proofs.ParserSoundness
