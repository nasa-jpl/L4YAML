/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Grammar

/-!
# Soundness Proofs

This module proves that the `NodeToValue` correspondence relation
(Grammar.lean) is total, deterministic, and faithfully implemented
by the computable `toYamlValue` specification function.

## Theorem Inventory

### §1: Specification Function Correctness
- `toYamlValueList_eq_map` — `toYamlValueList` = `List.map toYamlValue`
- `toYamlValuePairs_eq_map` — `toYamlValuePairs` = `List.map` of pair conversion
- `toYamlValue_correct` — `toYamlValue n = v ↔ NodeToValue n v`

### §2: Totality & Determinism
- `nodeToValue_total` — every `ValidNode` has a corresponding `YamlValue`
- `nodeToValue_deterministic` — `NodeToValue n v₁ ∧ NodeToValue n v₂ → v₁ = v₂`

### §3: Scalar Soundness
- `plainScalar_style_sound` — plain scalars produce `.plain` style
- `singleQuoted_style_sound` — single-quoted scalars produce `.singleQuoted`
- `doubleQuoted_style_sound` — double-quoted scalars produce `.doubleQuoted`
- `literal_style_sound` — literal scalars produce `.literal` style
- `folded_style_sound` — folded scalars produce `.folded` style
- `scalar_content_preserved` — scalar content is preserved through the correspondence

### §4: Collection Soundness
- `blockSeq_style_sound` — block sequences produce `.block` style
- `flowSeq_style_sound` — flow sequences produce `.flow` style
- `blockMap_style_sound` — block mappings produce `.block` style
- `flowMap_style_sound` — flow mappings produce `.flow` style
- `seq_items_sound` — sequence item count is preserved
- `map_entries_sound` — mapping entry count is preserved

### §5: Structural Composition
- `validYaml_construct` — `ValidYaml` can always be constructed from a `ValidNode`
- `validYaml_value_eq_toYamlValue` — the value in `ValidYaml` equals `toYamlValue`

## Zero Axioms

All theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.Soundness

open Lean4Yaml
open Lean4Yaml.Grammar

/-! ## §1  Specification Function Correctness

The `toYamlValue` function (Grammar.lean) computes the `YamlValue` for
any `ValidNode`. Here we prove it faithfully implements the `NodeToValue`
inductive relation.
-/

/--
`toYamlValueList` agrees with `List.map toYamlValue`.

This structural lemma is needed because `toYamlValueList` is defined
via explicit recursion (to satisfy Lean's termination checker) rather
than `List.map`.
-/
theorem toYamlValueList_eq_map (ns : List ValidNode) :
    toYamlValue.toYamlValueList ns = ns.map toYamlValue := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp [toYamlValue.toYamlValueList, List.map, ih]

/--
`toYamlValuePairs` agrees with `List.map` of the pair conversion.
-/
theorem toYamlValuePairs_eq_map (es : List (ValidNode × ValidNode)) :
    toYamlValue.toYamlValuePairs es = es.map fun ⟨k, v⟩ => (toYamlValue k, toYamlValue v) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp [toYamlValue.toYamlValuePairs, List.map, ih]

/-! ### Size helpers for well-founded recursion through product lists -/

private theorem prod_fst_sizeOf_lt {α β : Type _} [SizeOf α] [SizeOf β]
    (l : List (α × β)) (i : Nat) (hi : i < l.length) :
    sizeOf l[i].1 < sizeOf l := by
  have h1 := List.sizeOf_lt_of_mem (List.getElem_mem hi)
  have h2 : sizeOf l[i] = 1 + sizeOf l[i].1 + sizeOf l[i].2 := by
    cases l[i]; simp [Prod.mk.sizeOf_spec]
  omega

private theorem prod_snd_sizeOf_lt {α β : Type _} [SizeOf α] [SizeOf β]
    (l : List (α × β)) (i : Nat) (hi : i < l.length) :
    sizeOf l[i].2 < sizeOf l := by
  have h1 := List.sizeOf_lt_of_mem (List.getElem_mem hi)
  have h2 : sizeOf l[i] = 1 + sizeOf l[i].1 + sizeOf l[i].2 := by
    cases l[i]; simp [Prod.mk.sizeOf_spec]
  omega

/--
Forward direction: `toYamlValue` produces a value satisfying `NodeToValue`.

Defined as a recursive function (not tactic proof) because `ValidNode`
is a nested inductive, so the `induction` tactic does not support it.
Uses well-founded recursion on `sizeOf` to handle recursive calls through
list elements.
-/
def toYamlValue_nodeToValue : (n : ValidNode) → NodeToValue n (toYamlValue n)
  | .plainScalarBlock content h hf hcs hsh => .plainScalarBlock content h hf hcs hsh
  | .plainScalarFlow content h hf hcs hsh hfl => .plainScalarFlow content h hf hcs hsh hfl
  | .singleQuoted content => .singleQuoted content
  | .doubleQuoted content => .doubleQuoted content
  | .literalScalar content indent chomp => .literalScalar content indent chomp
  | .foldedScalar content indent chomp => .foldedScalar content indent chomp
  | .blockSeq indent items => by
      simp [toYamlValue, toYamlValueList_eq_map]
      exact .blockSeq indent items (items.map toYamlValue) (by simp) (fun i hi => by
        simp [List.get_eq_getElem, List.getElem_map]
        exact toYamlValue_nodeToValue items[i])
  | .blockMap indent entries => by
      simp [toYamlValue, toYamlValuePairs_eq_map]
      exact .blockMap indent entries
        (entries.map fun ⟨k, v⟩ => (toYamlValue k, toYamlValue v)) (by simp)
        (fun i hi => by
          simp [List.get_eq_getElem, List.getElem_map]
          exact toYamlValue_nodeToValue entries[i].1)
        (fun i hi => by
          simp [List.get_eq_getElem, List.getElem_map]
          exact toYamlValue_nodeToValue entries[i].2)
  | .flowSeq items => by
      simp [toYamlValue, toYamlValueList_eq_map]
      exact .flowSeq items (items.map toYamlValue) (by simp) (fun i hi => by
        simp [List.get_eq_getElem, List.getElem_map]
        exact toYamlValue_nodeToValue items[i])
  | .flowMap entries => by
      simp [toYamlValue, toYamlValuePairs_eq_map]
      exact .flowMap entries
        (entries.map fun ⟨k, v⟩ => (toYamlValue k, toYamlValue v)) (by simp)
        (fun i hi => by
          simp [List.get_eq_getElem, List.getElem_map]
          exact toYamlValue_nodeToValue entries[i].1)
        (fun i hi => by
          simp [List.get_eq_getElem, List.getElem_map]
          exact toYamlValue_nodeToValue entries[i].2)
termination_by n => sizeOf n
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem (List.getElem_mem ‹_›); omega)
    | (have := prod_fst_sizeOf_lt _ _ ‹_›; omega)
    | (have := prod_snd_sizeOf_lt _ _ ‹_›; omega)

/-! ### Helper: list equality from element-wise induction hypotheses -/

private theorem vals_eq_map_of_ih
    (nodes : List ValidNode) (vals : List YamlValue)
    (hlen : nodes.length = vals.length)
    (ih : ∀ i (hi : i < nodes.length),
      vals.get ⟨i, by omega⟩ = toYamlValue (nodes.get ⟨i, hi⟩)) :
    vals = nodes.map toYamlValue := by
  apply List.ext_get (by simp [hlen])
  intro i hi₁ hi₂
  simp only [List.get_eq_getElem, List.getElem_map]
  exact ih i (by omega)

private theorem pairs_eq_map_of_ih
    (entries : List (ValidNode × ValidNode))
    (pairs : List (YamlValue × YamlValue))
    (hlen : entries.length = pairs.length)
    (ihk : ∀ i (hi : i < entries.length),
      (pairs.get ⟨i, by omega⟩).1 = toYamlValue (entries.get ⟨i, hi⟩).1)
    (ihv : ∀ i (hi : i < entries.length),
      (pairs.get ⟨i, by omega⟩).2 = toYamlValue (entries.get ⟨i, hi⟩).2) :
    pairs = entries.map fun ⟨k, v⟩ => (toYamlValue k, toYamlValue v) := by
  apply List.ext_get (by simp [hlen])
  intro i hi₁ hi₂
  simp only [List.get_eq_getElem, List.getElem_map]
  exact Prod.ext (ihk i (by omega)) (ihv i (by omega))

/--
Reverse direction: `NodeToValue n v` implies `v = toYamlValue n`.
-/
theorem nodeToValue_implies_toYamlValue {n : ValidNode} {v : YamlValue}
    (h : NodeToValue n v) : v = toYamlValue n := by
  induction h with
  | plainScalarBlock _ _ _ _ _ => rfl
  | plainScalarFlow _ _ _ _ _ _ => rfl
  | singleQuoted _ => rfl
  | doubleQuoted _ => rfl
  | literalScalar _ _ _ => rfl
  | foldedScalar _ _ _ => rfl
  | blockSeq indent nodes vals hlen hcorr ih =>
    simp [toYamlValue, toYamlValueList_eq_map]
    exact vals_eq_map_of_ih nodes vals hlen ih
  | blockMap indent entries pairs hlen hkeys hvals ihk ihv =>
    simp [toYamlValue, toYamlValuePairs_eq_map]
    exact pairs_eq_map_of_ih entries pairs hlen ihk ihv
  | flowSeq nodes vals hlen hcorr ih =>
    simp [toYamlValue, toYamlValueList_eq_map]
    exact vals_eq_map_of_ih nodes vals hlen ih
  | flowMap entries pairs hlen hkeys hvals ihk ihv =>
    simp [toYamlValue, toYamlValuePairs_eq_map]
    exact pairs_eq_map_of_ih entries pairs hlen ihk ihv

/--
**Specification function correctness**: `toYamlValue n = v` if and only
if `NodeToValue n v`.

This is the key lemma connecting the computable function to the
inductive relation.
-/
theorem toYamlValue_correct (n : ValidNode) (v : YamlValue) :
    toYamlValue n = v ↔ NodeToValue n v := by
  constructor
  · intro h; rw [← h]; exact toYamlValue_nodeToValue n
  · intro h; exact (nodeToValue_implies_toYamlValue h).symm

/-! ## §2  Totality & Determinism

`NodeToValue` is a **total function** from `ValidNode` to `YamlValue`:
every grammar node has a corresponding value, and that value is unique.
-/

/--
**Totality**: every `ValidNode` has a corresponding `YamlValue`.
-/
theorem nodeToValue_total (n : ValidNode) :
    ∃ v, NodeToValue n v :=
  ⟨toYamlValue n, toYamlValue_nodeToValue n⟩

/--
**Determinism**: `NodeToValue` maps each node to exactly one value.
-/
theorem nodeToValue_deterministic {n : ValidNode} {v₁ v₂ : YamlValue}
    (h₁ : NodeToValue n v₁) (h₂ : NodeToValue n v₂) : v₁ = v₂ := by
  rw [nodeToValue_implies_toYamlValue h₁, nodeToValue_implies_toYamlValue h₂]

/-! ## §3  Scalar Soundness

Each scalar `ValidNode` constructor produces the correct `ScalarStyle`
in its corresponding `YamlValue`. These are the per-parser soundness
lemmas: they guarantee the parser cannot mis-label scalar styles.
-/

/-- Plain scalars (block context) produce `.plain` style. -/
theorem plainScalar_block_style_sound (content : String) (h : content.length > 0)
    (hfirst : validPlainFirst content)
    (hnoCS : noColonSpace content) (hnoSH : noSpaceHash content) :
    ∃ s, toYamlValue (.plainScalarBlock content h hfirst hnoCS hnoSH) = .scalar s ∧ s.style = .plain := by
  exact ⟨⟨content, .plain, none, none, none⟩, rfl, rfl⟩

/-- Plain scalars (flow context) produce `.plain` style. -/
theorem plainScalar_flow_style_sound (content : String) (h : content.length > 0)
    (hfirst : validPlainFirst content)
    (hnoCS : noColonSpace content) (hnoSH : noSpaceHash content)
    (hnoFlow : noFlowIndicators content) :
    ∃ s, toYamlValue (.plainScalarFlow content h hfirst hnoCS hnoSH hnoFlow) = .scalar s ∧ s.style = .plain := by
  exact ⟨⟨content, .plain, none, none, none⟩, rfl, rfl⟩

/-- Single-quoted scalars produce `.singleQuoted` style. -/
theorem singleQuoted_style_sound (content : String) :
    ∃ s, toYamlValue (.singleQuoted content) = .scalar s ∧ s.style = .singleQuoted := by
  exact ⟨⟨content, .singleQuoted, none, none, none⟩, rfl, rfl⟩

/-- Double-quoted scalars produce `.doubleQuoted` style. -/
theorem doubleQuoted_style_sound (content : String) :
    ∃ s, toYamlValue (.doubleQuoted content) = .scalar s ∧ s.style = .doubleQuoted := by
  exact ⟨⟨content, .doubleQuoted, none, none, none⟩, rfl, rfl⟩

/-- Literal block scalars produce `.literal` style. -/
theorem literal_style_sound (content : String) (indent : Nat) (chomp : ChompStyle) :
    ∃ s, toYamlValue (.literalScalar content indent chomp) = .scalar s
    ∧ s.style = .literal := by
  exact ⟨⟨content, .literal, none, none, some ⟨chomp, some indent⟩⟩, rfl, rfl⟩

/-- Folded block scalars produce `.folded` style. -/
theorem folded_style_sound (content : String) (indent : Nat) (chomp : ChompStyle) :
    ∃ s, toYamlValue (.foldedScalar content indent chomp) = .scalar s
    ∧ s.style = .folded := by
  exact ⟨⟨content, .folded, none, none, some ⟨chomp, some indent⟩⟩, rfl, rfl⟩

/--
**Scalar content preservation**: the content string in a scalar `ValidNode`
is exactly the content string in the corresponding `YamlValue.scalar`.

This guarantees the parser does not silently alter scalar content during
the grammar→value correspondence.
-/
theorem scalar_content_preserved (n : ValidNode) (v : YamlValue)
    (h : NodeToValue n v) :
    (∀ c hne hf hcs hsh, n = .plainScalarBlock c hne hf hcs hsh → ∃ s, v = .scalar s ∧ s.content = c) ∧
    (∀ c hne hf hcs hsh hfl, n = .plainScalarFlow c hne hf hcs hsh hfl → ∃ s, v = .scalar s ∧ s.content = c) ∧
    (∀ c, n = .singleQuoted c → ∃ s, v = .scalar s ∧ s.content = c) ∧
    (∀ c, n = .doubleQuoted c → ∃ s, v = .scalar s ∧ s.content = c) ∧
    (∀ c i ch, n = .literalScalar c i ch → ∃ s, v = .scalar s ∧ s.content = c) ∧
    (∀ c i ch, n = .foldedScalar c i ch → ∃ s, v = .scalar s ∧ s.content = c) := by
  have hv := nodeToValue_implies_toYamlValue h
  subst hv
  exact ⟨
    fun c hne _ _ _ heq => by subst heq; exact ⟨_, rfl, rfl⟩,
    fun c hne _ _ _ _ heq => by subst heq; exact ⟨_, rfl, rfl⟩,
    fun c heq => by subst heq; exact ⟨_, rfl, rfl⟩,
    fun c heq => by subst heq; exact ⟨_, rfl, rfl⟩,
    fun c i ch heq => by subst heq; exact ⟨_, rfl, rfl⟩,
    fun c i ch heq => by subst heq; exact ⟨_, rfl, rfl⟩⟩

/-! ## §4  Collection Soundness

Collection `ValidNode` constructors produce the correct `CollectionStyle`
and preserve element/entry counts.
-/

/-- Block sequences produce `.block` collection style. -/
theorem blockSeq_style_sound (indent : Nat) (items : List ValidNode) :
    ∃ style arr, toYamlValue (.blockSeq indent items) = .sequence style arr none
    ∧ style = .block := by
  exact ⟨.block, _, rfl, rfl⟩

/-- Flow sequences produce `.flow` collection style. -/
theorem flowSeq_style_sound (items : List ValidNode) :
    ∃ style arr, toYamlValue (.flowSeq items) = .sequence style arr none
    ∧ style = .flow := by
  exact ⟨.flow, _, rfl, rfl⟩

/-- Block mappings produce `.block` collection style. -/
theorem blockMap_style_sound (indent : Nat) (entries : List (ValidNode × ValidNode)) :
    ∃ style arr, toYamlValue (.blockMap indent entries) = .mapping style arr none
    ∧ style = .block := by
  exact ⟨.block, _, rfl, rfl⟩

/-- Flow mappings produce `.flow` collection style. -/
theorem flowMap_style_sound (entries : List (ValidNode × ValidNode)) :
    ∃ style arr, toYamlValue (.flowMap entries) = .mapping style arr none
    ∧ style = .flow := by
  exact ⟨.flow, _, rfl, rfl⟩

/--
**Sequence item count preservation**: the number of items in a `ValidNode`
sequence matches the number of items in the resulting `YamlValue.sequence`.
-/
theorem seq_items_count_preserved (items : List ValidNode) :
    (toYamlValue.toYamlValueList items).length = items.length := by
  rw [toYamlValueList_eq_map]; simp

/--
**Mapping entry count preservation**: the number of entries in a `ValidNode`
mapping matches the number in the resulting `YamlValue.mapping`.
-/
theorem map_entries_count_preserved (entries : List (ValidNode × ValidNode)) :
    (toYamlValue.toYamlValuePairs entries).length = entries.length := by
  rw [toYamlValuePairs_eq_map]; simp

/-! ## §5  Structural Composition

These theorems show that the specification types compose correctly:
any `ValidNode` can be lifted to a `ValidYaml`, and the `ValidYaml`
value field is exactly `toYamlValue`.
-/

/--
**ValidYaml construction**: given any `ValidNode`, we can construct
a `ValidYaml` bundling the node with its canonical value.
-/
theorem validYaml_construct (input : String) (n : ValidNode) :
    ∃ vy : ValidYaml, vy.input = input ∧ vy.grammar = n
    ∧ vy.value = toYamlValue n := by
  exact ⟨{
    input := input
    value := toYamlValue n
    grammar := n
    corresponds := toYamlValue_nodeToValue n
  }, rfl, rfl, rfl⟩

/--
**Value determination**: the `YamlValue` in a `ValidYaml` is uniquely
determined by its `ValidNode` — it must be `toYamlValue grammar`.
-/
theorem validYaml_value_eq_toYamlValue (vy : ValidYaml) :
    vy.value = toYamlValue vy.grammar :=
  nodeToValue_implies_toYamlValue vy.corresponds

/--
**Scalar ValidYaml is a scalar YamlValue**: if a `ValidYaml`'s grammar
is any scalar constructor, the value is a `YamlValue.scalar`.
-/
theorem validYaml_scalar_is_scalar (vy : ValidYaml) :
    (∃ c h hf hcs hsh, vy.grammar = .plainScalarBlock c h hf hcs hsh) ∨
    (∃ c h hf hcs hsh hfl, vy.grammar = .plainScalarFlow c h hf hcs hsh hfl) ∨
    (∃ c, vy.grammar = .singleQuoted c) ∨
    (∃ c, vy.grammar = .doubleQuoted c) ∨
    (∃ c i ch, vy.grammar = .literalScalar c i ch) ∨
    (∃ c i ch, vy.grammar = .foldedScalar c i ch) →
    ∃ s, vy.value = .scalar s := by
  intro h
  rw [validYaml_value_eq_toYamlValue]
  rcases h with ⟨c, h, _, _, _, heq⟩ | ⟨c, h, _, _, _, _, heq⟩ | ⟨c, heq⟩ | ⟨c, heq⟩ | ⟨c, i, ch, heq⟩ | ⟨c, i, ch, heq⟩ <;>
  rw [heq] <;> exact ⟨_, rfl⟩

/--
**Collection ValidYaml is a collection YamlValue**: if a `ValidYaml`'s grammar
is any collection constructor, the value is a sequence or mapping.
-/
theorem validYaml_collection_kind (vy : ValidYaml) :
    (∃ n items, vy.grammar = .blockSeq n items) ∨
    (∃ items, vy.grammar = .flowSeq items) →
    ∃ style arr tag, vy.value = .sequence style arr tag := by
  intro h
  rw [validYaml_value_eq_toYamlValue]
  rcases h with ⟨n, items, heq⟩ | ⟨items, heq⟩ <;>
  rw [heq] <;> exact ⟨_, _, _, rfl⟩

end Lean4Yaml.Proofs.Soundness
