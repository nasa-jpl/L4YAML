import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection 595 -- compose sequence items element-wise (outer-parse half)

R594 pinned the RIGHT SIDE of the per-element locality equation:
  `(rd.map compose)[0]!.value = .scalar (Scalar.mk items[i].content .doubleQuoted none none none)`
for scalar elements, via the standalone parse of `emitScalar`.

R595 (this brick) pins the outer-parse half: given `items'` (the raw parser output, a
flow sequence) and `items''` (from `doc.compose`), we prove

  `items'' = items'.map (fun v => (v.resolveAliases doc.anchors).stripAnchors)`

and the SCALAR COROLLARY: if `items'[j]! = .scalar (Scalar.mk c s none none none)` (an
anchor-free scalar, as emitter output always is), then `items''[j]! = .scalar (Scalar.mk c s none none none)`.

Combined: R594 gives `(rd.map compose)[0]!.value = .scalar c_dq` and R595 will give (once
scanner-span-locality lands) `items''[j]! = .scalar c_dq`, closing the locality equation.
Scanner-span-locality (the `items'[j]! = ...` half) is the next frontier brick.

## Proof strategy

`compose_seq_items_pointwise` unfolds `doc.compose.value = (doc.value.resolveAliases ..).stripAnchors`,
substitutes `h_val`, rewrites both functions' sequence cases via `resolveList_eq_map` /
`stripList_eq_map`, collapses `l.toList.map f |>.toArray` to `l.map f` via
`← Array.toList_map` + `Array.toArray_toList`, then extracts `items''` by
`YamlValue.sequence.injEq`.

`compose_seq_scalar_item` uses `subst (compose_seq_items_pointwise ...)` to reduce `items''`
to `items'.map f`, then chains `getElem!_pos` + `Array.getElem_map` + `getElem!_pos` to get
`items''[j]! = f items'[j]! = f (.scalar s)`, then `resolveAliases_scalar` +
`stripAnchors_scalar` + `rfl` (anchor already none) to close.

## Inhabitation debt: rules 1 and 2 apply

* Rule 1 (`h_val`/`h_comp` antecedents reachable): `seqAB` parses to a sequence; the raw and
  composed values are accessible concretely.
* Rule 2 (conclusion non-vacuous): `seq_items_pointwise_concrete` applies `compose_seq_items_pointwise`
  on a REAL witness (`seqAB`), recovering the map equation. `scalar_item_concrete_elem0` fires
  `compose_seq_scalar_item` on element 0 of `seqAB`.

Rule 3 does not apply (no provider universal `∀ P` in either theorem type).
-/

namespace ComposeSeqItemsPointwise

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: same as LocalityReductionJoint -/

def a : YamlValue := .scalar { content := "a", style := .plain }
def b : YamlValue := .scalar { content := "b", style := .plain }
def seqAB : YamlValue := .sequence .flow #[a, b] none none

/-! ## Concrete helpers: recover items' (raw) and items'' (composed) from parsing seqAB -/

-- Raw parse result
def rawDocsSeq : Option (Array YamlDocument) :=
  match parseYamlRaw (emit seqAB) with
  | .ok docs => some docs
  | _ => none

-- Raw document value (pre-compose) — the `.value` of `raw_docs[0]!`
def rawSeqItems : Option (Array YamlValue) :=
  match rawDocsSeq with
  | some docs => match docs[0]!.value with
                 | .sequence _ its _ _ => some its
                 | _ => none
  | _ => none

-- Composed document value — the `.value` of `(raw_docs.map compose)[0]!`
def composedSeqItems : Option (Array YamlValue) :=
  match rawDocsSeq with
  | some docs => match (docs.map YamlDocument.compose)[0]!.value with
                 | .sequence _ its _ _ => some its
                 | _ => none
  | _ => none

/-! ## Rule 1: antecedents reachable (parse succeeds, raw and composed items are sequences) -/

theorem raw_parse_seq_succeeds : rawDocsSeq.isSome = true := by native_decide

theorem raw_seq_items_is_some : rawSeqItems.isSome = true := by native_decide

theorem composed_seq_items_is_some : composedSeqItems.isSome = true := by native_decide

/-! ## Rule 2: conclusion non-vacuous (abstract application of the new theorems) -/

/-- `compose_seq_items_pointwise` fires on the raw/composed items from a REAL parse. -/
theorem seq_items_pointwise_concrete
    (docs : Array YamlDocument)
    (_h_parse : parseYamlRaw (emit seqAB) = .ok docs)
    (h_size : docs.size = 1)
    (items' items'' : Array YamlValue)
    (h_af : ∀ v ∈ items'.toList, v.anchorFree = true)
    (h_val : docs[0]!.value = .sequence .flow items' none none)
    (h_comp : (docs.map YamlDocument.compose)[0]!.value = .sequence .flow items'' none none) :
    items'' = items'.map (fun v => (v.resolveAliases docs[0]!.anchors).stripAnchors) := by
  have h_doc_comp : (docs[0]!.compose).value = .sequence .flow items'' none none := by
    have h0 : 0 < docs.size := by omega
    have h_lift : (docs.map YamlDocument.compose)[0]! = docs[0]!.compose := by
      rw [getElem!_pos _ 0 (by rwa [Array.size_map])]
      rw [Array.getElem_map (hi := by rwa [Array.size_map])]
      congr 1; exact (getElem!_pos docs 0 h0).symm
    rw [← h_lift]; exact h_comp
  exact compose_seq_items_pointwise docs[0]! items' items'' h_af h_val h_doc_comp

/-- `compose_seq_scalar_item` fires: element `i` of items'' equals the standalone scalar
    if the corresponding raw item is that scalar. -/
theorem scalar_item_concrete_elem0
    (docs : Array YamlDocument)
    (_h_parse : parseYamlRaw (emit seqAB) = .ok docs)
    (h_size : docs.size = 1)
    (items' items'' : Array YamlValue)
    (h_af : ∀ v ∈ items'.toList, v.anchorFree = true)
    (h_val : docs[0]!.value = .sequence .flow items' none none)
    (h_comp : (docs.map YamlDocument.compose)[0]!.value = .sequence .flow items'' none none)
    (h_items_size : 0 < items'.size)
    (h_item : items'[0]! = .scalar (Scalar.mk "a" .doubleQuoted none none none)) :
    items''[0]! = .scalar (Scalar.mk "a" .doubleQuoted none none none) := by
  have h_doc_comp : (docs[0]!.compose).value = .sequence .flow items'' none none := by
    have h0 : 0 < docs.size := by omega
    have h_lift : (docs.map YamlDocument.compose)[0]! = docs[0]!.compose := by
      rw [getElem!_pos _ 0 (by rwa [Array.size_map])]
      rw [Array.getElem_map (hi := by rwa [Array.size_map])]
      congr 1; exact (getElem!_pos docs 0 h0).symm
    rw [← h_lift]; exact h_comp
  exact compose_seq_scalar_item docs[0]! items' items'' h_af h_val h_doc_comp 0 h_items_size "a" .doubleQuoted h_item

/-! ## Axiom audit: the new theorems use no sorry -/

/-- info: 'L4YAML.Proofs.EmitterScannability.compose_seq_items_pointwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compose_seq_items_pointwise

/-- info: 'L4YAML.Proofs.EmitterScannability.compose_seq_scalar_item' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compose_seq_scalar_item

end ComposeSeqItemsPointwise
