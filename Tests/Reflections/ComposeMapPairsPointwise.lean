import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection 604 -- compose mapping pairs element-wise (outer-parse half, R604)

`compose_map_pairs_pointwise` (§5.18) characterizes what `YamlDocument.compose` does
element-wise when the document value is a flow mapping:

  `theorem compose_map_pairs_pointwise`
  `    (doc : YamlDocument) (pairs' pairs'' : Array (YamlValue × YamlValue))`
  `    (h_val : doc.value = .mapping .flow pairs' none none)`
  `    (h_comp : (doc.compose).value = .mapping .flow pairs'' none none) :`
  `    pairs'' = pairs'.map (fun ⟨k, v⟩ =>`
  `      ((k.resolveAliases doc.anchors).stripAnchors,`
  `       (v.resolveAliases doc.anchors).stripAnchors))`

`compose_map_scalar_pair` (§5.18 corollary) gives the scalar case: if key/value in
`pairs'[j]!` are both anchor-free scalars, they survive compose unchanged.

These are the MAPPING ANALOGS of `compose_seq_items_pointwise` / `compose_seq_scalar_item`
(§5.17, R595).  They are verified-but-unconsumed: once scanner-span-locality for mapping
pairs lands (`pairs'[j]! = (.scalar sk, .scalar sv)`), `compose_map_scalar_pair` will close
the per-pair locality equation `(rd.map compose)[0]!.value = (pairs''[j]!).fst/snd`, filling
the mapping locality sorry at `emit_roundtrip_mapping_content_eq`
(`EmitterScannability.lean:1147`).

## Proof strategy

`compose_map_pairs_pointwise` mirrors `compose_seq_items_pointwise` exactly, using
`resolvePairs_eq_map` / `stripPairs_eq_map` instead of `resolveList_eq_map` /
`stripList_eq_map`, and `YamlValue.mapping.injEq` to extract `pairs''`.

`compose_map_scalar_pair` uses `subst (compose_map_pairs_pointwise ...)` to reduce `pairs''`
to `pairs'.map f`, then chains `getElem!_pos` + `Array.getElem_map` + `getElem!_pos` to get
`pairs''[j]! = f pairs'[j]! = f (.scalar sk, .scalar sv)`, then `resolveAliases_scalar` +
unfolding `stripAnchors` to close (`anchor = none` means `{ s with anchor := none } = s`).

## Inhabitation debt: rules 1 and 2 apply

* Rule 1 (`h_val`/`h_comp` antecedents reachable): `mapKV` parses to a mapping; the raw and
  composed values are accessible concretely.
* Rule 2 (conclusion non-vacuous): `map_pairs_pointwise_concrete` applies
  `compose_map_pairs_pointwise` on a REAL witness (`mapKV`), recovering the map equation.
  `scalar_pair_concrete_elem0` fires `compose_map_scalar_pair` on pair 0 of `mapKV`.

Rule 3 does not apply (no provider universal `∀ P` in either theorem type).
-/

namespace ComposeMapPairsPointwise

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures -/

def k : YamlValue := .scalar { content := "k", style := .plain }
def v : YamlValue := .scalar { content := "v", style := .plain }
def mapKV : YamlValue := .mapping .flow #[(k, v)] none none

/-! ## Concrete helpers: recover pairs' (raw) and pairs'' (composed) from parsing mapKV -/

def rawDocsMap : Option (Array YamlDocument) :=
  match parseYamlRaw (emit mapKV) with
  | .ok docs => some docs
  | _ => none

def rawMapPairs : Option (Array (YamlValue × YamlValue)) :=
  match rawDocsMap with
  | some docs => match docs[0]!.value with
                 | .mapping _ ps _ _ => some ps
                 | _ => none
  | _ => none

def composedMapPairs : Option (Array (YamlValue × YamlValue)) :=
  match rawDocsMap with
  | some docs => match (docs.map YamlDocument.compose)[0]!.value with
                 | .mapping _ ps _ _ => some ps
                 | _ => none
  | _ => none

/-! ## Rule 1: antecedents reachable (parse succeeds, raw and composed pairs are mappings) -/

theorem raw_parse_map_succeeds : rawDocsMap.isSome = true := by native_decide

theorem raw_map_pairs_is_some : rawMapPairs.isSome = true := by native_decide

theorem composed_map_pairs_is_some : composedMapPairs.isSome = true := by native_decide

/-! ## Rule 2: conclusion non-vacuous (abstract application of the new theorems) -/

/-- `compose_map_pairs_pointwise` fires on the raw/composed pairs from a REAL parse. -/
theorem map_pairs_pointwise_concrete
    (docs : Array YamlDocument)
    (_h_parse : parseYamlRaw (emit mapKV) = .ok docs)
    (h_size : docs.size = 1)
    (pairs' pairs'' : Array (YamlValue × YamlValue))
    (h_val : docs[0]!.value = .mapping .flow pairs' none none)
    (h_comp : (docs.map YamlDocument.compose)[0]!.value = .mapping .flow pairs'' none none) :
    pairs'' = pairs'.map (fun ⟨kv, vv⟩ => ((kv.resolveAliases docs[0]!.anchors).stripAnchors,
                                             (vv.resolveAliases docs[0]!.anchors).stripAnchors)) := by
  have h_doc_comp : (docs[0]!.compose).value = .mapping .flow pairs'' none none := by
    have h0 : 0 < docs.size := by omega
    have h_lift : (docs.map YamlDocument.compose)[0]! = docs[0]!.compose := by
      rw [getElem!_pos _ 0 (by rwa [Array.size_map])]
      rw [Array.getElem_map (hi := by rwa [Array.size_map])]
      congr 1; exact (getElem!_pos docs 0 h0).symm
    rw [← h_lift]; exact h_comp
  exact compose_map_pairs_pointwise docs[0]! pairs' pairs'' h_val h_doc_comp

/-- `compose_map_scalar_pair` fires: pair 0 of pairs'' equals the standalone scalar pair
    if the corresponding raw pair 0 is that scalar pair. -/
theorem scalar_pair_concrete_elem0
    (docs : Array YamlDocument)
    (_h_parse : parseYamlRaw (emit mapKV) = .ok docs)
    (h_size : docs.size = 1)
    (pairs' pairs'' : Array (YamlValue × YamlValue))
    (h_val : docs[0]!.value = .mapping .flow pairs' none none)
    (h_comp : (docs.map YamlDocument.compose)[0]!.value = .mapping .flow pairs'' none none)
    (h_pairs_size : 0 < pairs'.size)
    (h_pair : pairs'[0]! = (.scalar (Scalar.mk "k" .doubleQuoted none none none),
                             .scalar (Scalar.mk "v" .doubleQuoted none none none))) :
    pairs''[0]! = (.scalar (Scalar.mk "k" .doubleQuoted none none none),
                   .scalar (Scalar.mk "v" .doubleQuoted none none none)) := by
  have h_doc_comp : (docs[0]!.compose).value = .mapping .flow pairs'' none none := by
    have h0 : 0 < docs.size := by omega
    have h_lift : (docs.map YamlDocument.compose)[0]! = docs[0]!.compose := by
      rw [getElem!_pos _ 0 (by rwa [Array.size_map])]
      rw [Array.getElem_map (hi := by rwa [Array.size_map])]
      congr 1; exact (getElem!_pos docs 0 h0).symm
    rw [← h_lift]; exact h_comp
  exact compose_map_scalar_pair docs[0]! pairs' pairs'' h_val h_doc_comp 0 h_pairs_size
      "k" "v" .doubleQuoted .doubleQuoted h_pair

/-! ## Axiom audit: the new theorems use no sorry -/

/-- info: 'L4YAML.Proofs.EmitterScannability.compose_map_pairs_pointwise' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compose_map_pairs_pointwise

/-- info: 'L4YAML.Proofs.EmitterScannability.compose_map_scalar_pair' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compose_map_scalar_pair

end ComposeMapPairsPointwise
