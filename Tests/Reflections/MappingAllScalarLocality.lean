import L4YAML.Proofs.Output.EmitterScannability
import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Proofs.Output.EmitterScannability.ScannerSpanLocality

/-!
# Reflection -- mapping all-scalar locality branch in emit_roundtrip_mapping_content_eq

The sorry at `EmitterScannability.lean:1147` (inside `emit_roundtrip_mapping_content_eq`)
is resolved for all-scalar flow mappings by chaining R605 → R607 → R608 → compose:

```
parseStream_flowMapStart_loop_witness      (R605: exposes parseFlowMappingLoop at pos=2)
  → scanFiltered_emitMap_allScalar_pair_at (R607: token layout from the scanner)
  → parseFlowMappingLoop_allScalar_pair_at (R608: pins pairs'[j]! per pair)
  → compose_map_scalar_pair                (R604 corollary: pairs''[j]! from pairs'[j]!)
  → parseYamlRaw_emitScalar_compose_value  (scalar leaf: standalone re-parse value)
```

Token layout for pairs.length = n: streamStart fmStart [key sk value sv ...]* fmEnd streamEnd
(`tokens.size = 5n+3`).

## Inhabitation-debt check

* **Rule 1** (antecedents reachable): `mapAX_all_scalar` shows the `h_all_sc` branch is
  reached for any concrete 1-pair all-scalar mapping.  `map_locality_size` + `map_loc_key0` +
  `map_loc_val0` ground the locality conclusion TRUE on real emission.

* **Rule 2** (conclusion non-vacuous): `mapping_roundtrip_native` fires `contentEq` for a
  concrete 1-pair all-scalar mapping via `native_decide`; `mapping_all_scalar_locality_chain`
  shows the abstract size + locality pair for a concrete scanner scan.

* Rule 3 does not apply (no provider universal in the filled branch).
-/

namespace MappingAllScalarLocality

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures -/

def sk_a : Scalar := { content := "a", style := .plain }
def sv_x : Scalar := { content := "x", style := .plain }
def mapAX : YamlValue := .mapping .flow #[(.scalar sk_a, .scalar sv_x)] none none

/-! ## Concrete helpers: recover pairs'' from whole-structure parse, and standalone values. -/

def parsedMapAXPairs : Option (Array (YamlValue × YamlValue)) :=
  match parseYamlRaw (emit mapAX) with
  | .ok docs => match (docs.map YamlDocument.compose)[0]!.value with
               | .mapping _ ps _ _ => some ps
               | _ => none
  | _ => none

def parsedStandalone (v : YamlValue) : Option YamlValue :=
  match parseYamlRaw (emit v) with
  | .ok docs => some (docs.map YamlDocument.compose)[0]!.value
  | _ => none

/-! ## Rule 1: antecedents reachable — all-scalar by_cases branch is reached -/

/-- Any 1-pair all-scalar mapping satisfies `h_all_sc`, routing to the now-proven branch. -/
theorem mapAX_all_scalar :
    ∀ p ∈ (#[(.scalar sk_a, .scalar sv_x)] : Array (YamlValue × YamlValue)).toList,
    ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv := by
  intro p hp
  have h_toList : (#[(.scalar sk_a, .scalar sv_x)] :
      Array (YamlValue × YamlValue)).toList = [(.scalar sk_a, .scalar sv_x)] := rfl
  rw [h_toList, List.mem_singleton] at hp
  subst hp
  exact ⟨sk_a, sv_x, rfl, rfl⟩

/-! ## Rule 1 (continued): THE INHABITATION PROBE — locality conjunction TRUE on real emission.

`pairs''[j]!.fst/snd` from the whole-structure parse equals `parsedStandalone` of the
corresponding key/value — i.e. `(rd.map compose)[0]!.value = pairs''[j]!.fst/snd` holds
on real data.  Same grounding as `LocalityReductionJoint` but for the mapping axis. -/

theorem map_locality_size : parsedMapAXPairs.map (·.size) = some 1 := by native_decide

theorem map_loc_key0 :
    (parsedMapAXPairs.map (fun ps => ps[0]!.fst) == parsedStandalone (.scalar sk_a)) = true := by
  native_decide

theorem map_loc_val0 :
    (parsedMapAXPairs.map (fun ps => ps[0]!.snd) == parsedStandalone (.scalar sv_x)) = true := by
  native_decide

/-! ## Rule 2: conclusion non-vacuous -/

/-- Parsing the emission of `{a:x}` succeeds and is content-equivalent. -/
theorem mapping_roundtrip_native :
    (match parseYaml (emit mapAX) with
     | .ok docs => docs.size == 1 && contentEq mapAX docs[0]!.value
     | .error _ => false) = true := by
  native_decide

/-- Abstract: for a 1-pair all-scalar mapping, the size + locality conjunction holds.

Chains R607 → R608 → compose_map_scalar_pair to pin `pairs''[0]!`, then applies
`parseYamlRaw_emitScalar_compose_value` to close each locality equation. -/
theorem mapping_all_scalar_locality_chain
    (sk sv : Scalar)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered
        ("{" ++ emit.emitPairList [(.scalar sk, .scalar sv)] ++ "}") = .ok tokens)
    (raw_docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok raw_docs)
    (h_sz : raw_docs.size = 1)
    (pairs'' : Array (YamlValue × YamlValue))
    (h_shape : (raw_docs.map YamlDocument.compose)[0]!.value = .mapping .flow pairs'' none none) :
    pairs''.size = 1 ∧
    (∀ rd : Array YamlDocument,
      parseYamlRaw (emit (.scalar sk)) = .ok rd → rd.size = 1 →
      (rd.map YamlDocument.compose)[0]!.value = pairs''[0]!.fst) ∧
    (∀ rd : Array YamlDocument,
      parseYamlRaw (emit (.scalar sv)) = .ok rd → rd.size = 1 →
      (rd.map YamlDocument.compose)[0]!.value = pairs''[0]!.snd) := by
  -- Step 1: all-scalar predicate for the 1-pair list
  have h_ne_list : ([(.scalar sk, .scalar sv)] : List (YamlValue × YamlValue)) ≠ [] :=
    List.cons_ne_nil _ _
  have h_all_sc : ∀ p ∈ ([(.scalar sk, .scalar sv)] : List (YamlValue × YamlValue)),
      ∃ sk' sv' : Scalar, p.1 = .scalar sk' ∧ p.2 = .scalar sv' := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl; exact ⟨sk, sv, rfl, rfl⟩
  -- Step 2: R607 token facts
  obtain ⟨h_tok_sz, h_t1, h_scalar_tok, _h_fe_tok, h_fme_tok, h_key_tok, h_mv_tok⟩ :=
    scanFiltered_emitMap_allScalar_pair_at [(.scalar sk, .scalar sv)] h_ne_list h_all_sc
      tokens h_scan
  -- Step 3: R605 loop witness
  obtain ⟨pairs', ps_loop, ps_doc, h_pd_tok, h_pd_pos, h_loop_ok, h_raw_val⟩ :=
    parseStream_flowMapStart_loop_witness tokens raw_docs h_parse (by omega) (by omega) h_t1
  -- Step 4: R608 pins pairs'[0]!
  have h_fuel : 1 + 1 ≤ 4 * tokens.size + 2 := by rw [h_tok_sz]; omega
  obtain ⟨h_pairs'_sz, h_pairs'_vals⟩ :=
    parseFlowMappingLoop_allScalar_pair_at h_ne_list h_all_sc
      (fun j hj => h_key_tok j hj)
      (fun j hj sk' sv' hp => h_scalar_tok j hj sk' sv' hp)
      (fun j hj => h_mv_tok j hj)
      (fun j hpos hlt => by
        simp only [List.length_cons, List.length_nil] at hlt
        exact absurd hpos (by omega))
      h_fme_tok h_tok_sz h_pd_tok h_pd_pos h_fuel h_loop_ok
  obtain ⟨sk0, sv0, h_pair0_opt, h_pair0_pin⟩ := h_pairs'_vals 0 (by simp)
  -- Bridge: h_pair0_opt says [(.scalar sk, .scalar sv)][0]? = some (.scalar sk0, .scalar sv0)
  -- The concrete list head gives [0]? = some (.scalar sk, .scalar sv), so sk0 = sk, sv0 = sv
  have h_opt0_val : ([(.scalar sk, .scalar sv)] : List (YamlValue × YamlValue))[0]? =
      some (.scalar sk, .scalar sv) := rfl
  rw [h_opt0_val] at h_pair0_opt
  simp only [Option.some.injEq, Prod.mk.injEq, YamlValue.scalar.injEq] at h_pair0_opt
  -- h_pair0_opt : sk = sk0 ∧ sv = sv0
  rw [← h_pair0_opt.1, ← h_pair0_opt.2] at h_pair0_pin
  -- h_pair0_pin : pairs'[0]! = (.scalar sk.content .dq ..., .scalar sv.content .dq ...)
  -- Step 5: compose bridge for pairs''[0]!
  have h_ne_raw : 0 < raw_docs.size := by omega
  have h_0' : 0 < (raw_docs.map YamlDocument.compose).size := by rw [Array.size_map]; exact h_ne_raw
  have h_comp_val : (raw_docs[0]!.compose).value = .mapping .flow pairs'' none none := by
    have h_eq : (raw_docs.map YamlDocument.compose)[0]!.value = (raw_docs[0]!.compose).value := by
      rw [getElem!_pos _ 0 h_0', getElem!_pos raw_docs 0 h_ne_raw, Array.getElem_map]
    rw [← h_eq]; exact h_shape
  have h_pairs'_size : pairs'.size = 1 := by rw [h_pairs'_sz]; rfl
  -- the single pinned pair is an anchorless scalar pair, so pairs' is anchor-free (J2 guard)
  have h_af : ∀ p ∈ pairs'.toList, p.1.anchorFree = true ∧ p.2.anchorFree = true := by
    intro q hq
    obtain ⟨i, hi, h_eq⟩ := List.getElem_of_mem hq
    have hi'' : i < pairs'.size := by rwa [Array.length_toList] at hi
    have h_i0 : i = 0 := by omega
    subst h_i0
    have h_q : q = pairs'[0]! := by
      rw [← h_eq, Array.getElem_toList, getElem!_pos pairs' 0 hi'']
    rw [h_q, h_pair0_pin]
    exact ⟨by simp [YamlValue.anchorFree], by simp [YamlValue.anchorFree]⟩
  have h_pairs''_size : pairs''.size = 1 := by
    rw [compose_map_pairs_pointwise (raw_docs[0]!) pairs' pairs'' h_af h_raw_val h_comp_val,
        Array.size_map, h_pairs'_size]
  have h_pairs'_0 : 0 < pairs'.size := by omega
  have h_pairs''_0 : pairs''[0]! =
      (.scalar (Scalar.mk sk.content .doubleQuoted none none none),
       .scalar (Scalar.mk sv.content .doubleQuoted none none none)) :=
    compose_map_scalar_pair (raw_docs[0]!) pairs' pairs'' h_af h_raw_val h_comp_val
      0 h_pairs'_0 sk.content sv.content .doubleQuoted .doubleQuoted h_pair0_pin
  -- Step 6: locality equations from parseYamlRaw_emitScalar_compose_value
  exact ⟨h_pairs''_size,
    fun rd h_rd h_rd_sz =>
      (parseYamlRaw_emitScalar_compose_value sk.content rd
        ((show emitScalar sk.content = emit (.scalar sk) from rfl) ▸ h_rd) h_rd_sz).trans
      (congrArg Prod.fst h_pairs''_0).symm,
    fun rd h_rd h_rd_sz =>
      (parseYamlRaw_emitScalar_compose_value sv.content rd
        ((show emitScalar sv.content = emit (.scalar sv) from rfl) ▸ h_rd) h_rd_sz).trans
      (congrArg Prod.snd h_pairs''_0).symm⟩

/-! ## Axiom audit: the new sub-chain is sorry-free -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowMappingLoop_allScalar_pair_at' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowMappingLoop_allScalar_pair_at

/-- info: 'L4YAML.Proofs.EmitterScannability.compose_map_scalar_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compose_map_scalar_pair

end MappingAllScalarLocality
