import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection 607 -- `scanFiltered_emitMap_allScalar_pair_at` (R607)

R607 is the mapping analog of R597 (`scanFiltered_emitSeq_allScalar_token_at`).
For a non-empty all-scalar pair list, `scanFiltered ("{" ++ emitPairList pairs ++ "}")` returns
a token array satisfying:

  `tokens.size = 5 * pairs.length + 3`
  `tokens[1]!.val = .flowMappingStart`
  `tokens[2 + 5*j + 1]!.val = .scalar sk.content .doubleQuoted`  (key of pair j)
  `tokens[2 + 5*j + 3]!.val = .scalar sv.content .doubleQuoted`  (value of pair j)
  `tokens[2 + 5*j + 4]!.val = .flowEntry`  (for j + 1 < pairs.length)
  `tokens[5 * pairs.length + 1]!.val = .flowMappingEnd`

R607 packages R606's body-block facts into the full filtered token array, with a
constant offset-2 shift (streamStart + flowMappingStart in prefix).

## Token layout for pairs.length = n

  index 0           : streamStart
  index 1           : flowMappingStart
  for each pair j (0-indexed):
    index 2 + 5*j   : .key
    index 2 + 5*j+1 : .scalar sk.content .doubleQuoted
    index 2 + 5*j+2 : .mappingValue
    index 2 + 5*j+3 : .scalar sv.content .doubleQuoted
    index 2 + 5*j+4 : .flowEntry  (only for j < n-1)
  index 5*n + 1     : flowMappingEnd
  index 5*n + 2     : streamEnd

## Inhabitation-debt rules

* Rule 1 (antecedents reachable): `h_ne` and `h_all` are trivially satisfied on
  any concrete all-scalar pair list.  `h_scan` is satisfied by any well-formed
  serialized flow mapping.

* Rule 2 (conclusion non-vacuous): `r607_singleton_fires` applies R607 on a
  singleton list (tokens.size = 8); `r607_two_pair_fires` applies it on a
  two-pair list (tokens.size = 13) and extracts key/value pins at both pairs
  plus the inter-pair `.flowEntry`.

Rule 3 does not apply (no provider universal in the precondition).
-/

namespace ScannerMapSpanLocality

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.Proofs.EmitterScannability
open L4YAML.Proofs.CouplingBridge

/-! ## Concrete fixtures -/

def sk_a : Scalar := { content := "a", style := .plain }
def sv_x : Scalar := { content := "x", style := .plain }
def sk_b : Scalar := { content := "b", style := .plain }
def sv_y : Scalar := { content := "y", style := .plain }

/-! ## Rule 1: structural antecedents reachable -/

theorem ne_singleton :
    ([(.scalar sk_a, .scalar sv_x)] : List (YamlValue × YamlValue)) ≠ [] := by decide

theorem ne_two_pair :
    ([(.scalar sk_a, .scalar sv_x), (.scalar sk_b, .scalar sv_y)] :
     List (YamlValue × YamlValue)) ≠ [] := by decide

theorem all_scalar_singleton :
    ∀ p ∈ ([(.scalar sk_a, .scalar sv_x)] : List (YamlValue × YamlValue)),
    ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  exact ⟨sk_a, sv_x, by rw [hp], by rw [hp]⟩

theorem all_scalar_two_pair :
    ∀ p ∈ ([(.scalar sk_a, .scalar sv_x), (.scalar sk_b, .scalar sv_y)] :
           List (YamlValue × YamlValue)),
    ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨sk_a, sv_x, rfl, rfl⟩
  · exact ⟨sk_b, sv_y, rfl, rfl⟩

/-! ## Rule 2: conclusion non-vacuous -- abstract applications of R607 -/

/-- R607 fires on a singleton all-scalar pair list: token array has size 8,
    with `tokens[3]!.val = .scalar sk.content .doubleQuoted` (key at 2+5*0+1)
    and `tokens[5]!.val = .scalar sv.content .doubleQuoted` (value at 2+5*0+3). -/
theorem r607_singleton_fires
    (sk sv : Scalar)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered
        ("{" ++ emit.emitPairList [(.scalar sk, .scalar sv)] ++ "}") = .ok tokens) :
    tokens.size = 8 ∧
    tokens[1]!.val = .flowMappingStart ∧
    tokens[3]!.val = .scalar sk.content .doubleQuoted ∧
    tokens[5]!.val = .scalar sv.content .doubleQuoted ∧
    tokens[6]!.val = .flowMappingEnd := by
  obtain ⟨h_sz, h_t1, h_content, _h_fe, h_fme, _h_key, _h_mv⟩ :=
    scanFiltered_emitMap_allScalar_pair_at [(.scalar sk, .scalar sv)]
      (List.cons_ne_nil _ _)
      (fun p hp => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        exact ⟨sk, sv, by rw [hp], by rw [hp]⟩)
      tokens h_scan
  obtain ⟨h_k, h_v⟩ := h_content 0 (by simp) sk sv (by simp)
  exact ⟨by simp only [List.length_singleton] at h_sz; exact h_sz,
         h_t1,
         by simpa using h_k,
         by simpa using h_v,
         by simpa using h_fme⟩

/-- R607 fires on a two-pair all-scalar list: token array has size 13,
    with keys/values at 3/5 (pair 0), flowEntry at 6, keys/values at 8/10 (pair 1),
    and flowMappingEnd at 11. -/
theorem r607_two_pair_fires
    (sk1 sv1 sk2 sv2 : Scalar)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered
        ("{" ++ emit.emitPairList [(.scalar sk1, .scalar sv1),
                                   (.scalar sk2, .scalar sv2)] ++ "}") = .ok tokens) :
    tokens.size = 13 ∧
    tokens[1]!.val = .flowMappingStart ∧
    tokens[3]!.val = .scalar sk1.content .doubleQuoted ∧
    tokens[5]!.val = .scalar sv1.content .doubleQuoted ∧
    tokens[6]!.val = .flowEntry ∧
    tokens[8]!.val = .scalar sk2.content .doubleQuoted ∧
    tokens[10]!.val = .scalar sv2.content .doubleQuoted ∧
    tokens[11]!.val = .flowMappingEnd := by
  obtain ⟨h_sz, h_t1, h_content, h_fe, h_fme, _h_key, _h_mv⟩ :=
    scanFiltered_emitMap_allScalar_pair_at
      [(.scalar sk1, .scalar sv1), (.scalar sk2, .scalar sv2)]
      (List.cons_ne_nil _ _)
      (fun p hp => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact ⟨sk1, sv1, rfl, rfl⟩
        · exact ⟨sk2, sv2, rfl, rfl⟩)
      tokens h_scan
  obtain ⟨h_k1, h_v1⟩ := h_content 0 (by simp) sk1 sv1 (by simp)
  obtain ⟨h_k2, h_v2⟩ := h_content 1 (by simp) sk2 sv2 (by simp)
  have h_fe0 := h_fe 0 (by simp)
  exact ⟨by simp only [List.length_cons, List.length_nil] at h_sz; omega,
         h_t1,
         by simpa using h_k1,
         by simpa using h_v1,
         by simpa using h_fe0,
         by simpa using h_k2,
         by simpa using h_v2,
         by simpa using h_fme⟩

/-! ## Axiom audit: R607 depends on propext, Classical.choice, Quot.sound, and
    the native_decide axioms from the double-quoted scanner (same set as R606). -/

/-- info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_emitMap_allScalar_pair_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_15,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_18,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_27,
 escapeChar_hex_structure._native.native_decide.ax_1_1,
 escapeChar_hex_structure._native.native_decide.ax_1_2,
 escapeChar_hex_structure._native.native_decide.ax_1_3,
 escapeTag_not_linebreak._native.native_decide.ax_1_10,
 escapeTag_not_linebreak._native.native_decide.ax_1_11,
 escapeTag_not_linebreak._native.native_decide.ax_1_12,
 escapeTag_not_linebreak._native.native_decide.ax_1_2,
 escapeTag_not_linebreak._native.native_decide.ax_1_3,
 escapeTag_not_linebreak._native.native_decide.ax_1_4,
 escapeTag_not_linebreak._native.native_decide.ax_1_5,
 escapeTag_not_linebreak._native.native_decide.ax_1_6,
 escapeTag_not_linebreak._native.native_decide.ax_1_7,
 escapeTag_not_linebreak._native.native_decide.ax_1_8,
 escapeTag_not_linebreak._native.native_decide.ax_1_9,
 hexNibble_is_hex._native.native_decide.ax_1_1,
 hexNibble_lt128._native.native_decide.ax_1_1,
 hex_foldl_roundtrip._native.native_decide.ax_1_1,
 hex_two_foldl_bound._native.native_decide.ax_1_1,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_10,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_11,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_12,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_13,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_14,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_15,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_16,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_17,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_18,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_19,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_2,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_20,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_21,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_22,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_23,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_3,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_4,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_5,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_6,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_7,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_8,
 Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_9] -/
#guard_msgs (whitespace := lax) in
#print axioms scanFiltered_emitMap_allScalar_pair_at

end ScannerMapSpanLocality
