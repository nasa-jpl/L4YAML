import L4YAML.Proofs.Output.EmitterScannability.ScannerSpanLocality

/-!
# Reflection 606 -- `emitPairList_allScalar_body_content_at` (R606)

R606 is the mapping analog of R596 (`emitList_allScalar_body_content_at`).  For a
non-empty all-scalar pair list `emitPairList pairs`, scanning from a flow-context
scanner state produces a body block satisfying

  `block.length = 5 * pairs.length - 1`
  `block[5*j+1]!.val = .scalar sk_j.content .doubleQuoted`   (key of pair j)
  `block[5*j+3]!.val = .scalar sv_j.content .doubleQuoted`   (value of pair j)
  `block[5*j+4]!.val = .flowEntry`  (separator, for j + 1 < pairs.length only)

Compared with R596 (2 tokens per item), R606 produces 5 tokens per pair:
  [.key, key-scalar, .mappingValue, value-scalar, .flowEntry]
but the last pair has no `.flowEntry` (hence 5n - 1 total).

Extra precondition vs R596: `s.simpleKeyAllowed = true` (needed to scan the
explicit `.key` token that precedes each key scalar).

## Inhabitation-debt rules

* Rule 1 (antecedents reachable): `h_ne` and `h_all` are trivially satisfied on
  any concrete all-scalar pair list.  Verified abstractly.

* Rule 2 (conclusion non-vacuous): `r606_singleton_fires` applies R606 on a
  singleton list; `r606_two_pair_fires` applies it on a two-pair list and
  extracts both key+value positions and the inter-pair `.flowEntry`.

Rule 3 does not apply (no provider universal in the precondition).
-/

namespace PairListBodyContentAt

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.Proofs.EmitterScannability
open L4YAML.Proofs.CouplingBridge

/-! ## Concrete fixtures -/

def sk_a : Scalar := { content := "a", style := .plain }
def sv_a : Scalar := { content := "x", style := .plain }
def sk_b : Scalar := { content := "b", style := .plain }
def sv_b : Scalar := { content := "y", style := .plain }

/-! ## Rule 1: structural antecedents reachable -/

theorem ne_singleton :
    ([(.scalar sk_a, .scalar sv_a)] : List (YamlValue × YamlValue)) ≠ [] := by decide

theorem ne_two_pair :
    ([(.scalar sk_a, .scalar sv_a), (.scalar sk_b, .scalar sv_b)] :
     List (YamlValue × YamlValue)) ≠ [] := by decide

theorem all_scalar_singleton :
    ∀ p ∈ ([(.scalar sk_a, .scalar sv_a)] : List (YamlValue × YamlValue)),
    ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  exact ⟨sk_a, sv_a, by rw [hp], by rw [hp]⟩

theorem all_scalar_two_pair :
    ∀ p ∈ ([(.scalar sk_a, .scalar sv_a), (.scalar sk_b, .scalar sv_b)] :
           List (YamlValue × YamlValue)),
    ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨sk_a, sv_a, rfl, rfl⟩
  · exact ⟨sk_b, sv_b, rfl, rfl⟩

/-! ## Rule 2: conclusion non-vacuous -- abstract applications of R606

The theorem has 17 conjuncts in its conclusion:
  (A1) ScanChainGrew, (A2) ScannerSurfCorr,
  (A3–A13) eleven state-equality/invariant fields,
  (A14) token-filter eq, (A15) block length,
  (A16) pointwise key/value content, (A17) flow-entry positions.
-/

/-- R606 fires on a singleton all-scalar pair list: the scanner fact yields a
    4-token block with `.scalar sk.content .dq` at position 1 and
    `.scalar sv.content .dq` at position 3. -/
theorem r606_singleton_fires
    (sk sv : Scalar)
    (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s
        ⟨(emit.emitPairList [(.scalar sk, .scalar sv)]).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0) (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0) (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line) (h_endline : EndLineOnLine s)
    (h_ska : s.simpleKeyAllowed = true) (h_sync : s.simpleKeyStack.size = s.flowLevel) :
    ∃ (_n : Nat) (s' : ScannerState) (block : List (Positioned YamlToken)),
      ScannerSurfCorr s' ⟨rest, s'.col⟩ ∧
      block.length = 4 ∧
      block[1]!.val = .scalar sk.content .doubleQuoted ∧
      block[3]!.val = .scalar sv.content .doubleQuoted := by
  obtain ⟨_n, s', block,
          _h_chain, h_corr',                             -- A1, A2
          _, _, _, _, _, _, _, _, _, _, _,               -- A3-A13 (11 fields)
          _h_filt, h_len, h_pw, _h_fe⟩ :=              -- A14, A15, A16, A17
    emitPairList_allScalar_body_content_at [(.scalar sk, .scalar sv)]
      (List.cons_ne_nil _ _)
      (fun p hp => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        exact ⟨sk, sv, by rw [hp], by rw [hp]⟩)
      s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
  obtain ⟨_, h_k_val, _, h_v_val⟩ :=
    h_pw 0 (by simp) sk sv (by simp)
  exact ⟨_n, s', block, h_corr',
         by simp only [List.length_singleton] at h_len ⊢; omega,
         h_k_val, h_v_val⟩

/-- R606 fires on a two-pair all-scalar list: 9-token block with
    key₁ at 1, value₁ at 3, `.flowEntry` at 4, key₂ at 6, value₂ at 8. -/
theorem r606_two_pair_fires
    (sk1 sv1 sk2 sv2 : Scalar)
    (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s
        ⟨(emit.emitPairList [(.scalar sk1, .scalar sv1),
                              (.scalar sk2, .scalar sv2)]).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0) (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0) (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line) (h_endline : EndLineOnLine s)
    (h_ska : s.simpleKeyAllowed = true) (h_sync : s.simpleKeyStack.size = s.flowLevel) :
    ∃ (_n : Nat) (s' : ScannerState) (block : List (Positioned YamlToken)),
      ScannerSurfCorr s' ⟨rest, s'.col⟩ ∧
      block.length = 9 ∧
      block[1]!.val = .scalar sk1.content .doubleQuoted ∧
      block[3]!.val = .scalar sv1.content .doubleQuoted ∧
      block[4]!.val = .flowEntry ∧
      block[6]!.val = .scalar sk2.content .doubleQuoted ∧
      block[8]!.val = .scalar sv2.content .doubleQuoted := by
  obtain ⟨_n, s', block,
          _h_chain, h_corr',                             -- A1, A2
          _, _, _, _, _, _, _, _, _, _, _,               -- A3-A13 (11 fields)
          _h_filt, h_len, h_pw, h_fe⟩ :=               -- A14, A15, A16, A17
    emitPairList_allScalar_body_content_at
      [(.scalar sk1, .scalar sv1), (.scalar sk2, .scalar sv2)]
      (List.cons_ne_nil _ _)
      (fun p hp => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact ⟨sk1, sv1, rfl, rfl⟩
        · exact ⟨sk2, sv2, rfl, rfl⟩)
      s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska h_sync
  obtain ⟨_, h_k1, _, h_v1⟩ := h_pw 0 (by simp) sk1 sv1 (by simp)
  obtain ⟨_, h_k2, _, h_v2⟩ := h_pw 1 (by simp) sk2 sv2 (by simp)
  obtain ⟨_, h_fe0⟩ := h_fe 0 (by simp)
  exact ⟨_n, s', block, h_corr',
         by simp only [List.length_cons, List.length_singleton] at h_len ⊢; omega,
         h_k1, h_v1, h_fe0, by simpa using h_k2, by simpa using h_v2⟩

/-! ## Axiom audit: R606 depends on propext, Classical.choice, Quot.sound, and
    the native_decide axioms from the double-quoted scanner and escape functions
    (same set as R596). -/

/-- info: 'L4YAML.Proofs.EmitterScannability.emitPairList_allScalar_body_content_at' depends on axioms: [propext,
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
#print axioms emitPairList_allScalar_body_content_at

end PairListBodyContentAt
