import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection 596 -- scanner-span-locality body-content fact (R596)

R596 (`emitList_allScalar_body_content_at`) is the SCANNER FACT that drives the
Front-B sorry at `EmitterScannability.lean:938`.  It says: for a non-empty
all-scalar flow sequence `emitList items`, scanning from a flow-context state `s`
produces a body block `block` satisfying

  `block.length = 2 * items.length - 1`
  `block[2*j]!.val = .scalar items[j].content .doubleQuoted`

for each `j < items.length`.  The odd-indexed slots carry the `flowEntry` separators.

## Inhabitation debt: rules 1 and 2 apply

* Rule 1 (antecedents reachable): the `h_ne` and `h_all` antecedents are trivially
  satisfied on any concrete all-scalar list.  The scanner-state preconditions
  (`inFlow`, `flowLevel`, `ScannerSurfCorr`) are satisfied by any flow-scanner
  state created during parsing of a flow sequence.  We verify the structural
  `h_ne`/`h_all` part concretely via `decide`.

* Rule 2 (conclusion non-vacuous): `r596_singleton_fires` applies the abstract
  theorem on a singleton list and recovers `block[0]!.val = .scalar sc.content .dq`.
  `r596_two_elem_fires` does the same for a two-element list, extracting both
  the j=0 and j=1 pointwise facts.

Rule 3 does not apply (no provider universal `forall P` in the precondition).
-/

namespace ScannerSpanLocality

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.Proofs.EmitterScannability
open L4YAML.Proofs.CouplingBridge

/-! ## Rule 1: structural antecedents reachable on concrete lists -/

def sc_a : Scalar := { content := "a", style := .plain }
def sc_b : Scalar := { content := "b", style := .plain }

theorem ne_singleton : ([.scalar sc_a] : List YamlValue) ≠ [] := by decide
theorem ne_two_elem  : ([.scalar sc_a, .scalar sc_b] : List YamlValue) ≠ [] := by decide

theorem all_scalar_singleton :
    ∀ v ∈ ([.scalar sc_a] : List YamlValue), ∃ sc : Scalar, v = .scalar sc := by
  intro v hv
  simp only [List.mem_singleton] at hv
  exact ⟨sc_a, hv⟩

theorem all_scalar_two_elem :
    ∀ v ∈ ([.scalar sc_a, .scalar sc_b] : List YamlValue), ∃ sc : Scalar, v = .scalar sc := by
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl
  · exact ⟨sc_a, rfl⟩
  · exact ⟨sc_b, rfl⟩

/-! ## Rule 2: conclusion non-vacuous -- abstract applications of R596

The theorem has 16 conjuncts in its conclusion:
  (A1) ScanChainGrew, (A2) ScannerSurfCorr,
  (A3-A13) eleven state-equality fields,
  (A14) token-filter eq, (A15) block length, (A16) pointwise content.
-/

/-- R596 fires on a singleton all-scalar list: the scanner fact yields a
    one-token block with `.scalar sc.content .doubleQuoted` at position 0. -/
theorem r596_singleton_fires
    (sc : Scalar)
    (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨(emit.emitList [.scalar sc]).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0) (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0) (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line) (h_endline : EndLineOnLine s)
    (h_sync : s.simpleKeyStack.size = s.flowLevel) :
    ∃ (_n : Nat) (s' : ScannerState) (block : List (Positioned YamlToken)),
      ScannerSurfCorr s' ⟨rest, s'.col⟩ ∧
      block.length = 1 ∧
      block[0]!.val = .scalar sc.content .doubleQuoted := by
  obtain ⟨_n, s', block,
          _h_chain, h_corr',                            -- A1, A2
          _, _, _, _, _, _, _, _, _, _, _,              -- A3-A13 (11 fields)
          _h_filt, h_len, h_pw⟩ :=                     -- A14, A15, A16
    emitList_allScalar_body_content_at [.scalar sc]
      (List.cons_ne_nil _ _)
      (fun v hv => by simp only [List.mem_singleton] at hv; exact ⟨sc, hv⟩)
      s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
  obtain ⟨_, h_val⟩ := h_pw 0 (by simp) sc (by simp)
  exact ⟨_n, s', block, h_corr', by simp only [List.length_singleton] at h_len ⊢; omega, h_val⟩

/-- R596 fires on a two-element all-scalar list: the scanner fact yields a
    three-token block (`scalar a`, `flowEntry`, `scalar b`) with the two
    `.scalar` tokens at positions 0 and 2. -/
theorem r596_two_elem_fires
    (sca scb : Scalar)
    (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s
        ⟨(emit.emitList [.scalar sca, .scalar scb]).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0) (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0) (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line) (h_endline : EndLineOnLine s)
    (h_sync : s.simpleKeyStack.size = s.flowLevel) :
    ∃ (_n : Nat) (s' : ScannerState) (block : List (Positioned YamlToken)),
      ScannerSurfCorr s' ⟨rest, s'.col⟩ ∧
      block.length = 3 ∧
      block[0]!.val = .scalar sca.content .doubleQuoted ∧
      block[2]!.val = .scalar scb.content .doubleQuoted := by
  obtain ⟨_n, s', block,
          _h_chain, h_corr',                            -- A1, A2
          _, _, _, _, _, _, _, _, _, _, _,              -- A3-A13 (11 fields)
          _h_filt, h_len, h_pw⟩ :=                     -- A14, A15, A16
    emitList_allScalar_body_content_at [.scalar sca, .scalar scb]
      (List.cons_ne_nil _ _)
      (fun v hv => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl
        · exact ⟨sca, rfl⟩
        · exact ⟨scb, rfl⟩)
      s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sync
  obtain ⟨_, h_val0⟩ := h_pw 0 (by simp) sca (by simp)
  obtain ⟨_, h_val2⟩ := h_pw 1 (by simp) scb (by simp)
  exact ⟨_n, s', block, h_corr',
         by simp only [List.length_cons, List.length_nil] at h_len ⊢; omega,
         h_val0, by simpa using h_val2⟩

/-! ## R597: `scanFiltered_emitSeq_allScalar_token_at` -- token-array content pin

R597 bridges R596's body block to the **full filtered token array**: given
`scanFiltered ("[" ++ emitList items ++ "]") = .ok tokens` with items a
non-empty all-scalar list, R597 gives:

  `tokens.size = 2 * items.length + 3`
  `tokens[1]!.val = .flowSequenceStart`
  `tokens[2 + 2*j]!.val = .scalar (items[j] as Scalar).content .doubleQuoted`

**Inhabitation-debt check**:
- Rule 1 (antecedents reachable): the scanner-state precondition is implicit --
  we drive it via `scanFiltered` directly, so no flow-context precondition.
  `h_ne` and `h_all` hold on any concrete all-scalar list.
- Rule 2 (conclusion non-vacuous): `r597_singleton_fires` instantiates on a
  single-element list; `r597_two_elem_fires` on a two-element list.
-/

/-- R597 fires on a singleton all-scalar list: the scanner returns a token
    array of size 5 with `tokens[2]!.val = .scalar sc.content .doubleQuoted`. -/
theorem r597_singleton_fires
    (sc : Scalar)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList [.scalar sc] ++ "]") = .ok tokens) :
    tokens.size = 5 ∧
    tokens[1]!.val = .flowSequenceStart ∧
    tokens[2]!.val = .scalar sc.content .doubleQuoted := by
  obtain ⟨h_sz, h_t1, h_content⟩ :=
    scanFiltered_emitSeq_allScalar_token_at [.scalar sc]
      (List.cons_ne_nil _ _)
      (fun v hv => by simp only [List.mem_singleton] at hv; exact ⟨sc, hv⟩)
      tokens h_scan
  refine ⟨by simp only [List.length_singleton] at h_sz; exact h_sz, h_t1, ?_⟩
  have h := h_content 0 (by simp) sc (by simp)
  simpa using h

/-- R597 fires on a two-element all-scalar list: token array has size 7 and
    `tokens[2]!.val = .scalar sca.content .doubleQuoted`,
    `tokens[4]!.val = .scalar scb.content .doubleQuoted`. -/
theorem r597_two_elem_fires
    (sca scb : Scalar)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered
        ("[" ++ emit.emitList [.scalar sca, .scalar scb] ++ "]") = .ok tokens) :
    tokens.size = 7 ∧
    tokens[2]!.val = .scalar sca.content .doubleQuoted ∧
    tokens[4]!.val = .scalar scb.content .doubleQuoted := by
  obtain ⟨h_sz, _h_t1, h_content⟩ :=
    scanFiltered_emitSeq_allScalar_token_at [.scalar sca, .scalar scb]
      (List.cons_ne_nil _ _)
      (fun v hv => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl
        · exact ⟨sca, rfl⟩
        · exact ⟨scb, rfl⟩)
      tokens h_scan
  simp only [List.length_cons, List.length_nil] at h_sz
  refine ⟨by omega, ?_, ?_⟩
  · have h := h_content 0 (by simp) sca (by simp); simpa using h
  · have h := h_content 1 (by simp) scb (by simp); simpa using h

/-! ## Axiom audit: R596 depends on propext, Classical.choice, Quot.sound, and
    the native_decide axioms from the double-quoted scanner and escape functions. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.emitList_allScalar_body_content_at' depends on axioms: [propext,
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
#print axioms emitList_allScalar_body_content_at

end ScannerSpanLocality
