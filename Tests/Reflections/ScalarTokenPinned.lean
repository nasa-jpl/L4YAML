import L4YAML.Proofs.Output.EmitterScannability.WellBracketed

/-!
# Reflection 593 -- Scalar token content pinning (SS5.12)

R592 (SS5.10.5) supplied the element-value join for `parseFlowSequenceLoop_push_pointwise`.
R593 supplies the SCANNER-SPAN-LOCALITY bridge: when `scanDoubleQuoted` / `scanNextToken`
consumes the emitted form `'"' :: escapeString content ++ '"' :: rest`, the resulting
filtered-token push is EXACTLY `.scalar content .doubleQuoted` -- content pinned, no existential.

Two theorems landed:
* `scanDoubleQuoted_tokens_push_content` (FilteredGrowth.lean): the `scanDoubleQuoted`-level pin.
* `scanNextToken_flow_scalar_filtered_push_content` (WellBracketed.lean): the `scanNextToken`-level pin.

## Proof strategy

`scanDoubleQuoted_tokens_push` (already in FilteredGrowth) gives `exists c, tokens = push (.scalar c
.doubleQuoted, ...)`.  `scanDoubleQuoted_flow_ok` (ScanSteps) gives
`lastRealTokenVal? tokens = some (.scalar content .doubleQuoted)`.  Combining via
`lastRealTokenVal_push_non_ph'` and `YamlToken.scalar.inj` recovers `c = content`.

The `native_decide` axioms in the list below originate in `collectDoubleQuotedLoop_escapeString_succeeds`
and its dependencies (`escapeChar_hex_structure`, `escapeTag_not_linebreak`, `escapeTag_roundtrip`, etc.)
-- all shipped with the scanner proof base.  `sorry` is absent.

## Inhabitation debt: rules 1 and 2 apply

* Rule 1 (`hcorr` antecedent reachable): the scanner succeeds on `emitScalar content`.
* Rule 2 (conclusion non-vacuous): the theorem applies type-abstractly to recover
  `.scalar content .doubleQuoted`.

Neither theorem has `forall P, ...` provider universals; Rule 3 does not apply.
-/

namespace ScalarTokenPinned

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability
open L4YAML.Proofs.CouplingBridge

/-! ## Rule 1: scanner succeeds on `emitScalar content` (antecedent reachable). -/

theorem scanner_succeeds_on_emitScalar :
    (scanFiltered (emitScalar "hello")).isOk = true := by native_decide

/-! ## Axiom audit: `sorry`-free; `native_decide` axioms from scanner escape-proof base. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.scanDoubleQuoted_tokens_push_content' depends on axioms: [propext,
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
#print axioms scanDoubleQuoted_tokens_push_content

/-- info: 'L4YAML.Proofs.EmitterScannability.scanNextToken_flow_scalar_filtered_push_content' depends on axioms: [propext,
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
#print axioms scanNextToken_flow_scalar_filtered_push_content

/-! ## Rule 2: conclusion non-vacuous -- content string is recovered (type-abstract application). -/

/-- `scanNextToken_flow_scalar_filtered_push_content` applied type-abstractly.
    Given any scanner state `s` with the correct surface correlation, the token pushed to
    the filtered array has `.val = .scalar content .doubleQuoted`. -/
theorem content_recovered_type_abstractly
    (s s' : ScannerState)
    (content : String) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'"' :: (escapeString content).toList ++ ['"'] ++ rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0)
    (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken,
      tok.val = .scalar content .doubleQuoted ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok :=
  scanNextToken_flow_scalar_filtered_push_content s content rest hcorr h_flow h_indent h_col h_snt

end ScalarTokenPinned
