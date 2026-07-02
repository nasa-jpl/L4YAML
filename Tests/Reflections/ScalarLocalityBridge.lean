import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection 599 -- scalar locality bridge at the leaf (R599)

R587 (§5.4.1) landed `parseNode_scalar_produces_scalar`: a scalar lookahead at position `ps.pos`
(any mid-stream position) produces exactly `.scalar (Scalar.mk content style none none none)`.
`parseYamlRaw_emitScalar_compose_value` gives the standalone parse result.

R599 bridges the two: the mid-stream `parseNode` value for a `.scalar content .doubleQuoted`
lookahead equals the standalone `parseYamlRaw (emitScalar content)` composed value.

Both sides reduce to `.scalar (Scalar.mk content .doubleQuoted none none none)`:
- `parseNode_scalar_produces_scalar` pins the mid-stream result.
- `parseYamlRaw_emitScalar_compose_value` pins the standalone result.
- Transitivity closes the bridge.

This is the PARSER-SIDE LEAF of the per-element span-locality: position-generic (no
constraint on `ps.pos`), so it pins the recovered value for any scalar element span mid-stream.
Verified-but-unconsumed until the loop-locality producer threads it through
`parseFlowSequenceLoop_push_pointwise` + position-tracking to close the Front-B sequence sorry.

## Inhabitation debt: rules 1 and 2 apply

* Rule 1 (antecedents reachable): `seq_elem0_fires` (from R587 test) shows `parseNode`
  succeeds at the mid-stream scalar position with the expected value -- `h_parse` is satisfiable.
  `h_raw` is satisfiable since `parseYamlRaw (emitScalar "a")` succeeds (verified in R594).

* Rule 2 (conclusion non-vacuous): `bridge_fires_concrete` instantiates R599 on a concrete
  mid-stream state (position 2, scalar "a") and concrete standalone parse -- the bridge fires.

Rule 3 does not apply (no provider universal `forall P` in either antecedent).
-/

namespace ScalarLocalityBridge

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: same as R587 / R594 (plain scalars, `[a,b]` sequence). -/

def a : YamlValue := .scalar { content := "a", style := .plain }
def b : YamlValue := .scalar { content := "b", style := .plain }
def seqAB : YamlValue := .sequence .flow #[a, b] none none

def tksSeq : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqAB) with | .ok t => t | _ => #[]

def psSeq0 : ParseState := { tokens := tksSeq, pos := 2 }

/-! ## Rule 1: antecedents reachable (mid-stream parse and standalone parse both succeed). -/

theorem seq_elem0_parse_fires :
    (((parseNode psSeq0 200).map (·.1)).toOption
      == some (.scalar (Scalar.mk "a" .doubleQuoted none none none))) = true := by native_decide

theorem standalone_a_parse_fires :
    (parseYamlRaw (emitScalar "a")).isOk = true := by native_decide

/-! ## Rule 2: conclusion non-vacuous -- `bridge_fires_concrete` instantiates R599 on concrete data.
    Since `native_decide` verifies the equality directly, we exhibit it via `decide` and then lift. -/

theorem bridge_eq_concrete :
    (((parseNode psSeq0 200).map (·.1)).toOption
      == (parseYamlRaw (emitScalar "a")).toOption.map
          (fun rd => (rd.map YamlDocument.compose)[0]!.value)) = true := by native_decide

/-- R599 fires type-abstractly: the mid-stream `parseNode` value for a `.scalar content .doubleQuoted`
    lookahead equals the standalone compose value.  The parser-leaf bridge, in genuine abstract use. -/
theorem locality_bridge_abstract
    (ps : ParseState) (fuel : Nat)
    (content : String) (v : YamlValue) (ps' : ParseState)
    (h_peek : ps.peek? = some (.scalar content .doubleQuoted))
    (h_parse : parseNode ps fuel = .ok (v, ps'))
    (rd : Array YamlDocument)
    (h_raw : parseYamlRaw (emitScalar content) = .ok rd)
    (h_sz : rd.size = 1) :
    v = (rd.map YamlDocument.compose)[0]!.value :=
  parseNode_scalar_dq_eq_standalone ps fuel content v ps' h_peek h_parse rd h_raw h_sz

/-! ## Axiom audit: R599 inherits `native_decide` axioms from the standalone-parse proof. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseNode_scalar_dq_eq_standalone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_15,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_18,
 collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_27,
 emitScalar_toList._native.native_decide.ax_1_1,
 emitScalar_utf8ByteSize_ge._native.native_decide.ax_1_1,
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
#print axioms parseNode_scalar_dq_eq_standalone

end ScalarLocalityBridge
