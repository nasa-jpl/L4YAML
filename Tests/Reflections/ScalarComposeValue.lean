module

public import L4YAML.Proofs.Output.EmitterScannability

@[expose] public section Blanket

/-!
# Reflection 594 -- standalone scalar parse, composed value pin (SS5.12 continued)

R593 (SS5.12) pinned the scalar token content at the scanner level.
R594 pins the COMPOSED VALUE end: when `parseYamlRaw (emitScalar content)` succeeds and returns
exactly one document, the composed first document's value is EXACTLY
`.scalar (Scalar.mk content .doubleQuoted none none none)`.

This is the RIGHT SIDE of the per-element locality equation
`(rd.map compose)[0]!.value = items''[i]!` for scalar elements.
Verified-but-unconsumed: the LEFT SIDE (`items''[i]! = ...`) is R595.

## Proof strategy

Three existing lemmas chain directly:
* `scanFiltered_emitScalar_vals` -- 3-token structure (streamStart, scalar content dq, streamEnd).
* `parseStream_three_tokens_scalar` -- 3-token stream produces `docs[0]!.value = .scalar (Scalar.mk ...)`.
* `compose_scalar_content doc s h_val` -- compose on an anchor-free scalar is
  `.scalar { s with anchor := none }`, definitionally equal to `.scalar s` when `s.anchor = none`.

Key craft note: `subst h_eq` where `h_eq : rd = docs` eliminates `docs` (the NEWER local variable
introduced by `obtain`), keeping `rd` (the OLDER function parameter).  All post-subst references
must use `rd`.  The `rw [show (rd.map compose)[0]!.value = (rd[0]!.compose).value from ...]` step
is verbatim from the sorry-context pattern at EmitterScannability.lean:1097.

## Inhabitation debt: rules 1 and 2 apply

* Rule 1 (`h_raw` antecedent reachable): `parseYamlRaw (emitScalar "hello")` succeeds.
* Rule 2 (conclusion non-vacuous): `compose_value_scalar_type_abstractly` applies the theorem
  type-abstractly; the conclusion is non-vacuous because rule 1 confirms the antecedent holds.

Neither theorem has `forall P, ...` provider universals; Rule 3 does not apply.

The `#guard_msgs` axiom set has two entries beyond R593: `emitScalar_toList._native.native_decide.ax_1_1`
and `emitScalar_utf8ByteSize_ge._native.native_decide.ax_1_1`, pulled in by `scanFiltered_emitScalar_vals`
via `scanLoop_two_iter_eq` (which verifies the scanner loop boundary conditions on concrete emitter output).
-/

namespace ScalarComposeValue

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Rule 1: parser succeeds on `emitScalar content` (h_raw antecedent reachable). -/

theorem parse_succeeds_emitScalar :
    (parseYamlRaw (emitScalar "hello")).isOk = true := by native_decide

/-! ## Axiom audit: `sorry`-free; same `native_decide` axioms as R593 (scanner escape chain). -/

/--
info: 'L4YAML.Proofs.EmitterScannability.parseYamlRaw_emitScalar_compose_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_10,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_11,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_12,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_13,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_14,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_15,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_16,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_17,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_18,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_19,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_2,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_20,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_21,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_22,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_23,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_3,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_4,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_5,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_6,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_7,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_8,
 _private.L4YAML.Proofs.RoundTrip.RoundTrip.0.L4YAML.Proofs.RoundTrip.escapeTag_roundtrip._native.native_decide.ax_1_9,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_15,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_18,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.collectDoubleQuotedLoop_escapeString_succeeds._native.native_decide.ax_1_27,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeChar_hex_structure._native.native_decide.ax_1_1,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeChar_hex_structure._native.native_decide.ax_1_2,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeChar_hex_structure._native.native_decide.ax_1_3,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_10,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_11,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_12,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_2,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_3,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_4,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_5,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_6,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_7,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_8,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.escapeTag_not_linebreak._native.native_decide.ax_1_9,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.hexNibble_is_hex._native.native_decide.ax_1_1,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.hexNibble_lt128._native.native_decide.ax_1_1,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.hex_foldl_roundtrip._native.native_decide.ax_1_1,
 _private.L4YAML.Proofs.Output.EmitterScannability.EscapeProperties.0.L4YAML.Proofs.EmitterScannability.hex_two_foldl_bound._native.native_decide.ax_1_1,
 _private.L4YAML.Proofs.Output.EmitterScannability.ScannerAcceptance.0.L4YAML.Proofs.EmitterScannability.emitScalar_toList._native.native_decide.ax_1_1,
 _private.L4YAML.Proofs.Output.EmitterScannability.ScannerAcceptance.0.L4YAML.Proofs.EmitterScannability.emitScalar_utf8ByteSize_ge._native.native_decide.ax_1_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms parseYamlRaw_emitScalar_compose_value

/-! ## Rule 2: conclusion non-vacuous -- composed value is scalar (type-abstract application). -/

/-- `parseYamlRaw_emitScalar_compose_value` applied type-abstractly.
    Given any parse result `rd` for `emitScalar "hello"` of size 1, the composed first
    document's value is `.scalar (Scalar.mk "hello" .doubleQuoted none none none)`. -/
theorem compose_value_scalar_type_abstractly
    (rd : Array YamlDocument)
    (h_raw : parseYamlRaw (emitScalar "hello") = .ok rd)
    (h_sz : rd.size = 1) :
    (rd.map YamlDocument.compose)[0]!.value =
      .scalar (Scalar.mk "hello" .doubleQuoted none none none) :=
  parseYamlRaw_emitScalar_compose_value "hello" rd h_raw h_sz

end ScalarComposeValue

end Blanket
