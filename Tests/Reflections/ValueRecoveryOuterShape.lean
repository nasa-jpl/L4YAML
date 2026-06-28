import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 572 — INHABITATION PROBE for Front B's value-recovery trace, brick 1 (outer shape)

This file is the inhabitation test the [[feedback-inhabitation-debt-validate-target-defs]] discipline
demands for the FIRST brick of **Front B** — the content-fidelity sorries
(`emit_roundtrip_{sequence,mapping}_content_eq`, `EmitterScannability.lean:845`/`:885`). Front B owes
"the exact parsed value structure from parser trace"; brick 1 pins the recovered value's OUTER
constructor: a successful `parseFlowSequence` / `parseFlowMapping` always returns
`.sequence .flow _ none none` / `.mapping .flow _ none none` (the lone `.ok` branch literally builds
that head). The lemmas `parseFlowSequence_produces_sequence` / `parseFlowMapping_produces_mapping`
live in `ContentFidelity.lean`; this file imports the REAL defs and probes them on REAL emitted bytes.
It lives under `Tests/` — NOT inline in source — per the discipline's "inhabitation tests in `tests/`"
rule.

## Why this probe (the inhabitation-debt risk for a CONCLUSION lemma)

The outer-shape lemmas are CONCLUSIONS — Lean proves them TRUE (not merely well-formed). But a
conclusion `(antecedent) → (shape)` is worthless if the antecedent is never satisfiable on real data:
it would type-check yet never fire. The antecedent here is `parseFlowSequence ps fuel = .ok (v, ps')`.
So the genuine probe is: confirm on REAL emitted output that the parse IS `.ok` of a flow collection
(antecedent fires NON-vacuously), then show the actual lemma consumes that real `.ok` and delivers the
shape. We ground on `emit`ted bytes — exactly what sorries 3/4 face — not a hand-typed literal.

* `seqOuterShape_fires` / `mapOuterShape_fires` — the REAL parse of emitted `["x"]` / `{"a":"b"}`
  is `.ok` of a `.sequence .flow _ none none` / `.mapping .flow _ none none`. The antecedent is
  genuinely inhabited; the conclusion genuinely holds.
* `seqPS_recovers_sequence` / `mapPS_recovers_mapping` — the actual lemma applied to the REAL
  scan-derived `ParseState`: from the (firing-confirmed) `.ok` it yields the sequence / mapping shape.
-/

namespace ValueRecoveryOuterShape

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-- A genuine grammable flow sequence `["x"]`. -/
def seqValue : YamlValue := .sequence .flow #[.scalar { content := "x", style := .doubleQuoted }]

/-- A genuine grammable flow mapping `{"a":"b"}`. -/
def mapValue : YamlValue :=
  .mapping .flow #[(.scalar { content := "a", style := .doubleQuoted },
                    .scalar { content := "b", style := .doubleQuoted })]

/-- Tokens from scanning the REAL emitted bytes of `seqValue` (not a hand-typed literal). -/
def seqTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqValue) with | .ok ts => ts | .error _ => #[]

/-- Tokens from scanning the REAL emitted bytes of `mapValue`. -/
def mapTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapValue) with | .ok ts => ts | .error _ => #[]

/-- A `ParseState` positioned at the opening `[` (index 1, just past `streamStart`). -/
def seqPS : ParseState := { tokens := seqTokens, pos := 1 }

/-- A `ParseState` positioned at the opening `{`. -/
def mapPS : ParseState := { tokens := mapTokens, pos := 1 }

/-- Bool witness: the real parse of emitted `["x"]` is `.ok` of a flow sequence with default
    tag/anchor — exactly the lemma's conclusion shape, on real data. -/
def seqOuterShapeFires : Bool :=
  match parseFlowSequence seqPS (4 * seqTokens.size + 4) with
  | .ok (.sequence .flow _ none none, _) => true
  | _ => false

/-- Bool witness: the real parse of emitted `{"a":"b"}` is `.ok` of a flow mapping. -/
def mapOuterShapeFires : Bool :=
  match parseFlowMapping mapPS (4 * mapTokens.size + 4) with
  | .ok (.mapping .flow _ none none, _) => true
  | _ => false

-- GENUINE real-data firing: the `.ok (.sequence/.mapping …)` antecedent is satisfiable on
-- emitted output, so the outer-shape lemmas are NOT vacuously true.
theorem seqOuterShape_fires : seqOuterShapeFires = true := by native_decide
theorem mapOuterShape_fires : mapOuterShapeFires = true := by native_decide

/-- The actual lemma `parseFlowSequence_produces_sequence` applied to the REAL scan-derived state.
    Its hypothesis is satisfiable here (witnessed by `seqOuterShape_fires`), so this is a genuine,
    non-vacuous use: from the real `.ok` the lemma delivers the flow-sequence shape. -/
theorem seqPS_recovers_sequence
    (v : YamlValue) (ps' : ParseState)
    (h : parseFlowSequence seqPS (4 * seqTokens.size + 4) = .ok (v, ps')) :
    ∃ items', v = .sequence .flow items' none none :=
  parseFlowSequence_produces_sequence _ _ _ _ h

/-- Mirror: `parseFlowMapping_produces_mapping` applied to the REAL mapping state. -/
theorem mapPS_recovers_mapping
    (v : YamlValue) (ps' : ParseState)
    (h : parseFlowMapping mapPS (4 * mapTokens.size + 4) = .ok (v, ps')) :
    ∃ pairs', v = .mapping .flow pairs' none none :=
  parseFlowMapping_produces_mapping _ _ _ _ h

-- Axiom audit — the source lemmas are structural unfolds; `Classical.choice` is inherited from
-- the parser/`Except`-monad simp machinery they unfold, NOT from `native_decide` (the
-- `native_decide` firing probes above are separate and carry `Lean.ofReduceBool` on top).
/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowSequence_produces_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseFlowSequence_produces_sequence

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowMapping_produces_mapping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseFlowMapping_produces_mapping

end ValueRecoveryOuterShape
