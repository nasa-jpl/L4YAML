import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 574 — INHABITATION PROBE for Front B's value-recovery trace, brick 2 sub-link (b)

This file is the inhabitation test the [[feedback-inhabitation-debt-validate-target-defs]] discipline
demands for **brick 2 sub-link (b)** of Front B — the `compose`-preservation lemmas
`compose_preserves_flow_sequence` / `compose_preserves_flow_mapping` (in `ContentFidelity.lean`
§5.5). Brick 2 sub-link (a) (§5.4) pinned the outer constructor through `parseNode` (the raw
serialization tree). The content-fidelity sorries, however, compare against
`(raw_docs.map YamlDocument.compose)[0]!.value` — the **composed** representation graph. `compose`
(YAML 1.2.2 §3.1) is `resolveAliases` then `stripAnchors` on the value; both recurse into children
but pass `style`/`tag` through and force `anchor := none`, so a `.sequence .flow _ none none` /
`.mapping .flow _ none none` head survives with the SAME outer constructor.

## Why this probe (the inhabitation-debt risk for a CONCLUSION lemma with ONE antecedent)

The compose lemmas are CONCLUSIONS `(doc.value = .sequence .flow items' none none) -> (composed shape)`,
so Lean proves them TRUE — but a conclusion is worthless if its antecedent is never satisfiable on
real data: it would type-check yet never fire. Brick 2 sub-link (a) had TWO antecedents (`h_peek` +
`parseNode … = .ok …`); sub-link (b) has just ONE (`doc.value` IS a flow collection with default
tag/anchor), so the inhabitation obligation collapses back to single-antecedent satisfiability —
witnessed here on REAL emitted+parsed bytes (exactly what sorries 3/4 face), not a hand-typed literal.

* `seqDocValueIsFlowSeq_fires` / `mapDocValueIsFlowMap_fires` — the single antecedent is satisfiable:
  the value of a REAL document parsed from emitted output IS `.sequence/.mapping .flow _ none none`.
* `seqComposePreservesFlowSeq_fires` / `mapComposePreservesFlowMap_fires` — the conclusion holds
  end-to-end on REAL composed data: after `compose`, the value is STILL a flow collection with
  default tag/anchor — the lemma's claim, verified on real bytes, so it is NOT vacuously true.
* `seqRawDoc_compose_recovers_sequence` / `mapRawDoc_compose_recovers_mapping` — the actual lemma
  applied to the REAL composed document, with the antecedent satisfiable by the witnesses above.
-/

namespace ValueRecoveryCompose

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

/-- The FIRST document parsed (raw — serialization tree, pre-`compose`) from the REAL emitted bytes
    of `seqValue`. This is a genuine `YamlDocument`, exactly the kind the content-fidelity sorries
    feed to `compose`. (`default` is unreachable: parsing emitted output succeeds — see below.) -/
def seqRawDoc : YamlDocument :=
  match parseYamlRaw (emit seqValue) with
  | .ok raw_docs => raw_docs[0]!
  | .error _ => default

/-- Mirror: the first raw document parsed from the emitted bytes of `mapValue`. -/
def mapRawDoc : YamlDocument :=
  match parseYamlRaw (emit mapValue) with
  | .ok raw_docs => raw_docs[0]!
  | .error _ => default

/-- Bool witness for antecedent satisfiability: the REAL raw document's value IS a flow sequence with
    default tag/anchor — i.e. `seqRawDoc.value = .sequence .flow _ none none` holds for some items. -/
def seqDocValueIsFlowSeq : Bool :=
  match seqRawDoc.value with
  | .sequence .flow _ none none => true
  | _ => false

/-- Mirror: the real raw mapping document's value is a flow mapping with default tag/anchor. -/
def mapDocValueIsFlowMap : Bool :=
  match mapRawDoc.value with
  | .mapping .flow _ none none => true
  | _ => false

-- The single antecedent of the compose lemmas is satisfiable on REAL data.
theorem seqDocValueIsFlowSeq_fires : seqDocValueIsFlowSeq = true := by native_decide
theorem mapDocValueIsFlowMap_fires : mapDocValueIsFlowMap = true := by native_decide

/-- Bool witness for the conclusion, end-to-end on REAL composed data: after `compose`, the value is
    STILL a flow sequence with default tag/anchor. This is the lemma's conclusion shape verified on
    actual emitted+parsed+composed bytes — confirming the claim is non-vacuous. -/
def seqComposePreservesFlowSeq : Bool :=
  match (seqRawDoc.compose).value with
  | .sequence .flow _ none none => true
  | _ => false

/-- Mirror: the composed mapping value is still a flow mapping with default tag/anchor. -/
def mapComposePreservesFlowMap : Bool :=
  match (mapRawDoc.compose).value with
  | .mapping .flow _ none none => true
  | _ => false

-- The conclusion holds on REAL composed data: `compose` preserves the outer flow-collection shape.
theorem seqComposePreservesFlowSeq_fires : seqComposePreservesFlowSeq = true := by native_decide
theorem mapComposePreservesFlowMap_fires : mapComposePreservesFlowMap = true := by native_decide

/-- The actual lemma `compose_preserves_flow_sequence` applied to the REAL raw document. Its single
    hypothesis is satisfiable here (witnessed by `seqDocValueIsFlowSeq_fires`), so this is a genuine,
    non-vacuous use: from the real flow-sequence value, the lemma delivers a flow-sequence composed
    value — the outer-shape half of the value-recovery trace, lifted across `compose`. -/
theorem seqRawDoc_compose_recovers_sequence
    (items' : Array YamlValue)
    (h : seqRawDoc.value = .sequence .flow items' none none) :
    ∃ items'', (seqRawDoc.compose).value = .sequence .flow items'' none none :=
  compose_preserves_flow_sequence seqRawDoc items' h

/-- Mirror: `compose_preserves_flow_mapping` applied to the REAL raw mapping document. -/
theorem mapRawDoc_compose_recovers_mapping
    (pairs' : Array (YamlValue × YamlValue))
    (h : mapRawDoc.value = .mapping .flow pairs' none none) :
    ∃ pairs'', (mapRawDoc.compose).value = .mapping .flow pairs'' none none :=
  compose_preserves_flow_mapping mapRawDoc pairs' h

-- Axiom audit — the source lemmas are pure structural unfolds of `compose` / `resolveAliases` /
-- `stripAnchors` (a `rfl` projection, two `unfold`s, and a constructor witness), so their profile is
-- LEANER than bricks 1 and 2(a): no `Classical.choice` — those inherited it from the `Except`-monad
-- simp machinery, which these never touch. (The `native_decide` firing probes above are separate and
-- carry `Lean.ofReduceBool` on top.)
/-- info: 'L4YAML.Proofs.EmitterScannability.compose_preserves_flow_sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compose_preserves_flow_sequence

/-- info: 'L4YAML.Proofs.EmitterScannability.compose_preserves_flow_mapping' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compose_preserves_flow_mapping

end ValueRecoveryCompose
