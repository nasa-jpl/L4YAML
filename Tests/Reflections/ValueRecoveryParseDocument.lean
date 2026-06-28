import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 575 — INHABITATION PROBE for Front B's value-recovery trace, brick 2 last link (part 1)

This file is the inhabitation test the [[feedback-inhabitation-debt-validate-target-defs]] discipline
demands for the **`parseDocument` dispatch** lemmas `parseDocument_flowSeqStart_produces_sequence` /
`parseDocument_flowMapStart_produces_mapping` (in `ContentFidelity.lean` §5.6). Brick 2 sub-link (a)
(§5.4) pinned the outer constructor through `parseNode`; sub-link (b) (§5.5) lifted it across
`compose`. This link lifts brick 2(a) one level up the parser stack — through `parseDocument`'s
`prepareDocumentState` directive-skip, root-node dispatch, and `YamlDocument` wrap — so it is the
first half of the remaining `parseStream`/`parseStreamLoop`/`parseDocument` wrapping
(`parseStream_doc_from_parseDocument` supplies the loop half).

## Why this probe (the inhabitation-debt risk for a CONCLUSION lemma with TWO antecedents)

`parseDocument_flowSeqStart_produces_sequence` is a CONCLUSION
`(ps.peek? = some .flowSequenceStart) → (parseDocument ps = .ok (doc, ps')) → (composed-shape)`, so
Lean proves it TRUE — but a conclusion is worthless if its antecedents are never *jointly* satisfiable
on real data: it would type-check yet never fire. The R573 sharpening of the inhabitation-debt
discipline says TWO antecedents must be probed for **joint** satisfiability on the SAME real datum, not
separately. So the witnesses below all run on ONE `ParseState` per shape — `seqDocPS` / `mapDocPS` —
built from REAL emitted+scanned bytes (`emit` then `scanFiltered`, positioned just past
`streamStart`), exactly the state the first-document parse faces inside `parseStream`.

* `seqPSPeeksFlowSeqStart_fires` / `mapPSPeeksFlowMapStart_fires` — antecedent 1 is satisfiable: the
  real positioned state's lookahead IS `.flowSequenceStart` / `.flowMappingStart` (the emitter's
  leading `[` / `{`).
* `seqParseDocProducesFlowSeq_fires` / `mapParseDocProducesFlowMap_fires` — antecedent 2 is
  satisfiable JOINTLY with antecedent 1 on the SAME `seqDocPS` / `mapDocPS`: `parseDocument` succeeds
  there AND the resulting document's value is a flow collection with default tag/anchor — the lemma's
  conclusion shape, verified end-to-end on real bytes, so the lemma is NOT vacuously true.
* `seqDocPS_parseDocument_recovers_sequence` / `mapDocPS_parseDocument_recovers_mapping` — the actual
  lemma applied to the REAL positioned state, with both antecedents satisfiable by the witnesses
  above: a genuine, non-vacuous use lifting the outer shape through `parseDocument`.
-/

namespace ValueRecoveryParseDocument

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

/-- A REAL `ParseState` positioned at the document's first content token — built from the REAL
    emitted+scanned bytes of `seqValue`, advanced once past `streamStart`. This is exactly the state
    the first-document parse faces inside `parseStreamLoop`. (`default` is unreachable: scanning
    emitted output succeeds — witnessed below.) -/
def seqDocPS : ParseState :=
  match scanFiltered (emit seqValue) with
  | .ok tokens => ({ tokens := tokens } : ParseState).advance
  | .error _ => default

/-- Mirror: the real positioned state from the emitted+scanned bytes of `mapValue`. -/
def mapDocPS : ParseState :=
  match scanFiltered (emit mapValue) with
  | .ok tokens => ({ tokens := tokens } : ParseState).advance
  | .error _ => default

/-- Bool witness for antecedent 1: the real positioned state's lookahead IS `.flowSequenceStart`. -/
def seqPSPeeksFlowSeqStart : Bool :=
  match seqDocPS.peek? with
  | some .flowSequenceStart => true
  | _ => false

/-- Mirror: the real positioned mapping state's lookahead is `.flowMappingStart`. -/
def mapPSPeeksFlowMapStart : Bool :=
  match mapDocPS.peek? with
  | some .flowMappingStart => true
  | _ => false

-- Antecedent 1 of the parseDocument-dispatch lemmas is satisfiable on REAL positioned data.
theorem seqPSPeeksFlowSeqStart_fires : seqPSPeeksFlowSeqStart = true := by native_decide
theorem mapPSPeeksFlowMapStart_fires : mapPSPeeksFlowMapStart = true := by native_decide

/-- Bool witness for antecedent 2 JOINTLY with antecedent 1 on the SAME `seqDocPS`: `parseDocument`
    succeeds there AND the resulting document's value is a flow sequence with default tag/anchor —
    the lemma's conclusion shape, verified end-to-end on the same real positioned bytes whose
    lookahead `seqPSPeeksFlowSeqStart_fires` already pinned. -/
def seqParseDocProducesFlowSeq : Bool :=
  match parseDocument seqDocPS with
  | .ok (doc, _) =>
    match doc.value with
    | .sequence .flow _ none none => true
    | _ => false
  | .error _ => false

/-- Mirror: `parseDocument mapDocPS` succeeds and yields a flow mapping with default tag/anchor. -/
def mapParseDocProducesFlowMap : Bool :=
  match parseDocument mapDocPS with
  | .ok (doc, _) =>
    match doc.value with
    | .mapping .flow _ none none => true
    | _ => false
  | .error _ => false

-- Antecedent 2 holds JOINTLY with antecedent 1 on the SAME state: parseDocument recovers the shape.
theorem seqParseDocProducesFlowSeq_fires : seqParseDocProducesFlowSeq = true := by native_decide
theorem mapParseDocProducesFlowMap_fires : mapParseDocProducesFlowMap = true := by native_decide

/-- The actual lemma `parseDocument_flowSeqStart_produces_sequence` applied to the REAL positioned
    state. Both hypotheses are satisfiable here (witnessed jointly above), so this is a genuine,
    non-vacuous use: from the real `.flowSequenceStart` lookahead and a successful `parseDocument`,
    the lemma delivers a flow-sequence document value — the `parseDocument` link of brick 2's
    wrapping. -/
theorem seqDocPS_parseDocument_recovers_sequence
    (doc : YamlDocument) (ps' : ParseState)
    (h_peek : seqDocPS.peek? = some .flowSequenceStart)
    (h : parseDocument seqDocPS = .ok (doc, ps')) :
    ∃ items', doc.value = .sequence .flow items' none none :=
  parseDocument_flowSeqStart_produces_sequence seqDocPS doc ps' h_peek h

/-- Mirror: `parseDocument_flowMapStart_produces_mapping` applied to the REAL positioned mapping
    state. -/
theorem mapDocPS_parseDocument_recovers_mapping
    (doc : YamlDocument) (ps' : ParseState)
    (h_peek : mapDocPS.peek? = some .flowMappingStart)
    (h : parseDocument mapDocPS = .ok (doc, ps')) :
    ∃ pairs', doc.value = .mapping .flow pairs' none none :=
  parseDocument_flowMapStart_produces_mapping mapDocPS doc ps' h_peek h

-- Axiom audit — the source lemmas lift brick 2(a) through `parseDocument`'s directive-skip / root
-- dispatch / wrap, so they inherit brick 2(a)'s `Classical.choice` from the parser/`Except`-monad
-- simp machinery (same profile as bricks 1 / 2(a); brick 2(b) was leaner only because `compose`
-- never touches that machinery). NOT from `native_decide` (the firing probes above are separate and
-- carry `Lean.ofReduceBool` on top).
/-- info: 'L4YAML.Proofs.EmitterScannability.parseDocument_flowSeqStart_produces_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseDocument_flowSeqStart_produces_sequence

/-- info: 'L4YAML.Proofs.EmitterScannability.parseDocument_flowMapStart_produces_mapping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseDocument_flowMapStart_produces_mapping

end ValueRecoveryParseDocument
