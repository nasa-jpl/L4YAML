import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 577 — INHABITATION PROBE for Front B's value-recovery trace, brick 2 ASSEMBLED

This file is the inhabitation test the [[feedback-inhabitation-debt-validate-target-defs]] discipline
demands for the **assembled outer-shape recovery** lemmas
`parseStream_flow{Seq,Map}Start_recovers_outer_shape` (in `ContentFidelity.lean` §5.8). Those compose
§5.7 (first-document position-pinning) -> §5.6 (`parseDocument` dispatch) -> §5.5 (`compose` preserves
the head) into the full outer-shape half of the trace: a successful `parseStream` whose position-1
lookahead is the flow opener recovers a composed first document whose value is a flow collection with
default tag/anchor.

## Why this probe (the inhabitation-debt risk for a CONCLUSION lemma with FOUR antecedents)

Each §5.8 lemma is a CONCLUSION
`(parseStream tokens = .ok raw_docs) -> (0 < raw_docs.size) -> (1 < tokens.size) ->
 (tokens[1]!.val = .flowSequenceStart) -> (exists items'', ...)`,
so Lean proves it TRUE -- but a conclusion is worthless if its antecedents are never *jointly*
satisfiable on real data: it would type-check yet never fire. The R573 sharpening of the
inhabitation-debt discipline says MULTIPLE antecedents must be probed for **joint** satisfiability on
the SAME real datum. Here there are FOUR, so the witness below checks all four at once on ONE token
array per shape -- `seqTokens` / `mapTokens` -- built from REAL emitted+scanned bytes (`emit` then
`scanFiltered`), exactly what `parseYamlRaw` feeds the parser.

* `seqAllAntecedents_fires` / `mapAllAntecedents_fires` — all FOUR antecedents hold JOINTLY on the SAME
  `seqTokens` / `mapTokens`: `parseStream` succeeds (the `.ok` branch), the document array is non-empty,
  the token array has more than one element, AND its position-1 token is the flow opener. The lemma is
  therefore NOT vacuously true.
* `seqOuterShapeIsFlowSeq_fires` / `mapOuterShapeIsFlowMap_fires` — the CONCLUSION is meaningful and
  matches reality: end-to-end on real bytes the composed first document IS a flow sequence / mapping
  with default tag/anchor — exactly the `exists items''/pairs'', ... = .sequence/.mapping .flow _ none none`
  the lemma claims. Outer-shape recovery is not idle.
* `seqTokens_outer_shape_recovered` / `mapTokens_outer_shape_recovered` — the actual §5.8 lemma applied
  to the REAL token arrays, with all four antecedents satisfiable by the witnesses above: a genuine,
  non-vacuous use recovering the outer flow shape of the composed first document. This is the entire
  outer-shape half of Front B's trace firing on real data; only the per-element body (brick 3) remains.
-/

namespace ValueRecoveryOuterShapeAssembled

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

/-- REAL tokens from the emitted+scanned bytes of `seqValue` — exactly what `parseStream` parses.
    (`#[]` is unreachable: scanning emitter output succeeds, witnessed by `seqAllAntecedents_fires`.) -/
def seqTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqValue) with
  | .ok t => t
  | .error _ => #[]

/-- Mirror: REAL tokens from the emitted+scanned bytes of `mapValue`. -/
def mapTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapValue) with
  | .ok t => t
  | .error _ => #[]

/-- All FOUR antecedents of `parseStream_flowSeqStart_recovers_outer_shape` JOINTLY on the SAME
    `seqTokens`: `parseStream` succeeds (`.ok` branch), `0 < raw_docs.size`, `1 < seqTokens.size`,
    and `seqTokens[1]!.val = .flowSequenceStart`. -/
def seqAllAntecedents : Bool :=
  match parseStream seqTokens with
  | .ok raw_docs =>
    (0 < raw_docs.size) &&
    (1 < seqTokens.size) &&
    (match seqTokens[1]!.val with | .flowSequenceStart => true | _ => false)
  | .error _ => false

/-- Mirror for the mapping token array (position-1 token is `.flowMappingStart`). -/
def mapAllAntecedents : Bool :=
  match parseStream mapTokens with
  | .ok raw_docs =>
    (0 < raw_docs.size) &&
    (1 < mapTokens.size) &&
    (match mapTokens[1]!.val with | .flowMappingStart => true | _ => false)
  | .error _ => false

theorem seqAllAntecedents_fires : seqAllAntecedents = true := by native_decide
theorem mapAllAntecedents_fires : mapAllAntecedents = true := by native_decide

/-- The CONCLUSION is meaningful and matches reality: end-to-end on real bytes the composed first
    document is a flow sequence with default tag/anchor — exactly the shape §5.8 recovers. -/
def seqOuterShapeIsFlowSeq : Bool :=
  match parseStream seqTokens with
  | .ok raw_docs =>
    match (raw_docs.map YamlDocument.compose)[0]!.value with
    | .sequence .flow _ none none => true
    | _ => false
  | .error _ => false

/-- Mirror: the composed first document on the mapping bytes is a flow mapping with default
    tag/anchor. -/
def mapOuterShapeIsFlowMap : Bool :=
  match parseStream mapTokens with
  | .ok raw_docs =>
    match (raw_docs.map YamlDocument.compose)[0]!.value with
    | .mapping .flow _ none none => true
    | _ => false
  | .error _ => false

theorem seqOuterShapeIsFlowSeq_fires : seqOuterShapeIsFlowSeq = true := by native_decide
theorem mapOuterShapeIsFlowMap_fires : mapOuterShapeIsFlowMap = true := by native_decide

/-- The actual lemma `parseStream_flowSeqStart_recovers_outer_shape` applied to the REAL `seqTokens`.
    All four hypotheses are satisfiable here (witnessed jointly by `seqAllAntecedents_fires`), so this
    is a genuine, non-vacuous use: a successful `parseStream` with a non-empty document array and a
    position-1 flow opener recovers a composed first document whose value is a flow sequence — the
    entire outer-shape half of Front B's value-recovery trace, on real data. -/
theorem seqTokens_outer_shape_recovered
    (raw_docs : Array YamlDocument)
    (h_parse : parseStream seqTokens = .ok raw_docs)
    (h_ne : 0 < raw_docs.size)
    (h_lt : 1 < seqTokens.size)
    (h_head : seqTokens[1]!.val = .flowSequenceStart) :
    ∃ items'', (raw_docs.map YamlDocument.compose)[0]!.value = .sequence .flow items'' none none :=
  parseStream_flowSeqStart_recovers_outer_shape seqTokens raw_docs h_parse h_ne h_lt h_head

/-- Mirror: the lemma applied to the REAL mapping token array. -/
theorem mapTokens_outer_shape_recovered
    (raw_docs : Array YamlDocument)
    (h_parse : parseStream mapTokens = .ok raw_docs)
    (h_ne : 0 < raw_docs.size)
    (h_lt : 1 < mapTokens.size)
    (h_head : mapTokens[1]!.val = .flowMappingStart) :
    ∃ pairs'', (raw_docs.map YamlDocument.compose)[0]!.value = .mapping .flow pairs'' none none :=
  parseStream_flowMapStart_recovers_outer_shape mapTokens raw_docs h_parse h_ne h_lt h_head

-- Axiom audit — the assembled outer-shape lemmas route through §5.7's position-pinning
-- (`parseStream_first_doc_at_pos_one`, carrying `Classical.choice` from the `Except`-monad simp) plus
-- the §5.6 / §5.5 links and the `Array.map` / `getElem!` bridge, so both carry the same
-- `[propext, Classical.choice, Quot.sound]` profile as the §5.7 traces. They do NOT depend on
-- `Lean.ofReduceBool` (the firing probes above are separate `native_decide` lemmas).
/-- info: 'L4YAML.Proofs.EmitterScannability.parseStream_flowSeqStart_recovers_outer_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseStream_flowSeqStart_recovers_outer_shape

/-- info: 'L4YAML.Proofs.EmitterScannability.parseStream_flowMapStart_recovers_outer_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseStream_flowMapStart_recovers_outer_shape

end ValueRecoveryOuterShapeAssembled
