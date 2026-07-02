import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 573 — INHABITATION PROBE for Front B's value-recovery trace, brick 2 sub-link (a)

This file is the inhabitation test the [[feedback-inhabitation-debt-validate-target-defs]] discipline
demands for **brick 2 sub-link (a)** of Front B — the `parseNode`-dispatch lemmas
`parseNode_flowSeqStart_produces_sequence` / `parseNode_flowMapStart_produces_mapping` (in
`ContentFidelity.lean` §5.4). They lift brick 1's outer-shape recovery (§5.3) up one level of the
parser stack: a successful `parseNode` whose lookahead is `.flowSequenceStart` / `.flowMappingStart`
produces `.sequence .flow _ none none` / `.mapping .flow _ none none` (properties skip, content
dispatches to the flow parser, `applyNodeFinalization` is identity on the `none none` slots).

## Why this probe (the inhabitation-debt risk for a CONCLUSION lemma with TWO antecedents)

The dispatch lemmas are CONCLUSIONS, so Lean proves them TRUE — but a conclusion
`(h_peek) → (parseNode … = .ok …) → (shape)` is worthless if the two antecedents are never JOINTLY
satisfiable on real data: it would type-check yet never fire. So the genuine probe confirms, on REAL
emitted bytes, that BOTH antecedents hold at once — the real scan-derived `ParseState`'s lookahead
IS `.flowSequenceStart`/`.flowMappingStart`, AND `parseNode` on it returns `.ok` of the matching flow
shape — then applies the actual lemma non-vacuously. We ground on `emit`ted output (exactly what
sorries 3/4 face), not a hand-typed literal. This sharpens the R572 (brick 1) probe: brick 1's lemma
had ONE antecedent (`parseFlowSequence … = .ok …`); brick 2 adds the `h_peek` antecedent, so the
inhabitation obligation is the JOINT satisfiability of both, witnessed here.

* `seqPS_peek_flowSeqStart` / `mapPS_peek_flowMapStart` — antecedent 1 (`h_peek`) is satisfiable:
  the real scan-derived state's lookahead is the flow-collection-start token.
* `seqNodeDispatch_fires` / `mapNodeDispatch_fires` — antecedent 2 fires non-vacuously: the real
  `parseNode` returns `.ok` of `.sequence .flow _ none none` / `.mapping .flow _ none none`.
* `seqPS_node_recovers_sequence` / `mapPS_node_recovers_mapping` — the actual lemma applied to the
  REAL state, with `h_peek` discharged by the firing-confirmed witness above.
-/

namespace ValueRecoveryNodeDispatch

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

/-- A `ParseState` positioned at the opening `[` (index 1, just past `streamStart`) — exactly the
    state `parseNode` faces when its content dispatch reaches the flow sequence. -/
def seqPS : ParseState := { tokens := seqTokens, pos := 1 }

/-- A `ParseState` positioned at the opening `{`. -/
def mapPS : ParseState := { tokens := mapTokens, pos := 1 }

-- Antecedent 1 (`h_peek`) is satisfiable on REAL data: the scan-derived lookahead is the
-- flow-collection-start token. (`YamlToken` derives `DecidableEq`, so `native_decide` applies.)
theorem seqPS_peek_flowSeqStart : seqPS.peek? = some .flowSequenceStart := by native_decide
theorem mapPS_peek_flowMapStart : mapPS.peek? = some .flowMappingStart := by native_decide

/-- Bool witness: the real `parseNode` on emitted `["x"]` returns `.ok` of a flow sequence with
    default tag/anchor — exactly the lemma's conclusion shape, on real data. -/
def seqNodeDispatchFires : Bool :=
  match parseNode seqPS (4 * seqTokens.size + 4) with
  | .ok (.sequence .flow _ none none, _) => true
  | _ => false

/-- Bool witness: the real `parseNode` on emitted `{"a":"b"}` returns `.ok` of a flow mapping. -/
def mapNodeDispatchFires : Bool :=
  match parseNode mapPS (4 * mapTokens.size + 4) with
  | .ok (.mapping .flow _ none none, _) => true
  | _ => false

-- Antecedent 2 fires non-vacuously: jointly with the peek witnesses above, both antecedents of
-- the dispatch lemmas hold on the SAME real emitted output, so the lemmas are NOT vacuously true.
theorem seqNodeDispatch_fires : seqNodeDispatchFires = true := by native_decide
theorem mapNodeDispatch_fires : mapNodeDispatchFires = true := by native_decide

/-- The actual lemma `parseNode_flowSeqStart_produces_sequence` applied to the REAL scan-derived
    state. Both its hypotheses are satisfiable here (witnessed by `seqPS_peek_flowSeqStart` and
    `seqNodeDispatch_fires`), so this is a genuine, non-vacuous use: from the real `.ok` the lemma
    delivers the flow-sequence shape. -/
theorem seqPS_node_recovers_sequence
    (v : YamlValue) (ps' : ParseState)
    (h : parseNode seqPS (4 * seqTokens.size + 4) = .ok (v, ps')) :
    ∃ items', v = .sequence .flow items' none none :=
  parseNode_flowSeqStart_produces_sequence _ _ _ _ seqPS_peek_flowSeqStart h

/-- Mirror: `parseNode_flowMapStart_produces_mapping` applied to the REAL mapping state. -/
theorem mapPS_node_recovers_mapping
    (v : YamlValue) (ps' : ParseState)
    (h : parseNode mapPS (4 * mapTokens.size + 4) = .ok (v, ps')) :
    ∃ pairs', v = .mapping .flow pairs' none none :=
  parseNode_flowMapStart_produces_mapping _ _ _ _ mapPS_peek_flowMapStart h

-- Axiom audit — the source lemmas are structural unfolds over brick 1; `Classical.choice` is
-- inherited from the parser/`Except`-monad simp machinery they unfold (same profile as brick 1),
-- NOT from `native_decide` (the `native_decide` firing probes above are separate and carry
-- `Lean.ofReduceBool` on top).
/-- info: 'L4YAML.Proofs.EmitterScannability.parseNode_flowSeqStart_produces_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseNode_flowSeqStart_produces_sequence

/-- info: 'L4YAML.Proofs.EmitterScannability.parseNode_flowMapStart_produces_mapping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms parseNode_flowMapStart_produces_mapping

end ValueRecoveryNodeDispatch
