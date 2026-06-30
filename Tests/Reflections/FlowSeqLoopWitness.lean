import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Proofs.Output.EmitterScannability.ScannerSpanLocality

/-!
# Reflection 602 -- parseStream flow-sequence loop witness (R602)

`parseStream_flowSeqStart_loop_witness` (§5.8a) threads the `parseStream` pipeline
backward to expose the underlying `parseFlowSequenceLoop` call and its result array:

  `∃ (items' : Array YamlValue) (ps_loop ps_doc : ParseState),`
  `  ps_doc.tokens = tokens ∧ ps_doc.pos = 2 ∧`
  `  parseFlowSequenceLoop ps_doc (4 * tokens.size + 2) #[] = .ok (items', ps_loop) ∧`
  `  raw_docs[0]!.value = .sequence .flow items' none none`

This witness is the bridge that lets R597 + R601 be threaded into the Front-B
sequence locality proof: R601 needs the loop call directly; R602 exposes it.

## Inhabitation-debt check

* **Rule 1** (antecedents reachable): token-array facts (`tks_ge2`, `tks_t1_fss`)
  are decidable and checked via `native_decide`.  Parse success is confirmed by
  the Bool computation `parse_ab_succeeds`.

* **Rule 2** (conclusion non-vacuous): `loop_witness_fires_bool` shows that
  `parseStream` on the concrete two-element sequence produces a raw `items'` array
  with the expected double-quoted scalar values.  `r602_outer_shape` shows the
  abstract theorem fires end-to-end.

* **Rule 3** does not apply (no provider universal in the precondition).
-/

namespace FlowSeqLoopWitness

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Concrete fixtures -/

def sc_a : Scalar := { content := "a", style := .plain }
def sc_b : Scalar := { content := "b", style := .plain }

def seqAB : YamlValue := .sequence .flow #[.scalar sc_a, .scalar sc_b] none none

def tks_ab : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqAB) with | .ok t => t | _ => #[]

/-! ## Rule 1: structural antecedents reachable on concrete sequence -/

theorem tks_ge2 : 1 < tks_ab.size := by native_decide

theorem tks_t1_fss : tks_ab[1]!.val = .flowSequenceStart := by native_decide

/-- Parse succeeds on the concrete token array (YamlDocument lacks DecidableEq, so we
    check via `.isOk` rather than asserting a concrete equality). -/
theorem parse_ab_succeeds : (parseStream tks_ab).isOk = true := by native_decide

/-! ## Rule 2: loop witness fires — value pin on concrete sequence -/

/-- Bool check: `parseStream` on `["a","b"]` gives a first raw document whose `.value`
    is a flow sequence with exactly the two double-quoted scalar values. -/
def loop_witness_fires_bool : Bool :=
  match parseStream tks_ab with
  | .ok raw_docs =>
    match raw_docs[0]!.value with
    | .sequence .flow items' _ _ =>
      (items'.size == 2) &&
      (items'[0]! == .scalar (.mk "a" .doubleQuoted none none none)) &&
      (items'[1]! == .scalar (.mk "b" .doubleQuoted none none none))
    | _ => false
  | .error _ => false

theorem loop_witness_fires : loop_witness_fires_bool = true := by native_decide

/-! ## Abstract application of R602 -/

/-- R602 exposes the flow-sequence outer shape: given a successful `parseStream`
    with flow-sequence-start at token[1], the first raw document has flow-sequence
    shape and the items array is the direct result of `parseFlowSequenceLoop`. -/
theorem r602_outer_shape
    (tokens : Array (Positioned YamlToken)) (raw_docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok raw_docs)
    (h_ne : 0 < raw_docs.size) (h_lt : 1 < tokens.size)
    (h_t1 : tokens[1]!.val = .flowSequenceStart) :
    ∃ (items' : Array YamlValue) (ps_loop ps_doc : ParseState),
      ps_doc.tokens = tokens ∧ ps_doc.pos = 2 ∧
      parseFlowSequenceLoop ps_doc (4 * tokens.size + 2) #[] = .ok (items', ps_loop) ∧
      raw_docs[0]!.value = .sequence .flow items' none none :=
  parseStream_flowSeqStart_loop_witness tokens raw_docs h_parse h_ne h_lt h_t1

/-! ## Axiom audit: R602 depends on [propext, Classical.choice, Quot.sound] -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseStream_flowSeqStart_loop_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseStream_flowSeqStart_loop_witness

end FlowSeqLoopWitness
