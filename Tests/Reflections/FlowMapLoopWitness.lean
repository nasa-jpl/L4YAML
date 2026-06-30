import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 605 -- parseStream flow-mapping loop witness (R605)

`parseStream_flowMapStart_loop_witness` (§5.8b) threads the `parseStream` pipeline
backward to expose the underlying `parseFlowMappingLoop` call and its result array:

  `∃ (pairs' : Array (YamlValue × YamlValue)) (ps_loop ps_doc : ParseState),`
  `  ps_doc.tokens = tokens ∧ ps_doc.pos = 2 ∧`
  `  parseFlowMappingLoop ps_doc (4 * tokens.size + 2) #[] = .ok (pairs', ps_loop) ∧`
  `  raw_docs[0]!.value = .mapping .flow pairs' none none`

Mirror of R602 (`parseStream_flowSeqStart_loop_witness`, §5.8a) for the mapping axis.
This witness bridges `h_parse` to the per-pair value pins needed by the all-scalar branch
of `emit_roundtrip_mapping_content_eq`: R605 exposes `pairs'`; scanner-span-locality for
mapping pairs will pin `pairs'[j]!`; `compose_map_scalar_pair` (R604) then closes
`(pairs''[j]!).fst/snd`.

## Inhabitation-debt check

* **Rule 1** (antecedents reachable): token-array facts (`tks_ge2`, `tks_t1_fms`)
  are decidable and checked via `native_decide`.  Parse success is confirmed by
  the Bool computation `parse_kv_succeeds`.

* **Rule 2** (conclusion non-vacuous): `loop_witness_fires_bool` shows that
  `parseStream` on the concrete singleton mapping produces a raw `pairs'` array
  with the expected double-quoted scalar key and value.  `r605_outer_shape` shows the
  abstract theorem fires end-to-end.

* **Rule 3** does not apply (no provider universal in the precondition).
-/

namespace FlowMapLoopWitness

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Concrete fixtures -/

def k : YamlValue := .scalar { content := "k", style := .plain }
def v : YamlValue := .scalar { content := "v", style := .plain }
def mapKV : YamlValue := .mapping .flow #[(k, v)] none none

def tks_kv : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapKV) with | .ok t => t | _ => #[]

/-! ## Rule 1: structural antecedents reachable on concrete mapping -/

theorem tks_ge2 : 1 < tks_kv.size := by native_decide

theorem tks_t1_fms : tks_kv[1]!.val = .flowMappingStart := by native_decide

/-- Parse succeeds on the concrete token array (YamlDocument lacks DecidableEq, so we
    check via `.isOk` rather than asserting a concrete equality). -/
theorem parse_kv_succeeds : (parseStream tks_kv).isOk = true := by native_decide

/-! ## Rule 2: loop witness fires -- value pin on concrete mapping -/

/-- Bool check: `parseStream` on `{"k": "v"}` gives a first raw document whose `.value`
    is a flow mapping with exactly the one double-quoted scalar key-value pair. -/
def loop_witness_fires_bool : Bool :=
  match parseStream tks_kv with
  | .ok raw_docs =>
    match raw_docs[0]!.value with
    | .mapping .flow pairs' _ _ =>
      (pairs'.size == 1) &&
      (pairs'[0]!.1 == .scalar (.mk "k" .doubleQuoted none none none)) &&
      (pairs'[0]!.2 == .scalar (.mk "v" .doubleQuoted none none none))
    | _ => false
  | .error _ => false

theorem loop_witness_fires : loop_witness_fires_bool = true := by native_decide

/-! ## Abstract application of R605 -/

/-- R605 exposes the flow-mapping outer shape: given a successful `parseStream`
    with flow-mapping-start at token[1], the first raw document has flow-mapping
    shape and the pairs array is the direct result of `parseFlowMappingLoop`. -/
theorem r605_outer_shape
    (tokens : Array (Positioned YamlToken)) (raw_docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok raw_docs)
    (h_ne : 0 < raw_docs.size) (h_lt : 1 < tokens.size)
    (h_t1 : tokens[1]!.val = .flowMappingStart) :
    ∃ (pairs' : Array (YamlValue × YamlValue)) (ps_loop ps_doc : ParseState),
      ps_doc.tokens = tokens ∧ ps_doc.pos = 2 ∧
      parseFlowMappingLoop ps_doc (4 * tokens.size + 2) #[] = .ok (pairs', ps_loop) ∧
      raw_docs[0]!.value = .mapping .flow pairs' none none :=
  parseStream_flowMapStart_loop_witness tokens raw_docs h_parse h_ne h_lt h_t1

/-! ## Axiom audit: R605 depends on [propext, Classical.choice, Quot.sound] -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseStream_flowMapStart_loop_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseStream_flowMapStart_loop_witness

end FlowMapLoopWitness
