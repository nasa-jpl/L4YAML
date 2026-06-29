import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 588 — `parseFlow{Sequence,Mapping}Loop` per-element invariant (§5.10.1): the value-half
  spine of brick 3's content half.

R587 (§5.4.1) landed the parser-side *dispatch leaf* (a scalar lookahead pins a scalar value). The next
parser-side brick is the loop *induction*'s value-half spine. §5.10 already proved the loop only
APPENDS (`parseFlowSequenceLoop_result_append`: `result.toList = acc.toList ++ extra`), but its `extra`
is existential and says nothing about the elements. §5.10.1 adds the parametric **per-element
invariant**: any property `P` that holds of the accumulator AND of every `parseNode` /
`parseSinglePairMapping` (sequence) / `parseFlowMappingValue` (mapping) output, holds of every element
of the loop result. It is the parser-side analogue of the block loop's `Scannable`-tracking induction
(`parseBlockSequenceLoop_wb`), generalized over an arbitrary `P` — proved by the SAME fuel induction as
§5.10 (emission-independent, scanner-free; the smallest-first value-half spine), every recursion branch
lifting `P` over `acc.push w` via `Array.mem_push`.

## Why this probe (inhabitation debt: `h_node` / `h_pair` are `∀`-quantified PROVIDER HYPOTHESES — the
  "only ever a hypothesis" alarm, rule 3, applied to MY hypotheses)

`parseFlowSequenceLoop_all` is a verified implication (no inhabitation debt of its own), but its key
hypotheses `h_node : ∀ ps f v ps', parseNode ps f = .ok (v, ps') → P v` (and `h_pair`, and the mapping
twin's `h_implicit` / `h_explicit`) are universals over EVERY parser output. Per
[[inhabitation-debt-validate-target-defs]] rule 3 / R542 (a proven assembler's new `∀…→…` provider
hypothesis is the alarm to EXHIBIT it dischargeable), the probe must show those hypotheses are genuinely
satisfiable into a NON-TRIVIAL conclusion — not vacuously, and not only for `P := True`.

* `seq_loop_succeeds` / `map_loop_succeeds` `native_decide` that the loop SUCCEEDS at the real
  loop-entry states (`[a,b]` / `{a:b}` after the bracket-open marker) — so the lemma's `h_ok` antecedent
  is reachable on genuine emission data, not vacuous.
* `seq_loop_recovers_two` / `map_loop_recovers_one` `native_decide` that the real loop result has 2 / 1
  elements — so the conclusion `∀ v ∈ result.1, P v` ranges over a NON-EMPTY domain (rule 2: a membership
  invariant over an empty array proves nothing; here it fires over real recovered elements).
* `seq_loop_all_applies` / `map_loop_all_applies` instantiate the lemma on the real loop-entry state with
  `P := True` (all provider hypotheses discharged trivially) — the END-TO-END application type-checks.
* `seq_loop_provenance` / `map_loop_provenance` are the genuine rule-3 firing: instantiate with a
  NON-TRIVIAL `P` (the value/pair came from a successful `parseNode` / `parseSinglePairMapping` /
  `parseFlowMappingValue` call) and DISCHARGE every provider hypothesis (`Or.inl`/`Or.inr` with the
  parse witness). The universal hypotheses are not just assumed — they are proved, into a useful
  provenance conclusion the locality producer will refine with positional bookkeeping.
* `seq_loop_provenance_empty` / `map_loop_provenance_empty` are the rule-2 boundary: fire the provenance
  corollary at `fuel = 0` (loop returns the accumulator verbatim), conclusion vacuous over `#[]`.

`#print axioms` pins both invariants to `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); the
`native_decide` grounding theorems add the compiler-reflection axioms transitively — `#print axioms`
it, never assume.
-/

namespace LoopElementInvariant

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: a flow sequence `[a,b]` and flow mapping `{a:b}`; the real loop-entry `ParseState`s
    (pos 2, just past `flowSequenceStart` / `flowMappingStart`, accumulator `#[]`). -/

def a : YamlValue := .scalar { content := "a", style := .plain }
def b : YamlValue := .scalar { content := "b", style := .plain }
def seqAB : YamlValue := .sequence .flow #[a, b] none none
def mapAB : YamlValue := .mapping .flow #[(a, b)] none none

def tksSeq : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqAB) with | .ok t => t | _ => #[]
def tksMap : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapAB) with | .ok t => t | _ => #[]

def psLoopSeq : ParseState := { tokens := tksSeq, pos := 2 }
def psLoopMap : ParseState := { tokens := tksMap, pos := 2 }

/-! ## NON-VACUITY of `h_ok` (rule 3): the loop SUCCEEDS at the real entry states. -/

theorem seq_loop_succeeds :
    (parseFlowSequenceLoop psLoopSeq 200 #[]).toOption.isSome = true := by native_decide
theorem map_loop_succeeds :
    (parseFlowMappingLoop psLoopMap 200 #[]).toOption.isSome = true := by native_decide

/-! ## NON-VACUITY of the conclusion DOMAIN (rule 2): the real loop recovers 2 / 1 elements, so
    `∀ v ∈ result.1, P v` is not a statement about the empty array. -/

theorem seq_loop_recovers_two :
    ((parseFlowSequenceLoop psLoopSeq 200 #[]).toOption.map (·.1.size) == some 2) = true := by
  native_decide
theorem map_loop_recovers_one :
    ((parseFlowMappingLoop psLoopMap 200 #[]).toOption.map (·.1.size) == some 1) = true := by
  native_decide

/-! ## END-TO-END application on the real loop-entry state (`P := True`; all provider hypotheses
    discharged trivially) — the lemma fires top-to-bottom on genuine data. -/

theorem seq_loop_all_applies (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop psLoopSeq 200 #[] = .ok result) :
    ∀ v ∈ result.1, True :=
  parseFlowSequenceLoop_all (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    psLoopSeq 200 #[] result (by intro v hv; simp at hv) h_ok

theorem map_loop_all_applies (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop psLoopMap 200 #[] = .ok result) :
    ∀ v ∈ result.1, True :=
  parseFlowMappingLoop_all (fun _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    psLoopMap 200 #[] result (by intro v hv; simp at hv) h_ok

/-! ## THE GENUINE RULE-3 FIRING: a NON-TRIVIAL `P` (provenance) with every provider hypothesis
    DISCHARGED — the universals are proved, not assumed, into a useful conclusion. -/

/-- Every recovered sequence element came from a successful `parseNode` (plain entry) or
    `parseSinglePairMapping` (implicit-mapping `.key` entry). -/
def SeqProvenance (v : YamlValue) : Prop :=
  (∃ ps f ps', parseNode ps f = .ok (v, ps')) ∨
  (∃ ps f ps', parseSinglePairMapping ps f = .ok (v, ps'))

theorem seq_loop_provenance (ps : ParseState) (fuel : Nat) (acc : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_acc : ∀ v ∈ acc, SeqProvenance v)
    (h_ok : parseFlowSequenceLoop ps fuel acc = .ok result) :
    ∀ v ∈ result.1, SeqProvenance v :=
  parseFlowSequenceLoop_all SeqProvenance
    (fun ps f _ ps' h => Or.inl ⟨ps, f, ps', h⟩)
    (fun ps f _ ps' h => Or.inr ⟨ps, f, ps', h⟩)
    ps fuel acc result h_acc h_ok

/-- Every recovered mapping pair has a key from `parseNode` (implicit) or `parseExplicitKey` (explicit)
    and a value from `parseFlowMappingValue`. -/
def MapProvenance (kv : YamlValue × YamlValue) : Prop :=
  (∃ ps f ps' ps2 sp kc ps3,
    parseNode ps f = .ok (kv.1, ps') ∧ parseFlowMappingValue ps2 f sp kc = .ok (kv.2, ps3)) ∨
  (∃ ps f ps' ps2 sp kc ps3,
    parseExplicitKey ps f = .ok (kv.1, ps') ∧ parseFlowMappingValue ps2 f sp kc = .ok (kv.2, ps3))

theorem map_loop_provenance (ps : ParseState) (fuel : Nat) (acc : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_acc : ∀ v ∈ acc, MapProvenance v)
    (h_ok : parseFlowMappingLoop ps fuel acc = .ok result) :
    ∀ v ∈ result.1, MapProvenance v :=
  parseFlowMappingLoop_all MapProvenance
    (fun ps f _ ps' ps2 sp kc _ ps3 hk hv => Or.inl ⟨ps, f, ps', ps2, sp, kc, ps3, hk, hv⟩)
    (fun ps f _ ps' ps2 sp kc _ ps3 hk hv => Or.inr ⟨ps, f, ps', ps2, sp, kc, ps3, hk, hv⟩)
    ps fuel acc result h_acc h_ok

/-! ## BOUNDARY (rule 2): fire the provenance corollary at `fuel = 0` — the loop returns the
    accumulator verbatim, so the conclusion is vacuous over the empty accumulator. -/

theorem seq_loop_provenance_empty (ps : ParseState)
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop ps 0 #[] = .ok result) :
    ∀ v ∈ result.1, SeqProvenance v :=
  seq_loop_provenance ps 0 #[] result (by intro v hv; simp at hv) h_ok

theorem map_loop_provenance_empty (ps : ParseState)
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop ps 0 #[] = .ok result) :
    ∀ v ∈ result.1, MapProvenance v :=
  map_loop_provenance ps 0 #[] result (by intro v hv; simp at hv) h_ok

/-! ## Axiom audit: both invariants are choice-clean (no `sorryAx`). -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowSequenceLoop_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowSequenceLoop_all

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowMappingLoop_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowMappingLoop_all

end LoopElementInvariant
