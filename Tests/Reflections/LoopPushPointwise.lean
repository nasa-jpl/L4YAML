import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 592 -- `parseFlow{Sequence,Mapping}Loop` element-value join (§5.10.5)

R591 (§5.10.4) pinned the indexed sub-call witness: for each `j`, a sub-call `(ps_j, acc_j)` with
`acc_j.toList = result.1.toList.take (j+1)`.  §5.10.5 supplies the element-value join: the concrete
value `v` pushed at step `j`, together with explicit pre- and post-push sub-calls that bracket it.

Key craft note (off-by-one in the combine):  `push_subwit` at `j` gives `acc_j.size = j+1` (NOT `j`),
so `step_index` on that sub-call yields `result.1[j+1] = v`, not `result.1[j]`.  The correct combine
for `result.1[j]` requires `push_subwit(j-1)` (giving `acc_{j-1}.size = j`) then `step_push + step_index`.
`push_pointwise` re-derives this by direct fuel induction, avoiding the two-step indirection.

The conclusion uses bang-indexing `result.1[j]! = v` so no dependent bound appears in the `∃`.

## Inhabitation debt: rules 1 and 2 apply; rule 3 N/A

Neither theorem has `∀ P, (∀ x, P x) → ...` provider universals (rule 3 does not apply).

* Rule 1 (`h_ok` reachable): `seq_loop_ok` / `map_loop_ok` confirm loop succeeds on real data.
* Rule 2 (conclusion non-vacuous): `seq_result_nonempty` confirms `result.1.size != 0`, so `j = 0`
  lies in `[0, result.1.size)` and the existential is non-vacuous.
* End-to-end: `seq_pointwise_j0_applies` / `map_pointwise_j0_applies` apply each theorem type-abstractly.

`#print axioms` confirms both `push_pointwise` variants pull `Classical.choice` via `by_cases`
(same as `push_subwit`): axiom set `[propext, Classical.choice, Quot.sound]`.
-/

namespace LoopPushPointwise

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: `[a,b]` / `{a:b}`, same as R590--R591. -/

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

/-! ## Rule 1: loop succeeds (h_ok antecedent reachable). -/

theorem seq_loop_ok :
    (parseFlowSequenceLoop psLoopSeq 201 #[]).toOption.isSome = true := by native_decide
theorem map_loop_ok :
    (parseFlowMappingLoop psLoopMap 201 #[]).toOption.isSome = true := by native_decide

/-! ## Rule 2: conclusion non-vacuous (j = 0 in range). -/

/-- Result is non-empty so `j = 0` lies in `[0, result.1.size)` -- the existential is non-vacuous. -/
theorem seq_result_nonempty :
    ((parseFlowSequenceLoop psLoopSeq 201 #[]).toOption.map fun r => r.1.size != 0) ==
      some true := by native_decide

theorem map_result_nonempty :
    ((parseFlowMappingLoop psLoopMap 201 #[]).toOption.map fun r => r.1.size != 0) ==
      some true := by native_decide

/-! ## END-TO-END APPLICATION: apply theorems type-abstractly at j = 0. -/

/-- `push_pointwise` applied to the real sequence entry at `j = 0`.  Witnesses `ps_j = psLoopSeq`,
    `acc_j = #[]` (covering 0 elements), `acc_j.push v = #[a]`, `result.1[0]! = a`.
    `seq_result_nonempty` confirms `hj_lt` is reachable. -/
theorem seq_pointwise_j0_applies
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop psLoopSeq 201 #[] = .ok result)
    (hj_lt : 0 < result.1.size) :
    ∃ (ps_j ps_j' : ParseState) (fuel_j : Nat) (v : YamlValue) (acc_j : Array YamlValue),
      acc_j.toList = result.1.toList.take 0 ∧
      parseFlowSequenceLoop ps_j (fuel_j + 1) acc_j = .ok result ∧
      parseFlowSequenceLoop ps_j' fuel_j (acc_j.push v) = .ok result ∧
      result.1[0]! = v :=
  parseFlowSequenceLoop_push_pointwise psLoopSeq 201 #[] result h_ok 0 (Nat.zero_le _) hj_lt

/-- `push_pointwise` applied to the real mapping entry at `j = 0`.  Witness pair `(a, b)`. -/
theorem map_pointwise_j0_applies
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop psLoopMap 201 #[] = .ok result)
    (hj_lt : 0 < result.1.size) :
    ∃ (ps_j ps_j' : ParseState) (fuel_j : Nat) (mkey mval : YamlValue)
      (acc_j : Array (YamlValue × YamlValue)),
      acc_j.toList = result.1.toList.take 0 ∧
      parseFlowMappingLoop ps_j (fuel_j + 1) acc_j = .ok result ∧
      parseFlowMappingLoop ps_j' fuel_j (acc_j.push (mkey, mval)) = .ok result ∧
      result.1[0]! = (mkey, mval) :=
  parseFlowMappingLoop_push_pointwise psLoopMap 201 #[] result h_ok 0 (Nat.zero_le _) hj_lt

/-! ## Axiom audit: both variants pull Classical.choice via by_cases. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowSequenceLoop_push_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowSequenceLoop_push_pointwise

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowMappingLoop_push_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowMappingLoop_push_pointwise

end LoopPushPointwise
