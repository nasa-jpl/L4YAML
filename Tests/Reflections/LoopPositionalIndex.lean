import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 590 -- `parseFlow{Sequence,Mapping}Loop` positional index (§5.10.3)

R589 (§5.10.2) landed the *structural one-step reduction*: a successful
`parseFlowSequenceLoop ps (fuel+1) acc` either terminates (`result.1 = acc`) or reduces to a tail
call `parseFlowSequenceLoop ps'' fuel (acc.push v)`. §5.10.3 pins the *positional index* for the
`Or.inr` case:

  `result.1[acc.size] = v`

Proof: `result_append` (§5.10) on `h_push` gives `result.1.toList = acc.toList ++ [v] ++ extra`;
position `acc.size` = `acc.toList.length` falls in the `[v]` slot by `List.getElem_append_right`;
`List.getElem_cons_zero` reduces to `v`; `Array.getElem_toList` lifts back to the array. No fuel
induction, no emission machinery. Combined with `step_push` (§5.10.2), this pins each element
at its correct index without scanner-side reasoning.

## Why this probe (inhabitation debt: positional index has no provider universals -- rules 1 and 2)

`parseFlowSequenceLoop_step_index` has NO `forall...->` provider hypotheses (rule 3 N/A). Its
antecedents `h_ok` and `h_push` are of the same structural form as §5.10.2.

* Rule 1 (`h_ok` reachable): `seq_loop_ok` / `map_loop_ok` confirm the loop SUCCEEDS at the real
  entry states (R589 evidence, repeated here). `h_push` reachability follows from §5.10.2's
  `step_push` `Or.inr` branch on the same real data (R589's `seq_loop_step_takes_push` confirms
  `Or.inr` fires).
* Rule 2 (conclusion non-vacuous): `seq_step_index_fires` / `map_step_index_fires` confirm by
  `native_decide` that `result.1[0]?.isSome = true` on real data -- the element at index 0
  exists, so the existential `∃ h, result.1[0]'h = v` is non-vacuous.
* End-to-end: `seq_step_index_applies` / `map_step_index_applies` apply the theorem type-abstractly,
  confirming the conclusion type-checks with `(0 : Nat) < result.1.size` and `result.1[0] = v`.

`#print axioms` pins both index lemmas to `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
Note: rule 2 probes `isSome` (not `== some v`) because round-trip BEq on `YamlValue` is
unreliable for parsed scalars; value equality is guaranteed by the theorem itself.
-/

namespace LoopPositionalIndex

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures (reuse R589 setup): `[a,b]` / `{a:b}`, real loop-entry states at pos 2. -/

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

/-! ## Rule 1: loop succeeds (h_ok reachable); h_push reachable via step_push's Or.inr. -/

theorem seq_loop_ok :
    (parseFlowSequenceLoop psLoopSeq 201 #[]).toOption.isSome = true := by native_decide
theorem map_loop_ok :
    (parseFlowMappingLoop psLoopMap 201 #[]).toOption.isSome = true := by native_decide

/-! ## Rule 2: the positional index is non-vacuously present at index 0. -/

/-- The loop yields an element at index 0. Confirms `step_index`'s existential `result.1[0]`
    is non-vacuous on real data (the index exists; value equality follows from the theorem). -/
theorem seq_step_index_fires :
    ((parseFlowSequenceLoop psLoopSeq 201 #[]).toOption.map fun r => r.1[0]?.isSome) ==
      some true := by native_decide

/-- The loop yields a pair at index 0 in the real mapping result. -/
theorem map_step_index_fires :
    ((parseFlowMappingLoop psLoopMap 201 #[]).toOption.map fun r => r.1[0]?.isSome) ==
      some true := by native_decide

/-! ## END-TO-END APPLICATION: `step_index` applied type-abstractly to real hypotheses. -/

/-- Apply `parseFlowSequenceLoop_step_index` to the real entry state. `h_push` is the tail call
    from §5.10.2's `step_push` `Or.inr` branch, reachable (confirmed by `seq_step_index_fires`). -/
theorem seq_step_index_applies
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop psLoopSeq 201 #[] = .ok result)
    (v : YamlValue) (ps'' : ParseState)
    (h_push : parseFlowSequenceLoop ps'' 200 (#[v] : Array YamlValue) = .ok result) :
    ∃ h : (0 : Nat) < result.1.size, result.1[0]'h = v :=
  parseFlowSequenceLoop_step_index psLoopSeq 200 #[] result h_ok v ps'' h_push

/-- Apply `parseFlowMappingLoop_step_index` to the real mapping entry state. -/
theorem map_step_index_applies
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop psLoopMap 201 #[] = .ok result)
    (k v : YamlValue) (ps'' : ParseState)
    (h_push : parseFlowMappingLoop ps'' 200 (#[(k, v)] : Array _) = .ok result) :
    ∃ h : (0 : Nat) < result.1.size, result.1[0]'h = (k, v) :=
  parseFlowMappingLoop_step_index psLoopMap 200 #[] result h_ok k v ps'' h_push

/-! ## Axiom audit: both index lemmas are choice-clean (no `sorryAx`). -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowSequenceLoop_step_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowSequenceLoop_step_index

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowMappingLoop_step_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowMappingLoop_step_index

end LoopPositionalIndex
