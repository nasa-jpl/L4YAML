import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 589 -- `parseFlow{Sequence,Mapping}Loop` one-step structural reduction (§5.10.2)

R588 (§5.10.1) landed the *value-half spine*: any property `P` closed under the loop's parse branches
holds of every element in the result (membership invariant; index-blind). The membership invariant is
EXACTLY index-blind -- it says every element satisfies `P`, but says nothing about WHICH parse call
produced element `i`. The positional join peeling off element `i` needs to step the loop one iteration
at a time. §5.10.2 supplies that STRUCTURAL step:

  `parseFlowSequenceLoop ps (fuel+1) acc = .ok result` -->
  result.1 = acc  OR  exists v ps'', parseFlowSequenceLoop ps'' fuel (acc.push v) = .ok result

Purely structural: no fuel induction, no emission machinery, no scanner reasoning. Separator-advance
and path-push/pop bookkeeping live inside the proof; the conclusion sees only `v`, `ps''`, and the tail
call. The provenance of `v` (from `parseNode` or `parseSinglePairMapping`) is captured by §5.10.1's
`_all`. Combined with §5.10's `result_append`, the step pins `result.1[acc.size] = v`.

## Why this probe (inhabitation debt: structural step has no provider universals -- rules 1 and 2 apply)

`parseFlowSequenceLoop_step_push` has NO `forall...->` provider hypotheses (rule 3 does not apply).
Its antecedent `h_ok : parseFlowSequenceLoop ... = .ok result` is the same shape as §5.10/§5.10.1.

* Rule 1 (`h_ok` reachable): `seq_loop_ok` / `map_loop_ok` confirm the loop SUCCEEDS at the real
  entry states (pos 2, past the bracket-open token).
* Rule 2 (conclusion non-vacuous, `Or.inr` fires): `seq_loop_step_takes_push` /
  `map_loop_step_takes_push` confirm by `native_decide` that result.1.size = 2/1 on real data.
  Since `Or.inl result.1 = #[]` implies result.1.size = 0 (contradicting size 2/1), `Or.inr` is the
  only branch that can hold -- the step lemma is NOT a tautology via `Or.inl`.
* `seq_loop_step_applies` / `map_loop_step_applies`: end-to-end application on the real data;
  the disjunction type-checks against genuine parse results.
* `seq_loop_step_index` / `map_loop_step_index`: positional anchor -- `(acc.push v)[acc.size] = v`.
  This is the SHAPE of the per-step fact the induction will close: `result.1[acc.size] = v` follows
  from the tail call + §5.10's `result_append`.

`#print axioms` pins both step lemmas to `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
-/

namespace LoopStructuralStep

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures (reuse R588 setup): `[a,b]` / `{a:b}`, real loop-entry states at pos 2. -/

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

/-! ## Rule 1: loop succeeds at real entry (h_ok antecedent reachable). -/

theorem seq_loop_ok :
    (parseFlowSequenceLoop psLoopSeq 201 #[]).toOption.isSome = true := by native_decide
theorem map_loop_ok :
    (parseFlowMappingLoop psLoopMap 201 #[]).toOption.isSome = true := by native_decide

/-! ## Rule 2: the first step PUSHES, confirming `Or.inr` fires on real data. -/

/-- The loop returns 2 elements at the real entry state, so `Or.inl (result.1 = #[])` is
    blocked (size 2 != 0) and the step lemma's content lives in `Or.inr`. -/
theorem seq_loop_step_takes_push :
    ((parseFlowSequenceLoop psLoopSeq 201 #[]).toOption.map (·.1.size) == some 2) = true := by
  native_decide

/-- Same for mapping: 1 pair returned. -/
theorem map_loop_step_takes_push :
    ((parseFlowMappingLoop psLoopMap 201 #[]).toOption.map (·.1.size) == some 1) = true := by
  native_decide

/-! ## END-TO-END APPLICATION: the step lemma fires on real data and type-checks. -/

/-- Apply `parseFlowSequenceLoop_step_push` to the real entry state. The result is a genuine
    `Or`, not a tautology: `seq_loop_step_takes_push` confirms `Or.inr` is the live branch. -/
theorem seq_loop_step_applies
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop psLoopSeq 201 #[] = .ok result) :
    result.1 = #[] ∨ ∃ v ps'', parseFlowSequenceLoop ps'' 200 (#[v] : Array YamlValue) = .ok result :=
  parseFlowSequenceLoop_step_push psLoopSeq 200 #[] result h_ok

/-- Apply `parseFlowMappingLoop_step_push` to the real entry state. -/
theorem map_loop_step_applies
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop psLoopMap 201 #[] = .ok result) :
    result.1 = #[] ∨ ∃ k v ps'', parseFlowMappingLoop ps'' 200 (#[(k, v)] : Array _) = .ok result :=
  parseFlowMappingLoop_step_push psLoopMap 200 #[] result h_ok

/-! ## POSITIONAL ANCHOR: `(acc.push v)[acc.size] = v`. -/

/-- After one push on an empty accumulator, index 0 equals the pushed value. This is the SHAPE of the
    per-step positional fact: combined with §5.10's `result_append` on the tail call, the induction
    will close `result.1[acc.size] = v` at each step. -/
theorem seq_loop_step_index (v : YamlValue) :
    ((#[] : Array YamlValue).push v)[0]'(by simp) = v := by simp

theorem map_loop_step_index (k v : YamlValue) :
    ((#[] : Array (YamlValue × YamlValue)).push (k, v))[0]'(by simp) = (k, v) := by simp

/-! ## Axiom audit: both step lemmas are choice-clean (no `sorryAx`). -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowSequenceLoop_step_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowSequenceLoop_step_push

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowMappingLoop_step_push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowMappingLoop_step_push

end LoopStructuralStep
