import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 579 — INHABITATION PROBE for Front B's brick-3 content-list step algebra (§5.9)

Reflection 578 consumed §5.8's outer-shape recovery into the two content-fidelity sorries, retyping
each to its **brick-3 residual** — the per-element comparison `(items.size == items''.size &&
contentEq.contentEqList items.toList items''.toList) = true` (and the `pairs''` mapping mirror).
**Reflection 579 lands the first link of brick 3**: the emission-independent *step algebra* that the
per-element loop induction will consume — `contentEqList_append_singleton` / `contentEqList_push`
(sequence) and `contentEqPairList_append_singleton` / `contentEqPairList_push` (mapping), all in
`ContentFidelity.lean` §5.9. Each says: extending two content-equal value/pair lists by one
content-equal element (or `Array.push`ing one onto two content-equal accumulators) preserves
`contentEqList` / `contentEqPairList`. That is the *exact* invariant-extension step a content-tracking
`parseFlowSequenceLoop` / `parseFlowMappingLoop` induction performs each iteration (`parseNode` one
entry, `Array.push` it, the round-trip IH supplies one fresh content-equal element).

## Why this probe (inhabitation debt, and what is DIFFERENT this turn)

Unlike R578's *consuming* lemmas — which deliberately retain `sorryAx` because brick 3 is the residual
they retyped toward — these four §5.9 lemmas are **genuinely sorry-free** (`[propext]` only; the audits
below certify it). So this turn owes the standard birth-probe of a sorry-free construct: evaluate the
lemma's CONCLUSION on real witnesses to confirm it is TRUE, not merely well-formed, and — per
inhabitation-debt rule 2 — probe the BOUNDARY (the `nil` base case) AND a NON-degenerate recursive case
(a non-empty prefix, where `contentEqList`'s recursive `&&` branch actually fires), since a universal
fails at its extremes and a singleton-only probe would skip the recursion entirely.

The witnesses below use scalars that are content-equal but differ in `style` (`.plain` vs
`.doubleQuoted`) — exactly the difference `contentEq` is meant to ignore — so a passing probe confirms
the lemma threads genuine style-blind content equality, not trivial syntactic equality.

* `seqStepBase_holds` / `mapStepBase_holds` — append-singleton on the `nil` base (the degenerate edge).
* `seqStep_holds` / `mapStep_holds` — append-singleton on a non-empty prefix (recursion fires).
* `seqPush_holds` / `mapPush_holds` — the `Array.push` corollary on real accumulators (brick-3 shape).
* `seqResidual2_holds` / `mapResidual2_holds` — R578's brick-3 residual on a **two-element** fixture
  (real `emit` -> `scanFiltered` -> `parseStream` -> `compose`), extending R578's singleton probe to
  where `contentEqList`'s recursive branch fires: the recovered `items''` / `pairs''` are size-matched
  AND pairwise content-equal at length 2, so the step algebra targets a TRUE residual at every length.

The `#print axioms` audits certify the four source lemmas are `[propext]`-clean — sorry-free, no
`Classical.choice` — which is what distinguishes this verified-but-unconsumed artifact from R578's
sorry-carrying consumers.
-/

namespace ContentListStepAlgebra

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Style-blind content-equal scalar fixtures (same content, different `style`) -/

def sx  : YamlValue := .scalar { content := "x", style := .plain }
def sx' : YamlValue := .scalar { content := "x", style := .doubleQuoted }
def sy  : YamlValue := .scalar { content := "y", style := .plain }
def sy' : YamlValue := .scalar { content := "y", style := .doubleQuoted }

def ka  : YamlValue := .scalar { content := "a", style := .plain }
def ka' : YamlValue := .scalar { content := "a", style := .doubleQuoted }
def vb  : YamlValue := .scalar { content := "b", style := .plain }
def vb' : YamlValue := .scalar { content := "b", style := .doubleQuoted }
def kc  : YamlValue := .scalar { content := "c", style := .plain }
def kc' : YamlValue := .scalar { content := "c", style := .doubleQuoted }
def vd  : YamlValue := .scalar { content := "d", style := .plain }
def vd' : YamlValue := .scalar { content := "d", style := .doubleQuoted }

/-! ## Probe: `contentEqList_append_singleton` / `_push` (sequence) conclusion on real witnesses -/

/-- Boundary (`nil` base): appending one content-equal element to two empty lists. -/
theorem seqStepBase_holds :
    contentEq.contentEqList ([] ++ [sx]) ([] ++ [sx']) = true := by native_decide

/-- Recursive case (non-empty prefix `[sy]`/`[sy']`, where `contentEqList`'s `&&` branch fires). -/
theorem seqStep_holds :
    contentEq.contentEqList ([sy] ++ [sx]) ([sy'] ++ [sx']) = true := by native_decide

/-- The `Array.push` corollary's shape on real content-equal accumulators (the brick-3 loop step). -/
theorem seqPush_holds :
    contentEq.contentEqList ((#[sy]).push sx).toList ((#[sy']).push sx').toList = true := by
  native_decide

/-! ## Probe: `contentEqPairList_append_singleton` / `_push` (mapping) conclusion on real witnesses -/

/-- Boundary (`nil` base): appending one content-equal pair to two empty pair lists. -/
theorem mapStepBase_holds :
    contentEq.contentEqPairList ([] ++ [(ka, vb)]) ([] ++ [(ka', vb')]) = true := by native_decide

/-- Recursive case (non-empty prefix, where `contentEqPairList`'s recursive branch fires). -/
theorem mapStep_holds :
    contentEq.contentEqPairList ([(kc, vd)] ++ [(ka, vb)]) ([(kc', vd')] ++ [(ka', vb')]) = true := by
  native_decide

/-- The `Array.push` corollary's shape on real content-equal pair accumulators (brick-3 map step). -/
theorem mapPush_holds :
    contentEq.contentEqPairList ((#[(kc, vd)]).push (ka, vb)).toList
                                ((#[(kc', vd')]).push (ka', vb')).toList = true := by native_decide

/-! ## Probe: R578's brick-3 residual on TWO-element fixtures (recursion fires on real parse data) -/

def seqItems2 : Array YamlValue :=
  #[.scalar { content := "x", style := .doubleQuoted },
    .scalar { content := "y", style := .doubleQuoted }]
def seqValue2 : YamlValue := .sequence .flow seqItems2

def mapPairs2 : Array (YamlValue × YamlValue) :=
  #[(.scalar { content := "a", style := .doubleQuoted },
     .scalar { content := "b", style := .doubleQuoted }),
    (.scalar { content := "c", style := .doubleQuoted },
     .scalar { content := "d", style := .doubleQuoted })]
def mapValue2 : YamlValue := .mapping .flow mapPairs2

def seqTokens2 : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqValue2) with
  | .ok t => t
  | .error _ => #[]

def mapTokens2 : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapValue2) with
  | .ok t => t
  | .error _ => #[]

/-- The brick-3 residual at LENGTH 2: the recovered `items''` is size-matched and pairwise
    content-equal to the original `seqItems2` — the recursive `&&` branch of `contentEqList` the §5.9
    step algebra threads, evaluated on real emitted+parsed+composed bytes. -/
def seqResidual2Holds : Bool :=
  match parseStream seqTokens2 with
  | .ok raw_docs =>
    match (raw_docs.map YamlDocument.compose)[0]!.value with
    | .sequence _ items'' _ _ =>
      (seqItems2.size == items''.size) && contentEq.contentEqList seqItems2.toList items''.toList
    | _ => false
  | .error _ => false

/-- Mapping mirror: the brick-3 pair residual at length 2 (`contentEqPairList`'s recursive branch). -/
def mapResidual2Holds : Bool :=
  match parseStream mapTokens2 with
  | .ok raw_docs =>
    match (raw_docs.map YamlDocument.compose)[0]!.value with
    | .mapping _ pairs'' _ _ =>
      (mapPairs2.size == pairs''.size) && contentEq.contentEqPairList mapPairs2.toList pairs''.toList
    | _ => false
  | .error _ => false

theorem seqResidual2Holds_fires : seqResidual2Holds = true := by native_decide
theorem mapResidual2Holds_fires : mapResidual2Holds = true := by native_decide

/-! ## Axiom audit: the four §5.9 step lemmas are sorry-free (`[propext]` only)

Unlike R578's consuming lemmas (which retain `sorryAx`), these brick-3 prep lemmas are genuinely
discharged — the audits certify `[propext]`, with no `Classical.choice` and no `sorryAx`. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.contentEqList_append_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms contentEqList_append_singleton

/-- info: 'L4YAML.Proofs.EmitterScannability.contentEqList_push' depends on axioms: [propext] -/
#guard_msgs in
#print axioms contentEqList_push

/-- info: 'L4YAML.Proofs.EmitterScannability.contentEqPairList_append_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms contentEqPairList_append_singleton

/-- info: 'L4YAML.Proofs.EmitterScannability.contentEqPairList_push' depends on axioms: [propext] -/
#guard_msgs in
#print axioms contentEqPairList_push

end ContentListStepAlgebra
