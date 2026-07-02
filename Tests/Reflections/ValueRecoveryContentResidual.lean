import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner

/-!
# Reflection 578 — INHABITATION PROBE for Front B's brick-3 RESIDUAL (after consuming §5.8)

Reflection 577 landed `parseStream_flow{Seq,Map}Start_recovers_outer_shape` (§5.8): the assembled
outer-shape half of Front B's value-recovery trace. **Reflection 578 CONSUMES those two lemmas** into
the content-fidelity sorries `emit_roundtrip_{sequence,mapping}_content_eq` (`EmitterScannability.lean`,
the `_ :: _` non-empty branches). The consumption RETYPES each residual — from "the entire non-empty
collection case, needing the exact parsed value structure" down to a precise per-element goal:

* sequence: `(items.size == items''.size && contentEq.contentEqList items.toList items''.toList) = true`
* mapping:  `(pairs.size == pairs''.size && contentEq.contentEqPairList pairs.toList pairs''.toList) = true`

where `items''` / `pairs''` are the elements the parser recovers under the (now §5.8-certified) outer
flow shape. That retyped goal is **brick 3** — the genuinely hard per-element
`parseFlowSequenceLoop` / `parseFlowMappingLoop` induction, deferred to a future turn.

## Why this probe (inhabitation debt for a RETYPED, deferred residual)

Retyping a `sorry` to a sharper goal is only progress if the sharper goal is **TRUE**. A `rw` chain
type-checks against `exact sorry` regardless of whether the residual it leaves is even satisfiable; if
`items''` were NOT element-wise content-equal to the original `items`, brick 3 would be a dead end and
the consumption would have retyped one sorry into an *unprovable* one. The
[[ref-probe-deferred-universal-before-producing]] discipline says: before committing to PROVE a deferred
target, evaluate whether it actually holds on real data. So the witnesses below evaluate the EXACT
retyped residual on REAL emitted+scanned+parsed+composed bytes (`emit` -> `scanFiltered` -> `parseStream`
-> `YamlDocument.compose`, exactly the `parseYamlRaw`/`parseYaml` pipeline the lemmas trace):

* `seqResidualHolds_fires` / `mapResidualHolds_fires` — the brick-3 residual itself, byte-identically
  shaped to the goal left at the `_ :: _` branch, evaluates to `true`: the recovered `items''` / `pairs''`
  have the original size AND are pairwise content-equal. Brick 3 is a TRUE goal, not a dead end.
* `seqContentFidelityHolds_fires` / `mapContentFidelityHolds_fires` — the ultimate end-to-end goal both
  sorries serve, `contentEq value (composed first doc).value = true`, also holds on real data: full
  content fidelity is reachable once brick 3 lands.
-/

namespace ValueRecoveryContentResidual

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-- The elements of a genuine grammable flow sequence `["x"]`. -/
def seqItems : Array YamlValue := #[.scalar { content := "x", style := .doubleQuoted }]

/-- A genuine grammable flow sequence `["x"]`. -/
def seqValue : YamlValue := .sequence .flow seqItems

/-- The pairs of a genuine grammable flow mapping `{"a":"b"}`. -/
def mapPairs : Array (YamlValue × YamlValue) :=
  #[(.scalar { content := "a", style := .doubleQuoted },
     .scalar { content := "b", style := .doubleQuoted })]

/-- A genuine grammable flow mapping `{"a":"b"}`. -/
def mapValue : YamlValue := .mapping .flow mapPairs

/-- REAL tokens from the emitted+scanned bytes of `seqValue` — exactly what `parseStream` parses. -/
def seqTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqValue) with
  | .ok t => t
  | .error _ => #[]

/-- Mirror: REAL tokens from the emitted+scanned bytes of `mapValue`. -/
def mapTokens : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapValue) with
  | .ok t => t
  | .error _ => #[]

/-- The brick-3 residual on REAL data: under the §5.8-recovered outer flow-sequence shape, the
    recovered items `items''` match the original `seqItems` ELEMENT-WISE — byte-identically the goal
    `(items.size == items''.size && contentEq.contentEqList items.toList items''.toList) = true` that
    consuming §5.8 leaves at `emit_roundtrip_sequence_content_eq`'s `_ :: _` branch. -/
def seqResidualHolds : Bool :=
  match parseStream seqTokens with
  | .ok raw_docs =>
    match (raw_docs.map YamlDocument.compose)[0]!.value with
    | .sequence _ items'' _ _ =>
      (seqItems.size == items''.size) && contentEq.contentEqList seqItems.toList items''.toList
    | _ => false
  | .error _ => false

/-- Mirror: the brick-3 residual for the mapping case (`contentEqPairList`). -/
def mapResidualHolds : Bool :=
  match parseStream mapTokens with
  | .ok raw_docs =>
    match (raw_docs.map YamlDocument.compose)[0]!.value with
    | .mapping _ pairs'' _ _ =>
      (mapPairs.size == pairs''.size) && contentEq.contentEqPairList mapPairs.toList pairs''.toList
    | _ => false
  | .error _ => false

theorem seqResidualHolds_fires : seqResidualHolds = true := by native_decide
theorem mapResidualHolds_fires : mapResidualHolds = true := by native_decide

/-- The ultimate end-to-end goal `emit_roundtrip_sequence_content_eq` serves: full content fidelity of
    the composed first document against the original value, on real bytes. Reachable once brick 3 lands. -/
def seqContentFidelityHolds : Bool :=
  match parseStream seqTokens with
  | .ok raw_docs => contentEq seqValue (raw_docs.map YamlDocument.compose)[0]!.value
  | .error _ => false

/-- Mirror: end-to-end content fidelity for the mapping value. -/
def mapContentFidelityHolds : Bool :=
  match parseStream mapTokens with
  | .ok raw_docs => contentEq mapValue (raw_docs.map YamlDocument.compose)[0]!.value
  | .error _ => false

theorem seqContentFidelityHolds_fires : seqContentFidelityHolds = true := by native_decide
theorem mapContentFidelityHolds_fires : mapContentFidelityHolds = true := by native_decide

-- Note on axioms: the CONSUMING lemmas `emit_roundtrip_{sequence,mapping}_content_eq` deliberately
-- still carry `sorryAx` — brick 3 (the per-element loop induction) is the residual this consumption
-- retyped TOWARD, not away. There is therefore no new sorry-free declaration to certify here; this
-- file's job is purely the inhabitation evidence above that that residual is TRUE on real data.

end ValueRecoveryContentResidual
