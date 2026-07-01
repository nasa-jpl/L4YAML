import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection -- Front-B non-all-scalar locality blocking structure

After R609, four sorry sites remain in Front-B.  Sorries 3 and 4 (inside
`emit_roundtrip_sequence_content_eq` and `emit_roundtrip_mapping_content_eq`) have the form:

```
· sorry  -- non-all-scalar branch of by_cases h_all_sc
```

The sorry goal is the LOCALITY CONJUNCTION:
```
items.size = items''.size ∧
∀ i rd, parseYamlRaw (emit items[i]) = .ok rd → rd.size = 1 →
  (rd.map YamlDocument.compose)[0]!.value = items''[i.val]!
```
where `items''` is the array of composed values from the WHOLE-STREAM parse of
`"[" ++ emitList items ++ "]"`.

The IH available gives only:
```
contentEq items[i] (rd.map YamlDocument.compose)[0]!.value = true
```
i.e. the STANDALONE re-parse is content-equivalent, not value-EQUAL, to the whole-stream slot.

The second conjunct is the LOCALITY EQUALITY:
  `(standalone parse)[0]!.value = items''[i.val]!`

This requires `parseNode_position_invariant` (span-locality): if the tokens at position `pos`
in the full stream equal the tokens at position `pos'` in the standalone stream (token-for-token),
then `parseNode` at `pos` gives the same result as at `pos'`.  This is TRUE because `parseNode`
only reads forward until bracket depth returns to 0, ignoring surrounding context.

## Inhabitation debt check

Per [[inhabitation-debt-validate-target-defs]] rule 1, we must verify the non-all-scalar
sorry target is TRUE on concrete witnesses BEFORE writing the sorry.

The concrete witness: the single-element sequence `[["a"]]` (outer seq containing `["a"]`).
The single item is `.sequence .flow #[.scalar "a" .plain]` -- NOT a scalar.

We verify by `native_decide` that:
1. The STANDALONE parse of `emit items[0]` gives a specific value.
2. The WHOLE-STREAM parse gives `items''[0]!` equal to that standalone value.
3. Hence the locality EQUALITY holds on this concrete witness.
-/

namespace NonAllScalarLocality

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.RoundTrip
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures -/

def inner_sc : Scalar := { content := "a", style := .plain }
def inner_item : YamlValue := .sequence .flow #[.scalar inner_sc] none none
def outerSeq : YamlValue := .sequence .flow #[inner_item] none none

/-- Composed items from the whole-stream parse of `outerSeq`. -/
def parsedOuterItems : Option (Array YamlValue) :=
  match parseYamlRaw (emit outerSeq) with
  | .ok docs => match (docs.map YamlDocument.compose)[0]!.value with
               | .sequence _ items _ _ => some items
               | _ => none
  | _ => none

/-- Standalone composed value from parsing just `emit inner_item`. -/
def parsedInnerStandalone : Option YamlValue :=
  match parseYamlRaw (emit inner_item) with
  | .ok docs => some (docs.map YamlDocument.compose)[0]!.value
  | _ => none

/-! ## Rule 1: antecedent reachable -- the `h_all_sc` case-split goes to the non-all-scalar branch -/

/-- The outer array has a non-scalar item, so the `by_cases h_all_sc` takes the FALSE branch. -/
theorem outerSeq_not_all_scalar :
    ¬ (∀ v ∈ (#[inner_item] : Array YamlValue).toList, ∃ sc : Scalar, v = .scalar sc) := by
  intro h
  have hmem : inner_item ∈ (#[inner_item] : Array YamlValue).toList := by simp
  obtain ⟨sc, h_eq⟩ := h inner_item hmem
  simp [inner_item] at h_eq

/-! ## Rule 2: conclusion non-vacuous -- locality equality holds on the concrete witness -/

/-- The whole-stream parse recovers exactly 1 outer item. -/
theorem outer_parse_size : parsedOuterItems.map (·.size) = some 1 := by native_decide

/-- THE INHABITATION PROBE: the locality equality holds -- slot 0 from the whole-stream parse
    equals the standalone parse of `inner_item`.  This is what the sorry must prove in general. -/
theorem locality_eq_slot0 :
    (parsedOuterItems.map (·[0]!) == parsedInnerStandalone) = true := by native_decide

/-- The standalone parse is content-equivalent to `inner_item` (from the IH). -/
theorem inner_item_standalone_contentEq :
    (match parsedInnerStandalone with
     | some v => contentEq inner_item v
     | none => false) = true := by native_decide

/-- The whole-stream slot 0 is also content-equivalent to `inner_item`.
    This follows from `locality_eq_slot0` by substitution (the standalone value = slot 0). -/
theorem inner_item_whole_stream_contentEq :
    (match parsedOuterItems with
     | some items => contentEq inner_item items[0]!
     | none => false) = true := by native_decide

/-! ## The gap: IH gives contentEq but the sorry needs value equality

`contentEq_trans` is PROVEN, so we COULD chain:
  IH:    `contentEq items[i] v_standalone = true`
  need:  `contentEq v_standalone items''[i]! = true`
  → by trans: `contentEq items[i] items''[i]! = true`

But `contentEqList_of_reparse` / `reparse_deliverable_of_locality_seq` need the EQUALITY
  `v_standalone = items''[i]!` (stronger) to close via IH substitution.

`contentEq v_standalone items''[i]! = true` is WEAKER than `v_standalone = items''[i]!`.
We have the equality on the concrete witness (above), but the sorry needs a UNIVERSAL proof.

The universal proof requires `parseNode_position_invariant`: if full-stream tokens at `pos + k`
equal standalone tokens at `1 + k` for all `k`, then `parseNode` at `pos` in the full stream
equals `parseNode` at `1` in the standalone stream.  This is true because `parseNode` only reads
forward until bracket depth = 0 and ignores surrounding context. -/

/-- `contentEq_trans` is available and fires correctly (tool is sound, gap is the equality). -/
theorem contentEq_trans_available (v1 v2 v3 : YamlValue)
    (h12 : contentEq v1 v2 = true) (h23 : contentEq v2 v3 = true) :
    contentEq v1 v3 = true :=
  contentEq_trans v1 v2 v3 h12 h23

/-! ## Axiom audit -/

/-- info: 'NonAllScalarLocality.locality_eq_slot0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 locality_eq_slot0._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms locality_eq_slot0

end NonAllScalarLocality
