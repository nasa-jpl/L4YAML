import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 585 — per-element re-parse consumer joint (§5.15): retype the two Front-B frontier sorries
  to one typed PRODUCER deliverable, and ground that deliverable's TRUTH before the retype.

R584 corrected Front B's producer target to "in-stream segment = the marker-stripped *core* of
`scanFiltered (emit v)`". R585 does NOT yet build that (hard) scanner producer; it lands the **consumer
joint** that sits between §5.11's pointwise → fold assembly and the actual content-fidelity sorry sites,
and CONSUMES it there — collapsing each opaque Front-B residual to one precisely-typed obligation.

The two `emit_roundtrip_{sequence,mapping}_content_eq` proofs carry a per-element round-trip IH that
speaks in *re-parse* terms (`parseYamlRaw (emit items[i]) = .ok rd → … → contentEq items[i] (rd.map
compose)[0]!.value`), not in `contentEq items[i] items''[i]` directly. §5.15's `contentEqList_of_reparse`
/ `contentEqPairList_of_reparse` compose that IH with §5.11: fed (a) the size equality and (b) the
per-element **re-parse deliverable** `∀ i, ∃ rd, parseYamlRaw (emit items[i]) = .ok rd ∧ rd.size = 1 ∧
(rd.map compose)[0]!.value = items''[i]!`, they discharge the whole brick-3 conjunction. Consuming them
RETYPES each frontier sorry from the content goal to exactly that bundled deliverable `h_size ∧ h_rep`
([[ref-consumer-joint-before-producer]], [[ref-reduction-by-import]]).

## Why this probe (inhabitation debt: the RETYPED frontier sorry's target must be TRUE)

The joints are verified implications — no inhabitation debt of their own. **The debt is on the bundled
deliverable** the retyped sorries now state: had it been FALSE, the retype would have re-pointed two
frontier sorries at an unprovable target (the R540 trap, one level out). So per
[[inhabitation-debt-validate-target-defs]] rule 1 (probe at birth) the deliverable is grounded against
REAL emission BEFORE the retype:

* `seq_deliverable_{size,elem0,elem1}` / `map_deliverable_{size,key0,val0}` `native_decide` that the
  whole-structure parse (`parseYamlRaw (emit (.sequence/.mapping …))`, recovered `items''`/`pairs''`)
  yields, for each element index, EXACTLY the value the standalone parse of that element yields
  (`parsedStandalone`), and that the sizes match. This is the producer's exact claim — parser-locality:
  parsing the whole structure recovers each element the same as parsing it alone — checked on the
  smallest non-degenerate witnesses (`[a,b]` 2 elements; `{a:b}` 1 entry, both key & value).

Non-vacuity of the joint itself: `joint_fires_empty_{seq,map}` fire it on the empty arrays (a real
conjunction out, not orphan scaffolding); the `*_shape` re-typings pin the contract abstractly. A
*non-vacuous* concrete firing is intentionally NOT attempted — discharging the ∀-hypotheses `ih`/`h_rep`
concretely would amount to proving a slice of the not-yet-built scanner/parser-locality producer; the
deliverable grounding above is what shows those hypotheses are inhabited on real data.

`#print axioms` pins both joints to `[propext, Classical.choice, Quot.sound]` — choice via the core
`Array`/`List` simp lemmas, NOT from `Except` reasoning; `#print axioms` it, never assume.
-/

namespace ReparseConsumerJoint

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.RoundTrip
open L4YAML.Scanner
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: plain scalars, a flow sequence, a flow mapping (the emitter double-quotes scalars). -/

def a : YamlValue := .scalar { content := "a", style := .plain }
def b : YamlValue := .scalar { content := "b", style := .plain }
def seqAB : YamlValue := .sequence .flow #[a, b] none none
def mapAB : YamlValue := .mapping .flow #[(a, b)] none none

/-! ## Deliverable grounding helpers: recover the parsed `items''`/`pairs''` of the whole structure,
    and the standalone parse value of a single element. -/

/-- Parse the whole flow sequence and recover its parsed items array (`items''`). -/
def parsedSeqItems : Option (Array YamlValue) :=
  match L4YAML.TokenParser.parseYamlRaw (emit seqAB) with
  | .ok docs => match (docs.map YamlDocument.compose)[0]!.value with
                | .sequence _ its _ _ => some its
                | _ => none
  | _ => none

/-- Parse the whole flow mapping and recover its parsed pairs array (`pairs''`). -/
def parsedMapPairs : Option (Array (YamlValue × YamlValue)) :=
  match L4YAML.TokenParser.parseYamlRaw (emit mapAB) with
  | .ok docs => match (docs.map YamlDocument.compose)[0]!.value with
                | .mapping _ ps _ _ => some ps
                | _ => none
  | _ => none

/-- Parse a single emitted value standalone, recovering its composed value. -/
def parsedStandalone (v : YamlValue) : Option YamlValue :=
  match L4YAML.TokenParser.parseYamlRaw (emit v) with
  | .ok docs => some (docs.map YamlDocument.compose)[0]!.value
  | _ => none

/-! ## THE INHABITATION PROBE: the per-element re-parse deliverable is TRUE on real emission.
    Whole-structure element `items''[k]` == standalone parse value of element `k`, sizes match. -/

theorem seq_deliverable_size : parsedSeqItems.map (·.size) = some 2 := by native_decide
theorem seq_deliverable_elem0 :
    (parsedSeqItems.map (fun its => its[0]!) == parsedStandalone a) = true := by native_decide
theorem seq_deliverable_elem1 :
    (parsedSeqItems.map (fun its => its[1]!) == parsedStandalone b) = true := by native_decide

theorem map_deliverable_size : parsedMapPairs.map (·.size) = some 1 := by native_decide
theorem map_deliverable_key0 :
    (parsedMapPairs.map (fun ps => ps[0]!.fst) == parsedStandalone a) = true := by native_decide
theorem map_deliverable_val0 :
    (parsedMapPairs.map (fun ps => ps[0]!.snd) == parsedStandalone b) = true := by native_decide

/-! ## Non-vacuity: the joint FIRES on the empty arrays (vacuous hypotheses, a real conjunction out). -/

theorem joint_fires_empty_seq :
    ((#[] : Array YamlValue).size == (#[] : Array YamlValue).size
      && contentEq.contentEqList (#[] : Array YamlValue).toList (#[] : Array YamlValue).toList) = true :=
  contentEqList_of_reparse #[] #[] rfl (fun i => i.elim0) (fun i => i.elim0)

theorem joint_fires_empty_map :
    ((#[] : Array (YamlValue × YamlValue)).size == (#[] : Array (YamlValue × YamlValue)).size
      && contentEq.contentEqPairList (#[] : Array (YamlValue × YamlValue)).toList
           (#[] : Array (YamlValue × YamlValue)).toList) = true :=
  contentEqPairList_of_reparse #[] #[] rfl (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)

/-! ## Abstract residual contract: the joints pin, for ANY recovered `items''`/`pairs''`, the bundled
    deliverable `h_size ∧ h_rep` → the brick-3 conjunction (the single typed obligation the producer owes). -/

theorem reparse_seq_shape
    (items items'' : Array YamlValue)
    (h_size : items.size = items''.size)
    (ih : ∀ (i : Fin items.size) (rd : Array YamlDocument),
            L4YAML.TokenParser.parseYamlRaw (emit items[i]) = .ok rd → rd.size = 1 →
            contentEq items[i] (rd.map YamlDocument.compose)[0]!.value = true)
    (h_rep : ∀ (i : Fin items.size), ∃ rd : Array YamlDocument,
              L4YAML.TokenParser.parseYamlRaw (emit items[i]) = .ok rd ∧ rd.size = 1 ∧
              (rd.map YamlDocument.compose)[0]!.value = items''[i.val]!) :
    (items.size == items''.size && contentEq.contentEqList items.toList items''.toList) = true :=
  contentEqList_of_reparse items items'' h_size ih h_rep

theorem reparse_map_shape
    (pairs pairs'' : Array (YamlValue × YamlValue))
    (h_size : pairs.size = pairs''.size)
    (ihk : ∀ (i : Fin pairs.size) (rd : Array YamlDocument),
            L4YAML.TokenParser.parseYamlRaw (emit pairs[i].fst) = .ok rd → rd.size = 1 →
            contentEq pairs[i].fst (rd.map YamlDocument.compose)[0]!.value = true)
    (ihv : ∀ (i : Fin pairs.size) (rd : Array YamlDocument),
            L4YAML.TokenParser.parseYamlRaw (emit pairs[i].snd) = .ok rd → rd.size = 1 →
            contentEq pairs[i].snd (rd.map YamlDocument.compose)[0]!.value = true)
    (h_rep : ∀ (i : Fin pairs.size),
              (∃ rdk : Array YamlDocument,
                L4YAML.TokenParser.parseYamlRaw (emit pairs[i].fst) = .ok rdk ∧ rdk.size = 1 ∧
                (rdk.map YamlDocument.compose)[0]!.value = (pairs''[i.val]!).fst) ∧
              (∃ rdv : Array YamlDocument,
                L4YAML.TokenParser.parseYamlRaw (emit pairs[i].snd) = .ok rdv ∧ rdv.size = 1 ∧
                (rdv.map YamlDocument.compose)[0]!.value = (pairs''[i.val]!).snd)) :
    (pairs.size == pairs''.size && contentEq.contentEqPairList pairs.toList pairs''.toList) = true :=
  contentEqPairList_of_reparse pairs pairs'' h_size ihk ihv h_rep

/-! ## Axiom audit: both joints are sorry-free (`[propext, Classical.choice, Quot.sound]`). -/

/-- info: 'L4YAML.Proofs.EmitterScannability.contentEqList_of_reparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms contentEqList_of_reparse

/-- info: 'L4YAML.Proofs.EmitterScannability.contentEqPairList_of_reparse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms contentEqPairList_of_reparse

end ReparseConsumerJoint
