import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection 586 — locality-reduction consumer joint (§5.16): retype the two Front-B frontier sorries
  one layer deeper, from the existential re-parse bundle to the PURE locality equation.

R585 (§5.15) retyped each Front-B frontier sorry to the bundled producer deliverable `h_size ∧ h_rep`,
where `h_rep i : ∃ rd, parseYamlRaw (emit items[i]) = .ok rd ∧ rd.size = 1 ∧ (rd.map compose)[0]!.value
= items''[i]!`.  That still bundled THREE obligations per element: parse-SUCCESS, single-DOCUMENT, and
the genuinely-hard LOCALITY equation.  But the first two are NOT part of the hard producer — they are
already proven for every grammable value (`emit_parse_succeeds`, `emit_produces_single_document`).

R586 (§5.16) lands the **locality-reduction joint** `reparse_deliverable_of_locality_{seq,pair}` that
discharges those two from the existing lemmas, leaving the producer owing ONLY the locality equation.
Consuming it at the two sorry sites RETYPES each frontier sorry once more — from the existential bundle
`∀ i, ∃ rd, parse ∧ size ∧ value-eq` to the size equality plus the pure equation
`∀ i, ∀ rd, parse → size → (rd.map compose)[0]!.value = items''[i]!`.  The round-trip-success plumbing is
gone; the hard scanner-span-locality + parser-locality producer now owes only the equation (and the
size).  This is the §5.15 move one layer deeper ([[ref-consumer-joint-before-producer]],
[[ref-reduction-by-import]]).

The flow→block bridge: grammability arrives at the sorry site in FLOW context (`Grammable items[i]
(inFlow || style == .flow)`); `emit_parse_succeeds`/`emit_produces_single_document` need block context
(`Grammable items[i] false`).  `grammable_to_block` weakens it — a clean structural weakening, since the
`inFlow` flag only ever TIGHTENS the scalar leaf (`ScalarScannable_any_implies_false`), never the shape.

## Why this probe (inhabitation debt: the RETYPED frontier sorry's new target must be TRUE)

The joints + the weakening are verified implications — no inhabitation debt of their own.  **The debt is
on the new bundled target** `h_size ∧ h_loc` the retyped sorries now state.  Per
[[inhabitation-debt-validate-target-defs]] rule 1 (probe at birth), the LOCALITY target is grounded
against REAL emission BEFORE the retype:

* `seq_locality_size/elem0/elem1` / `map_locality_size/key0/val0` `native_decide` that the whole-structure
  parse recovers, for each element index, EXACTLY the value the STANDALONE parse of that element yields
  (`parsedStandalone`) — i.e. `(rd.map compose)[0]!.value = items''[i]!`, the producer's exact locality
  claim — and that the sizes match, on the smallest non-degenerate witnesses `[a,b]`/`{a:b}`.  (Same
  target R585 grounded; re-affirmed here for the §5.16 locality+size shape.)

Non-vacuity of the new artifacts:
* `block_a` fires `grammable_to_block` on a CONCRETE witness (`Grammable a true → Grammable a false`),
  exercising the scalar leaf — a real weakening out, not orphan plumbing.
* `joint_fires_empty_{seq,map}` fire the locality-reduction joints on the empty arrays (vacuous
  hypotheses, a real `∀`-existential out); `locality_reduces_{seq,map}` pin the residual contract
  abstractly — for ANY recovered `items''`/`pairs''`, locality + grammability → the §5.15 deliverable.

`#print axioms` pins `grammable_to_block` to `[propext, Classical.choice, Quot.sound]`; the joints add
only the `native_decide` axioms transitively from `emit_parse_succeeds`/`emit_produces_single_document`
(no `sorryAx`) — `#print axioms` it, never assume.
-/

namespace LocalityReductionJoint

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: plain scalars, a flow sequence, a flow mapping (the emitter double-quotes scalars). -/

def a : YamlValue := .scalar { content := "a", style := .plain }
def b : YamlValue := .scalar { content := "b", style := .plain }
def seqAB : YamlValue := .sequence .flow #[a, b] none none
def mapAB : YamlValue := .mapping .flow #[(a, b)] none none

/-! ## Deliverable grounding helpers (recover whole-structure `items''`/`pairs''`; standalone value). -/

def parsedSeqItems : Option (Array YamlValue) :=
  match L4YAML.TokenParser.parseYamlRaw (emit seqAB) with
  | .ok docs => match (docs.map YamlDocument.compose)[0]!.value with
                | .sequence _ its _ _ => some its
                | _ => none
  | _ => none

def parsedMapPairs : Option (Array (YamlValue × YamlValue)) :=
  match L4YAML.TokenParser.parseYamlRaw (emit mapAB) with
  | .ok docs => match (docs.map YamlDocument.compose)[0]!.value with
                | .mapping _ ps _ _ => some ps
                | _ => none
  | _ => none

def parsedStandalone (v : YamlValue) : Option YamlValue :=
  match L4YAML.TokenParser.parseYamlRaw (emit v) with
  | .ok docs => some (docs.map YamlDocument.compose)[0]!.value
  | _ => none

/-! ## THE INHABITATION PROBE: the per-element LOCALITY target is TRUE on real emission.
    Whole-structure element `items''[k]` == standalone parse value of element `k`, sizes match. -/

theorem seq_locality_size : parsedSeqItems.map (·.size) = some 2 := by native_decide
theorem seq_locality_elem0 :
    (parsedSeqItems.map (fun its => its[0]!) == parsedStandalone a) = true := by native_decide
theorem seq_locality_elem1 :
    (parsedSeqItems.map (fun its => its[1]!) == parsedStandalone b) = true := by native_decide

theorem map_locality_size : parsedMapPairs.map (·.size) = some 1 := by native_decide
theorem map_locality_key0 :
    (parsedMapPairs.map (fun ps => ps[0]!.fst) == parsedStandalone a) = true := by native_decide
theorem map_locality_val0 :
    (parsedMapPairs.map (fun ps => ps[0]!.snd) == parsedStandalone b) = true := by native_decide

/-! ## Non-vacuity: `grammable_to_block` weakens a CONCRETE flow-grammable scalar to block context. -/

theorem grammable_a_true : Grammable a true := by
  unfold a
  refine .scalar _ true ?_
  unfold ScalarScannable
  intro _hplain _hlen
  exact ⟨by decide, by decide, by decide, fun _ => by decide⟩

theorem block_a : Grammable a false := grammable_to_block grammable_a_true

/-! ## Non-vacuity: the joints FIRE on the empty arrays (vacuous hypotheses, a real ∀-existential out). -/

theorem joint_fires_empty_seq :
    ∀ (i : Fin (#[] : Array YamlValue).size), ∃ rd : Array YamlDocument,
      L4YAML.TokenParser.parseYamlRaw (emit (#[] : Array YamlValue)[i]) = .ok rd ∧ rd.size = 1 ∧
      (rd.map YamlDocument.compose)[0]!.value = (#[] : Array YamlValue)[i.val]! :=
  reparse_deliverable_of_locality_seq #[] #[] (fun i => i.elim0) (fun i => i.elim0)

theorem joint_fires_empty_map :
    ∀ (i : Fin (#[] : Array (YamlValue × YamlValue)).size),
      (∃ rdk : Array YamlDocument,
        L4YAML.TokenParser.parseYamlRaw (emit (#[] : Array (YamlValue × YamlValue))[i].fst)
          = .ok rdk ∧ rdk.size = 1 ∧
        (rdk.map YamlDocument.compose)[0]!.value = ((#[] : Array (YamlValue × YamlValue))[i.val]!).fst) ∧
      (∃ rdv : Array YamlDocument,
        L4YAML.TokenParser.parseYamlRaw (emit (#[] : Array (YamlValue × YamlValue))[i].snd)
          = .ok rdv ∧ rdv.size = 1 ∧
        (rdv.map YamlDocument.compose)[0]!.value = ((#[] : Array (YamlValue × YamlValue))[i.val]!).snd) :=
  reparse_deliverable_of_locality_pair #[] #[] (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0)

/-! ## Abstract residual contract: for ANY recovered `items''`/`pairs''`, locality + grammability pin
    the §5.15 deliverable — the single typed obligation the producer owes after §5.16. -/

theorem locality_reduces_seq
    (items items'' : Array YamlValue)
    (h_gram : ∀ (i : Fin items.size), Grammable items[i] false)
    (h_loc : ∀ (i : Fin items.size) (rd : Array YamlDocument),
              L4YAML.TokenParser.parseYamlRaw (emit items[i]) = .ok rd → rd.size = 1 →
              (rd.map YamlDocument.compose)[0]!.value = items''[i.val]!) :
    ∀ (i : Fin items.size), ∃ rd : Array YamlDocument,
      L4YAML.TokenParser.parseYamlRaw (emit items[i]) = .ok rd ∧ rd.size = 1 ∧
      (rd.map YamlDocument.compose)[0]!.value = items''[i.val]! :=
  reparse_deliverable_of_locality_seq items items'' h_gram h_loc

theorem locality_reduces_map
    (pairs pairs'' : Array (YamlValue × YamlValue))
    (h_gram_k : ∀ (i : Fin pairs.size), Grammable pairs[i].fst false)
    (h_gram_v : ∀ (i : Fin pairs.size), Grammable pairs[i].snd false)
    (h_loc_k : ∀ (i : Fin pairs.size) (rd : Array YamlDocument),
              L4YAML.TokenParser.parseYamlRaw (emit pairs[i].fst) = .ok rd → rd.size = 1 →
              (rd.map YamlDocument.compose)[0]!.value = (pairs''[i.val]!).fst)
    (h_loc_v : ∀ (i : Fin pairs.size) (rd : Array YamlDocument),
              L4YAML.TokenParser.parseYamlRaw (emit pairs[i].snd) = .ok rd → rd.size = 1 →
              (rd.map YamlDocument.compose)[0]!.value = (pairs''[i.val]!).snd) :
    ∀ (i : Fin pairs.size),
      (∃ rdk : Array YamlDocument,
        L4YAML.TokenParser.parseYamlRaw (emit pairs[i].fst) = .ok rdk ∧ rdk.size = 1 ∧
        (rdk.map YamlDocument.compose)[0]!.value = (pairs''[i.val]!).fst) ∧
      (∃ rdv : Array YamlDocument,
        L4YAML.TokenParser.parseYamlRaw (emit pairs[i].snd) = .ok rdv ∧ rdv.size = 1 ∧
        (rdv.map YamlDocument.compose)[0]!.value = (pairs''[i.val]!).snd) :=
  reparse_deliverable_of_locality_pair pairs pairs'' h_gram_k h_gram_v h_loc_k h_loc_v

/-! ## Axiom audit: the weakening is choice-clean; the joints add only `native_decide` axioms. -/

/-- info: 'L4YAML.Proofs.EmitterScannability.grammable_to_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grammable_to_block

end LocalityReductionJoint
