import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 587 — `parseNode` scalar dispatch leaf (§5.4.1): complete the position-generic
  dispatch family and pin the parser-locality leaf of the span-locality bridge.

R586 (§5.16) left the two Front-B frontier sorries owing the size equality plus the PURE LOCALITY
equation `(rd.map compose)[0]!.value = items''[i]!` — the producer's deliverable.  Both halves flow
from the SAME `parseFlowSequenceLoop` / `parseFlowMappingLoop` induction (it `parseNode`s one element
span per iteration and `Array.push`es it).  So the producer's per-element step is a *mid-stream*
`parseNode`, and the locality equation says that mid-stream recovery equals the *standalone* parse of
`emit items[i]`.

The §5.4 dispatch family already pinned, **position-generically**, the constructor a successful
`parseNode` produces from a `.flowSequenceStart` / `.flowMappingStart` lookahead
(`parseNode_flowSeqStart_produces_sequence`, `parseNode_flowMapStart_produces_mapping`).  It was
missing its **scalar** member: a `.scalar content style` lookahead was only pinned *inside* the
whole-stream `parseStream_three_tokens_scalar`, fixed to position 1 — not reusable mid-stream.

R587 (§5.4.1) lands that member.  `parseNode_scalar_produces_scalar` proves a scalar lookahead
recovers exactly `.scalar (Scalar.mk content style none none none)`, position-generically (no
constraint on `ps.pos`) — the **parser-side leaf** of the per-element span-locality, INDEPENDENT of the
(harder, cross-state) scanner segment-equality.  This completes the dispatch family
([[ref-complete-projection-family-for-new-member]]) and is consumed by the future loop-locality
producer ([[ref-consumer-joint-before-producer]]).

## Why this probe (inhabitation debt: a position-generic lemma with no producer yet is "only ever a
hypothesis" — rule 3 — until it is shown to FIRE on a concrete mid-stream state)

`parseNode_scalar_produces_scalar` is a verified implication (no inhabitation debt of its own), but it
is verified-but-UNCONSUMED: nothing in the library calls it yet.  Per
[[inhabitation-debt-validate-target-defs]] rule 3, that is the alarm to EXHIBIT it firing — not on the
comfortable whole-stream START (position 1, already covered by `parseStream_three_tokens_scalar`) but
at the BOUNDARY the producer actually hits: a scalar element span **mid-stream** (`ps.pos ≥ 2`), where
position-genericity is the whole point.

* `seq_elem0_fires` / `seq_elem1_fires` / `map_key0_fires` / `map_val0_fires` `native_decide` that
  `parseNode` SUCCEEDS at the mid-stream scalar positions of `[a,b]` (pos 2, 4) and `{a:b}` (pos 3, 5)
  with exactly the scalar value — so the lemma's hypothesis `h` is satisfiable, not vacuous.
* `lemma_pins_seq_elem0` … `lemma_pins_map_val0` actually APPLY the lemma at those mid-stream states
  (discharging `h_peek` by `native_decide`), pinning the recovered value position-generically — the
  lemma in genuine use, not just stated.
* `seq_elem0_locality_at_leaf` / `map_key0_locality_at_leaf` ground the BRIDGE TARGET at the leaf: the
  mid-stream `parseNode` value EQUALS the standalone `parseYamlRaw (emit ·)` composed value — the
  per-element locality equation, on the smallest non-degenerate witnesses, with the parser half now
  pinned by the lemma.
* `dispatch_family_scalar_generic` re-exposes the lemma over an ARBITRARY `ps` — the position-generic
  twin of the collection dispatch lemmas, the shape the loop-locality producer consumes.

`#print axioms` pins the lemma to `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); the
`native_decide` grounding theorems add the compiler-reflection axioms transitively — `#print axioms`
it, never assume.
-/

namespace ParseNodeScalarDispatchLeaf

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures: plain scalars, a flow sequence, a flow mapping (the emitter double-quotes scalars). -/

def a : YamlValue := .scalar { content := "a", style := .plain }
def b : YamlValue := .scalar { content := "b", style := .plain }
def seqAB : YamlValue := .sequence .flow #[a, b] none none
def mapAB : YamlValue := .mapping .flow #[(a, b)] none none

/-- Whole-structure filtered token stream (`#[]` on the impossible error branch). -/
def tksSeq : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqAB) with | .ok t => t | _ => #[]
def tksMap : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapAB) with | .ok t => t | _ => #[]

/-- `ParseState`s pointed MID-STREAM at the scalar element spans:
    `[ "a" , "b" ]` body scalars at filtered positions 2 and 4;
    `{ "a" : "b" }` key/value scalars at filtered positions 3 and 5 (after the `key`/`value` markers). -/
def psSeq0 : ParseState := { tokens := tksSeq, pos := 2 }
def psSeq1 : ParseState := { tokens := tksSeq, pos := 4 }
def psMapK : ParseState := { tokens := tksMap, pos := 3 }
def psMapV : ParseState := { tokens := tksMap, pos := 5 }

/-! ## NON-VACUITY (rule 3): `parseNode` FIRES at each mid-stream scalar span with the scalar value —
    so the lemma's hypothesis `h : parseNode … = .ok (v, ps')` is satisfiable, not vacuous. -/

theorem seq_elem0_fires :
    (((parseNode psSeq0 200).map (·.1)).toOption
      == some (.scalar (Scalar.mk "a" .doubleQuoted none none none))) = true := by native_decide
theorem seq_elem1_fires :
    (((parseNode psSeq1 200).map (·.1)).toOption
      == some (.scalar (Scalar.mk "b" .doubleQuoted none none none))) = true := by native_decide
theorem map_key0_fires :
    (((parseNode psMapK 200).map (·.1)).toOption
      == some (.scalar (Scalar.mk "a" .doubleQuoted none none none))) = true := by native_decide
theorem map_val0_fires :
    (((parseNode psMapV 200).map (·.1)).toOption
      == some (.scalar (Scalar.mk "b" .doubleQuoted none none none))) = true := by native_decide

/-! ## THE LEMMA IN USE: apply `parseNode_scalar_produces_scalar` at each mid-stream state, pinning the
    recovered value position-generically (`h_peek` discharged by `native_decide`). -/

theorem lemma_pins_seq_elem0 (v : YamlValue) (ps' : ParseState)
    (h : parseNode psSeq0 200 = .ok (v, ps')) :
    v = .scalar (Scalar.mk "a" .doubleQuoted none none none) :=
  parseNode_scalar_produces_scalar psSeq0 200 "a" .doubleQuoted v ps' (by native_decide) h

theorem lemma_pins_seq_elem1 (v : YamlValue) (ps' : ParseState)
    (h : parseNode psSeq1 200 = .ok (v, ps')) :
    v = .scalar (Scalar.mk "b" .doubleQuoted none none none) :=
  parseNode_scalar_produces_scalar psSeq1 200 "b" .doubleQuoted v ps' (by native_decide) h

theorem lemma_pins_map_key0 (v : YamlValue) (ps' : ParseState)
    (h : parseNode psMapK 200 = .ok (v, ps')) :
    v = .scalar (Scalar.mk "a" .doubleQuoted none none none) :=
  parseNode_scalar_produces_scalar psMapK 200 "a" .doubleQuoted v ps' (by native_decide) h

theorem lemma_pins_map_val0 (v : YamlValue) (ps' : ParseState)
    (h : parseNode psMapV 200 = .ok (v, ps')) :
    v = .scalar (Scalar.mk "b" .doubleQuoted none none none) :=
  parseNode_scalar_produces_scalar psMapV 200 "b" .doubleQuoted v ps' (by native_decide) h

/-! ## BRIDGE TARGET AT THE LEAF: the mid-stream `parseNode` value EQUALS the standalone
    `parseYamlRaw (emit ·)` composed value — the per-element locality equation, grounded. -/

theorem seq_elem0_locality_at_leaf :
    (((parseNode psSeq0 200).map (·.1)).toOption
      == (parseYamlRaw (emit a)).toOption.map (fun d => (d.map YamlDocument.compose)[0]!.value)) = true := by
  native_decide

theorem seq_elem1_locality_at_leaf :
    (((parseNode psSeq1 200).map (·.1)).toOption
      == (parseYamlRaw (emit b)).toOption.map (fun d => (d.map YamlDocument.compose)[0]!.value)) = true := by
  native_decide

theorem map_key0_locality_at_leaf :
    (((parseNode psMapK 200).map (·.1)).toOption
      == (parseYamlRaw (emit a)).toOption.map (fun d => (d.map YamlDocument.compose)[0]!.value)) = true := by
  native_decide

theorem map_val0_locality_at_leaf :
    (((parseNode psMapV 200).map (·.1)).toOption
      == (parseYamlRaw (emit b)).toOption.map (fun d => (d.map YamlDocument.compose)[0]!.value)) = true := by
  native_decide

/-! ## FAMILY COMPLETENESS: the scalar member re-exposed over an ARBITRARY `ps` — the position-generic
    twin of the collection dispatch lemmas, the shape the loop-locality producer consumes. -/

theorem dispatch_family_scalar_generic (ps : ParseState) (fuel : Nat)
    (content : String) (style : ScalarStyle) (v : YamlValue) (ps' : ParseState)
    (h_peek : ps.peek? = some (.scalar content style))
    (h : parseNode ps fuel = .ok (v, ps')) :
    v = .scalar (Scalar.mk content style none none none) :=
  parseNode_scalar_produces_scalar ps fuel content style v ps' h_peek h

/-! ## R600: `parseNode_scalar_advances_by_one` -- position-advance at the scalar leaf

Companion to `parseNode_scalar_produces_scalar` (R587): same dispatch path, extracts the
SECOND pair component (the post-parse state) instead of the first (the parsed value).
Proved by the same unfolding: `parseNodeProperties_skip` returns `ps` unchanged (no tag/anchor);
`parseNodeContent` returns `ps.advance` (increments `pos` by 1); `applyNodeFinalization_pos`
shows finalization preserves position.

Verified-but-unconsumed: the loop-locality position-tracking producer threads this through
`parseFlowSequenceLoop_push_pointwise` to prove `ps_j.pos = 2 + 2*j` for each element `j`
of the all-scalar flow sequence parse loop.
-/

theorem advance_by_one_generic (ps : ParseState) (fuel : Nat)
    (content : String) (style : ScalarStyle) (v : YamlValue) (ps' : ParseState)
    (h_peek : ps.peek? = some (.scalar content style))
    (h : parseNode ps fuel = .ok (v, ps')) :
    ps'.pos = ps.pos + 1 :=
  parseNode_scalar_advances_by_one ps fuel content style v ps' h_peek h

/-- Inhabitation: R600 fires concretely on the mid-stream scalar position.
    Extract `.pos` as a `Nat` before comparing (avoids `Decidable YamlValue × ParseState`). -/
theorem advance_by_one_fires_concrete :
    (((parseNode psSeq0 200).map (·.2.pos)).toOption == some (psSeq0.pos + 1)) = true := by
  native_decide

/-! ## Axiom audit: the dispatch leaf is choice-clean (no `sorryAx`). -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseNode_scalar_produces_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseNode_scalar_produces_scalar

/-- info: 'L4YAML.Proofs.EmitterScannability.parseNode_scalar_advances_by_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseNode_scalar_advances_by_one

end ParseNodeScalarDispatchLeaf
