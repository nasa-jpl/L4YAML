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

/-! ## Rule 2 boundary strengthening (inhabitation-debt): the `[["a"]]` probe is VACUOUS
     on the two hardest span-locality conjuncts

Per [[inhabitation-debt-validate-target-defs]] rule 2 ("probe the BOUNDARY, not the middle")
and the R547 lesson ("a conjunct VACUOUS on your fixture is validated by NOBODY"): the original
witness `outerSeq = [["a"]]` is a SINGLE-element outer sequence.  The span-locality equality
`(standalone parse of emit items[i]) = items''[i]!` has (at least) three characteristic boundaries:

| # | Property parseNode must have | Fires on `[["a"]]`? |
|---|------------------------------|---------------------|
| A | reads MULTIPLE tokens forward (nested collection, depth > 0)          | YES (inner `["a"]`) |
| B | IGNORES TRAILING siblings (stops at its OWN matching close, not EOF)  | **NO** — one element, no trailing tokens |
| C | POSITION-INVARIANT at nonzero offset (element at index > 0)           | **NO** — only slot 0 |

Conjuncts B and C are exactly what makes span-locality nontrivial — and the `[["a"]]` probe
skips both.  The fixtures below FIRE B and C on both axes (seq and map), grounded on REAL emission
(rule 5: the arrays ARE `parseYamlRaw (emit ·)`, not hand-built).  If any YamlValue constructor
leaked a source position, these `native_decide`s would be `false`; all are `true`, so the
span-locality TARGET is inhabited AT ITS BOUNDARY — the eventual `parseNode_position_invariant`
proof is not an R540-style boundary-fragile trap. -/

def sc (s : String) : YamlValue := .scalar { content := s, style := .plain }
def flowSeq (its : Array YamlValue) : YamlValue := .sequence .flow its none none
def flowMap (ps : Array (YamlValue × YamlValue)) : YamlValue := .mapping .flow ps none none

/-- composed items of the whole-stream parse (seq axis). -/
def wholeItems (v : YamlValue) : Option (Array YamlValue) :=
  match parseYamlRaw (emit v) with
  | .ok docs => match (docs.map YamlDocument.compose)[0]!.value with
               | .sequence _ its _ _ => some its
               | _ => none
  | _ => none

/-- composed pairs of the whole-stream parse (map axis). -/
def wholePairs (v : YamlValue) : Option (Array (YamlValue × YamlValue)) :=
  match parseYamlRaw (emit v) with
  | .ok docs => match (docs.map YamlDocument.compose)[0]!.value with
               | .mapping _ ps _ _ => some ps
               | _ => none
  | _ => none

/-- standalone composed value of parsing just `emit v`. -/
def standaloneVal (v : YamlValue) : Option YamlValue :=
  match parseYamlRaw (emit v) with
  | .ok docs => some (docs.map YamlDocument.compose)[0]!.value
  | _ => none

/-! ### SEQ axis -/

/-- multi-element, non-scalar NOT last: `[ ["a"], ["b"], "c" ]`. -/
def seqMulti : YamlValue := flowSeq #[ flowSeq #[sc "a"], flowSeq #[sc "b"], sc "c" ]
/-- decoy: doubly-nested first element + trailing scalar `[ [["x"]], "y" ]`.  A naive
    "stop at the FIRST `]`" locality would mis-cut here; the true matching-close is exercised. -/
def seqDecoy : YamlValue := flowSeq #[ flowSeq #[flowSeq #[sc "x"]], sc "y" ]
/-- twins `[ ["a"], ["a"] ]`: identical subtrees at DIFFERENT offsets. -/
def seqTwins : YamlValue := flowSeq #[ flowSeq #[sc "a"], flowSeq #[sc "a"] ]

theorem seqMulti_size : (wholeItems seqMulti).map (·.size) = some 3 := by native_decide

/-- Conjunct B (ignores trailing siblings): slot 0 has TWO trailing siblings, yet its whole-stream
    value equals the standalone parse of `["a"]`. -/
theorem seqMulti_slot0_locality :
    ((wholeItems seqMulti).map (·[0]!) == standaloneVal (flowSeq #[sc "a"])) = true := by
  native_decide

/-- Conjuncts B+C (nonzero offset AND trailing siblings): slot 1 sits after `["a"]` and before
    `"c"`, yet equals the standalone parse of `["b"]`. -/
theorem seqMulti_slot1_locality :
    ((wholeItems seqMulti).map (·[1]!) == standaloneVal (flowSeq #[sc "b"])) = true := by
  native_decide

/-- Decoy: the doubly-nested first element parses to the SAME value standalone. -/
theorem seqDecoy_slot0_locality :
    ((wholeItems seqDecoy).map (·[0]!) == standaloneVal (flowSeq #[flowSeq #[sc "x"]])) = true := by
  native_decide

/-- Position-invariance made explicit: two identical subtrees at different token offsets compose
    to EQUAL values.  This is `false` iff a position leaks into `YamlValue`. -/
theorem seqTwins_position_invariance :
    (match wholeItems seqTwins with | some its => its[0]! == its[1]! | none => false) = true := by
  native_decide

/-! ### MAP axis -/

/-- multi-pair, nested value NOT last: `{ "a": ["p"], "b": ["q"] }`. -/
def mapMulti : YamlValue := flowMap #[ (sc "a", flowSeq #[sc "p"]), (sc "b", flowSeq #[sc "q"]) ]
/-- decoy: doubly-nested value + trailing pair `{ "a": [["z"]], "b": "w" }`. -/
def mapDecoy : YamlValue := flowMap #[ (sc "a", flowSeq #[flowSeq #[sc "z"]]), (sc "b", sc "w") ]

theorem mapMulti_size : (wholePairs mapMulti).map (·.size) = some 2 := by native_decide

/-- Value locality, slot 0 (nested value, trailing pair follows). -/
theorem mapMulti_val0_locality :
    ((wholePairs mapMulti).map (fun ps => ps[0]!.snd) == standaloneVal (flowSeq #[sc "p"])) = true := by
  native_decide

/-- Value locality, slot 1 (nonzero offset + nested value). -/
theorem mapMulti_val1_locality :
    ((wholePairs mapMulti).map (fun ps => ps[1]!.snd) == standaloneVal (flowSeq #[sc "q"])) = true := by
  native_decide

/-- Key locality, slot 0 (the map sorry's first conjunct is keyed on `.fst`). -/
theorem mapMulti_key0_locality :
    ((wholePairs mapMulti).map (fun ps => ps[0]!.fst) == standaloneVal (sc "a")) = true := by
  native_decide

/-- Decoy on the map axis: doubly-nested value equals its standalone parse. -/
theorem mapDecoy_val0_locality :
    ((wholePairs mapDecoy).map (fun ps => ps[0]!.snd) == standaloneVal (flowSeq #[flowSeq #[sc "z"]])) = true := by
  native_decide

/-! ## Proof plan: the sorry equality is a chain of THREE pieces (not one)

The boundary probes above confirm the TARGET is true; the universal proof factors the sorry's
locality equality `(parseYamlRaw (emit items[i]) composed)[0]!.value = items''[i]!` as:

* **P1 — whole-stream loop-value theorem** (general analog of the all-scalar
  `parseFlowSeqLoop_allScalar_value_at`): `items''[i]! = (parseNode {full_tokens, pos_i} fuel)`'s
  YamlValue, composed, where `pos_i` is the token offset at which element `i` starts.  Fuel
  induction on `parseFlowSequenceLoop`; the hard part is computing `pos_i` (bracket-balance
  bookkeeping), NOT specialised to scalars.
* **P2 — span-locality** (`parseNode_position_invariant`): the YamlValue component of
  `parseNode {full_tokens, pos_i} fuel` equals that of `parseNode {standalone_tokens, 1} fuel`
  whenever the token streams AGREE FORWARD (`∀ k, full[pos_i+k]?.val = standalone[1+k]?.val`).
  Mutual induction over the parser clique (parseNode / parseNodeContent / parseFlowSequenceLoop /
  parseFlowMappingLoop / …).  Only the FIRST component (YamlValue) is invariant — the output
  `ParseState.pos` advances by the same DELTA but differs absolutely, so the lemma must project
  the value, not equate whole states (`YamlValue` is position-free — see the agent map; `.value`
  after `compose` carries no offsets, which is why the probes above are `= true`).
* **P3 — standalone compose** (already essentially available): the standalone
  `parseYamlRaw (emit items[i])` composed value equals the compose of `parseNode {standalone, 1}`.

Chain: `standalone value ={P3}= compose(parseNode standalone) ={P2}= compose(parseNode full@pos_i)
={P1}= items''[i]!`.  The **all-scalar branch (R609) collapsed P1+P3 and SKIPPED P2** because a
scalar's parseNode reads exactly one token — position-trivial.  Non-scalars need P2 in full.
Map axis is identical with `parseFlowMappingLoop` and key/value projections (`ps[i]!.fst/.snd`).

The two conjuncts the `[["a"]]` probe left vacuous (B: ignore-trailing; C: nonzero-offset) are
EXACTLY the two properties P2's mutual induction must establish — so the boundary fixtures here
are the concrete regression that P2 must generalise. -/

/-! ## Axiom audit -/

/-- info: 'NonAllScalarLocality.locality_eq_slot0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 locality_eq_slot0._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms locality_eq_slot0

end NonAllScalarLocality
