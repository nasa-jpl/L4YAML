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
open L4YAML.Scanner
open L4YAML.Proofs.RoundTrip
open L4YAML.Proofs.EmitterScannability
open L4YAML.Proofs.ParserGrammable

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

/-! ## P2 statement-shape probe (inhabitation-debt): the naive `parseNode_position_invariant`
     is FALSE / unusable on THREE independent axes

The probes above confirm the DOWNSTREAM equality (`items''[i]! = standalone value`) is true.  But
before building P2's mutual induction we must fix its EXACT statement.  The naive form (the earlier
plan below, and [[ref-front-b-nonallscalar-blocking]]'s first draft) was:

    parseNode {t1, p1} f  =  parseNode {t2, p2} f        given  ∀ k, t1[p1+k]? = t2[p2+k]?

**Every clause of that is wrong.**  We disprove/confirm on REAL tokens, `p2_full = [["a"],["b"]]`
and standalone item `p2_std0 = ["a"]`.  `scanFiltered` places item 0's `parseNode` at pos 2 in the
full stream, pos 1 standalone (read off by `#eval`):

    full:       [ streamStart, `[`@0, `[`@1, "a"@2, `]`@5, `,`@6, `[`@8, "b"@9, `]`@12, `]`@13, end@14 ]
    standalone: [ streamStart, `[`@0,        "a"@1, `]`@4,                                    end@5  ]

* **Axis A — the conclusion must project the VALUE, not the whole `ParseState`.**  Output `pos`
  differs (5 full vs 4 standalone), so whole-result equality is FALSE; only `.map (·.1)` agrees.
* **Axis B — the agreement hypothesis must be BOUNDED to the span, not `∀ k`.**  Forward `.val`s
  agree for k = 0,1,2 (`[ "a" ]`) then DIVERGE at k = 3 (full `flowEntry` vs standalone `streamEnd`).
  So `∀ k` agreement is UNSATISFIABLE in the application: the `∀ k` lemma, however true, can NEVER be
  applied to close sorries 3+4.  This is the load-bearing correction — it forces a bounded-span
  FRAME lemma (P2a below), strictly more work than a clean unbounded induction.
* **Axis C — agreement is on the token `.val`, not the `Positioned` token.**  The same `[` carries
  offset 1 in the full stream, 0 standalone: `Positioned`-equality is FALSE within the span,
  `.val`-equality TRUE.  parseNode's value must (and does) ignore embedded offsets — `nodeStartPos`
  only feeds `nodePositions` (tracking gated off) and `YamlValue` is position-free.
* **Axis D — anchors (prose caveat; not fired by these fixtures).**  The whole-stream parse carries
  anchors accumulated from PRIOR siblings; standalone does not.  The value is still invariant because
  `parseNode` returns `.alias name` UNRESOLVED (resolution is deferred to `compose`) and the
  `parseYamlRaw (emit items[i]) = .ok rd` hypothesis forces item i's aliases to be self-contained
  (else standalone would fail `undefinedAlias`).  `emit` never emits a per-item alias to a sibling
  anchor, so the extra inherited anchors are inert.  The `Prop` below fixes `anchors := anch` on both
  sides for this reason; a fully general statement would carry a "no free alias" side condition. -/

def p2_full : YamlValue := flowSeq #[ flowSeq #[sc "a"], flowSeq #[sc "b"] ]
def p2_std0 : YamlValue := flowSeq #[sc "a"]
def p2_toks (v : YamlValue) : Array (Positioned YamlToken) :=
  match scanFiltered (emit v) with | .ok t => t | .error _ => #[]
def p2_psF : ParseState := { tokens := p2_toks p2_full, pos := 2 }
def p2_psS : ParseState := { tokens := p2_toks p2_std0, pos := 1 }

/-- **Axis C**: same token `.val` at the span start, but DIFFERENT `Positioned` (offset 1 vs 0). -/
theorem p2_axisC_val_agrees_positioned_differs :
    ( ((p2_toks p2_full)[2]!.val == (p2_toks p2_std0)[1]!.val)
      && !((p2_toks p2_full)[2]! == (p2_toks p2_std0)[1]!) ) = true := by native_decide

/-- **Axis B**: forward `.val` agreement is bounded (k = 0,1,2) then DIVERGES at k = 3, so the
    `∀ k` hypothesis is unsatisfiable in the application (full has `flowEntry`, standalone `streamEnd`). -/
theorem p2_axisB_agreement_bounded_then_diverges :
    ( ((p2_toks p2_full)[2]!.val == (p2_toks p2_std0)[1]!.val)
      && ((p2_toks p2_full)[3]!.val == (p2_toks p2_std0)[2]!.val)
      && ((p2_toks p2_full)[4]!.val == (p2_toks p2_std0)[3]!.val)
      && !((p2_toks p2_full)[5]!.val == (p2_toks p2_std0)[4]!.val) ) = true := by native_decide

/-- **Axis A + CRUX**: the parseNode VALUE is invariant across position/stream, but the output
    `ParseState.pos` is NOT (5 vs 4) — the lemma must project `·.1`.  This is the target's core. -/
theorem p2_axisA_value_invariant_state_not :
    ( ((parseNode p2_psF 100).toOption.map (·.1) == (parseNode p2_psS 100).toOption.map (·.1))
      && !((parseNode p2_psF 100).toOption.map (·.2.pos)
            == (parseNode p2_psS 100).toOption.map (·.2.pos)) ) = true := by native_decide

/-- The refined P2 target — **value span-locality** — as a typechecked `Prop`.  Note the corrections
    forced by the axes above: BOUNDED `.val`-agreement hypothesis (`k < n`, on `·.val`), and a
    VALUE-projected conclusion (`.map (·.1)`).  The two `ps'.pos ≤ p + n` clauses are the FRAME
    side-condition **P2a** (parseNode stays within its span), for which `parseNode_pos_mono_all`
    is the established mutual-induction precedent.  Inhabitation-debt discipline: this is captured as
    a well-typed `Prop` and validated at the boundary by the `native_decide`s above — it is NOT
    proved here, and NO `sorry` asserts it. -/
def ParseNodeValueSpanLocal : Prop :=
  ∀ (t1 t2 : Array (Positioned YamlToken)) (p1 p2 f n : Nat)
    (anch : Array (String × YamlValue)),
    (∀ k, k < n → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))) →
    (∀ v ps', parseNode { tokens := t1, pos := p1, anchors := anch } f = .ok (v, ps') →
      ps'.pos ≤ p1 + n) →
    (∀ v ps', parseNode { tokens := t2, pos := p2, anchors := anch } f = .ok (v, ps') →
      ps'.pos ≤ p2 + n) →
    (parseNode { tokens := t1, pos := p1, anchors := anch } f).map (·.1)
      = (parseNode { tokens := t2, pos := p2, anchors := anch } f).map (·.1)

/-! ## P2a (FRAME) + Bridge birth-probes (inhabitation-debt Rule 1 + Rule 2)

The P2 disproof above fixed P2b's statement (`ParseNodeValueSpanLocal`).  But that statement has two
sub-targets that are ALSO to-be-built and carry their own inhabitation debt: its FRAME side-conditions
(`ps'.pos ≤ p + n`, produced by **P2a**) and its bounded-`.val`-agreement HYPOTHESIS (produced by the
**Bridge**).  Per [[inhabitation-debt-validate-target-defs]] rule 1 (probe at birth) and rule 2 (probe
the BOUNDARY), each is birth-probed here on REAL tokens BEFORE the mutual induction is built.

**Plan correction found while locating the P2a precedent.**  The 4-piece plan below (and
[[ref-front-b-nonallscalar-blocking]]) called P2a "a strengthening of `parseNode_pos_mono_all`."  It is
NOT a strengthening: `parseNode_pos_mono_all` (ParserWellBehaved.lean, `ParseNodePosMono`) proves ONLY
the LOWER bound `ps'.pos ≥ ps.pos` — its whole content is "position never decreases," which says nothing
about WHERE parseNode stops.  P2a needs the UPPER bound `ps'.pos = p + span`, a structurally different
fact that must LOCATE the Dyck-matching close.  The machinery for that already exists
(`flowBracketBalance_matching_close`, ParserGrammableBase.lean).  So P2a reuses the mono induction's
SHAPE (mutual over the flow sub-clique) but threads bracket balance, not `≥`.  The per-element LEAF
precedent is `parseNode_scalar_advances_by_one` (`ps'.pos = ps.pos + 1`); P2a is its non-scalar analog
(`ps'.pos = matchingClose + 1`).  The all-scalar loop proof `parseFlowSeqLoop_allScalar_value_at_aux`
threads exactly this leaf (plus `parseNode_scalar_produces_scalar` = P2b's leaf) with a CLOSED-FORM
position invariant `2*k+1`; for non-scalars the widths vary, so P1's invariant becomes cumulative
`pos_i = 2 + Σ_{j<i}(width_j + 1)` and the two leaves become mutual-inductive.  This confirms P2a is a
GENUINE separate leaf, NOT absorbed into P1. -/

/-- **P2a target — FRAME (parseNode reads exactly its bracket span).**  Upper-bound companion to the
    lower-bound `parseNode_pos_mono_all`; together they pin `ps'.pos`.  This is exactly the FRAME
    hypothesis `ParseNodeValueSpanLocal` consumes.  The Dyck conditions say `[p, p+n)` is a balanced,
    first-return span (`tokens[p]` opens, balance stays ≥ 1 strictly inside, hits 0 at `p+n`) — the
    matching close `flowBracketBalance_matching_close` produces.  **The `0 < n` guard is load-bearing**
    (found this pass while going to prove P2a): without it `n = 0` satisfies both Dyck conditions
    vacuously (`flowBracketBalance t p (p + 0) = flowBracketBalance t p p = 0` by the empty-range branch;
    the interior `∀ i, p < i < p` is vacuous) while forcing the FALSE `ps'.pos = p` — `parseNode` always
    advances on success.  `p2a_n0_hole_refutes_unguarded` refutes the unguarded form on a real witness,
    and `frameSpan_unique` shows the guarded conditions pin `n` uniquely.  Typechecked target, validated
    at the boundary by `p2a_*` below; NOT proved, NO `sorry`. -/
def ParseNodeFrameWithinSpan : Prop :=
  ∀ (t : Array (Positioned YamlToken)) (p n f : Nat) (v : YamlValue) (ps' : ParseState)
    (anch : Array (String × YamlValue)),
    0 < n →
    flowBracketBalance t p (p + n) = 0 →
    (∀ i, p < i → i < p + n → flowBracketBalance t p i ≥ 1) →
    parseNode { tokens := t, pos := p, anchors := anch } f = .ok (v, ps') →
    ps'.pos = p + n

/-! ### P2a target CORRECTION (inhabitation-debt Rule 2 — the `n = 0` boundary)

Going to PROVE P2a, the first move is Rule 1 / Rule 2: probe the target at its BOUNDARY.  The degenerate
`n = 0` edge — never fired by the `p2a_*` span probes, which all use the true `n > 0` span — REFUTES the
unguarded frame.  `flowBracketBalance t p (p + 0) = flowBracketBalance t p p = 0` (empty range; def
`if lo ≥ hi then 0`) and the interior quantifier is vacuous, so BOTH Dyck hypotheses hold at `n = 0` for
ANY `p` — yet the conclusion demands `ps'.pos = p`, and `parseNode` always advances on success.  The fix
is the `0 < n` guard now in the def.  This is the third Rule-2 save on the Front-B frontier (cf. the
Axis-B `∀k`-unsat and the mono-lower-bound corrections): a birth-probed `Prop` that typechecks and
passes every span probe can still be FALSE at an un-probed edge. -/

/-- **Refutation of the UNGUARDED frame at `n = 0`.**  On the real witness `p2_full` at `p = 2`:
    the first Dyck hypothesis holds (`flowBracketBalance … 2 (2+0) = 0`, empty span) and the interior
    hypothesis is vacuous, so the unguarded `ParseNodeFrameWithinSpan` would demand `ps'.pos = 2 + 0 = 2`.
    But `parseNode` lands at `5`.  Hence the unguarded target is FALSE; the `0 < n` guard is necessary. -/
theorem p2a_n0_hole_refutes_unguarded :
    ( (flowBracketBalance (p2_toks p2_full) 2 (2 + 0) == (0 : Int))
      && ((parseNode { tokens := p2_toks p2_full, pos := 2 } 100).toOption.map (·.2.pos) == some 5)
      && !((5 : Nat) == 2 + 0) ) = true := by native_decide

/-- **Guarded conditions pin the span uniquely.**  With `0 < n`, the balanced-first-return conditions
    determine `n`: two positive spans that both balance to 0 with a strictly-positive interior are equal
    (else the smaller span's endpoint sits strictly inside the larger, where the interior floor forces
    balance ≥ 1, contradicting its own balance-0).  Pure `flowBracketBalance` combinatorics — no
    `parseNode`.  This is the well-formedness the `0 < n` guard restores (the conclusion `ps'.pos = p + n`
    now names a UNIQUE `n`) and a genuine building block: it lets the frame's `n` be identified with the
    `flowBracketBalance_matching_close` span. -/
theorem frameSpan_unique
    (t : Array (Positioned YamlToken)) (p n1 n2 : Nat)
    (h1pos : 0 < n1) (h2pos : 0 < n2)
    (h1zero : flowBracketBalance t p (p + n1) = 0)
    (h2zero : flowBracketBalance t p (p + n2) = 0)
    (h1int : ∀ i, p < i → i < p + n1 → flowBracketBalance t p i ≥ 1)
    (h2int : ∀ i, p < i → i < p + n2 → flowBracketBalance t p i ≥ 1) :
    n1 = n2 := by
  rcases Nat.lt_trichotomy n1 n2 with h | h | h
  · have hbad := h2int (p + n1) (by omega) (by omega)
    rw [h1zero] at hbad; omega
  · exact h
  · have hbad := h1int (p + n2) (by omega) (by omega)
    rw [h2zero] at hbad; omega

/-! ### P2a boundary probes -- parseNode advances to EXACTLY the matching close, never to EOF.

Token layout (`#eval`-read, confirmed against `scanFiltered (emit ·)`):

    full [["a"],["b"]]:  0 ss, 1 `[`, 2 `[`, 3 "a", 4 `]`, 5 `,`, 6 `[`, 7 "b", 8 `]`, 9 `]`, 10 se
    seqDecoy [[["x"]],"y"]: 0 ss,1 `[`,2 `[`,3 `[`,4 "x",5 `]`,6 `]`,7 `,`,8 "y",9 `]`,10 se

`p2_full` item 0 opens at pos 2 (span 3 → close@4); item 1 (the LAST element) opens at pos 6
(span 3 → close@8, outer close@9, EOF@10). -/

/-- **P2a boundary (seq).**  Item 0 parseNode: pos 2 → 5 (= 2 + span 3).  Item 1 is the LAST element,
    yet its parseNode lands at 9 (= 6 + span 3) — pointing AT the outer `]`@9, having consumed only its
    own `[b]` (tokens 6,7,8).  It does NOT run to EOF (size 11, streamEnd@10).  The frame is TIGHT. -/
theorem p2a_frame_seq_last_element_stops_at_own_close :
    ( ((parseNode { tokens := p2_toks p2_full, pos := 2 } 100).toOption.map (·.2.pos) == some 5)
      && ((parseNode { tokens := p2_toks p2_full, pos := 6 } 100).toOption.map (·.2.pos) == some 9) )
      = true := by native_decide

def p2_seqDecoy : YamlValue := flowSeq #[ flowSeq #[flowSeq #[sc "x"]], sc "y" ]

/-- **P2a decoy (matching close, not first close).**  The doubly-nested item 0 `[["x"]]` opens at pos 2;
    the FIRST `]` is at pos 5, the MATCHING close at pos 6.  parseNode lands at 7 (= 2 + span 5) —
    skipping BOTH closes and stopping at the `flowEntry`@7, not mis-cutting at the first `]`@5.  This is
    the boundary a naive "stop at the first close" frame would fail. -/
theorem p2a_frame_seq_decoy_matching_not_first :
    ((parseNode { tokens := p2_toks p2_seqDecoy, pos := 2 } 100).toOption.map (·.2.pos) == some 7)
      = true := by native_decide

def p2_mapMulti : YamlValue := flowMap #[ (sc "a", flowSeq #[sc "p"]), (sc "b", flowSeq #[sc "q"]) ]

/-- **P2a boundary (map value axis).**  In `{ "a":["p"], "b":["q"] }` the value `["p"]` opens at pos 5
    (→ 8), and the LAST value `["q"]` opens at pos 12 (→ 15) — pointing AT the `}`@15, not running into
    the mapping close or EOF (size 17).  Confirms the frame is tight on the map value axis too. -/
theorem p2a_frame_map_value_stops_at_own_close :
    ( ((parseNode { tokens := p2_toks p2_mapMulti, pos := 5 } 100).toOption.map (·.2.pos) == some 8)
      && ((parseNode { tokens := p2_toks p2_mapMulti, pos := 12 } 100).toOption.map (·.2.pos) == some 15) )
      = true := by native_decide

/-! ### Bridge boundary probes -- the emitted tokens of element i are a CONTIGUOUS `.val`-run.

The Bridge discharges P2b's bounded-`.val`-agreement hypothesis: item i's tokens in the whole stream
are token-for-token (on `.val`) the standalone tokens of `scanFiltered (emit items[i])` over item i's
span.  Its general (non-scalar) form is the analog of the all-scalar R596/R597
(`emitList_allScalar_body_content_at`, `scanFiltered_emitSeq_allScalar_token_at`), proved by induction
on `emit.emitList` — but with VARIABLE element widths, unlike the fixed width-2 all-scalar case.  We do
NOT fabricate a `Prop` (its honest statement needs the `pos_i`/`span_i` bookkeeping R596/R597 encode);
we validate the concrete contiguity at a NONZERO offset (`p2_axisB` already covers slot 0). -/

def p2_std1 : YamlValue := flowSeq #[sc "b"]

/-- **Bridge boundary (nonzero offset).**  Item 1 `["b"]` opens at pos 6 in the whole stream; its body
    run `full[6,7,8].val` equals the standalone `scanFiltered (emit ["b"])` body run `std1[1,2,3].val`
    token-for-token.  Combined with `p2_axisB` (slot 0 agrees for k < 3 then diverges), this is the
    Bridge's contiguity at both a zero and a nonzero slot. -/
theorem bridge_seq_slot1_contiguous_val :
    ( ((p2_toks p2_full)[6]!.val == (p2_toks p2_std1)[1]!.val)
      && ((p2_toks p2_full)[7]!.val == (p2_toks p2_std1)[2]!.val)
      && ((p2_toks p2_full)[8]!.val == (p2_toks p2_std1)[3]!.val) ) = true := by native_decide

/-! ## Proof plan (CORRECTED): the sorry equality is a chain of FOUR pieces

The earlier 3-piece plan (P1/P2/P3) understated the work: Axis B splits the old "P2" into a FRAME
lemma plus a value lemma, and adds a scanner-side bridge to discharge the bounded agreement.  The
sorry's locality equality `(parseYamlRaw (emit items[i]) composed)[0]!.value = items''[i]!` factors as:

* **P1 — whole-stream loop-value theorem** (general analog of all-scalar
  `parseFlowSeqLoop_allScalar_value_at`, whose aux `parseFlowSeqLoop_allScalar_value_at_aux` is the
  exact template): `items''[i]! = compose (parseNode {full, pos_i} fuel).1`.  Fuel induction on
  `parseFlowSequenceLoop`, threading P2a (advance) + P2b (value) as the per-element leaves — precisely
  where the all-scalar aux threads `parseNode_scalar_advances_by_one` + `parseNode_scalar_produces_scalar`.
  The hard part is the position invariant: the all-scalar closed form `pos_k = 2*k+1` generalises to the
  CUMULATIVE `pos_i = 2 + Σ_{j<i}(width_j + 1)` because element widths now vary.  *Missing.*
* **P2a — FRAME / reads-within-span** (NEW, forced by Axis B) = `ParseNodeFrameWithinSpan` above:
  `parseNode {t, p} f = .ok (_, ps') → ps'.pos = p + n` on a Dyck-balanced span `[p, p+n)` with `0 < n`.
  **NOT a strengthening of `parseNode_pos_mono_all`** (that proves only the LOWER bound `ps'.pos ≥
  ps.pos`); P2a is the UPPER bound and must LOCATE the matching close — `flowBracketBalance_matching_close`
  supplies the span, and P2a reuses the mono induction's SHAPE (mutual over the flow sub-clique) while
  threading balance.  Leaf precedent: `parseNode_scalar_advances_by_one` (the `n = 1` case).  The `0 < n`
  guard was found necessary this pass (`n = 0` refuted the unguarded form —
  `p2a_n0_hole_refutes_unguarded`); with it the span is unique (`frameSpan_unique`, landed sorry-free),
  so the conclusion's `n` can be identified with the matching-close span.  Probed tight at the boundary
  (`p2a_*`).  *Missing (the parseNode mutual induction; correction + uniqueness landed).*
* **P2b — value span-locality** = `ParseNodeValueSpanLocal` above: value invariant under BOUNDED
  `.val`-agreement + the two frame side-conditions.  Mutual induction over the parser clique
  (parseNode / parseNodeContent / parseFlowSequenceLoop / parseFlowMappingLoop / …), projecting the
  value and jointly tracking consumed length.  This is the crux; no existing lemma. *Missing.*
* **Bridge — scanner-span agreement** (NEW, discharges P2b's hypothesis): the emitted tokens of
  `items[i]` occur as a CONTIGUOUS `.val`-run inside the emitted tokens of the whole sequence, i.e.
  `∀ k < span_i, full[pos_i+k]?.val = standalone[1+k]?.val`.  General (non-scalar) analog of the
  all-scalar R596/R597 (`emitList_allScalar_body_content_at`, `scanFiltered_emitSeq_allScalar_token_at`).
  *Missing.*
* **P3 — standalone compose** (essentially available): standalone `parseYamlRaw (emit items[i])`
  composed value equals `compose (parseNode {standalone, 1}).1`.

Chain: `standalone ={P3}= compose(parseNode std@1) ={P2b+Bridge}= compose(parseNode full@pos_i)
={P1}= items''[i]!`.  The **all-scalar branch (R609) collapsed P1+P3 and SKIPPED P2a/P2b/Bridge**
because a scalar's parseNode reads exactly one token — span-trivial, `.val`-agreement is the single
token, no framing needed.  Non-scalars need all four.  Map axis mirrors with `parseFlowMappingLoop`
and key/value projections (`ps[i]!.fst/.snd`).

**Build order (cheapest first).**  P2a and the Bridge are the cheapest: both are birth-probed above and
lean on existing machinery (`flowBracketBalance_matching_close`; R596/R597).  P2b is the crux mutual
induction (consumes P2a's frame + the Bridge's agreement).  P1 threads P2a+P2b at the loop and computes
the cumulative `pos_i`.  Each is a self-contained unit (the all-scalar R596/R597/R601/R602 were each
their own).

The `[["a"]]` probe left conjuncts B (ignore-trailing) and C (nonzero-offset) vacuous; the SEQ/MAP
fixtures fire them; the three axis probes disprove the naive P2; and the `p2a_*`/`bridge_*` probes pin
P2a tight and the Bridge contiguous at a nonzero offset — together they are the concrete regression the
eventual P1/P2a/P2b/Bridge proofs must satisfy. -/

/-! ## Axiom audit -/

/-- info: 'NonAllScalarLocality.locality_eq_slot0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 locality_eq_slot0._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms locality_eq_slot0

/-- info: 'NonAllScalarLocality.p2a_n0_hole_refutes_unguarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 p2a_n0_hole_refutes_unguarded._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms p2a_n0_hole_refutes_unguarded

/-! The span-uniqueness building block is `sorry`-free and `Classical`-free: `[propext, Quot.sound]`
    only (`omega` on the arithmetic goal `n1 = n2` does not pull `Classical.choice`). -/
/-- info: 'NonAllScalarLocality.frameSpan_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frameSpan_unique

end NonAllScalarLocality
