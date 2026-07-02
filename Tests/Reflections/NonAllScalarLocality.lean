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

/-- The refined P2 target — **value span-locality** — as a typechecked `Prop`.  Corrections forced by
    the axes above: BOUNDED `.val`-agreement hypothesis (`k < n`, on `·.val`) and a VALUE-projected
    conclusion.  **A FOURTH correction, found this pass (2026-07-01): the conclusion must be
    error-INSENSITIVE** — `.toOption.map (·.1)` (failure ↦ `none`), NOT the `Except`-level `.map (·.1)`.
    parseNode's failure payload is position-dependent (fuel-0 returns `.error (.nestingDepthExceeded
    ps.currentLine)`, and `currentLine` reads the current token's `.pos.line`), so the error-sensitive
    `.map` form is FALSE at the FAILING boundary: two agreeing positions on different lines fail with
    different errors while the agreement holds and the frame conditions are vacuous.  `p2b_map_form_false`
    refutes it; `p2b_toOption_form_survives` shows the corrected form survives that witness.  The earlier
    probes ALREADY projected through `.toOption` (Axis A) — only the `def` was over-strong.  The two
    `ps'.pos ≤ p + n` clauses are the FRAME side-condition **P2a**.  Inhabitation-debt discipline:
    captured as a well-typed `Prop`, validated at the SUCCESS boundary (axes above) AND the FAILING
    boundary (`p2b_*` below); NOT proved here, NO `sorry`. -/
def ParseNodeValueSpanLocal : Prop :=
  ∀ (t1 t2 : Array (Positioned YamlToken)) (p1 p2 f n : Nat)
    (anch : Array (String × YamlValue)),
    (∀ k, k < n → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))) →
    (∀ v ps', parseNode { tokens := t1, pos := p1, anchors := anch } f = .ok (v, ps') →
      ps'.pos ≤ p1 + n) →
    (∀ v ps', parseNode { tokens := t2, pos := p2, anchors := anch } f = .ok (v, ps') →
      ps'.pos ≤ p2 + n) →
    (parseNode { tokens := t1, pos := p1, anchors := anch } f).toOption.map (·.1)
      = (parseNode { tokens := t2, pos := p2, anchors := anch } f).toOption.map (·.1)

/-! ### P2b projection CORRECTION (inhabitation-debt Rule 2 — the FAILING boundary was never probed)

The success-boundary probes above (`p2_axisA` …) all project through `.toOption`, but the `def` was
first written with the `Except`-level `.map (·.1)`, which is error-SENSITIVE.  The failing boundary was
never exercised, and it REFUTES the `.map` form: parseNode's fuel-0 error is
`.nestingDepthExceeded ps.currentLine`, and `currentLine` reads the current token's `.pos.line`, so two
agreeing positions on different lines fail with different errors.  Witness: a single scalar token,
identical `.val`, `.pos.line` 0 vs 1.  This is a textbook Rule-2 catch — a `Prop` that passes every
SUCCESS probe was still false at the un-probed FAILING edge; see [[inhabitation-debt-validate-target-defs]]. -/

/-- One scalar token at a chosen source line; identical `.val`, different `.pos.line`. -/
def p2b_tokL (line : Nat) : Array (Positioned YamlToken) :=
  #[ { pos := { offset := 0, line := line, col := 0 }, val := .scalar "x" .plain } ]

/-- Decidable projection exposing the position-dependent fuel-0 error line. -/
def p2b_errLine : Except ScanError YamlValue → Option Nat
  | .error (.nestingDepthExceeded l) => some l
  | _ => none

/-- **The error-SENSITIVE `.map (·.1)` form of value span-locality is FALSE** — the reason the `def`
    above projects through `.toOption`.  At `f = 0` both parses fail with `.nestingDepthExceeded
    ps.currentLine`; the bounded agreement holds (identical `.val`) and both frame conditions are
    vacuous (no `.ok` on failure), yet the two `Except`-mapped conclusions carry different error lines. -/
theorem p2b_map_form_false :
    ¬ (∀ (t1 t2 : Array (Positioned YamlToken)) (p1 p2 f n : Nat)
        (anch : Array (String × YamlValue)),
        (∀ k, k < n → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))) →
        (∀ v ps', parseNode { tokens := t1, pos := p1, anchors := anch } f = .ok (v, ps') →
          ps'.pos ≤ p1 + n) →
        (∀ v ps', parseNode { tokens := t2, pos := p2, anchors := anch } f = .ok (v, ps') →
          ps'.pos ≤ p2 + n) →
        (parseNode { tokens := t1, pos := p1, anchors := anch } f).map (·.1)
          = (parseNode { tokens := t2, pos := p2, anchors := anch } f).map (·.1)) := by
  intro H
  have hcon := H (p2b_tokL 0) (p2b_tokL 1) 0 0 0 1 #[]
    (by intro k hk; rcases k with _ | m
        · decide
        · omega)
    (by intro v ps' h
        have hno : (parseNode { tokens := p2b_tokL 0, pos := 0, anchors := #[] } 0).toOption.isSome = false := by
          native_decide
        rw [h] at hno; simp [Except.toOption] at hno)
    (by intro v ps' h
        have hno : (parseNode { tokens := p2b_tokL 1, pos := 0, anchors := #[] } 0).toOption.isSome = false := by
          native_decide
        rw [h] at hno; simp [Except.toOption] at hno)
  have h0 : p2b_errLine ((parseNode { tokens := p2b_tokL 0, pos := 0, anchors := #[] } 0).map (·.1)) = some 0 := by
    native_decide
  have h1 : p2b_errLine ((parseNode { tokens := p2b_tokL 1, pos := 0, anchors := #[] } 0).map (·.1)) = some 1 := by
    native_decide
  rw [hcon, h1] at h0
  exact absurd h0 (by decide)

/-- The corrected `.toOption.map` form SURVIVES the witness that killed the `.map` form: both parses
    fail, `.toOption` sends both to `none`, so the conclusion holds. -/
theorem p2b_toOption_form_survives :
    ((parseNode { tokens := p2b_tokL 0, pos := 0, anchors := #[] } 0).toOption.map (·.1)
      == (parseNode { tokens := p2b_tokL 1, pos := 0, anchors := #[] } 0).toOption.map (·.1)) = true := by
  native_decide

/-! ### P2b SCALAR LEAF — the first branch of the corrected `ParseNodeValueSpanLocal`, `sorry`-free

With P2b's statement fixed to `.toOption.map`, its eventual mutual induction's FIRST branch — a scalar
head — discharges NOW, and the proof reveals a simplification worth recording: **the scalar case needs
NEITHER frame side-condition NOR the `k ≥ 1` agreement.**  A scalar-head parse is trailing-independent
(`parseNode_scalar_produces_scalar` routes the scalar peek straight to its value, and
`applyNodeFinalization` leaves a scalar head untouched), so the recovered value depends on the head
token alone — pinned equal across the two positions by agreement at `k = 0` (needing only `0 < n`).
Three source-shaped facts, the branch, then birth/boundary/fires probes on REAL emission. -/

/-- Scalar-head parse SUCCEEDS (`.ok`) for any positive fuel — the forward companion of the
    hypothesis-driven `parseNode_scalar_produces_scalar`. -/
theorem parseNode_scalar_head_isOk (ps : ParseState) (n : Nat)
    (content : String) (style : ScalarStyle)
    (h_peek : ps.peek? = some (.scalar content style)) :
    ∃ vp, parseNode ps (n + 1) = .ok vp := by
  have h_np : parseNodeProperties ps = .ok ({}, ps) :=
    L4YAML.Proofs.ParserWellBehaved.parseNodeProperties_skip ps (by rw [h_peek]; trivial)
  have h_vnp : ∀ p, validateNodeProps ps p ({} : NodeProperties) = .ok () := by
    intro p; unfold validateNodeProps
    simp only [h_peek, bind, Except.bind, pure, Except.pure]; rfl
  have h_pnc : parseNodeContent ps n ({} : NodeProperties)
      = .ok (YamlValue.scalar { content := content, style := style }, ps.advance) := by
    unfold parseNodeContent; rw [h_peek]
  unfold parseNode
  simp only [h_peek, bind, Except.bind, pure, Except.pure, h_np, h_vnp, h_pnc]
  exact ⟨_, rfl⟩

/-- Scalar-head parse's recovered VALUE (under `.toOption.map`) is exactly the head scalar,
    position-generic — the single-sided leaf fact both sides of the equality reduce to. -/
theorem parseNode_scalar_toOption_value (ps : ParseState) (f : Nat)
    (content : String) (style : ScalarStyle)
    (h_peek : ps.peek? = some (.scalar content style)) (hf : 0 < f) :
    (parseNode ps f).toOption.map (·.1) = some (.scalar (Scalar.mk content style none none none)) := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  obtain ⟨⟨v, ps'⟩, hok⟩ := parseNode_scalar_head_isOk ps n content style h_peek
  have hv : v = .scalar (Scalar.mk content style none none none) :=
    parseNode_scalar_produces_scalar ps (n + 1) content style v ps' h_peek hok
  rw [hok]; simp [Except.toOption, hv]

/-- Plumbing: a `ParseState`'s `peek?` is exactly the array-lookup of its position, projected to `.val`
    (`getElem!` in `peek?` ↔ bounded `getElem?`).  Converts the bounded-`.val`-agreement HYPOTHESIS of
    `ParseNodeValueSpanLocal` into a `peek?` equality. -/
theorem peek_eq_getElem_map (t : Array (Positioned YamlToken)) (p : Nat)
    (a : Array (String × YamlValue)) :
    ({ tokens := t, pos := p, anchors := a } : ParseState).peek? = t[p]?.map (·.val) := by
  unfold ParseState.peek?
  by_cases h : p < t.size
  · simp only [if_pos h, getElem?_pos t p h, getElem!_pos t p h, Option.map_some]
  · simp only [if_neg h, getElem?_neg t p h, Option.map_none]

/-- **The P2b SCALAR LEAF** — the scalar-head branch of `ParseNodeValueSpanLocal`, discharged
    `sorry`-free and WITHOUT the frame side-conditions or the `k ≥ 1` agreement.  From agreement at
    `k = 0` (`0 < n`) both start positions peek the same scalar; each side's value is then that scalar
    (or `none` at `f = 0`), so the two `.toOption.map (·.1)` agree.  The two `ps'.pos ≤ p + n` frame
    clauses of `ParseNodeValueSpanLocal` are UNUSED here — a finding: only the COLLECTION branches of
    the P2b crux will consume the frame. -/
theorem parseNodeValueSpanLocal_scalar_branch
    (t1 t2 : Array (Positioned YamlToken)) (p1 p2 f n : Nat)
    (anch : Array (String × YamlValue)) (content : String) (style : ScalarStyle)
    (hn : 0 < n)
    (h_head : t1[p1]?.map (·.val) = some (.scalar content style))
    (h_agree : ∀ k, k < n → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))) :
    (parseNode { tokens := t1, pos := p1, anchors := anch } f).toOption.map (·.1)
      = (parseNode { tokens := t2, pos := p2, anchors := anch } f).toOption.map (·.1) := by
  have hk0 := h_agree 0 hn
  rw [Nat.add_zero, Nat.add_zero] at hk0
  have h_head2 : t2[p2]?.map (·.val) = some (.scalar content style) := by rw [← hk0]; exact h_head
  have hpk1 : ({ tokens := t1, pos := p1, anchors := anch } : ParseState).peek?
      = some (.scalar content style) := by rw [peek_eq_getElem_map]; exact h_head
  have hpk2 : ({ tokens := t2, pos := p2, anchors := anch } : ParseState).peek?
      = some (.scalar content style) := by rw [peek_eq_getElem_map]; exact h_head2
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf; simp [parseNode, Except.toOption]
  · rw [parseNode_scalar_toOption_value _ f content style hpk1 hf,
        parseNode_scalar_toOption_value _ f content style hpk2 hf]

/-- REAL emission (`sc`/`flowSeq`/`p2_toks` reuse): `["x"]`-standalone tokens; scalar `"x"`
    (double-quoted) at pos 1, trailing streamEnd. -/
def plsc_std : Array (Positioned YamlToken) := p2_toks (sc "x")
/-- REAL emission: flow seq `[q, x]` tokens; scalar `"x"` at pos 4, trailing flowSequenceEnd. -/
def plsc_ctx : Array (Positioned YamlToken) := p2_toks (flowSeq #[sc "q", sc "x"])

/-- Rule 1 / Rule 5 (non-vacuous on REAL emission): the two positions share ONLY the head scalar (their
    trailing tokens differ — streamEnd vs flowSequenceEnd), yet the recovered values agree AND are a
    genuine `some` scalar (not both-`none`). -/
theorem plsc_birth_value_agrees :
    ( ((parseNode { tokens := plsc_std, pos := 1, anchors := #[] } 8).toOption.map (·.1)
        == (parseNode { tokens := plsc_ctx, pos := 4, anchors := #[] } 8).toOption.map (·.1))
      && (parseNode { tokens := plsc_std, pos := 1, anchors := #[] } 8).toOption.isSome ) = true := by
  native_decide

/-- Rule 2 (boundary `f = 0`): both fail (fuel exhausted); `.toOption` sends both to `none`, so they
    still agree — the failing edge on which the rejected `.map` form disagreed (`p2b_map_form_false`). -/
theorem plsc_boundary_f0 :
    ( ((parseNode { tokens := plsc_std, pos := 1, anchors := #[] } 0).toOption.map (·.1)
        == (parseNode { tokens := plsc_ctx, pos := 4, anchors := #[] } 0).toOption.map (·.1))
      && !(parseNode { tokens := plsc_std, pos := 1, anchors := #[] } 0).toOption.isSome ) = true := by
  native_decide

/-- Rule 2 (the LEAF FIRES): the abstract `parseNodeValueSpanLocal_scalar_branch`, driven through the
    concrete REAL-emission witness (`n = 1`, trailing differs) — hypotheses genuinely satisfied. -/
theorem plsc_leaf_fires :
    (parseNode { tokens := plsc_std, pos := 1, anchors := #[] } 8).toOption.map (·.1)
      = (parseNode { tokens := plsc_ctx, pos := 4, anchors := #[] } 8).toOption.map (·.1) := by
  apply parseNodeValueSpanLocal_scalar_branch plsc_std plsc_ctx 1 4 8 1 #[] "x" .doubleQuoted
  · decide
  · native_decide
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0; native_decide

/-! ### P2b→JOINT re-architecture — value AND relative-advance in ONE conclusion (inhabitation-debt)

The 6th pass found the flow parser is LOOKAHEAD-driven (loops exit on `peek? = closer`, no bracket
counter), and [[ref-front-b-nonallscalar-blocking]] estimates the flowBracketBalance-based **P2a frame**
(an absolute-reach upper bound produced separately, then consumed by P2b) at ~1500 lines — a parser↔balance
bridge that fights the parser's grain.  Before sinking that cost, discipline says validate a cheaper
ARCHITECTURE.  A lookahead parser keeps two runs at agreeing positions in lockstep, so the natural object
is not "where does each run stop (absolute)" but "do the two runs ADVANCE equally (relative)."  That makes
the advance a CONCLUSION of the SAME induction that proves value-agreement — the [[ref-consumer-joint-before-producer]]
/ [[ref-joint-co-construction]] shape — rather than an imported frame.

**Birth-probed TRUE on REAL collection emission** (`jvadv_*` below): for the nested element `["a"]` inside
`[["a"],["b"]]`, the ABSOLUTE output `pos` differs (5 full vs 4 standalone) yet the RELATIVE advance AGREES
(both 3) — exactly why the joint projects `·.2.pos - p`, not `·.2.pos`.  The payoff: P1 can thread the
per-element advance PRODUCED here (transferred to the directly-computable STANDALONE advance) instead of a
separately-produced absolute-reach P2a.  Whether the eventual COLLECTION branch still needs per-element
`flowBracketBalance` framing, or threads `.val`-agreement directly, is the open question the next pass
decides — NOT claimed here.  This pass captures the joint conclusion + lands its scalar leaf `sorry`-free. -/

/-- NEW helper (advance companion of `parseNode_scalar_toOption_value`): a scalar-head parse advances by
    EXACTLY one, under `.toOption.map` — relative advance `r.2.pos - ps.pos = 1`.  From
    `parseNode_scalar_advances_by_one` (the production `n = 1` leaf) via `parseNode_scalar_head_isOk`. -/
theorem parseNode_scalar_toOption_advance (ps : ParseState) (f : Nat)
    (content : String) (style : ScalarStyle)
    (h_peek : ps.peek? = some (.scalar content style)) (hf : 0 < f) :
    (parseNode ps f).toOption.map (fun r => r.2.pos - ps.pos) = some 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  obtain ⟨⟨v, ps'⟩, hok⟩ := parseNode_scalar_head_isOk ps n content style h_peek
  have hadv : ps'.pos = ps.pos + 1 :=
    parseNode_scalar_advances_by_one ps (n + 1) content style v ps' h_peek hok
  rw [hok]; simp only [Except.toOption, Option.map_some]; rw [hadv]; congr 1; omega

/-- **The JOINT target** — `ParseNodeValueSpanLocal` strengthened with a second conclusion: under the SAME
    hypotheses (bounded `.val`-agreement + the two frame side-conditions), not only does the recovered
    VALUE agree, but the RELATIVE ADVANCE (`·.2.pos - p`) agrees too.  The advance agreement is genuinely
    new content — the frames give only UPPER bounds (`≤ p + n`), not equality and not cross-run agreement.
    Producing the advance here (rather than importing an absolute-reach P2a) is the re-architecture; it is
    what P1 threads as the cumulative `pos_i`.  Typechecked target, birth-probed at the SUCCESS boundary on
    a real collection (`jvadv_*`) and the FAILING boundary (`f = 0`); NOT proved as a whole, NO `sorry`. -/
def ParseNodeValueAdvanceLocal : Prop :=
  ∀ (t1 t2 : Array (Positioned YamlToken)) (p1 p2 f n : Nat)
    (anch : Array (String × YamlValue)),
    (∀ k, k < n → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))) →
    (∀ v ps', parseNode { tokens := t1, pos := p1, anchors := anch } f = .ok (v, ps') →
      ps'.pos ≤ p1 + n) →
    (∀ v ps', parseNode { tokens := t2, pos := p2, anchors := anch } f = .ok (v, ps') →
      ps'.pos ≤ p2 + n) →
    ((parseNode { tokens := t1, pos := p1, anchors := anch } f).toOption.map (·.1)
      = (parseNode { tokens := t2, pos := p2, anchors := anch } f).toOption.map (·.1))
    ∧ ((parseNode { tokens := t1, pos := p1, anchors := anch } f).toOption.map (fun r => r.2.pos - p1)
      = (parseNode { tokens := t2, pos := p2, anchors := anch } f).toOption.map (fun r => r.2.pos - p2))

/-- **The JOINT SCALAR LEAF** — the scalar-head branch of `ParseNodeValueAdvanceLocal`, `sorry`-free.
    Combines the value leaf (`parseNode_scalar_toOption_value`) with the advance leaf
    (`parseNode_scalar_toOption_advance`, advance `= 1` both sides): from agreement at `k = 0` (`0 < n`)
    both positions peek the same scalar, so both value and relative-advance agree.  As with the value-only
    branch, the two frame side-conditions are UNUSED — a scalar head is trailing-independent, so only the
    COLLECTION branches will consume framing.  This is the template the collection step follows: prove
    value + advance TOGETHER, keeping the two runs in lockstep. -/
theorem parseNodeValueAdvanceLocal_scalar_branch
    (t1 t2 : Array (Positioned YamlToken)) (p1 p2 f n : Nat)
    (anch : Array (String × YamlValue)) (content : String) (style : ScalarStyle)
    (hn : 0 < n)
    (h_head : t1[p1]?.map (·.val) = some (.scalar content style))
    (h_agree : ∀ k, k < n → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))) :
    ((parseNode { tokens := t1, pos := p1, anchors := anch } f).toOption.map (·.1)
      = (parseNode { tokens := t2, pos := p2, anchors := anch } f).toOption.map (·.1))
    ∧ ((parseNode { tokens := t1, pos := p1, anchors := anch } f).toOption.map (fun r => r.2.pos - p1)
      = (parseNode { tokens := t2, pos := p2, anchors := anch } f).toOption.map (fun r => r.2.pos - p2)) := by
  have hk0 := h_agree 0 hn
  rw [Nat.add_zero, Nat.add_zero] at hk0
  have h_head2 : t2[p2]?.map (·.val) = some (.scalar content style) := by rw [← hk0]; exact h_head
  have hpk1 : ({ tokens := t1, pos := p1, anchors := anch } : ParseState).peek?
      = some (.scalar content style) := by rw [peek_eq_getElem_map]; exact h_head
  have hpk2 : ({ tokens := t2, pos := p2, anchors := anch } : ParseState).peek?
      = some (.scalar content style) := by rw [peek_eq_getElem_map]; exact h_head2
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos f with hf | hf
    · subst hf; simp [parseNode, Except.toOption]
    · rw [parseNode_scalar_toOption_value _ f content style hpk1 hf,
          parseNode_scalar_toOption_value _ f content style hpk2 hf]
  · rcases Nat.eq_zero_or_pos f with hf | hf
    · subst hf; simp [parseNode, Except.toOption]
    · rw [parseNode_scalar_toOption_advance _ f content style hpk1 hf,
          parseNode_scalar_toOption_advance _ f content style hpk2 hf]

/-- **Joint birth (REAL collection, the crux of the re-architecture).**  For the nested element `["a"]`
    (`p2_full` item 0 at pos 2 vs standalone `p2_std0` at pos 1): the ABSOLUTE output `pos` DIFFERS (5 vs
    4), yet the RELATIVE advance AGREES (both 3) and the value agrees, and both are `some` — non-vacuous.
    This is the collection case the scalar leaf does NOT cover; it validates that projecting `·.2.pos - p`
    (relative), not `·.2.pos` (absolute), is what makes the joint conclusion TRUE across the two streams. -/
theorem jvadv_collection_relative_advance_agrees :
    ( !((parseNode p2_psF 100).toOption.map (·.2.pos) == (parseNode p2_psS 100).toOption.map (·.2.pos))
      && ((parseNode p2_psF 100).toOption.map (fun r => r.2.pos - 2)
            == (parseNode p2_psS 100).toOption.map (fun r => r.2.pos - 1))
      && ((parseNode p2_psF 100).toOption.map (·.1) == (parseNode p2_psS 100).toOption.map (·.1))
      && (parseNode p2_psF 100).toOption.isSome ) = true := by native_decide

/-- **Joint boundary (`f = 0`).**  Both parses fail; `.toOption` sends the ADVANCE projection of both to
    `none`, so the advance conclusion holds vacuously — the same failing edge the value conclusion survives. -/
theorem jvadv_boundary_f0 :
    ( ((parseNode { tokens := plsc_std, pos := 1, anchors := #[] } 0).toOption.map (fun r => r.2.pos - 1)
        == (parseNode { tokens := plsc_ctx, pos := 4, anchors := #[] } 0).toOption.map (fun r => r.2.pos - 4))
      && (parseNode { tokens := plsc_std, pos := 1, anchors := #[] } 0).toOption.isNone ) = true := by
  native_decide

/-- **Joint scalar leaf FIRES** — the abstract `parseNodeValueAdvanceLocal_scalar_branch` driven through the
    REAL-emission witness (`n = 1`, trailing differs): BOTH the value and the relative-advance conclusions
    discharge, hypotheses genuinely satisfied (not vacuous). -/
theorem jvadv_scalar_leaf_fires :
    ((parseNode { tokens := plsc_std, pos := 1, anchors := #[] } 8).toOption.map (·.1)
      = (parseNode { tokens := plsc_ctx, pos := 4, anchors := #[] } 8).toOption.map (·.1))
    ∧ ((parseNode { tokens := plsc_std, pos := 1, anchors := #[] } 8).toOption.map (fun r => r.2.pos - 1)
      = (parseNode { tokens := plsc_ctx, pos := 4, anchors := #[] } 8).toOption.map (fun r => r.2.pos - 4)) := by
  apply parseNodeValueAdvanceLocal_scalar_branch plsc_std plsc_ctx 1 4 8 1 #[] "x" .doubleQuoted
  · decide
  · native_decide
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0; native_decide

/-! ### JOINT COLLECTION branch, step 1 — the loop-joint TARGET, the balance-FREE shift brick, and the
     two loop BASE branches (`sorry`-free)

The joint scalar leaf above closes a NODE whose head is a scalar.  A NODE whose head is a flow collection
(`.sequence`/`.mapping`) reduces — after `parseNode` peels the head bracket and one unit of fuel — to a
LOOP over the body: `parseFlowSequenceLoop` (TokenParser.lean:400) / `parseFlowMappingLoop` (:495).  So the
collection branch of `ParseNodeValueAdvanceLocal` reduces to a JOINT LOOP fact: two loop runs at agreeing
positions, sharing an accumulator, produce EQUAL items AND advance EQUALLY (relative).  This pass captures
that loop-joint target, lands its BALANCE-FREE mechanism and its two BASE branches `sorry`-free, and probes
it on REAL emission — WITHOUT attempting the recursive step (a genuine mutual induction over the parser
clique, next pass).  Discipline: probe/validate the target before the induction; no `sorry` on source.

**The re-architecture's central bet, made concrete here.** The 6th-pass finding was that the loop is
LOOKAHEAD-driven (exits on `peek? = flowSequenceEnd`, no bracket counter).  The recursive loop step, given
the joint IH on the element (value + EQUAL advance `w`), must re-establish the bounded `.val`-agreement at
the SHIFTED positions `p1+w`, `p2+w` to fire the IH on the loop tail.  `agree_shift` below shows that
re-establishment is PURE index arithmetic driven by the equal advance `w` — NO `flowBracketBalance`.  That
is the mechanism that would retire P2a's ~1500-line balance bridge.  (Still not a proof that it does — the
recursive step, where `w` must also be shown to keep the element WITHIN the span, is next pass.  `agree_shift`
is `[propext, Quot.sound]` — `Classical`-free — underscoring it is plain arithmetic, not parser reasoning.) -/

/-- **The balance-FREE agreement-shift brick.**  If bounded `.val`-agreement holds over `[p, p+n)` and both
    runs advance by the SAME `w`, agreement holds over the residual span at the shifted starts `p1+w`,
    `p2+w`.  Pure index arithmetic (`[propext, Quot.sound]`, no `flowBracketBalance`, no `Classical`).  This
    is what the recursive loop step will use to re-arm the IH's agreement hypothesis from the joint's ADVANCE
    conclusion `w` — the replacement for P2a's imported balance frame. -/
theorem agree_shift (t1 t2 : Array (Positioned YamlToken)) (p1 p2 n w : Nat)
    (h_agree : ∀ k, k < n → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))) :
    ∀ k, k < n - w → (t1[(p1 + w) + k]?.map (·.val)) = (t2[(p2 + w) + k]?.map (·.val)) := by
  intro k hk
  have hkw : w + k < n := by omega
  have h := h_agree (w + k) hkw
  rw [show p1 + w + k = p1 + (w + k) by omega, show p2 + w + k = p2 + (w + k) by omega]
  exact h

/-- **The loop-joint TARGET** — the object the flow-COLLECTION branch of `ParseNodeValueAdvanceLocal`
    reduces to.  Two `parseFlowSequenceLoop` runs at agreeing positions, sharing the accumulator `items`,
    under bounded `.val`-agreement + the two frame side-conditions: the recovered items AGREE and the
    RELATIVE advance AGREES.  Same shape as the node joint, keyed on the loop instead of `parseNode`.
    Typechecked target, birth-probed on a real collection (`loop_joint_birth`) and the empty-collection
    boundary (`loop_close_fires`); NOT proved as a whole, NO `sorry`. -/
def ParseFlowSequenceLoopValueAdvanceLocal : Prop :=
  ∀ (t1 t2 : Array (Positioned YamlToken)) (p1 p2 f n : Nat)
    (anch : Array (String × YamlValue)) (items : Array YamlValue),
    (∀ k, k < n → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))) →
    (∀ its ps', parseFlowSequenceLoop { tokens := t1, pos := p1, anchors := anch } f items = .ok (its, ps') →
      ps'.pos ≤ p1 + n) →
    (∀ its ps', parseFlowSequenceLoop { tokens := t2, pos := p2, anchors := anch } f items = .ok (its, ps') →
      ps'.pos ≤ p2 + n) →
    ((parseFlowSequenceLoop { tokens := t1, pos := p1, anchors := anch } f items).toOption.map (·.1)
      = (parseFlowSequenceLoop { tokens := t2, pos := p2, anchors := anch } f items).toOption.map (·.1))
    ∧ ((parseFlowSequenceLoop { tokens := t1, pos := p1, anchors := anch } f items).toOption.map (fun r => r.2.pos - p1)
      = (parseFlowSequenceLoop { tokens := t2, pos := p2, anchors := anch } f items).toOption.map (fun r => r.2.pos - p2))

/-- Reduction helper: at a `flowSequenceEnd` head the loop returns the accumulator unmoved. -/
theorem parseFlowSeqLoop_close_step (ps : ParseState) (g : Nat) (items : Array YamlValue)
    (h : ps.peek? = some .flowSequenceEnd) :
    parseFlowSequenceLoop ps (g + 1) items = .ok (items, ps) := by
  unfold parseFlowSequenceLoop
  simp only [h]

/-- **Loop base branch 1 — fuel 0.**  The loop returns `(items, ps)` unmoved on both sides, so value
    (`items`) and relative advance (`0`) agree trivially.  No hypotheses needed. -/
theorem parseFlowSeqLoop_joint_fuel0
    (t1 t2 : Array (Positioned YamlToken)) (p1 p2 : Nat)
    (anch : Array (String × YamlValue)) (items : Array YamlValue) :
    ((parseFlowSequenceLoop { tokens := t1, pos := p1, anchors := anch } 0 items).toOption.map (·.1)
      = (parseFlowSequenceLoop { tokens := t2, pos := p2, anchors := anch } 0 items).toOption.map (·.1))
    ∧ ((parseFlowSequenceLoop { tokens := t1, pos := p1, anchors := anch } 0 items).toOption.map (fun r => r.2.pos - p1)
      = (parseFlowSequenceLoop { tokens := t2, pos := p2, anchors := anch } 0 items).toOption.map (fun r => r.2.pos - p2)) := by
  refine ⟨?_, ?_⟩ <;> simp [parseFlowSequenceLoop, Except.toOption]

/-- **Loop base branch 2 — empty collection (head is the closer).**  From `.val`-agreement at `k = 0`
    (`0 < n`) both runs peek `flowSequenceEnd` and return the accumulator unmoved; value + relative advance
    agree.  The two frame side-conditions are UNUSED — the empty-collection base, like the scalar leaf, sheds
    the frame; only the RECURSIVE step will consume it. -/
theorem parseFlowSeqLoop_joint_close
    (t1 t2 : Array (Positioned YamlToken)) (p1 p2 f n : Nat)
    (anch : Array (String × YamlValue)) (items : Array YamlValue)
    (hn : 0 < n)
    (h_head : t1[p1]?.map (·.val) = some .flowSequenceEnd)
    (h_agree : ∀ k, k < n → (t1[p1 + k]?.map (·.val)) = (t2[p2 + k]?.map (·.val))) :
    ((parseFlowSequenceLoop { tokens := t1, pos := p1, anchors := anch } f items).toOption.map (·.1)
      = (parseFlowSequenceLoop { tokens := t2, pos := p2, anchors := anch } f items).toOption.map (·.1))
    ∧ ((parseFlowSequenceLoop { tokens := t1, pos := p1, anchors := anch } f items).toOption.map (fun r => r.2.pos - p1)
      = (parseFlowSequenceLoop { tokens := t2, pos := p2, anchors := anch } f items).toOption.map (fun r => r.2.pos - p2)) := by
  have hk0 := h_agree 0 hn
  rw [Nat.add_zero, Nat.add_zero] at hk0
  have h_head2 : t2[p2]?.map (·.val) = some .flowSequenceEnd := by rw [← hk0]; exact h_head
  have hpk1 : ({ tokens := t1, pos := p1, anchors := anch } : ParseState).peek? = some .flowSequenceEnd := by
    rw [peek_eq_getElem_map]; exact h_head
  have hpk2 : ({ tokens := t2, pos := p2, anchors := anch } : ParseState).peek? = some .flowSequenceEnd := by
    rw [peek_eq_getElem_map]; exact h_head2
  rcases Nat.eq_zero_or_pos f with hf | hf
  · subst hf; exact parseFlowSeqLoop_joint_fuel0 t1 t2 p1 p2 anch items
  · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [parseFlowSeqLoop_close_step _ g items hpk1, parseFlowSeqLoop_close_step _ g items hpk2]
    refine ⟨?_, ?_⟩ <;> simp [Except.toOption]

/-- REAL-emission loop witnesses (reuse `p2_toks`/`p2_full`/`p2_std0`). -/
def lj_loopFull (p : Nat) : Except ScanError (Array YamlValue × ParseState) :=
  parseFlowSequenceLoop { tokens := p2_toks p2_full, pos := p, anchors := #[] } 100 #[]
def lj_loopStd (p : Nat) : Except ScanError (Array YamlValue × ParseState) :=
  parseFlowSequenceLoop { tokens := p2_toks p2_std0, pos := p, anchors := #[] } 100 #[]
def lj_empty : Array (Positioned YamlToken) := p2_toks (flowSeq #[])
def lj_nested : Array (Positioned YamlToken) := p2_toks (flowSeq #[ flowSeq #[], flowSeq #[sc "z"] ])

/-- **Loop-joint birth (REAL collection, the crux).**  The inner `["a"]` loop in `[["a"],["b"]]` (`full`
    from pos 3) vs the standalone `["a"]` loop (`std0` from pos 2): ABSOLUTE output `pos` DIFFERS (4 vs 3),
    yet the RELATIVE advance AGREES (both 1) and the items AGREE, both `some` — non-vacuous.  Exactly why
    the loop joint projects `·.2.pos - p` (relative), not `·.2.pos` (absolute). -/
theorem loop_joint_birth :
    ( !((lj_loopFull 3).toOption.map (·.2.pos) == (lj_loopStd 2).toOption.map (·.2.pos))
      && ((lj_loopFull 3).toOption.map (fun r => r.2.pos - 3) == (lj_loopStd 2).toOption.map (fun r => r.2.pos - 2))
      && ((lj_loopFull 3).toOption.map (·.1) == (lj_loopStd 2).toOption.map (·.1))
      && (lj_loopFull 3).toOption.isSome ) = true := by native_decide

/-- **Balance-free recursive-step evidence.**  After the scalar element `"a"` advances by 1 on BOTH runs,
    the residual `.val`-agreement still holds at the shifted positions (`full[4] = ] = std0[3]`), and the
    shifted head IS the closer — so the loop reaches its exit by AGREEMENT alone, with no `flowBracketBalance`
    term.  This is the concrete witness for what `agree_shift` does structurally. -/
theorem loop_step_shift_balance_free :
    ( ((p2_toks p2_full)[3]!.val == (p2_toks p2_std0)[2]!.val)
      && ((p2_toks p2_full)[4]!.val == (p2_toks p2_std0)[3]!.val)
      && ((p2_toks p2_full)[4]!.val == YamlToken.flowSequenceEnd) ) = true := by native_decide

/-- **Close branch FIRES on REAL emission.**  The inner `[]` loop inside `[[], ["z"]]` (`lj_nested` from
    pos 3) vs the standalone `[]` loop (`lj_empty` from pos 2) — two DIFFERENT streams sharing ONLY the
    `flowSequenceEnd` head; the abstract `parseFlowSeqLoop_joint_close` discharges (empty items, advance 0
    both sides), hypotheses genuinely satisfied. -/
theorem loop_close_fires :
    ((parseFlowSequenceLoop { tokens := lj_nested, pos := 3, anchors := #[] } 100 #[]).toOption.map (·.1)
      = (parseFlowSequenceLoop { tokens := lj_empty, pos := 2, anchors := #[] } 100 #[]).toOption.map (·.1))
    ∧ ((parseFlowSequenceLoop { tokens := lj_nested, pos := 3, anchors := #[] } 100 #[]).toOption.map (fun r => r.2.pos - 3)
      = (parseFlowSequenceLoop { tokens := lj_empty, pos := 2, anchors := #[] } 100 #[]).toOption.map (fun r => r.2.pos - 2)) := by
  apply parseFlowSeqLoop_joint_close lj_nested lj_empty 3 2 100 1 #[] #[] (by omega)
  · native_decide
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0; native_decide

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
    and `frameSpan_unique` shows the guarded conditions pin `n` uniquely.  The two combinatorial bricks the
    frame induction will consume — `frameHead_classified` (head dispatcher) and `frame_matching_close_at_end`
    (span-end locator) — are proved `sorry`-free below.  Typechecked target, validated at the boundary by
    `p2a_*` below; the parseNode side is NOT proved, NO `sorry`. -/
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

/-! ### P2a combinatorial bricks — the head DISPATCHER and the span-END locator (both `sorry`-free)

`frameSpan_unique` above shows the guarded frame names a UNIQUE `n`.  The two bricks below are the
other pure-`flowBracketBalance` facts the eventual parseNode frame induction will consume — landed this
pass while going to prove P2a, again WITHOUT scaffolding a `sorry` on the (only just corrected) target:

* `frameHead_classified` — the BRANCH DISPATCHER.  Under the guarded frame the head token's bracket
  delta is fixed by `n`: `0` when `n = 1` (a scalar leaf — parseNode's scalar branch, advancing by 1)
  and `1` when `n ≥ 2` (a flow-collection opener).  This is precisely the missing
  `flowBracketDelta tokens[p]!.val = 1` premise that `flowBracketBalance_matching_close` requires — the
  gap the `n = 0` hole exposed (an unguarded `n = 0` has NO classified head, so the matching-close
  locator could never fire).  Proof: `flowBracketBalance t p (p+1) = flowBracketDelta t[p]!.val` (one
  `frameBal_step`); `n = 1` forces it `= 0` via `h_zero`, `n ≥ 2` forces it `≥ 1` via the interior floor,
  and `flowBracketDelta_le_one` caps it at `1`.
* `frame_matching_close_at_end` — the span-END locator.  For a flow collection (`n ≥ 2`) the matching
  close is the span's LAST token: `tokens[p+n-1]` is a closer and the body `[p+1, p+n-1)` is itself
  balanced.  This is the shape that lets the frame conclude parseNode — which reads to its matching
  close — advances to exactly `p + n`.  Proof: `flowBracketBalance_matching_close` at the opener
  (`frameHead_classified` supplies the opener premise) yields a close `j`; the strict interior floor
  `h_int` at `j+1` forces `j = p + n - 1` (else `balance p (j+1) = 0` contradicts `≥ 1`).

Together with `frameSpan_unique` these reduce the OUTSTANDING P2a work to the parseNode side alone:
the fuel-indexed mutual induction over the flow parser clique (the upper-bound companion to the
existing lower-bound `ParseNodePosMono`, `ParserWellBehaved.lean`), whose scalar LEAF is
`parseNode_scalar_advances_by_one` (`n = 1`) and whose collection step reads to
`frame_matching_close_at_end`'s closer.  No production file is touched and no `sorry` is introduced. -/

/-- One-step balance recurrence (mirrors the local `step` inside `flowBracketBalance_matching_close`):
    advancing the upper endpoint by one token adds that token's `flowBracketDelta`. -/
theorem frameBal_step (t : Array (Positioned YamlToken)) (lo i : Nat)
    (h_lo_i : lo ≤ i) (h_sz : i < t.size) :
    flowBracketBalance t lo (i + 1)
      = flowBracketBalance t lo i + flowBracketDelta t[i]!.val := by
  rw [flowBracketBalance_compose t lo i (i + 1) h_lo_i (by omega)]
  have hlen : i < t.toList.length := by rw [Array.length_toList]; exact h_sz
  rw [flowBracketBalance_single t i hlen]
  have h1 : t.toList[i]'hlen = t[i] := Array.getElem_toList h_sz
  have h2 : t[i] = t[i]! := (getElem!_pos t i h_sz).symm
  rw [h1, h2]

/-- The empty range has balance `0`. -/
theorem frameBal_empty (t : Array (Positioned YamlToken)) (p : Nat) :
    flowBracketBalance t p p = 0 := by simp [flowBracketBalance]

/-- **Frame head classification (pure Dyck combinatorics).**  Under the P2a frame conditions the head
    token's bracket delta is fixed by `n`: neutral (`0`) when `n = 1` (a scalar leaf), opener (`1`) when
    `n ≥ 2` (a flow collection).  This is exactly the branch dispatcher the parseNode frame induction
    needs, and it supplies the `flowBracketDelta = 1` premise that `flowBracketBalance_matching_close`
    requires — the fact the `n = 0` hole showed was missing (an unguarded `n = 0` has no classified head).
    `sorry`-free; the `0 < n` guard is what makes the classification total. -/
theorem frameHead_classified (t : Array (Positioned YamlToken)) (p n : Nat)
    (h_sz : p < t.size) (h_pos : 0 < n)
    (h_zero : flowBracketBalance t p (p + n) = 0)
    (h_int : ∀ i, p < i → i < p + n → flowBracketBalance t p i ≥ 1) :
    flowBracketDelta t[p]!.val = if n = 1 then 0 else 1 := by
  have hstep : flowBracketBalance t p (p + 1) = flowBracketDelta t[p]!.val := by
    have hb := frameBal_step t p p (Nat.le_refl _) h_sz
    rw [frameBal_empty] at hb; simpa using hb
  by_cases hn1 : n = 1
  · subst hn1
    have hd : flowBracketDelta t[p]!.val = 0 := by rw [← hstep]; exact h_zero
    simp [hd]
  · have hge : flowBracketBalance t p (p + 1) ≥ 1 := h_int (p + 1) (by omega) (by omega)
    have hle : flowBracketDelta t[p]!.val ≤ 1 := flowBracketDelta_le_one _
    rw [hstep] at hge
    rw [if_neg hn1]; omega

/-- **Frame matching-close at the span end (`n ≥ 2`).**  For a flow-collection frame the matching close
    is the LAST token of the span: `t[p+n-1]` is a closer and the enclosed body `[p+1, p+n-1)` is itself
    balanced.  This is what lets the frame conclude parseNode — which reads forward to its matching close —
    advances to exactly `p + n`.  Proved by applying `flowBracketBalance_matching_close` at the opener
    (`frameHead_classified` supplies the opener premise) and pinning `j = p + n - 1` via the strict
    interior floor `h_int`.  `sorry`-free. -/
theorem frame_matching_close_at_end (t : Array (Positioned YamlToken)) (p n : Nat)
    (h_sz : p + n ≤ t.size) (h_n2 : 2 ≤ n)
    (h_zero : flowBracketBalance t p (p + n) = 0)
    (h_int : ∀ i, p < i → i < p + n → flowBracketBalance t p i ≥ 1) :
    flowBracketDelta t[p + n - 1]!.val = -1 ∧
    flowBracketBalance t (p + 1) (p + n - 1) = 0 := by
  have h_p_sz : p < t.size := by omega
  have h_open : flowBracketDelta t[p]!.val = 1 := by
    have hc := frameHead_classified t p n h_p_sz (by omega) h_zero h_int
    rw [if_neg (by omega : ¬ n = 1)] at hc; exact hc
  have h_dyck : ∀ i, p ≤ i → i ≤ p + n → flowBracketBalance t p i ≥ 0 := by
    intro i h_lo h_hi
    rcases Nat.lt_or_ge p i with hpi | hpi
    · rcases Nat.lt_or_ge i (p + n) with hin | hin
      · have := h_int i hpi hin; omega
      · have he : i = p + n := by omega
        subst he; omega
    · have he : i = p := by omega
      rw [he]; have := frameBal_empty t p; omega
  obtain ⟨j, hkj, hjhi, hjclose, hjbody, _hjfloor⟩ :=
    flowBracketBalance_matching_close t p p (p + n) (Nat.le_refl _) (by omega) h_sz
      (frameBal_empty t p) h_open h_zero h_dyck
  have h_p1 : flowBracketBalance t p (p + 1) = 1 := by
    have hb := frameBal_step t p p (Nat.le_refl _) h_p_sz
    rw [frameBal_empty, h_open] at hb; simpa using hb
  have h_pj : flowBracketBalance t p j = 1 := by
    have hc := flowBracketBalance_compose t p (p + 1) j (by omega) (by omega)
    rw [h_p1, hjbody] at hc; omega
  have h_j_sz : j < t.size := by omega
  have h_pj1 : flowBracketBalance t p (j + 1) = 0 := by
    have hb := frameBal_step t p j (by omega) h_j_sz
    rw [h_pj, hjclose] at hb; omega
  have h_not : ¬ (j + 1 < p + n) := by
    intro hlt
    have hfloor := h_int (j + 1) (by omega) hlt
    rw [h_pj1] at hfloor; omega
  have h_j_eq : j = p + n - 1 := by omega
  subst h_j_eq
  exact ⟨hjclose, hjbody⟩

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
  (`p2a_*`).  The two pure-`flowBracketBalance` bricks the induction consumes are now landed sorry-free:
  `frameHead_classified` (head is neutral iff `n = 1`, opener iff `n ≥ 2` — the branch dispatcher and the
  missing `flowBracketBalance_matching_close` premise) and `frame_matching_close_at_end` (the close is the
  span's last token, body balanced).  *Missing: only the parseNode-side fuel-indexed mutual induction (the
  upper-bound companion to `ParseNodePosMono`); correction + uniqueness + both combinatorial bricks landed.*
* **P2b — value span-locality** = `ParseNodeValueSpanLocal` above: value invariant under BOUNDED
  `.val`-agreement + the two frame side-conditions.  Mutual induction over the parser clique
  (parseNode / parseNodeContent / parseFlowSequenceLoop / parseFlowMappingLoop / …), projecting the
  value and jointly tracking consumed length.  This is the crux.  **Its SCALAR branch is now landed
  `sorry`-free** (`parseNodeValueSpanLocal_scalar_branch`, above): the scalar head is
  trailing-independent (`parseNode_scalar_produces_scalar`), so it closes from agreement at `k = 0`
  alone — needing NEITHER frame side-condition NOR `k ≥ 1` agreement (a finding: the frame is consumed
  only by the COLLECTION branches).  **RE-ARCHITECTED this pass to the JOINT `ParseNodeValueAdvanceLocal`**
  (above): value AND relative-advance (`·.2.pos - p`) in ONE conclusion.  A lookahead parser keeps two
  agreeing runs in lockstep, so the advance is a CONCLUSION of the same induction, not an imported P2a
  frame — the [[ref-consumer-joint-before-producer]] shape.  Birth-probed TRUE on a real collection
  (`jvadv_collection_relative_advance_agrees`: absolute `pos` differs 5≠4, relative advance agrees 3=3);
  the joint scalar leaf `parseNodeValueAdvanceLocal_scalar_branch` is landed `sorry`-free.  *Missing: the
  flow-COLLECTION branches (`.sequence`/`.mapping` heads), where the loop induction threads the joint —
  and where it is DECIDED whether per-element framing still needs `flowBracketBalance` (P2a) or the
  lockstep advance threads `.val`-agreement directly, potentially retiring the ~1500-line balance bridge.*
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

**Build order (cheapest first).**  The Bridge is birth-probed and leans on R596/R597.  The crux is now
the JOINT `ParseNodeValueAdvanceLocal` collection branch (value + advance in lockstep, scalar leaf landed);
its collection step decides whether P2a's separate `flowBracketBalance` frame is still needed or is retired
by threading the joint advance directly.  P1 threads the joint at the loop and computes the cumulative
`pos_i` from the per-element advance the joint PRODUCES.  Each is a self-contained unit (the all-scalar
R596/R597/R601/R602 were each their own).

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

/-! The two P2a combinatorial bricks are `sorry`-free.  Both inherit `Classical.choice` from
    `flowBracketBalance_matching_close`/`flowBracketBalance_compose` (`frameSpan_unique` avoided it
    because it is pure `omega`), so the profile is the standard `[propext, Classical.choice, Quot.sound]`
    — no `sorryAx`. -/
/-- info: 'NonAllScalarLocality.frameHead_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frameHead_classified

/-- info: 'NonAllScalarLocality.frame_matching_close_at_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frame_matching_close_at_end

/-! The P2b projection refutation and its corrected-form survival probe are `sorry`-free (the
    `native_decide` axioms are the standard reflected-`decide` ones, as for every probe in this file). -/
/-- info: 'NonAllScalarLocality.p2b_map_form_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 p2b_map_form_false._native.native_decide.ax_1_2,
 p2b_map_form_false._native.native_decide.ax_1_6,
 p2b_map_form_false._native.native_decide.ax_1_7,
 p2b_map_form_false._native.native_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms p2b_map_form_false

/-- info: 'NonAllScalarLocality.p2b_toOption_form_survives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 p2b_toOption_form_survives._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms p2b_toOption_form_survives

/-! The P2b scalar-leaf facts are `sorry`-free.  `peek_eq_getElem_map` is pure `[propext]` (it is just
    `getElem!`↔`getElem?` plumbing); the three parser-side facts and the branch inherit the standard
    `[propext, Classical.choice, Quot.sound]`; the probes add only the per-declaration reflected-`decide`
    axioms. -/
/-- info: 'NonAllScalarLocality.parseNode_scalar_head_isOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseNode_scalar_head_isOk

/-- info: 'NonAllScalarLocality.parseNode_scalar_toOption_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseNode_scalar_toOption_value

/-- info: 'NonAllScalarLocality.peek_eq_getElem_map' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms peek_eq_getElem_map

/-- info: 'NonAllScalarLocality.parseNodeValueSpanLocal_scalar_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseNodeValueSpanLocal_scalar_branch

/-- info: 'NonAllScalarLocality.plsc_birth_value_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 plsc_birth_value_agrees._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms plsc_birth_value_agrees

/-- info: 'NonAllScalarLocality.plsc_boundary_f0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 plsc_boundary_f0._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms plsc_boundary_f0

/-- info: 'NonAllScalarLocality.plsc_leaf_fires' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 plsc_leaf_fires._native.native_decide.ax_1_1,
 plsc_leaf_fires._native.native_decide.ax_1_3] -/
#guard_msgs (whitespace := lax) in
#print axioms plsc_leaf_fires

/-! The JOINT (value+advance) re-architecture facts are `sorry`-free.  The new advance helper and the
    joint scalar branch inherit the standard `[propext, Classical.choice, Quot.sound]`; the probes add only
    per-declaration reflected-`decide` axioms. -/
/-- info: 'NonAllScalarLocality.parseNode_scalar_toOption_advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseNode_scalar_toOption_advance

/-- info: 'NonAllScalarLocality.parseNodeValueAdvanceLocal_scalar_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseNodeValueAdvanceLocal_scalar_branch

/-- info: 'NonAllScalarLocality.jvadv_collection_relative_advance_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 jvadv_collection_relative_advance_agrees._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms jvadv_collection_relative_advance_agrees

/-- info: 'NonAllScalarLocality.jvadv_boundary_f0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 jvadv_boundary_f0._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms jvadv_boundary_f0

/-- info: 'NonAllScalarLocality.jvadv_scalar_leaf_fires' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 jvadv_scalar_leaf_fires._native.native_decide.ax_1_1,
 jvadv_scalar_leaf_fires._native.native_decide.ax_1_3] -/
#guard_msgs (whitespace := lax) in
#print axioms jvadv_scalar_leaf_fires

/-! The JOINT COLLECTION step-1 facts are `sorry`-free.  `agree_shift` is `[propext, Quot.sound]` —
    `Classical`-free, being pure index arithmetic; the loop reduction/base branches inherit the standard
    `[propext, Classical.choice, Quot.sound]`; the probes add only per-declaration reflected-`decide`. -/
/-- info: 'NonAllScalarLocality.agree_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms agree_shift

/-- info: 'NonAllScalarLocality.parseFlowSeqLoop_close_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowSeqLoop_close_step

/-- info: 'NonAllScalarLocality.parseFlowSeqLoop_joint_fuel0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowSeqLoop_joint_fuel0

/-- info: 'NonAllScalarLocality.parseFlowSeqLoop_joint_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowSeqLoop_joint_close

/-- info: 'NonAllScalarLocality.loop_joint_birth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 loop_joint_birth._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms loop_joint_birth

/-- info: 'NonAllScalarLocality.loop_step_shift_balance_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 loop_step_shift_balance_free._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms loop_step_shift_balance_free

/-- info: 'NonAllScalarLocality.loop_close_fires' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 loop_close_fires._native.native_decide.ax_1_2,
 loop_close_fires._native.native_decide.ax_1_4] -/
#guard_msgs (whitespace := lax) in
#print axioms loop_close_fires

end NonAllScalarLocality
