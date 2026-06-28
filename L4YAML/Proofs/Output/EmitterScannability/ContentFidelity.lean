/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Proofs.Output.EmitterScannability.ScanChainGrowth

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.RoundTrip
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.ParserWellBehaved
open L4YAML.Proofs.ScalarCoupling

-- resolveAliases is identity on scalars
theorem resolveAliases_scalar (s : Scalar)
    (anchors : Array (String × YamlValue)) :
    (YamlValue.scalar s).resolveAliases anchors = .scalar s := by
  unfold YamlValue.resolveAliases; rfl

-- stripAnchors on scalar just clears the anchor
theorem stripAnchors_scalar (s : Scalar) :
    (YamlValue.scalar s).stripAnchors = .scalar { s with anchor := none } := by
  unfold YamlValue.stripAnchors; rfl

-- contentEq for scalars only depends on content string
theorem contentEq_scalar_content (s₁ s₂ : Scalar)
    (h : s₁.content = s₂.content) : contentEq (.scalar s₁) (.scalar s₂) = true := by
  unfold contentEq; simp [h]

/-! ### §5.2  Scanner content preservation

The scanner's double-quoted collector recovers the original content string
from the emitter's escape-encoded output. This is the key roundtrip property.
-/

-- Hex foldl roundtrip for control characters (c.val.toNat < 0x20)
/-- **Scanner content preservation**: scanning `emitScalar content` produces
    a token stream where the scalar token's content equals the original.

    This bridges the emitter's `escapeString` encoding with the scanner's
    `collectDoubleQuotedLoop` + `processEscape` decoding. The proof follows
    from `collectDoubleQuotedLoop_escapeString_succeeds` strengthened with
    content equality (the loop accumulator reconstructs the original string). -/
theorem scanFiltered_emitScalar_content (content : String) (tokens : Array (Positioned YamlToken))
    (h_scan : scanFiltered (emitScalar content) = .ok tokens) :
    ∃ i, i < tokens.size ∧ tokens[i]!.val = .scalar content .doubleQuoted := by
  -- Get scanner state with token membership
  obtain ⟨s₁, h_snt1, h_peek1, h_flow1, h_dp1, ⟨tok, h_tok_mem, h_tok_val⟩, h_ids1, _⟩ :=
    scanNextToken_emitScalar_init content
  have h_snt2 : scanNextToken s₁ = .ok none := scanNextToken_eof s₁ h_peek1
  -- Compute the raw scan result
  have h_size := emitScalar_utf8ByteSize_ge content
  have h_fuel : ((emitScalar content).utf8ByteSize + 1) * 4 ≥ 2 := by omega
  -- scan reduces to scanLoop on the initial state
  have h_scan_eq : scan (emitScalar content)
      = scanLoop ((ScannerState.mk' (emitScalar content)).emit .streamStart)
          (((emitScalar content).utf8ByteSize + 1) * 4) := by
    have h_chars := chars_from_zero_toList (emitScalar content)
    rw [emitScalar_toList] at h_chars
    have h_corr := initial_corr (emitScalar content) _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons (ScannerState.mk' (emitScalar content)) '"'
      ((escapeString content).toList ++ ['"']) 0 h_corr
    have h_pk_emit : ((ScannerState.mk' (emitScalar content)).emit .streamStart).peek?
        = (ScannerState.mk' (emitScalar content)).peek? := rfl
    unfold scan; dsimp only []
    rw [h_pk_emit, h_pk]
    split <;> first | rfl | exact absurd ‹_› (by decide)
  -- Get concrete token array via scanLoop_two_iter_eq
  have h_loop_eq := scanLoop_two_iter_eq h_fuel h_snt1 h_snt2 h_flow1 h_dp1
  -- The raw scan result is ((unwindIndents s₁ (-1)).emit .streamEnd).tokens
  have h_scan_raw : scan (emitScalar content) =
      .ok ((unwindIndents s₁ (-1)).emit .streamEnd).tokens := by
    rw [h_scan_eq, h_loop_eq]
  -- Scalar token survives through unwindIndents (prefix preservation)
  have h_tok_in_uwi : tok ∈ (unwindIndents s₁ (-1)).tokens := by
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp h_tok_mem
    rw [Array.mem_iff_getElem]
    have h_sz := ScannerCorrectness.unwindIndents_adds_tokens s₁ (-1)
    have h_pref := ScannerCorrectness.unwindIndents_preserves_prefix s₁ (-1) i hi
    exact ⟨i, by omega, h_pref⟩
  -- Scalar token survives through .emit .streamEnd (push preserves membership)
  have h_tok_in_raw : tok ∈ ((unwindIndents s₁ (-1)).emit .streamEnd).tokens := by
    exact Array.mem_push_of_mem _ h_tok_in_uwi
  -- Scalar token survives through filter (scalar ≠ placeholder)
  have h_tok_filtered : tok ∈ ((unwindIndents s₁ (-1)).emit .streamEnd).tokens.filter
      (fun t => t.val != .placeholder) := by
    rw [Array.mem_filter]
    refine ⟨h_tok_in_raw, ?_⟩
    rw [h_tok_val]
    -- Different constructors: .scalar vs .placeholder → beq = false → bne = true
    rfl
  -- Link filtered result to `tokens` via h_scan
  have h_tokens_eq : tokens = ((unwindIndents s₁ (-1)).emit .streamEnd).tokens.filter
      (fun t => t.val != .placeholder) := by
    simp only [scanFiltered, h_scan_raw] at h_scan
    exact (Except.ok.inj h_scan).symm
  -- Extract index from membership
  rw [h_tokens_eq]
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp h_tok_filtered
  exact ⟨i, hi, by rw [getElem!_pos]; exact h_tok_val⟩

/-- When `parseDirectives` sees a non-directive token, it returns immediately
    with empty directives and unchanged state.
    The `for _ in [:fuel] do` loop breaks on the first iteration because
    `peek?` matches `| _ => break`. -/
theorem parseDirectives_skip (ps : ParseState)
    (h : match ps.peek? with
        | some (.versionDirective _ _) | some (.tagDirective _ _) => False
        | _ => True) :
    parseDirectives ps = (#[], ps) := by
  unfold parseDirectives
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize ps.tokens.size - ps.pos = fuel
  cases fuel with
  | zero =>
    simp only [List.range', List.forIn_nil]
    rfl
  | succ n =>
    simp only [List.range'_succ, List.forIn_cons, pure, bind]
    split
    · rename_i minor h_done
      split at h_done
      · cases h_done
      · cases h_done
      · cases h_done; rfl
    · rename_i b h_yield
      split at h_yield
      · exfalso; revert h; simp_all
      · exfalso; revert h; simp_all
      · cases h_yield

-- ═══ Helper infrastructure for flow collection parser acceptance ═══

-- Combined scanner-parser pipeline Bool checks for "[]" and "{}".
-- Using native_decide on Bool expressions avoids needing DecidableEq instances
-- for Except, Array, etc.
def checkFullSeq : Bool :=
  match Scanner.scanFiltered "[]" with
  | .ok tokens =>
    match parseStream tokens with
    | .ok docs => docs.size == 1
    | .error _ => false
  | .error _ => false

def checkFullMap : Bool :=
  match Scanner.scanFiltered "{}" with
  | .ok tokens =>
    match parseStream tokens with
    | .ok docs => docs.size == 1
    | .error _ => false
  | .error _ => false

theorem checkFullSeq_true : checkFullSeq = true := by native_decide
theorem checkFullMap_true : checkFullMap = true := by native_decide

-- Content fidelity Bool checks for empty flow collections.
-- Verifies: parseYamlRaw "[]"/{}" succeeds AND the composed result is content-equivalent
-- to the original empty collection.
def checkContentSeq : Bool :=
  match parseYamlRaw "[]" with
  | .ok raw_docs =>
    raw_docs.size == 1 &&
    contentEq (.sequence .flow #[]) (raw_docs.map YamlDocument.compose)[0]!.value
  | .error _ => false

def checkContentMap : Bool :=
  match parseYamlRaw "{}" with
  | .ok raw_docs =>
    raw_docs.size == 1 &&
    contentEq (.mapping .flow #[]) (raw_docs.map YamlDocument.compose)[0]!.value
  | .error _ => false

theorem checkContentSeq_true : checkContentSeq = true := by native_decide
theorem checkContentMap_true : checkContentMap = true := by native_decide

-- ==========================================
-- Helper Lemmas for Content Fidelity
-- ==========================================

-- contentEq on sequences ignores style/tag/anchor: only items matter.
theorem contentEq_sequence_items (style₁ style₂ : CollectionStyle)
    (items₁ items₂ : Array YamlValue)
    (tag₁ tag₂ anchor₁ anchor₂ : Option String) :
    contentEq (.sequence style₁ items₁ tag₁ anchor₁)
              (.sequence style₂ items₂ tag₂ anchor₂) =
    (items₁.size == items₂.size && contentEq.contentEqList items₁.toList items₂.toList) := by
  unfold contentEq; rfl

-- contentEq on mappings ignores style/tag/anchor: only pairs matter.
theorem contentEq_mapping_pairs (style₁ style₂ : CollectionStyle)
    (pairs₁ pairs₂ : Array (YamlValue × YamlValue))
    (tag₁ tag₂ anchor₁ anchor₂ : Option String) :
    contentEq (.mapping style₁ pairs₁ tag₁ anchor₁)
              (.mapping style₂ pairs₂ tag₂ anchor₂) =
    (pairs₁.size == pairs₂.size && contentEq.contentEqPairList pairs₁.toList pairs₂.toList) := by
  unfold contentEq; rfl

-- contentEq on sequences with any style/tag/anchor equals contentEq with canonical style/tag/anchor.
theorem contentEq_seq_style_irrel (style : CollectionStyle) (items : Array YamlValue)
    (tag anchor : Option String) (v : YamlValue) :
    contentEq (.sequence style items tag anchor) v =
    contentEq (.sequence .flow items none none) v := by
  cases v with
  | sequence style₂ items₂ tag₂ anchor₂ =>
    rw [contentEq_sequence_items, contentEq_sequence_items]
  | _ => unfold contentEq; rfl

-- contentEq on mappings with any style/tag/anchor equals contentEq with canonical style/tag/anchor.
theorem contentEq_map_style_irrel (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag anchor : Option String) (v : YamlValue) :
    contentEq (.mapping style pairs tag anchor) v =
    contentEq (.mapping .flow pairs none none) v := by
  cases v with
  | mapping style₂ pairs₂ tag₂ anchor₂ =>
    rw [contentEq_mapping_pairs, contentEq_mapping_pairs]
  | _ => unfold contentEq; rfl

/-! ### §5.3  Front B — value-recovery trace, brick 1: outer-shape recovery

The two non-empty content-fidelity sorries (`emit_roundtrip_{sequence,mapping}_content_eq`)
owe "the exact parsed value structure from parser trace": that re-parsing emitted flow output
recovers a `.sequence` / `.mapping` whose children are the per-element parses. The *first* link
of that trace is purely structural and emission-independent: the flow-collection parsers
**always** wrap their accumulated items/pairs in `.sequence .flow _ none none` /
`.mapping .flow _ none none` on success (the lone `.ok` branch of `parseFlowSequence` /
`parseFlowMapping` literally constructs that head; every other path is an `.error`). So before
any per-element recovery, the parsed value's *outer constructor* is pinned. These are the parser
primitives the later trace lifts (through `parseNode`/`parseDocument`/`parseStream` and
`compose`) to `(raw_docs.map YamlDocument.compose)[0]!.value`; verified-but-unconsumed until that
lift lands. -/

/-- **Outer-shape recovery (sequence).** A successful `parseFlowSequence` yields a flow sequence
    value with default (`none`) tag/anchor — structurally, regardless of fuel or contents: the
    only `.ok` branch constructs `YamlValue.sequence .flow items` (and `.sequence .flow items`
    *is* `.sequence .flow items none none` by the constructor defaults). The first link of Front
    B's value-recovery trace. -/
theorem parseFlowSequence_produces_sequence (ps : ParseState) (fuel : Nat)
    (v : YamlValue) (ps' : ParseState)
    (h : parseFlowSequence ps fuel = .ok (v, ps')) :
    ∃ items', v = .sequence .flow items' none none := by
  cases fuel with
  | zero => simp only [parseFlowSequence, reduceCtorEq] at h
  | succ n =>
    simp only [parseFlowSequence, bind, Except.bind] at h
    cases hl : parseFlowSequenceLoop ps.advance n #[] with
    | error e => rw [hl] at h; simp only [reduceCtorEq] at h
    | ok r =>
      obtain ⟨items, ps2⟩ := r
      rw [hl] at h
      simp only [] at h
      cases hp : ps2.peek? with
      | none => rw [hp] at h; simp only [reduceCtorEq] at h
      | some tok =>
        cases tok with
        | flowSequenceEnd =>
          rw [hp] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨items, h.1.symm⟩
        | _ => rw [hp] at h; simp only [reduceCtorEq] at h

/-- **Outer-shape recovery (mapping).** Mirror of `parseFlowSequence_produces_sequence`: a
    successful `parseFlowMapping` yields a flow mapping value with default tag/anchor — the only
    `.ok` branch constructs `YamlValue.mapping .flow pairs`. -/
theorem parseFlowMapping_produces_mapping (ps : ParseState) (fuel : Nat)
    (v : YamlValue) (ps' : ParseState)
    (h : parseFlowMapping ps fuel = .ok (v, ps')) :
    ∃ pairs', v = .mapping .flow pairs' none none := by
  cases fuel with
  | zero => simp only [parseFlowMapping, reduceCtorEq] at h
  | succ n =>
    simp only [parseFlowMapping, bind, Except.bind] at h
    cases hl : parseFlowMappingLoop ps.advance n #[] with
    | error e => rw [hl] at h; simp only [reduceCtorEq] at h
    | ok r =>
      obtain ⟨pairs, ps2⟩ := r
      rw [hl] at h
      simp only [] at h
      cases hp : ps2.peek? with
      | none => rw [hp] at h; simp only [reduceCtorEq] at h
      | some tok =>
        cases tok with
        | flowMappingEnd =>
          rw [hp] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨pairs, h.1.symm⟩
        | _ => rw [hp] at h; simp only [reduceCtorEq] at h

/-! ### §5.4  Front B — value-recovery trace, brick 2 sub-link (a): `parseNode` dispatch

Brick 1 (§5.3) pinned the *outer constructor* of `parseFlowSequence` / `parseFlowMapping`. Brick 2
lifts that one level up the parser stack: when `parseNode` faces a `.flowSequenceStart` /
`.flowMappingStart` lookahead it dispatches — through `parseNodeProperties` (a no-op here, since the
token is neither anchor nor tag, by `parseNodeProperties_skip`) and `parseNodeContent` (which routes
a `.flowSequenceStart`/`.flowMappingStart` peek straight to the flow parser) — to `parseFlowSequence`
/ `parseFlowMapping`, then runs `applyNodeFinalization`. With **empty** node properties
(`({} : NodeProperties).tag = .anchor = none` — exactly the emitter's output, which never emits
anchors or tags) finalization rewrites the flow collection's `none none` tag/anchor slots to
`props.tag` / `props.anchor`, i.e. back to `none none`: the outer shape survives the lift verbatim.

This is the `parseNode` analogue of the scalar dispatch packaged in `parseStream_three_tokens_scalar`
(`EmitterScannability.lean:186`, whose `h_parseNode`/`h_finalize` steps do the same threading for a
scalar peek). Verified-but-unconsumed until brick 2 sub-link (b) (`compose` preserving the outer
constructor) and the `parseStream`/`parseDocument` wrapping land. -/

/-- **`parseNode` dispatch (sequence).** A successful `parseNode` whose lookahead is
    `.flowSequenceStart` produces a flow sequence with default (`none`) tag/anchor: the token is
    neither anchor nor tag so `parseNodeProperties` skips (empty props), `validateNodeProps` passes
    (no block-collection / duplicate-anchor trigger), content dispatch routes to `parseFlowSequence`
    (whose outer shape `parseFlowSequence_produces_sequence` pins to `.sequence .flow _ none none`),
    and `applyNodeFinalization` leaves that head untouched because the empty props supply `none`
    tag/anchor. Brick 2's dispatch link, lifting brick 1 through `parseNode`. -/
theorem parseNode_flowSeqStart_produces_sequence (ps : ParseState) (fuel : Nat)
    (v : YamlValue) (ps' : ParseState)
    (h_peek : ps.peek? = some .flowSequenceStart)
    (h : parseNode ps fuel = .ok (v, ps')) :
    ∃ items', v = .sequence .flow items' none none := by
  cases fuel with
  | zero => simp only [parseNode, reduceCtorEq] at h
  | succ n =>
    -- properties skip (flowSequenceStart is neither anchor nor tag)
    have h_np : parseNodeProperties ps = .ok ({}, ps) :=
      parseNodeProperties_skip ps (by rw [h_peek]; trivial)
    -- validation passes for any prePropPos (the block-start / dup-anchor triggers don't fire)
    have h_vnp : ∀ p, validateNodeProps ps p ({} : NodeProperties) = .ok () := by
      intro p; unfold validateNodeProps
      simp only [h_peek, bind, Except.bind, pure, Except.pure]
      rfl
    -- content dispatch routes a flowSequenceStart peek to parseFlowSequence (at decremented fuel)
    have h_pnc : parseNodeContent ps n ({} : NodeProperties) = parseFlowSequence ps n := by
      unfold parseNodeContent; rw [h_peek]
    unfold parseNode at h
    simp only [h_peek, bind, Except.bind, pure, Except.pure, h_np, h_vnp, h_pnc] at h
    cases hfs : parseFlowSequence ps n with
    | error e => rw [hfs] at h; simp only [reduceCtorEq] at h
    | ok r =>
      obtain ⟨val, ps_c⟩ := r
      obtain ⟨items', hval⟩ := parseFlowSequence_produces_sequence ps n val ps_c hfs
      rw [hfs] at h
      simp only [Except.ok.injEq] at h
      subst hval
      refine ⟨items', ?_⟩
      have h1 := congrArg Prod.fst h
      simp only [applyNodeFinalization] at h1
      exact h1.symm

/-- **`parseNode` dispatch (mapping).** Mirror of `parseNode_flowSeqStart_produces_sequence`: a
    successful `parseNode` whose lookahead is `.flowMappingStart` produces a flow mapping with
    default tag/anchor, by the same skip / dispatch / finalization-is-identity argument over
    `parseFlowMapping_produces_mapping`. -/
theorem parseNode_flowMapStart_produces_mapping (ps : ParseState) (fuel : Nat)
    (v : YamlValue) (ps' : ParseState)
    (h_peek : ps.peek? = some .flowMappingStart)
    (h : parseNode ps fuel = .ok (v, ps')) :
    ∃ pairs', v = .mapping .flow pairs' none none := by
  cases fuel with
  | zero => simp only [parseNode, reduceCtorEq] at h
  | succ n =>
    have h_np : parseNodeProperties ps = .ok ({}, ps) :=
      parseNodeProperties_skip ps (by rw [h_peek]; trivial)
    have h_vnp : ∀ p, validateNodeProps ps p ({} : NodeProperties) = .ok () := by
      intro p; unfold validateNodeProps
      simp only [h_peek, bind, Except.bind, pure, Except.pure]
      rfl
    have h_pnc : parseNodeContent ps n ({} : NodeProperties) = parseFlowMapping ps n := by
      unfold parseNodeContent; rw [h_peek]
    unfold parseNode at h
    simp only [h_peek, bind, Except.bind, pure, Except.pure, h_np, h_vnp, h_pnc] at h
    cases hfm : parseFlowMapping ps n with
    | error e => rw [hfm] at h; simp only [reduceCtorEq] at h
    | ok r =>
      obtain ⟨val, ps_c⟩ := r
      obtain ⟨pairs', hval⟩ := parseFlowMapping_produces_mapping ps n val ps_c hfm
      rw [hfm] at h
      simp only [Except.ok.injEq] at h
      subst hval
      refine ⟨pairs', ?_⟩
      have h1 := congrArg Prod.fst h
      simp only [applyNodeFinalization] at h1
      exact h1.symm

/-! ### §5.5  Front B — value-recovery trace, brick 2 sub-link (b): `compose` preserves outer shape

Brick 2 sub-link (a) (§5.4) pinned the outer constructor through `parseNode`; the parsed
serialization tree's head is `.sequence .flow _ none none` / `.mapping .flow _ none none`. But the
content-fidelity sorries compare against `(raw_docs.map YamlDocument.compose)[0]!.value` — the
*composed* representation graph, not the raw parse. `compose` (YAML 1.2.2 §3.1) is
`resolveAliases` then `stripAnchors` on the value field. Both walk the tree and **recurse into the
children**, but on a collection head they pass `style` and `tag` through verbatim, and `stripAnchors`
forces `anchor := none` — so a `.sequence .flow _ none none` / `.mapping .flow _ none none` head
survives `compose` with the *same outer constructor* (only the items/pairs arrays are rewritten by
the recursive child-walk, which is brick 3's concern). This closes the outer-shape half of the trace:
the composed value is still a flow collection with default tag/anchor, exactly what
`contentEq_{seq,map}_style_irrel` need before the per-element comparison. Verified-but-unconsumed
until the `parseStream`/`parseDocument` wrapping (which feeds a real `doc.value` into these) and
brick 3 (the per-element induction) land. -/

/-- **`compose` preserves outer shape (sequence).** If a document's value is a flow sequence with
    default tag/anchor, then so is its `compose`d value: `compose` runs `resolveAliases` then
    `stripAnchors` on the value, and both preserve the `.sequence .flow _ none none` head (passing
    `style`/`tag` through, and `stripAnchors` clearing the anchor slot to the `none` it already
    held). The recursive child-walk rewrites only the items array. Brick 2 sub-link (b), lifting the
    outer shape across `compose`. -/
theorem compose_preserves_flow_sequence (doc : YamlDocument) (items' : Array YamlValue)
    (h : doc.value = .sequence .flow items' none none) :
    ∃ items'', (doc.compose).value = .sequence .flow items'' none none := by
  have hv : (doc.compose).value
      = (doc.value.resolveAliases doc.anchors).stripAnchors := rfl
  rw [hv, h]
  unfold YamlValue.resolveAliases YamlValue.stripAnchors
  exact ⟨_, rfl⟩

/-- **`compose` preserves outer shape (mapping).** Mirror of `compose_preserves_flow_sequence`: a
    flow mapping with default tag/anchor stays a flow mapping with default tag/anchor across
    `compose`, by the same `resolveAliases`/`stripAnchors` pass-through and the recursive child-walk
    touching only the pairs array. -/
theorem compose_preserves_flow_mapping (doc : YamlDocument) (pairs' : Array (YamlValue × YamlValue))
    (h : doc.value = .mapping .flow pairs' none none) :
    ∃ pairs'', (doc.compose).value = .mapping .flow pairs'' none none := by
  have hv : (doc.compose).value
      = (doc.value.resolveAliases doc.anchors).stripAnchors := rfl
  rw [hv, h]
  unfold YamlValue.resolveAliases YamlValue.stripAnchors
  exact ⟨_, rfl⟩

/-! ### §5.6  Front B — value-recovery trace, brick 2 last link (part 1): `parseDocument` dispatch

Brick 2 sub-link (a) (§5.4) pinned the outer constructor through `parseNode`; sub-link (b) (§5.5)
lifted it across `compose`. The remaining wrapping is `parseStream` → `parseStreamLoop` →
`parseDocument` → `parseNode`. `parseStream_doc_from_parseDocument` (`ParserWellBehaved`) already
bridges the loop: every document `parseStream` emits came from a `parseDocument` on a state with the
same token array. This section supplies the next link up — `parseDocument` itself preserves the
flow-collection outer shape.

On a `.flowSequenceStart` / `.flowMappingStart` lookahead, `prepareDocumentState` skips directives
(the token is no directive, by `parseDirectives_skip`), sets `tagHandles := #[]` and consumes no
`---` (the peek is not `.documentStart`), leaving the lookahead intact; the root-node dispatch — since
the peek is neither `.documentEnd`/`.streamEnd`/`none` — routes to `parseNode`, whose output (by brick
2(a)) is `.sequence .flow _ none none` / `.mapping .flow _ none none`; `parseDocument` then stores that
verbatim in the document's `value` field. Verified-but-unconsumed until the first-document
position-pinning (that the first emitted doc's `parseDocument` runs at pos 1, peeking the emitter's
leading `[` / `{`) joins it to `parseStream_doc_from_parseDocument` and brick 2(b). -/

/-- **`parseDocument` dispatch (sequence).** A successful `parseDocument` whose lookahead is
    `.flowSequenceStart` produces a document whose value is a flow sequence with default tag/anchor:
    `prepareDocumentState` skips the (non-directive) token leaving the peek intact, the root-node
    dispatch routes the peek to `parseNode` (not the empty-node branch), and brick 2(a)
    (`parseNode_flowSeqStart_produces_sequence`) pins that node's shape, which `parseDocument` stores
    verbatim. The `parseDocument` link of brick 2's wrapping. -/
theorem parseDocument_flowSeqStart_produces_sequence (ps : ParseState)
    (doc : YamlDocument) (ps' : ParseState)
    (h_peek : ps.peek? = some .flowSequenceStart)
    (h : parseDocument ps = .ok (doc, ps')) :
    ∃ items', doc.value = .sequence .flow items' none none := by
  -- prepareDocumentState skips the (non-directive) flowSequenceStart, leaving the peek intact
  have h_pd : parseDirectives ps = (#[], ps) :=
    parseDirectives_skip ps (by rw [h_peek]; trivial)
  have h_peek_a : ({ ps with tagHandles := #[] } : ParseState).peek? = some .flowSequenceStart := by
    rw [show ({ ps with tagHandles := #[] } : ParseState).peek? = ps.peek? from rfl]; exact h_peek
  have h_prep : prepareDocumentState ps = .ok (#[], { ps with tagHandles := #[] }) := by
    unfold prepareDocumentState
    rw [h_pd]
    simp only [Array.filterMap_empty]
    rw [show (({ ps with tagHandles := #[] } : ParseState).peek? == some YamlToken.documentStart)
          = false from by rw [h_peek_a]; decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold ParseState.tryConsume
    rw [h_peek_a]
    simp only [show (BEq.beq YamlToken.flowSequenceStart YamlToken.documentStart) = false from by decide,
               Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind]
  -- root-node dispatch: flowSequenceStart routes to parseNode (not the empty-node branch)
  unfold parseDocument at h
  simp only [bind, Except.bind, h_prep, h_peek_a] at h
  cases h_pn : parseNode ({ ps with tagHandles := #[] } : ParseState)
      (4 * ({ ps with tagHandles := #[] } : ParseState).tokens.size + 4) with
  | error e => rw [h_pn] at h; simp only [reduceCtorEq] at h
  | ok r =>
    obtain ⟨val, ps_b⟩ := r
    obtain ⟨items', hval⟩ :=
      parseNode_flowSeqStart_produces_sequence _ _ val ps_b h_peek_a h_pn
    rw [h_pn] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨items', hval⟩

/-- **`parseDocument` dispatch (mapping).** Mirror of `parseDocument_flowSeqStart_produces_sequence`:
    a successful `parseDocument` whose lookahead is `.flowMappingStart` produces a document whose
    value is a flow mapping with default tag/anchor, by the same directive-skip / root dispatch /
    `parseNode`-shape (`parseNode_flowMapStart_produces_mapping`) argument. -/
theorem parseDocument_flowMapStart_produces_mapping (ps : ParseState)
    (doc : YamlDocument) (ps' : ParseState)
    (h_peek : ps.peek? = some .flowMappingStart)
    (h : parseDocument ps = .ok (doc, ps')) :
    ∃ pairs', doc.value = .mapping .flow pairs' none none := by
  have h_pd : parseDirectives ps = (#[], ps) :=
    parseDirectives_skip ps (by rw [h_peek]; trivial)
  have h_peek_a : ({ ps with tagHandles := #[] } : ParseState).peek? = some .flowMappingStart := by
    rw [show ({ ps with tagHandles := #[] } : ParseState).peek? = ps.peek? from rfl]; exact h_peek
  have h_prep : prepareDocumentState ps = .ok (#[], { ps with tagHandles := #[] }) := by
    unfold prepareDocumentState
    rw [h_pd]
    simp only [Array.filterMap_empty]
    rw [show (({ ps with tagHandles := #[] } : ParseState).peek? == some YamlToken.documentStart)
          = false from by rw [h_peek_a]; decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold ParseState.tryConsume
    rw [h_peek_a]
    simp only [show (BEq.beq YamlToken.flowMappingStart YamlToken.documentStart) = false from by decide,
               Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind]
  unfold parseDocument at h
  simp only [bind, Except.bind, h_prep, h_peek_a] at h
  cases h_pn : parseNode ({ ps with tagHandles := #[] } : ParseState)
      (4 * ({ ps with tagHandles := #[] } : ParseState).tokens.size + 4) with
  | error e => rw [h_pn] at h; simp only [reduceCtorEq] at h
  | ok r =>
    obtain ⟨val, ps_b⟩ := r
    obtain ⟨pairs', hval⟩ :=
      parseNode_flowMapStart_produces_mapping _ _ val ps_b h_peek_a h_pn
    rw [h_pn] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨pairs', hval⟩

/-! ### §5.7  Front B — value-recovery trace, brick 2 last link (part 2): first-document position-pinning

§5.6 lifts the outer shape through `parseDocument`, but `parseDocument_flowSeqStart_produces_sequence`
needs the lookahead `ps.peek? = some .flowSequenceStart`, which holds only at **position 1** — the
emitter's leading `[`. `parseStream_doc_from_parseDocument` (`ParserWellBehaved`) exposes that EVERY
document came from SOME `parseDocument` with the same tokens, but loses the position. This section pins
it for the FIRST document: `parseStream` runs `expect .streamStart` (advancing pos 0 → 1) then enters
`parseStreamLoop` with an EMPTY accumulator, so the first document it produces is the `parseDocument`
output of the loop's entry state — which is at pos 1.

This link is shape-agnostic (no seq/map split): the position fact is identical for any first document.
It joins §5.6 to the head-token scanner facts (`scanFiltered_emit{Seq,Map}_nonempty_structure` give
`tokens[1]!.val = .flowSequenceStart` / `.flowMappingStart`) so that the value-recovery trace's outer
half fires end-to-end on `(raw_docs.map compose)[0]!.value`. Verified-but-unconsumed until §5.8
assembles those into the outer-shape recovery lemma and discharges the per-element body (brick 3). -/

/-- `expect` advances the position by exactly one on success (it returns `ps.advance` whenever the
    lookahead matches). The position half of `expect_tokens`. -/
theorem expect_pos_succ (ps ps' : ParseState) (tok : YamlToken) (desc : String)
    (h : ps.expect tok desc = .ok ps') : ps'.pos = ps.pos + 1 := by
  unfold ParseState.expect at h
  split at h
  · split at h
    · simp only [Except.ok.injEq] at h; subst h; rfl
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

/-- `parseStreamLoop` only ever appends to its accumulator (never reorders or drops), so once the
    accumulator is non-empty its head element is preserved verbatim into the result, and the result
    stays non-empty. The structural invariant behind first-document recovery. -/
theorem parseStreamLoop_preserves_head
    (ps : ParseState) (docs : Array YamlDocument) (streamState : StreamState) (fuel : Nat)
    (result : Array YamlDocument)
    (h_ne : 0 < docs.size)
    (h_ok : parseStreamLoop ps docs streamState fuel = .ok result) :
    0 < result.size ∧ result[0]! = docs[0]! := by
  induction fuel generalizing ps docs streamState with
  | zero =>
    simp only [parseStreamLoop, Except.ok.injEq] at h_ok
    subst h_ok; exact ⟨h_ne, rfl⟩
  | succ fuel ih =>
    unfold parseStreamLoop at h_ok
    split at h_ok
    · -- streamEnd → result = docs
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact ⟨h_ne, rfl⟩
    · -- none → result = docs
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact ⟨h_ne, rfl⟩
    · rename_i tok
      split at h_ok
      · simp at h_ok  -- validation failure → error, contradiction
      · dsimp only [] at h_ok
        generalize h_pd : parseDocument ps = pd_result at h_ok
        cases pd_result with
        | error e => simp at h_ok
        | ok val =>
          obtain ⟨doc_new, ps'⟩ := val
          dsimp only [] at h_ok
          have h_ne' : 0 < (docs.push doc_new).size := by rw [Array.size_push]; omega
          have h_push_head : (docs.push doc_new)[0]! = docs[0]! := by
            rw [getElem!_pos (docs.push doc_new) 0 h_ne', getElem!_pos docs 0 h_ne]
            exact Array.getElem_push_lt h_ne
          split at h_ok
          · -- stuck → result = docs.push doc_new
            simp only [Except.ok.injEq] at h_ok; subst h_ok; exact ⟨h_ne', h_push_head⟩
          · -- recurse: head still preserved through the deeper call
            obtain ⟨h_rs, h_rh⟩ := ih _ _ _ h_ne' h_ok
            exact ⟨h_rs, h_rh.trans h_push_head⟩

/-- The FIRST document `parseStreamLoop` produces from an EMPTY accumulator came from `parseDocument`
    run on the loop's ENTRY state. A non-empty result forces the productive branch (peek is not
    `streamEnd`/`none`, validation passes, `parseDocument` succeeds), and `parseStreamLoop_preserves_head`
    carries the freshly-pushed doc through any deeper recursion as `result[0]!`. -/
theorem parseStreamLoop_first_doc_from_entry
    (ps : ParseState) (streamState : StreamState) (fuel : Nat)
    (result : Array YamlDocument)
    (h_ok : parseStreamLoop ps #[] streamState fuel = .ok result)
    (h_ne : 0 < result.size) :
    ∃ ps', parseDocument ps = .ok (result[0]!, ps') := by
  cases fuel with
  | zero =>
    simp only [parseStreamLoop, Except.ok.injEq] at h_ok
    subst h_ok; simp at h_ne
  | succ fuel =>
    unfold parseStreamLoop at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; simp at h_ne  -- streamEnd → empty, ⊥
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; simp at h_ne  -- none → empty, ⊥
    · rename_i tok
      split at h_ok
      · simp at h_ok  -- validation failure
      · dsimp only [] at h_ok
        generalize h_pd : parseDocument ps = pd_result at h_ok
        cases pd_result with
        | error e => simp at h_ok
        | ok val =>
          obtain ⟨doc_new, ps'⟩ := val
          dsimp only [] at h_ok
          have h_head : result[0]! = doc_new := by
            have h_one : 0 < (#[].push doc_new : Array YamlDocument).size := by
              rw [Array.size_push]; simp
            split at h_ok
            · -- stuck → result = #[].push doc_new
              simp only [Except.ok.injEq] at h_ok; subst h_ok
              rw [getElem!_pos _ 0 h_one]; simp
            · -- recurse: head preserved
              obtain ⟨_, h_rh⟩ :=
                parseStreamLoop_preserves_head _ _ _ fuel _ h_one h_ok
              rw [h_rh, getElem!_pos _ 0 h_one]; simp
          -- Plugging the witness `ps'` collapses `parseDocument ps` to `h_pd`'s RHS, so the goal is
          -- `Except.ok (doc_new, ps') = Except.ok (result[0]!, ps')`; `h_head` rewrites it to `rfl`.
          exact ⟨ps', by rw [h_head]⟩

/-- **First-document position-pinning.** When `parseStream` succeeds with a non-empty document array,
    its first document came from a `parseDocument` run on a state at position 1 — just past
    `streamStart` — over the same token array. Joins §5.6's `parseDocument` dispatch to the head-token
    scanner facts: at pos 1 the lookahead is `tokens[1]`, which for emitted flow collections is the
    leading `[` / `{`. The position-dependent half of brick 2's wrapping. -/
theorem parseStream_first_doc_at_pos_one
    (tokens : Array (Positioned YamlToken)) (docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok docs)
    (h_ne : 0 < docs.size) :
    ∃ ps ps', ps.tokens = tokens ∧ ps.pos = 1 ∧ parseDocument ps = .ok (docs[0]!, ps') := by
  unfold parseStream at h_parse
  simp only [bind, Except.bind] at h_parse
  split at h_parse
  · simp at h_parse
  · rename_i ps_start h_expect
    have h_tok : ps_start.tokens = tokens :=
      (expect_tokens _ _ _ _ h_expect).trans (by simp)
    have h_pos : ps_start.pos = 1 := by
      rw [expect_pos_succ _ _ _ _ h_expect]
    obtain ⟨ps', h_pd⟩ :=
      parseStreamLoop_first_doc_from_entry ps_start .initial tokens.size docs h_parse h_ne
    exact ⟨ps_start, ps', h_tok, h_pos, h_pd⟩

/-! ### §5.8  Front B — value-recovery trace, brick 2 assembled: outer-shape recovery end-to-end

§5.3–§5.7 supplied the individual links of Front B's value-recovery trace; this section composes them
into the **outer-shape half**, end-to-end on the parse side. Given a successful `parseStream` whose
first token after `streamStart` (position 1) is the flow opener `.flowSequenceStart` /
`.flowMappingStart`, the **composed** first document's value is a flow collection with default
tag/anchor:

  `parseStream_first_doc_at_pos_one` (§5.7) — the first doc came from `parseDocument` run at pos 1;
  `parseDocument_flow{Seq,Map}Start_produces_{sequence,mapping}` (§5.6) — that doc's value is the flow shape;
  `compose_preserves_flow_{sequence,mapping}` (§5.5) — the shape survives `compose`;
  + a `getElem!`/`Array.map` bridge landing it on `(raw_docs.map compose)[0]!.value`.

The two head-token hypotheses (`1 < tokens.size`, `tokens[1]!.val = .flowSequenceStart` /
`.flowMappingStart`) are exactly what `scanFiltered_emit{Seq,Map}_nonempty_structure`
(`NonemptyStructure`) already delivers for emitted flow collections (it gives `tokens.size ≥ 5` and the
position-1 opener as conjuncts). So the consumer (`emit_roundtrip_{sequence,mapping}_content_eq`,
`EmitterScannability.lean:845`/`:885`) discharges them from the scan, then this lemma +
`contentEq_{seq,map}_style_irrel` + `contentEq_{sequence_items,mapping_pairs}` reduce the
content-fidelity goal to the per-element comparison `contentEqList` / `contentEqPairList` — **brick 3**,
the per-element flow-loop induction. Kept parameterized on the head-token facts (rather than importing
the scan-side structure lemma here) so this section owns exactly the parse-side links. Verified-but-
unconsumed until brick 3 lands and the two content-fidelity sorries close. -/

/-- **Outer-shape recovery, assembled (sequence).** A successful `parseStream` whose position-1
    lookahead is `.flowSequenceStart` recovers a composed first document whose value is a flow sequence
    with default tag/anchor. Composes §5.7 (position-pinning) → §5.6 (`parseDocument` dispatch) → §5.5
    (`compose` preserves the head), then bridges `(raw_docs.map compose)[0]!`. The full outer-shape half
    of Front B's value-recovery trace; only the per-element body (brick 3) remains. -/
theorem parseStream_flowSeqStart_recovers_outer_shape
    (tokens : Array (Positioned YamlToken)) (raw_docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok raw_docs)
    (h_ne : 0 < raw_docs.size)
    (h_lt : 1 < tokens.size)
    (h_head : tokens[1]!.val = .flowSequenceStart) :
    ∃ items'', (raw_docs.map YamlDocument.compose)[0]!.value = .sequence .flow items'' none none := by
  obtain ⟨ps, ps', h_ps_tok, h_ps_pos, h_pd⟩ :=
    parseStream_first_doc_at_pos_one tokens raw_docs h_parse h_ne
  have h_peek : ps.peek? = some .flowSequenceStart := by
    unfold ParseState.peek?
    rw [h_ps_pos, h_ps_tok, if_pos h_lt, h_head]
  obtain ⟨items', h_doc_val⟩ :=
    parseDocument_flowSeqStart_produces_sequence ps raw_docs[0]! ps' h_peek h_pd
  obtain ⟨items'', h_comp⟩ := compose_preserves_flow_sequence raw_docs[0]! items' h_doc_val
  refine ⟨items'', ?_⟩
  have h_map : (raw_docs.map YamlDocument.compose)[0]! = (raw_docs[0]!).compose := by
    have h0' : 0 < (raw_docs.map YamlDocument.compose).size := by rw [Array.size_map]; omega
    rw [getElem!_pos _ 0 h0', getElem!_pos raw_docs 0 h_ne, Array.getElem_map]
  rw [h_map]; exact h_comp

/-- **Outer-shape recovery, assembled (mapping).** Mirror of `parseStream_flowSeqStart_recovers_outer_shape`:
    a successful `parseStream` whose position-1 lookahead is `.flowMappingStart` recovers a composed
    first document whose value is a flow mapping with default tag/anchor, by the same §5.7 → §5.6 → §5.5
    composition over the mapping-side links and the same `getElem!`/`Array.map` bridge. -/
theorem parseStream_flowMapStart_recovers_outer_shape
    (tokens : Array (Positioned YamlToken)) (raw_docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok raw_docs)
    (h_ne : 0 < raw_docs.size)
    (h_lt : 1 < tokens.size)
    (h_head : tokens[1]!.val = .flowMappingStart) :
    ∃ pairs'', (raw_docs.map YamlDocument.compose)[0]!.value = .mapping .flow pairs'' none none := by
  obtain ⟨ps, ps', h_ps_tok, h_ps_pos, h_pd⟩ :=
    parseStream_first_doc_at_pos_one tokens raw_docs h_parse h_ne
  have h_peek : ps.peek? = some .flowMappingStart := by
    unfold ParseState.peek?
    rw [h_ps_pos, h_ps_tok, if_pos h_lt, h_head]
  obtain ⟨pairs', h_doc_val⟩ :=
    parseDocument_flowMapStart_produces_mapping ps raw_docs[0]! ps' h_peek h_pd
  obtain ⟨pairs'', h_comp⟩ := compose_preserves_flow_mapping raw_docs[0]! pairs' h_doc_val
  refine ⟨pairs'', ?_⟩
  have h_map : (raw_docs.map YamlDocument.compose)[0]! = (raw_docs[0]!).compose := by
    have h0' : 0 < (raw_docs.map YamlDocument.compose).size := by rw [Array.size_map]; omega
    rw [getElem!_pos _ 0 h0', getElem!_pos raw_docs 0 h_ne, Array.getElem_map]
  rw [h_map]; exact h_comp

/-! ### §5.9  Front B — value-recovery trace, brick 3 prep: content-list step algebra

Brick 1–2 (§5.3–§5.8) recovered the *outer shape* of the re-parsed value: the composed first
document is a flow `.sequence` / `.mapping` whose body is the parser's existential `items''` /
`pairs''`. Consuming that into `emit_roundtrip_{sequence,mapping}_content_eq` (R578) retyped each
content-fidelity sorry to its **brick-3 residual** — the per-element comparison

  `(items.size == items''.size && contentEq.contentEqList items.toList items''.toList) = true`
  `(pairs.size == pairs''.size && contentEq.contentEqPairList pairs.toList pairs''.toList) = true`

Brick 3 discharges that by an induction over `parseFlowSequenceLoop` / `parseFlowMappingLoop`
carrying a *content invariant*: after parsing `k` entries the accumulator (raw items, then composed)
is pairwise content-equal to the original's first `k`. Each loop iteration `parseNode`s one entry and
`Array.push`es it; the per-element round-trip IH supplies one fresh content-equal element. The
invariant therefore extends **one element at a time** — and that extension is exactly the algebra
below: appending content-equal elements to content-equal lists preserves `contentEqList` /
`contentEqPairList` (and the `Array.push` corollaries the loop accumulator extends by). These are the
emission-independent, decidable list-fold *steps* the brick-3 loop invariant consumes; the parse-side
loop induction (relating the accumulator to `emitList`'s spans) is the remaining work. The base case
(`contentEqList [] [] = true`) and the size half are immediate. Verified-but-unconsumed until that
induction lands. -/

/-- **Content-list step (sequence, lists).** Appending one content-equal element to each of two
    content-equal value lists keeps them content-equal: the `contentEqList` inductive step the
    brick-3 flow-sequence loop invariant extends by, one parsed item per iteration. (Length-mismatch
    cases are vacuous — `contentEqList` is already `false` there, so `h` is unsatisfiable.) -/
theorem contentEqList_append_singleton (l₁ l₂ : List YamlValue) (a b : YamlValue)
    (h : contentEq.contentEqList l₁ l₂ = true) (hab : contentEq a b = true) :
    contentEq.contentEqList (l₁ ++ [a]) (l₂ ++ [b]) = true := by
  match l₁, l₂ with
  | [], [] =>
      simp only [List.nil_append, contentEq.contentEqList, Bool.and_true]; exact hab
  | [], _ :: _ => simp [contentEq.contentEqList] at h
  | _ :: _, [] => simp [contentEq.contentEqList] at h
  | x :: xs, y :: ys =>
      simp only [contentEq.contentEqList, Bool.and_eq_true] at h
      simp only [List.cons_append, contentEq.contentEqList, Bool.and_eq_true]
      exact ⟨h.1, contentEqList_append_singleton xs ys a b h.2 hab⟩

/-- **Content-list step (sequence, accumulator).** `Array.push` corollary of
    `contentEqList_append_singleton`: pushing content-equal elements onto two content-equal arrays
    keeps their `toList`s content-equal. This is the exact shape the brick-3 sequence loop invariant
    extends by (the loop accumulator is an `Array YamlValue` grown via `items_acc.push val`). -/
theorem contentEqList_push (A B : Array YamlValue) (a b : YamlValue)
    (h : contentEq.contentEqList A.toList B.toList = true) (hab : contentEq a b = true) :
    contentEq.contentEqList (A.push a).toList (B.push b).toList = true := by
  rw [Array.toList_push, Array.toList_push]
  exact contentEqList_append_singleton A.toList B.toList a b h hab

/-- **Content-pair-list step (mapping, lists).** Mirror of `contentEqList_append_singleton` for
    key/value pair lists: appending one content-equal pair to each of two content-equal pair lists
    keeps them content-equal. The `contentEqPairList` inductive step the brick-3 flow-mapping loop
    invariant extends by, one parsed entry per iteration. -/
theorem contentEqPairList_append_singleton (l₁ l₂ : List (YamlValue × YamlValue))
    (ka va kb vb : YamlValue)
    (h : contentEq.contentEqPairList l₁ l₂ = true)
    (hk : contentEq ka kb = true) (hv : contentEq va vb = true) :
    contentEq.contentEqPairList (l₁ ++ [(ka, va)]) (l₂ ++ [(kb, vb)]) = true := by
  match l₁, l₂ with
  | [], [] =>
      simp only [List.nil_append, contentEq.contentEqPairList, Bool.and_true, Bool.and_eq_true]
      exact ⟨hk, hv⟩
  | [], _ :: _ => simp [contentEq.contentEqPairList] at h
  | _ :: _, [] => simp [contentEq.contentEqPairList] at h
  | (k₁, v₁) :: rest₁, (k₂, v₂) :: rest₂ =>
      simp only [contentEq.contentEqPairList, Bool.and_eq_true] at h
      simp only [List.cons_append, contentEq.contentEqPairList, Bool.and_eq_true]
      exact ⟨⟨h.1.1, h.1.2⟩,
             contentEqPairList_append_singleton rest₁ rest₂ ka va kb vb h.2 hk hv⟩

/-- **Content-pair-list step (mapping, accumulator).** `Array.push` corollary of
    `contentEqPairList_append_singleton`: the exact shape the brick-3 mapping loop invariant extends
    by (the loop accumulator is an `Array (YamlValue × YamlValue)` grown via `pairs_acc.push (k, v)`). -/
theorem contentEqPairList_push (A B : Array (YamlValue × YamlValue))
    (ka va kb vb : YamlValue)
    (h : contentEq.contentEqPairList A.toList B.toList = true)
    (hk : contentEq ka kb = true) (hv : contentEq va vb = true) :
    contentEq.contentEqPairList (A.push (ka, va)).toList (B.push (kb, vb)).toList = true := by
  rw [Array.toList_push, Array.toList_push]
  exact contentEqPairList_append_singleton A.toList B.toList ka va kb vb h hk hv

/-! ### §5.10  Front B — value-recovery trace, brick 3 link (b) scaffold: loop-result list decomposition

§5.9 supplied the *step* algebra (extend two content-equal lists by one content-equal element). Link
(b) — the content-tracking loop induction relating the parser's recovered `items''` / `pairs''` (the
§5.8 existential) element-wise to the original `items` / `pairs` — first needs the purely *structural*
fact that the loop only ever APPENDS to its accumulator: a successful `parseFlowSequenceLoop ps fuel
acc` returns an array whose `toList` is `acc.toList ++ extra`, where `extra` is the (existentially
quantified) list of elements parsed in this call.

This is emission-independent and proved by fuel induction over the loop definition ALONE — no bracket
balance, fuel adequacy, or `ParseNodeFlowSeqOk` machinery (contrast `parseFlowSequenceLoop_emitter_ok`,
`ParserWellBehaved.lean:4184`, which needs all of it to prove the loop SUCCEEDS): every branch either
returns the accumulator verbatim (`extra := []`) or recurses on `acc.push v` (`extra := v :: extra'`,
via `Array.toList_push`). The mapping lemma is the list refinement of `parseFlowMappingLoop_pairs_grow`
(`ParserWellBehaved.lean:2107`, which tracks only the SIZE `≥`).

Instantiated at the loop's entry accumulator `acc := #[]` (where §5.8's trace enters the loop), this
gives `items''.toList = extra` — the scaffold on which brick 3's two residual conjuncts hang: the size
half (`items.size = extra.length`) and the content half (`contentEqList items.toList extra`, via §5.9's
step algebra, once each `extra` element is characterized by the per-element round-trip IH).
Verified-but-unconsumed until that per-element characterization (the remaining hard part of link (b))
lands. -/

/-- **Loop-result list decomposition (sequence).** A successful `parseFlowSequenceLoop` returns an
    array whose `toList` extends the accumulator's `toList` by the list of elements parsed in this
    call. Pure structural fact: fuel induction over the loop, every branch either returns the
    accumulator (`extra := []`) or recurses on `acc.push v` (`extra := v :: …`, via `Array.toList_push`). -/
theorem parseFlowSequenceLoop_result_append
    (ps : ParseState) (fuel : Nat) (acc : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop ps fuel acc = .ok result) :
    ∃ extra, result.1.toList = acc.toList ++ extra := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    cases h_ok
    exact ⟨[], by simp⟩
  | succ k ih =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; cases h_ok; exact ⟨[], by simp⟩
    · all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try contradiction)
      all_goals (try (simp at h_ok))
      all_goals (first
        | (cases h_ok; exact ⟨[], by simp⟩)
        | (obtain ⟨e, he⟩ := ih _ _ h_ok
           rw [he, Array.toList_push, List.append_assoc]; exact ⟨_, rfl⟩))

/-- **Loop-result list decomposition (mapping).** Mirror of `parseFlowSequenceLoop_result_append`: a
    successful `parseFlowMappingLoop` returns a pair array whose `toList` extends the accumulator's by
    the entries parsed in this call. The list refinement of `parseFlowMappingLoop_pairs_grow`
    (`ParserWellBehaved.lean:2107`), same fuel induction with `pairs.push (key, val)`. -/
theorem parseFlowMappingLoop_result_append
    (ps : ParseState) (fuel : Nat) (acc : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop ps fuel acc = .ok result) :
    ∃ extra, result.1.toList = acc.toList ++ extra := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    cases h_ok
    exact ⟨[], by simp⟩
  | succ k ih =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; cases h_ok; exact ⟨[], by simp⟩
    · all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try contradiction)
      all_goals (try (simp at h_ok))
      all_goals (first
        | (cases h_ok; exact ⟨[], by simp⟩)
        | (obtain ⟨e, he⟩ := ih _ _ h_ok
           rw [he, Array.toList_push, List.append_assoc]; exact ⟨_, rfl⟩))

/-! ### §5.11  Front B — value-recovery trace, brick 3 content half: pointwise → fold assembly

§5.9 supplied the *incremental* step (extend two content-equal lists by one content-equal element);
§5.10 supplied the *structural* scaffold (the loop only appends, so `items''.toList = extra`). This
section supplies the **consumer joint** for brick 3's content half: the assembly that packages the
per-element producer's eventual deliverable — *pointwise* content-equality plus equal length — into the
fold `contentEqList` / `contentEqPairList` the retyped residual demands.

It is the dual decomposition to §5.9. §5.9 threads one element per loop iteration (the producer that
accumulates inductively); §5.11 instead lets the producer collect ALL its per-element facts first —
`∀ i, contentEq items[i] extra[i]` (one application of the per-element round-trip IH at each index) plus
`items.size = extra.length` — and assembles them in one shot. Landing it now RETYPES brick 3's content
residual from "prove the fold `contentEqList items.toList extra`" to "prove pointwise
`contentEq items[i] extra[i]` for every `i`, and the length", which is the genuine producer contract the
remaining (hard) span-locality / compositionality bridge owes. Pure list structural induction —
emission-independent, no parser machinery — so it stands in isolation now and is verified-but-unconsumed
until that producer lands ([[ref-consumer-joint-before-producer]], [[ref-universal-packaging-is-its-own-joint]]). -/

/-- **Pointwise → fold (sequence).** Two equal-length value lists that are pointwise content-equal are
    `contentEqList`-equal. The consumer joint for brick 3's content half: it packages the per-element
    deliverable (`∀ i, contentEq l₁[i] l₂[i]`, supplied index-by-index by the per-element round-trip IH)
    + the length into the fold. Pure structural recursion on the first list; the head fact comes from
    index `0`, the tail from the IH at shifted indices. -/
theorem contentEqList_of_pointwise (l₁ l₂ : List YamlValue)
    (h_len : l₁.length = l₂.length)
    (h_pt : ∀ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
              contentEq l₁[i] l₂[i] = true) :
    contentEq.contentEqList l₁ l₂ = true := by
  match l₁, l₂ with
  | [], [] => rfl
  | [], _ :: _ => simp at h_len
  | _ :: _, [] => simp at h_len
  | x :: xs, y :: ys =>
      simp only [contentEq.contentEqList, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · have h0 := h_pt 0 (by simp) (by simp)
        simpa [List.getElem_cons_zero] using h0
      · refine contentEqList_of_pointwise xs ys (by simpa using h_len) ?_
        intro i h₁ h₂
        have hi := h_pt (i + 1) (by simp only [List.length_cons]; omega)
                                (by simp only [List.length_cons]; omega)
        simpa [List.getElem_cons_succ] using hi

/-- **Pointwise → fold (mapping).** Mirror for key/value pair lists: two equal-length pair lists whose
    keys and values are pointwise content-equal are `contentEqPairList`-equal. The consumer joint for
    the mapping side of brick 3's content half; the per-element deliverable here is the pair
    `contentEq l₁[i].1 l₂[i].1 ∧ contentEq l₁[i].2 l₂[i].2` (the IHs `ihk`/`ihv`), assembled into the
    fold. -/
theorem contentEqPairList_of_pointwise (l₁ l₂ : List (YamlValue × YamlValue))
    (h_len : l₁.length = l₂.length)
    (h_pt : ∀ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
              contentEq l₁[i].1 l₂[i].1 = true ∧ contentEq l₁[i].2 l₂[i].2 = true) :
    contentEq.contentEqPairList l₁ l₂ = true := by
  match l₁, l₂ with
  | [], [] => rfl
  | [], _ :: _ => simp at h_len
  | _ :: _, [] => simp at h_len
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys =>
      simp only [contentEq.contentEqPairList, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h0 := (h_pt 0 (by simp) (by simp)).1
        simpa [List.getElem_cons_zero] using h0
      · have h0 := (h_pt 0 (by simp) (by simp)).2
        simpa [List.getElem_cons_zero] using h0
      · refine contentEqPairList_of_pointwise xs ys (by simpa using h_len) ?_
        intro i h₁ h₂
        have hi := h_pt (i + 1) (by simp only [List.length_cons]; omega)
                                (by simp only [List.length_cons]; omega)
        exact ⟨by simpa [List.getElem_cons_succ] using hi.1,
               by simpa [List.getElem_cons_succ] using hi.2⟩

/-! ### §5.12  Front B — value-recovery trace, brick 3 producer prep: emission-string decomposition

§5.9–§5.11 supplied the *consumer* side of brick 3's content half: the step algebra (§5.9), the
loop-result append scaffold (§5.10), and the pointwise → fold assembly joint (§5.11). What remains is
the genuinely *hard* PRODUCER — the span-locality / compositionality bridge that supplies, for each `k`,
`contentEq items[k] extra[k] = true`, by showing the loop's `k`-th `parseNode` consumes exactly the
sub-span `emit items[k]` of the whole emitted stream. **This section lands that producer's FIRST
sub-link**: the purely *emission-structural* fact that the body string `emit.emitList items` IS the
per-element emissions `emit items[k]` glued by the literal separator `", "` — i.e.

  `emit.emitList l = ", ".intercalate (l.map emit)`

and the bracketed whole-`emit` corollary `emit (.sequence …) = "[" ++ ", ".intercalate … ++ "]"`. The
scanner-side token-span decomposition the producer ultimately needs (each inter-`flowEntry` segment of
`scanFiltered (emit …)` equals `scanFiltered (emit items[k])`) cannot even be *stated* until the
emitted string is known to be literally that per-element concatenation. This closed form is exactly the
char-list split currently *inlined ad-hoc* inside `emitList_scans_nonempty`
(`ScanChainGrowth.lean:222`, `(emit.emitList (v :: v' :: vs)).toList ++ rest = (emit v).toList ++ …`),
finally factored as a reusable lemma.

Proved by structural induction over the list — emission-independent, no scanner/parser machinery — the
three `emit.emitList` cases (`[]`, `[v]`, `v :: w :: ws`) matching `String.intercalate`'s
`intercalate_nil` / `intercalate_singleton` / `intercalate_cons_cons` one-for-one. Verified-but-unconsumed
until the scanner-side span decomposition (the producer's next sub-link) consumes it. -/

/-- **Emission-string decomposition (sequence body).** The comma-separated flow-sequence body emitted by
    `emit.emitList` is the `", "`-intercalation of the per-element emissions: `emit.emitList l =
    ", ".intercalate (l.map emit)`. The closed form on which the producer's span-locality rests — the
    body string IS `emit items[0] ++ ", " ++ emit items[1] ++ …`. Pure structural induction; the three
    `emitList` cases match `String.intercalate`'s `nil` / `singleton` / `cons_cons`. -/
theorem emitList_eq_intercalate (l : List YamlValue) :
    emit.emitList l = ", ".intercalate (l.map emit) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    cases vs with
    | nil => rfl
    | cons w ws =>
      have h : emit.emitList (v :: w :: ws) = emit v ++ ", " ++ emit.emitList (w :: ws) := rfl
      rw [h, ih]
      simp only [List.map_cons, String.intercalate_cons_cons]

/-- **Emission-string decomposition (mapping body).** Mirror for key/value entries: the flow-mapping body
    emitted by `emit.emitPairList` is the `", "`-intercalation of the per-entry emissions `emit k ++ ": "
    ++ emit v`. Same structural induction, destructuring each head pair so the `emitPairList` equations
    fire. -/
theorem emitPairList_eq_intercalate (l : List (YamlValue × YamlValue)) :
    emit.emitPairList l
      = ", ".intercalate (l.map (fun p => emit p.1 ++ ": " ++ emit p.2)) := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    cases rest with
    | nil => obtain ⟨k, v⟩ := p; rfl
    | cons q qs =>
      obtain ⟨k, v⟩ := p
      have h : emit.emitPairList ((k, v) :: q :: qs)
             = emit k ++ ": " ++ emit v ++ ", " ++ emit.emitPairList (q :: qs) := rfl
      rw [h, ih]
      simp only [List.map_cons, String.intercalate_cons_cons]

/-- **Whole-`emit` bracketed form (sequence).** A flow sequence emits as its bracketed body intercalation:
    `emit (.sequence …) = "[" ++ ", ".intercalate (items.toList.map emit) ++ "]"`. The producer-facing
    statement — the WHOLE emitted stream, expressed per-element. Immediate from `emitList_eq_intercalate`
    (the `style`/`tag`/`anchor` fields are irrelevant to the body). -/
theorem emit_sequence_eq_bracket_intercalate
    (style : CollectionStyle) (items : Array YamlValue)
    (tag anchor : Option String) :
    emit (.sequence style items tag anchor)
      = "[" ++ ", ".intercalate (items.toList.map emit) ++ "]" := by
  show "[" ++ emit.emitList items.toList ++ "]"
      = "[" ++ ", ".intercalate (items.toList.map emit) ++ "]"
  rw [emitList_eq_intercalate]

/-- **Whole-`emit` bracketed form (mapping).** Mirror: `emit (.mapping …) = "{" ++ ", ".intercalate
    (pairs.toList.map (fun p => emit p.1 ++ ": " ++ emit p.2)) ++ "}"`. Immediate from
    `emitPairList_eq_intercalate`. -/
theorem emit_mapping_eq_bracket_intercalate
    (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag anchor : Option String) :
    emit (.mapping style pairs tag anchor)
      = "{" ++ ", ".intercalate (pairs.toList.map (fun p => emit p.1 ++ ": " ++ emit p.2)) ++ "}" := by
  show "{" ++ emit.emitPairList pairs.toList ++ "}"
      = "{" ++ ", ".intercalate (pairs.toList.map (fun p => emit p.1 ++ ": " ++ emit p.2)) ++ "}"
  rw [emitPairList_eq_intercalate]

/-! ### §5.13  Front B — value-recovery trace, brick 3 producer prep: char-list segment peel

§5.12 gave the *string* closed form `emit.emitList l = ", ".intercalate (l.map emit)`. But the
scanner does not consume strings — every scanner predicate in the `EmitListScansInFlow` family
(`ScanChainGrowth.lean:166`) is stated over the **char list** `(emit.emitList items).toList ++ rest`,
and the per-element scan recursion (`emitList_scans_nonempty`, `ScanChainGrowth.lean:203`) peels one
element off the FRONT of that char list at a time: `(emit v).toList ++ [',', ' '] ++ …`. That peel is
currently an *ad-hoc inline* (`ScanChainGrowth.lean:222`, `simp [emit.emitList, String.toList_append,
List.append_assoc]`). This section factors it as a reusable lemma — the `toList`-level bridge from
§5.12's string form to the `toList ++ rest` shape the scanner producer's span-locality recursion
peels.

Two shapes, both pure emission/string facts (no scanner/parser machinery, so they stand in isolation
and cannot perturb the 4-sorry frontier):
* the **single-step head peel** `(emit.emitList (v :: tail)).toList = (emit v).toList ++ [',', ' '] ++
  (emit.emitList tail).toList` (`tail ≠ []`) — the exact step the scanner recursion takes, exposing the
  first element's emission chars as a prefix and the literal `[',', ' ']` separator the comma/space
  scan steps consume; and
* the **whole-stream bracket char form** `(emit (.sequence …)).toList = '[' :: (body.toList ++ [']'])`
  — the framing the producer enters the body scan with (`'['` is the `flowSequenceStart`, the trailing
  `']'` the `flowSequenceEnd`).

This is the LAST emission-only prerequisite: the next sub-link must cross into scanner machinery — the
span-locality identity that each peeled `(emit v).toList` segment scans to the standalone
`scanFiltered (emit v)` token run. Verified-but-unconsumed until that consumes it
([[ref-consumer-joint-before-producer]]). -/

/-- **Char-list head peel (sequence body).** For a non-empty tail, the char list the scanner consumes
    for `emit.emitList (v :: tail)` is the head element's emission chars, the literal `[',', ' ']`
    separator, then the tail body's chars: `(emit.emitList (v :: tail)).toList = (emit v).toList ++
    [',', ' '] ++ (emit.emitList tail).toList`. The single peel step the flow-sequence scan recursion
    takes (`ScanChainGrowth.lean:222`), now reusable. (`tail = []` is excluded — there the separator is
    absent and `emit.emitList [v] = emit v`, the singleton scan base case.) -/
theorem emitList_toList_cons_of_ne_nil (v : YamlValue) (tail : List YamlValue) (h : tail ≠ []) :
    (emit.emitList (v :: tail)).toList
      = (emit v).toList ++ [',', ' '] ++ (emit.emitList tail).toList := by
  cases tail with
  | nil => exact absurd rfl h
  | cons w ws =>
    have hs : emit.emitList (v :: w :: ws) = emit v ++ ", " ++ emit.emitList (w :: ws) := rfl
    rw [hs]
    simp [String.toList_append]

/-- **Char-list head peel (mapping body).** Mirror for key/value entries: for a non-empty tail,
    `(emit.emitPairList ((k, val) :: tail)).toList = (emit k).toList ++ [':', ' '] ++ (emit val).toList
    ++ [',', ' '] ++ (emit.emitPairList tail).toList`. The head ENTRY emits as `emit k ++ ": " ++ emit
    val` (the inner `[':', ' ']` joins key to value), then the `[',', ' ']` entry separator, then the
    tail. The single peel step the flow-mapping scan recursion takes. -/
theorem emitPairList_toList_cons_of_ne_nil
    (k val : YamlValue) (tail : List (YamlValue × YamlValue)) (h : tail ≠ []) :
    (emit.emitPairList ((k, val) :: tail)).toList
      = (emit k).toList ++ [':', ' '] ++ (emit val).toList ++ [',', ' ']
        ++ (emit.emitPairList tail).toList := by
  cases tail with
  | nil => exact absurd rfl h
  | cons q qs =>
    have hs : emit.emitPairList ((k, val) :: q :: qs)
            = emit k ++ ": " ++ emit val ++ ", " ++ emit.emitPairList (q :: qs) := rfl
    rw [hs]
    simp [String.toList_append]

/-- **Whole-stream bracket char form (sequence).** A flow sequence's emitted char list is the
    `flowSequenceStart` char `'['`, then the body chars, then the `flowSequenceEnd` char `']'`:
    `(emit (.sequence …)).toList = '[' :: ((emit.emitList items.toList).toList ++ [']'])`. The framing
    the producer enters the body scan with — `'['` opens the flow level, the trailing `']'` closes it,
    and everything between is the §5.12/§5.13 per-element body. -/
theorem emit_sequence_toList_bracket
    (style : CollectionStyle) (items : Array YamlValue) (tag anchor : Option String) :
    (emit (.sequence style items tag anchor)).toList
      = '[' :: ((emit.emitList items.toList).toList ++ [']']) := by
  show ("[" ++ emit.emitList items.toList ++ "]").toList
      = '[' :: ((emit.emitList items.toList).toList ++ [']'])
  simp [String.toList_append]

/-- **Whole-stream bracket char form (mapping).** Mirror: `(emit (.mapping …)).toList = '{' ::
    ((emit.emitPairList pairs.toList).toList ++ ['}'])`. `'{'` opens the flow level, the trailing `'}'`
    closes it. -/
theorem emit_mapping_toList_bracket
    (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue)) (tag anchor : Option String) :
    (emit (.mapping style pairs tag anchor)).toList
      = '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}']) := by
  show ("{" ++ emit.emitPairList pairs.toList ++ "}").toList
      = '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'])
  simp [String.toList_append]

end L4YAML.Proofs.EmitterScannability
