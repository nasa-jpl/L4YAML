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

end L4YAML.Proofs.EmitterScannability
