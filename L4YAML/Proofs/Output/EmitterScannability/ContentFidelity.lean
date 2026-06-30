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

/-! ### §5.4.1  Front B — value-recovery trace, brick 3 producer prep: `parseNode` scalar dispatch leaf

The §5.4 dispatch family pins the *constructor* a successful `parseNode` produces from its lookahead,
**position-generically** (for ANY `ps`, not just the whole-stream start): `parseNode_flowSeqStart_produces_sequence`
and `parseNode_flowMapStart_produces_mapping` cover the two collection peeks.  The family was missing its
**scalar** member: a `.scalar content style` lookahead was only pinned *inside* the whole-stream
`parseStream_three_tokens_scalar` (`EmitterScannability.lean:186`) — fixed to position `1`, not reusable
mid-stream.

§5.4.1 lands that member.  `parseNode_scalar_produces_scalar` proves a scalar lookahead recovers exactly
`.scalar (Scalar.mk content style none none none)` — by the same skip / dispatch / finalization-is-identity
argument as the collection twins, with two scalar-specific simplifications: content dispatch routes a scalar
peek *directly* to the value (`parseNodeContent`'s first arm), and `applyNodeFinalization` leaves a scalar head
untouched (only `.sequence`/`.mapping … none none` heads get the props rewrite — a scalar takes the `other`
arm), so the empty props (`{}.tag = .anchor = none`) survive verbatim.

This is the **parser-side leaf** of the per-element span-locality the §5.10–§5.14 producer-prep chain builds
toward: when the `parseFlowSequenceLoop` / `parseFlowMappingLoop` induction reaches a *scalar* element span
mid-stream, this lemma pins the recovered value position-generically — the parser half of "`items''[k]` =
standalone parse of `emit items[k]`" for the leaf case, INDEPENDENT of the (harder, cross-state) scanner
segment-equality.  It matches the standalone scalar parse (`parseYamlRaw_emitScalar_value` recovers the same
`.scalar … .doubleQuoted`), so the bridge target holds at the leaf with both halves pinned.  Verified-but-
unconsumed until the loop-locality producer consumes it; position-generic, so it stands in isolation and cannot
perturb the 4-sorry frontier. -/

/-- **`parseNode` dispatch (scalar).** Completing member of the §5.4 dispatch family: a successful
    `parseNode` whose lookahead is `.scalar content style` produces exactly
    `.scalar (Scalar.mk content style none none none)`.  The scalar token is neither alias nor anchor/tag,
    so the alias check skips and `parseNodeProperties` returns empty props; `validateNodeProps` passes (no
    block-collection / duplicate-anchor trigger); content dispatch routes the scalar peek straight to the
    value `{ content, style, tag := props.tag, anchor := props.anchor }`; and `applyNodeFinalization` leaves
    a scalar head untouched (the `other` arm — only flow/block collection heads with `none none` get the
    props rewrite).  Empty props ⇒ `tag = anchor = none`; `blockMeta` defaults `none`.  Position-generic
    (no constraint on `ps.pos`), so it pins the recovered value for a scalar element span anywhere
    mid-stream — the parser-locality leaf the loop-locality producer consumes. -/
theorem parseNode_scalar_produces_scalar (ps : ParseState) (fuel : Nat)
    (content : String) (style : ScalarStyle) (v : YamlValue) (ps' : ParseState)
    (h_peek : ps.peek? = some (.scalar content style))
    (h : parseNode ps fuel = .ok (v, ps')) :
    v = .scalar (Scalar.mk content style none none none) := by
  cases fuel with
  | zero => simp only [parseNode, reduceCtorEq] at h
  | succ n =>
    -- properties skip (a scalar token is neither anchor nor tag)
    have h_np : parseNodeProperties ps = .ok ({}, ps) :=
      parseNodeProperties_skip ps (by rw [h_peek]; trivial)
    -- validation passes for any prePropPos (the block-start / dup-anchor triggers don't fire)
    have h_vnp : ∀ p, validateNodeProps ps p ({} : NodeProperties) = .ok () := by
      intro p; unfold validateNodeProps
      simp only [h_peek, bind, Except.bind, pure, Except.pure]
      rfl
    -- content dispatch routes a scalar peek straight to the scalar value (empty-prop tag/anchor)
    have h_pnc : parseNodeContent ps n ({} : NodeProperties)
        = .ok (YamlValue.scalar { content := content, style := style }, ps.advance) := by
      unfold parseNodeContent; rw [h_peek]
    unfold parseNode at h
    simp only [h_peek, bind, Except.bind, pure, Except.pure, h_np, h_vnp, h_pnc] at h
    -- finalization is identity on a scalar head (the `other` arm); read off the first component
    have h2 := Except.ok.inj h
    have h1 := congrArg Prod.fst h2
    simp only [applyNodeFinalization] at h1
    exact h1.symm

/-- **`parseNode` position advance (scalar, R600).** A successful `parseNode` whose lookahead is
    `.scalar content style` advances position by exactly 1.  The scalar token is neither alias nor
    anchor/tag, so `parseNodeProperties` returns empty props and the SAME parse state (no position
    change); `parseNodeContent` returns `ps.advance` (position +1); and `applyNodeFinalization_pos`
    shows finalization preserves position.  Proof mirrors `parseNode_scalar_produces_scalar` but
    extracts the SECOND pair component.  Position-generic, no constraint on `ps.pos`.  Verified-but-
    unconsumed until the loop-locality position-tracking producer threads it through
    `parseFlowSequenceLoop_push_pointwise` to prove `ps_j.pos = 2 + 2*j`. -/
theorem parseNode_scalar_advances_by_one
    (ps : ParseState) (fuel : Nat)
    (content : String) (style : ScalarStyle) (v : YamlValue) (ps' : ParseState)
    (h_peek : ps.peek? = some (.scalar content style))
    (h_parse : parseNode ps fuel = .ok (v, ps')) :
    ps'.pos = ps.pos + 1 := by
  cases fuel with
  | zero => simp only [parseNode, reduceCtorEq] at h_parse
  | succ n =>
    have h_np : parseNodeProperties ps = .ok ({}, ps) :=
      parseNodeProperties_skip ps (by rw [h_peek]; trivial)
    have h_vnp : ∀ p, validateNodeProps ps p ({} : NodeProperties) = .ok () := by
      intro p; unfold validateNodeProps
      simp only [h_peek, bind, Except.bind, pure, Except.pure]
      rfl
    have h_pnc : parseNodeContent ps n ({} : NodeProperties)
        = .ok (YamlValue.scalar { content := content, style := style }, ps.advance) := by
      unfold parseNodeContent; rw [h_peek]
    unfold parseNode at h_parse
    simp only [h_peek, bind, Except.bind, pure, Except.pure, h_np, h_vnp, h_pnc] at h_parse
    have h2 := Except.ok.inj h_parse
    -- (applyNodeFinalization ...).2 = ps' via the second pair component
    have h_ps'_eq : ps' = (applyNodeFinalization
        (YamlValue.scalar { content := content, style := style }) ps.advance {}
        (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2 :=
      (congrArg Prod.snd h2).symm
    rw [h_ps'_eq, applyNodeFinalization_pos]
    simp [ParseState.advance]

/-- `parseNode` for a scalar lookahead preserves the token array. -/
theorem parseNode_scalar_tokens_preserved (ps : ParseState) (fuel : Nat)
    (content : String) (style : ScalarStyle) (v : YamlValue) (ps' : ParseState)
    (h_peek : ps.peek? = some (.scalar content style))
    (h_parse : parseNode ps fuel = .ok (v, ps')) :
    ps'.tokens = ps.tokens := by
  cases fuel with
  | zero => simp only [parseNode, reduceCtorEq] at h_parse
  | succ n =>
    have h_np : parseNodeProperties ps = .ok ({}, ps) :=
      parseNodeProperties_skip ps (by rw [h_peek]; trivial)
    have h_vnp : ∀ p, validateNodeProps ps p ({} : NodeProperties) = .ok () := by
      intro p; unfold validateNodeProps
      simp only [h_peek, bind, Except.bind, pure, Except.pure]
      rfl
    have h_pnc : parseNodeContent ps n ({} : NodeProperties)
        = .ok (YamlValue.scalar { content := content, style := style }, ps.advance) := by
      unfold parseNodeContent; rw [h_peek]
    unfold parseNode at h_parse
    simp only [h_peek, bind, Except.bind, pure, Except.pure, h_np, h_vnp, h_pnc] at h_parse
    have h2 := Except.ok.inj h_parse
    have h_ps'_eq : ps' = (applyNodeFinalization
        (YamlValue.scalar { content := content, style := style }) ps.advance {}
        (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2 :=
      (congrArg Prod.snd h2).symm
    rw [h_ps'_eq, applyNodeFinalization_tokens]
    simp [ParseState.advance]

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

/-! ### §5.8a  Loop witness for sequence outer-shape recovery (R602)

R602 strengthens `parseStream_flowSeqStart_recovers_outer_shape` by also exposing the specific
`parseFlowSequenceLoop` call (at `pos = 2`, fuel `4·tokens.size+2`) whose result IS `items'`.
This enables R601 to pin per-element values without going through `FlowSubrangesOk` /
`ParseNodeFlowSeqOk` — only the parse-success hypothesis `h_parse` is needed. -/

/-- **Loop witness for outer-shape recovery (sequence), R602.** Exposes the specific
    `parseFlowSequenceLoop` call (tokens preserved, `pos = 2`, fuel `4·tokens.size+2`) whose
    result array IS the first document's value array `items'`. Enables R601 to pin element values
    given only `h_parse : parseStream tokens = .ok raw_docs`. Proved by tracing
    `parseStream_first_doc_at_pos_one` → `prepareDocumentState` → `parseNode` →
    `parseFlowSequence` → `parseFlowSequenceLoop`. -/
theorem parseStream_flowSeqStart_loop_witness
    (tokens : Array (Positioned YamlToken)) (raw_docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok raw_docs)
    (h_ne : 0 < raw_docs.size)
    (h_lt : 1 < tokens.size)
    (h_t1 : tokens[1]!.val = .flowSequenceStart) :
    ∃ (items' : Array YamlValue) (ps_loop ps_doc : ParseState),
      ps_doc.tokens = tokens ∧ ps_doc.pos = 2 ∧
      parseFlowSequenceLoop ps_doc (4 * tokens.size + 2) #[] = .ok (items', ps_loop) ∧
      raw_docs[0]!.value = .sequence .flow items' none none := by
  obtain ⟨ps_1, ps_1', h_tok, h_pos, h_pd⟩ :=
    parseStream_first_doc_at_pos_one tokens raw_docs h_parse h_ne
  let ps_th : ParseState := { ps_1 with tagHandles := #[] }
  have h_th_tok : ps_th.tokens = tokens := by simp [ps_th, h_tok]
  have h_th_pos : ps_th.pos = 1 := by simp [ps_th, h_pos]
  have h_ps1_peek : ps_1.peek? = some .flowSequenceStart := by
    unfold ParseState.peek?; rw [h_pos, h_tok, if_pos h_lt, h_t1]
  have h_th_peek : ps_th.peek? = some .flowSequenceStart := by
    simp only [ps_th]; exact h_ps1_peek
  have h_pd_dir : parseDirectives ps_1 = (#[], ps_1) :=
    parseDirectives_skip ps_1 (by rw [h_ps1_peek]; trivial)
  have h_prep : prepareDocumentState ps_1 = .ok (#[], ({ ps_1 with tagHandles := #[] } : ParseState)) := by
    unfold prepareDocumentState; rw [h_pd_dir]; simp only [Array.filterMap_empty]
    rw [show (ps_th.peek? == some YamlToken.documentStart) = false from by rw [h_th_peek]; decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold ParseState.tryConsume; rw [h_th_peek]
    simp only [show (BEq.beq YamlToken.flowSequenceStart YamlToken.documentStart) = false from by decide,
               Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind]
  -- Fold inline struct back to ps_th so subsequent simp lemmas match syntactically
  have h_fold : ({ ps_1 with tagHandles := #[] } : ParseState) = ps_th := rfl
  unfold parseDocument at h_pd
  simp only [bind, Except.bind, h_prep, h_fold, h_th_peek, h_th_tok] at h_pd
  have h_np : parseNodeProperties ps_th = .ok ({}, ps_th) :=
    parseNodeProperties_skip ps_th (by rw [h_th_peek]; trivial)
  have h_vnp : ∀ p, validateNodeProps ps_th p ({} : NodeProperties) = .ok () := by
    intro p; unfold validateNodeProps; simp [h_th_peek, bind, Except.bind, pure, Except.pure]
  have h_pnc : parseNodeContent ps_th (4 * tokens.size + 3) ({} : NodeProperties) =
      parseFlowSequence ps_th (4 * tokens.size + 3) := by
    unfold parseNodeContent; rw [h_th_peek]
  cases h_pn : parseNode ps_th (4 * tokens.size + 4) with
  | error e => rw [h_pn] at h_pd; simp only [reduceCtorEq] at h_pd
  | ok r_pn =>
    obtain ⟨val_pn, ps_pn⟩ := r_pn
    -- Consume h_pd immediately while h_pn still reads parseNode ... = .ok (val_pn, ps_pn)
    rw [h_pn] at h_pd
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_pd
    obtain ⟨h_doc, -⟩ := h_pd
    -- h_doc : {value := val_pn, ...} = raw_docs[0]!
    -- Now unfold parseNode to learn what val_pn is
    unfold parseNode at h_pn
    simp only [h_th_peek, bind, Except.bind, pure, Except.pure, h_np, h_vnp, h_pnc] at h_pn
    cases h_fs : parseFlowSequence ps_th (4 * tokens.size + 3) with
    | error e => rw [h_fs] at h_pn; simp only [reduceCtorEq] at h_pn
    | ok r_fs =>
      obtain ⟨val_fs, ps_fs⟩ := r_fs
      rw [h_fs] at h_pn
      -- h_pn : applyNodeFinalization val_fs ps_fs {} nodeStartPos = (val_pn, ps_pn)
      simp only [Except.ok.injEq] at h_pn
      -- Unfold parseFlowSequence body to expose the loop call
      simp only [parseFlowSequence, bind, Except.bind] at h_fs
      cases h_loop : parseFlowSequenceLoop ps_th.advance (4 * tokens.size + 2) #[] with
      | error e => rw [h_loop] at h_fs; simp only [reduceCtorEq] at h_fs
      | ok r_loop =>
        obtain ⟨items', ps_loop⟩ := r_loop
        rw [h_loop] at h_fs
        simp only [] at h_fs  -- iota-reduce match .ok (items', ps_loop)
        cases h_fse : ps_loop.peek? with
        | none => rw [h_fse] at h_fs; simp only [reduceCtorEq] at h_fs
        | some tok =>
          cases tok with
          | flowSequenceEnd =>
            rw [h_fse] at h_fs
            simp only [Except.ok.injEq, Prod.mk.injEq] at h_fs
            -- h_fs.1 : .sequence .flow items' = val_fs (i.e. val_fs = .seq .flow items')
            have h_val_pn : val_pn = .sequence .flow items' := by
              have h1 := congrArg Prod.fst h_pn
              simp only [applyNodeFinalization, ← h_fs.1] at h1
              exact h1.symm
            exact ⟨items', ps_loop, ps_th.advance,
              by simp [ps_th, ParseState.advance, h_tok],
              by simp [ps_th, ParseState.advance, h_pos],
              h_loop,
              (congrArg YamlDocument.value h_doc).symm.trans h_val_pn⟩
          | _ => rw [h_fse] at h_fs; simp at h_fs

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

/-! ### §5.10.1  Front B — value-recovery trace, brick 3 link (b) value-half spine: per-element invariant

§5.10 supplied the purely *structural* scaffold (the loop only APPENDS, so `items''.toList = extra`);
its `extra` is existential and carries no information about the elements. Brick 3's content half needs
to characterize each recovered element, so the next loop fact is the **value-half spine**: any property
`P` that holds of the accumulator AND of every value a successful `parseNode` /
`parseSinglePairMapping` produces, holds of every element of the loop result. This is the parametric
loop *invariant* — the parser-side analogue of the block loop's `Scannable`-tracking induction
(`parseBlockSequenceLoop_wb`, `ParserWellBehaved.lean:855`, which carries `Scannable · false` element-
wise through the same shape), here generalized over an arbitrary `P` so the locality producer can
specialize it.

Like §5.10 this is proved by the *same* fuel induction over the loop alone — emission-independent, no
bracket balance, fuel adequacy, or grammability machinery — so it is the **smallest-first** value-half
spine: parametric in `P`, scanner-free. Every branch either returns the accumulator verbatim (`P`
holds by `h_acc`) or recurses on `acc.push w` where `w` is a `parseNode` / `parseSinglePairMapping`
output (`P w` from `h_node` / `h_pair`, lifted over the push by `Array.mem_push`). The
locality producer consumes it by taking `P v := v` is the standalone re-parse of the corresponding
emitted element — but the membership invariant is index-blind, so the producer still owes the
positional bookkeeping (which `parseNode` call recovered element `i`); this lemma discharges the
"every recovered element came from a value-preserving parse" half. Verified-but-unconsumed until that
positional join lands. -/

/-- **Per-element invariant (sequence).** Any `P` closed under the loop's two value-producing branches
    (`parseNode` for plain entries, `parseSinglePairMapping` for the implicit-mapping `.key` branch)
    and holding of the accumulator, holds of every element of a successful `parseFlowSequenceLoop`
    result. Parametric value-half spine; same fuel induction as `parseFlowSequenceLoop_result_append`,
    lifting `P` over each `acc.push w` via `Array.mem_push`. -/
theorem parseFlowSequenceLoop_all (P : YamlValue → Prop)
    (h_node : ∀ ps f v ps', parseNode ps f = .ok (v, ps') → P v)
    (h_pair : ∀ ps f v ps', parseSinglePairMapping ps f = .ok (v, ps') → P v)
    (ps : ParseState) (fuel : Nat) (acc : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_acc : ∀ v ∈ acc, P v)
    (h_ok : parseFlowSequenceLoop ps fuel acc = .ok result) :
    ∀ v ∈ result.1, P v := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    cases h_ok
    exact h_acc
  | succ k ih =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · -- peek = flowSequenceEnd → return acc verbatim
      simp only [Except.ok.injEq] at h_ok; cases h_ok; exact h_acc
    · -- separator ite, then key / end / parseNode dispatch
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try contradiction)
      all_goals (try (simp only [Except.ok.injEq] at h_ok))
      all_goals (first
        | (cases h_ok; exact h_acc)
        | (refine ih _ _ ?_ h_ok
           intro v hv
           rcases Array.mem_push.mp hv with h | h
           · exact h_acc v h
           · subst h
             first
               | exact h_node _ _ _ _ (by assumption)
               | exact h_pair _ _ _ _ (by assumption)))

/-- **Per-element invariant (mapping).** Mirror of `parseFlowSequenceLoop_all`: the loop pushes
    `(key, val)` pairs, the key from `parseNode` (implicit-key branch) or `parseExplicitKey`
    (explicit-`.key` branch) and the value from `parseFlowMappingValue`, so a pair property `P` closed
    under both production paths and holding of the accumulator holds of every recovered pair. -/
theorem parseFlowMappingLoop_all (P : (YamlValue × YamlValue) → Prop)
    (h_implicit : ∀ ps f k ps' ps2 sp kc v ps3,
      parseNode ps f = .ok (k, ps') →
      parseFlowMappingValue ps2 f sp kc = .ok (v, ps3) → P (k, v))
    (h_explicit : ∀ ps f k ps' ps2 sp kc v ps3,
      parseExplicitKey ps f = .ok (k, ps') →
      parseFlowMappingValue ps2 f sp kc = .ok (v, ps3) → P (k, v))
    (ps : ParseState) (fuel : Nat) (acc : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_acc : ∀ v ∈ acc, P v)
    (h_ok : parseFlowMappingLoop ps fuel acc = .ok result) :
    ∀ v ∈ result.1, P v := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    cases h_ok
    exact h_acc
  | succ k ih =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; cases h_ok; exact h_acc
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
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try contradiction)
      all_goals (try (simp only [Except.ok.injEq] at h_ok))
      all_goals (first
        | (cases h_ok; exact h_acc)
        | (refine ih _ _ ?_ h_ok
           intro v hv
           rcases Array.mem_push.mp hv with h | h
           · exact h_acc v h
           · subst h
             first
               | exact h_implicit _ _ _ _ _ _ _ _ _ (by assumption) (by assumption)
               | exact h_explicit _ _ _ _ _ _ _ _ _ (by assumption) (by assumption)))

/-! ### §5.10.2  Front B — value-recovery trace, brick 3 link (b) structural step: one-step loop reduction

§5.10.1 supplied the *value-half spine*: any property `P` closed under the loop's parse branches
and holding of the accumulator holds of every element of the result (membership invariant; index-blind).
The positional join — which parse call recovered element `i` — needs to peel the loop ONE STEP at a time.
This section supplies that step: a successful `parseFlowSequenceLoop ps (fuel+1) acc` either **terminates**
at this step (returning `acc` unchanged, when a terminal token fires or a separator is missing) or
**reduces** to a tail call `parseFlowSequenceLoop ps'' fuel (acc.push v)` for some `v` and successor
state `ps''`.

The provenance of `v` — that it came from `parseNode` (plain entry) or `parseSinglePairMapping`
(implicit-mapping `.key` entry) — is already captured by §5.10.1's `_all` invariant for any `P` closed
under those branches. The step lemma adds the STRUCTURAL complement: the recursive call uses `acc.push v`
as the new accumulator, so `result.1[acc.size] = v` follows by §5.10's `result_append` from the
recursive call's append scaffold. Together the two halves pin element `acc.size` without needing to know
the separator positions or path bookkeeping, which are isolated entirely inside this proof.

Like §5.10–§5.10.1, proved by `unfold` + the `split`-cascade over the `(fuel+1)` branches alone — no
fuel induction, no emission machinery. Seq before map; the mapping mirror uses the same pattern with
`∃ k v`. Verified-but-unconsumed until the positional induction that assembles `∀ i, result.1[i] = extra[i]`
from repeated step applications lands. -/

/-- **One-step loop reduction (sequence).** A successful `parseFlowSequenceLoop ps (fuel+1) acc` either
    terminates returning `acc` unchanged (some terminal token fired or the separator was absent), or
    reduces to the tail call `parseFlowSequenceLoop ps'' fuel (acc.push v)`. The separator-advance and
    path bookkeeping are isolated here; the provenance of `v` (that it came from `parseNode` or
    `parseSinglePairMapping`) follows from §5.10.1's `parseFlowSequenceLoop_all`. The step that the
    positional induction iterates: combined with §5.10's `result_append`, it pins `result.1[acc.size] = v`
    without scanner-side reasoning. -/
theorem parseFlowSequenceLoop_step_push
    (ps : ParseState) (fuel : Nat) (acc : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop ps (fuel+1) acc = .ok result) :
    result.1 = acc ∨
    ∃ v ps'', parseFlowSequenceLoop ps'' fuel (acc.push v) = .ok result := by
  unfold parseFlowSequenceLoop at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp only [Except.ok.injEq] at h_ok; cases h_ok; exact Or.inl rfl
  · all_goals (try (split at h_ok))
    all_goals (try (split at h_ok))
    all_goals (try (split at h_ok))
    all_goals (try (split at h_ok))
    all_goals (try (split at h_ok))
    all_goals (try (split at h_ok))
    all_goals (try (split at h_ok))
    all_goals (try (split at h_ok))
    all_goals (try contradiction)
    all_goals (try (simp only [Except.ok.injEq] at h_ok))
    all_goals (first
      | (cases h_ok; exact Or.inl rfl)
      | (exact Or.inr ⟨_, _, h_ok⟩))

/-- **One-step loop reduction (mapping).** Mirror of `parseFlowSequenceLoop_step_push` for
    `parseFlowMappingLoop`: a successful `(fuel+1)` call either terminates returning `acc`, or reduces
    to `parseFlowMappingLoop ps'' fuel (acc.push (k, v))`. Separator and path bookkeeping isolated here;
    key provenance (`parseNode` vs `parseExplicitKey`) and value provenance (`parseFlowMappingValue`)
    follow from `parseFlowMappingLoop_all`. -/
theorem parseFlowMappingLoop_step_push
    (ps : ParseState) (fuel : Nat) (acc : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop ps (fuel+1) acc = .ok result) :
    result.1 = acc ∨
    ∃ k v ps'', parseFlowMappingLoop ps'' fuel (acc.push (k, v)) = .ok result := by
  unfold parseFlowMappingLoop at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp only [Except.ok.injEq] at h_ok; cases h_ok; exact Or.inl rfl
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
    all_goals (try (split at h_ok))
    all_goals (try (split at h_ok))
    all_goals (try contradiction)
    all_goals (try (simp only [Except.ok.injEq] at h_ok))
    all_goals (first
      | (cases h_ok; exact Or.inl rfl)
      | (exact Or.inr ⟨_, _, _, h_ok⟩))

/-! ### §5.10.3  Front B — value-recovery trace, brick 3 link (b) positional index: `result.1[acc.size] = v`

§5.10.2 supplied the *structural step*: a successful `parseFlowSequenceLoop ps (fuel+1) acc` either
terminates (`result.1 = acc`) or reduces to a tail call `parseFlowSequenceLoop ps'' fuel (acc.push v)`.
This section supplies the **positional index** fact: in the `Or.inr` case, the element at position
`acc.size` in the final result is exactly `v`. This is the per-step positional fact the positional
induction iterates: at each fuel step `acc.size` increases by 1, so repeatedly applying `step_push` +
`step_index` recovers each element at its correct index.

Proof: apply `parseFlowSequenceLoop_result_append` (§5.10) to `h_push` — the tail call has
`(acc.push v)` as accumulator, so `result.1.toList = (acc.push v).toList ++ extra`. Expanding via
`Array.toList_push` and `List.append_assoc` gives `result.1.toList = acc.toList ++ ([v] ++ extra)`.
The index fact goes via `getElem?` (no dependent bound) to avoid a Lean motive issue when rewriting
`result.1.toList` under a dependent `List.getElem` bound: (a) evaluate `result.1.toList[acc.size]?`
using `conv => lhs; rw [he]` + `List.getElem?_append_right` + `List.getElem?_cons_zero` to get
`result.1.toList[acc.size]? = some v`; (b) convert via `List.getElem?_eq_getElem`; (c) lift to
`result.1[acc.size]` via `Array.getElem_toList`. No fuel induction, no emission machinery. Note:
`_h_ok` is the outer call's hypothesis, included for context; only `h_push` is used in the proof.
Verified-but-unconsumed until the fuel induction that iterates `step_push` + `step_index` lands. -/

/-- **Positional index (sequence).** Given `h_push`, the `Or.inr` witness from §5.10.2's
    `parseFlowSequenceLoop_step_push`, the element at position `acc.size` in the final result is `v`.
    Proof: `result_append` on `h_push` gives `result.1.toList = acc.toList ++ [v] ++ extra`; index
    `acc.size` falls in the `[v]` slot, recovered by `List.getElem_append_right`. -/
theorem parseFlowSequenceLoop_step_index
    (ps : ParseState) (fuel : Nat) (acc : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (_h_ok : parseFlowSequenceLoop ps (fuel+1) acc = .ok result)
    (v : YamlValue) (ps'' : ParseState)
    (h_push : parseFlowSequenceLoop ps'' fuel (acc.push v) = .ok result) :
    ∃ h : acc.size < result.1.size, result.1[acc.size]'h = v := by
  obtain ⟨extra, he⟩ := parseFlowSequenceLoop_result_append ps'' fuel (acc.push v) result h_push
  rw [Array.toList_push, List.append_assoc] at he
  have hsize : acc.size < result.1.size := by
    have hlen := congrArg List.length he
    simp only [List.length_append, List.length_cons, List.length_nil, Array.length_toList] at hlen
    omega
  refine ⟨hsize, ?_⟩
  have hsize' : acc.size < result.1.toList.length := by rwa [Array.length_toList]
  -- Use getElem? (no dependent bound) to avoid motive issue when rewriting he
  have hle : acc.toList.length ≤ acc.size := by simp [Array.length_toList]
  have hopt : result.1.toList[acc.size]? = some v := by
    conv => lhs; rw [he]
    rw [List.getElem?_append_right hle]
    simp [Array.length_toList]
  rw [List.getElem?_eq_getElem hsize'] at hopt
  simp only [Option.some.injEq] at hopt
  simpa only [Array.getElem_toList] using hopt

/-- **Positional index (mapping).** Mirror of `parseFlowSequenceLoop_step_index` for
    `parseFlowMappingLoop`: given `h_push`, the element at position `acc.size` is `(k, v)`. -/
theorem parseFlowMappingLoop_step_index
    (ps : ParseState) (fuel : Nat) (acc : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (_h_ok : parseFlowMappingLoop ps (fuel+1) acc = .ok result)
    (k v : YamlValue) (ps'' : ParseState)
    (h_push : parseFlowMappingLoop ps'' fuel (acc.push (k, v)) = .ok result) :
    ∃ h : acc.size < result.1.size, result.1[acc.size]'h = (k, v) := by
  obtain ⟨extra, he⟩ := parseFlowMappingLoop_result_append ps'' fuel (acc.push (k, v)) result h_push
  rw [Array.toList_push, List.append_assoc] at he
  have hsize : acc.size < result.1.size := by
    have hlen := congrArg List.length he
    simp only [List.length_append, List.length_cons, List.length_nil, Array.length_toList] at hlen
    omega
  refine ⟨hsize, ?_⟩
  have hsize' : acc.size < result.1.toList.length := by rwa [Array.length_toList]
  have hle : acc.toList.length ≤ acc.size := by simp [Array.length_toList]
  have hopt : result.1.toList[acc.size]? = some (k, v) := by
    conv => lhs; rw [he]
    rw [List.getElem?_append_right hle]
    simp [Array.length_toList]
  rw [List.getElem?_eq_getElem hsize'] at hopt
  simp only [Option.some.injEq] at hopt
  simpa only [Array.getElem_toList] using hopt

/-! ### §5.18  Front B — loop value pin for all-scalar flow sequences (R601)

`parseFlowSeqLoop_allScalar_value_at` combines the scanner token-array facts (R597: every
scalar slot carries `.scalar sc.content .doubleQuoted` and every separator slot carries
`.flowEntry`) with the parser position tracking to pin EVERY element of the loop result.

Given a token array of the form

  `[fss, body..., fse]`  (size = 2*items.length + 3)
  `tokens[2 + 2*j]! = .scalar sc_j.content .doubleQuoted`
  `tokens[2*j+1]! = .flowEntry` for j > 0

and a parser state pointing at position 2 (after the `flowSequenceStart`), the loop
produces a result satisfying

  `result.1.size = items.length`
  `result.1[j]! = .scalar (Scalar.mk sc_j.content .doubleQuoted none none none)`.

Proof strategy: fuel induction.  Position invariant: at step k the parser is at position
`if k = 0 then 2 else 2*k+1`.
`parseNode_scalar_produces_scalar` pins the value; `parseNode_scalar_advances_by_one` and
`parseNode_scalar_tokens_preserved` track position+tokens for the IH; and
`parseFlowSequenceLoop_step_index` converts the recursive-call witness into the
`result.1[k]! = val` equation. -/

private theorem parseFlowSeqLoop_allScalar_value_at_aux
    {tokens : Array (Positioned YamlToken)}
    {items : List YamlValue}
    (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, ∃ sc : Scalar, v = .scalar sc)
    (h_scalar_tok : ∀ j : Nat, j < items.length → ∀ sc : Scalar, items[j]? = some (.scalar sc) →
        tokens[2 + 2 * j]!.val = .scalar sc.content .doubleQuoted)
    (h_fe_tok : ∀ j : Nat, 0 < j → j < items.length → tokens[2 * j + 1]!.val = .flowEntry)
    (h_fse_tok : tokens[2 * items.length + 1]!.val = .flowSequenceEnd)
    (h_sz : tokens.size = 2 * items.length + 3)
    {k : Nat} (h_kle : k ≤ items.length)
    {acc : Array YamlValue} (h_acc : acc.size = k)
    {ps : ParseState} (h_toks : ps.tokens = tokens)
    (h_pos : ps.pos = if k = 0 then 2 else 2 * k + 1)
    {fuel : Nat} (h_fuel : items.length - k + 1 ≤ fuel)
    {result : Array YamlValue × ParseState}
    (h_ok : parseFlowSequenceLoop ps fuel acc = .ok result) :
    result.1.size = items.length ∧
    ∀ j : Nat, k ≤ j → j < items.length →
        ∃ sc : Scalar, items[j]? = some (.scalar sc) ∧
        result.1[j]! = .scalar (Scalar.mk sc.content .doubleQuoted none none none) := by
  induction fuel generalizing k acc ps with
  | zero => omega
  | succ n ih =>
    have h_ne_len : items.length ≠ 0 := by
      intro h; cases items with
      | nil => exact absurd rfl h_ne
      | cons _ _ => simp at h
    by_cases h_keq : k = items.length
    · -- EXIT: k = items.length, loop sees flowSequenceEnd
      subst h_keq
      have h_pos_val : ps.pos = 2 * items.length + 1 := by
        rw [h_pos, if_neg h_ne_len]
      have h_peek_fse : ps.peek? = some .flowSequenceEnd :=
        peek_of_pos_val h_pos_val (by rw [h_toks, h_sz]; omega)
          (by rw [h_toks]; exact h_fse_tok)
      simp only [parseFlowSequenceLoop, h_peek_fse, Except.ok.injEq] at h_ok
      exact ⟨h_ok ▸ h_acc, fun j _ h_lt => absurd h_lt (by omega)⟩
    · -- STEP: k < items.length
      have h_klt : k < items.length := Nat.lt_of_le_of_ne h_kle h_keq
      obtain ⟨sc_k, h_val_k⟩ := h_all _ (List.getElem_mem h_klt)
      have h_item_k : items[k]? = some (.scalar sc_k) :=
        (List.getElem?_eq_getElem h_klt).trans (congrArg some h_val_k)
      have h_tok_k := h_scalar_tok k h_klt sc_k h_item_k
      have h_ok_orig := h_ok
      by_cases h_k0 : k = 0
      · -- k = 0: ps.pos = 2, peek? = scalar
        subst h_k0
        simp only [ite_true] at h_pos
        have h_peek : ps.peek? = some (.scalar sc_k.content .doubleQuoted) :=
          peek_of_pos_val h_pos (by rw [h_toks, h_sz]; omega)
            (by rw [h_toks]; exact h_tok_k)
        -- struct update of currentPath is transparent to peek?
        have h_path_peek :
            ({ ps with currentPath := ps.currentPath.push (.index acc.size) } : ParseState).peek?
              = some (.scalar sc_k.content .doubleQuoted) := h_peek
        unfold parseFlowSequenceLoop at h_ok
        simp only [bind, Except.bind, pure, Except.pure] at h_ok
        split at h_ok  -- outer: fse vs wildcard
        · simp [h_peek] at *
        · simp only [if_neg (show ¬ (acc.size > 0) from by omega)] at h_ok
          split at h_ok  -- inner: key | fse | wildcard
          · simp [h_peek] at *
          · simp [h_peek] at *
          · split at h_ok  -- parseNode: error | ok
            · simp at h_ok
            · rename_i pair h_pn; obtain ⟨val, ps_node⟩ := pair
              have h_val : val = .scalar (Scalar.mk sc_k.content .doubleQuoted none none none) :=
                parseNode_scalar_produces_scalar _ n sc_k.content .doubleQuoted val ps_node
                  h_path_peek h_pn
              have h_node_pos : ps_node.pos = 3 := by
                have h_ip : ({ ps with currentPath := ps.currentPath.push (.index acc.size) }
                              : ParseState).pos = ps.pos := rfl
                have := parseNode_scalar_advances_by_one _ n sc_k.content .doubleQuoted val ps_node
                  h_path_peek h_pn
                omega
              have h_node_toks : ps_node.tokens = tokens := by
                have h_it : ({ ps with currentPath := ps.currentPath.push (.index acc.size) }
                              : ParseState).tokens = ps.tokens := rfl
                have := parseNode_scalar_tokens_preserved _ n sc_k.content .doubleQuoted val ps_node
                  h_path_peek h_pn
                rw [h_it, h_toks] at this; exact this
              have h_kle1 : 1 ≤ items.length := by omega
              have h_acc1 : (acc.push val).size = 1 := by simp [h_acc]
              have h_pos1 :
                  ({ ps_node with currentPath := ps.currentPath } : ParseState).pos =
                  if 1 = 0 then 2 else 2 * 1 + 1 := by
                simp [h_node_pos]
              have h_fuel1 : items.length - 1 + 1 ≤ n := by omega
              obtain ⟨h_sz_r, h_vals_r⟩ := ih h_kle1 h_acc1
                (show ({ ps_node with currentPath := ps.currentPath } : ParseState).tokens = tokens
                  from h_node_toks)
                h_pos1 h_fuel1 h_ok
              obtain ⟨h_idx_h, h_idx_eq⟩ :=
                parseFlowSequenceLoop_step_index ps n acc result h_ok_orig val
                  { ps_node with currentPath := ps.currentPath } h_ok
              exact ⟨h_sz_r, fun j h_ge h_lt => by
                rcases Nat.eq_or_lt_of_le h_ge with rfl | h_jpos
                · exact ⟨sc_k, h_item_k, by
                    rw [← h_acc, getElem!_pos result.1 acc.size h_idx_h, h_idx_eq, h_val]⟩
                · exact h_vals_r j h_jpos h_lt⟩
      · -- k > 0: ps.pos = 2k+1, peek? = .flowEntry
        have h_kpos : 0 < k := by omega
        simp only [if_neg h_k0] at h_pos
        have h_peek_fe : ps.peek? = some .flowEntry :=
          peek_of_pos_val h_pos (by rw [h_toks, h_sz]; omega)
            (by rw [h_toks]; exact h_fe_tok k h_kpos h_klt)
        have h_adv_pos : ps.advance.pos = 2 + 2 * k := by
          simp only [ParseState.advance, h_pos]; omega
        have h_adv_toks : ps.advance.tokens = tokens := by simp [ParseState.advance, h_toks]
        have h_adv_peek : ps.advance.peek? = some (.scalar sc_k.content .doubleQuoted) :=
          peek_of_pos_val h_adv_pos (by rw [h_adv_toks, h_sz]; omega)
            (by rw [h_adv_toks]; exact h_tok_k)
        have h_adv_path_peek :
            ({ ps.advance with currentPath := ps.currentPath.push (.index acc.size) } : ParseState).peek?
              = some (.scalar sc_k.content .doubleQuoted) := h_adv_peek
        unfold parseFlowSequenceLoop at h_ok
        simp only [bind, Except.bind, pure, Except.pure] at h_ok
        split at h_ok  -- outer: fse vs wildcard
        · simp [h_peek_fe] at *
        · simp only [if_pos (show acc.size > 0 from by rw [h_acc]; exact h_kpos)] at h_ok
          split at h_ok  -- flowEntry match: .flowEntry | wildcard
          · split at h_ok  -- inner (post-advance): key | fse | wildcard
            · simp [h_adv_peek] at *
            · simp [h_adv_peek] at *
            · split at h_ok  -- parseNode: error | ok
              · simp at h_ok
              · rename_i pair h_pn; obtain ⟨val, ps_node⟩ := pair
                have h_val : val = .scalar (Scalar.mk sc_k.content .doubleQuoted none none none) :=
                  parseNode_scalar_produces_scalar _ n sc_k.content .doubleQuoted val ps_node
                    h_adv_path_peek h_pn
                have h_node_pos : ps_node.pos = 2 * (k + 1) + 1 := by
                  have h_ip : ({ ps.advance with currentPath := ps.currentPath.push (.index acc.size) }
                                : ParseState).pos = ps.advance.pos := rfl
                  have := parseNode_scalar_advances_by_one _ n sc_k.content .doubleQuoted val ps_node
                    h_adv_path_peek h_pn
                  omega
                have h_node_toks : ps_node.tokens = tokens := by
                  have h_it : ({ ps.advance with currentPath := ps.currentPath.push (.index acc.size) }
                                : ParseState).tokens = ps.advance.tokens := rfl
                  have := parseNode_scalar_tokens_preserved _ n sc_k.content .doubleQuoted val ps_node
                    h_adv_path_peek h_pn
                  rw [h_it, h_adv_toks] at this; exact this
                have h_kle' : k + 1 ≤ items.length := h_klt
                have h_acc' : (acc.push val).size = k + 1 := by simp [h_acc]
                have h_pos' :
                    ({ ps_node with currentPath := ps.currentPath } : ParseState).pos =
                    if k + 1 = 0 then 2 else 2 * (k + 1) + 1 := by
                  have : ({ ps_node with currentPath := ps.currentPath } : ParseState).pos
                      = ps_node.pos := rfl
                  rw [this, h_node_pos, if_neg (Nat.succ_ne_zero k)]
                have h_fuel' : items.length - (k + 1) + 1 ≤ n := by omega
                obtain ⟨h_sz_r, h_vals_r⟩ := ih h_kle' h_acc'
                  (show ({ ps_node with currentPath := ps.currentPath } : ParseState).tokens = tokens
                    from h_node_toks)
                  h_pos' h_fuel' h_ok
                obtain ⟨h_idx_h, h_idx_eq⟩ :=
                  parseFlowSequenceLoop_step_index ps n acc result h_ok_orig val
                    { ps_node with currentPath := ps.currentPath } h_ok
                exact ⟨h_sz_r, fun j h_ge h_lt => by
                  rcases Nat.eq_or_lt_of_le h_ge with rfl | h_jgt
                  · exact ⟨sc_k, h_item_k, by
                      rw [← h_acc, getElem!_pos result.1 acc.size h_idx_h, h_idx_eq, h_val]⟩
                  · exact h_vals_r j h_jgt h_lt⟩
          · simp [h_peek_fe] at *

/-- **Loop value pin for all-scalar flow sequences (R601).**  Given a token array whose
    scalar slots satisfy `tokens[2 + 2*j]! = .scalar sc_j.content .doubleQuoted` and whose
    separator slots satisfy `tokens[2*j+1]! = .flowEntry` (j > 0), together with
    `tokens[2*items.length+1]! = .flowSequenceEnd`, a `parseFlowSequenceLoop` call starting
    at position 2 with empty accumulator produces a result whose size equals `items.length`
    and whose j-th element is `.scalar (Scalar.mk sc_j.content .doubleQuoted none none none)`.
    Verified-but-unconsumed until threaded into the Front-B sequence locality sorry. -/
theorem parseFlowSeqLoop_allScalar_value_at
    {tokens : Array (Positioned YamlToken)}
    {items : List YamlValue}
    (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, ∃ sc : Scalar, v = .scalar sc)
    (h_scalar_tok : ∀ j : Nat, j < items.length → ∀ sc : Scalar, items[j]? = some (.scalar sc) →
        tokens[2 + 2 * j]!.val = .scalar sc.content .doubleQuoted)
    (h_fe_tok : ∀ j : Nat, 0 < j → j < items.length → tokens[2 * j + 1]!.val = .flowEntry)
    (h_fse_tok : tokens[2 * items.length + 1]!.val = .flowSequenceEnd)
    (h_sz : tokens.size = 2 * items.length + 3)
    {ps : ParseState} (h_toks : ps.tokens = tokens) (h_pos : ps.pos = 2)
    {fuel : Nat} (h_fuel : items.length + 1 ≤ fuel)
    {result : Array YamlValue × ParseState}
    (h_ok : parseFlowSequenceLoop ps fuel #[] = .ok result) :
    result.1.size = items.length ∧
    ∀ j : Nat, j < items.length →
        ∃ sc : Scalar, items[j]? = some (.scalar sc) ∧
        result.1[j]! = .scalar (Scalar.mk sc.content .doubleQuoted none none none) := by
  obtain ⟨h_size, h_vals⟩ := parseFlowSeqLoop_allScalar_value_at_aux h_ne h_all h_scalar_tok
    h_fe_tok h_fse_tok h_sz (Nat.zero_le _) (by simp) h_toks
    (by simp only [ite_true, h_pos]) (by omega) h_ok
  exact ⟨h_size, fun j h_lt => h_vals j (Nat.zero_le j) h_lt⟩

/-! ### §5.10.4  Front B — value-recovery trace, brick 3 link (b) indexed sub-call witnesses

§5.10.3 supplied the *per-step positional index*: given `h_push`, `result.1[acc.size] = v`. This
section supplies the **fuel-induction step** — iterating `step_push` + `step_index` to extract, for
EVERY index `j ≥ acc.size` in `result.1`, a sub-loop call whose accumulator covers exactly
`result.1[:j+1]`.

Two sub-theorems per variant:
* `parseFlowSequenceLoop_pushcount_le_fuel` — `result.1.size ≤ acc.size + fuel`: the loop pushes at
  most `fuel` elements. Proved by fuel induction + `step_push`: each `Or.inr` push step decrements
  `fuel` by 1; `Or.inl` or base pushes nothing.
* `parseFlowSequenceLoop_push_subwit` — for each `j` with `acc.size ≤ j < result.1.size`, there
  exist a sub-call witness `(ps_j, acc_j)` with `parseFlowSequenceLoop ps_j (fuel - (j - acc.size) - 1)
  acc_j = .ok result` and `acc_j.toList = result.1.toList.take (j + 1)` (the accumulator IS the first
  `j+1` elements of the final result). Proved by fuel induction + `step_push` + `step_index`:
  - `Or.inl` (`result.1 = acc`): no `j ≥ acc.size` in `[acc.size, result.1.size)`.
  - `Or.inr` (`v, ps'', h_push`):
    - `j = acc.size`: witness `(ps'', acc.push v)`. The accumulator content follows from
      `result_append` on `h_push` + `List.take_append` (with `n = (acc.push v).toList.length`,
      `(l₁ ++ l₂).take l₁.length = l₁.take l₁.length = l₁`). Fuel: `(k+1) - 0 - 1 = k`. ✓
    - `j > acc.size`: IH on `(ps'', k, acc.push v)`, then `convert ... using 2; omega` for
      fuel arithmetic (`(k+1) - (j - acc.size) - 1 = k - (j - (acc.size + 1)) - 1`).

The mapping mirror replaces `(k, v)` pairs and uses `parseFlowMappingLoop_step_push` + `_step_index`.

Verified-but-unconsumed until the scanner-span-locality bridge (§5.14) connects `ps_j.tokens[ps_j.pos]`
to the i-th flow-entry segment of `scanFiltered (emit (.sequence ...))`, supplying the bridge between
the sub-call's parse state and the emitted span of `items[j]`. -/

/-- **Push count ≤ fuel (sequence).** The loop pushes at most `fuel` elements:
    `result.1.size ≤ acc.size + fuel`. Proved by fuel induction + `step_push`. -/
theorem parseFlowSequenceLoop_pushcount_le_fuel
    (ps : ParseState) (fuel : Nat) (acc : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop ps fuel acc = .ok result) :
    result.1.size ≤ acc.size + fuel := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; cases h_ok; simp
  | succ k ih =>
    rcases parseFlowSequenceLoop_step_push ps k acc result h_ok with h_term | ⟨v, ps'', h_push⟩
    · rw [h_term]; omega
    · have h := ih ps'' (acc.push v) h_push
      simp only [Array.size_push] at h; omega

/-- **Push count ≤ fuel (mapping).** Mirror of `parseFlowSequenceLoop_pushcount_le_fuel`:
    `result.1.size ≤ acc.size + fuel` for `parseFlowMappingLoop`. -/
theorem parseFlowMappingLoop_pushcount_le_fuel
    (ps : ParseState) (fuel : Nat) (acc : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop ps fuel acc = .ok result) :
    result.1.size ≤ acc.size + fuel := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; cases h_ok; simp
  | succ k ih =>
    rcases parseFlowMappingLoop_step_push ps k acc result h_ok with h_term | ⟨kv, v, ps'', h_push⟩
    · rw [h_term]; omega
    · have h := ih ps'' (acc.push (kv, v)) h_push
      simp only [Array.size_push] at h; omega

/-- **Indexed sub-call witness (sequence).** For each `j` with `acc.size ≤ j < result.1.size`,
    there exist `ps_j` and `acc_j` such that `parseFlowSequenceLoop ps_j (fuel - (j - acc.size) - 1)
    acc_j = .ok result` and `acc_j.toList = result.1.toList.take (j + 1)`. The accumulator `acc_j`
    is exactly the first `j+1` elements of the final result — the sub-call that produced element `j`.
    Proved by fuel induction + `step_push`: `j = acc.size` uses `acc.push v` as witness (content from
    `result_append` + `List.take_append`); `j > acc.size` recurses on the `acc.push v` sub-call. -/
theorem parseFlowSequenceLoop_push_subwit
    (ps : ParseState) (fuel : Nat) (acc : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop ps fuel acc = .ok result) :
    ∀ j : Nat, acc.size ≤ j → j < result.1.size →
      ∃ (ps_j : ParseState) (acc_j : Array YamlValue),
        parseFlowSequenceLoop ps_j (fuel - (j - acc.size) - 1) acc_j = .ok result ∧
        acc_j.toList = result.1.toList.take (j + 1) := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; cases h_ok
    intro j _ h; simp only [] at h; omega
  | succ k ih =>
    intro j hj_ge hj_lt
    rcases parseFlowSequenceLoop_step_push ps k acc result h_ok with h_term | ⟨v, ps'', h_push⟩
    · rw [h_term] at hj_lt; omega
    · by_cases hj_eq : j = acc.size
      · -- j = acc.size: witness is (ps'', acc.push v)
        subst hj_eq
        obtain ⟨extra, he⟩ := parseFlowSequenceLoop_result_append ps'' k (acc.push v) result h_push
        have hlen : (acc.push v).toList.length = acc.size + 1 := by
          simp only [Array.toList_push, List.length_append, List.length_singleton, Array.length_toList]
        refine ⟨ps'', acc.push v, ?_, ?_⟩
        · -- fuel: (k+1) - (acc.size - acc.size) - 1 = k
          have hfuel : k + 1 - (acc.size - acc.size) - 1 = k := by omega
          rw [hfuel]; exact h_push
        · -- acc_j.toList = result.1.toList.take (acc.size + 1)
          rw [he, ← hlen]; exact List.take_left.symm
      · -- j > acc.size: IH on h_push with acc := acc.push v
        have hj_gt : acc.size < j := Nat.lt_of_le_of_ne hj_ge (Ne.symm hj_eq)
        have hj_ge' : (acc.push v).size ≤ j := by simp only [Array.size_push]; omega
        obtain ⟨ps_j, acc_j, h_sub, h_tl⟩ := ih ps'' (acc.push v) h_push j hj_ge' hj_lt
        refine ⟨ps_j, acc_j, ?_, h_tl⟩
        have hfuel' : k + 1 - (j - acc.size) - 1 = k - (j - (acc.push v).size) - 1 := by
          simp only [Array.size_push]; omega
        rw [hfuel']; exact h_sub

/-- **Indexed sub-call witness (mapping).** Mirror of `parseFlowSequenceLoop_push_subwit` for
    `parseFlowMappingLoop`: for each `j` with `acc.size ≤ j < result.1.size`, there exist `ps_j`
    and `acc_j` with `parseFlowMappingLoop ps_j (fuel - (j - acc.size) - 1) acc_j = .ok result`
    and `acc_j.toList = result.1.toList.take (j + 1)`. Same fuel induction structure with pairs. -/
theorem parseFlowMappingLoop_push_subwit
    (ps : ParseState) (fuel : Nat) (acc : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop ps fuel acc = .ok result) :
    ∀ j : Nat, acc.size ≤ j → j < result.1.size →
      ∃ (ps_j : ParseState) (acc_j : Array (YamlValue × YamlValue)),
        parseFlowMappingLoop ps_j (fuel - (j - acc.size) - 1) acc_j = .ok result ∧
        acc_j.toList = result.1.toList.take (j + 1) := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; cases h_ok
    intro j _ h; simp only [] at h; omega
  | succ k ih =>
    intro j hj_ge hj_lt
    rcases parseFlowMappingLoop_step_push ps k acc result h_ok with h_term | ⟨kv, v, ps'', h_push⟩
    · rw [h_term] at hj_lt; omega
    · by_cases hj_eq : j = acc.size
      · -- j = acc.size: witness is (ps'', acc.push (kv, v))
        subst hj_eq
        obtain ⟨extra, he⟩ :=
          parseFlowMappingLoop_result_append ps'' k (acc.push (kv, v)) result h_push
        have hlen : (acc.push (kv, v)).toList.length = acc.size + 1 := by
          simp only [Array.toList_push, List.length_append, List.length_singleton, Array.length_toList]
        refine ⟨ps'', acc.push (kv, v), ?_, ?_⟩
        · have hfuel : k + 1 - (acc.size - acc.size) - 1 = k := by omega
          rw [hfuel]; exact h_push
        · rw [he, ← hlen]; exact List.take_left.symm
      · -- j > acc.size: IH on h_push
        have hj_gt : acc.size < j := Nat.lt_of_le_of_ne hj_ge (Ne.symm hj_eq)
        have hj_ge' : (acc.push (kv, v)).size ≤ j := by simp only [Array.size_push]; omega
        obtain ⟨ps_j, acc_j, h_sub, h_tl⟩ := ih ps'' (acc.push (kv, v)) h_push j hj_ge' hj_lt
        refine ⟨ps_j, acc_j, ?_, h_tl⟩
        have hfuel' : k + 1 - (j - acc.size) - 1 = k - (j - (acc.push (kv, v)).size) - 1 := by
          simp only [Array.size_push]; omega
        rw [hfuel']; exact h_sub

/-! ### §5.10.5  Front B — value-recovery trace, brick 3 link (b) element-value join: `result.1[j]! = v`

§5.10.4 supplied the indexed sub-call witness: for each `j ≥ acc.size` in `[acc.size, result.1.size)`,
a sub-call `(ps_j, acc_j)` with `acc_j.toList = result.1.toList.take (j+1)` -- the accumulator IS the
first `j+1` elements of the final result. This section supplies the **element-value join**: the value `v`
that was pushed at step `j`, together with explicit pre- and post-push sub-calls that bracket the push.

Two theorem pairs (seq + map):
* `parseFlowSequenceLoop_push_pointwise` -- for each `j` in `[acc.size, result.1.size)`, there exist
  `ps_j ps_j' : ParseState`, `fuel_j : Nat`, `v : YamlValue`, `acc_j : Array YamlValue` such that:
  - `acc_j.toList = result.1.toList.take j`  (acc_j covers elements 0..j-1; NOT element j itself)
  - `parseFlowSequenceLoop ps_j (fuel_j+1) acc_j = .ok result`  (outer call: parse state before element j)
  - `parseFlowSequenceLoop ps_j' fuel_j (acc_j.push v) = .ok result`  (push call: v lands at index j)
  - `result.1[j]! = v`  (element at position j is the pushed value; `!` avoids a dependent bound proof)

Proof: `induction fuel generalizing ps acc`.
- `j = acc.size` base: `step_index` on `(h_ok, step_push(h_ok))` gives `result.1[acc.size] = v`;
  `result_append` + `List.take_left` gives `acc_j = acc` (i.e., `acc.toList = result.1.toList.take acc.size`).
- `j > acc.size`: IH on `(ps'', k, acc.push v)` at `j` forwards the witness unchanged.

The Note on §5.10.4's off-by-one: `push_subwit` at `j` gives `acc_j` with `acc_j.size = j+1` (NOT `j`),
so applying `step_index` to THAT sub-call gives `result.1[j+1] = v`, not `result.1[j]`. The correct combine
for `result.1[j]` uses `push_subwit(j-1)` (giving `acc_{j-1}.size = j`) then `step_push + step_index`. This
theorem re-derives the same structure by direct fuel induction, avoiding the two-step indirection.

`by_cases` on `j = acc.size` introduces `Classical.choice` (same as `push_subwit`). The `!`-indexed
conclusion avoids a dependent existential; the caller converts via `getElem!_pos` when a bound is needed.
Verified-but-unconsumed until §5.14's scanner-span-locality bridge connects `ps_j` to `emit items[j]`. -/

/-- **Element-value join (sequence).** For each `j` in `[acc.size, result.1.size)`, a bracketing triple
    `(ps_j, acc_j, ps_j')` witnesses the push of `v` at position `j`: `ps_j` is the outer call
    (fuel `fuel_j+1`, accumulator covering `j` elements), `ps_j'` is the push tail call (fuel `fuel_j`,
    accumulator `acc_j.push v`), and `result.1[j]! = v`.  `acc_j.toList = result.1.toList.take j` pins
    the accumulator content.  Proof: fuel induction; `j = acc.size` uses `step_index`; `j > acc.size`
    uses the IH on `(ps'', k, acc.push v)`. -/
theorem parseFlowSequenceLoop_push_pointwise
    (ps : ParseState) (fuel : Nat) (acc : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop ps fuel acc = .ok result) :
    ∀ j : Nat, acc.size ≤ j → j < result.1.size →
      ∃ (ps_j ps_j' : ParseState) (fuel_j : Nat) (v : YamlValue) (acc_j : Array YamlValue),
        acc_j.toList = result.1.toList.take j ∧
        parseFlowSequenceLoop ps_j (fuel_j + 1) acc_j = .ok result ∧
        parseFlowSequenceLoop ps_j' fuel_j (acc_j.push v) = .ok result ∧
        result.1[j]! = v := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; cases h_ok
    intro j _ h; simp only [] at h; omega
  | succ k ih =>
    intro j hj_ge hj_lt
    rcases parseFlowSequenceLoop_step_push ps k acc result h_ok with h_term | ⟨v, ps'', h_push⟩
    · rw [h_term] at hj_lt; omega
    · by_cases hj_eq : j = acc.size
      · subst hj_eq
        obtain ⟨h_idx, h_val⟩ :=
          parseFlowSequenceLoop_step_index ps k acc result h_ok v ps'' h_push
        obtain ⟨extra, he⟩ :=
          parseFlowSequenceLoop_result_append ps'' k (acc.push v) result h_push
        have h_take : acc.toList = result.1.toList.take acc.size := by
          rw [he, Array.toList_push, List.append_assoc, ← Array.length_toList]
          exact List.take_left.symm
        refine ⟨ps, ps'', k, v, acc, h_take, h_ok, h_push, ?_⟩
        rw [getElem!_pos result.1 acc.size h_idx]; exact h_val
      · have hj_gt : acc.size < j := Nat.lt_of_le_of_ne hj_ge (Ne.symm hj_eq)
        have hj_ge' : (acc.push v).size ≤ j := by simp only [Array.size_push]; omega
        obtain ⟨ps_j, ps_j', fuel_j, v', acc_j, h_take, h_outer, h_inner, h_eq⟩ :=
          ih ps'' (acc.push v) h_push j hj_ge' hj_lt
        exact ⟨ps_j, ps_j', fuel_j, v', acc_j, h_take, h_outer, h_inner, h_eq⟩

/-- **Element-value join (mapping).** Mirror of `parseFlowSequenceLoop_push_pointwise` for
    `parseFlowMappingLoop`: for each `j` in `[acc.size, result.1.size)`, the pair `(mkey, mval)` pushed
    at position `j`, with `acc_j.toList = result.1.toList.take j`, explicit pre/post-push sub-calls, and
    `result.1[j]! = (mkey, mval)`.  Same fuel-induction structure with pairs. -/
theorem parseFlowMappingLoop_push_pointwise
    (ps : ParseState) (fuel : Nat) (acc : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop ps fuel acc = .ok result) :
    ∀ j : Nat, acc.size ≤ j → j < result.1.size →
      ∃ (ps_j ps_j' : ParseState) (fuel_j : Nat) (mkey mval : YamlValue)
        (acc_j : Array (YamlValue × YamlValue)),
        acc_j.toList = result.1.toList.take j ∧
        parseFlowMappingLoop ps_j (fuel_j + 1) acc_j = .ok result ∧
        parseFlowMappingLoop ps_j' fuel_j (acc_j.push (mkey, mval)) = .ok result ∧
        result.1[j]! = (mkey, mval) := by
  induction fuel generalizing ps acc with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; cases h_ok
    intro j _ h; simp only [] at h; omega
  | succ k ih =>
    intro j hj_ge hj_lt
    rcases parseFlowMappingLoop_step_push ps k acc result h_ok with h_term | ⟨mk, mv, ps'', h_push⟩
    · rw [h_term] at hj_lt; omega
    · by_cases hj_eq : j = acc.size
      · subst hj_eq
        obtain ⟨h_idx, h_val⟩ :=
          parseFlowMappingLoop_step_index ps k acc result h_ok mk mv ps'' h_push
        obtain ⟨extra, he⟩ :=
          parseFlowMappingLoop_result_append ps'' k (acc.push (mk, mv)) result h_push
        have h_take : acc.toList = result.1.toList.take acc.size := by
          rw [he, Array.toList_push, List.append_assoc, ← Array.length_toList]
          exact List.take_left.symm
        refine ⟨ps, ps'', k, mk, mv, acc, h_take, h_ok, h_push, ?_⟩
        rw [getElem!_pos result.1 acc.size h_idx]; exact h_val
      · have hj_gt : acc.size < j := Nat.lt_of_le_of_ne hj_ge (Ne.symm hj_eq)
        have hj_ge' : (acc.push (mk, mv)).size ≤ j := by simp only [Array.size_push]; omega
        obtain ⟨ps_j, ps_j', fuel_j, mk', mv', acc_j, h_take, h_outer, h_inner, h_eq⟩ :=
          ih ps'' (acc.push (mk, mv)) h_push j hj_ge' hj_lt
        exact ⟨ps_j, ps_j', fuel_j, mk', mv', acc_j, h_take, h_outer, h_inner, h_eq⟩

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
span-locality identity relating each peeled `(emit v).toList` segment to the standalone
`scanFiltered (emit v)` token run.  §5.14 takes that first scanner step and lands its first
*correction*: the in-stream segment is NOT literally `scanFiltered (emit v)` (which carries the
`.streamStart`/`.streamEnd` stream markers a mid-stream segment cannot), but its marker-stripped
*core*.  Verified-but-unconsumed until that consumes it ([[ref-consumer-joint-before-producer]]). -/

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

/-! ### §5.14  Front B — value-recovery trace, brick 3 producer prep: standalone-scan stream framing

§5.13 ended the emission-only prerequisites; the span-locality producer's next sub-link crosses into
scanner machinery.  R583's stated target was that each in-stream `(emit v).toList` segment scans to
"the standalone `scanFiltered (emit v)` token run".  Before producing anything against that target,
the inhabitation-debt discipline ([[ref-probe-deferred-universal-before-producing]]) demands checking
it is even TRUE — and an `#eval` probe of the real token stream shows it is **literally false**:

  `scanFiltered (emit (.scalar {content := "a", ..}))` vals = `[.streamStart, .scalar "a" .., .streamEnd]`
  in-stream segment for that same element = `[.scalar "a" ..]`   (NO stream markers)

`scan` opens every run with `.streamStart` and closes it with `.streamEnd` (`scanLoop`), and BOTH pass
the `.placeholder` filter, so a *standalone* `scanFiltered` is bracketed by stream markers that a
*mid-stream* segment can never carry.  The true producer contract is therefore "segment = the
**marker-stripped core** of `scanFiltered (emit v)`", not the whole token run.  This section lands that
correction as the stream-marker framing of any successful `scanFiltered`:

* `scanFiltered_first_is_streamStart` / `scanFiltered_last_is_streamEnd` — the first/last filtered
  token is `.streamStart`/`.streamEnd` (the filter keeps both; lifted from `scan_first_is_streamStart`
  / `scan_last_is_streamEnd` through `Array.filter`'s order-preservation via the `List.filter`
  head/last surgery `filter_cons_of_pos` / `filter_reverse`); and
* `scanFiltered_stream_framing` / `scanFiltered_vals_stream_framing` — the decomposition
  `ft.toList = t0 :: (core ++ [tlast])` (resp. its `.val`-map `.streamStart :: coreVals ++ [.streamEnd]`)
  exposing the marker-free `core`/`coreVals` the eventual segment-equality targets.

Emission-independent (stated for ANY input whose `scanFiltered` succeeds with `≥ 2` tokens — the caller
discharges that for `emit v`), so it stands in isolation and cannot perturb the 4-sorry frontier.
Verified-but-unconsumed until the segment-equality producer consumes it. -/

/-- **List head/middle/last split.** Any list of length `≥ 2` decomposes as `a :: (core ++ [b])` — a
    distinct head `a`, middle `core`, and last `b`.  Pure structural fact (`dropLast_concat_getLast`);
    the shape the stream framing hangs the `.streamStart` head and `.streamEnd` last on. -/
theorem list_split_head_mid_last {α : Type _} (L : List α) (h : 2 ≤ L.length) :
    ∃ a core b, L = a :: (core ++ [b]) := by
  cases L with
  | nil => simp at h
  | cons a t =>
    have ht : t ≠ [] := by intro hc; rw [hc] at h; simp at h
    exact ⟨a, t.dropLast, t.getLast ht, by rw [List.dropLast_concat_getLast ht]⟩

/-- **First filtered token is `.streamStart`.** For any input whose `scanFiltered` succeeds with a
    non-empty token array, the first token is `.streamStart`.  Lifted from `scan_first_is_streamStart`
    (the raw `scan`'s `tokens[0]`) through the `.placeholder` filter: `.streamStart` passes the filter,
    and `Array.filter` preserves order, so the raw head survives as the filtered head
    (`List.filter_cons_of_pos`). -/
theorem scanFiltered_first_is_streamStart (input : String) (ft : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ft) (h_size : ft.size > 0) :
    (ft[0]'h_size).val = YamlToken.streamStart := by
  unfold scanFiltered at h
  split at h
  · rename_i raw h_scan
    have h_ft : ft = raw.filter (fun t => t.val != .placeholder) := (Except.ok.inj h).symm
    have h_le : ft.size ≤ raw.size := by rw [h_ft]; exact Array.size_filter_le
    have h_raw_pos : raw.size > 0 := by omega
    have h_ss : (raw[0]'h_raw_pos).val = YamlToken.streamStart :=
      ScannerCorrectness.scan_first_is_streamStart input raw h_scan h_raw_pos
    have h_p0 : (fun t : Positioned YamlToken => t.val != .placeholder) (raw[0]'h_raw_pos) = true := by
      simp only [h_ss]; rfl
    have h_tl_len : raw.toList.length = raw.size := Array.length_toList
    obtain ⟨x, xs, hx⟩ : ∃ x xs, raw.toList = x :: xs := by
      match hl : raw.toList with
      | [] => rw [hl] at h_tl_len; simp only [List.length_nil] at h_tl_len; omega
      | x :: xs => exact ⟨x, xs, rfl⟩
    have hx0 : x = raw[0]'h_raw_pos := by
      have e1 : raw.toList[0]? = some x := by rw [hx]; rfl
      have e2 : raw.toList[0]? = some (raw[0]'h_raw_pos) := by
        rw [List.getElem?_eq_getElem (by rw [h_tl_len]; exact h_raw_pos),
            Array.getElem_toList h_raw_pos]
      rw [e1] at e2; exact (Option.some.inj e2)
    have h_ft_tl : ft.toList = raw.toList.filter (fun t => t.val != .placeholder) := by
      rw [h_ft, Array.toList_filter]
    rw [hx, List.filter_cons_of_pos (hx0 ▸ h_p0)] at h_ft_tl
    have h_ft0 : ft[0]'h_size = x := by
      have e : ft.toList[0]? = some (ft[0]'h_size) := by
        rw [List.getElem?_eq_getElem (by rw [Array.length_toList]; exact h_size),
            Array.getElem_toList h_size]
      rw [h_ft_tl] at e; simp only [List.getElem?_cons_zero] at e
      exact (Option.some.inj e).symm
    rw [h_ft0, hx0, h_ss]
  · exact absurd h (by simp)

/-- **Last filtered token is `.streamEnd`.** Mirror of `scanFiltered_first_is_streamStart` for the
    array's end: lifted from `scan_last_is_streamEnd` through the filter via the `List.filter_reverse`
    + `filter_cons_of_pos` surgery (the raw last token `.streamEnd` passes the filter and stays last,
    since reversing-then-filtering keeps the head). -/
theorem scanFiltered_last_is_streamEnd (input : String) (ft : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ft) (h_size : ft.size > 0) :
    (ft[ft.size - 1]'(by omega)).val = YamlToken.streamEnd := by
  unfold scanFiltered at h
  split at h
  · rename_i raw h_scan
    have h_ft : ft = raw.filter (fun t => t.val != .placeholder) := (Except.ok.inj h).symm
    have h_le : ft.size ≤ raw.size := by rw [h_ft]; exact Array.size_filter_le
    have h_raw_pos : raw.size > 0 := by omega
    have h_se : (raw[raw.size - 1]'(by omega)).val = YamlToken.streamEnd :=
      ScannerCorrectness.scan_last_is_streamEnd input raw h_scan h_raw_pos
    have h_tl_len : raw.toList.length = raw.size := Array.length_toList
    have h_ftl : ft.toList.length = ft.size := Array.length_toList
    have h_ft_tl : ft.toList = raw.toList.filter (fun t => t.val != .placeholder) := by
      rw [h_ft, Array.toList_filter]
    have h_last_raw : raw.toList.getLast? = some (raw[raw.size - 1]'(by omega)) := by
      rw [List.getLast?_eq_getElem?, h_tl_len,
          List.getElem?_eq_getElem (by omega), Array.getElem_toList]
    have h_rev_ne : raw.toList.reverse ≠ [] := by
      intro hc
      have hl := List.length_reverse (as := raw.toList)
      rw [hc, List.length_nil, h_tl_len] at hl; omega
    obtain ⟨z, zs, hz⟩ : ∃ z zs, raw.toList.reverse = z :: zs := by
      match hl : raw.toList.reverse with
      | [] => exact absurd hl h_rev_ne
      | z :: zs => exact ⟨z, zs, rfl⟩
    have hz_eq : z = raw[raw.size - 1]'(by omega) := by
      have e : raw.toList.reverse.head? = some z := by rw [hz]; rfl
      rw [List.head?_reverse, h_last_raw] at e
      exact (Option.some.inj e).symm
    have h_pz' : (fun t : Positioned YamlToken => t.val != .placeholder) z = true := by
      rw [hz_eq]; simp only [h_se]; rfl
    have h_filter_rev :
        raw.toList.reverse.filter (fun t => t.val != .placeholder)
          = z :: zs.filter (fun t => t.val != .placeholder) := by
      rw [hz]; exact List.filter_cons_of_pos h_pz'
    have h_ft_getlast : ft.toList.getLast? = some z := by
      rw [h_ft_tl, ← List.head?_reverse, ← List.filter_reverse, h_filter_rev]; rfl
    have h_ftlast : ft[ft.size - 1]'(by omega) = z := by
      have e : ft.toList.getLast? = some (ft[ft.size - 1]'(by omega)) := by
        rw [List.getLast?_eq_getElem?, Array.length_toList,
            List.getElem?_eq_getElem (by omega), Array.getElem_toList]
      rw [h_ft_getlast] at e
      exact (Option.some.inj e).symm
    rw [h_ftlast, hz_eq, h_se]
  · exact absurd h (by simp)

/-- **Stream-marker framing (token level).** Any successful `scanFiltered` with `≥ 2` tokens decomposes
    as `t0 :: (core ++ [tlast])` where `t0.val = .streamStart` and `tlast.val = .streamEnd` — the
    stream markers bracket a marker-free `core`.  The producer's CORRECTED contract: an in-stream
    segment equals `core`, never the whole `scanFiltered (emit v)`.  Assembled from the head/last
    framing and the structural `list_split_head_mid_last`. -/
theorem scanFiltered_stream_framing (input : String) (ft : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ft) (h_size : 2 ≤ ft.size) :
    ∃ (t0 tlast : Positioned YamlToken) (core : List (Positioned YamlToken)),
      ft.toList = t0 :: (core ++ [tlast])
      ∧ t0.val = YamlToken.streamStart ∧ tlast.val = YamlToken.streamEnd := by
  have h_pos : ft.size > 0 := by omega
  have h_ftl : ft.toList.length = ft.size := Array.length_toList
  have h_first := scanFiltered_first_is_streamStart input ft h h_pos
  have h_last := scanFiltered_last_is_streamEnd input ft h h_pos
  obtain ⟨t0, core, tlast, hdec⟩ :=
    list_split_head_mid_last ft.toList (by rw [Array.length_toList]; omega)
  refine ⟨t0, tlast, core, hdec, ?_, ?_⟩
  · have ht0_eq : ft[0]'h_pos = t0 := by
      have e : ft.toList[0]? = some (ft[0]'h_pos) := by
        rw [List.getElem?_eq_getElem (by rw [Array.length_toList]; exact h_pos),
            Array.getElem_toList]
      rw [hdec] at e; simp only [List.getElem?_cons_zero] at e
      exact (Option.some.inj e).symm
    rw [← ht0_eq]; exact h_first
  · have htlast_eq : ft[ft.size - 1]'(by omega) = tlast := by
      have e : ft.toList.getLast? = some (ft[ft.size - 1]'(by omega)) := by
        rw [List.getLast?_eq_getElem?, Array.length_toList,
            List.getElem?_eq_getElem (by omega), Array.getElem_toList]
      rw [hdec, List.getLast?_cons_of_ne_nil (by simp), List.getLast?_concat] at e
      exact (Option.some.inj e).symm
    rw [← htlast_eq]; exact h_last

/-- **Stream-marker framing (value level).** The `.val`-projection of `scanFiltered_stream_framing`:
    the token VALUES are `.streamStart :: (coreVals ++ [.streamEnd])`.  This is the form the
    segment-equality producer reads — `coreVals` is exactly the marker-free token-value run the
    in-stream segment must equal (the parser consumes token values, not positions). -/
theorem scanFiltered_vals_stream_framing (input : String) (ft : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ft) (h_size : 2 ≤ ft.size) :
    ∃ coreVals, ft.toList.map (·.val)
      = YamlToken.streamStart :: (coreVals ++ [YamlToken.streamEnd]) := by
  obtain ⟨t0, tlast, core, hdec, h_t0, h_tlast⟩ := scanFiltered_stream_framing input ft h h_size
  refine ⟨core.map (·.val), ?_⟩
  rw [hdec]
  simp only [List.map_cons, List.map_append, List.map_cons, List.map_nil, h_t0, h_tlast]

/-! ### §5.15  Front B — value-recovery trace, brick 3 content half: per-element re-parse consumer joint

§5.9–§5.11 supplied the consumer side of brick 3's content half — the step algebra (§5.9), the
loop-result append scaffold (§5.10), and the pointwise → fold assembly joint (§5.11). §5.11 already
retyped the residual from "prove the fold `contentEqList items.toList items''.toList`" to "prove
pointwise `contentEq items[i] items''[i]` plus the length". But the per-element round-trip IH the
`emit_roundtrip_{sequence,mapping}_content_eq` proofs carry does NOT speak in `contentEq items[i]
items''[i]` directly — it speaks in *re-parse* terms:

  `ih i rd : parseYamlRaw (emit items[i]) = .ok rd → rd.size = 1 → contentEq items[i] (rd.map compose)[0]!.value`

So one more consumer layer sits between §5.11 and the actual sorry sites: compose that IH with §5.11.
§5.15 is that layer. It takes the genuine **producer deliverable** — for each element index, the
re-parse fact `∃ rd, parseYamlRaw (emit items[i]) = .ok rd ∧ rd.size = 1 ∧ (rd.map compose)[0]!.value
= items''[i]!` (the scanner-span-locality + parser-locality round-trip the §5.10–§5.14 chain is
building toward), plus the size equality `items.size = items''.size` — and discharges the whole
brick-3 conjunction `(items.size == items''.size && contentEqList items.toList items''.toList) = true`
by feeding each re-parse fact through the IH (re-parse → pointwise `contentEq`) and the result through
§5.11's `contentEqList_of_pointwise` (pointwise → fold). The deliverable is stated with bang-indexing
(`items''[i]!`) so it is *non-dependent* on `h_size` — i.e. the two halves bundle into one
`h_size ∧ h_rep`, the single typed obligation the retyped frontier sorry now states.

Consuming §5.15 at the two `emit_roundtrip_*_content_eq` sorry sites RETYPES each frontier sorry from
the opaque content goal to exactly that bundled producer contract — collapsing the scattered residual
to one boundary ([[ref-consumer-joint-before-producer]], [[ref-reduction-by-import]]): "produce, for the
recovered `items''`/`pairs''`, the size equality and the per-element re-parse facts." Pure plumbing
(IH application + §5.11), emission-independent, no scanner/parser machinery — the deliverable's TRUTH is
grounded against real emission in the paired `Tests/Reflections` probe before the retype. -/

/-- **Per-element re-parse → brick-3 conjunction (sequence).** Composes the per-element round-trip IH
    with §5.11 (`contentEqList_of_pointwise`): given the size equality and, for each index `i`, the
    re-parse fact that `items''[i]!` is the composed value of `parseYamlRaw (emit items[i])` (the
    producer deliverable), discharge the full brick-3 sequence conjunction. Bang-indexed deliverable so
    `h_size ∧ h_rep` is one non-dependent obligation. -/
theorem contentEqList_of_reparse
    (items items'' : Array YamlValue)
    (h_size : items.size = items''.size)
    (ih : ∀ (i : Fin items.size) (rd : Array YamlDocument),
            parseYamlRaw (emit items[i]) = .ok rd → rd.size = 1 →
            contentEq items[i] (rd.map YamlDocument.compose)[0]!.value = true)
    (h_rep : ∀ (i : Fin items.size), ∃ rd : Array YamlDocument,
              parseYamlRaw (emit items[i]) = .ok rd ∧ rd.size = 1 ∧
              (rd.map YamlDocument.compose)[0]!.value = items''[i.val]!) :
    (items.size == items''.size && contentEq.contentEqList items.toList items''.toList) = true := by
  rw [Bool.and_eq_true]
  refine ⟨by simp [h_size], ?_⟩
  apply contentEqList_of_pointwise
  · rw [Array.length_toList, Array.length_toList]; exact h_size
  · intro i h₁ h₂
    rw [Array.length_toList] at h₁ h₂
    obtain ⟨rd, h_parse_rd, h_sz_rd, h_val_eq⟩ := h_rep ⟨i, h₁⟩
    have h_content := ih ⟨i, h₁⟩ rd h_parse_rd h_sz_rd
    rw [h_val_eq] at h_content
    have h_bang : items''[i]! = items''[i]'h₂ := getElem!_pos items'' i h₂
    rw [h_bang] at h_content
    rw [Array.getElem_toList, Array.getElem_toList]
    exact h_content

/-- **Per-element re-parse → brick-3 conjunction (mapping).** Mirror of `contentEqList_of_reparse`:
    composes the key/value round-trip IHs (`ihk`/`ihv`) with §5.11's `contentEqPairList_of_pointwise`.
    The per-entry deliverable is a CONJUNCTION — both the key and the value re-parse to `pairs''[i]!`'s
    `.fst`/`.snd` — assembled into the brick-3 mapping conjunction. -/
theorem contentEqPairList_of_reparse
    (pairs pairs'' : Array (YamlValue × YamlValue))
    (h_size : pairs.size = pairs''.size)
    (ihk : ∀ (i : Fin pairs.size) (rd : Array YamlDocument),
            parseYamlRaw (emit pairs[i].fst) = .ok rd → rd.size = 1 →
            contentEq pairs[i].fst (rd.map YamlDocument.compose)[0]!.value = true)
    (ihv : ∀ (i : Fin pairs.size) (rd : Array YamlDocument),
            parseYamlRaw (emit pairs[i].snd) = .ok rd → rd.size = 1 →
            contentEq pairs[i].snd (rd.map YamlDocument.compose)[0]!.value = true)
    (h_rep : ∀ (i : Fin pairs.size),
              (∃ rdk : Array YamlDocument,
                parseYamlRaw (emit pairs[i].fst) = .ok rdk ∧ rdk.size = 1 ∧
                (rdk.map YamlDocument.compose)[0]!.value = (pairs''[i.val]!).fst) ∧
              (∃ rdv : Array YamlDocument,
                parseYamlRaw (emit pairs[i].snd) = .ok rdv ∧ rdv.size = 1 ∧
                (rdv.map YamlDocument.compose)[0]!.value = (pairs''[i.val]!).snd)) :
    (pairs.size == pairs''.size && contentEq.contentEqPairList pairs.toList pairs''.toList) = true := by
  rw [Bool.and_eq_true]
  refine ⟨by simp [h_size], ?_⟩
  apply contentEqPairList_of_pointwise
  · rw [Array.length_toList, Array.length_toList]; exact h_size
  · intro i h₁ h₂
    rw [Array.length_toList] at h₁ h₂
    obtain ⟨⟨rdk, h_pk, h_szk, h_vk⟩, ⟨rdv, h_pv, h_szv, h_vv⟩⟩ := h_rep ⟨i, h₁⟩
    have h_ck := ihk ⟨i, h₁⟩ rdk h_pk h_szk
    have h_cv := ihv ⟨i, h₁⟩ rdv h_pv h_szv
    have h_bang : pairs''[i]! = pairs''[i]'h₂ := getElem!_pos pairs'' i h₂
    rw [h_bang] at h_vk h_vv
    rw [h_vk] at h_ck
    rw [h_vv] at h_cv
    rw [Array.getElem_toList, Array.getElem_toList]
    exact ⟨h_ck, h_cv⟩

/-! ### §5.17  Compose sequence items element-wise (R595)

The `items''` array that `parseStream_flowSeqStart_recovers_outer_shape` hands back is the
compose-image of the raw parser output `items'`: each `items''[j]!` equals
`(items'[j]!.resolveAliases doc.anchors).stripAnchors`.

Two theorems:
* `compose_seq_items_pointwise` — the general element-wise equation:
  `items'' = items'.map (fun v => (v.resolveAliases doc.anchors).stripAnchors)`.
* `compose_seq_scalar_item` — the scalar corollary: if `items'[j]! = .scalar s` with
  anchor = none, then `items''[j]! = .scalar s` (compose is identity on anchor-free scalars).

These are VERIFIED-BUT-UNCONSUMED: they will be combined with the scanner-span-locality
leaf (to be landed as a future brick) to fill the sorry at
`emit_roundtrip_sequence_content_eq` (EmitterScannability.lean:1002). -/

/-- **Compose sequence items element-wise (outer-parse half, R595).** If `doc.value` is a flow
    sequence with items `items'` and `doc.compose.value` is the same shape with items `items''`,
    then `items'' = items'.map (fun v => (v.resolveAliases doc.anchors).stripAnchors)`.

    This characterizes the OUTER-PARSE items as the element-wise compose-image of the raw parser
    items. Combined with the scanner-span-locality leaf (scanner-level identification of each
    `items'[j]!`), it closes the per-element locality equation:
    `(rd.map compose)[0]!.value = items''[j]!` for scalar elements. -/
theorem compose_seq_items_pointwise
    (doc : YamlDocument) (items' items'' : Array YamlValue)
    (h_val : doc.value = .sequence .flow items' none none)
    (h_comp : (doc.compose).value = .sequence .flow items'' none none) :
    items'' = items'.map (fun v => (v.resolveAliases doc.anchors).stripAnchors) := by
  -- Step A: resolveAliases on sequence maps items' element-wise
  have h_step2 : (YamlValue.sequence .flow items' none none).resolveAliases doc.anchors =
      .sequence .flow (items'.toList.map (fun v => v.resolveAliases doc.anchors)).toArray none none := by
    simp only [YamlValue.resolveAliases]
    congr 1
    exact congrArg List.toArray (resolveList_eq_map items'.toList doc.anchors)
  -- Step B: stripAnchors on the resolved sequence maps items' element-wise, then collapses
  --         the two maps into one via List.map_map + Array.toArray_toList round-trip
  have h_step3 :
      (YamlValue.sequence .flow (items'.toList.map (fun v => v.resolveAliases doc.anchors)).toArray none none).stripAnchors =
      .sequence .flow (items'.map (fun v => (v.resolveAliases doc.anchors).stripAnchors)) none none := by
    simp only [YamlValue.stripAnchors]
    congr 1
    rw [List.toList_toArray, stripList_eq_map, List.map_map, ← Array.toList_map, Array.toArray_toList]
    simp [Function.comp]
  -- Assemble: doc.compose.value = .sequence .flow (items'.map f)
  have h_assembled : (doc.compose).value =
      .sequence .flow (items'.map (fun v => (v.resolveAliases doc.anchors).stripAnchors)) none none := by
    show (doc.value.resolveAliases doc.anchors).stripAnchors = _
    rw [h_val, h_step2, h_step3]
  -- Extract items'' = items'.map f by injectivity of the sequence constructor
  have h_eq := h_comp.symm.trans h_assembled
  simp only [YamlValue.sequence.injEq] at h_eq
  exact h_eq.2.1

/-- **Scalar item identity under compose (R595 corollary).** If `items'[j]! = .scalar s` with
    anchor = none (as emitter output always is), then `items''[j]! = .scalar s`.

    Proof: `compose_seq_items_pointwise` gives `items'' = items'.map f`;
    `resolveAliases_scalar` gives `(scalar s).resolveAliases anchors = scalar s`;
    `stripAnchors_scalar` gives `(scalar s).stripAnchors = scalar { s with anchor := none }`;
    `anchor = none` gives `{ s with anchor := none } = s`. So compose is identity here. -/
theorem compose_seq_scalar_item
    (doc : YamlDocument) (items' items'' : Array YamlValue)
    (h_val : doc.value = .sequence .flow items' none none)
    (h_comp : (doc.compose).value = .sequence .flow items'' none none)
    (j : Nat) (hj : j < items'.size)
    (content : String) (style : ScalarStyle)
    (h_item : items'[j]! = .scalar (Scalar.mk content style none none none)) :
    items''[j]! = .scalar (Scalar.mk content style none none none) := by
  have h_eq := compose_seq_items_pointwise doc items' items'' h_val h_comp
  subst h_eq
  have h_sz : j < (items'.map (fun v => (v.resolveAliases doc.anchors).stripAnchors)).size :=
    by rwa [Array.size_map]
  have step1 := getElem!_pos (items'.map (fun v => (v.resolveAliases doc.anchors).stripAnchors)) j h_sz
  have step2 := @Array.getElem_map YamlValue YamlValue
      (fun v => (v.resolveAliases doc.anchors).stripAnchors) items' j h_sz
  have step3 := getElem!_pos items' j hj
  rw [step1, step2, ← step3, h_item, resolveAliases_scalar, stripAnchors_scalar]

end L4YAML.Proofs.EmitterScannability
