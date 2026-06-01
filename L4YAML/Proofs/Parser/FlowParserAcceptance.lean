import L4YAML.Proofs.Parser.ParserWellBehaved

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace L4YAML.Proofs.ParserWellBehaved

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.ParserGrammable

/-! ## §I  Flow-body parser acceptance — base cases (`.bridge.parsenode`)

Substrate for producing `ParseNodeFlowSeqOk` / `ParseEntryFlowMapOk` on
emitter token streams.  Those predicates assert that the *real* parser
(`parseNode`, `parseFlowSequenceLoop`, `parseFlowMappingLoop`) succeeds and
advances correctly over a flow body.  The eventual discharge is a mutual
strong induction on span (see the `.iterators` `flow_parser_ok_of_structure`
sketch) that bottoms out on a *scalar* node and recurses through nested
`[…]` / `{…}` bracket groups.

This module establishes the **leaf** of that induction: what `parseNode`
does when it peeks a scalar token.  It is purely a fact about the parser —
it carries no `FlowSubrangesOk` / body-structure hypothesis — so it is
shared verbatim by both the sequence and the mapping inductions.  The
"where does the result land" obligation (the next token being `.flowEntry`
or an end bracket) is *not* part of this lemma; that is a property of the
token stream, supplied by the caller from the body-token characterization. -/

/-- `validateNodeProps` succeeds (returns `.ok ()`) when peeking at a scalar
    token with the empty `NodeProperties`.

    A scalar is not a block-collection start, so the §8.2.2 same-line check
    is vacuous; and `{}` has `hadDuplicateAnchor = false`, so the §6.9.2
    duplicate-anchor check is skipped. -/
theorem validateNodeProps_scalar (ps : ParseState) (prePropPos : Nat)
    (c : String) (s : ScalarStyle) (h_peek : ps.peek? = some (.scalar c s)) :
    validateNodeProps ps prePropPos {} = .ok () := by
  simp [validateNodeProps, h_peek, bind, Except.bind, pure, Except.pure]

/-- **Scalar base case** for flow-body parser acceptance.

    When the parse state peeks a `scalar c s` token, `parseNode` succeeds
    with positive fuel: node properties are empty (no anchor/tag), property
    validation passes, content dispatch returns the scalar, and finalization
    leaves a scalar value untouched.  The result advances the position by
    exactly one token and preserves the token array and `trackPositions`.

    This is the leaf of the `flow_parser_ok_of_structure` induction, used by
    both the `ParseNodeFlowSeqOk` and `ParseEntryFlowMapOk` derivations. -/
theorem parseNode_scalar_flow (ps : ParseState) (m : Nat) (h_m : 0 < m)
    (c : String) (s : ScalarStyle) (h_peek : ps.peek? = some (.scalar c s)) :
    ∃ ps', parseNode ps m =
        .ok (YamlValue.scalar { content := c, style := s, tag := none, anchor := none }, ps') ∧
      ps'.pos = ps.pos + 1 ∧
      ps'.tokens = ps.tokens ∧
      ps'.trackPositions = ps.trackPositions := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- Properties skip: scalar is neither anchor nor tag.
  have h_props : parseNodeProperties ps = .ok ({}, ps) :=
    parseNodeProperties_skip ps (by simp [h_peek])
  -- Property validation passes on a scalar peek.
  have h_val : validateNodeProps ps ps.pos {} = .ok () :=
    validateNodeProps_scalar ps ps.pos c s h_peek
  -- Content dispatch returns the scalar and advances by one.
  have h_content : parseNodeContent ps k {} =
      .ok (YamlValue.scalar { content := c, style := s, tag := none, anchor := none }, ps.advance) := by
    simp [parseNodeContent, h_peek]
  refine ⟨(applyNodeFinalization
            (YamlValue.scalar { content := c, style := s, tag := none, anchor := none })
            ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2,
          ?_, ?_, ?_, ?_⟩
  · -- The parseNode equation.
    unfold parseNode
    simp only [h_peek, bind, Except.bind, pure, Except.pure, h_props, h_val, h_content]
    -- Finalization leaves a scalar value unchanged.
    simp only [applyNodeFinalization]
  · rw [applyNodeFinalization_pos]; rfl
  · rw [applyNodeFinalization_tokens]; rfl
  · rw [applyNodeFinalization_trackPositions]; rfl

/-! ## §II  Flow-body parser acceptance — bracket reduction (`.bridge.parsenode.brackets`)

The recursive cases of the node induction.  When `parseNode` peeks an
opening flow bracket (`[` / `{`), property handling is vacuous (a flow
collection start is *not* a block-collection start, so the §8.2.2
same-line check does not fire, and `{}` carries no duplicate anchor), so
the node reduces to a single call of `parseFlowSequence` / `parseFlowMapping`
post-finalization.

These reductions are *conditional on* the body parse succeeding — that is
the consumer shape the eventual induction supplies via the already-closed
loop theorems `parseFlow{Sequence,Mapping}Loop_emitter_ok`.  They carry no
`FlowSubrangesOk` hypothesis: like the scalar leaf, they are pure facts
about how `parseNode` dispatches, shared by both inductions. -/

/-- `validateNodeProps` succeeds on an opening-flow-sequence peek with empty
    `NodeProperties`: `.flowSequenceStart` is not a block-collection start, so
    the §8.2.2 same-line check is vacuous, and `{}` skips the §6.9.2 check. -/
theorem validateNodeProps_flowSeqStart (ps : ParseState) (prePropPos : Nat)
    (h_peek : ps.peek? = some .flowSequenceStart) :
    validateNodeProps ps prePropPos {} = .ok () := by
  simp [validateNodeProps, h_peek, bind, Except.bind, pure, Except.pure]

/-- `validateNodeProps` succeeds on an opening-flow-mapping peek with empty
    `NodeProperties` (same reasoning as `validateNodeProps_flowSeqStart`). -/
theorem validateNodeProps_flowMapStart (ps : ParseState) (prePropPos : Nat)
    (h_peek : ps.peek? = some .flowMappingStart) :
    validateNodeProps ps prePropPos {} = .ok () := by
  simp [validateNodeProps, h_peek, bind, Except.bind, pure, Except.pure]

/-- **Flow-sequence recursive case** for node parsing.

    When the parse state peeks a `flowSequenceStart` token and the inner
    `parseFlowSequence ps k` succeeds with result `(v, ps')`, then
    `parseNode ps (k+1)` succeeds with the finalized value `v` (a flow
    sequence value is unchanged by empty-property finalization) at the same
    landing state.  This connects `parseNode` to the already-closed loop
    theorem `parseFlowSequenceLoop_emitter_ok`. -/
theorem parseNode_flowSeqStart_of_parse (ps ps' : ParseState) (k : Nat) (v : YamlValue)
    (h_peek : ps.peek? = some .flowSequenceStart)
    (h_parse : parseFlowSequence ps k = .ok (v, ps')) :
    parseNode ps (k + 1) =
      .ok (applyNodeFinalization v ps' {}
        (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })) := by
  have h_props : parseNodeProperties ps = .ok ({}, ps) :=
    parseNodeProperties_skip ps (by simp [h_peek])
  have h_val : validateNodeProps ps ps.pos {} = .ok () :=
    validateNodeProps_flowSeqStart ps ps.pos h_peek
  have h_content : parseNodeContent ps k {} = .ok (v, ps') := by
    simp only [parseNodeContent, h_peek]; exact h_parse
  unfold parseNode
  simp only [h_peek, bind, Except.bind, pure, Except.pure, h_props, h_val, h_content]

/-- **Flow-mapping recursive case** for node parsing (mirror of
    `parseNode_flowSeqStart_of_parse`).  Connects `parseNode` to
    `parseFlowMappingLoop_emitter_ok`. -/
theorem parseNode_flowMapStart_of_parse (ps ps' : ParseState) (k : Nat) (v : YamlValue)
    (h_peek : ps.peek? = some .flowMappingStart)
    (h_parse : parseFlowMapping ps k = .ok (v, ps')) :
    parseNode ps (k + 1) =
      .ok (applyNodeFinalization v ps' {}
        (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })) := by
  have h_props : parseNodeProperties ps = .ok ({}, ps) :=
    parseNodeProperties_skip ps (by simp [h_peek])
  have h_val : validateNodeProps ps ps.pos {} = .ok () :=
    validateNodeProps_flowMapStart ps ps.pos h_peek
  have h_content : parseNodeContent ps k {} = .ok (v, ps') := by
    simp only [parseNodeContent, h_peek]; exact h_parse
  unfold parseNode
  simp only [h_peek, bind, Except.bind, pure, Except.pure, h_props, h_val, h_content]

/-! ## §III  Structure → parser-state bridge (`.bridge.parsenode.brackets`, predicates half)

The reduction lemmas (§I/§II) connect `parseNode` to its sub-parses but say
nothing about *where the result lands*.  The consumers
`ParseNodeFlowSeqOk` / `ParseEntryFlowMapOk` demand the landing conditions —
the next `ps.peek?` is a separator (`.flowEntry`) or the closing bracket, and
the bracket balance over the consumed span is `0`.  Those facts are exactly
what the body-structure predicates (`SeqBodyProps` / `MapBodyProps`,
`ParserGrammableBase.lean`) record, but stated over the *token array*
(`tokens[k]!.val`) rather than over a `ParseState`.

This section builds the glue that crosses that gap:

* `peek_of_isFlowContentStart` — turns a `isFlowContentStart` fact at a token
  position into the content-start `ps.peek?` disjunction that both node
  inductions dispatch on.  A pure peek fact, shared verbatim by the sequence
  and the mapping derivations.
* `parseNode_seqScalar_ok` — the **scalar branch** of the
  `ParseNodeFlowSeqOk` derivation, discharged directly from `SeqBodyProps`.
  This is the one node case that needs *no* inductive hypothesis (a scalar has
  no inner body), so it is a standalone, non-circular brick: it combines the
  §I scalar reduction (`parseNode_scalar_flow`) with `SeqBodyProps.scalar_succ`
  for the successor peek and `flowBracketBalance_single` for the span balance. -/

/-- Translate a token-level `isFlowContentStart` fact at the current position
    into the content-start `ps.peek?` disjunction.  Used by both flow-body node
    inductions to dispatch `parseNodeContent`. -/
theorem peek_of_isFlowContentStart {ps : ParseState} {k : Nat}
    (h_pos : ps.pos = k) (h_bound : k < ps.tokens.size)
    (h_cs : isFlowContentStart ps.tokens[k]!.val) :
    (∃ c s, ps.peek? = some (.scalar c s)) ∨
    ps.peek? = some .flowSequenceStart ∨
    ps.peek? = some .flowMappingStart := by
  simp only [isFlowContentStart] at h_cs
  rcases h_cs with ⟨c, s, h⟩ | h | h
  · exact Or.inl ⟨c, s, peek_of_pos_val h_pos h_bound h⟩
  · exact Or.inr (Or.inl (peek_of_pos_val h_pos h_bound h))
  · exact Or.inr (Or.inr (peek_of_pos_val h_pos h_bound h))

/-- **Scalar branch of `ParseNodeFlowSeqOk`.**

    At a depth-0 scalar position inside a flow-sequence body satisfying
    `SeqBodyProps`, `parseNode` succeeds, advances by exactly one token, and
    lands on either a `.flowEntry` separator or the closing `.flowSequenceEnd`
    (at the body end); the consumed single-token span has bracket balance `0`.

    This discharges the scalar disjunct of the node induction with no inductive
    hypothesis, combining the §I reduction `parseNode_scalar_flow` with
    `SeqBodyProps.scalar_succ` (successor peek) and `flowBracketBalance_single`
    (span balance). -/
theorem parseNode_seqScalar_ok {tokens : Array (Positioned YamlToken)}
    {endPos body_start : Nat}
    (hbody : SeqBodyProps tokens body_start endPos)
    (h_end : endPos < tokens.size)
    (ps : ParseState) (m : Nat) (h_m : 0 < m)
    (h_tok : ps.tokens = tokens)
    (h_pos_lt : ps.pos < endPos)
    (h_bs : body_start ≤ ps.pos)
    (h_bal : flowBracketBalance tokens body_start ps.pos = 0)
    (c : String) (s : ScalarStyle)
    (h_peek : ps.peek? = some (.scalar c s)) :
    ∃ val ps', parseNode ps m = .ok (val, ps') ∧
      ps'.pos > ps.pos ∧ ps'.pos ≤ endPos ∧
      ps'.tokens = tokens ∧
      ps'.trackPositions = ps.trackPositions ∧
      (ps'.peek? = some .flowEntry ∨
       (ps'.peek? = some .flowSequenceEnd ∧ ps'.pos = endPos)) ∧
      flowBracketBalance tokens ps.pos ps'.pos = 0 := by
  -- §I scalar reduction: parseNode succeeds, advancing by one token.
  obtain ⟨ps', h_node, h_pos', h_tok', h_tp'⟩ := parseNode_scalar_flow ps m h_m c s h_peek
  -- The token at the current position is the scalar `c s`.
  obtain ⟨h_pos_sz, h_val_eq⟩ := peek_some_val h_peek
  have h_val_tok : tokens[ps.pos]!.val = .scalar c s := by rw [← h_tok]; exact h_val_eq
  have hsz : ps.pos < tokens.size := by rw [← h_tok]; exact h_pos_sz
  -- Structural successor: after a depth-0 scalar comes `.flowEntry` or the end.
  obtain ⟨h_k1_le, h_next⟩ :=
    hbody.scalar_succ ps.pos h_bs h_pos_lt h_bal ⟨c, s, h_val_tok⟩
  refine ⟨_, ps', h_node, by omega, by omega, by rw [h_tok']; exact h_tok, h_tp', ?_, ?_⟩
  · -- Landing peek at `ps'.pos = ps.pos + 1`.
    rcases h_next with h_fe | ⟨h_se, h_eq⟩
    · exact Or.inl
        (peek_of_pos_val h_pos' (by rw [h_tok', h_tok]; omega) (by rw [h_tok', h_tok]; exact h_fe))
    · exact Or.inr
        ⟨peek_of_pos_val h_pos' (by rw [h_tok', h_tok]; omega) (by rw [h_tok', h_tok]; exact h_se),
         by omega⟩
  · -- The single scalar token contributes zero bracket balance.
    rw [h_pos']
    have hsz' : ps.pos < tokens.toList.length := by simpa using hsz
    rw [flowBracketBalance_single tokens ps.pos hsz']
    have h1 : tokens.toList[ps.pos]'hsz' = tokens[ps.pos] := Array.getElem_toList hsz
    have h2 : tokens[ps.pos] = tokens[ps.pos]! := (getElem!_pos tokens ps.pos hsz).symm
    rw [h1, h2, h_val_tok]
    rfl

end L4YAML.Proofs.ParserWellBehaved
