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

/-! ## §IV  Map-entry parser acceptance — the scalar-keyed/scalar-valued entry

The `ParseEntryFlowMapOk` analogue of §III's `parseNode_seqScalar_ok`.  A flow
mapping body entry at depth 0 has the token shape
`.key, key_content, .value, val_content, (.flowEntry | .flowMappingEnd)`.  The
*scalar-keyed, scalar-valued* entry is the one entry case that needs **no**
inductive hypothesis (neither key nor value has an inner body), so — exactly
like the sequence scalar leaf — it is a standalone, non-circular brick.

Two reductions stand between this brick and the §I scalar leaf, because a map
entry runs the parser *twice* (key, then value) through two dedicated parser
entry points:

* `parseExplicitKey_scalar` — on a scalar peek, `parseExplicitKey` falls through
  its `.value`/`.flowEntry`/`.flowMappingEnd` guard to a plain `parseNode`.
* `parseFlowMappingValue_scalar` — the value half: it pushes the key path,
  no-ops `tryConsume .key` (peek is `.value`), consumes the `.value` separator,
  then `parseNode`s the scalar value and restores the path.  This is the only
  `do`-block reduction in the file (the others are pure `match` dispatch).

`parseEntry_mapScalar_ok` then reads the entry's structural successors off
`MapBodyProps` (M4 for the `.value` after a scalar key, M7 for the
`.flowEntry`/`.flowMappingEnd` after a scalar value) and computes the span
bracket balance from the four depth-0 non-bracket tokens (`.key`, scalar,
`.value`, scalar — each `flowBracketDelta = 0`). -/

/-- A single depth-0 non-bracket token contributes zero bracket balance over its
    one-token span.  The `flowBracketBalance_single` bridge specialized to a token
    whose `flowBracketDelta` is `0` (`.key`, `.value`, `.scalar`, …). -/
theorem flowBracketBalance_step_zero {tokens : Array (Positioned YamlToken)} {q : Nat}
    (hq : q < tokens.size) (h0 : flowBracketDelta tokens[q]!.val = 0) :
    flowBracketBalance tokens q (q + 1) = 0 := by
  have hsz' : q < tokens.toList.length := by simpa using hq
  rw [flowBracketBalance_single tokens q hsz']
  have h1 : tokens.toList[q]'hsz' = tokens[q] := Array.getElem_toList hq
  have h2 : tokens[q] = tokens[q]! := (getElem!_pos tokens q hq).symm
  rw [h1, h2]; exact h0

/-- **Scalar branch of `parseExplicitKey`.**  When the parse state peeks a
    `scalar c s` token, `parseExplicitKey` dispatches past its empty-key guards
    (`.value` / `.flowEntry` / `.flowMappingEnd`) to `parseNode`, succeeding with
    the scalar value, advancing by one, and preserving tokens / `trackPositions`. -/
theorem parseExplicitKey_scalar (ps : ParseState) (m : Nat) (h_m : 0 < m)
    (c : String) (s : ScalarStyle) (h_peek : ps.peek? = some (.scalar c s)) :
    ∃ ps', parseExplicitKey ps m =
        .ok (YamlValue.scalar { content := c, style := s, tag := none, anchor := none }, ps') ∧
      ps'.pos = ps.pos + 1 ∧ ps'.tokens = ps.tokens ∧ ps'.trackPositions = ps.trackPositions := by
  obtain ⟨ps', h_node, h_pos', h_tok', h_tp'⟩ := parseNode_scalar_flow ps m h_m c s h_peek
  refine ⟨ps', ?_, h_pos', h_tok', h_tp'⟩
  simp only [parseExplicitKey, h_peek]
  exact h_node

/-- **Scalar branch of `parseFlowMappingValue`.**

    At a state peeking the `.value` separator with a scalar value token next,
    `parseFlowMappingValue` consumes the separator and parses the scalar:
    `tryConsume .key` is a no-op (the peek is `.value`, not `.key`),
    `tryConsume .value` advances past the separator, and the scalar branch of
    `parseNode` returns the value.  The result advances by exactly two tokens
    (separator + scalar) and preserves tokens / `trackPositions` (only
    `currentPath` is touched, and it is restored to `savedPath`). -/
theorem parseFlowMappingValue_scalar (ps : ParseState) (m : Nat) (h_m : 0 < m)
    (savedPath : YamlPath) (keyContent : String)
    (cv : String) (sv : ScalarStyle)
    (h_peek_value : ps.peek? = some .value)
    (h_succ_lt : ps.pos + 1 < ps.tokens.size)
    (h_succ_scalar : ps.tokens[ps.pos + 1]!.val = .scalar cv sv) :
    ∃ ps', parseFlowMappingValue ps m savedPath keyContent =
        .ok (YamlValue.scalar { content := cv, style := sv, tag := none, anchor := none }, ps') ∧
      ps'.pos = ps.pos + 2 ∧ ps'.tokens = ps.tokens ∧ ps'.trackPositions = ps.trackPositions := by
  -- The path-pushed state `{ps with currentPath := …}`: each `ParseState.peek?`/
  -- field projection reduces through the record update to the corresponding field
  -- of `ps` (`set` is unavailable — core Lean only — so we work on the literal).
  -- `peek?` reads only `pos`/`tokens`, so it is defeq to `ps.peek?`.
  have hpk1 : ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseState).peek?
      = some YamlToken.value := h_peek_value
  -- `tryConsume .key` is a no-op; `tryConsume .value` advances past the separator.
  have htck : ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseState).tryConsume
      YamlToken.key = (false, { ps with currentPath := savedPath.push (.key keyContent) }) := by
    simp [ParseState.tryConsume, hpk1]
  have htcv : ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseState).tryConsume
      YamlToken.value
      = (true, ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseState).advance) := by
    simp [ParseState.tryConsume, hpk1]
  -- After consuming `.value`, the peek is the scalar value token.
  have hpk2 : ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseState).advance.peek?
      = some (YamlToken.scalar cv sv) := by
    have e1 : ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseState).advance.pos
        = ps.pos + 1 := rfl
    have e2 : ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseState).advance.tokens
        = ps.tokens := rfl
    unfold ParseState.peek?
    rw [e1, e2, if_pos h_succ_lt, h_succ_scalar]
  obtain ⟨ps_d, h_node, h_pos_d, h_tok_d, h_tp_d⟩ :=
    parseNode_scalar_flow _ m h_m cv sv hpk2
  refine ⟨{ ps_d with currentPath := savedPath }, ?_, ?_, ?_, ?_⟩
  · -- Reduce the `do`-block: path push, two `tryConsume`s, scalar `parseNode`, path restore.
    simp only [parseFlowMappingValue, htck, htcv, hpk2, h_node,
      bind, Except.bind, if_true]
  · -- pos = ps.pos + 2.
    have e1 : ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseState).advance.pos
        = ps.pos + 1 := rfl
    have : ps_d.pos = ps.pos + 1 + 1 := by rw [h_pos_d, e1]
    omega
  · -- tokens preserved.
    show ps_d.tokens = ps.tokens
    rw [h_tok_d]; rfl
  · -- trackPositions preserved.
    show ps_d.trackPositions = ps.trackPositions
    rw [h_tp_d]; rfl

/-- **Scalar-keyed/scalar-valued branch of `ParseEntryFlowMapOk`.**

    At a depth-0 `.key` position inside a flow-mapping body satisfying
    `MapBodyProps`, where both the key and the value are scalar tokens, the full
    `parseExplicitKey` + `parseFlowMappingValue` chain succeeds: the key parse
    (on `ps.advance`, past the loop-consumed `.key`) lands on the `.value`
    separator, and the value parse lands on either a `.flowEntry` separator or
    the closing `.flowMappingEnd` (at the body end); the consumed four-token span
    has bracket balance `0`.

    This is the entry-induction leaf — no inductive hypothesis (neither key nor
    value has an inner body) — and the `ParseEntryFlowMapOk` analogue of §III's
    `parseNode_seqScalar_ok`.  M4 (`key_scalar_value`) supplies the `.value`
    after a scalar key; M7 (`value_scalar_succ`) supplies the landing after a
    scalar value. -/
theorem parseEntry_mapScalar_ok {tokens : Array (Positioned YamlToken)}
    {endPos body_start : Nat}
    (hbody : MapBodyProps tokens body_start endPos)
    (h_end : endPos < tokens.size)
    (ps : ParseState) (m : Nat) (h_m : 0 < m)
    (h_tok : ps.tokens = tokens)
    (h_pos_lt : ps.pos < endPos)
    (h_bs : body_start ≤ ps.pos)
    (h_bal : flowBracketBalance tokens body_start ps.pos = 0)
    (h_peek : ps.peek? = some .key)
    (ck : String) (sk : ScalarStyle)
    (h_key_scalar : tokens[ps.pos + 1]!.val = .scalar ck sk)
    (cv : String) (sv : ScalarStyle)
    (h_val_scalar : tokens[ps.pos + 3]!.val = .scalar cv sv) :
    ∃ key_val key_ps,
      parseExplicitKey ps.advance m = .ok (key_val, key_ps) ∧
      key_ps.pos > ps.pos ∧ key_ps.pos ≤ endPos ∧
      key_ps.tokens = tokens ∧
      key_ps.trackPositions = ps.trackPositions ∧
      ∀ (savedPath : YamlPath) (keyContent : String),
        ∃ val_val val_ps,
          parseFlowMappingValue key_ps m savedPath keyContent = .ok (val_val, val_ps) ∧
          val_ps.pos > ps.pos ∧ val_ps.pos ≤ endPos ∧
          val_ps.tokens = tokens ∧
          val_ps.trackPositions = ps.trackPositions ∧
          (val_ps.peek? = some .flowEntry ∨
           (val_ps.peek? = some .flowMappingEnd ∧ val_ps.pos = endPos)) ∧
          flowBracketBalance tokens ps.pos val_ps.pos = 0 := by
  -- The `.key` token at the entry position.
  obtain ⟨hp_lt, h_key_tok⟩ := peek_some_val h_peek
  rw [h_tok] at hp_lt h_key_tok
  -- M4: after a scalar-keyed `.key`, the `.value` separator follows at `ps.pos + 2`.
  obtain ⟨h_val_lt, h_value_tok⟩ :=
    hbody.key_scalar_value ps.pos h_bs h_pos_lt h_bal h_key_tok ⟨ck, sk, h_key_scalar⟩
  -- Bracket balance is `0` up to the `.value` position (two depth-0 zero-delta tokens).
  have hd_key : flowBracketDelta tokens[ps.pos]!.val = 0 := by rw [h_key_tok]; rfl
  have hd_keyscalar : flowBracketDelta tokens[ps.pos + 1]!.val = 0 := by rw [h_key_scalar]; rfl
  have hs_key : flowBracketBalance tokens ps.pos (ps.pos + 1) = 0 :=
    flowBracketBalance_step_zero hp_lt hd_key
  have hs_keyscalar : flowBracketBalance tokens (ps.pos + 1) (ps.pos + 2) = 0 :=
    flowBracketBalance_step_zero (by omega) hd_keyscalar
  have hbal_value : flowBracketBalance tokens body_start (ps.pos + 2) = 0 := by
    rw [flowBracketBalance_compose tokens body_start ps.pos (ps.pos + 2) h_bs (by omega),
        flowBracketBalance_compose tokens ps.pos (ps.pos + 1) (ps.pos + 2) (by omega) (by omega),
        h_bal, hs_key, hs_keyscalar]; rfl
  -- M7: after a scalar value, the entry lands on `.flowEntry` or the closing `.flowMappingEnd`.
  have hidx : ps.pos + 2 + 2 = ps.pos + 4 := by omega
  have h7 := hbody.value_scalar_succ (ps.pos + 2) (by omega) h_val_lt hbal_value h_value_tok
    ⟨cv, sv, h_val_scalar⟩
  rw [hidx] at h7
  obtain ⟨h_land_le, h_land_tok⟩ := h7
  -- Key parse: `parseExplicitKey ps.advance` on a scalar peek lands on the `.value`.
  have hadv_peek : (ps.advance).peek? = some (.scalar ck sk) := by
    apply peek_of_pos_val (k := ps.pos + 1) (by simp [ParseState.advance]) _ _
    · simp only [ParseState.advance]; rw [h_tok]; omega
    · simp only [ParseState.advance]; rw [h_tok]; exact h_key_scalar
  obtain ⟨key_ps, h_key_parse, h_key_pos, h_key_tokeq, h_key_tp⟩ :=
    parseExplicitKey_scalar ps.advance m h_m ck sk hadv_peek
  -- key_ps lands at `ps.pos + 2` (= the `.value` position), tokens / trackPositions preserved.
  have hadv_pos : (ps.advance).pos = ps.pos + 1 := rfl
  have hk_pos : key_ps.pos = ps.pos + 2 := by rw [h_key_pos, hadv_pos]
  have hk_tok : key_ps.tokens = tokens := by rw [h_key_tokeq]; simp [ParseState.advance, h_tok]
  have hk_tp : key_ps.trackPositions = ps.trackPositions := by
    rw [h_key_tp]; simp [ParseState.advance]
  refine ⟨_, key_ps, h_key_parse, by omega, by omega, hk_tok, hk_tp, ?_⟩
  intro savedPath keyContent
  -- Value parse: `parseFlowMappingValue key_ps` consumes `.value` and parses the scalar value.
  have hkey_value_peek : key_ps.peek? = some YamlToken.value := by
    apply peek_of_pos_val (k := ps.pos + 2) hk_pos
    · rw [hk_tok]; omega
    · rw [hk_tok]; exact h_value_tok
  have hkey_succ_lt : key_ps.pos + 1 < key_ps.tokens.size := by rw [hk_pos, hk_tok]; omega
  have hkey_succ_scalar : key_ps.tokens[key_ps.pos + 1]!.val = .scalar cv sv := by
    rw [hk_tok, hk_pos]; exact h_val_scalar
  obtain ⟨val_ps, h_val_parse, h_val_pos, h_val_tokeq, h_val_tp⟩ :=
    parseFlowMappingValue_scalar key_ps m h_m savedPath keyContent cv sv
      hkey_value_peek hkey_succ_lt hkey_succ_scalar
  -- val_ps lands at `ps.pos + 4`, tokens / trackPositions back to the entry state.
  have hv_pos : val_ps.pos = ps.pos + 4 := by rw [h_val_pos, hk_pos]
  have hv_tok : val_ps.tokens = tokens := by rw [h_val_tokeq]; exact hk_tok
  have hv_tp : val_ps.trackPositions = ps.trackPositions := by rw [h_val_tp]; exact hk_tp
  refine ⟨_, val_ps, h_val_parse, by omega, by omega, hv_tok, hv_tp, ?_, ?_⟩
  · -- Landing peek at `ps.pos + 4`.
    rcases h_land_tok with h_fe | ⟨h_me, h_eq⟩
    · exact Or.inl (peek_of_pos_val hv_pos (by rw [hv_tok]; omega) (by rw [hv_tok]; exact h_fe))
    · exact Or.inr
        ⟨peek_of_pos_val hv_pos (by rw [hv_tok]; omega) (by rw [hv_tok]; exact h_me), by omega⟩
  · -- Span bracket balance: four depth-0 zero-delta tokens.
    rw [hv_pos]
    have hd_value : flowBracketDelta tokens[ps.pos + 2]!.val = 0 := by rw [h_value_tok]; rfl
    have hd_valscalar : flowBracketDelta tokens[ps.pos + 3]!.val = 0 := by rw [h_val_scalar]; rfl
    have hs_value : flowBracketBalance tokens (ps.pos + 2) (ps.pos + 3) = 0 :=
      flowBracketBalance_step_zero (by omega) hd_value
    have hs_valscalar : flowBracketBalance tokens (ps.pos + 3) (ps.pos + 4) = 0 :=
      flowBracketBalance_step_zero (by omega) hd_valscalar
    rw [flowBracketBalance_compose tokens ps.pos (ps.pos + 2) (ps.pos + 4) (by omega) (by omega),
        flowBracketBalance_compose tokens ps.pos (ps.pos + 1) (ps.pos + 2) (by omega) (by omega),
        flowBracketBalance_compose tokens (ps.pos + 2) (ps.pos + 3) (ps.pos + 4) (by omega) (by omega),
        hs_key, hs_keyscalar, hs_value, hs_valscalar]; rfl

/-! ## §V  Collection-entry acceptance — lifting the loop theorems (`.bridge.parsenode.brackets`, entry half)

The §III/§IV leaves discharge the *scalar* cases of the node/entry inductions
with no inductive hypothesis.  The *bracket* cases — a node whose token is an
opening `[`/`{`, or a map entry whose key/value is a bracket group — reduce
(via §II's `parseNode_flow{Seq,Map}Start_of_parse`) to a single success of the
collection parser `parseFlowSequence` / `parseFlowMapping` over the inner body.

This section lifts the already-closed *loop* theorems
(`parseFlow{Sequence,Mapping}Loop_emitter_ok`) to those collection entry points.
`parseFlowSequence ps (fuel+1)` consumes the opening `[`, runs the loop on
`ps.advance`, and on the loop landing at the matching `]` (which the loop
theorem guarantees) takes the closing branch and advances past it — so the
whole collection consumes the span `[ps.pos, j+1)` and lands at `j+1`.

The preconditions are exactly the existing `Loop{Seq,Map}Preconditions` bundles
(`ParserWellBehaved.lean`), which the eventual span induction will discharge for
the inner body from `FlowSubrangesOk` + the inductive hypothesis.  Like the
leaves, these carry no `FlowSubrangesOk` hypothesis themselves: they are pure
facts about how the collection parser dispatches once the loop is known to
succeed, shared verbatim by the sequence and mapping node cases. -/

/-- **Flow-sequence collection acceptance.**  Given the loop preconditions for
    the inner body `[ps.advance.pos, j)` (with `j` the matching `]`),
    `parseFlowSequence ps (fuel+1)` succeeds: it consumes the opening `[`, runs
    `parseFlowSequenceLoop` to the closing `]` at `j`, and advances past it,
    landing at `j+1` with the token array and `trackPositions` preserved.

    The bridge between the closed loop theorem `parseFlowSequenceLoop_emitter_ok`
    and §II's `parseNode_flowSeqStart_of_parse`: the latter consumes exactly a
    `parseFlowSequence ps k = .ok (v, ps')` success of this shape. -/
theorem parseFlowSequence_emitter_ok (ps : ParseState) (fuel j body_start : Nat)
    (pre : LoopSeqPreconditions ps.tokens ps.advance j body_start fuel) :
    ∃ items ps', parseFlowSequence ps (fuel + 1) =
        .ok (YamlValue.sequence .flow items, ps') ∧
      ps'.pos = j + 1 ∧ ps'.tokens = ps.tokens ∧ ps'.trackPositions = ps.trackPositions := by
  obtain ⟨items, ps2, h_loop, h_peek2, h_pos2, h_tok2, h_tp2⟩ :=
    parseFlowSequenceLoop_emitter_ok fuel ps.advance #[] j body_start
      pre.h_pn pre.h_fuel pre.h_pos pre.h_end_pos pre.h_end_tok pre.h_at_end
      pre.h_entry pre.h_content_start pre.h_after_fe pre.h_bal pre.h_bs
  refine ⟨items, ps2.advance, ?_, ?_, ?_, ?_⟩
  · -- Consume `[`, run the loop, take the closing-`]` branch, advance past it.
    unfold parseFlowSequence
    simp only [bind, Except.bind]
    rw [h_loop]; simp only [h_peek2]
  · -- `ps2.advance.pos = ps2.pos + 1 = j + 1` (loop landed at `j`).
    show ps2.pos + 1 = j + 1
    rw [h_pos2]
  · -- tokens preserved (`ps.advance.tokens` is defeq `ps.tokens`).
    show ps2.tokens = ps.tokens
    rw [h_tok2]; simp only [ParseState.advance]
  · -- trackPositions preserved.
    show ps2.trackPositions = ps.trackPositions
    rw [h_tp2]; simp only [ParseState.advance]

/-- **Flow-mapping collection acceptance** (mirror of
    `parseFlowSequence_emitter_ok`).  Given the loop preconditions for the inner
    body `[ps.advance.pos, j)` (with `j` the matching `}`),
    `parseFlowMapping ps (fuel+1)` succeeds, consuming the span `[ps.pos, j+1)`
    and landing at `j+1`.  Bridges `parseFlowMappingLoop_emitter_ok` to §II's
    `parseNode_flowMapStart_of_parse`.

    The `LoopMapPreconditions.h_after_fe` gives the strict bound `k+1 < j` for the
    post-separator key; the loop theorem only needs `k+1 ≤ j`, so it is weakened. -/
theorem parseFlowMapping_emitter_ok (ps : ParseState) (fuel j body_start : Nat)
    (pre : LoopMapPreconditions ps.tokens ps.advance j body_start fuel) :
    ∃ pairs ps', parseFlowMapping ps (fuel + 1) =
        .ok (YamlValue.mapping .flow pairs, ps') ∧
      ps'.pos = j + 1 ∧ ps'.tokens = ps.tokens ∧ ps'.trackPositions = ps.trackPositions := by
  obtain ⟨pairs, ps2, h_loop, h_peek2, h_pos2, h_tok2, h_tp2⟩ :=
    parseFlowMappingLoop_emitter_ok fuel ps.advance #[] j body_start
      pre.h_pn pre.h_fuel pre.h_pos pre.h_end_pos pre.h_end_tok pre.h_at_end
      pre.h_entry pre.h_key_start
      (fun k hk1 hk2 hk3 hk4 =>
        let ⟨h1, h2⟩ := pre.h_after_fe k hk1 hk2 hk3 hk4; ⟨Nat.le_of_lt h1, h2⟩)
      pre.h_bal pre.h_bs
  refine ⟨pairs, ps2.advance, ?_, ?_, ?_, ?_⟩
  · -- Consume `{`, run the loop, take the closing-`}` branch, advance past it.
    unfold parseFlowMapping
    simp only [bind, Except.bind]
    rw [h_loop]; simp only [h_peek2]
  · show ps2.pos + 1 = j + 1
    rw [h_pos2]
  · show ps2.tokens = ps.tokens
    rw [h_tok2]; simp only [ParseState.advance]
  · show ps2.trackPositions = ps.trackPositions
    rw [h_tp2]; simp only [ParseState.advance]

/-! ## §VI  Loop-precondition assembly from body structure (`.iterators.bundle`)

The span strong-induction `flow_parser_ok_of_structure` descends into a depth-0
bracket `[…]` / `{…}` at position `k = ps.pos` whose matching close is `j`.  To
parse that bracket it calls §V (`parseFlow{Sequence,Mapping}_emitter_ok`), which
consumes a `Loop{Seq,Map}Preconditions` bundle for the inner body `[k+1, j)`.

These two theorems ASSEMBLE that bundle from exactly the two ingredients the
induction has on hand at the bracket:

* the inner body's structure — `SeqBodyProps`/`MapBodyProps tokens (k+1) j`,
  obtained from `FlowSubrangesOk.{seq,map}` at the subrange `(k+1, j)`; and
* the inner body's acceptance predicate — `ParseNodeFlowSeqOk`/`ParseEntryFlowMapOk
  tokens j fuel (k+1)`, obtained from the inductive hypothesis (the inner span
  `j - (k+1)` is strictly smaller than the outer span).

`ps_adv` is `ps.advance` (positioned at `k+1`); the inner `body_start` coincides
with `ps_adv.pos`, so the empty-prefix balance and `body_start ≤ pos` facts are
trivial.  The interesting fields convert the structural predicates' token-value
classifications (`isFlowContentStart`, `.key`) into the `peek?`/`.val` shapes the
loop theorem expects. -/

/-- Assemble `LoopSeqPreconditions` for the inner sequence body `[ps_adv.pos, j)`
    from its `SeqBodyProps` and its `ParseNodeFlowSeqOk` predicate. -/
theorem loopSeqPre_of (tokens : Array (Positioned YamlToken)) (ps_adv : ParseState)
    (j fuel : Nat)
    (h_tok : ps_adv.tokens = tokens)
    (hbody : SeqBodyProps tokens ps_adv.pos j)
    (h_pn : ParseNodeFlowSeqOk tokens j fuel ps_adv.pos)
    (h_le : ps_adv.pos ≤ j)
    (h_j_end : j < tokens.size)
    (h_end_tok : tokens[j]!.val = .flowSequenceEnd)
    (h_fuel : fuel > 2 * (j - ps_adv.pos) + 1) :
    LoopSeqPreconditions tokens ps_adv j ps_adv.pos fuel := by
  refine { h_pn := h_pn, h_fuel := h_fuel, h_pos := h_le, h_end_pos := ?_,
           h_end_tok := ?_, h_at_end := ?_, h_entry := ?_, h_content_start := ?_,
           h_after_fe := ?_, h_bal := ?_, h_bs := Nat.le_refl _ }
  · rw [h_tok]; exact h_j_end
  · rw [h_tok]; exact h_end_tok
  · -- h_at_end: peek = seqEnd ⟹ at end position (else content_start gives a contradiction)
    intro h_peek
    obtain ⟨_, h_val⟩ := peek_some_val h_peek
    rw [h_tok] at h_val
    rcases Nat.eq_or_lt_of_le h_le with h_eq | h_lt
    · exact h_eq
    · exfalso
      have h_cs := hbody.content_start h_lt
      simp only [isFlowContentStart] at h_cs
      rcases h_cs with ⟨c, s, hc⟩ | hc | hc <;> rw [h_val] at hc <;> cases hc
  · intro h; simp at h
  · -- h_content_start: content-start token at ps_adv.pos lifts to a peek? disjunction
    intro h_lt _
    have h_cs := hbody.content_start h_lt
    simp only [isFlowContentStart] at h_cs
    have h_bound : ps_adv.pos < ps_adv.tokens.size := by rw [h_tok]; omega
    rcases h_cs with ⟨c, s, hc⟩ | hc | hc
    · exact .inl ⟨c, s, peek_of_pos_val rfl h_bound (by rw [h_tok]; exact hc)⟩
    · exact .inr (.inl (peek_of_pos_val rfl h_bound (by rw [h_tok]; exact hc)))
    · exact .inr (.inr (peek_of_pos_val rfl h_bound (by rw [h_tok]; exact hc)))
  · -- h_after_fe: flowEntry at depth 0 ⟹ content-start successor (S3)
    intro k hk_lo hk_hi hk_fe hk_bal
    rw [h_tok] at hk_fe hk_bal
    obtain ⟨h_succ_lt, h_succ_cs⟩ := hbody.after_fe k hk_lo hk_hi hk_bal hk_fe
    refine ⟨by omega, ?_⟩
    rw [h_tok]
    simp only [isFlowContentStart] at h_succ_cs
    exact h_succ_cs
  · rw [h_tok]; simp [flowBracketBalance]

/-- Assemble `LoopMapPreconditions` for the inner mapping body `[ps_adv.pos, j)`
    from its `MapBodyProps` and its `ParseEntryFlowMapOk` predicate. -/
theorem loopMapPre_of (tokens : Array (Positioned YamlToken)) (ps_adv : ParseState)
    (j fuel : Nat)
    (h_tok : ps_adv.tokens = tokens)
    (hbody : MapBodyProps tokens ps_adv.pos j)
    (h_pn : ParseEntryFlowMapOk tokens j fuel ps_adv.pos)
    (h_le : ps_adv.pos ≤ j)
    (h_j_end : j < tokens.size)
    (h_end_tok : tokens[j]!.val = .flowMappingEnd)
    (h_fuel : fuel > 2 * (j - ps_adv.pos) + 1) :
    LoopMapPreconditions tokens ps_adv j ps_adv.pos fuel := by
  refine { h_pn := h_pn, h_fuel := h_fuel, h_pos := h_le, h_end_pos := ?_,
           h_end_tok := ?_, h_at_end := ?_, h_entry := ?_, h_key_start := ?_,
           h_after_fe := ?_, h_bal := ?_, h_bs := Nat.le_refl _ }
  · rw [h_tok]; exact h_j_end
  · rw [h_tok]; exact h_end_tok
  · -- h_at_end: peek = mapEnd ⟹ at end position (else key_start gives `.key ≠ .mapEnd`)
    intro h_peek
    obtain ⟨_, h_val⟩ := peek_some_val h_peek
    rw [h_tok] at h_val
    rcases Nat.eq_or_lt_of_le h_le with h_eq | h_lt
    · exact h_eq
    · exfalso
      have h_key := hbody.key_start h_lt
      rw [h_val] at h_key
      cases h_key
  · intro h; simp at h
  · -- h_key_start: `.key` token at ps_adv.pos lifts to a peek? = some .key
    intro h_lt _
    have h_key := hbody.key_start h_lt
    have h_bound : ps_adv.pos < ps_adv.tokens.size := by rw [h_tok]; omega
    exact peek_of_pos_val rfl h_bound (by rw [h_tok]; exact h_key)
  · -- h_after_fe: flowEntry at depth 0 ⟹ `.key` successor, strictly before `j` (M2 + j is mapEnd)
    intro k hk_lo hk_hi hk_fe hk_bal
    rw [h_tok] at hk_fe hk_bal
    obtain ⟨h_succ_le, h_succ_key⟩ := hbody.after_fe k hk_lo hk_hi hk_bal hk_fe
    have h_succ_lt : k + 1 < j := by
      rcases Nat.lt_or_ge (k + 1) j with h | h
      · exact h
      · exfalso
        have h_eq : k + 1 = j := by omega
        rw [h_eq, h_end_tok] at h_succ_key
        cases h_succ_key
    exact ⟨h_succ_lt, by rw [h_tok]; exact h_succ_key⟩
  · rw [h_tok]; simp [flowBracketBalance]

end L4YAML.Proofs.ParserWellBehaved
