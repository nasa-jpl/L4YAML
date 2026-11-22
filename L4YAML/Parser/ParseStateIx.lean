/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Indexed.TokenStream
public import L4YAML.Spec.YamlSpec
public import L4YAML.Parser.AnchorIndex

public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-! # `ParseStateIx` — Phase 3 Step 6a indexed parser state

## Role

Indexed twin of `L4YAML/Parser/State.lean`: the substrate over
which the indexed token parser (Step 6b) operates. Mirrors the
legacy `ParseState` API 1-to-1 with two type-level changes:

1. The state record is parameterised by `input : String` so the
   token stream is dependently typed:
   `tokens : Indexed.TokenStream input` rather than
   `tokens : Array (Positioned YamlToken)`.
2. Every accessor that read `Positioned.val` / `Positioned.pos`
   on the legacy side now reads `IxToken.token` / `IxToken.start`
   on the indexed side.

Everything else — anchor map, tag handles, `trackPositions`,
`currentPath`, `nodePositions`, `NodeProperties`, tag resolution,
`emptyNode`, `applyNodeFinalization`, `validateNodeProps` —
ports verbatim. Those helpers do not pattern-match on the token
storage layout; they manipulate `YamlValue` and `YamlPath`
state that is identical between the two parsers.

## Phase 3 Step 6a discipline

This file lands the **state record + navigation primitives +
token-consumption helpers + node-property scaffolding** with no
proofs. Step 6b clones the 14 mutually-recursive parser functions
over `ParseStateIx`; Step 6c–6d port the parser proofs. Step 6f
renames `ParseStateIx.lean` → `Parser/State.lean` (overwriting
the legacy file) and retargets `L4YAML.lean`.

## Staging-namespace convention

Same as Step 5 staging (`L4YAML.Scanner.Indexed`): this file
sits in `L4YAML.TokenParser.Indexed` so its `ParseState`,
`NodeProperties`, `emptyNode`, etc. do not collide with the
legacy `L4YAML.TokenParser` declarations while both are in the
build.
-/

namespace L4YAML.TokenParser.Indexed

open L4YAML L4YAML.Indexed

/-! ## Parse State -/

/-- Indexed parse state: cursor into the indexed token stream
    plus per-document state.

    The type parameter `input : String` is inherited from the
    token stream — every token's `[start, stop)` is a verified
    offset into `input`, and the parser carries that invariant
    through its cursor.

    Auxiliary state (anchors, tag handles, position tracking)
    is unchanged from the legacy `ParseState`; only the token
    container differs. -/
structure ParseStateIx (input : String) where
  /-- Indexed token stream from the scanner -/
  tokens : Indexed.TokenStream input
  /-- Current index into the token array -/
  pos : Nat := 0
  /-- Accumulated anchor definitions -/
  anchors : Array (String × YamlValue) := #[]
  /-- Hash index of `anchors` (name → first binding); see `AnchorIndex`. -/
  anchorIndex : AnchorIndex anchors := by exact AnchorIndex.empty
  /-- Anchor names DECLARED by a `&` node property, whether or not the node the
      property decorates has finished parsing.  §7.1's only error is an anchor
      that does not *previously occur*, and §3.2.2.2 binds an alias to the most
      recent event carrying the anchor — for a collection that is its START
      event — so an alias may name the enclosing, still-open node (`&x [*x]`).
      `anchors` cannot answer that question: it stores resolved VALUES and so
      cannot exist before node finalization.  The scanner already keeps this
      set under the name `definedAnchors`. -/
  declaredAnchors : Array String := #[]
  /-- Hash index of `declaredAnchors`; see `DeclaredIndex`. -/
  declaredIndex : DeclaredIndex declaredAnchors := by exact DeclaredIndex.empty
  /-- Tag handle → prefix mapping declared via `%TAG` for the current document.
      §6.8.2.2: tag handles are local to the document.
      Each entry is `(handle, tagPrefix)` so `!handle!suffix` resolves to
      `tagPrefix ++ suffix` during node property parsing (§6.8.2). -/
  tagHandles : Array (String × String) := #[]
  /-- Whether to record node positions (G5c). Disabled by default;
      enabled by `parseYamlWithComments`. -/
  trackPositions : Bool := false
  /-- Current path from document root for node position tracking (G5c). -/
  currentPath : YamlPath := #[]
  /-- Accumulated node position map (G5c).
      Each entry is `(path, startPos, endPos)` for a parsed node. -/
  nodePositions : Array (YamlPath × YamlPos × YamlPos) := #[]

instance (input : String) : Inhabited (ParseStateIx input) where
  default := { tokens := Indexed.TokenStream.empty input }

/-- Create a `ParseStateIx` positioned at the start of the token stream. -/
def ParseStateIx.mk' {input : String} (tokens : Indexed.TokenStream input) :
    ParseStateIx input :=
  { tokens := tokens }

/-- Whether there are more tokens to consume. -/
def ParseStateIx.hasMore {input : String} (ps : ParseStateIx input) : Bool :=
  ps.pos < ps.tokens.size

/-- Peek at the current `IxToken` without consuming.

    The indexed analogue of legacy `peek?` returns the full
    `IxToken input` (including positions and bound proofs) rather
    than just the underlying `YamlToken`. The legacy `peek?` /
    `peekPos?` shape is recovered via `.map (·.token)` /
    `.map (·.start)` below. -/
def ParseStateIx.peekIx? {input : String} (ps : ParseStateIx input) :
    Option (Indexed.IxToken input) :=
  ps.tokens.get? ps.pos

/-- Peek at the current token value without consuming. -/
def ParseStateIx.peek? {input : String} (ps : ParseStateIx input) :
    Option YamlToken :=
  ps.peekIx?.map (·.token)

/-- Peek at the current token's source position. -/
def ParseStateIx.peekPos? {input : String} (ps : ParseStateIx input) :
    Option YamlPos :=
  ps.peekIx?.map (·.start)

/-- Peek at the token one past the current one, without consuming.
    Indexed twin of `ParseState.peekNext?` — used for the two-token
    lookahead that distinguishes a scanner-inserted retroactive `key`
    marker (`key` immediately followed by `value`) from a genuine next
    map entry. -/
def ParseStateIx.peekNext? {input : String} (ps : ParseStateIx input) :
    Option YamlToken :=
  (ps.tokens.get? (ps.pos + 1)).map (·.token)

/-- Advance past the current token. -/
def ParseStateIx.advance {input : String} (ps : ParseStateIx input) :
    ParseStateIx input :=
  { ps with pos := ps.pos + 1 }

/-- Position of the last consumed token (for node span tracking, G5c). -/
def ParseStateIx.lastPos? {input : String} (ps : ParseStateIx input) :
    Option YamlPos :=
  if ps.pos > 0 then
    (ps.tokens.get? (ps.pos - 1)).map (·.start)
  else
    none

/-- Line number of the current token (for error reporting). -/
def ParseStateIx.currentLine {input : String} (ps : ParseStateIx input) : Nat :=
  match ps.peekPos? with
  | some p => p.line
  | none => 0

/-- Consume a specific token, error if mismatch.
    **Error**: `expectedToken` if the current token doesn't match `tok`. -/
def ParseStateIx.expect {input : String} (ps : ParseStateIx input)
    (tok : YamlToken) (desc : String) : Except ScanError (ParseStateIx input) :=
  match ps.peek? with
  | some t =>
    if BEq.beq t tok then .ok ps.advance
    else .error (.expectedToken desc ps.currentLine (some (toString (repr t))))
  | none => .error (.expectedToken desc ps.currentLine none)

/-- Try to consume a specific token if present. Returns `(true, advanced)` or `(false, unchanged)`. -/
def ParseStateIx.tryConsume {input : String} (ps : ParseStateIx input)
    (tok : YamlToken) : (Bool × ParseStateIx input) :=
  match ps.peek? with
  | some t => if BEq.beq t tok then (true, ps.advance) else (false, ps)
  | none => (false, ps)

/-- Record that `&name` has occurred, before the node it decorates is complete.
    Indexed twin of `L4YAML.ParseState.declareAnchor`. -/
def ParseStateIx.declareAnchor {input : String} (ps : ParseStateIx input)
    (name : String) : ParseStateIx input :=
  { ps with declaredAnchors := ps.declaredAnchors.push name,
            declaredIndex := ps.declaredIndex.push name }

/-- `declareAnchor` writes only `declaredAnchors`; every other field, and so
    every reading a positional proof takes, is untouched.  `declareAnchorOpt`
    is its only caller, so these fire only under the node-properties stage. -/
@[simp] lemma ParseStateIx.declareAnchor_pos {input : String} (ps : ParseStateIx input) (name : String) :
    (ps.declareAnchor name).pos = ps.pos := rfl

@[simp] lemma ParseStateIx.declareAnchor_tokens {input : String} (ps : ParseStateIx input) (name : String) :
    (ps.declareAnchor name).tokens = ps.tokens := rfl

@[simp] lemma ParseStateIx.declareAnchor_anchors {input : String} (ps : ParseStateIx input) (name : String) :
    (ps.declareAnchor name).anchors = ps.anchors := rfl

@[simp] lemma ParseStateIx.declareAnchor_tagHandles {input : String} (ps : ParseStateIx input) (name : String) :
    (ps.declareAnchor name).tagHandles = ps.tagHandles := rfl

@[simp] lemma ParseStateIx.declareAnchor_trackPositions {input : String} (ps : ParseStateIx input) (name : String) :
    (ps.declareAnchor name).trackPositions = ps.trackPositions := rfl

@[simp] lemma ParseStateIx.declareAnchor_nodePositions {input : String} (ps : ParseStateIx input) (name : String) :
    (ps.declareAnchor name).nodePositions = ps.nodePositions := rfl

@[simp] lemma ParseStateIx.declareAnchor_currentPath {input : String} (ps : ParseStateIx input) (name : String) :
    (ps.declareAnchor name).currentPath = ps.currentPath := rfl

/-- Declare the anchor a node's properties carry, if they carry one.

    One application rather than a `match` at `parseNodeProperties`' tail, so
    that the shape of its result — `.ok (props, state)` — is the shape every
    proof about that stage already reasons about. -/
def ParseStateIx.declareAnchorOpt {input : String} (ps : ParseStateIx input) :
    Option String → ParseStateIx input
  | none => ps
  | some name => ps.declareAnchor name

@[simp] lemma ParseStateIx.declareAnchorOpt_none {input : String}
    (ps : ParseStateIx input) : ps.declareAnchorOpt none = ps := rfl

@[simp] lemma ParseStateIx.declareAnchorOpt_some {input : String}
    (ps : ParseStateIx input) (name : String) :
    ps.declareAnchorOpt (some name) = ps.declareAnchor name := rfl

/-- Register an anchor definition `&name` with its resolved value for alias lookup.

    The value is stripped (anchor annotation removed), adapted for any flow
    context, and then resolved (aliases expanded from the current anchor map)
    before storing.  This ensures:
    - Transitive alias chains resolve correctly (`*b → [*a, world] → [hello, world]`)
    - Anchor map values compare equal to plain values (no stale `anchor := some name`)

    Cleaning runs on the raw value, *before* alias substitution, so it costs
    O(size of the anchor's own syntax) and the substituted anchor values stay
    shared rather than being rebuilt node by node.  Every stored value is
    already a fixed point of `stripAnchors ∘ adaptForFlowContext`, so this is
    the same value the resolve-first order produced
    (`Algebra.Value.cleaned_resolveAliases_comm`); only the cost differs.
-/
def ParseStateIx.addAnchor {input : String} (ps : ParseStateIx input)
    (name : String) (val : YamlValue) : ParseStateIx input :=
  let cleaned := (val.stripAnchors.adaptForFlowContext).resolveAliasesWith ps.anchorIndex.find?
  { ps with anchors := ps.anchors.push (name, cleaned),
            anchorIndex := ps.anchorIndex.push name cleaned }

/-- `addAnchor` stores the value `resolveAliases` would compute (clean first, then resolve): the index
    only changes how the first-match lookup is performed. -/
@[simp] lemma ParseStateIx.addAnchor_anchors {input : String} (ps : ParseStateIx input) (name : String) (val : YamlValue) :
    (ps.addAnchor name val).anchors =
      ps.anchors.push (name, (val.stripAnchors.adaptForFlowContext).resolveAliases ps.anchors) := by
  simp [ParseStateIx.addAnchor]

/-! ## Node Properties -/

/-- Parsed optional node properties (anchor and/or tag). -/
structure NodeProperties where
  anchor : Option String := none
  tag : Option String := none
  /-- Set when two anchors appeared before the same node.  The check is
      deferred to `parseNode` so that collection-start tokens (which arise
      from scanner retroactive insertion) can disambiguate the two anchors
      into collection-anchor vs key-anchor (see 6BFJ). -/
  hadDuplicateAnchor : Bool := false
  deriving Repr, BEq, Inhabited

/-- Resolve a tag shorthand using the `%TAG` handle→prefix mapping (§6.8.2).

    - **Verbatim** (`handle = ""`): pass through the suffix as a raw URI.
    - **Declared handle** (found in `tagHandles`): expand to `prefix ++ suffix`.
    - **Default secondary** (`!!` without explicit `%TAG !!`): keep shorthand
      `"!!" ++ suffix` to match the old parser's convention (see README §10d).
    - **Default primary** (`!` without explicit `%TAG !`): keep `"!" ++ suffix`. -/
@[yaml_spec "6.8.2" 99 "c-ns-shorthand-tag"]
def resolveTag (tagHandles : Array (String × String))
    (handle suffix : String) : String :=
  if handle == "" && suffix != "" then suffix
  else
    match tagHandles.find? (·.1 == handle) with
    | some (_, pfx) => pfx ++ suffix
    | none =>
      if handle == "!!" then "!!" ++ suffix
      else handle ++ suffix

/-- Parse node properties: optional anchor and tag in either order.

    **Implements** (YAML 1.2.2 §6.9, §6.8.2):
    - `[96] c-ns-properties(n,c)` = `(c-ns-tag-property ... | c-ns-anchor-property ...)`
    - `[101] c-ns-anchor-property` = `"&" ns-anchor-name`
    - `[96-99] c-ns-tag-property` = `c-verbatim-tag | c-ns-shorthand-tag | c-non-specific-tag`

    Validates that non-builtin tag handles (`!`, `!!`) were declared
    via `%TAG` in the current document (§6.8.2.2).
    Flags duplicate anchors on the same node (§6.9.2) via `hadDuplicateAnchor`;
    the actual rejection is deferred to `parseNode` so that collection-start
    tokens from scanner retroactive insertion can disambiguate (see 6BFJ).

    **Pre**: Parse state at potential anchor/tag tokens.
    **Post**: Returns `(NodeProperties, advanced state)` — at most one anchor and one tag.
    **Error**: `undeclaredTagHandle` (named handle not in `%TAG` declarations). -/
@[yaml_spec "6.9" 96 "c-ns-properties(n,c)"]
def parseNodeProperties {input : String} (ps : ParseStateIx input) :
    Except ScanError (NodeProperties × ParseStateIx input) := do
  let mut ps := ps
  let mut props : NodeProperties := {}
  for _ in [:2] do
    match ps.peek? with
    | some (.anchor name) =>
      if props.anchor.isSome then
        props := { props with hadDuplicateAnchor := true }
      props := { props with anchor := some name }
      ps := ps.advance
    | some (.tag handle suffix) =>
      if handle != "" && handle != "!" && handle != "!!" then
        if !ps.tagHandles.any (·.1 == handle) then
          let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
          throw (.undeclaredTagHandle handle pos.line pos.col)
      let fullTag := resolveTag ps.tagHandles handle suffix
      props := { props with tag := some fullTag }
      ps := ps.advance
    | _ => break
  -- §3.2.2.2/§7.1: the anchor OCCURS at the node's start event, so it is
  -- already visible to an alias INSIDE the node it decorates (`&x [*x]`).
  -- The declaration is taken from the COMPUTED properties rather than from the
  -- loop, because the start event carries only the last `&`: a superseded
  -- `&a` in `&a &b` — which §6.9.2 tolerates on collection content — names no
  -- node, and so must not become aliasable.  `addAnchor`'s value table answers
  -- a different question and is written later, at `applyNodeFinalization`.
  return (props, ps.declareAnchorOpt props.anchor)

/-! ## Empty Node -/

/-- YAML's implicit null for absent nodes. -/
@[yaml_spec "7.2" 105 "e-scalar",
  yaml_spec "7.2" 106 "e-node"]
def emptyNode : YamlValue :=
  YamlValue.scalar { content := "", style := .plain }

/-! ## Node Finalization Helper -/

/-- The G5c path segment a mapping key contributes; non-scalar keys read as `"0"`.
    A named def so parser bodies carry no `match` for proofs to case-split. -/
@[simp] def keyPathSegment (key : YamlValue) : String :=
  match key with | .scalar s => s.content | _ => "0"

/-- Attach `props` to a collection node that carries no properties yet.
    Kept out of `applyNodeFinalization` so that its equation lemmas need no
    case split on `val`. -/
@[simp] def applyNodeProps (val : YamlValue) (props : NodeProperties) : YamlValue :=
  match val with
  | YamlValue.sequence style items none none =>
    YamlValue.sequence style items props.tag props.anchor
  | YamlValue.mapping style pairs none none =>
    YamlValue.mapping style pairs props.tag props.anchor
  | other => other

/-- Apply node properties, register anchors, and record G5c positions.

    This is the pure tail of `parseNode` after content dispatch.
    Extracted to simplify proofs (see legacy `applyNodeFinalization_scannable`;
    the indexed analogue lands in Step 6c). -/
def applyNodeFinalization {input : String}
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) : (YamlValue × ParseStateIx input) :=
  let val := applyNodeProps val props
  let ps := match props.anchor with
    | some name => ps.addAnchor name val
    | none => ps
  let ps := if ps.trackPositions then
      let nodeEndPos := ps.lastPos?.getD nodeStartPos
      { ps with nodePositions := ps.nodePositions.push (ps.currentPath, nodeStartPos, nodeEndPos) }
    else ps
  (val, ps)

/-! ## Property-validation helper -/

/-- Validate node properties after parsing (extracted from `parseNode`
    for Pattern 4b mitigation).

    - §8.2.2 [200]: Block collections must start on a new line after
      node properties. Properties and block collection start on the
      same line is an error.
    - §6.9.2: Duplicate anchors are rejected on scalar/empty content
      but tolerated on collection-start content (block/flow seq/map,
      block entry). -/
def validateNodeProps {input : String} (ps : ParseStateIx input)
    (prePropPos : Nat) (props : NodeProperties) : Except ScanError Unit := do
  match ps.peek? with
  | some .blockSequenceStart | some .blockMappingStart =>
    if ps.pos > prePropPos then
      match ps.tokens.get? (ps.pos - 1) with
      | some lastPropTok =>
        let blockPos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
        if lastPropTok.start.line == blockPos.line then
          throw (.trailingContent blockPos.line blockPos.col)
      | none => pure ()
  | _ => pure ()
  if props.hadDuplicateAnchor then
    match ps.peek? with
    | some .blockSequenceStart | some .blockMappingStart
    | some .flowSequenceStart  | some .flowMappingStart
    | some .blockEntry => pure ()
    | _ => throw (.duplicateAnchor ps.currentLine)

end L4YAML.TokenParser.Indexed

end Blanket
