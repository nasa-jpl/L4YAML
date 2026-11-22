/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Token.Token
public import L4YAML.Spec.YamlSpec
public import L4YAML.Parser.AnchorIndex

public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-!
# Parser State

`ParseState` and its low-level accessors — the substrate on which the
recursive-descent token parser operates.

Split from the monolithic `Parser/TokenParser.lean` during Blueprint
Initiative 1 Phase 3 (Parser split).  See
`Blueprint/03-code-organization.md`.

## Scope

- Structural type: `ParseState`.
- Constructor: `ParseState.mk'`.
- Navigation accessors: `hasMore`, `peek?`, `peekPos?`, `advance`,
  `lastPos?`, `currentLine`.
- Token-consumption helpers: `expect`, `tryConsume`.
- Anchor registration: `addAnchor`.
- Node-property scaffolding: `NodeProperties`, `resolveTag`,
  `parseNodeProperties`, `emptyNode`, `applyNodeFinalization`,
  `validateNodeProps`.

Nothing in this file participates in the mutually-recursive descent
itself — those live in `Parser/TokenParser.lean`.
-/

namespace L4YAML.TokenParser

open L4YAML

/-! ## Parse State -/

/-- Parse state: current position in the token array plus per-document state.

    The parse state is a lightweight cursor over the scanner's token array.
    It also carries:
    - **anchors**: accumulated `&name` → value bindings for alias resolution
    - **tagHandles**: handles declared via `%TAG` in the current document (§6.8.2.2)
-/
structure ParseState where
  /-- Token array from the scanner -/
  tokens : Array (Positioned YamlToken)
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
  deriving Repr, Inhabited

/-- Create a `ParseState` positioned at the start of the token array. -/
def ParseState.mk' (tokens : Array (Positioned YamlToken)) : ParseState :=
  { tokens := tokens }

/-- Whether there are more tokens to consume. -/
def ParseState.hasMore (ps : ParseState) : Bool :=
  ps.pos < ps.tokens.size

/-- Peek at the current token value without consuming. -/
def ParseState.peek? (ps : ParseState) : Option YamlToken :=
  if ps.pos < ps.tokens.size then
    some ps.tokens[ps.pos]!.val
  else
    none

/-- Peek at the token one past the current one, without consuming.
    Used for the two-token lookahead that distinguishes a scanner-inserted
    retroactive `key` marker (`key` immediately followed by `value`) from a
    genuine next map entry. -/
def ParseState.peekNext? (ps : ParseState) : Option YamlToken :=
  if ps.pos + 1 < ps.tokens.size then
    some ps.tokens[ps.pos + 1]!.val
  else
    none

/-- Peek at the current token's source position. -/
def ParseState.peekPos? (ps : ParseState) : Option YamlPos :=
  if ps.pos < ps.tokens.size then
    some ps.tokens[ps.pos]!.pos
  else
    none

/-- Advance past the current token. -/
def ParseState.advance (ps : ParseState) : ParseState :=
  { ps with pos := ps.pos + 1 }

/-- Position of the last consumed token (for node span tracking, G5c). -/
def ParseState.lastPos? (ps : ParseState) : Option YamlPos :=
  if ps.pos > 0 && ps.pos ≤ ps.tokens.size then
    some ps.tokens[ps.pos - 1]!.pos
  else
    none

/-- Line number of the current token (for error reporting). -/
def ParseState.currentLine (ps : ParseState) : Nat :=
  match ps.peekPos? with
  | some p => p.line
  | none => 0

/-- Consume a specific token, error if mismatch.
    **Error**: `expectedToken` if the current token doesn't match `tok`. -/
def ParseState.expect (ps : ParseState) (tok : YamlToken) (desc : String) : Except ScanError ParseState :=
  match ps.peek? with
  | some t =>
    if BEq.beq t tok then .ok ps.advance
    else .error (.expectedToken desc ps.currentLine (some (toString (repr t))))
  | none => .error (.expectedToken desc ps.currentLine none)

/-- Try to consume a specific token if present. Returns `(true, advanced)` or `(false, unchanged)`. -/
def ParseState.tryConsume (ps : ParseState) (tok : YamlToken) : (Bool × ParseState) :=
  match ps.peek? with
  | some t => if BEq.beq t tok then (true, ps.advance) else (false, ps)
  | none => (false, ps)

/-- Record that `&name` has occurred, before the node it decorates is complete.

    §7.1's existence test reads this set; `addAnchor`'s value table answers a
    different question (what the alias resolves *to*) and is written later. -/
def ParseState.declareAnchor (ps : ParseState) (name : String) : ParseState :=
  { ps with declaredAnchors := ps.declaredAnchors.push name,
            declaredIndex := ps.declaredIndex.push name }

/-- `declareAnchor` writes only `declaredAnchors`; every other field, and so
    every reading a positional proof takes, is untouched.  `declareAnchorOpt`
    is its only caller, so these fire only under the node-properties stage. -/
@[simp] lemma ParseState.declareAnchor_pos (ps : ParseState) (name : String) :
    (ps.declareAnchor name).pos = ps.pos := rfl

@[simp] lemma ParseState.declareAnchor_tokens (ps : ParseState) (name : String) :
    (ps.declareAnchor name).tokens = ps.tokens := rfl

@[simp] lemma ParseState.declareAnchor_anchors (ps : ParseState) (name : String) :
    (ps.declareAnchor name).anchors = ps.anchors := rfl

@[simp] lemma ParseState.declareAnchor_tagHandles (ps : ParseState) (name : String) :
    (ps.declareAnchor name).tagHandles = ps.tagHandles := rfl

@[simp] lemma ParseState.declareAnchor_trackPositions (ps : ParseState) (name : String) :
    (ps.declareAnchor name).trackPositions = ps.trackPositions := rfl

@[simp] lemma ParseState.declareAnchor_nodePositions (ps : ParseState) (name : String) :
    (ps.declareAnchor name).nodePositions = ps.nodePositions := rfl

@[simp] lemma ParseState.declareAnchor_currentPath (ps : ParseState) (name : String) :
    (ps.declareAnchor name).currentPath = ps.currentPath := rfl

/-- Declare the anchor a node's properties carry, if they carry one.

    One application rather than a `match` at `parseNodeProperties`' tail, so
    that the shape of its result — `.ok (props, state)` — is the shape every
    proof about that stage already reasons about. -/
def ParseState.declareAnchorOpt (ps : ParseState) : Option String → ParseState
  | none => ps
  | some name => ps.declareAnchor name

@[simp] lemma ParseState.declareAnchorOpt_none (ps : ParseState) :
    ps.declareAnchorOpt none = ps := rfl

@[simp] lemma ParseState.declareAnchorOpt_some (ps : ParseState) (name : String) :
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
def ParseState.addAnchor (ps : ParseState) (name : String) (val : YamlValue) : ParseState :=
  let cleaned := (val.stripAnchors.adaptForFlowContext).resolveAliasesWith ps.anchorIndex.find?
  { ps with anchors := ps.anchors.push (name, cleaned),
            anchorIndex := ps.anchorIndex.push name cleaned }

/-- `addAnchor` stores the value `resolveAliases` would compute (clean first, then resolve): the index
    only changes how the first-match lookup is performed. -/
@[simp] lemma ParseState.addAnchor_anchors (ps : ParseState) (name : String) (val : YamlValue) :
    (ps.addAnchor name val).anchors =
      ps.anchors.push (name, (val.stripAnchors.adaptForFlowContext).resolveAliases ps.anchors) := by
  simp [ParseState.addAnchor]

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
def parseNodeProperties (ps : ParseState) : Except ScanError (NodeProperties × ParseState) := do
  let mut ps := ps
  let mut props : NodeProperties := {}
  for _ in [:2] do
    match ps.peek? with
    | some (.anchor name) =>
      -- §6.9.2: At most one anchor per node.  Flag the duplicate here;
      -- the actual rejection is deferred to `parseNode` (scalar branch)
      -- so that collection-content cases like 6BFJ can tolerate the
      -- scanner's consecutive-anchor quirk.
      if props.anchor.isSome then
        props := { props with hadDuplicateAnchor := true }
      props := { props with anchor := some name }
      ps := ps.advance
    | some (.tag handle suffix) =>
      -- §6.8.2.2: Named handles must be declared via %TAG.
      -- Built-in handles: "" (verbatim), "!" (primary), "!!" (secondary).
      if handle != "" && handle != "!" && handle != "!!" then
        if !ps.tagHandles.any (·.1 == handle) then
          let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
          throw (.undeclaredTagHandle handle pos.line pos.col)
      -- §6.8.2: Resolve tag shorthand via %TAG handle→prefix mapping.
      -- Declared handles expand to `prefix ++ suffix`; undeclared builtins
      -- keep shorthand form (`!!suffix`, `!suffix`) for old-parser compat.
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

/-! ## Node Finalization Helper

After content dispatch, `parseNode` applies node properties to non-scalar
values, registers anchors, and records G5c position tracking. These are
all pure `let` bindings (no `Except.bind`), extracted here so proofs can
reason about them independently of the recursive content dispatch. -/

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
    Extracted to simplify proofs: `applyNodeFinalization_scannable` shows
    that if the raw content value is `Scannable`, the finalized value is too. -/
def applyNodeFinalization
    (val : YamlValue) (ps : ParseState) (props : NodeProperties)
    (nodeStartPos : YamlPos) : (YamlValue × ParseState) :=
  -- Apply node properties to non-scalar nodes if not already set
  let val := applyNodeProps val props
  -- Register anchor
  let ps := match props.anchor with
    | some name => ps.addAnchor name val
    | none => ps
  -- G5c: record node position (only if tracking enabled)
  let ps := if ps.trackPositions then
      let nodeEndPos := ps.lastPos?.getD nodeStartPos
      { ps with nodePositions := ps.nodePositions.push (ps.currentPath, nodeStartPos, nodeEndPos) }
    else ps
  (val, ps)

/-! ## Property-validation helper

The block-start-on-same-line and duplicate-anchor checks were extracted
from `parseNode` (Pattern 4b mitigation) so they live with the rest of
the `NodeProperties` machinery. -/

/-- Validate node properties after parsing (extracted from `parseNode`
    for Pattern 4b mitigation).

    - §8.2.2 [200]: Block collections must start on a new line after
      node properties. Properties and block collection start on the
      same line is an error.
    - §6.9.2: Duplicate anchors are rejected on scalar/empty content
      but tolerated on collection-start content (block/flow seq/map,
      block entry). -/
def validateNodeProps (ps : ParseState) (prePropPos : Nat)
    (props : NodeProperties) : Except ScanError Unit := do
  match ps.peek? with
  | some .blockSequenceStart | some .blockMappingStart =>
    if ps.pos > prePropPos then
      let lastPropPos := ps.tokens[ps.pos - 1]!.pos
      let blockPos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
      if lastPropPos.line == blockPos.line then
        throw (.trailingContent blockPos.line blockPos.col)
  | _ => pure ()
  if props.hadDuplicateAnchor then
    match ps.peek? with
    | some .blockSequenceStart | some .blockMappingStart
    | some .flowSequenceStart  | some .flowMappingStart
    | some .blockEntry => pure ()
    | _ => throw (.duplicateAnchor ps.currentLine)

end L4YAML.TokenParser

end Blanket
