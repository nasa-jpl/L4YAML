/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Indexed.TokenStream
import L4YAML.Spec.YamlSpec

/-! # `ParseStateIx` — Phase 3 Step 6a indexed parser state (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

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

/-- Register an anchor definition `&name` with its resolved value for alias lookup.

    The value is resolved (aliases expanded from the current anchor map)
    and stripped (anchor annotation removed) before storing.  This ensures:
    - Transitive alias chains resolve correctly (`*b → [*a, world] → [hello, world]`)
    - Anchor map values compare equal to plain values (no stale `anchor := some name`)
-/
def ParseStateIx.addAnchor {input : String} (ps : ParseStateIx input)
    (name : String) (val : YamlValue) : ParseStateIx input :=
  let cleaned := ((val.resolveAliases ps.anchors).stripAnchors).adaptForFlowContext
  { ps with anchors := ps.anchors.push (name, cleaned) }

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
  return (props, ps)

/-! ## Empty Node -/

/-- YAML's implicit null for absent nodes. -/
@[yaml_spec "7.2" 105 "e-scalar",
  yaml_spec "7.2" 106 "e-node"]
def emptyNode : YamlValue :=
  YamlValue.scalar { content := "", style := .plain }

/-! ## Node Finalization Helper -/

/-- Apply node properties, register anchors, and record G5c positions.

    This is the pure tail of `parseNode` after content dispatch.
    Extracted to simplify proofs (see legacy `applyNodeFinalization_scannable`;
    the indexed analogue lands in Step 6c). -/
def applyNodeFinalization {input : String}
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) : (YamlValue × ParseStateIx input) :=
  let val := match val with
    | YamlValue.sequence style items none none =>
      YamlValue.sequence style items props.tag props.anchor
    | YamlValue.mapping style pairs none none =>
      YamlValue.mapping style pairs props.tag props.anchor
    | other => other
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
