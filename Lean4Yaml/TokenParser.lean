/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Token
import Lean4Yaml.Scanner

/-!
# YAML Grammar Parser (Token → AST)

Phase 9: Token stream → `YamlValue` / `YamlDocument` AST.

The grammar parser implements the 54 syntactic-layer (S) productions from
YAML 1.2.2, operating on token arrays produced by the scanner. It never
touches raw characters — that eliminates the `detectMappingKeyImpl` false
positive class of bugs where character-level lookahead misidentified
mapping keys.

## Architecture

```
Array (Positioned YamlToken) ──→ TokenParser ──→ Array YamlDocument
```

The parser is a **pure function**:
  `Array (Positioned YamlToken) → Except ScanError (Array YamlDocument)`

Internally it uses `ParseState` (current index into the token array) and
operates via recursive descent, matching token patterns.

## Token Grammar (S-layer productions ~§9)

```
stream       ::= STREAM-START document* STREAM-END
document     ::= (directive* DOC-START)? node DOC-END?
node         ::= alias | (tag? anchor? | anchor? tag?) content
content      ::= scalar | sequence | mapping
sequence     ::= block_sequence | flow_sequence
mapping      ::= block_mapping  | flow_mapping
block_sequence ::= BLOCK-SEQ-START (BLOCK-ENTRY node?)* BLOCK-END
block_mapping  ::= BLOCK-MAP-START (KEY node? VALUE node?)* BLOCK-END
flow_sequence  ::= FLOW-SEQ-START (node (FLOW-ENTRY node)*)? FLOW-SEQ-END
flow_mapping   ::= FLOW-MAP-START (KEY? node? VALUE node? (FLOW-ENTRY ...)*)? FLOW-MAP-END
```

## References

- YAML 1.2.2 §9 (Document Stream)
- YAML 1.2.2 §7 (Flow Style Productions, S-layer)
- YAML 1.2.2 §8 (Block Style Productions, S-layer)
- libyaml `parser.c`
-/

namespace Lean4Yaml.TokenParser

open Lean4Yaml

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
  /-- Tag handles declared via `%TAG` for the current document.
      §6.8.2.2: tag handles are local to the document. -/
  tagHandles : Array String := #[]
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

/-- Peek at the current token's source position. -/
def ParseState.peekPos? (ps : ParseState) : Option YamlPos :=
  if ps.pos < ps.tokens.size then
    some ps.tokens[ps.pos]!.pos
  else
    none

/-- Advance past the current token. -/
def ParseState.advance (ps : ParseState) : ParseState :=
  { ps with pos := ps.pos + 1 }

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

/-- Register an anchor definition `&name` with its resolved value for alias lookup. -/
def ParseState.addAnchor (ps : ParseState) (name : String) (val : YamlValue) : ParseState :=
  { ps with anchors := ps.anchors.push (name, val) }

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
        if !ps.tagHandles.contains handle then
          let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
          throw (.undeclaredTagHandle handle pos.line pos.col)
      -- Store tags in shorthand form to match the old parser's convention.
      -- `!!suffix` stays as `!!suffix`; verbatim/named handles pass through.
      let fullTag := if handle == "" && suffix != "" then suffix
                     else if handle == "!!" then "!!" ++ suffix
                     else handle ++ suffix
      props := { props with tag := some fullTag }
      ps := ps.advance
    | _ => break
  return (props, ps)

/-! ## Empty Node -/

/-- YAML's implicit null for absent nodes. -/
def emptyNode : YamlValue :=
  YamlValue.scalar { content := "", style := .plain }

/-! ## Recursive Descent Parser

### Fuel-based recursion (P10.8a)

All 12 functions in the mutual block take a `fuel : Nat` parameter that
decreases by 1 at each function entry (via `match fuel with | fuel + 1 => ...`).
This structure prepares for P10.8b where `partial` will be removed and
`termination_by fuel` will close all obligations trivially.

Initial fuel is set by `parseDocument` to `4 * tokens.size + 4`, which
bounds the total number of mutual-function entries.  Each token generates
at most ~4 function entries (dispatch + collection + loop + sub-node).
-/

mutual

/-- Parse a YAML node — the core recursive descent function.

    **Implements** (YAML 1.2.2 §7–§8, S-layer):
    - `[196] s-l+block-node(n,c)`  = `s-l+block-in-block(n,c) | s-l+flow-in-block(n)`
    - `[197] s-l+flow-in-block(n)` = `s-separate(n+1,FLOW-OUT) ns-flow-node(n+1,FLOW-OUT) ...`
    - `[198] s-l+block-in-block(n,c)` = `s-l+block-scalar(n,c) | s-l+block-collection(n,c)`
    - `[159] ns-flow-node(n,c)` = `c-ns-alias-node | ns-flow-content(n,c) | (ns-flow-content ...)`

    Sequence: alias check → node properties → content dispatch (scalar / block collection / flow collection / empty).

    **Pre**: Parse state positioned at the first token of a node (alias, anchor, tag, or content).
    **Post**: Returns the parsed `YamlValue` and the advanced parse state.
    **Error**: `nestingDepthExceeded` (fuel exhausted), `trailingContent` (properties and block collection on same line),
    `duplicateAnchor` (two anchors on scalar/empty node, §6.9.2). -/
partial def parseNode (ps : ParseState) (fuel : Nat) : Except ScanError (YamlValue × ParseState) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  -- Check for alias
  match ps.peek? with
  | some (.alias name) =>
    return (YamlValue.alias name, ps.advance)
  | _ => pure ()
  -- Parse optional node properties
  let prePropPos := ps.pos
  let (props, ps) ← parseNodeProperties ps
  -- §8.2.2 [200]: After node properties, block collections require
  -- s-l-comments (line break) before starting. Properties and block
  -- collection start on the same line is an error.
  match ps.peek? with
  | some .blockSequenceStart | some .blockMappingStart =>
    if ps.pos > prePropPos then -- properties were consumed
      let lastPropPos := ps.tokens[ps.pos - 1]!.pos
      let blockPos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
      if lastPropPos.line == blockPos.line then
        throw (.trailingContent blockPos.line blockPos.col)
  | _ => pure ()
  -- §6.9.2: Reject duplicate anchors when the content is a scalar (or empty
  -- node).  Collection-start content (mapping/sequence) tolerates the
  -- duplicate because the scanner's single-simpleKey design sometimes
  -- places a collection-anchor and a key-anchor consecutively in the
  -- token stream (see 6BFJ); the first anchor is silently assigned to
  -- the collection.
  if props.hadDuplicateAnchor then
    match ps.peek? with
    | some .blockSequenceStart | some .blockMappingStart
    | some .flowSequenceStart  | some .flowMappingStart
    | some .blockEntry => pure ()   -- collection: tolerate
    | _ => throw (.duplicateAnchor ps.currentLine)  -- scalar/empty: reject
  -- Parse content
  let (val, ps) ← match ps.peek? with
    | some (YamlToken.scalar content style) =>
      .ok (YamlValue.scalar { content, style, tag := props.tag, anchor := props.anchor }, ps.advance)
    | some .blockSequenceStart => parseBlockSequence ps fuel
    | some .blockMappingStart => parseBlockMapping ps fuel
    | some .blockEntry =>
      -- Implicit block sequence: libyaml/our scanner omits BLOCK-SEQUENCE-START
      -- when block entries sit at the same indent as the containing mapping key.
      parseImplicitBlockSequence ps fuel
    | some .flowSequenceStart => parseFlowSequence ps fuel
    | some .flowMappingStart => parseFlowMapping ps fuel
    | _ =>
      -- Empty node with possible properties
      .ok (YamlValue.scalar { content := "", style := .plain, tag := props.tag, anchor := props.anchor }, ps)
  -- Apply node properties to non-scalar nodes if not already set
  let val := match val with
    | YamlValue.sequence style items none none =>
      YamlValue.sequence style items props.tag props.anchor
    | YamlValue.mapping style pairs none none =>
      YamlValue.mapping style pairs props.tag props.anchor
    | other => other
  -- Register anchor
  let ps := match props.anchor with
    | some name => ps.addAnchor name val
    | none => ps
  .ok (val, ps)

/-- Parse a block sequence.

    **Implements** (YAML 1.2.2 §8.2.1):
    - `[186] l+block-sequence(n)` = `(s-indent(n+m) c-l-block-seq-entry(n+m))+`
    - `[187] c-l-block-seq-entry(n)` = `"-" s-l+block-indented(n,BLOCK-IN)`

    Token grammar: `BLOCK-SEQ-START (BLOCK-ENTRY node?)* BLOCK-END`

    **Pre**: Current token is `blockSequenceStart`.
    **Post**: Consumes through `blockEnd`, returns `YamlValue.sequence .block items`. -/
partial def parseBlockSequence (ps : ParseState) (fuel : Nat) : Except ScanError (YamlValue × ParseState) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance  -- consume blockSequenceStart
  let (items, ps) ← parseBlockSequenceLoop ps fuel #[]
  let ps := match ps.peek? with
    | some .blockEnd => ps.advance
    | _ => ps
  .ok (YamlValue.sequence .block items, ps)

/-- Tail-recursive loop for block sequence entries. -/
partial def parseBlockSequenceLoop (ps : ParseState) (fuel : Nat)
    (items : Array YamlValue) : Except ScanError (Array YamlValue × ParseState) := do
  match fuel with
  | 0 => .ok (items, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .blockEntry =>
      let ps := ps.advance
      match ps.peek? with
      | some .blockEntry | some .blockEnd | none =>
        parseBlockSequenceLoop ps fuel (items.push emptyNode)
      | _ => do
        let (val, ps) ← parseNode ps fuel
        parseBlockSequenceLoop ps fuel (items.push val)
    | _ => .ok (items, ps)

/-- Parse an implicit block sequence (no `BLOCK-SEQUENCE-START` token).

    **Implements** (YAML 1.2.2 §8.2.1):
    - `[186] l+block-sequence(n)` — variant where the scanner omits
      `BLOCK-SEQUENCE-START` because block entries sit at the same indent
      level as the containing mapping key (matching libyaml behaviour).

    There is no corresponding `BLOCK-END` for this sequence; entries are
    terminated by a `key`, `blockEnd`, or `streamEnd` token belonging to
    the parent structure.

    **Pre**: Current token is `blockEntry` without a preceding `blockSequenceStart`.
    **Post**: Consumes entries until parent-structure delimiter, returns
    `YamlValue.sequence .block items`. -/
partial def parseImplicitBlockSequence (ps : ParseState) (fuel : Nat) : Except ScanError (YamlValue × ParseState) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let (items, ps) ← parseImplicitBlockSequenceLoop ps fuel #[]
  -- No blockEnd to consume — the parent mapping owns it.
  .ok (YamlValue.sequence .block items, ps)

/-- Tail-recursive loop for implicit block sequence entries. -/
partial def parseImplicitBlockSequenceLoop (ps : ParseState) (fuel : Nat)
    (items : Array YamlValue) : Except ScanError (Array YamlValue × ParseState) := do
  match fuel with
  | 0 => .ok (items, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .blockEntry =>
      let ps := ps.advance
      match ps.peek? with
      | some .blockEntry | some .blockEnd | some .key | none =>
        parseImplicitBlockSequenceLoop ps fuel (items.push emptyNode)
      | _ => do
        let (val, ps) ← parseNode ps fuel
        parseImplicitBlockSequenceLoop ps fuel (items.push val)
    | _ => .ok (items, ps)

/-- Parse a block mapping.

    **Implements** (YAML 1.2.2 §8.2.2):
    - `[188] l+block-mapping(n)` = `(s-indent(n+m) ns-l-block-map-entry(n+m))+`
    - `[189] ns-l-block-map-entry(n)` = `c-l-block-map-explicit-entry(n) | ns-l-block-map-implicit-entry(n)`
    - `[192] ns-l-block-map-implicit-entry(n)` = `(ns-s-implicit-yaml-key ... | e-node) c-l-block-map-implicit-value(n)`

    Token grammar: `BLOCK-MAP-START (KEY node? VALUE node?)* BLOCK-END`

    Handles both explicit (`?` key) and implicit key entries.  Enforces:
    - §8.2.2 [200]: block collections require line break before content
    - §8.2.1: value node properties on new line must be more indented than key

    **Pre**: Current token is `blockMappingStart`.
    **Post**: Consumes through `blockEnd`, returns `YamlValue.mapping .block pairs`. -/
partial def parseBlockMapping (ps : ParseState) (fuel : Nat) : Except ScanError (YamlValue × ParseState) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance  -- consume blockMappingStart
  let (pairs, ps) ← parseBlockMappingLoop ps fuel #[]
  let ps := match ps.peek? with
    | some .blockEnd => ps.advance
    | _ => ps
  .ok (YamlValue.mapping .block pairs, ps)

/-- Tail-recursive loop for block mapping entries. -/
partial def parseBlockMappingLoop (ps : ParseState) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue)) : Except ScanError (Array (YamlValue × YamlValue) × ParseState) := do
  match fuel with
  | 0 => .ok (pairs, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .key => do
      -- §8.2.2 [200]: Block collections require s-l-comments (line break)
      -- before content. Save the key indicator line to detect
      -- implicit keys with block collections on the same line.
      let keyPos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
      let keyLine := keyPos.line
      let keyCol := keyPos.col
      let ps := ps.advance
      -- Parse key — check whether key has content (non-empty implicit key)
      let keyHasContent := match ps.peek? with
        | some .value | some .blockEnd => false
        | _ => true
      let (key, ps) ← if keyHasContent then
        parseNode ps fuel
      else
        .ok (emptyNode, ps)
      -- Parse value
      let (consumed, ps) := ps.tryConsume .value
      let (val, ps) ← if consumed then do
        -- §8.2.1: Value node properties on a new line must be more
        -- indented than the parent key. Reject anchors/tags at or
        -- below the key's column on a subsequent line (G9HC, H7J7).
        let valueLine := if ps.pos > 0 then ps.tokens[ps.pos - 1]!.pos.line else 0
        for i in [ps.pos : min (ps.pos + 2) ps.tokens.size] do
          match ps.tokens[i]!.val with
          | .anchor _ | .tag _ _ =>
            let propPos := ps.tokens[i]!.pos
            if propPos.line != valueLine && propPos.col <= keyCol then
              throw (.trailingContent propPos.line propPos.col)
          | _ => break
        match ps.peek? with
        | some .key | some .blockEnd | none => .ok (emptyNode, ps)
        | some .blockMappingStart | some .blockSequenceStart =>
          let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
          if keyHasContent && pos.line == keyLine then
            throw (.trailingContent pos.line pos.col)
          else
            parseNode ps fuel
        | _ => parseNode ps fuel
      else
        .ok (emptyNode, ps)
      parseBlockMappingLoop ps fuel (pairs.push (key, val))
    | some .value => do
      -- Implicit key (empty key)
      let ps := ps.advance
      let (val, ps) ← match ps.peek? with
        | some .key | some .blockEnd | none => .ok (emptyNode, ps)
        | _ => parseNode ps fuel
      parseBlockMappingLoop ps fuel (pairs.push (emptyNode, val))
    | _ => .ok (pairs, ps)

/-- Parse a flow sequence.

    **Implements** (YAML 1.2.2 §7.4.1):
    - `[109] c-flow-sequence(n,c)` = `"[" s-separate(n,c)? ns-s-flow-seq-entries(n,FLOW-IN)? "]"`
    - `[110] ns-s-flow-seq-entries(n,c)` = `ns-flow-seq-entry(n,c) ...`

    Token grammar: `FLOW-SEQ-START (node (FLOW-ENTRY node)*)? FLOW-SEQ-END`

    Supports implicit mappings inside flow sequences via `parseSinglePairMapping`.

    **Pre**: Current token is `flowSequenceStart`.
    **Post**: Consumes through `flowSequenceEnd`, returns `YamlValue.sequence .flow items`. -/
partial def parseFlowSequence (ps : ParseState) (fuel : Nat) : Except ScanError (YamlValue × ParseState) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance  -- consume flowSequenceStart
  let (items, ps) ← parseFlowSequenceLoop ps fuel #[]
  let ps := match ps.peek? with
    | some .flowSequenceEnd => ps.advance
    | _ => ps
  .ok (YamlValue.sequence .flow items, ps)

/-- Tail-recursive loop for flow sequence entries. -/
partial def parseFlowSequenceLoop (ps : ParseState) (fuel : Nat)
    (items : Array YamlValue) : Except ScanError (Array YamlValue × ParseState) := do
  match fuel with
  | 0 => .ok (items, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .flowSequenceEnd => .ok (items, ps)
    | _ => do
      let ps ← if items.size > 0 then
        match ps.peek? with
        | some .flowEntry => pure ps.advance
        | _ => return (items, ps)   -- no separator → end of entries
      else pure ps
      -- Check for implicit mapping in flow sequence: `key: value`
      match ps.peek? with
      | some .key => do
        let (mapVal, ps) ← parseSinglePairMapping ps fuel
        parseFlowSequenceLoop ps fuel (items.push mapVal)
      | some .flowSequenceEnd => .ok (items, ps)
      | _ => do
        let (val, ps) ← parseNode ps fuel
        parseFlowSequenceLoop ps fuel (items.push val)

/-- Parse a flow mapping.

    **Implements** (YAML 1.2.2 §7.4.2):
    - `[138] c-flow-mapping(n,c)` = `"{" s-separate(n,c)? ns-s-flow-map-entries(n,FLOW-IN)? "}"`
    - `[139] ns-s-flow-map-entries(n,c)` = `ns-flow-map-entry(n,c) ...`
    - `[140] ns-flow-map-entry(n,c)` = `("?" ... | ns-flow-map-implicit-entry(n,c))`

    Token grammar: `FLOW-MAP-START (entries)? FLOW-MAP-END`

    Handles explicit (`?` key) and implicit key entries.

    **Pre**: Current token is `flowMappingStart`.
    **Post**: Consumes through `flowMappingEnd`, returns `YamlValue.mapping .flow pairs`. -/
partial def parseFlowMapping (ps : ParseState) (fuel : Nat) : Except ScanError (YamlValue × ParseState) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance  -- consume flowMappingStart
  let (pairs, ps) ← parseFlowMappingLoop ps fuel #[]
  let ps := match ps.peek? with
    | some .flowMappingEnd => ps.advance
    | _ => ps
  .ok (YamlValue.mapping .flow pairs, ps)

/-- Tail-recursive loop for flow mapping entries. -/
partial def parseFlowMappingLoop (ps : ParseState) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue)) : Except ScanError (Array (YamlValue × YamlValue) × ParseState) := do
  match fuel with
  | 0 => .ok (pairs, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .flowMappingEnd => .ok (pairs, ps)
    | _ => do
      let ps ← if pairs.size > 0 then
        match ps.peek? with
        | some .flowEntry => pure ps.advance
        | _ => return (pairs, ps)   -- no separator → end of entries
      else pure ps
      match ps.peek? with
      | some .flowMappingEnd => .ok (pairs, ps)
      | some .key => do
        let ps := ps.advance
        let (key, ps) ← match ps.peek? with
          | some .value | some .flowEntry | some .flowMappingEnd =>
            .ok (emptyNode, ps)
          | _ => parseNode ps fuel
        let (consumed, ps) := ps.tryConsume .value
        let (val, ps) ← if consumed then
          match ps.peek? with
          | some .flowEntry | some .flowMappingEnd | none =>
            .ok (emptyNode, ps)
          | _ => parseNode ps fuel
        else
          .ok (emptyNode, ps)
        parseFlowMappingLoop ps fuel (pairs.push (key, val))
      | _ => do
        -- Implicit key: value without KEY token
        let (key, ps) ← parseNode ps fuel
        let (consumed, ps) := ps.tryConsume .value
        let (val, ps) ← if consumed then
          match ps.peek? with
          | some .flowEntry | some .flowMappingEnd | none =>
            .ok (emptyNode, ps)
          | _ => parseNode ps fuel
        else
          .ok (emptyNode, ps)
        parseFlowMappingLoop ps fuel (pairs.push (key, val))

/-- Parse a single key:value pair as an implicit mapping (in flow sequences).

    **Implements** (YAML 1.2.2 §7.4.1):
    - `[143] ns-flow-map-yaml-key-entry(n,c)` within a flow sequence context

    When the scanner emits a `key` token inside a flow sequence (e.g., `[key: value]`),
    the pair is wrapped as a single-entry flow mapping.

    **Pre**: Current token is `key` inside a flow sequence.
    **Post**: Consumes key, optional value, returns `YamlValue.mapping .flow #[(key, val)]`. -/
partial def parseSinglePairMapping (ps : ParseState) (fuel : Nat) : Except ScanError (YamlValue × ParseState) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance  -- consume KEY token
  let (key, ps) ← match ps.peek? with
    | some .value | some .flowEntry | some .flowSequenceEnd =>
      .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  let (consumed, ps) := ps.tryConsume .value
  let (val, ps) ← if consumed then
    match ps.peek? with
    | some .flowEntry | some .flowSequenceEnd | none =>
      .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  else
    .ok (emptyNode, ps)
  .ok (YamlValue.mapping .flow #[(key, val)], ps)

end -- mutual

/-! ## Stream-Level Grammar Table (§9.2)

YAML 1.2.2 §9.2 production [211] constrains the document stream:

```
l-yaml-stream ::=
  l-document-prefix* l-any-document?
  ( l-document-suffix+ l-document-prefix* l-any-document?
  | l-document-prefix* l-explicit-document?
  )*
```

After the first document, a bare document (no `---`) is only permitted
if the previous document was terminated by `...` (`l-document-suffix`).
Otherwise, the next document must be explicit (`---`) or a directive.
The `StreamState` type and `validNextToken` function encode this
constraint as a declarative grammar table for document boundary validation.
-/

/-- Stream-level state for document boundary validation (§9.2 [211]). -/
inductive StreamState where
  /-- Before or during the first document — any token is valid. -/
  | initial
  /-- After a document that was NOT terminated by `...`.
      Only `---`, `...`, directives, or end-of-stream are valid next. -/
  | afterDocument
  /-- After a `...` document-end marker.
      Any document type (including bare) is valid next. -/
  | afterDocumentEnd
  deriving Repr, BEq, Inhabited

/-- Declarative grammar table: which tokens are valid at each stream state?

    This directly encodes YAML 1.2.2 §9.2 [211].
    - `initial`: first document in the stream — any content is valid.
    - `afterDocumentEnd`: previous document ended with `...` — any content is valid.
    - `afterDocument`: previous document had no `...` — only explicit documents
      (`---`), document-end markers (`...`), directives, or stream-end are valid.
      Bare content (scalars, collection starters, anchors, tags) is rejected.

    Note: structural "continuation" tokens (`key`, `value`, `blockEnd`,
    `flowEntry`, `flowMappingEnd`, `flowSequenceEnd`) are allowed through
    because they may be artifacts of the scanner's retroactive KEY insertion
    in flow context — the parser will produce empty/harmless documents from
    them.  Only tokens that could genuinely *start* a bare document node
    (per §9.1.4 `l-bare-document` → `s-l+block-node`) are rejected. -/
def StreamState.validNextToken (state : StreamState) (tok : YamlToken) : Bool :=
  match state with
  | .initial         => true   -- first document: any token is valid
  | .afterDocumentEnd => true   -- after `...`: any document type is valid
  | .afterDocument    =>
    match tok with
    -- Tokens that start explicit/directive documents:
    | .documentStart       => true
    | .documentEnd         => true   -- another `...` (starts suffix cycle)
    | .streamEnd           => true   -- end of stream
    | .versionDirective .. => true   -- `%YAML` directive document
    | .tagDirective ..     => true   -- `%TAG` directive document
    -- Structural tokens (scanner/parser artifacts, not bare content):
    | .key                 => true
    | .value               => true
    | .blockEnd            => true
    | .flowEntry           => true
    | .flowMappingEnd      => true
    | .flowSequenceEnd     => true
    -- Bare content tokens — §9.2 violation:
    | .scalar ..           => false  -- plain/quoted scalar
    | .blockSequenceStart  => false  -- `- ...` at top level
    | .blockMappingStart   => false  -- implicit mapping start
    | .blockEntry          => false  -- `- ` block entry
    | .flowSequenceStart   => false  -- `[`
    | .flowMappingStart    => false  -- `{`
    | .anchor ..           => false  -- `&name`
    | .alias ..            => false  -- `*name`
    | .tag ..              => false  -- `!tag`
    | .comment ..          => true   -- comments are never content
    | .streamStart         => false  -- should never appear here

/-! ## Directive Parsing -/

/-- Parse directives (`%YAML`, `%TAG`) before a document start marker.

    **Implements** (YAML 1.2.2 §6.8):
    - `[82] l-directive` = `"%" ( ns-yaml-directive | ns-tag-directive | ... ) s-l-comments`

    Consumes consecutive directive tokens, returns an array of `Directive` values.

    **Pre**: Parse state at potential directive tokens.
    **Post**: Consumes all contiguous directive tokens, returns `(directives, advanced state)`. -/
def parseDirectives (ps : ParseState) : (Array Directive × ParseState) := Id.run do
  let mut ps := ps
  let mut dirs : Array Directive := #[]
  let fuel := ps.tokens.size - ps.pos
  for _ in [:fuel] do
    match ps.peek? with
    | some (.versionDirective major minor) =>
      dirs := dirs.push (.yaml s!"{major}.{minor}")
      ps := ps.advance
    | some (.tagDirective handle tagPrefix) =>
      dirs := dirs.push (.tag handle tagPrefix)
      ps := ps.advance
    | _ => break
  return (dirs, ps)

/-! ## Document Parsing -/

/-- Parse a single YAML document.

    **Implements** (YAML 1.2.2 §9.1):
    - `[205] l-any-document` = `l-directive-document | l-explicit-document | l-bare-document`
    - `[208] l-directive-document` = `l-directive+ l-explicit-document`
    - `[207] l-explicit-document` = `c-directives-end (l-bare-document | e-node s-l-comments)`
    - `[206] l-bare-document` = `s-l+block-node(-1,BLOCK-IN)`

    Sequence: directives → tag handle registration → optional `---` → root node.

    **Pre**: Parse state at the first token of a document (directive, `---`, or content).
    **Post**: Returns `YamlDocument` (value + directives + anchors) and advanced state.
    **Error**: `contentOnDocumentStartLine` (block collection on `---` line, §9.1.1). -/
def parseDocument (ps : ParseState) : Except ScanError (YamlDocument × ParseState) := do
  -- Optional directives
  let (dirs, ps) := parseDirectives ps
  -- §6.8.2.2: Tag handles are local to the document.
  -- Extract declared handles from this document's %TAG directives.
  let tagHandles := dirs.filterMap fun
    | .tag handle _ => some handle
    | _ => none
  let ps := { ps with tagHandles := tagHandles }
  -- Optional document start marker
  let docStartLine := if ps.peek? == some .documentStart then
    ps.peekPos?.map (·.line)
  else
    none
  let (_, ps) := ps.tryConsume .documentStart
  -- §9.1.1 [200]: Block collections require s-l-comments (line break)
  -- before content. A block mapping/sequence cannot start on the `---` line.
  if let some dsLine := docStartLine then
    match ps.peek? with
    | some .blockMappingStart | some .blockSequenceStart =>
      let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
      if pos.line == dsLine then
        throw (.contentOnDocumentStartLine pos.line pos.col)
    | _ => pure ()
  -- Parse the document's root node
  -- Initial fuel: 4 × token count + 4 bounds all mutual-function entries.
  -- Each token generates at most ~4 function entries in the recursion.
  let fuel := 4 * ps.tokens.size + 4
  let (val, ps) ← match ps.peek? with
    | some .documentEnd | some .streamEnd | none =>
      .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  -- Note: `documentEnd` (`...`) is NOT consumed here.
  -- It is consumed by `parseStream` to track document boundary state
  -- for §9.2 [211] validation.
  .ok ({ value := val, directives := dirs, anchors := ps.anchors }, ps)

/-! ## Stream Parsing -/

/-- Parse a complete YAML stream (multiple documents).

    **Implements** (YAML 1.2.2 §9.2):
    - `[211] l-yaml-stream` = `l-document-prefix* l-any-document? ( l-document-suffix+ ... | ... )*`

    Uses `StreamState` and `validNextToken` to enforce §9.2 [211] document
    boundary rules: after a document without `...`, only explicit documents
    (`---`), `...`, directives, or stream-end are valid.

    `scan ∘ parseStream` composes the full Phase 9 pipeline:
    `String → Except ScanError (Array YamlDocument)`

    **Pre**: Token array starts with `streamStart`.
    **Post**: Consumes through `streamEnd`, returns array of documents.
    **Error**: `invalidBareDocument` (bare content after non-`...`-terminated document, §9.2). -/
def parseStream (tokens : Array (Positioned YamlToken)) : Except ScanError (Array YamlDocument) := do
  let mut ps := ParseState.mk' tokens
  -- Expect stream start
  ps ← ps.expect .streamStart "STREAM-START"
  let mut docs : Array YamlDocument := #[]
  let mut streamState : StreamState := .initial
  let fuel := tokens.size
  for _ in [:fuel] do
    match ps.peek? with
    | some .streamEnd => break
    | none => break
    | some tok =>
      -- §9.2 [211] document boundary validation:
      -- After a document without `...`, only explicit documents are valid.
      if !streamState.validNextToken tok then
        let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
        throw (.invalidBareDocument pos.line pos.col)
      let savedPos := ps.pos
      let (doc, ps') ← parseDocument ps
      docs := docs.push doc
      ps := ps'
      -- Consume optional document-end marker (`...`) and update stream state.
      -- This determines what token types are valid at the next iteration.
      let (consumed, ps') := ps.tryConsume .documentEnd
      streamState := if consumed then .afterDocumentEnd else .afterDocument
      ps := ps'
      -- Stuck detection: if neither parseDocument nor tryConsume advanced
      -- the position, break to prevent infinite looping on unconsumed
      -- structural tokens (e.g., orphaned `key`/`value` from scanner).
      if ps.pos == savedPos then break
  .ok docs

/-! ## Convenience: Full Pipeline

YAML 1.2.2 §3.1 defines **Load** as the composition of two processes:
- **Parse**: character stream → serialization event tree
- **Compose**: serialization event tree → representation node graph

The *Raw* variants return the serialization tree (anchors + aliases preserved).
The standard variants apply Compose for backward compatibility.
-/

/-- Internal: scan + parse pipeline returning structured `ScanError`.

    **Implements**: Complete YAML Load pipeline (scan + parse).
    Composes `Scanner.scan` and `parseStream` into a single function.

    Callers who need machine-inspectable errors (e.g., for testing specific
    error categories) should use this directly. The public `parseYaml*`
    functions map errors to `String` at the API boundary. -/
def scanAndParse (input : String) : Except ScanError (Array YamlDocument) :=
  match Scanner.scan input with
  | .ok tokens => parseStream tokens
  | .error e => .error e

/--
Parse a YAML string into an array of documents (**serialization tree**).

**Implements** (YAML 1.2.2 §3.1):
- **Parse** step only — character stream → serialization event tree.

Returns documents with `.alias name` nodes and `anchor` fields preserved.
Each `YamlDocument` includes an `anchors` map that can be used by
`YamlDocument.compose` to resolve aliases.

**Error** boundary: `ScanError` → `String` mapping happens here. -/
def parseYamlRaw (input : String) : Except String (Array YamlDocument) :=
  match Scanner.scan input with
  | .ok tokens =>
    match parseStream tokens with
    | .ok docs => .ok docs
    | .error e => .error e.toString
  | .error e => .error e.toString

/--
Parse a YAML string into an array of documents (**representation graph**).

**Implements** (YAML 1.2.2 §3.1):
- Full **Load** = Parse (→ serialization tree) + Compose (→ representation graph).

Aliases are resolved and anchor annotations are stripped.
This is the main entry point for most use cases.

**Error** boundary: `ScanError` → `String` mapping happens here. -/
def parseYaml (input : String) : Except String (Array YamlDocument) :=
  match parseYamlRaw input with
  | .ok docs => .ok (docs.map YamlDocument.compose)
  | .error e => .error e

/--
Parse a YAML string expecting exactly one document (**serialization tree**).

Returns the raw document with `.alias` nodes and `anchor` fields preserved.
**Error**: `multipleDocuments` if more than one document is found. -/
def parseYamlSingleRaw (input : String) : Except String YamlDocument :=
  match parseYamlRaw input with
  | .ok docs =>
    if docs.size == 0 then .ok { value := YamlValue.null }
    else if docs.size == 1 then .ok docs[0]!
    else .error (ScanError.multipleDocuments docs.size).toString
  | .error e => .error e

/--
Parse a YAML string expecting exactly one document (**representation graph**).

Returns the value of the single document with aliases resolved and
anchor annotations stripped.
**Error**: `multipleDocuments` if more than one document is found. -/
def parseYamlSingle (input : String) : Except String YamlValue :=
  match parseYaml input with
  | .ok docs =>
    if docs.size == 0 then .ok YamlValue.null
    else if docs.size == 1 then .ok docs[0]!.value
    else .error (ScanError.multipleDocuments docs.size).toString
  | .error e => .error e

end Lean4Yaml.TokenParser
