/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Indexed.TokenStream
import L4YAML.Spec.YamlSpec
import L4YAML.Parser.ParseStateIx
import L4YAML.Parser.FuelIx

/-! # `TokenParserIx` — Phase 3 Step 6b indexed token parser (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

## Role

Indexed twin of `L4YAML/Parser/TokenParser.lean`: the 18-function
mutual block plus document-stream grammar (`StreamState`,
`validNextToken`, `parseDirectives`, `prepareDocumentState`,
`parseDocument`, `parseStreamLoop`, `parseStreamIx`) reparented
onto `ParseStateIx input` and `Indexed.TokenStream input`.

The per-rule logic is a near-verbatim clone of the legacy
parser; the only structural changes are:

1. **State type** — `ParseStateIx input` rather than `ParseState`.
   The `{input : String}` implicit parameter threads through
   every function so each `ParseStateIx` is dependently typed.
2. **Token accessor** — `IxToken.token` / `IxToken.start` rather
   than `Positioned.val` / `Positioned.pos`.
3. **Random-access reads** — replaced `ps.tokens[i]!` (which
   needs `Inhabited (IxToken input)`, blocked by the bound proof
   fields) with `ps.tokens.get? i` followed by `match`. See
   `parseBlockMappingEntryValue` for the only random-access site.

Output type is plain `Array YamlDocument` (no `input`
parameter): this is the L2 → L1 step of the four-stage pipeline,
where the type-level binding to `input` is erased.

## Phase 3 Step 6f cutover

At cutover, `TokenParserIx.lean` and `FuelIx.lean` are renamed
to `Parser/TokenParser.lean` / `Parser/Fuel.lean` (overwriting
the legacy files), the `Indexed` namespace suffix is dropped,
and the `Ix` suffixes (`parseStreamIx`, `initialFuelIx`) are
removed.

## Naming convention

Per-rule function names are unchanged from the legacy parser
(`parseNode`, `parseBlockSequence`, …) — the indexed twins live
in the `L4YAML.TokenParser.Indexed` namespace, so the unqualified
names do not collide. Only the top-level entry point gets a
suffix (`parseStreamIx`) so external callers can distinguish the
two parsers during the staging period.
-/

namespace L4YAML.TokenParser.Indexed

open L4YAML L4YAML.Indexed

/-! ## Recursive Descent Parser

### Fuel-based termination (P10.8a–b)

All functions in the mutual block take a `fuel : Nat` parameter
that decreases by 1 at each function entry (via
`match fuel with | fuel + 1 => ...`). Lean 4 infers termination
automatically from the structural decrease on `fuel`, so no
explicit `termination_by` annotations are needed.

Initial fuel is set by `parseDocument` to `4 * ps.tokens.size + 4`
(see `Parser/FuelIx.lean`). -/

set_option maxHeartbeats 400000 in
mutual

/-- Dispatch content parsing based on the current token.
    Indexed twin of `L4YAML.TokenParser.parseNodeContent`. -/
@[yaml_spec "7.5" 156 "ns-flow-yaml-content(n,c)",
  yaml_spec "7.5" 157 "c-flow-json-content(n,c)",
  yaml_spec "7.5" 158 "ns-flow-content(n,c)",
  yaml_spec "7.5" 159 "ns-flow-yaml-node(n,c)"]
def parseNodeContent {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (props : NodeProperties) :
    Except ScanError (YamlValue × ParseStateIx input) :=
  match ps.peek? with
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

/-- Parse a YAML node — the core recursive descent function.
    Indexed twin of `L4YAML.TokenParser.parseNode`. -/
@[yaml_spec "8.1" 196 "s-l+block-node(n,c)",
  yaml_spec "7.5" 161 "ns-flow-node(n,c)",
  yaml_spec "8.2.3" 197 "s-l+flow-in-block(n)",
  yaml_spec "8.2.3" 198 "s-l+block-in-block(n,c)",
  yaml_spec "8.2.3" 199 "s-l+block-scalar(n,c)",
  yaml_spec "8.2.3" 200 "s-l+block-collection(n,c)",
  yaml_spec "8.2.1" 185 "s-l+block-indented(n,c)",
  yaml_spec "8.2.1" 201 "seq-space(n,c)"]
def parseNode {input : String} (ps : ParseStateIx input) (fuel : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let nodeStartPos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
  match ps.peek? with
  | some (.alias name) =>
    if !ps.anchors.any (fun (n, _) => n == name) then
      throw (.undefinedAlias name nodeStartPos.line nodeStartPos.col)
    let ps := ps.advance
    let ps := if ps.trackPositions then
        let nodeEndPos := ps.lastPos?.getD nodeStartPos
        { ps with nodePositions := ps.nodePositions.push (ps.currentPath, nodeStartPos, nodeEndPos) }
      else ps
    return (YamlValue.alias name, ps)
  | _ => pure ()
  let prePropPos := ps.pos
  let (props, ps) ← parseNodeProperties ps
  validateNodeProps ps prePropPos props
  let (val, ps) ← parseNodeContent ps fuel props
  .ok (applyNodeFinalization val ps props nodeStartPos)

/-- Parse a block sequence.
    Indexed twin of `L4YAML.TokenParser.parseBlockSequence`. -/
@[yaml_spec "8.2.1" 183 "l+block-sequence(n)"]
def parseBlockSequence {input : String} (ps : ParseStateIx input) (fuel : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance
  let (items, ps) ← parseBlockSequenceLoop ps fuel #[]
  let ps := match ps.peek? with
    | some .blockEnd => ps.advance
    | _ => ps
  .ok (YamlValue.sequence .block items, ps)

/-- Tail-recursive loop for block sequence entries.
    Indexed twin of `L4YAML.TokenParser.parseBlockSequenceLoop`. -/
@[yaml_spec "8.2.1" 184 "c-l-block-seq-entry(n)"]
def parseBlockSequenceLoop {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (items : Array YamlValue) :
    Except ScanError (Array YamlValue × ParseStateIx input) := do
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
        let savedPath := ps.currentPath
        let ps := { ps with currentPath := savedPath.push (.index items.size) }
        let (val, ps) ← parseNode ps fuel
        let ps := { ps with currentPath := savedPath }
        parseBlockSequenceLoop ps fuel (items.push val)
    | _ => .ok (items, ps)

/-- Parse an implicit block sequence (no `BLOCK-SEQUENCE-START` token).
    Indexed twin of `L4YAML.TokenParser.parseImplicitBlockSequence`. -/
@[yaml_spec "8.2.1" 186 "ns-l-compact-sequence(n)"]
def parseImplicitBlockSequence {input : String} (ps : ParseStateIx input) (fuel : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let (items, ps) ← parseImplicitBlockSequenceLoop ps fuel #[]
  .ok (YamlValue.sequence .block items, ps)

/-- Tail-recursive loop for implicit block sequence entries.
    Indexed twin of `L4YAML.TokenParser.parseImplicitBlockSequenceLoop`. -/
def parseImplicitBlockSequenceLoop {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (items : Array YamlValue) :
    Except ScanError (Array YamlValue × ParseStateIx input) := do
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
        let savedPath := ps.currentPath
        let ps := { ps with currentPath := savedPath.push (.index items.size) }
        let (val, ps) ← parseNode ps fuel
        let ps := { ps with currentPath := savedPath }
        parseImplicitBlockSequenceLoop ps fuel (items.push val)
    | _ => .ok (items, ps)

/-- Parse a block mapping.
    Indexed twin of `L4YAML.TokenParser.parseBlockMapping`. -/
@[yaml_spec "8.2.2" 187 "l+block-mapping(n)"]
def parseBlockMapping {input : String} (ps : ParseStateIx input) (fuel : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance
  let (pairs, ps) ← parseBlockMappingLoop ps fuel #[]
  let ps := match ps.peek? with
    | some .blockEnd => ps.advance
    | _ => ps
  .ok (YamlValue.mapping .block pairs, ps)

/-- Parse the value in a block mapping entry after the key has been parsed.
    Indexed twin of `L4YAML.TokenParser.parseBlockMappingEntryValue`.

    Random-access reads of `ps.tokens` use `get?` (returning `Option`)
    rather than `[i]!` to avoid the `Inhabited (IxToken input)` obligation
    — `IxToken input` carries the `startLEStop` / `stopLEInput` proof
    fields, which block deriving `Inhabited`. See Reflection 61. -/
@[yaml_spec "8.2.2" 188 "ns-l-block-map-entry(n)"]
def parseBlockMappingEntryValue {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (keyHasContent : Bool) (keyLine keyCol : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  let (consumed, ps) := ps.tryConsume .value
  if consumed then do
    -- §8.2.1: Value node properties on a new line must be more
    -- indented than the parent key. Reject anchors/tags at or
    -- below the key's column on a subsequent line (G9HC, H7J7).
    let valueLine :=
      if ps.pos > 0 then
        match ps.tokens.get? (ps.pos - 1) with
        | some t => t.start.line
        | none => 0
      else 0
    for i in [ps.pos : min (ps.pos + 2) ps.tokens.size] do
      match ps.tokens.get? i with
      | some t =>
        match t.token with
        | .anchor _ | .tag _ _ =>
          if t.start.line != valueLine && t.start.col <= keyCol then
            throw (.trailingContent t.start.line t.start.col)
        | _ => break
      | none => break
    match ps.peek? with
    | some .key | some .blockEnd | none => .ok (emptyNode, ps)
    | some .blockMappingStart | some .blockSequenceStart =>
      -- §8.2.1 [200]: Block collections require a line break before
      -- content.  Reject `key: - item` or `a: b: c` on the same line.
      let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
      if keyHasContent && pos.line == keyLine then
        throw (.trailingContent pos.line pos.col)
      else
        parseNode ps fuel
    | _ => parseNode ps fuel
  else
    .ok (emptyNode, ps)

/-- Handle the `.key` branch of a block mapping iteration.
    Indexed twin of `L4YAML.TokenParser.handleBlockMappingKeyEntry`. -/
@[yaml_spec "8.2.2" 189 "c-l-block-map-explicit-entry(n)",
  yaml_spec "8.2.2" 190 "c-l-block-map-explicit-key(n)",
  yaml_spec "8.2.2" 193 "ns-s-block-map-implicit-key"]
def handleBlockMappingKeyEntry {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (pairIdx : Nat) :
    Except ScanError (YamlValue × YamlValue × ParseStateIx input) := do
  let keyPos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
  let keyLine := keyPos.line
  let keyCol := keyPos.col
  let ps := ps.advance
  let keyHasContent := match ps.peek? with
    | some .value | some .blockEnd => false
    | _ => true
  let (key, ps) ← if keyHasContent then
    parseNode ps fuel
  else
    .ok (emptyNode, ps)
  let keyContent := match key with | .scalar s => s.content | _ => s!"{pairIdx}"
  let savedPath := ps.currentPath
  let ps := { ps with currentPath := savedPath.push (.key keyContent) }
  let (val, ps) ← parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol
  let ps := { ps with currentPath := savedPath }
  .ok (key, val, ps)

/-- Handle the `.value` branch of a block mapping iteration (implicit key).
    Indexed twin of `L4YAML.TokenParser.handleBlockMappingValueEntry`. -/
@[yaml_spec "8.2.2" 191 "l-block-map-explicit-value(n)",
  yaml_spec "8.2.2" 194 "c-l-block-map-implicit-value(n)"]
def handleBlockMappingValueEntry {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (pairIdx : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  let ps := ps.advance
  let savedPath := ps.currentPath
  let ps := { ps with currentPath := savedPath.push (.key s!"{pairIdx}") }
  let (val, ps) ← match ps.peek? with
    | some .key | some .blockEnd | none => .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  let ps := { ps with currentPath := savedPath }
  .ok (val, ps)

/-- Tail-recursive loop for block mapping entries.
    Indexed twin of `L4YAML.TokenParser.parseBlockMappingLoop`. -/
@[yaml_spec "8.2.2" 192 "ns-l-block-map-implicit-entry(n)",
  yaml_spec "8.2.2" 195 "ns-l-compact-mapping(n)"]
def parseBlockMappingLoop {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue)) :
    Except ScanError (Array (YamlValue × YamlValue) × ParseStateIx input) := do
  match fuel with
  | 0 => .ok (pairs, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .key => do
      let (key, val, ps) ← handleBlockMappingKeyEntry ps fuel pairs.size
      parseBlockMappingLoop ps fuel (pairs.push (key, val))
    | some .value => do
      let (val, ps) ← handleBlockMappingValueEntry ps fuel pairs.size
      parseBlockMappingLoop ps fuel (pairs.push (emptyNode, val))
    | _ => .ok (pairs, ps)

/-- Parse a flow sequence.
    Indexed twin of `L4YAML.TokenParser.parseFlowSequence`. -/
@[yaml_spec "7.4.1" 137 "c-flow-sequence(n,c)"]
def parseFlowSequence {input : String} (ps : ParseStateIx input) (fuel : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance
  let (items, ps) ← parseFlowSequenceLoop ps fuel #[]
  match ps.peek? with
  | some .flowSequenceEnd => .ok (YamlValue.sequence .flow items, ps.advance)
  | _ => .error (.expectedToken "']'" ps.currentLine none)

/-- Tail-recursive loop for flow sequence entries.
    Indexed twin of `L4YAML.TokenParser.parseFlowSequenceLoop`. -/
@[yaml_spec "7.4.1" 138 "ns-s-flow-seq-entries(n,c)",
  yaml_spec "7.4.1" 139 "ns-flow-seq-entry(n,c)"]
def parseFlowSequenceLoop {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (items : Array YamlValue) :
    Except ScanError (Array YamlValue × ParseStateIx input) := do
  match fuel with
  | 0 => .ok (items, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .flowSequenceEnd => .ok (items, ps)
    | _ => do
      let ps ← if items.size > 0 then
        match ps.peek? with
        | some .flowEntry => pure ps.advance
        | _ => return (items, ps)
      else pure ps
      match ps.peek? with
      | some .key => do
        let savedPath := ps.currentPath
        let ps := { ps with currentPath := savedPath.push (.index items.size) }
        let (mapVal, ps) ← parseSinglePairMapping ps fuel
        let ps := { ps with currentPath := savedPath }
        parseFlowSequenceLoop ps fuel (items.push mapVal)
      | some .flowSequenceEnd => .ok (items, ps)
      | _ => do
        let savedPath := ps.currentPath
        let ps := { ps with currentPath := savedPath.push (.index items.size) }
        let (val, ps) ← parseNode ps fuel
        let ps := { ps with currentPath := savedPath }
        parseFlowSequenceLoop ps fuel (items.push val)

/-- Parse a flow mapping.
    Indexed twin of `L4YAML.TokenParser.parseFlowMapping`. -/
@[yaml_spec "7.4.2" 140 "c-flow-mapping(n,c)"]
def parseFlowMapping {input : String} (ps : ParseStateIx input) (fuel : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance
  let (pairs, ps) ← parseFlowMappingLoop ps fuel #[]
  match ps.peek? with
  | some .flowMappingEnd => .ok (YamlValue.mapping .flow pairs, ps.advance)
  | _ => .error (.expectedToken "'}'" ps.currentLine none)

/-- Parse the value part of a flow mapping entry.
    Indexed twin of `L4YAML.TokenParser.parseFlowMappingValue`. -/
@[yaml_spec "7.4.2" 149 "c-ns-flow-map-adjacent-value(n,c)"]
def parseFlowMappingValue {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (savedPath : YamlPath) (keyContent : String) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  let ps := { ps with currentPath := savedPath.push (.key keyContent) }
  let (_, ps) := ps.tryConsume .key
  let (consumed, ps) := ps.tryConsume .value
  let (val, ps) ← if consumed then
    match ps.peek? with
    | some .flowEntry | some .flowMappingEnd | none => .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  else .ok (emptyNode, ps)
  .ok (val, { ps with currentPath := savedPath })

/-- Parse the key in an explicit-key flow mapping entry.
    Indexed twin of `L4YAML.TokenParser.parseExplicitKey`. -/
@[yaml_spec "7.4.2" 143 "ns-flow-map-explicit-entry(n,c)"]
def parseExplicitKey {input : String} (ps : ParseStateIx input) (fuel : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) :=
  match ps.peek? with
  | some .value | some .flowEntry | some .flowMappingEnd =>
    .ok (emptyNode, ps)
  | _ => parseNode ps fuel

/-- Tail-recursive loop for flow mapping entries.
    Indexed twin of `L4YAML.TokenParser.parseFlowMappingLoop`. -/
@[yaml_spec "7.4.2" 141 "ns-s-flow-map-entries(n,c)",
  yaml_spec "7.4.2" 142 "ns-flow-map-entry(n,c)",
  yaml_spec "7.4.2" 144 "ns-flow-map-implicit-entry(n,c)",
  yaml_spec "7.4.2" 145 "ns-flow-map-yaml-key-entry(n,c)",
  yaml_spec "7.4.2" 146 "c-ns-flow-map-empty-key-entry(n,c)",
  yaml_spec "7.4.2" 155 "c-s-implicit-json-key(c)"]
def parseFlowMappingLoop {input : String} (ps : ParseStateIx input) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue)) :
    Except ScanError (Array (YamlValue × YamlValue) × ParseStateIx input) := do
  match fuel with
  | 0 => .ok (pairs, ps)
  | fuel + 1 =>
    match ps.peek? with
    | some .flowMappingEnd => .ok (pairs, ps)
    | _ => do
      let ps ← if pairs.size > 0 then
        match ps.peek? with
        | some .flowEntry => pure ps.advance
        | _ => return (pairs, ps)
      else pure ps
      match ps.peek? with
      | some .flowMappingEnd => .ok (pairs, ps)
      | some .key => do
        let ps := ps.advance
        let (key, ps) ← parseExplicitKey ps fuel
        let keyContent := match key with | .scalar s => s.content | _ => s!"{pairs.size}"
        let (val, ps) ← parseFlowMappingValue ps fuel ps.currentPath keyContent
        parseFlowMappingLoop ps fuel (pairs.push (key, val))
      | _ => do
        let (key, ps) ← parseNode ps fuel
        let keyContent := match key with | .scalar s => s.content | _ => s!"{pairs.size}"
        let (val, ps) ← parseFlowMappingValue ps fuel ps.currentPath keyContent
        parseFlowMappingLoop ps fuel (pairs.push (key, val))

/-- Parse a single key:value pair as an implicit mapping (in flow sequences).
    Indexed twin of `L4YAML.TokenParser.parseSinglePairMapping`. -/
@[yaml_spec "7.4.1" 150 "ns-flow-pair(n,c)",
  yaml_spec "7.4.2" 151 "ns-flow-pair-entry(n,c)",
  yaml_spec "7.4.2" 152 "ns-flow-pair-yaml-key-entry(n,c)",
  yaml_spec "7.4.2" 153 "c-ns-flow-pair-json-key-entry(n,c)"]
def parseSinglePairMapping {input : String} (ps : ParseStateIx input) (fuel : Nat) :
    Except ScanError (YamlValue × ParseStateIx input) := do
  match fuel with
  | 0 => .error (.nestingDepthExceeded ps.currentLine)
  | fuel + 1 => do
  let ps := ps.advance
  let (key, ps) ← match ps.peek? with
    | some .value | some .flowEntry | some .flowSequenceEnd =>
      .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  let keyContent := match key with | .scalar s => s.content | _ => "0"
  let savedPath := ps.currentPath
  let ps := { ps with currentPath := savedPath.push (.key keyContent) }
  let (consumed, ps) := ps.tryConsume .value
  let (val, ps) ← if consumed then
    match ps.peek? with
    | some .flowEntry | some .flowSequenceEnd | none =>
      .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  else
    .ok (emptyNode, ps)
  let ps := { ps with currentPath := savedPath }
  .ok (YamlValue.mapping .flow #[(key, val)], ps)

end -- mutual

/-! ## Stream-Level Grammar Table (§9.2)

The `StreamState` / `validNextToken` declarations are
input-independent (they only inspect `YamlToken` values, not
positions or the indexed container). Re-stating them inside
`L4YAML.TokenParser.Indexed` keeps the indexed parser
self-contained — at Step 6f cutover, the legacy copies are
deleted and these become the canonical declarations. -/

/-- Stream-level state for document boundary validation (§9.2 [211]).
    Indexed twin of `L4YAML.TokenParser.StreamState`. -/
inductive StreamState where
  | initial
  | afterDocument
  | afterDocumentEnd
  deriving Repr, BEq, Inhabited

/-- Declarative grammar table for document-boundary validation.
    Indexed twin of `L4YAML.TokenParser.StreamState.validNextToken`. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def StreamState.validNextToken (state : StreamState) (tok : YamlToken) : Bool :=
  match state with
  | .initial         => true
  | .afterDocumentEnd => true
  | .afterDocument    =>
    match tok with
    | .documentStart       => true
    | .documentEnd         => true
    | .streamEnd           => true
    | .versionDirective .. => true
    | .tagDirective ..     => true
    | .key                 => true
    | .value               => true
    | .blockEnd            => true
    | .flowEntry           => true
    | .flowMappingEnd      => true
    | .flowSequenceEnd     => true
    | .scalar ..           => false
    | .blockSequenceStart  => false
    | .blockMappingStart   => false
    | .blockEntry          => false
    | .flowSequenceStart   => false
    | .flowMappingStart    => false
    | .anchor ..           => false
    | .alias ..            => false
    | .tag ..              => false
    | .comment ..          => true
    | .streamStart         => false
    | .placeholder         => true

/-! ## Directive Parsing -/

/-- Parse directives (`%YAML`, `%TAG`) before a document start marker.
    Indexed twin of `L4YAML.TokenParser.parseDirectives`. -/
@[yaml_spec "6.8" 82 "l-directive"]
def parseDirectives {input : String} (ps : ParseStateIx input) :
    (Array Directive × ParseStateIx input) := Id.run do
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

/-- Prepare document state: parse directives, register tag handles,
    consume optional `---`, and validate block-collection-on-same-line.
    Indexed twin of `L4YAML.TokenParser.prepareDocumentState`. -/
@[yaml_spec "9.1.1" 202 "l-document-prefix"]
def prepareDocumentState {input : String} (ps : ParseStateIx input) :
    Except ScanError (Array Directive × ParseStateIx input) := do
  let (dirs, ps) := parseDirectives ps
  let tagHandles := dirs.filterMap fun
    | .tag handle tagPrefix => some (handle, tagPrefix)
    | _ => none
  let ps := { ps with tagHandles := tagHandles }
  let docStartLine := if ps.peek? == some .documentStart then
    ps.peekPos?.map (·.line)
  else
    none
  let (_, ps) := ps.tryConsume .documentStart
  if let some dsLine := docStartLine then
    match ps.peek? with
    | some .blockMappingStart | some .blockSequenceStart =>
      let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
      if pos.line == dsLine then
        throw (.contentOnDocumentStartLine pos.line pos.col)
    | _ => pure ()
  .ok (dirs, ps)

/-- Parse a single YAML document.
    Indexed twin of `L4YAML.TokenParser.parseDocument`. -/
@[yaml_spec "9.1" 210 "l-any-document",
  yaml_spec "9.1.3" 207 "l-bare-document",
  yaml_spec "9.1.4" 208 "l-explicit-document",
  yaml_spec "9.1.5" 209 "l-directive-document"]
def parseDocument {input : String} (ps : ParseStateIx input) :
    Except ScanError (YamlDocument × ParseStateIx input) := do
  let (dirs, ps) ← prepareDocumentState ps
  -- Inline `4 * ps.tokens.size + 4` for proof-friendliness; the named
  -- formula in `Parser/FuelIx.lean` exists for new tooling that wants to
  -- talk about fuel by name (see legacy `Parser/Fuel.lean` for the same
  -- inline-vs-named tradeoff).
  let fuel := 4 * ps.tokens.size + 4
  let (val, ps) ← match ps.peek? with
    | some .documentEnd | some .streamEnd | none =>
      .ok (emptyNode, ps)
    | _ => parseNode ps fuel
  .ok ({ value := val, directives := dirs, anchors := ps.anchors,
         nodePositions := ps.nodePositions }, ps)

/-! ## Stream Parsing -/

/-- Tail-recursive loop for `parseStreamIx`.
    Indexed twin of `L4YAML.TokenParser.parseStreamLoop`. -/
def parseStreamLoop {input : String} (ps : ParseStateIx input) (docs : Array YamlDocument)
    (streamState : StreamState) (fuel : Nat) :
    Except ScanError (Array YamlDocument) :=
  match fuel with
  | 0 => .ok docs
  | fuel + 1 =>
    match ps.peek? with
    | some .streamEnd => .ok docs
    | none => .ok docs
    | some tok =>
      if !streamState.validNextToken tok then
        let pos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
        .error (.invalidBareDocument pos.line pos.col)
      else
        let savedPos := ps.pos
        match parseDocument ps with
        | .error e => .error e
        | .ok (doc, ps') =>
          let docs := docs.push doc
          let ps := { ps' with anchors := #[], nodePositions := #[], currentPath := #[] }
          let (consumed, ps) := ps.tryConsume .documentEnd
          let streamState := if consumed then .afterDocumentEnd else .afterDocument
          if ps.pos == savedPos then .ok docs
          else parseStreamLoop ps docs streamState fuel

/-- Parse a complete YAML stream (multiple documents) from an indexed
    token stream.

    Indexed twin of `L4YAML.TokenParser.parseStream`. The output type is
    plain `Array YamlDocument` (no `input` parameter): this is the
    L2 → L1 step where the type-level binding to `input` is erased.

    **Pre**: Token stream starts with `streamStart`.
    **Post**: Consumes through `streamEnd`, returns array of documents.
    **Error**: `invalidBareDocument` (bare content after non-`...`-terminated document, §9.2). -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def parseStreamIx {input : String} (tokens : Indexed.TokenStream input)
    (trackPositions : Bool := false) : Except ScanError (Array YamlDocument) := do
  let ps : ParseStateIx input := { tokens := tokens, trackPositions := trackPositions }
  let ps ← ps.expect .streamStart "STREAM-START"
  parseStreamLoop ps #[] .initial tokens.size

end L4YAML.TokenParser.Indexed
