/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.State
import L4YAML.Scanner.Whitespace
import L4YAML.Scanner.Indent
import L4YAML.Scanner.Document
import L4YAML.Scanner.NodeProperties
import L4YAML.Scanner.Scalar
import L4YAML.Scanner.SimpleKey
import L4YAML.Scanner.Linearise

/-!
# YAML Scanner (Tokenizer) — Dispatch Umbrella

Phase 9: Character stream → Token stream.

The scanner implements the 132 lexical-layer (L) productions from YAML 1.2.2,
converting a character stream into an array of positioned `YamlToken` values.
The grammar parser (S-layer) then operates on tokens, never on raw characters.

## Architecture

```
String ──→ scan ──→ Array (Positioned YamlToken) ──→ [Grammar Parser] ──→ YamlValue
```

The scanner is a **pure function** `String → Except ScanError (Array (Positioned YamlToken))`.
Internally it uses `ScannerState` to track:
- Current position (offset, line, col)
- Indentation stack (for virtual BLOCK-START/BLOCK-END generation)
- Flow nesting level (flow vs. block context)
- Simple key tracking

## Design Decisions

1. **Batch scanning** (not lazy/on-demand like libyaml). The entire input is
   scanned to a token array before parsing begins. Pure function, easy to verify.

2. **Indentation stack** generates virtual tokens: `blockSequenceStart`,
   `blockMappingStart`, `blockEnd` — analogous to Python's INDENT/DEDENT.

3. **Scalar content is fully resolved**: escapes expanded, line folding applied,
   chomp style applied. The grammar parser receives clean strings.

4. **Context-sensitive.** The same character sequence may tokenize differently
   depending on indentation level, flow/block context, and scalar style.

## Submodule Organization (Blueprint Initiative 1 Phase 2)

The scanner was monolithic (~2761 LoC in one file).  It is now split into
role-named submodules, with this file as the dispatch umbrella:

- [`Scanner.State`](State.lean) — `ScannerState`, `WellFormed`, accessors.
- [`Scanner.Whitespace`](Whitespace.lean) — `skipWhitespace`, `skipSpaces`,
  `consumeNewline`, `skipToContent`, comments (§6.1–§6.7).
- [`Scanner.Indent`](Indent.lean) — virtual `BLOCK-*` generation via
  `unwindIndents`, `pushSequenceIndent`, `pushMappingIndent`.
- [`Scanner.Document`](Document.lean) — `---` / `...` markers, `%YAML` /
  `%TAG` directives (§6.8, §9.1.2).
- [`Scanner.NodeProperties`](NodeProperties.lean) — anchors, aliases,
  tags (§6.9).
- [`Scanner.Scalar`](Scalar.lean) — escape sequences, quoted/plain/block
  scalars, line folding (§5.7, §6.5, §7.3, §8.1).
- [`Scanner.SimpleKey`](SimpleKey.lean) — simple-key resolution,
  `scanBlockEntry` / `scanKey` / `scanValue`, candidate predicates
  (§7.4, §8.2).

This file owns the flow-collection indicator scanners (`[`, `]`, `{`,
`}`, `,`) and the `scanNextToken` dispatch / `scanLoop` / `scan` /
`scanFiltered` main loop.

## Production Rule Contracts

Each scanning function documents which YAML 1.2.2 production(s) it implements
and the contract governing its variables and state transitions.

### Variable Classification

Every numeric variable in the scanner has exactly one of these roles:

- **Position** (absolute column, 0-based): the column where something is or
  must be. Indentation levels are positions. Examples: `parentIndent`,
  `contentIndent`, `s.col`, `currentIndent`.

- **Distance** (character count): how many characters of a particular kind.
  Always non-negative. Examples: `explicitIndent` (the `m` in `s-indent(m)`),
  `spacesConsumed`.

- **Pos** (`YamlPos`): a full (offset, line, col) triple for token attribution.
  Examples: `startPos`, `simpleKey.pos`.

The fundamental relationship: `Position = Position + Distance`.
Never add two Positions or use a Distance where a Position is expected.

### Pre/Post-Condition Style

Each scanning function specifies:

- **Implements**: YAML 1.2.2 production number(s) and section.
- **Pre**: Required scanner state at entry (position, context, expectations).
- **Post**: Scanner state at exit (position advanced past matched content,
  token(s) emitted, flags set).
- **Error**: Conditions under which `Except.error` is returned.

## References

- libyaml `scanner.c` (~2800 lines)
- YAML 1.2.2 §5–§8 (character, lexical, block/flow productions)
- `YAML_PRODUCTIONS.md` §Token–Grammar Layer Analysis
-/

namespace L4YAML.Scanner

open L4YAML
open L4YAML.CharPredicates

/-! ## Flow-Collection Indicator Scanning -/

/-- Scan a flow sequence start indicator `[`.

    **Implements** (YAML 1.2.2 §7.4.1):
    - `[137] c-flow-sequence(n,c)` = `"[" s-separate(n,c)? ...`
    - `[8]   c-sequence-start` = `"["`

    **Pre**: Scanner at `[`.
    **Post**: Emits `flowSequenceStart`, advances past `[`, increments `flowLevel`,
    pushes `true` onto `flowStack` (= sequence), sets `simpleKeyAllowed := true`.

    **Refactored for verification**: Uses explicit variable names (no shadowing)
    to make token tracking clearer for formal proofs. -/
@[yaml_spec "7.4.1" 137 "c-flow-sequence",
  yaml_spec "7.4.1" 8 "c-sequence-start"]
def scanFlowSequenceStart (s : ScannerState) : ScannerState :=
  -- Save the outer simple key so it survives flow nesting.
  -- Example: `[a, b]: value` — the simple key saved before `[` must
  -- still be pending after `]` for `:` to confirm it.
  -- J.2 dual-write: shadow `pendingKeyActive` onto `pendingKeyStack`
  -- in lockstep with `simpleKeyStack`.
  let savedKey := s.simpleKey
  let savedPending := s.pendingKeyActive
  let s_key_disabled := { s with simpleKey := { possible := false },
                                  pendingKeyActive := none }
  let s_with_token := s_key_disabled.emit .flowSequenceStart
  let s_after_advance := s_with_token.advance
  { s_after_advance with
      flowLevel := s_after_advance.flowLevel + 1,
      simpleKeyAllowed := true,
      flowStack := s_after_advance.flowStack.push true,
      simpleKeyStack := s_after_advance.simpleKeyStack.push savedKey,
      pendingKeyStack := s_after_advance.pendingKeyStack.push savedPending }

/-- Scan a flow sequence end indicator `]`.

    **Implements** (YAML 1.2.2 §7.4.1):
    - `[9]  c-sequence-end` = `"]"`

    **Pre**: Scanner at `]` inside a flow collection (`flowLevel > 0`).
    **Post**: Emits `flowSequenceEnd`, advances past `]`, decrements `flowLevel`,
    pops `flowStack`, sets `simpleKeyAllowed := false`.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "7.4.1" 9 "c-sequence-end"]
def scanFlowSequenceEnd (s : ScannerState) : ScannerState :=
  let s_with_token := s.emit .flowSequenceEnd
  let s_after_advance := s_with_token.advance
  -- Restore the outer simple key saved by the matching flow-open.
  -- J.2 dual-write: also restore `pendingKeyActive` from `pendingKeyStack`.
  let restored := s_with_token.simpleKeyStack.back?.getD {}
  let restoredPending := s_with_token.pendingKeyStack.back?.getD none
  { s_after_advance with
      flowLevel := if s_after_advance.flowLevel > 0 then s_after_advance.flowLevel - 1 else 0,
      simpleKeyAllowed := false,
      flowStack := s_after_advance.flowStack.pop,
      simpleKey := restored,
      simpleKeyStack := s_after_advance.simpleKeyStack.pop,
      pendingKeyActive := restoredPending,
      pendingKeyStack := s_after_advance.pendingKeyStack.pop }

/-- Scan a flow mapping start indicator `{`.

    **Implements** (YAML 1.2.2 §7.4.2):
    - `[140] c-flow-mapping(n,c)` = `"{" s-separate(n,c)? ...`
    - `[10]  c-mapping-start` = `"{"`

    **Pre**: Scanner at `{`.
    **Post**: Emits `flowMappingStart`, advances past `{`, increments `flowLevel`,
    pushes `false` onto `flowStack` (= mapping), sets `simpleKeyAllowed := true`.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "7.4.2" 140 "c-flow-mapping", yaml_spec "7.4.2" 10 "c-mapping-start"]
def scanFlowMappingStart (s : ScannerState) : ScannerState :=
  -- Save the outer simple key so it survives flow nesting.
  -- Example: `{a: b}: value` — the simple key saved before `{` must
  -- still be pending after `}` for `:` to confirm it.
  -- J.2 dual-write: shadow `pendingKeyActive` onto `pendingKeyStack`
  -- in lockstep with `simpleKeyStack`.
  let savedKey := s.simpleKey
  let savedPending := s.pendingKeyActive
  let s_key_disabled := { s with simpleKey := { possible := false },
                                  pendingKeyActive := none }
  let s_with_token := s_key_disabled.emit .flowMappingStart
  let s_after_advance := s_with_token.advance
  { s_after_advance with
      flowLevel := s_after_advance.flowLevel + 1,
      simpleKeyAllowed := true,
      flowStack := s_after_advance.flowStack.push false,
      simpleKeyStack := s_after_advance.simpleKeyStack.push savedKey,
      pendingKeyStack := s_after_advance.pendingKeyStack.push savedPending }

/-- Scan a flow mapping end indicator `}`.

    **Implements** (YAML 1.2.2 §7.4.2):
    - `[11] c-mapping-end` = `"}"`

    **Pre**: Scanner at `}` inside a flow collection (`flowLevel > 0`).
    **Post**: Emits `flowMappingEnd`, advances past `}`, decrements `flowLevel`,
    pops `flowStack`, sets `simpleKeyAllowed := false`.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "7.4.2" 11 "c-mapping-end"]
def scanFlowMappingEnd (s : ScannerState) : ScannerState :=
  let s_with_token := s.emit .flowMappingEnd
  let s_after_advance := s_with_token.advance
  -- Restore the outer simple key saved by the matching flow-open.
  -- J.2 dual-write: also restore `pendingKeyActive` from `pendingKeyStack`.
  let restored := s_with_token.simpleKeyStack.back?.getD {}
  let restoredPending := s_with_token.pendingKeyStack.back?.getD none
  { s_after_advance with
      flowLevel := if s_after_advance.flowLevel > 0 then s_after_advance.flowLevel - 1 else 0,
      simpleKeyAllowed := false,
      flowStack := s_after_advance.flowStack.pop,
      simpleKey := restored,
      simpleKeyStack := s_after_advance.simpleKeyStack.pop,
      pendingKeyActive := restoredPending,
      pendingKeyStack := s_after_advance.pendingKeyStack.pop }

/-- Last token value in the array, skipping up to two trailing
    `.placeholder` reservation slots inserted by `saveSimpleKey`.
    Returns `none` if there are no real tokens.

    **Initiative 3 / J.2 step 4**: renamed from `lastRealTokenVal?` since
    the "real vs. placeholder" distinction is going away.  At the J.2
    cutover (step 5) the body simplifies to `tokens.back?.map (·.val)`
    once `saveSimpleKey` stops pushing placeholders. -/
def lastTokenVal? (tokens : Array (Positioned YamlToken)) : Option YamlToken :=
  if tokens.size > 0 then
    let lastIdx := tokens.size - 1
    let tok1 := tokens[lastIdx]!.val
    if tok1 == .placeholder && lastIdx > 0 then
      let tok2 := tokens[lastIdx - 1]!.val
      if tok2 == .placeholder && lastIdx > 1 then
        some (tokens[lastIdx - 2]!.val)
      else some tok2
    else some tok1
  else none

/-- Scan a flow entry separator `,`.

    **Implements** (YAML 1.2.2 §7.4):
    - `[7] c-collect-entry` = `","`

    **Pre**: Scanner at `,` inside a flow collection (`flowLevel > 0`).
    **Post**: Emits `flowEntry`, advances past `,`, sets `simpleKeyAllowed := true`.
    **Error**: `invalidFlowEntry` if comma immediately follows a flow-open indicator
    (`[`, `{`) or another comma — catching leading/consecutive commas.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "7.4" 7 "c-collect-entry"]
def scanFlowEntry (s : ScannerState) : Except ScanError ScannerState := do
  -- §7.4: Leading comma (after flow-open) or consecutive commas are invalid.
  if let some lastTok := lastTokenVal? s.tokens then
    if lastTok == .flowSequenceStart || lastTok == .flowMappingStart ||
       lastTok == .flowEntry then
      throw (.invalidFlowEntry s.line s.col)
  let s_with_token := s.emit .flowEntry
  let s_after_advance := s_with_token.advance
  .ok { s_after_advance with simpleKeyAllowed := true }

/-! ## Main Scanner Loop -/

/-- Preprocessing phase of `scanNextToken`.

    Skips whitespace/comments, handles block indentation unwind,
    saves simple key position, and peeks at the next character.

    Returns `none` if input is exhausted, or `some (s', c)` where
    `s'` is the preprocessed state and `c` is the peeked character. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def scanNextToken_preprocess (s : ScannerState) :
    Except ScanError (Option (ScannerState × Char)) := do
  let s ← skipToContent s
  if !s.hasMore then return none
  let savedIndentSize := s.indents.size
  let s := if !s.inFlow && s.needIndentCheck then
    let s := unwindIndents s s.col
    { s with needIndentCheck := false }
  else s
  if s.indents.size < savedIndentSize && (s.col : Int) > s.currentIndent then
    return ← .error (.trailingContent s.line s.col)
  let s := saveSimpleKey s
  match s.peek? with
  | none => return none
  | some c => return some (s, c)

/-- Structural dispatch: validation checks, document markers, and directives.

    Returns `some s'` if a document marker or directive was processed,
    `none` to indicate fallthrough to indicator/content dispatch. -/
@[yaml_spec "9.1.2" 203 "c-directives-end",
  yaml_spec "9.1.2" 204 "c-document-end",
  yaml_spec "6.8" 82 "l-directive"]
def scanNextToken_dispatchStructural (s : ScannerState) (c : Char) :
    Except ScanError (Option ScannerState) := do
  -- §8.1 / §7.5: Flow content inside a block structure must be more
  -- indented than the enclosing block collection.
  if s.inFlow && s.currentIndent >= 0 && (s.col : Int) <= s.currentIndent then
    if c != ']' && c != '}' then
      return ← .error (.underIndentedFlowContent s.line s.col)
  -- §5.4: Document markers are forbidden inside flow collections.
  if s.col == 0 && s.inFlow && (atDocumentStart s || atDocumentEnd s) then
    return ← .error (.documentMarkerInFlow s.line)
  if s.col == 0 && atDocumentStart s then return some (scanDocumentStart s)
  if s.col == 0 && atDocumentEnd s then
    let s' ← scanDocumentEnd s
    return some s'
  if c == '%' && s.col == 0 then
    let s' ← scanDirective s
    return some s'
  return none

/-- Flow indicator dispatch: `[`, `]`, `{`, `}`, `,`.

    Returns `some s'` if a flow indicator was processed,
    `none` to indicate fallthrough. -/
@[yaml_spec "7.4.1" 137 "c-flow-sequence",
  yaml_spec "7.4.2" 140 "c-flow-mapping",
  yaml_spec "7.4" 7 "c-collect-entry"]
def scanNextToken_dispatchFlowIndicators (s : ScannerState) (c : Char) :
    Except ScanError (Option ScannerState) := do
  if c == '[' then return some (scanFlowSequenceStart s)
  if c == ']' then
    if s.flowLevel == 0 then return ← .error (.flowEndOutsideFlow ']' s.line s.col)
    let s' := scanFlowSequenceEnd s
    validateFlowClose s'
    return some s'
  if c == '{' then return some (scanFlowMappingStart s)
  if c == '}' then
    if s.flowLevel == 0 then return ← .error (.flowEndOutsideFlow '}' s.line s.col)
    let s' := scanFlowMappingEnd s
    validateFlowClose s'
    return some s'
  if c == ',' then
    if s.flowLevel == 0 then return ← .error (.flowEndOutsideFlow ',' s.line s.col)
    let s' ← scanFlowEntry s
    return some s'
  return none

/-- Block indicator dispatch: `-`, `?`, `:`.

    Returns `some s'` if a block indicator was processed,
    `none` to indicate fallthrough. -/
@[yaml_spec "8.2.1" 184 "c-l-block-seq-entry",
  yaml_spec "8.2.2" 190 "c-l-block-map-explicit-key",
  yaml_spec "8.2.2" 6 "c-mapping-value"]
def scanNextToken_dispatchBlockIndicators (s : ScannerState) (c : Char) :
    Except ScanError (Option ScannerState) := do
  if c == '-' && !s.inFlow && isBlockEntryCandidate s then
    let s' ← scanBlockEntry s
    return some s'
  if c == '?' && isKeyCandidate s then
    let s' ← scanKey s
    return some s'
  if c == ':' && isValueCandidate s then
    let s' ← scanValue s
    return some s'
  return none

/-- Content token dispatch: anchors, tags, scalars, and error.

    Handles `&`, `*`, `!`, `|`/`>`, `"`, `'`, plain scalars.
    Always either processes a token or returns an error. -/
@[yaml_spec "6.9" 96 "c-ns-properties",
  yaml_spec "7.3" 105 "c-flow-scalar",
  yaml_spec "8.1" 161 "c-l-block-scalar"]
def scanNextToken_dispatchContent (s : ScannerState) (c : Char) :
    Except ScanError ScannerState := do
  if c == '&' then
    let s' ← scanAnchorOrAlias s true
    let name := (collectAnchorNameLoop s.advance "" (s.inputEnd - s.advance.offset)).fst
    return { s' with definedAnchors := s'.definedAnchors.push name }
  if c == '*' then
    let name := (collectAnchorNameLoop s.advance "" (s.inputEnd - s.advance.offset)).fst
    if !(s.definedAnchors.any (· == name)) then
      .error (.undefinedAlias name s.currentPos.line s.currentPos.col)
    else
      let s' ← scanAnchorOrAlias s false
      return s'
  if c == '!' then
    let s' ← scanTag s
    return s'
  if c == '|' || c == '>' then
    let s' ← scanBlockScalar s
    return s'
  if c == '"' then
    let s' ← scanDoubleQuoted s
    -- §7.4: Quoted scalars can span lines; update simpleKey.endLine
    -- so scanValue can check key-end-line vs `:` line.
    -- J.2 dual-write: parallel update to the active pendingKey's endLine.
    let s' := if s'.simpleKey.possible then
      { s' with simpleKey := { s'.simpleKey with endLine := s'.line },
                pendingKeys := setPendingKeyEndLine s'.pendingKeys s'.pendingKeyActive s'.line }
    else s'
    return s'
  if c == '\'' then
    let s' ← scanSingleQuoted s
    let s' := if s'.simpleKey.possible then
      { s' with simpleKey := { s'.simpleKey with endLine := s'.line },
                pendingKeys := setPendingKeyEndLine s'.pendingKeys s'.pendingKeyActive s'.line }
    else s'
    return s'
  if canStartPlainScalarBool c (s.peekAt? 1) s.inFlow then
    let s' ← scanPlainScalar s; return s'
  .error (.unexpectedChar c s.line s.col)

/-- §8.1 [187]: Flow-collection start (`[` or `{`) from a block context must be
    more indented than the enclosing block collection.  Returns `.ok ()` to
    continue, or `.error` to reject.  Factored out so `unfold scanNextToken`
    does not expose `Bool.and` internals to the proof engine. -/
@[yaml_spec "8.1"]
def scanNextToken_checkBlockFlowIndent (s : ScannerState) (c : Char) :
    Except ScanError Unit :=
  if !s.inFlow && s.currentIndent >= 0 && (s.col : Int) <= s.currentIndent
      && (c == '[' || c == '{') then
    .error (.underIndentedFlowContent s.line s.col)
  else
    .ok ()

/-- Scan the next token from the input.

    **Implements**: Main dispatch loop for YAML token recognition.
    Called repeatedly by `scan` until input is exhausted.

    **Decomposed for provability**: Preprocessing and character dispatch are
    split into helper functions (`scanNextToken_preprocess`,
    `scanNextToken_dispatchStructural`, `scanNextToken_dispatchFlowIndicators`,
    `scanNextToken_dispatchBlockIndicators`, `scanNextToken_dispatchContent`)
    each with ≤ 7 branch points, keeping individual proofs tractable.

    Flow:
    1. `scanNextToken_preprocess` — skip whitespace, indent check, peek char
    2. `scanNextToken_dispatchStructural` — validation, document markers, directives
    3. `scanNextToken_dispatchFlowIndicators` — `[`, `]`, `{`, `}`, `,`
    4. `scanNextToken_dispatchBlockIndicators` — `-`, `?`, `:`
    5. `scanNextToken_dispatchContent` — `&`, `*`, `!`, `|`/`>`, `"`, `'`, plain

    **Pre**: Scanner state from previous token (or initial state).
    **Post**: Scanner past one token. Token emitted. State updated.
    **Error**: Unexpected character at current position. -/
@[yaml_spec "9.2"]
def scanNextToken (s : ScannerState) : Except ScanError (Option ScannerState) := do
  match ← scanNextToken_preprocess s with
  | none => return none
  | some (s, c) =>
    match ← scanNextToken_dispatchStructural s c with
    | some s' => return some s'
    | none =>
      -- Any non-directive, non-document-marker content means we're in a document.
      -- Disallow directives until the next `...` document-end marker.
      let s := if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true }
      else s
      -- §8.1 [187]: Flow-collection start from block context must be more
      -- indented than the enclosing block collection.
      scanNextToken_checkBlockFlowIndent s c
      match ← scanNextToken_dispatchFlowIndicators s c with
      | some s' => return some s'
      | none =>
        match ← scanNextToken_dispatchBlockIndicators s c with
        | some s' => return some s'
        | none =>
          let s' ← scanNextToken_dispatchContent s c
          return some s'

/-- Structurally recursive helper for scan.

    Processes tokens one at a time using `scanNextToken`, with fuel decreasing
    on each iteration. Returns when either:
    - `scanNextToken` returns `none` (normal completion)
    - fuel is exhausted (error)

    **Design for provability**: Uses structural recursion on fuel parameter,
    enabling standard induction tactics for theorem proving. This replaces
    the imperative `for` loop in the original implementation.

    **Implements**: Core scanning loop with termination checking.
    **Post**: Same as `scan` - returns tokens starting with `streamStart`,
    ending with `streamEnd`.
    **Error**: Same error conditions as `scan`. -/
@[yaml_spec "9.2"]
def scanLoop (s : ScannerState) (fuel : Nat) :
    Except ScanError (Array (Positioned YamlToken)) :=
  match fuel with
  | 0 =>
    -- Fuel exhausted without scanner signaling completion
    .error (.fuelExhausted s.line s.col)
  | fuel' + 1 =>
    match scanNextToken s with
    | .error e =>
      -- Propagate scanner error
      .error e
    | .ok none =>
      -- Scanner signals completion (no more tokens to process)
      -- Perform final validation and emit streamEnd
      if s.flowLevel > 0 then
        -- §7.4: Unclosed flow collections are an error
        .error (.unterminatedFlowCollection '[' s.line)
      else if s.directivesPresent && !s.documentEverStarted then
        -- §6.8: Directives without document are an error
        .error (.directiveWithoutDocument s.line)
      else
        -- Close all remaining block contexts and emit final token
        let final := unwindIndents s (-1)
        let final := final.emit .streamEnd
        .ok final.tokens
    | .ok (some s') =>
      -- Scanner produced a new state, continue with remaining fuel
      scanLoop s' fuel'
termination_by fuel

/-- Run the scanner on an input string, producing a token array.

    **Implements**: Complete YAML tokenization pipeline.
    Wraps `scanNextToken` in a fuel-bounded loop (via `scanLoop`), bookended by
    `streamStart`/`streamEnd` tokens.

    **Refactored for provability**: Now uses structurally recursive `scanLoop`
    instead of imperative `for` loop, enabling formal verification via induction.

    **Post**: Token array starts with `streamStart`, ends with `streamEnd`.
    All block collections are properly closed via `unwindIndents`.
    **Error**: `unterminatedFlowCollection` (unclosed `[`/`{`),
    `directiveWithoutDocument` (orphan directives), `fuelExhausted`. -/
@[yaml_spec "9.2" 211 "l-yaml-stream",
  yaml_spec "5.2" 3 "c-byte-order-mark",
  yaml_spec "9.1.1" 202 "l-document-prefix"]
def scan (input : String) : Except ScanError (Array (Positioned YamlToken)) :=
  let s := ScannerState.mk' input
  let s := s.emit .streamStart
  -- Handle BOM (Byte Order Mark)
  let s := match s.peek? with
    | some '\uFEFF' => s.advance
    | _ => s
  -- Calculate fuel: 4x input size should be more than enough
  let fuel := input.utf8ByteSize + 1
  scanLoop s (fuel * 4)

/-- Like `scan` but filters out internal placeholder tokens.
    Use this for all user-facing output and tests. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def scanFiltered (input : String) : Except ScanError (Array (Positioned YamlToken)) :=
  match scan input with
  | .ok tokens => .ok (tokens.filter fun t => t.val != .placeholder)
  | .error e => .error e

/-- Like `scanLoop` but returns the full final `ScannerState` (including
    collected comments) rather than just the token array. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def scanLoopFull (s : ScannerState) (fuel : Nat) : Except ScanError ScannerState :=
  match fuel with
  | 0 => .error (.fuelExhausted s.line s.col)
  | fuel' + 1 =>
    match scanNextToken s with
    | .error e => .error e
    | .ok none =>
      if s.flowLevel > 0 then
        .error (.unterminatedFlowCollection '[' s.line)
      else if s.directivesPresent && !s.documentEverStarted then
        .error (.directiveWithoutDocument s.line)
      else
        -- Re-run skipToContent to collect trailing comments that
        -- scanNextToken_preprocess discarded when returning none.
        -- scanNextToken calls skipToContent internally, but returns
        -- none (discarding the updated state) when end-of-input is
        -- reached after comment/whitespace consumption.
        let s := match skipToContent s with | .ok s' => s' | .error _ => s
        let final := unwindIndents s (-1)
        let final := final.emit .streamEnd
        .ok final
    | .ok (some s') => scanLoopFull s' fuel'
termination_by fuel

/-- Scan with comment preservation.

    Returns both the filtered token array and the collected comments
    (each as position × text). Comments are collected as a side-channel
    during scanning — they do not appear in the token array.

    The token array is identical to `scanFiltered`; comments are the
    additional information. -/
@[yaml_spec "9.2" 211 "l-yaml-stream",
  yaml_spec "6.6" 75 "c-nb-comment-text"]
def scanWithComments (input : String) :
    Except ScanError (Array (Positioned YamlToken) × Array (YamlPos × String)) :=
  let s := ScannerState.mk' input
  let s := s.emit .streamStart
  let s := match s.peek? with
    | some '\uFEFF' => s.advance
    | _ => s
  let fuel := input.utf8ByteSize + 1
  match scanLoopFull s (fuel * 4) with
  | .ok final =>
    let tokens := final.tokens.filter fun t => t.val != .placeholder
    .ok (tokens, final.comments)
  | .error e => .error e

end L4YAML.Scanner
