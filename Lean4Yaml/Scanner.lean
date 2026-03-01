/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Token

/-!
# YAML Scanner (Tokenizer)

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

namespace Lean4Yaml.Scanner

open Lean4Yaml

/-! ## Scanner State -/

/-- An entry on the indentation stack. -/
structure IndentEntry where
  /-- Column where this block collection starts -/
  column : Int
  /-- Whether this is a sequence (true) or mapping (false) -/
  isSequence : Bool
  deriving Repr, BEq, Inhabited

/-- Simple key tracking state.
    YAML §7.4: implicit keys are limited to a single line
    and 1024 characters in block context. -/
structure SimpleKeyState where
  /-- Whether a simple key is possible at the current position -/
  possible : Bool := false
  /-- Token index where the potential simple key started -/
  tokenIndex : Nat := 0
  /-- Source position of the potential simple key -/
  pos : YamlPos := default
  /-- Line where the simple key token ended (for multi-line quoted keys,
      this differs from `pos.line`). Used to validate that `:` follows
      on the same line as the key's end, not just its start. -/
  endLine : Nat := 0
  deriving Repr, BEq, Inhabited

/-- The scanner's mutable state. -/
structure ScannerState where
  /-- Source string being scanned -/
  input : String
  /-- End byte offset of input (cached from `input.utf8ByteSize`) -/
  inputEnd : Nat
  /-- Current byte offset -/
  offset : Nat := 0
  /-- Current line (0-based) -/
  line : Nat := 0
  /-- Current column (0-based) -/
  col : Nat := 0
  /-- Indentation stack. Bottom entry: `{ column := -1 }`. -/
  indents : Array IndentEntry := #[{ column := -1, isSequence := false }]
  /-- Flow nesting level. 0 = block context. -/
  flowLevel : Nat := 0
  /-- Emitted tokens -/
  tokens : Array (Positioned YamlToken) := #[]
  /-- Simple key tracking -/
  simpleKey : SimpleKeyState := {}
  /-- Whether a simple key is allowed at the current position.
      Set true after line breaks, block entries, keys, values.
      Set false after scalars, anchors, aliases, tags. -/
  simpleKeyAllowed : Bool := true
  /-- Whether we need to check indentation at current position -/
  needIndentCheck : Bool := true
  /-- Whether directives (`%YAML`, `%TAG`) are allowed at the current position.
      True at stream start and after `...`; false after `---` or content. -/
  allowDirectives : Bool := true
  /-- Whether a `%YAML` directive has been seen in the current directive block.
      Reset when `---` is emitted. Used to detect duplicate `%YAML`. -/
  seenYamlDirective : Bool := false
  /-- Whether any directive has been emitted since last `---`.
      Used to detect directives-without-document at EOF and before `...`. -/
  directivesPresent : Bool := false
  /-- Whether a document has ever been started (via `---` or implicit content).
      Used to detect directive-only streams. -/
  documentEverStarted : Bool := false
  deriving Repr, Inhabited

/-- Create initial scanner state from an input string. -/
def ScannerState.mk' (input : String) : ScannerState :=
  { input := input, inputEnd := input.utf8ByteSize }

/-! ## State Accessors -/

def ScannerState.currentPos (s : ScannerState) : YamlPos where
  offset := s.offset
  line := s.line
  col := s.col

def ScannerState.hasMore (s : ScannerState) : Bool :=
  s.offset < s.inputEnd

def ScannerState.peek? (s : ScannerState) : Option Char :=
  if s.offset < s.inputEnd then
    some (String.Pos.Raw.get s.input ⟨s.offset⟩)
  else
    none

def ScannerState.peekAt? (s : ScannerState) (n : Nat) : Option Char := Id.run do
  let mut pos : String.Pos.Raw := ⟨s.offset⟩
  for _ in [:n] do
    if pos.byteIdx < s.inputEnd then
      pos := String.Pos.Raw.next s.input pos
    else
      return none
  if pos.byteIdx < s.inputEnd then
    return some (String.Pos.Raw.get s.input pos)
  else
    return none

/-- Look at the character immediately before the current position in the raw input.
    Used for §6.7 comment validation: `c-nb-comment-text` (`#`) requires
    preceding `s-separate-in-line` (whitespace or start-of-line). -/
def ScannerState.peekBack? (s : ScannerState) : Option Char :=
  if s.offset > 0 then
    let prevPos := String.Pos.Raw.prev s.input ⟨s.offset⟩
    some (String.Pos.Raw.get s.input prevPos)
  else
    none

def ScannerState.advance (s : ScannerState) : ScannerState :=
  if s.offset < s.inputEnd then
    let c := String.Pos.Raw.get s.input ⟨s.offset⟩
    let nextPos := String.Pos.Raw.next s.input ⟨s.offset⟩
    if c == '\n' then
      { s with offset := nextPos.byteIdx, line := s.line + 1, col := 0 }
    else
      { s with offset := nextPos.byteIdx, col := s.col + 1 }
  else
    s

def ScannerState.advanceN (s : ScannerState) (n : Nat) : ScannerState := Id.run do
  let mut s' := s
  for _ in [:n] do
    s' := s'.advance
  return s'

def ScannerState.inFlow (s : ScannerState) : Bool :=
  s.flowLevel > 0

def ScannerState.currentIndent (s : ScannerState) : Int :=
  match s.indents.back? with
  | some e => e.column
  | none => -1

def ScannerState.emit (s : ScannerState) (tok : YamlToken) : ScannerState :=
  { s with tokens := s.tokens.push { pos := s.currentPos, val := tok } }

def ScannerState.emitAt (s : ScannerState) (pos : YamlPos) (tok : YamlToken) : ScannerState :=
  { s with tokens := s.tokens.push { pos := pos, val := tok } }

def ScannerState.insertAt (s : ScannerState) (idx : Nat) (pos : YamlPos) (tok : YamlToken) : ScannerState :=
  let positioned : Positioned YamlToken := { pos := pos, val := tok }
  if idx >= s.tokens.size then
    { s with tokens := s.tokens.push positioned }
  else
    let before := s.tokens.extract 0 idx
    let after := s.tokens.extract idx s.tokens.size
    { s with tokens := (before.push positioned) ++ after }

/-! ## Character Classification -/

def isLineBreak (c : Char) : Bool := c == '\n' || c == '\r'
def isWhiteSpace (c : Char) : Bool := c == ' ' || c == '\t'
def isBlank (c : Char) : Bool := isWhiteSpace c || isLineBreak c
def isFlowIndicator (c : Char) : Bool := c ∈ [',', '[', ']', '{', '}']
def isIndicator (c : Char) : Bool :=
  c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
       '\'', '"', '%', '@', '`']

/-! ## Whitespace Consumption

    YAML 1.2.2 distinguishes two kinds of horizontal whitespace:
    - `[31] s-space` = `#x20` (space only)
    - `[32] s-tab`  = `#x09` (tab only)
    - `[33] s-white` = `s-space | s-tab`

    Indentation ([63] `s-indent(n)` = `s-space × n`) uses **spaces only**.
    Separation ([66] `s-separate-in-line` = `s-white+`) allows **spaces + tabs**.

    `skipSpaces`     — matches `s-space*`  (for `s-indent`)
    `skipWhitespace` — matches `s-white*`  (for `s-separate-in-line`)
-/

/-- Check whether any TAB character appears in the contiguous whitespace
    (spaces + tabs) immediately before the current offset.  Scans backward
    without consuming anything.  Used by `scanBlockEntry` to enforce YAML §6.1:
    tabs must not be used in indentation.  Because `skipToContent` consumes
    whitespace (including tabs) on same-line continuations without checking,
    this backward scan detects tabs that slipped through as indentation before
    the block entry indicator.

    Handles `-\t-`, `- \t-`, `-\t -`, etc. — any tab in the preceding
    whitespace run means a tab contributed to the indentation of this token. -/
def ScannerState.hasTabInPrecedingWhitespace (s : ScannerState) : Bool := Id.run do
  let mut pos := s.offset
  for _ in [:s.offset] do
    if pos == 0 then break
    let prevPos := (String.Pos.Raw.prev s.input ⟨pos⟩).byteIdx
    let c := String.Pos.Raw.get s.input ⟨prevPos⟩
    if c == '\t' then return true
    if c == ' ' then pos := prevPos; continue
    break  -- non-whitespace character: stop scanning
  return false

/-- Skip zero or more `s-white` characters (spaces + tabs).
    Implements `s-white*` — use for `s-separate-in-line` ([66]) contexts.
    **Not** for indentation. See `skipSpaces` for `s-indent`. -/
def skipWhitespace (s : ScannerState) : ScannerState := Id.run do
  let mut s' := s
  let fuel := s.inputEnd - s.offset
  for _ in [:fuel] do
    match s'.peek? with
    | some c => if isWhiteSpace c then s' := s'.advance else break
    | none => break
  return s'

/-- Skip zero or more `s-space` characters (spaces only, no tabs).
    Implements `s-space*` — use for `s-indent(n)` ([63]) contexts.
    YAML §6.1: "tab characters must not be used in indentation". -/
def skipSpaces (s : ScannerState) : ScannerState := Id.run do
  let mut s' := s
  let fuel := s.inputEnd - s.offset
  for _ in [:fuel] do
    match s'.peek? with
    | some ' ' => s' := s'.advance
    | _ => break
  return s'

def skipToEndOfLine (s : ScannerState) : ScannerState := Id.run do
  let mut s' := s
  let fuel := s.inputEnd - s.offset
  for _ in [:fuel] do
    match s'.peek? with
    | some c => if isLineBreak c then break else s' := s'.advance
    | none => break
  return s'

def consumeNewline (s : ScannerState) : ScannerState :=
  match s.peek? with
  | some '\n' => { s.advance with needIndentCheck := true }
  | some '\r' =>
    let s' := s.advance
    match s'.peek? with
    | some '\n' => { s'.advance with needIndentCheck := true }
    | _ => { s' with needIndentCheck := true }
  | _ => s

/-- Advance past whitespace, comments, and line breaks to the next content character.

    **Implements**: `s-l-comments` ([79]) and parts of `l-comment` ([78]).

    Each iteration of the outer loop handles one "line" of skippable content:
    1. Skip indentation spaces (`s-indent`, [63]): `s-space*` via `skipSpaces`.
    2. Tab-as-indentation check (§6.1), guarded by `currentIndent`:
       - `col > currentIndent` → past indentation → tabs are `s-separate-in-line` [66] (legal)
       - `col ≤ currentIndent` → in indentation zone → tabs before content are an error
       - Flow context → no indentation significance → tabs always legal
    3. Skip remaining `s-separate-in-line` whitespace (spaces + tabs) via `skipWhitespace`.
    4. Skip optional comment: if `#`, consume to end of line.
    5. If line break: consume it, set `simpleKeyAllowed`, continue to next line.
    6. Otherwise: we've reached content — stop.

    **Error**: Tab character used as indentation (before content on a new line). -/
def skipToContent (s : ScannerState) : Except ScanError ScannerState := do
  let fuel := s.inputEnd - s.offset + 1
  let mut s' := s
  for _ in [:fuel] do
    -- After a newline, use skipSpaces for indentation (s-indent [63]: spaces only).
    -- Then check for tab-as-indentation, using currentIndent to determine the
    -- boundary between indentation territory and separation territory.
    --
    -- Track whether `#` is allowed as a comment start per §6.7:
    --   [78] l-comment ::= s-separate-in-line c-nb-comment-text? b-comment
    -- s-separate-in-line [66] = s-white+ | start-of-line.
    -- So `#` is a comment only if (a) at start-of-line, or (b) preceded by ≥1 s-white.
    -- Check the raw input character before `#` (via peekBack?) rather than tracking
    -- whitespace consumption, since prior token scanners may have consumed the whitespace.
    if s'.needIndentCheck then
      s' := skipSpaces s'
      -- Key insight: once col > currentIndent, we've consumed enough spaces
      -- to be inside the current block's content area. Any tabs here are
      -- s-separate-in-line [66] (legal separation), not indentation.
      if !s'.inFlow && (s'.col : Int) ≤ s'.currentIndent then
        -- Still at or below the current block's indent level.
        -- A tab here would extend into indentation territory — §6.1 violation.
        match s'.peek? with
        | some '\t' =>
          -- Peek past tabs/spaces to see what follows
          let probe := skipWhitespace s'
          match probe.peek? with
          | some '#' => s' := skipWhitespace s'   -- tab before comment: allowed
          | some c =>
            if isLineBreak c then s' := skipWhitespace s'  -- tab on blank line: allowed
            else
              -- Tab followed by content: tab used as indentation — forbidden §6.1
              throw (.tabInIndentation s'.line s'.col)
          | none => s' := skipWhitespace s'        -- tab before EOF: allowed
        | _ => pure ()
      else
        -- Past indentation boundary or in flow context: tabs are legal separation
        s' := skipWhitespace s'
    else
      s' := skipWhitespace s'
    -- §6.7: c-nb-comment-text (#) requires preceding s-separate-in-line.
    -- s-separate-in-line = s-white+ | start-of-line.
    -- Check the raw input: # must be preceded by whitespace or be at column 0.
    match s'.peek? with
    | some '#' =>
      let commentOk := s'.col == 0 || match s'.peekBack? with
        | some c => isWhiteSpace c || isLineBreak c || c == '\uFEFF'  -- BOM is transparent (§5.2)
        | none => true   -- start of input
      if commentOk then
        s' := skipToEndOfLine s'
      -- else: `#` without preceding whitespace — not a comment; leave for scanNextToken
    | _ => pure ()
    match s'.peek? with
    | some c =>
      if isLineBreak c then
        s' := consumeNewline s'
        s' := { s' with simpleKeyAllowed := true }
      else break
    | none => break
  return s'

/-! ## Indentation Management -/

def unwindIndents (s : ScannerState) (col : Int) : ScannerState := Id.run do
  let mut s' := s
  let fuel := s'.indents.size
  for _ in [:fuel] do
    if s'.currentIndent > col && s'.indents.size > 1 then
      s' := s'.emit .blockEnd
      s' := { s' with indents := s'.indents.pop }
    else
      break
  return s'

def pushSequenceIndent (s : ScannerState) (col : Int) : ScannerState :=
  if col > s.currentIndent then
    let s' := s.emit .blockSequenceStart
    { s' with indents := s'.indents.push { column := col, isSequence := true } }
  else s

def pushMappingIndent (s : ScannerState) (col : Int) : ScannerState :=
  if col > s.currentIndent then
    let s' := s.emit .blockMappingStart
    { s' with indents := s'.indents.push { column := col, isSequence := false } }
  else s

/-! ## Document Boundary Detection -/

def atDocumentStart (s : ScannerState) : Bool :=
  s.col == 0
  && s.peekAt? 0 == some '-'
  && s.peekAt? 1 == some '-'
  && s.peekAt? 2 == some '-'
  && match s.peekAt? 3 with
     | none => true
     | some c => isBlank c

def atDocumentEnd (s : ScannerState) : Bool :=
  s.col == 0
  && s.peekAt? 0 == some '.'
  && s.peekAt? 1 == some '.'
  && s.peekAt? 2 == some '.'
  && match s.peekAt? 3 with
     | none => true
     | some c => isBlank c

def atDocumentBoundary (s : ScannerState) : Bool :=
  atDocumentStart s || atDocumentEnd s

/-! ## Indicator Scanning -/

def scanFlowSequenceStart (s : ScannerState) : ScannerState :=
  let s' := { s with simpleKey := { possible := false } }
  let s' := s'.emit .flowSequenceStart
  { s'.advance with flowLevel := s'.flowLevel + 1, simpleKeyAllowed := true }

def scanFlowSequenceEnd (s : ScannerState) : ScannerState :=
  let s' := s.emit .flowSequenceEnd
  { s'.advance with flowLevel := if s'.flowLevel > 0 then s'.flowLevel - 1 else 0,
                    simpleKeyAllowed := false }

def scanFlowMappingStart (s : ScannerState) : ScannerState :=
  let s' := { s with simpleKey := { possible := false } }
  let s' := s'.emit .flowMappingStart
  { s'.advance with flowLevel := s'.flowLevel + 1, simpleKeyAllowed := true }

def scanFlowMappingEnd (s : ScannerState) : ScannerState :=
  let s' := s.emit .flowMappingEnd
  { s'.advance with flowLevel := if s'.flowLevel > 0 then s'.flowLevel - 1 else 0,
                    simpleKeyAllowed := false }

def scanFlowEntry (s : ScannerState) : Except ScanError ScannerState := do
  -- §7.4: Leading comma (after flow-open) or consecutive commas are invalid.
  if s.tokens.size > 0 then
    let lastTok := s.tokens[s.tokens.size - 1]!.val
    if lastTok == .flowSequenceStart || lastTok == .flowMappingStart ||
       lastTok == .flowEntry then
      throw (.invalidFlowEntry s.line s.col)
  .ok ({ (s.emit .flowEntry).advance with simpleKeyAllowed := true })

def scanBlockEntry (s : ScannerState) : Except ScanError ScannerState := do
  -- §6.1: Tab in indentation before block entry.
  -- Scan backward through whitespace consumed by skipToContent to detect any
  -- tab used as indentation for this block entry — forbidden.
  -- Handles `-\t-`, `- \t-`, `-\t -`, etc.
  if !s.inFlow then
    if s.hasTabInPrecedingWhitespace then
      throw (.tabInIndentation s.line s.col)
  let s' := if !s.inFlow then pushSequenceIndent s s.col else s
  .ok { (s'.emit .blockEntry).advance with simpleKeyAllowed := true }

def scanKey (s : ScannerState) : Except ScanError ScannerState := do
  let s' := if !s.inFlow then pushMappingIndent s s.col else s
  let s' := (s'.emit .key).advance
  -- §6.1: Tab immediately after `?` indicator in block context is
  -- indentation for the key content — forbidden.
  if !s'.inFlow then
    if let some '\t' := s'.peek? then
      throw (.tabInIndentation s'.line s'.col)
  .ok { s' with simpleKeyAllowed := true }

def scanValue (s : ScannerState) : Except ScanError ScannerState := do
  -- §7.4: "Plain keys are restricted to a single line."
  -- In block context, reject implicit keys where the key token and the `:`
  -- value indicator are on different lines.
  if s.simpleKey.possible && !s.inFlow && s.simpleKey.pos.line != s.line then
    throw (.invalidImplicitKey s.line)
  -- §8.2.1: A mapping key at the same indent as a block sequence is
  -- invalid.  Reject before building new state.
  if s.simpleKey.possible && !s.inFlow then
    let keyCol : Int := s.simpleKey.pos.col
    if keyCol <= s.currentIndent then
      if let some top := s.indents.back? then
        if top.isSequence && keyCol == top.column then
          throw (.trailingContent s.simpleKey.pos.line s.simpleKey.pos.col)
  let s' := if s.simpleKey.possible then
    let s'' := s.insertAt s.simpleKey.tokenIndex s.simpleKey.pos .key
    if !s.inFlow then
      let keyCol : Int := s.simpleKey.pos.col
      if keyCol > s''.currentIndent then
        let s3 := s''.insertAt s.simpleKey.tokenIndex s.simpleKey.pos .blockMappingStart
        { s3 with
          indents := s3.indents.push { column := keyCol, isSequence := false }
          simpleKey := { possible := false } }
      else
        { s'' with simpleKey := { possible := false } }
    else
      { s'' with simpleKey := { possible := false } }
  else
    if !s.inFlow then pushMappingIndent s s.col else s
  let s'' := (s'.emit .value).advance
  -- §6.1: Tab immediately after explicit `:` value indicator (at or below
  -- block indent level) — the tab functions as indentation for the value
  -- content, which is forbidden.  When `:` is past the indent level (inline
  -- implicit value, e.g., `key:\tval`), the tab is valid `s-separate-in-line`.
  if (s.col : Int) ≤ s.currentIndent && !s''.inFlow then
    if let some '\t' := s''.peek? then
      throw (.tabInIndentation s''.line s''.col)
  .ok { s'' with simpleKeyAllowed := true }

/-! ## Anchor and Alias Scanning -/

def scanAnchorOrAlias (s : ScannerState) (isAnchor : Bool) : ScannerState := Id.run do
  let startPos := s.currentPos
  let mut s' := s.advance
  let mut name := ""
  let fuel := s.inputEnd - s'.offset
  for _ in [:fuel] do
    match s'.peek? with
    | some c =>
      if !isFlowIndicator c && !isWhiteSpace c && !isLineBreak c then
        name := name.push c; s' := s'.advance
      else break
    | none => break
  if isAnchor then
    return { s'.emitAt startPos (.anchor name) with simpleKeyAllowed := false }
  else
    return { s'.emitAt startPos (.alias name) with simpleKeyAllowed := false }

/-! ## Tag Scanning -/

def scanTag (s : ScannerState) : ScannerState := Id.run do
  let startPos := s.currentPos
  let s' := s.advance  -- consume `!`
  match s'.peek? with
  | some '<' =>
    let mut s' := s'.advance
    let mut uri := ""
    let fuel := s.inputEnd - s'.offset
    for _ in [:fuel] do
      match s'.peek? with
      | some '>' => s' := s'.advance; break
      | some c => uri := uri.push c; s' := s'.advance
      | none => break
    return { s'.emitAt startPos (.tag "" uri) with simpleKeyAllowed := false }
  | some '!' =>
    let mut s' := s'.advance
    let mut suffix := ""
    let fuel := s.inputEnd - s'.offset
    for _ in [:fuel] do
      match s'.peek? with
      | some c =>
        if !isWhiteSpace c && !isLineBreak c && !isFlowIndicator c then
          suffix := suffix.push c; s' := s'.advance
        else break
      | none => break
    return { s'.emitAt startPos (.tag "!!" suffix) with simpleKeyAllowed := false }
  | _ =>
    let mut s' := s'
    let mut handle := "!"
    let mut chars := ""
    let fuel := s.inputEnd - s'.offset
    for _ in [:fuel] do
      match s'.peek? with
      | some '!' =>
        handle := "!" ++ chars ++ "!"
        chars := ""
        s' := s'.advance
        break
      | some c =>
        if !isWhiteSpace c && !isLineBreak c && !isFlowIndicator c then
          chars := chars.push c; s' := s'.advance
        else break
      | none => break
    let mut suffix := ""
    if handle == "!" then
      suffix := chars
    else
      let fuel' := s.inputEnd - s'.offset
      for _ in [:fuel'] do
        match s'.peek? with
        | some c =>
          if !isWhiteSpace c && !isLineBreak c && !isFlowIndicator c then
            suffix := suffix.push c; s' := s'.advance
          else break
        | none => break
    return { s'.emitAt startPos (.tag handle suffix) with simpleKeyAllowed := false }

/-! ## Directive Scanning -/

def scanDirective (s : ScannerState) : Except ScanError ScannerState := do
  -- §6.8: Directives are only allowed before a document (at stream start
  -- or after `...`). Reject directives after document content.
  if !s.allowDirectives then
    throw (.directiveAfterContent s.line)
  let startPos := s.currentPos
  let s' := s.advance  -- consume `%`
  let (name, s') := Id.run do
    let mut s' := s'
    let mut name := ""
    let fuel := s.inputEnd - s'.offset
    for _ in [:fuel] do
      match s'.peek? with
      | some c =>
        if !isWhiteSpace c && !isLineBreak c then
          name := name.push c; s' := s'.advance
        else break
      | none => break
    return (name, s')
  let s' := skipWhitespace s'
  if name == "YAML" then
    -- §6.8.1: At most one %YAML directive per document.
    if s.seenYamlDirective then
      throw (.duplicateYamlDirective s.line)
    let (major, minor, s') := Id.run do
      let mut s' := s'
      let mut major := ""
      let fuel := s.inputEnd - s'.offset
      for _ in [:fuel] do
        match s'.peek? with
        | some '.' => s' := s'.advance; break
        | some c => if c.isDigit then major := major.push c; s' := s'.advance else break
        | none => break
      let mut minor := ""
      let fuel' := s.inputEnd - s'.offset
      for _ in [:fuel'] do
        match s'.peek? with
        | some c => if c.isDigit then minor := minor.push c; s' := s'.advance else break
        | none => break
      return (major, minor, s')
    -- §6.8.1: After version, only s-separate-in-line + comment, or linebreak/EOF.
    -- c-nb-comment-text (#) requires preceding s-separate-in-line (≥1 s-white).
    let colBeforeWs := s'.col
    let s' := skipWhitespace s'
    match s'.peek? with
    | some '#' =>
      -- Verify whitespace was consumed (s-separate-in-line before #)
      if s'.col == colBeforeWs then
        throw (.directiveTrailingContent s'.line s'.col)
    | some c => if !isLineBreak c then throw (.directiveTrailingContent s'.line s'.col)
    | none => pure ()       -- EOF: ok (orphan directive caught later)
    let s' := { s'.emitAt startPos (.versionDirective major.toNat! minor.toNat!) with
                  seenYamlDirective := true, directivesPresent := true }
    .ok s'
  else if name == "TAG" then
    let (handle, tagPrefix, st) := Id.run do
      let mut st := s'
      let mut handle := ""
      let fuel := s.inputEnd - st.offset
      for _ in [:fuel] do
        match st.peek? with
        | some c =>
          if !isWhiteSpace c then handle := handle.push c; st := st.advance
          else break
        | none => break
      st := skipWhitespace st
      let mut tagPrefix := ""
      let fuel' := s.inputEnd - st.offset
      for _ in [:fuel'] do
        match st.peek? with
        | some c =>
          if !isWhiteSpace c && !isLineBreak c then
            tagPrefix := tagPrefix.push c; st := st.advance
          else break
        | none => break
      return (handle, tagPrefix, st)
    .ok { st.emitAt startPos (.tagDirective handle tagPrefix) with directivesPresent := true }
  else
    .ok (skipToEndOfLine s')

/-! ## Document Marker Scanning -/

def scanDocumentStart (s : ScannerState) : ScannerState :=
  let s' := unwindIndents s (-1)
  let s' := { s' with simpleKey := { possible := false } }
  { (s'.emit .documentStart).advanceN 3 with
    simpleKeyAllowed := true
    allowDirectives := false
    seenYamlDirective := false
    directivesPresent := false
    documentEverStarted := true }

def scanDocumentEnd (s : ScannerState) : Except ScanError ScannerState := do
  -- §9.1.2: Document end marker `...` requires an open document.
  -- If directives were present but no `---` followed, the `...` cannot
  -- close a document that was never opened.
  if s.directivesPresent && !s.documentEverStarted then
    throw (.directiveWithoutDocument s.line)
  let s' := unwindIndents s (-1)
  let s' := { s' with simpleKey := { possible := false } }
  let result := { (s'.emit .documentEnd).advanceN 3 with
    simpleKeyAllowed := true
    allowDirectives := true
    directivesPresent := false }
  -- §9.1.2: After `...`, only s-l-comments (whitespace + optional comment) allowed.
  let mut s'' := result
  -- Skip whitespace on the same line
  let fuel := s.inputEnd - s''.offset + 1
  for _ in [:fuel] do
    match s''.peek? with
    | some c =>
      if c == ' ' || c == '\t' then s'' := s''.advance
      else break
    | none => break
  -- After whitespace, must be comment (#), newline, or EOF
  match s''.peek? with
  | none => pure ()  -- EOF is fine
  | some '#' => pure ()  -- comment is fine
  | some c =>
    if isLineBreak c then pure ()  -- newline is fine
    else throw (.trailingContentAfterDocEnd s''.line s''.col)
  .ok result

/-! ## Escape Sequence Processing -/

private def parseHexEscape (s : ScannerState) (n : Nat) : Except ScanError (Char × ScannerState) := do
  let (hex, s') := Id.run do
    let mut s' := s
    let mut hex := ""
    for _ in [:n] do
      match s'.peek? with
      | some c =>
        if c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F') then
          hex := hex.push c; s' := s'.advance
        else return (hex, s')
      | none => return (hex, s')
    return (hex, s')
  if hex.length != n then
    .error (.invalidHexEscape n hex.length s'.line)
  else
    let val := hex.foldl (fun acc c =>
      acc * 16 + if c.isDigit then c.toNat - '0'.toNat
                 else if c >= 'a' then c.toNat - 'a'.toNat + 10
                 else c.toNat - 'A'.toNat + 10) 0
    if val < 0x110000 then
      .ok (Char.ofNat val, s')
    else
      .error (.unicodeOutOfRange s'.line)

def processEscape (s : ScannerState) : Except ScanError (Char × ScannerState) := do
  match s.peek? with
  | none => .error (.unterminatedEscape s.line)
  | some c =>
    let s' := s.advance
    match c with
    | '0'  => .ok ('\x00', s')
    | 'a'  => .ok ('\x07', s')
    | 'b'  => .ok ('\x08', s')
    | 't'  => .ok ('\t', s')
    | '\t' => .ok ('\t', s')
    | 'n'  => .ok ('\n', s')
    | 'v'  => .ok ('\x0B', s')
    | 'f'  => .ok ('\x0C', s')
    | 'r'  => .ok ('\r', s')
    | 'e'  => .ok ('\x1B', s')
    | ' '  => .ok (' ', s')
    | '"'  => .ok ('"', s')
    | '/'  => .ok ('/', s')
    | '\\' => .ok ('\\', s')
    | 'N'  => .ok ('\x85', s')
    | '_'  => .ok ('\xA0', s')
    | 'L'  => .ok (Char.ofNat 0x2028, s')
    | 'P'  => .ok (Char.ofNat 0x2029, s')
    | 'x'  => parseHexEscape s' 2
    | 'u'  => parseHexEscape s' 4
    | 'U'  => parseHexEscape s' 8
    | _    => .error (.unknownEscape c s.line)

/-! ## Scalar Scanning -/

/-- Trim trailing space/tab characters (YAML §6.5 flow line folding). -/
private def trimTrailingWS (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse)

def foldQuotedNewlines (s : ScannerState) : Except ScanError (String × ScannerState) := do
  let s' := consumeNewline s
  let mut s' := s'
  let mut emptyCount := (0 : Nat)
  let fuel := s.inputEnd - s'.offset + 1
  for _ in [:fuel] do
    let saved := s'
    s' := skipSpaces s'
    match s'.peek? with
    | some c =>
      if isLineBreak c then
        s' := consumeNewline s'
        emptyCount := emptyCount + 1
      else
        s' := saved; break
    | none => break
  -- §6.1: After consuming empty lines and leading spaces on the continuation
  -- line, check for tab-as-indentation.  If we haven't advanced past the
  -- current block indent level, a tab here is in the indentation zone.
  s' := skipSpaces s'
  if !s'.inFlow && (s'.col : Int) ≤ s'.currentIndent then
    if let some '\t' := s'.peek? then
      throw (.tabInIndentation s'.line s'.col)
  s' := skipWhitespace s'
  if emptyCount > 0 then
    return (String.ofList (List.replicate emptyCount '\n'), s')
  else
    return (" ", s')

def scanDoubleQuoted (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let mut s' := s.advance
  let mut content := ""
  let fuel := s.inputEnd - s'.offset + 1
  for _ in [:fuel] do
    match s'.peek? with
    | none => return ← .error (.unterminatedScalar .doubleQuoted startPos.line)
    | some '"' =>
      s' := s'.advance
      -- §7.3.2: In block context, after a double-quoted scalar, only
      -- whitespace, comments, `:` (value indicator), or end-of-line/EOF
      -- may follow on the same line. Other content is trailing garbage.
      if !s.inFlow then
        let mut probe := s'
        let probeFuel := s.inputEnd - probe.offset + 1
        for _ in [:probeFuel] do
          match probe.peek? with
          | some c => if c == ' ' || c == '\t' then probe := probe.advance else break
          | none => break
        match probe.peek? with
        | none => pure ()  -- EOF is fine
        | some c =>
          if isLineBreak c || c == '#' || c == ':' then pure ()
          else return ← .error (.trailingContent probe.line probe.col)
      return { s'.emitAt startPos (.scalar content .doubleQuoted) with simpleKeyAllowed := false }
    | some '\\' =>
      s' := s'.advance
      match s'.peek? with
      | some c =>
        if isLineBreak c then
          s' := consumeNewline s'
          s' := skipWhitespace s'
        else
          let (ch, s'') ← processEscape s'
          content := content.push ch
          s' := s''
      | none => return ← .error (.unterminatedEscape s'.line)
    | some c =>
      if isLineBreak c then
        content := trimTrailingWS content  -- YAML §6.5: trim trailing WS before fold
        let (folded, s'') ← foldQuotedNewlines s'
        -- §9.1.2: Document markers at col 0 terminate even inside quoted scalars
        if atDocumentStart s'' || atDocumentEnd s'' then
          return ← .error (.documentMarkerInScalar .doubleQuoted startPos.line)
        -- §8.1: Continuation line must be indented past current block level
        if (s''.col : Int) ≤ s.currentIndent then
          return ← .error (.underIndentedScalar .doubleQuoted s''.line)
        content := content ++ folded
        s' := s''
      else
        content := content.push c
        s' := s'.advance
  .error (.unterminatedScalar .doubleQuoted startPos.line)

def scanSingleQuoted (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let mut s' := s.advance
  let mut content := ""
  let fuel := s.inputEnd - s'.offset + 1
  for _ in [:fuel] do
    match s'.peek? with
    | none => return ← .error (.unterminatedScalar .singleQuoted startPos.line)
    | some '\'' =>
      s' := s'.advance
      match s'.peek? with
      | some '\'' =>
        content := content.push '\''
        s' := s'.advance
      | _ =>
        -- §7.3.2: In block context, after a single-quoted scalar, only
        -- whitespace, comments, `:` (value indicator), or end-of-line/EOF
        -- may follow on the same line.
        if !s.inFlow then
          let mut probe := s'
          let probeFuel := s.inputEnd - probe.offset + 1
          for _ in [:probeFuel] do
            match probe.peek? with
            | some c => if c == ' ' || c == '\t' then probe := probe.advance else break
            | none => break
          match probe.peek? with
          | none => pure ()
          | some c =>
            if isLineBreak c || c == '#' || c == ':' then pure ()
            else return ← .error (.trailingContent probe.line probe.col)
        return { s'.emitAt startPos (.scalar content .singleQuoted) with simpleKeyAllowed := false }
    | some c =>
      if isLineBreak c then
        content := trimTrailingWS content  -- YAML §6.5: trim trailing WS before fold
        let (folded, s'') ← foldQuotedNewlines s'
        -- §9.1.2: Document markers at col 0 terminate even inside quoted scalars
        if atDocumentStart s'' || atDocumentEnd s'' then
          return ← .error (.documentMarkerInScalar .singleQuoted startPos.line)
        -- §8.1: Continuation line must be indented past current block level
        if (s''.col : Int) ≤ s.currentIndent then
          return ← .error (.underIndentedScalar .singleQuoted s''.line)
        content := content ++ folded
        s' := s''
      else
        content := content.push c
        s' := s'.advance
  .error (.unterminatedScalar .singleQuoted startPos.line)

/--
Can character `c` start a plain scalar, given the next character and flow context?

**YAML 1.2.2**: [123] ns-plain-first(c) (§7.3.3)

Base rule: excludes indicators, whitespace, and line breaks.
Exception: `-`, `?`, `:` are allowed if followed by a safe character
(`ns-plain-safe` — non-blank, and in flow context, non-flow-indicator).
-/
def canStartPlainScalar (c : Char) (next : Option Char) (inFlow : Bool) : Bool :=
  if c == '-' || c == '?' || c == ':' then
    match next with
    | some n => !isWhiteSpace n && !isLineBreak n && !(inFlow && isFlowIndicator n)
    | none => false
  else
    !isIndicator c && !isWhiteSpace c && !isLineBreak c

def isPlainSafe (c : Char) (inFlow : Bool) : Bool :=
  if inFlow then
    !isWhiteSpace c && !isLineBreak c && !isFlowIndicator c
  else
    !isWhiteSpace c && !isLineBreak c

def scanPlainScalar (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let inFlow := s.inFlow
  -- §7.3.3: Continuation lines must be indented past the current block level.
  -- Use currentIndent + 1 (not s.col) so that continuation correctly includes
  -- lines at the block's content region, matching YAML 1.2.2 §7.3.3 / libyaml.
  let contentIndent := if inFlow then s.col
    else (max 0 (s.currentIndent + 1)).toNat
  let mut s' := s
  let mut content := ""
  let mut spaces := ""
  let fuel := (s.inputEnd - s.offset + 1) * 2
  for _ in [:fuel] do
    match s'.peek? with
    | none => break
    | some c =>
      -- ` #` terminates
      if c == '#' && spaces.length > 0 then break
      -- `: ` terminates at value indicator position
      if c == ':' then
        let next := s'.peekAt? 1
        let terminates := match next with
          | some n => isBlank n || (inFlow && isFlowIndicator n)
          | none => true
        if terminates then break
      -- Flow indicators terminate in flow context
      if inFlow && isFlowIndicator c then break
      -- Document boundary at col 0 terminates
      if s'.col == 0 && atDocumentBoundary s' then break
      -- Line break: check continuation
      if isLineBreak c then
        if inFlow then
          let (folded, s'') ← foldQuotedNewlines s'
          -- §7.3.3 [131]: After folding a newline to whitespace, `#` is
          -- preceded by whitespace and starts a comment (terminating the
          -- scalar).  `foldQuotedNewlines` already skipped leading
          -- whitespace on the continuation line, so s'' points at the
          -- first non-whitespace character.
          match s''.peek? with
          | some '#' => s' := s''; break
          | _ => pure ()
          content := content ++ folded  -- drop trailing `spaces` per YAML §6.5
          spaces := ""
          s' := s''
        else
          let saved := s'
          let s'' := consumeNewline s'
          -- Skip blank lines
          let (emptyCount, s'') := Id.run do
            let mut s'' := s''
            let mut cnt := (0 : Nat)
            let bfuel := s.inputEnd - s''.offset + 1
            for _ in [:bfuel] do
              let sv := s''
              s'' := skipSpaces s''
              match s''.peek? with
              | some bc =>
                if isLineBreak bc then
                  s'' := consumeNewline s''
                  cnt := cnt + 1
                else
                  s'' := sv; break
              | none => break
            return (cnt, s'')
          let s'' := skipSpaces s''
          if s''.col < contentIndent then
            s' := saved; break
          if atDocumentBoundary s'' then
            s' := saved; break
          if emptyCount > 0 then
            content := content ++ String.ofList (List.replicate emptyCount '\n')
          else
            content := content ++ " "  -- drop trailing `spaces` per YAML §6.5
          spaces := ""
          s' := s''
        continue
      -- Whitespace accumulates
      if isWhiteSpace c then
        spaces := spaces.push c; s' := s'.advance; continue
      -- Regular content character
      if !isPlainSafe c inFlow then break
      content := content ++ spaces
      spaces := ""
      content := content.push c
      s' := s'.advance
  -- Trim trailing whitespace: plain scalars never have trailing WS per §7.3.3
  content := trimTrailingWS content
  return { s'.emitAt startPos (.scalar content .plain) with simpleKeyAllowed := false }

/-- States for folded block scalar newline processing (YAML 1.2.2 §8.1.3).

    The YAML spec distinguishes four contexts that determine how a newline
    is folded:

    - `start`   — before any content has been accumulated
    - `content` — after a normal content line (`s-nb-folded-text` [171]);
                   a following single newline is folded to a space
    - `empty`   — after a blank line (`b-l-trimmed` [170]);
                   newline is preserved (becomes `\n`)
    - `more`    — after a more-indented line (`s-nb-spaced-text` [173]);
                   newline is preserved (becomes `\n`)

    Defining these as an inductive rather than encoding in a `Bool` makes
    each case a named constructor for pattern matching in proofs. -/
private inductive FoldState where
  | start   : FoldState
  | content : FoldState
  | empty   : FoldState
  | more    : FoldState
  deriving Repr, BEq

/-- Fold newlines in block scalar content per YAML 1.2.2 §8.1.3.

    **Implements** (folding pass for `[174] c-l+folded(n)`):
    - `[171] s-nb-folded-text(n)` — normal content line → fold newline to space
    - `[172] b-l-spaced(n)`       — more-indented line  → preserve newline
    - `[173] s-nb-spaced-text(n)` — more-indented line content
    - `[170] b-l-trimmed(n,c)`    — blank line           → preserve newline

    Input `raw` has already had indentation stripped by `scanBlockScalar`;
    lines at column 0 are content, lines starting with a space are
    more-indented.

    **State machine** (`FoldState`):
    - `start`   — initial state, no pending newline
    - `content` — in a normal content line; a pending newline folds to space
    - `empty`   — saw at least one blank line; pending newlines preserved
    - `more`    — in/after a more-indented line; pending newlines preserved

    On `\n`: don't emit yet — record blank lines in `pendingNL` count.
    On first non-`\n` char of a new line: emit pending newlines based on
    state and line classification (space-leading → more, otherwise → content). -/
private def foldBlockContent (raw : String) : String :=
  go raw.toList "" .start 0
where
  appendNewlines (acc : String) : Nat → String
    | 0 => acc
    | n + 1 => appendNewlines (acc.push '\n') n
  go : List Char → String → FoldState → Nat → String
    -- End of input: don't emit trailing newlines (chomping handles them)
    | [], acc, _, _ => acc
    -- Newline: don't emit yet, increment pending count
    | '\n' :: rest, acc, st, pending =>
      go rest acc st (pending + 1)
    -- First non-newline char after line boundary (pending > 0):
    -- Decide what to emit for the pending newline(s).
    -- `pending + 1` is the total number of `\n` chars seen since last content.
    | c :: rest, acc, st, pending + 1 =>
      -- Classify this new line: space-leading → more-indented [173]
      let isMore := c == ' '
      let newSt := if isMore then FoldState.more else .content
      -- Emit pending newline(s) based on previous line state.
      -- The rules derive from YAML 1.2.2 productions [170]-[181]:
      --   content→1→content : b-as-space [176] → fold to ` `
      --   content→1→more    : b-as-line-feed [177] → `\n`
      --   content→N>1→content : b-non-content + (N-1) l-empty → (N-1) `\n`s
      --   content→N>1→more   : b-as-line-feed + (N-1) l-empty → N `\n`s
      --   more→N→any         : b-as-line-feed + (N-1) l-empty → N `\n`s
      --   start→N→any        : l-empty × N → N `\n`s
      let acc := match st with
        | .start => appendNewlines acc (pending + 1)
        | .content =>
          if pending == 0 && !isMore then
            -- Single newline between two content lines → fold to space
            acc.push ' '
          else if pending == 0 && isMore then
            -- Single newline, content → more → preserve as line-feed
            acc.push '\n'
          else if isMore then
            -- Multiple newlines, next is more → all preserved
            appendNewlines acc (pending + 1)
          else
            -- Multiple newlines, next is content → first is b-non-content (silent)
            appendNewlines acc pending
        | .more => appendNewlines acc (pending + 1)
        | .empty => appendNewlines acc (pending + 1)  -- shouldn't occur in practice
      go rest (acc.push c) newSt 0
    -- Normal character within a line (pending == 0)
    | c :: rest, acc, st, 0 =>
      let newSt := match st with
        | .start => if c == ' ' then FoldState.more else .content
        | s => s
      go rest (acc.push c) newSt 0

/-- Scan a block scalar (literal `|` or folded `>`).

    **Implements** (YAML 1.2.2 §8.1):
    - `[170] c-l+literal(n)` = `"|" c-b-block-header(t,m) l-literal-content(n+m,t)`
    - `[174] c-l+folded(n)`  = `">" c-b-block-header(t,m) l-folded-content(n+m,t)`
    - `[162] c-b-block-header(t,m)` = `(c-indentation-indicator(m) c-chomping-indicator(t) | ...) s-b-comment`
    - `[163] c-indentation-indicator(m)` = `ns-dec-digit` (explicit) | `ε` (auto-detect)
    - `[164] c-chomping-indicator(t)` = `"-"` (STRIP) | `"+"` (KEEP) | `ε` (CLIP)
    - `[171] l-nb-literal-text(n)` = `l-empty(n,BLOCK-IN)* s-indent(n) nb-char+`
    - `[63]  s-indent(n)` = `s-space × n`  ← **spaces only**

    **Variable classification:**
    | Variable          | Kind     | Spec equivalent | Description |
    |-------------------|----------|-----------------|-------------|
    | `startPos`        | Pos      | —               | Position of `\|`/`>` for token attribution |
    | `parentIndent`    | Position | `n`             | Column of `\|`/`>` indicator (caller's indent level) |
    | `explicitOffset`  | Distance | `m` (explicit)  | 1–9 from `c-indentation-indicator`, or `none` |
    | `minContentIndent`| Position | `n + 1`         | Floor: spec requires `m ≥ 1`, so content ≥ `n + 1` |
    | `contentIndent`   | Position | `n + m`         | Target column for content lines |
    | `spacesConsumed`  | Distance | count in `s-indent(n+m)` | Spaces matched at start of content line |

    **Pre**: Scanner at `|` or `>`. `s.col` = `n` (parent indent level).
    **Post**: Scanner past block scalar content. Emits `.scalar content style`.
    **Error**: Missing newline after header. -/
def scanBlockScalar (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos  -- Pos: position of `|`/`>` indicator
  let isLiteral := s.peek? == some '|'
  let s' := s.advance
  -- Parse header: c-b-block-header(t,m) [162]
  let (chomp, explicitOffset, s') := Id.run do
    let mut s' := s'
    let mut chomp : ChompStyle := .clip          -- t: c-chomping-indicator [164]
    let mut explicitOffset : Option Nat := none  -- m: c-indentation-indicator [163] (Distance)
    for _ in [:2] do
      match s'.peek? with
      | some '-' => chomp := .strip; s' := s'.advance
      | some '+' => chomp := .keep; s' := s'.advance
      | some c =>
        if c.isDigit && c != '0' then
          explicitOffset := some (c.toNat - '0'.toNat)  -- Distance: 1–9
          s' := s'.advance
      | none => pure ()
    return (chomp, explicitOffset, s')
  -- s-b-comment: skip trailing whitespace and optional comment after header
  -- §6.7: c-nb-comment-text (#) requires preceding s-separate-in-line (≥1 s-white).
  let s' := skipWhitespace s'  -- s-separate-in-line [66]: s-white* (tabs ok here)
  let s' := match s'.peek? with
    | some '#' =>
      -- Check raw input: # must be preceded by whitespace (not at start-of-line here)
      let commentOk := match s'.peekBack? with
        | some c => isWhiteSpace c || isLineBreak c || c == '\uFEFF'  -- BOM is transparent (§5.2)
        | none => false
      if commentOk then skipToEndOfLine s'  -- c-nb-comment-text [77]: whitespace preceded `#`
      else s'  -- `#` without preceding whitespace — not a comment
    | _ => s'
  -- b-comment [76]: consume newline after header
  let s' ← match s'.peek? with
    | some c =>
      if isLineBreak c then .ok (consumeNewline s')
      else if !s'.hasMore then .ok s'
      else .error (.expectedNewline s'.line)
    | none => .ok s'
  -- Determine content indentation: n+m
  -- parentIndent = n = parent block's indentation level (§8.1.2).
  -- Uses currentIndent (Int, -1 at stream level) so that top-level block
  -- scalars correctly allow content at column 0, and nested block scalars
  -- use the block's indent rather than the column of the `|`/`>` indicator.
  let parentIndent : Int := s.currentIndent
  -- minContentIndent (Position) = n+1: spec §8.1.3 requires m ≥ 1
  let minContentIndent : Nat := (max 0 (parentIndent + 1)).toNat
  let (contentIndent, autoDetectTabErr?) := match explicitOffset with
    | some m =>
      -- Explicit: contentIndent (Position) = parentIndent (Position) + m (Distance)
      ((max 0 (parentIndent + (m : Int))).toNat, (none : Option (Nat × Nat)))
    | none =>
      -- Auto-detect: scan ahead past blank lines to find first content line.
      -- The detected column must respect the floor (minContentIndent).
      -- Uses skipSpaces (not skipWhitespace) because s-indent uses spaces only [63].
      Id.run do
        let mut probe := s'
        let fuel := s.inputEnd - probe.offset + 1
        for _ in [:fuel] do
          probe := skipSpaces probe
          match probe.peek? with
          | some c =>
            -- §6.1: Tab at col < minContentIndent is in the indentation zone
            -- where s-indent requires spaces only. Reject immediately.
            if c == '\t' && probe.col < minContentIndent then
              return (0, some (probe.line, probe.col))
            if isLineBreak c then
              -- §8.1.3: l-empty(n) lines have at most n = minContentIndent
              -- spaces.  Lines with more spaces are content lines (the
              -- trailing spaces are nb-char content) and set the indent.
              if probe.col > minContentIndent then
                return (probe.col, none)  -- whitespace-only content line
              probe := consumeNewline probe
            else
              -- detectedIndent (Position) = first content line's column
              -- contentIndent = max(minContentIndent, detectedIndent)
              -- If detectedIndent < minContentIndent, scalar has no content
              -- (the collection loop will terminate immediately).
              return (max minContentIndent probe.col, none)
          | none => break
        return (minContentIndent, none)  -- no content found; use floor
  if let some (line, col) := autoDetectTabErr? then
    throw (.tabInIndentation line col)
  -- Collect content: l-literal-content / l-folded-content
  -- Each content line must match: s-indent(contentIndent) nb-char+
  -- Empty lines (l-empty): s-indent(≤contentIndent) b-as-line-feed
  let (rawContent, s') := Id.run do
    let mut s' := s'
    let mut rawContent := ""
    let fuel := s.inputEnd - s'.offset + 1
    for _ in [:fuel] do
      -- §9.1.4 / §9.2: Document markers `---` and `...` at column 0 always
      -- terminate block scalar content, regardless of indentation.
      if s'.col == 0 && atDocumentBoundary s' then break
      -- Try to consume s-indent(contentIndent): exactly `contentIndent` spaces [63]
      let (spacesConsumed, s'') := Id.run do  -- spacesConsumed: Distance
        let mut s' := s'
        let mut cnt := (0 : Nat)
        for _ in [:contentIndent] do
          match s'.peek? with
          | some ' ' => s' := s'.advance; cnt := cnt + 1
          | _ => break
        return (cnt, s')
      s' := s''
      match s'.peek? with
      | none => break
      | some c =>
        if isLineBreak c then
          -- l-empty line: fewer than contentIndent spaces followed by line break
          rawContent := rawContent.push '\n'
          s' := consumeNewline s'
        else if spacesConsumed < contentIndent && !isLineBreak c then
          -- Less-indented non-empty line: end of block scalar content
          break
        else
          -- nb-char+: content characters until line break
          let innerFuel := s.inputEnd - s'.offset + 1
          for _ in [:innerFuel] do
            match s'.peek? with
            | some c' => if isLineBreak c' then break else rawContent := rawContent.push c'; s' := s'.advance
            | none => break
          match s'.peek? with
          | some c' => if isLineBreak c' then rawContent := rawContent.push '\n'; s' := consumeNewline s'
          | none => pure ()
    return (rawContent, s')
  -- Apply chomp: c-chomping-indicator(t) [164]
  let stripTrailingNewlines (str : String) : String :=
    String.ofList (str.toList.reverse.dropWhile (· == '\n') |>.reverse)
  let content := match chomp with
    | .strip => stripTrailingNewlines rawContent        -- t=STRIP: no final line breaks
    | .clip =>
      let stripped := stripTrailingNewlines rawContent
      if rawContent.endsWith "\n" then stripped ++ "\n" else stripped  -- t=CLIP: single final
    | .keep => rawContent                               -- t=KEEP: all trailing line breaks
  -- Apply folding (for `>` only): l-folded-content [174]
  let content := if isLiteral then content else foldBlockContent content
  let style := if isLiteral then ScalarStyle.literal else ScalarStyle.folded
  -- Block scalars cannot be implicit keys (§7.4): clear stale simpleKey.
  -- After a block scalar the scanner is at the start of the next line where
  -- new simple keys are allowed, so set simpleKeyAllowed := true.
  .ok ({ s'.emitAt startPos (.scalar content style) with
    simpleKeyAllowed := true
    simpleKey := { possible := false } })

/-! ## Main Scanner Loop -/

def saveSimpleKey (st : ScannerState) : ScannerState :=
  if st.simpleKeyAllowed && !st.inFlow then
    { st with simpleKey := {
        possible := true
        tokenIndex := st.tokens.size
        pos := st.currentPos
        endLine := st.line } }
  else if st.simpleKeyAllowed && st.inFlow then
    { st with simpleKey := {
        possible := true
        tokenIndex := st.tokens.size
        pos := st.currentPos
        endLine := st.line } }
  else st

/-- Scan the next token from the input.

    **Implements**: Main dispatch loop for YAML token recognition.
    Called repeatedly by `scan` until input is exhausted.

    Flow:
    1. `skipToContent` — advance past `s-l-comments` ([79])
    2. Indent check — `unwindIndents` for block context (emits `blockEnd` tokens)
    3. `saveSimpleKey` — record potential implicit key position
    4. Character dispatch — delegate to specific scanner based on current char

    **Pre**: Scanner state from previous token (or initial state).
    **Post**: Scanner past one token. Token emitted. State updated.
    **Error**: Unexpected character at current position. -/
def scanNextToken (s : ScannerState) : Except ScanError (Option ScannerState) := do
  -- Step 1: Skip to content — s-l-comments [79]
  let s ← skipToContent s
  if !s.hasMore then
    return none
  -- Step 2: Indent check — unwind block collections when de-indented
  --   §6.1: After unwinding, if the new content's column is strictly
  --   between the current indent level and the just-popped level, the
  --   content is at an invalid intermediate indentation.
  let savedIndentSize := s.indents.size
  let s := if !s.inFlow && s.needIndentCheck then
    let s := unwindIndents s s.col
    { s with needIndentCheck := false }
  else s
  -- Check for intermediate indentation after unwind.
  -- If unwindIndents popped levels (stack shrank) AND the content column
  -- is strictly deeper than the new currentIndent, the content is at an
  -- indentation level that doesn't match any enclosing block collection.
  if s.indents.size < savedIndentSize && (s.col : Int) > s.currentIndent then
    return ← .error (.trailingContent s.line s.col)
  -- Step 3: Save simple key position for potential implicit key
  let s := saveSimpleKey s
  match s.peek? with
  | none =>
    return none
  | some c =>
    -- §8.1 / §7.5: Flow content inside a block structure must be more
    -- indented than the enclosing block collection. Check on new lines
    -- (not the opening line of the flow collection).
    -- Only check when there IS an enclosing block (currentIndent ≥ 0).
    if s.inFlow && s.currentIndent >= 0 && (s.col : Int) <= s.currentIndent then
      -- Allow flow-close indicators (they end the flow, so indent doesn't apply)
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
    -- Any non-directive, non-document-marker content means we're in a document.
    -- Disallow directives until the next `...` document-end marker.
    let s := if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true }
    else s
    if c == '[' then return some (scanFlowSequenceStart s)
    if c == ']' then
      if s.flowLevel == 0 then return ← .error (.flowEndOutsideFlow ']' s.line s.col)
      let s' := scanFlowSequenceEnd s
      -- §7.5: When a flow collection close returns us to block context,
      -- only whitespace, comments, `:`, or end-of-line may follow on the same line.
      if s'.flowLevel == 0 then
        let mut probe := s'
        let probeFuel := s.inputEnd - probe.offset + 1
        for _ in [:probeFuel] do
          match probe.peek? with
          | some pc => if pc == ' ' || pc == '\t' then probe := probe.advance else break
          | none => break
        match probe.peek? with
        | none => pure ()
        | some pc =>
          if isLineBreak pc || pc == '#' || pc == ':' then pure ()
          else return ← .error (.trailingContent probe.line probe.col)
      return some s'
    if c == '{' then return some (scanFlowMappingStart s)
    if c == '}' then
      if s.flowLevel == 0 then return ← .error (.flowEndOutsideFlow '}' s.line s.col)
      let s' := scanFlowMappingEnd s
      if s'.flowLevel == 0 then
        let mut probe := s'
        let probeFuel := s.inputEnd - probe.offset + 1
        for _ in [:probeFuel] do
          match probe.peek? with
          | some pc => if pc == ' ' || pc == '\t' then probe := probe.advance else break
          | none => break
        match probe.peek? with
        | none => pure ()
        | some pc =>
          if isLineBreak pc || pc == '#' || pc == ':' then pure ()
          else return ← .error (.trailingContent probe.line probe.col)
      return some s'
    if c == ',' then
      -- §7.4.2: Flow entry indicator `,` is only valid inside flow collections.
      if s.flowLevel == 0 then return ← .error (.flowEndOutsideFlow ',' s.line s.col)
      let s' ← scanFlowEntry s
      return some s'
    if c == '-' && !s.inFlow then
      let next := s.peekAt? 1
      let isEntry := match next with
        | some n => isBlank n
        | none => true
      if isEntry then
        let s' ← scanBlockEntry s
        return some s'
    if c == '?' then
      let next := s.peekAt? 1
      let isKey := match next with
        | some n => isBlank n || (s.inFlow && isFlowIndicator n)
        | none => true
      if isKey then
        let s' ← scanKey s
        return some s'
    if c == ':' then
      -- YAML §7.4 / libyaml: In flow context, `:` is a value indicator
      -- whenever a simple key is possible (e.g., after a quoted scalar),
      -- regardless of the character that follows.
      -- In block context (or flow without a simple key), `:` requires
      -- a trailing blank or flow indicator.
      let isValue := if s.inFlow && s.simpleKey.possible then
        true
      else
        let next := s.peekAt? 1
        match next with
        | some n => isBlank n || (s.inFlow && isFlowIndicator n)
        | none => true
      if isValue then
        let s' ← scanValue s
        return some s'
    if c == '&' then return some (scanAnchorOrAlias s true)
    if c == '*' then return some (scanAnchorOrAlias s false)
    if c == '!' then return some (scanTag s)
    if c == '|' || c == '>' then
      let s' ← scanBlockScalar s
      return some s'
    if c == '"' then
      let s' ← scanDoubleQuoted s
      -- §7.4: Quoted scalars can span lines; update simpleKey.endLine
      -- so scanValue can check key-end-line vs `:` line.
      let s' := if s'.simpleKey.possible then
        { s' with simpleKey := { s'.simpleKey with endLine := s'.line } }
      else s'
      return some s'
    if c == '\'' then
      let s' ← scanSingleQuoted s
      let s' := if s'.simpleKey.possible then
        { s' with simpleKey := { s'.simpleKey with endLine := s'.line } }
      else s'
      return some s'
    if canStartPlainScalar c (s.peekAt? 1) s.inFlow then
      let s' ← scanPlainScalar s; return some s'
    .error (.unexpectedChar c s.line s.col)

/-- Run the scanner on an input string, producing a token array.

    **Post-condition**: starts with `streamStart`, ends with `streamEnd`. -/
def scan (input : String) : Except ScanError (Array (Positioned YamlToken)) := do
  let mut s := ScannerState.mk' input
  s := s.emit .streamStart
  -- Handle BOM
  match s.peek? with
  | some '\uFEFF' => s := s.advance
  | _ => pure ()
  let fuel := input.utf8ByteSize + 1
  for _ in [:fuel * 4] do
    match ← scanNextToken s with
    | some s' => s := s'
    | none =>
      -- §7.4: Unclosed flow collections are an error.
      if s.flowLevel > 0 then
        throw (.unterminatedFlowCollection '[' s.line)
      -- §6.8: If directives were present but no document followed, error.
      if s.directivesPresent && !s.documentEverStarted then
        throw (.directiveWithoutDocument s.line)
      let final := unwindIndents s (-1)
      let final := final.emit .streamEnd
      return final.tokens
  .error (.fuelExhausted s.line s.col)

end Lean4Yaml.Scanner
