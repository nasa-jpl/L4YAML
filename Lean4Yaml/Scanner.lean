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

The scanner is a **pure function** `String → Except String (Array (Positioned YamlToken))`.
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
def skipToContent (s : ScannerState) : Except String ScannerState := do
  let fuel := s.inputEnd - s.offset + 1
  let mut s' := s
  for _ in [:fuel] do
    -- After a newline, use skipSpaces for indentation (s-indent [63]: spaces only).
    -- Then check for tab-as-indentation, using currentIndent to determine the
    -- boundary between indentation territory and separation territory.
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
              throw s!"tab character in indentation at line {s'.line}, column {s'.col}"
          | none => s' := skipWhitespace s'        -- tab before EOF: allowed
        | _ => pure ()
      else
        -- Past indentation boundary or in flow context: tabs are legal separation
        s' := skipWhitespace s'
    else
      s' := skipWhitespace s'
    match s'.peek? with
    | some '#' => s' := skipToEndOfLine s'
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

def scanFlowEntry (s : ScannerState) : ScannerState :=
  { (s.emit .flowEntry).advance with simpleKeyAllowed := true }

def scanBlockEntry (s : ScannerState) : ScannerState :=
  let s' := if !s.inFlow then pushSequenceIndent s s.col else s
  { (s'.emit .blockEntry).advance with simpleKeyAllowed := true }

def scanKey (s : ScannerState) : ScannerState :=
  let s' := if !s.inFlow then pushMappingIndent s s.col else s
  { (s'.emit .key).advance with simpleKeyAllowed := true }

def scanValue (s : ScannerState) : ScannerState :=
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
  (s'.emit .value).advance |> fun s => { s with simpleKeyAllowed := true }

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

def scanDirective (s : ScannerState) : Except String ScannerState := do
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
    .ok (s'.emitAt startPos (.versionDirective major.toNat! minor.toNat!))
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
    .ok (st.emitAt startPos (.tagDirective handle tagPrefix))
  else
    .ok (skipToEndOfLine s')

/-! ## Document Marker Scanning -/

def scanDocumentStart (s : ScannerState) : ScannerState :=
  let s' := unwindIndents s (-1)
  let s' := { s' with simpleKey := { possible := false } }
  { (s'.emit .documentStart).advanceN 3 with simpleKeyAllowed := true }

def scanDocumentEnd (s : ScannerState) : ScannerState :=
  let s' := unwindIndents s (-1)
  let s' := { s' with simpleKey := { possible := false } }
  { (s'.emit .documentEnd).advanceN 3 with simpleKeyAllowed := true }

/-! ## Escape Sequence Processing -/

private def parseHexEscape (s : ScannerState) (n : Nat) : Except String (Char × ScannerState) := do
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
    .error s!"expected {n} hex digits in escape at line {s'.line}"
  else
    let val := hex.foldl (fun acc c =>
      acc * 16 + if c.isDigit then c.toNat - '0'.toNat
                 else if c >= 'a' then c.toNat - 'a'.toNat + 10
                 else c.toNat - 'A'.toNat + 10) 0
    if val < 0x110000 then
      .ok (Char.ofNat val, s')
    else
      .error s!"unicode escape out of range at line {s'.line}"

def processEscape (s : ScannerState) : Except String (Char × ScannerState) := do
  match s.peek? with
  | none => .error s!"unexpected end of input in escape at line {s.line}"
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
    | _    => .error s!"unknown escape '\\{c}' at line {s.line}"

/-! ## Scalar Scanning -/

/-- Trim trailing space/tab characters (YAML §6.5 flow line folding). -/
private def trimTrailingWS (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse)

def foldQuotedNewlines (s : ScannerState) : (String × ScannerState) := Id.run do
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
  s' := skipWhitespace s'
  if emptyCount > 0 then
    return (String.ofList (List.replicate emptyCount '\n'), s')
  else
    return (" ", s')

def scanDoubleQuoted (s : ScannerState) : Except String ScannerState := do
  let startPos := s.currentPos
  let mut s' := s.advance
  let mut content := ""
  let fuel := s.inputEnd - s'.offset + 1
  for _ in [:fuel] do
    match s'.peek? with
    | none => return ← .error s!"unterminated double-quoted scalar at line {startPos.line}"
    | some '"' =>
      s' := s'.advance
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
      | none => return ← .error s!"unterminated escape at end of input"
    | some c =>
      if isLineBreak c then
        content := trimTrailingWS content  -- YAML §6.5: trim trailing WS before fold
        let (folded, s'') := foldQuotedNewlines s'
        content := content ++ folded
        s' := s''
      else
        content := content.push c
        s' := s'.advance
  .error s!"unterminated double-quoted scalar at line {startPos.line}"

def scanSingleQuoted (s : ScannerState) : Except String ScannerState := do
  let startPos := s.currentPos
  let mut s' := s.advance
  let mut content := ""
  let fuel := s.inputEnd - s'.offset + 1
  for _ in [:fuel] do
    match s'.peek? with
    | none => return ← .error s!"unterminated single-quoted scalar at line {startPos.line}"
    | some '\'' =>
      s' := s'.advance
      match s'.peek? with
      | some '\'' =>
        content := content.push '\''
        s' := s'.advance
      | _ => return { s'.emitAt startPos (.scalar content .singleQuoted) with simpleKeyAllowed := false }
    | some c =>
      if isLineBreak c then
        content := trimTrailingWS content  -- YAML §6.5: trim trailing WS before fold
        let (folded, s'') := foldQuotedNewlines s'
        content := content ++ folded
        s' := s''
      else
        content := content.push c
        s' := s'.advance
  .error s!"unterminated single-quoted scalar at line {startPos.line}"

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

def scanPlainScalar (s : ScannerState) : ScannerState := Id.run do
  let startPos := s.currentPos
  let inFlow := s.inFlow
  let contentIndent := s.col
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
          let (folded, s'') := foldQuotedNewlines s'
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

private def foldBlockContent (raw : String) : String :=
  go raw.toList "" false
where
  go : List Char → String → Bool → String
    | [], acc, _ => acc
    | '\n' :: '\n' :: rest, acc, _ =>
      go ('\n' :: rest) (acc.push '\n') true
    | '\n' :: rest, acc, prevWasNewline =>
      if prevWasNewline then go rest (acc.push '\n') false
      else match rest with
        | [] => acc
        | '\n' :: _ => go rest (acc.push '\n') true
        | _ => go rest (acc.push ' ') false
    | c :: rest, acc, _ => go rest (acc.push c) false

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
def scanBlockScalar (s : ScannerState) : Except String ScannerState := do
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
  let s' := skipWhitespace s'  -- s-separate-in-line [66]: s-white* (tabs ok here)
  let s' := match s'.peek? with
    | some '#' => skipToEndOfLine s'  -- c-nb-comment-text [77]
    | _ => s'
  -- b-comment [76]: consume newline after header
  let s' ← match s'.peek? with
    | some c =>
      if isLineBreak c then .ok (consumeNewline s')
      else if !s'.hasMore then .ok s'
      else .error s!"expected newline after block scalar header at line {s'.line}"
    | none => .ok s'
  -- Determine content indentation: n+m
  -- parentIndent (Position) = n = column of `|`/`>` indicator
  let parentIndent := s.col
  -- minContentIndent (Position) = n+1: spec §8.1.3 requires m ≥ 1
  let minContentIndent := parentIndent + 1
  let contentIndent := match explicitOffset with
    | some m =>
      -- Explicit: contentIndent (Position) = parentIndent (Position) + m (Distance)
      parentIndent + m
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
            if isLineBreak c then probe := consumeNewline probe
            else
              -- detectedIndent (Position) = first content line's column
              -- contentIndent = max(minContentIndent, detectedIndent)
              -- If detectedIndent < minContentIndent, scalar has no content
              -- (the collection loop will terminate immediately).
              return max minContentIndent probe.col
          | none => break
        return minContentIndent  -- no content found; use floor
  -- Collect content: l-literal-content / l-folded-content
  -- Each content line must match: s-indent(contentIndent) nb-char+
  -- Empty lines (l-empty): s-indent(≤contentIndent) b-as-line-feed
  let (rawContent, s') := Id.run do
    let mut s' := s'
    let mut rawContent := ""
    let fuel := s.inputEnd - s'.offset + 1
    for _ in [:fuel] do
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
  .ok ({ s'.emitAt startPos (.scalar content style) with simpleKeyAllowed := false })

/-! ## Main Scanner Loop -/

def saveSimpleKey (st : ScannerState) : ScannerState :=
  if st.simpleKeyAllowed && !st.inFlow then
    { st with simpleKey := {
        possible := true
        tokenIndex := st.tokens.size
        pos := st.currentPos } }
  else if st.simpleKeyAllowed && st.inFlow then
    { st with simpleKey := {
        possible := true
        tokenIndex := st.tokens.size
        pos := st.currentPos } }
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
def scanNextToken (s : ScannerState) : Except String (Option ScannerState) := do
  -- Step 1: Skip to content — s-l-comments [79]
  let s ← skipToContent s
  if !s.hasMore then
    return none
  -- Step 2: Indent check — unwind block collections when de-indented
  let s := if !s.inFlow && s.needIndentCheck then
    let s := unwindIndents s s.col
    { s with needIndentCheck := false }
  else s
  -- Step 3: Save simple key position for potential implicit key
  let s := saveSimpleKey s
  match s.peek? with
  | none =>
    return none
  | some c =>
    if s.col == 0 && atDocumentStart s then return some (scanDocumentStart s)
    if s.col == 0 && atDocumentEnd s then return some (scanDocumentEnd s)
    if c == '%' && s.col == 0 then
      let s' ← scanDirective s
      return some s'
    if c == '[' then return some (scanFlowSequenceStart s)
    if c == ']' then return some (scanFlowSequenceEnd s)
    if c == '{' then return some (scanFlowMappingStart s)
    if c == '}' then return some (scanFlowMappingEnd s)
    if c == ',' then return some (scanFlowEntry s)
    if c == '-' && !s.inFlow then
      let next := s.peekAt? 1
      let isEntry := match next with
        | some n => isBlank n
        | none => true
      if isEntry then return some (scanBlockEntry s)
    if c == '?' then
      let next := s.peekAt? 1
      let isKey := match next with
        | some n => isBlank n || (s.inFlow && isFlowIndicator n)
        | none => true
      if isKey then return some (scanKey s)
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
      if isValue then return some (scanValue s)
    if c == '&' then return some (scanAnchorOrAlias s true)
    if c == '*' then return some (scanAnchorOrAlias s false)
    if c == '!' then return some (scanTag s)
    if c == '|' || c == '>' then
      let s' ← scanBlockScalar s
      return some s'
    if c == '"' then
      let s' ← scanDoubleQuoted s
      return some s'
    if c == '\'' then
      let s' ← scanSingleQuoted s
      return some s'
    if canStartPlainScalar c (s.peekAt? 1) s.inFlow then
      return some (scanPlainScalar s)
    .error s!"unexpected character '{c}' at line {s.line}, column {s.col}"

/-- Run the scanner on an input string, producing a token array.

    **Post-condition**: starts with `streamStart`, ends with `streamEnd`. -/
def scan (input : String) : Except String (Array (Positioned YamlToken)) := do
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
      let final := unwindIndents s (-1)
      let final := final.emit .streamEnd
      return final.tokens
  .error s!"scanner fuel exhausted at line {s.line}, column {s.col}"

end Lean4Yaml.Scanner
