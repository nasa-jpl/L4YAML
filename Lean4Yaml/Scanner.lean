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
  /-- Stack of saved simple keys for enclosing flow nesting levels.
      Pushed on flow-open (`[`, `{`), popped on flow-close (`]`, `}`).
      This allows a simple key (e.g., a flow mapping used as a key:
      `{a: b}: val`) to survive nested flow collection scanning. -/
  simpleKeyStack : Array SimpleKeyState := #[]
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
  /-- Stack tracking flow collection types.  `true` = sequence (`[`),
      `false` = mapping (`{`).  Pushed on flow-open, popped on flow-close. -/
  flowStack : Array Bool := #[]
  /-- Line number of the most recent explicit `?` key indicator, if the
      entry has not yet been closed by `:`.  Used to (a) inhibit simple-key
      saving on the same line as `?`, and (b) bypass the flow-sequence
      implicit-key-single-line restriction when `?` was used. -/
  explicitKeyLine : Option Nat := none
  deriving Repr, Inhabited

/-! ### State Invariants

The following predicate captures the structural invariants that every
well-formed `ScannerState` must satisfy.  Individual operations preserve
these invariants; see `Proofs/ScannerContracts.lean` for proofs.
-/

/-- Structural well-formedness invariant for `ScannerState`.

    These four conjuncts capture the essential invariants that all scanner
    operations must preserve:
    1. **Indent stack non-empty** — the sentinel `{ column := -1 }` is never popped.
    2. **Flow level = flow stack size** — `flowLevel` and `flowStack` stay in sync.
    3. **Simple key stack = flow stack size** — `simpleKeyStack` tracks flow nesting.
    4. **Offset bounded** — the scanner never reads past the input end. -/
def ScannerState.WellFormed (s : ScannerState) : Prop :=
  s.indents.size ≥ 1
  ∧ s.flowLevel = s.flowStack.size
  ∧ s.simpleKeyStack.size = s.flowStack.size
  ∧ s.offset ≤ s.inputEnd

/-- Create initial scanner state from an input string.
    Initializes offset, line, col to zero; empty token array and indent stack. -/
def ScannerState.mk' (input : String) : ScannerState :=
  { input := input, inputEnd := input.utf8ByteSize }

/-! ## State Accessors -/

/-- Whether the scanner is currently inside a flow sequence (`[…]`),
    as opposed to a flow mapping or block context. -/
def ScannerState.isInFlowSequence (s : ScannerState) : Bool :=
  s.flowLevel > 0 && s.flowStack.back? == some true

/-- Current (offset, line, col) triple for token position attribution. -/
def ScannerState.currentPos (s : ScannerState) : YamlPos where
  offset := s.offset
  line := s.line
  col := s.col

/-- Whether the scanner has more input characters to process. -/
def ScannerState.hasMore (s : ScannerState) : Bool :=
  s.offset < s.inputEnd

/-- Peek at the current character without consuming it. -/
def ScannerState.peek? (s : ScannerState) : Option Char :=
  if s.offset < s.inputEnd then
    some (String.Pos.Raw.get s.input ⟨s.offset⟩)
  else
    none

/-- Peek at the character `n` positions ahead without consuming. -/
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

/-- Advance past the current character, updating offset/line/col.
    Newlines (`\n`) reset col to 0 and increment line. -/
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

/-- Advance past `n` characters. -/
def ScannerState.advanceN (s : ScannerState) (n : Nat) : ScannerState := Id.run do
  let mut s' := s
  for _ in [:n] do
    s' := s'.advance
  return s'

/-- Whether the scanner is inside a flow collection (`flowLevel > 0`). -/
def ScannerState.inFlow (s : ScannerState) : Bool :=
  s.flowLevel > 0

/-- The column of the innermost block collection's indentation level.
    Returns -1 at stream level (before any block is opened). -/
def ScannerState.currentIndent (s : ScannerState) : Int :=
  match s.indents.back? with
  | some e => e.column
  | none => -1

/-- Emit a token at the current scanner position. -/
def ScannerState.emit (s : ScannerState) (tok : YamlToken) : ScannerState :=
  { s with tokens := s.tokens.push { pos := s.currentPos, val := tok } }

/-- Emit a token at a previously saved position (for post-hoc token attribution). -/
def ScannerState.emitAt (s : ScannerState) (pos : YamlPos) (tok : YamlToken) : ScannerState :=
  { s with tokens := s.tokens.push { pos := pos, val := tok } }

/-- Insert a token retroactively at an earlier index in the token array.
    Used by `scanValue` to insert `key`/`blockMappingStart` at the position
    where the implicit key began (the `simpleKey.tokenIndex`). -/
def ScannerState.insertAt (s : ScannerState) (idx : Nat) (pos : YamlPos) (tok : YamlToken) : ScannerState :=
  let positioned : Positioned YamlToken := { pos := pos, val := tok }
  if idx >= s.tokens.size then
    { s with tokens := s.tokens.push positioned }
  else
    let before := s.tokens.extract 0 idx
    let after := s.tokens.extract idx s.tokens.size
    { s with tokens := (before.push positioned) ++ after }

/-! ## Character Classification

    YAML 1.2.2 character sets used by the scanner:
    - `[24][25][26] b-char` = line feed / carriage return → `isLineBreak`
    - `[33] s-white` = space / tab → `isWhiteSpace`
    - `[22] c-indicator` = all indicator characters → `isIndicator`
    - `[23] c-flow-indicator` = `,`, `[`, `]`, `{`, `}` → `isFlowIndicator`
-/

/-- `[24][25][26] b-char`: line feed (`\n`) or carriage return (`\r`). -/
def isLineBreak (c : Char) : Bool := c == '\n' || c == '\r'
/-- `[33] s-white`: space or tab. -/
def isWhiteSpace (c : Char) : Bool := c == ' ' || c == '\t'
/-- Blank: whitespace or line break. -/
def isBlank (c : Char) : Bool := isWhiteSpace c || isLineBreak c
/-- `[23] c-flow-indicator`: `,`, `[`, `]`, `{`, `}`. -/
def isFlowIndicator (c : Char) : Bool := c ∈ [',', '[', ']', '{', '}']
/-- `[22] c-indicator`: all YAML indicator characters. -/
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

/-- Skip to the end of the current line (stop before line break). -/
def skipToEndOfLine (s : ScannerState) : ScannerState := Id.run do
  let mut s' := s
  let fuel := s.inputEnd - s.offset
  for _ in [:fuel] do
    match s'.peek? with
    | some c => if isLineBreak c then break else s' := s'.advance
    | none => break
  return s'

/-- Consume a newline (LF, CR, or CRLF), setting `needIndentCheck := true`
    so the next `scanNextToken` processes indentation. -/
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
      if (s'.col : Int) ≤ s'.currentIndent then
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
        -- §7.4.2: In flow sequences, implicit keys are restricted to a
        -- single line.  Don't re-enable simple keys on newline so that
        -- `saveSimpleKey` preserves (rather than overwrites) the pending
        -- key, allowing `scanValue` to detect the line mismatch.
        -- In block context and flow mappings, newlines always allow new keys.
        if !s'.isInFlowSequence then
          s' := { s' with simpleKeyAllowed := true }
      else break
    | none => break
  return s'

/-! ## Indentation Management -/

/-- Helper for unwindIndents using structural recursion.

    **Termination**: Structurally recursive on `fuel`.
    **Invariant**: At most `fuel` iterations, each popping one indent entry. -/
def unwindIndentsLoop (s : ScannerState) (col : Int) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    if s.currentIndent > col && s.indents.size > 1 then
      let s' := s.emit .blockEnd
      let s' := { s' with indents := s'.indents.pop }
      unwindIndentsLoop s' col fuel'
    else
      s
termination_by fuel

/-- Unwind the indentation stack, emitting `blockEnd` tokens for each closed block.

    **Implements**: Virtual BLOCK-END generation (libyaml, not a single YAML production).
    The scanner's indentation stack encodes the nesting structure of block collections;
    when the current column is at or left of a block's indent, that block is closed.

    **Pre**: `col` is the column of the next content character (or -1 for stream/document end).
    **Post**: All indent entries deeper than `col` are popped; a `blockEnd` token is emitted for each.
    **Error**: None (pure computation). -/
def unwindIndents (s : ScannerState) (col : Int) : ScannerState :=
  unwindIndentsLoop s col s.indents.size

/-- Push a new block sequence indent level if `col` is deeper than `currentIndent`.

    **Implements**: Virtual BLOCK-SEQUENCE-START generation.
    Emits `blockSequenceStart` and pushes `{ column := col, isSequence := true }` onto the stack.

    **Pre**: `col` is the column of the `-` block entry indicator.
    **Post**: If `col > currentIndent`, emits `blockSequenceStart` and pushes indent entry. -/
def pushSequenceIndent (s : ScannerState) (col : Int) : ScannerState :=
  if col > s.currentIndent then
    let s' := s.emit .blockSequenceStart
    { s' with indents := s'.indents.push { column := col, isSequence := true } }
  else s

/-- Push a new block mapping indent level if `col` is deeper than `currentIndent`.

    **Implements**: Virtual BLOCK-MAPPING-START generation.
    Emits `blockMappingStart` and pushes `{ column := col, isSequence := false }` onto the stack.

    **Pre**: `col` is the implicit key's column or the `?`/`:` indicator's column.
    **Post**: If `col > currentIndent`, emits `blockMappingStart` and pushes indent entry. -/
def pushMappingIndent (s : ScannerState) (col : Int) : ScannerState :=
  if col > s.currentIndent then
    let s' := s.emit .blockMappingStart
    { s' with indents := s'.indents.push { column := col, isSequence := false } }
  else s

/-! ## Document Boundary Detection -/

/-- Check if the scanner is at a document-start marker (`---`).

    **Implements** (YAML 1.2.2 §9.1.2):
    - `[202] c-directives-end` = `"---"`

    The marker must be at column 0 and followed by a blank character or EOF.

    **Pre**: Any scanner position.
    **Post**: Pure predicate — scanner state unchanged. -/
def atDocumentStart (s : ScannerState) : Bool :=
  s.col == 0
  && s.peekAt? 0 == some '-'
  && s.peekAt? 1 == some '-'
  && s.peekAt? 2 == some '-'
  && match s.peekAt? 3 with
     | none => true
     | some c => isBlank c

/-- Check if the scanner is at a document-end marker (`...`).

    **Implements** (YAML 1.2.2 §9.1.2):
    - `[203] c-document-end` = `"..."`

    The marker must be at column 0 and followed by a blank character or EOF.

    **Pre**: Any scanner position.
    **Post**: Pure predicate — scanner state unchanged. -/
def atDocumentEnd (s : ScannerState) : Bool :=
  s.col == 0
  && s.peekAt? 0 == some '.'
  && s.peekAt? 1 == some '.'
  && s.peekAt? 2 == some '.'
  && match s.peekAt? 3 with
     | none => true
     | some c => isBlank c

/-- Check if the scanner is at any document boundary (`---` or `...`). -/
def atDocumentBoundary (s : ScannerState) : Bool :=
  atDocumentStart s || atDocumentEnd s

/-! ## Indicator Scanning -/

/-- Scan a flow sequence start indicator `[`.

    **Implements** (YAML 1.2.2 §7.4):
    - `[109] c-flow-sequence(n,c)` = `"[" s-separate(n,c)? ...`
    - `[8]   c-sequence-start` = `"["`

    **Pre**: Scanner at `[`.
    **Post**: Emits `flowSequenceStart`, advances past `[`, increments `flowLevel`,
    pushes `true` onto `flowStack` (= sequence), sets `simpleKeyAllowed := true`.

    **Refactored for verification**: Uses explicit variable names (no shadowing)
    to make token tracking clearer for formal proofs. -/
def scanFlowSequenceStart (s : ScannerState) : ScannerState :=
  -- Save the outer simple key so it survives flow nesting.
  -- Example: `[a, b]: value` — the simple key saved before `[` must
  -- still be pending after `]` for `:` to confirm it.
  let savedKey := s.simpleKey
  let s_key_disabled := { s with simpleKey := { possible := false } }
  let s_with_token := s_key_disabled.emit .flowSequenceStart
  let s_after_advance := s_with_token.advance
  { s_after_advance with
      flowLevel := s_after_advance.flowLevel + 1,
      simpleKeyAllowed := true,
      flowStack := s_after_advance.flowStack.push true,
      simpleKeyStack := s_after_advance.simpleKeyStack.push savedKey }

/-- Scan a flow sequence end indicator `]`.

    **Implements** (YAML 1.2.2 §7.4):
    - `[9]  c-sequence-end` = `"]"`

    **Pre**: Scanner at `]` inside a flow collection (`flowLevel > 0`).
    **Post**: Emits `flowSequenceEnd`, advances past `]`, decrements `flowLevel`,
    pops `flowStack`, sets `simpleKeyAllowed := false`.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
def scanFlowSequenceEnd (s : ScannerState) : ScannerState :=
  let s_with_token := s.emit .flowSequenceEnd
  let s_after_advance := s_with_token.advance
  -- Restore the outer simple key saved by the matching flow-open.
  let restored := s_with_token.simpleKeyStack.back?.getD {}
  { s_after_advance with
      flowLevel := if s_after_advance.flowLevel > 0 then s_after_advance.flowLevel - 1 else 0,
      simpleKeyAllowed := false,
      flowStack := s_after_advance.flowStack.pop,
      simpleKey := restored,
      simpleKeyStack := s_after_advance.simpleKeyStack.pop }

/-- Scan a flow mapping start indicator `{`.

    **Implements** (YAML 1.2.2 §7.4):
    - `[138] c-flow-mapping(n,c)` = `"{" s-separate(n,c)? ...`
    - `[10]  c-mapping-start` = `"{"`

    **Pre**: Scanner at `{`.
    **Post**: Emits `flowMappingStart`, advances past `{`, increments `flowLevel`,
    pushes `false` onto `flowStack` (= mapping), sets `simpleKeyAllowed := true`.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
def scanFlowMappingStart (s : ScannerState) : ScannerState :=
  -- Save the outer simple key so it survives flow nesting.
  -- Example: `{a: b}: value` — the simple key saved before `{` must
  -- still be pending after `}` for `:` to confirm it.
  let savedKey := s.simpleKey
  let s_key_disabled := { s with simpleKey := { possible := false } }
  let s_with_token := s_key_disabled.emit .flowMappingStart
  let s_after_advance := s_with_token.advance
  { s_after_advance with
      flowLevel := s_after_advance.flowLevel + 1,
      simpleKeyAllowed := true,
      flowStack := s_after_advance.flowStack.push false,
      simpleKeyStack := s_after_advance.simpleKeyStack.push savedKey }

/-- Scan a flow mapping end indicator `}`.

    **Implements** (YAML 1.2.2 §7.4):
    - `[11] c-mapping-end` = `"}"`

    **Pre**: Scanner at `}` inside a flow collection (`flowLevel > 0`).
    **Post**: Emits `flowMappingEnd`, advances past `}`, decrements `flowLevel`,
    pops `flowStack`, sets `simpleKeyAllowed := false`.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
def scanFlowMappingEnd (s : ScannerState) : ScannerState :=
  let s_with_token := s.emit .flowMappingEnd
  let s_after_advance := s_with_token.advance
  -- Restore the outer simple key saved by the matching flow-open.
  let restored := s_with_token.simpleKeyStack.back?.getD {}
  { s_after_advance with
      flowLevel := if s_after_advance.flowLevel > 0 then s_after_advance.flowLevel - 1 else 0,
      simpleKeyAllowed := false,
      flowStack := s_after_advance.flowStack.pop,
      simpleKey := restored,
      simpleKeyStack := s_after_advance.simpleKeyStack.pop }

/-- Scan a flow entry separator `,`.

    **Implements** (YAML 1.2.2 §7.4):
    - `[7] c-collect-entry` = `","`

    **Pre**: Scanner at `,` inside a flow collection (`flowLevel > 0`).
    **Post**: Emits `flowEntry`, advances past `,`, sets `simpleKeyAllowed := true`.
    **Error**: `invalidFlowEntry` if comma immediately follows a flow-open indicator
    (`[`, `{`) or another comma — catching leading/consecutive commas.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
def scanFlowEntry (s : ScannerState) : Except ScanError ScannerState := do
  -- §7.4: Leading comma (after flow-open) or consecutive commas are invalid.
  if s.tokens.size > 0 then
    let lastTok := s.tokens[s.tokens.size - 1]!.val
    if lastTok == .flowSequenceStart || lastTok == .flowMappingStart ||
       lastTok == .flowEntry then
      throw (.invalidFlowEntry s.line s.col)
  let s_with_token := s.emit .flowEntry
  let s_after_advance := s_with_token.advance
  .ok { s_after_advance with simpleKeyAllowed := true }

/-- Scan a block entry indicator `-`.

    **Implements** (YAML 1.2.2 §8.2.1):
    - `[186] l+block-sequence(n)` = `(s-indent(n+m) c-l-block-seq-entry(n+m))+ for some fixed auto-detected m > 0`
    - `[187] c-l-block-seq-entry(n)` = `"-" s-l+block-indented(n,BLOCK-IN)`
    - `[4]   c-sequence-entry` = `"-"`

    **Pre**: Scanner at `-` followed by blank/EOF, in block context.
    **Post**: Pushes sequence indent if needed, emits `blockEntry`, advances past `-`,
    sets `simpleKeyAllowed := true`.
    **Error**: `tabInIndentation` if tab is found in preceding whitespace (§6.1).

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
def scanBlockEntry (s : ScannerState) : Except ScanError ScannerState := do
  -- §6.1: Tab in indentation before block entry.
  -- Scan backward through whitespace consumed by skipToContent to detect any
  -- tab used as indentation for this block entry — forbidden.
  -- Handles `-\t-`, `- \t-`, `-\t -`, etc.
  if !s.inFlow then
    if s.hasTabInPrecedingWhitespace then
      throw (.tabInIndentation s.line s.col)
  let s_with_indent := if !s.inFlow then pushSequenceIndent s s.col else s
  let s_with_token := s_with_indent.emit .blockEntry
  let s_after_advance := s_with_token.advance
  .ok { s_after_advance with simpleKeyAllowed := true }

/-- Scan an explicit key indicator `?`.

    **Implements** (YAML 1.2.2 §8.2.2):
    - `[188] l+block-mapping(n)` = `(s-indent(n+m) ns-l-block-map-entry(n+m))+ for some fixed auto-detected m > 0`
    - `[189] ns-l-block-map-entry(n)` = `c-l-block-map-explicit-entry(n) | ...`
    - `[190] c-l-block-map-explicit-entry(n)` = `c-l-block-map-explicit-key(n) ...`
    - `[191] c-l-block-map-explicit-key(n)` = `"?" s-l+block-indented(n,BLOCK-OUT)`
    - `[5]   c-mapping-key` = `"?"`

    **Pre**: Scanner at `?` followed by blank/EOF (or flow indicator in flow context).
    **Post**: Pushes mapping indent if needed, emits `key`, advances past `?`,
    sets `simpleKeyAllowed := true`, `explicitKeyLine := some s.line`.
    **Error**: `tabInIndentation` if tab immediately follows `?` in block context (§6.1).

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
def scanKey (s : ScannerState) : Except ScanError ScannerState := do
  let s_with_indent := if !s.inFlow then pushMappingIndent s s.col else s
  let s_with_token := s_with_indent.emit .key
  let s_after_advance := s_with_token.advance
  -- §6.1: Tab immediately after `?` indicator in block context is
  -- indentation for the key content — forbidden.
  if !s_after_advance.inFlow then
    if let some '\t' := s_after_advance.peek? then
      throw (.tabInIndentation s_after_advance.line s_after_advance.col)
  -- Invalidate any pending simple key.  The `?` has already emitted an
  -- explicit `key` token; the next `:` is this key's value indicator,
  -- not confirmation of a new implicit key.
  .ok { s_after_advance with simpleKeyAllowed := true, explicitKeyLine := some s.line,
                              simpleKey := { possible := false } }

/-- Scan a value indicator `:`.

    **Implements** (YAML 1.2.2 §8.2.2, §7.4):
    - `[192] ns-l-block-map-implicit-entry(n)` = `(ns-s-implicit-yaml-key ... | e-node) c-l-block-map-implicit-value(n)`
    - `[193] c-l-block-map-implicit-value(n)` = `":" (s-l+block-node(n,BLOCK-OUT) | ...)`
    - `[6]   c-mapping-value` = `":"`
    - `[152] ns-s-implicit-yaml-key(c)` — implicit keys restricted to single line

    This is the scanner's most complex function.  When a simple key is pending,
    the `:` retroactively confirms it by inserting `key` (and `blockMappingStart`
    in block context) at the saved position.  Multiple validation checks:

    **Variable classification:**
    | Variable    | Kind     | Description |
    |-------------|----------|-------------|
    | `keyCol`    | Position | Column of the pending simple key |
    | `s.col`     | Position | Column of the `:` value indicator |

    **Pre**: Scanner at `:` that qualifies as a value indicator.
    **Post**: Resolves pending simple key if any (retroactive `key`/`blockMappingStart`),
    emits `value`, advances past `:`, sets `simpleKeyAllowed := true`.
    **Error**: `invalidImplicitKey` (multiline implicit key in block §7.4, or flow sequence §7.4.2),
    `trailingContent` (key at same indent as block sequence §8.2.1),
    `invalidFlowEntry` (missing comma in flow mapping, T833 §7.4),
    `tabInIndentation` (tab after explicit `:` at/below indent level §6.1).

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
def scanValue (s : ScannerState) : Except ScanError ScannerState := do
  -- When `saveSimpleKey` saved the position of `:` itself (before dispatch
  -- recognised it as a value indicator) and an explicit `?` key is still
  -- pending, the saved key is spurious — discard it so the explicit-key
  -- path fires below.  Example: `? a\n: b` — the `:` on line 1 is the
  -- value indicator for the explicit key, not a new implicit key.
  let s_key_cleared := if s.explicitKeyLine.isSome && s.simpleKey.possible
              && s.simpleKey.pos.offset == s.offset then
    { s with simpleKey := { possible := false } }
  else s
  -- §7.4: "Plain keys are restricted to a single line."
  -- In block context, reject implicit keys where the key token and the `:`
  -- value indicator are on different lines.
  if s_key_cleared.simpleKey.possible && !s_key_cleared.inFlow && s_key_cleared.simpleKey.pos.line != s_key_cleared.line then
    throw (.invalidImplicitKey s_key_cleared.line)
  -- §7.4.2: In flow sequences, implicit key entries (without `?`) must
  -- have the key and `:` on the same line.  Flow mappings allow multi-line
  -- implicit keys per `ns-flow-map-yaml-key-entry(n,c)` with `s-separate`.
  if s_key_cleared.simpleKey.possible && s_key_cleared.isInFlowSequence && s_key_cleared.explicitKeyLine.isNone
      && s_key_cleared.simpleKey.endLine != s_key_cleared.line then
    throw (.invalidImplicitKey s_key_cleared.line)
  -- §8.2.1: A mapping key at the same indent as a block sequence is
  -- invalid.  Reject before building new state.
  if s_key_cleared.simpleKey.possible && !s_key_cleared.inFlow then
    let keyCol : Int := s_key_cleared.simpleKey.pos.col
    if keyCol <= s_key_cleared.currentIndent then
      if let some top := s_key_cleared.indents.back? then
        if top.isSequence && keyCol == top.column then
          throw (.trailingContent s_key_cleared.simpleKey.pos.line s_key_cleared.simpleKey.pos.col)
  -- T833: Missing comma in flow mapping.  When the simple key position is
  -- immediately after a `value` token (no intervening `flowEntry` comma),
  -- AND the current `:` is on a different line from that `value` token,
  -- the new key was created by plain-scalar folding across a newline into
  -- a value position — e.g., `{ foo: 1\n bar: 2 }` folds `1 bar` as a key.
  -- Reject because flow mapping entries require comma separation.
  -- Same-line cases like `{x: :x}` or `{"key"::value}` are valid (§7.4).
  if s_key_cleared.simpleKey.possible && s_key_cleared.inFlow && s_key_cleared.simpleKey.tokenIndex > 0 then
    if let some prevTok := s_key_cleared.tokens[s_key_cleared.simpleKey.tokenIndex - 1]? then
      if prevTok.val == .value && prevTok.pos.line != s_key_cleared.line then
        throw (.invalidFlowEntry s_key_cleared.line s_key_cleared.col)
  let s_prepared := if s_key_cleared.simpleKey.possible then
    let s_with_key := s_key_cleared.insertAt s_key_cleared.simpleKey.tokenIndex s_key_cleared.simpleKey.pos .key
    if !s_key_cleared.inFlow then
      let keyCol : Int := s_key_cleared.simpleKey.pos.col
      if keyCol > s_with_key.currentIndent then
        let s_with_mapping := s_with_key.insertAt s_key_cleared.simpleKey.tokenIndex s_key_cleared.simpleKey.pos .blockMappingStart
        { s_with_mapping with
          indents := s_with_mapping.indents.push { column := keyCol, isSequence := false }
          simpleKey := { possible := false } }
      else
        { s_with_key with simpleKey := { possible := false } }
    else
      { s_with_key with simpleKey := { possible := false } }
  else if s_key_cleared.explicitKeyLine.isSome then
    -- Explicit `?` already emitted `blockMappingStart + key`.
    -- Just emit `value` — no new mapping indent needed.
    -- Also discard any stale simpleKey (saved by saveSimpleKey before
    -- dispatch recognised `:` as a value indicator).
    { s_key_cleared with simpleKey := { possible := false } }
  else
    if !s_key_cleared.inFlow then pushMappingIndent s_key_cleared s_key_cleared.col else s_key_cleared
  let s_with_token := s_prepared.emit .value
  let s_after_advance := s_with_token.advance
  -- §6.1: Tab immediately after explicit `:` value indicator (at or below
  -- block indent level) — the tab functions as indentation for the value
  -- content, which is forbidden.  When `:` is past the indent level (inline
  -- implicit value, e.g., `key:\tval`), the tab is valid `s-separate-in-line`.
  if (s.col : Int) ≤ s.currentIndent && !s_after_advance.inFlow then
    if let some '\t' := s_after_advance.peek? then
      throw (.tabInIndentation s_after_advance.line s_after_advance.col)
  .ok { s_after_advance with simpleKeyAllowed := true, explicitKeyLine := none }

/-! ## Anchor and Alias Scanning -/

/-- Scan an anchor (`&name`) or alias (`*name`) indicator.

    **Implements** (YAML 1.2.2 §6.9):
    - `[101] c-ns-anchor-property` = `"&" ns-anchor-name`
    - `[104] c-ns-alias-node`      = `"*" ns-anchor-name`
    - `[102] ns-anchor-char`       = `ns-char - c-flow-indicator`
    - `[103] ns-anchor-name`       = `ns-anchor-char+`
    - `[13]  c-anchor` = `"&"` / `[14] c-alias` = `"*"`

    **Pre**: Scanner at `&` (anchor) or `*` (alias).
    **Post**: Advances past indicator + name characters, emits `.anchor name`
    or `.alias name`. Sets `simpleKeyAllowed := false`. -/
-- Helper: Collect anchor/alias name characters using structural recursion.
private def collectAnchorNameLoop (s : ScannerState) (name : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (name, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isFlowIndicator c && !isWhiteSpace c && !isLineBreak c then
        collectAnchorNameLoop s.advance (name.push c) fuel'
      else
        (name, s)
    | none => (name, s)

def scanAnchorOrAlias (s : ScannerState) (isAnchor : Bool) : ScannerState :=
  let startPos := s.currentPos
  let s_after_marker := s.advance
  let fuel := s.inputEnd - s_after_marker.offset
  let (name, s_after_name) := collectAnchorNameLoop s_after_marker "" fuel
  let token := if isAnchor then YamlToken.anchor name else YamlToken.alias name
  let s_with_token := s_after_name.emitAt startPos token
  { s_with_token with simpleKeyAllowed := false }

/-! ## Tag Scanning -/

-- Helper: Collect verbatim tag URI until '>'.
private def collectVerbatimTagLoop (s : ScannerState) (uri : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (uri, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '>' => (uri, s.advance)
    | some c => collectVerbatimTagLoop s.advance (uri.push c) fuel'
    | none => (uri, s)

-- Helper: Collect tag suffix characters (non-whitespace, non-flow).
private def collectTagSuffixLoop (s : ScannerState) (suffix : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (suffix, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isWhiteSpace c && !isLineBreak c && !isFlowIndicator c then
        collectTagSuffixLoop s.advance (suffix.push c) fuel'
      else
        (suffix, s)
    | none => (suffix, s)

-- Helper: Collect tag handle characters until '!' or invalid char.
-- Returns (chars_before_bang, found_second_bang, state).
private def collectTagHandleLoop (s : ScannerState) (chars : String) (fuel : Nat) : String × Bool × ScannerState :=
  match fuel with
  | 0 => (chars, false, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '!' => (chars, true, s.advance)
    | some c =>
      if !isWhiteSpace c && !isLineBreak c && !isFlowIndicator c then
        collectTagHandleLoop s.advance (chars.push c) fuel'
      else
        (chars, false, s)
    | none => (chars, false, s)

/-- Scan a tag property (`!`, `!!suffix`, `!handle!suffix`, `!<uri>`).

    **Implements** (YAML 1.2.2 §6.8.2):
    - `[96]  c-ns-tag-property` = `c-verbatim-tag | c-ns-shorthand-tag | c-non-specific-tag`
    - `[97]  c-verbatim-tag`    = `"!<" ns-uri-char+ ">"`
    - `[98]  c-ns-shorthand-tag` = `c-tag-handle ns-tag-char+`
    - `[99]  c-non-specific-tag` = `"!"`
    - `[15]  c-tag` = `"!"`

    Handles three tag forms:
    1. **Verbatim**: `!<uri>` → `(.tag "" "uri")`
    2. **Secondary**: `!!suffix` → `(.tag "!!" "suffix")`
    3. **Named/primary**: `!handle!suffix` or `!suffix` → `(.tag handle suffix)`

    **Pre**: Scanner at `!`.
    **Post**: Advances past tag, emits `.tag handle suffix`.
    Sets `simpleKeyAllowed := false`. -/
def scanTag (s : ScannerState) : ScannerState :=
  let startPos := s.currentPos
  let s_after_bang := s.advance  -- consume `!`
  match s_after_bang.peek? with
  | some '<' =>
    -- Verbatim tag: !<uri>
    let s_after_open := s_after_bang.advance
    let fuel := s.inputEnd - s_after_open.offset
    let (uri, s_after_uri) := collectVerbatimTagLoop s_after_open "" fuel
    let s_with_token := s_after_uri.emitAt startPos (.tag "" uri)
    { s_with_token with simpleKeyAllowed := false }
  | some '!' =>
    -- Secondary tag: !!suffix
    let s_after_second_bang := s_after_bang.advance
    let fuel := s.inputEnd - s_after_second_bang.offset
    let (suffix, s_after_suffix) := collectTagSuffixLoop s_after_second_bang "" fuel
    let s_with_token := s_after_suffix.emitAt startPos (.tag "!!" suffix)
    { s_with_token with simpleKeyAllowed := false }
  | _ =>
    -- Named/primary tag: !handle!suffix or !suffix
    let fuel := s.inputEnd - s_after_bang.offset
    let (chars, foundBang, s_after_handle) := collectTagHandleLoop s_after_bang "" fuel
    let (handle, suffix_or_chars) :=
      if foundBang then
        ("!" ++ chars ++ "!", "")
      else
        ("!", chars)
    let (suffix, s_after_suffix) :=
      if foundBang then
        let fuel' := s.inputEnd - s_after_handle.offset
        collectTagSuffixLoop s_after_handle "" fuel'
      else
        (suffix_or_chars, s_after_handle)
    let s_with_token := s_after_suffix.emitAt startPos (.tag handle suffix)
    { s_with_token with simpleKeyAllowed := false }

/-! ## Directive Scanning -/

-- Helper: Collect directive name (non-whitespace, non-linebreak characters).
private def collectDirectiveNameLoop (s : ScannerState) (name : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (name, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isWhiteSpace c && !isLineBreak c then
        collectDirectiveNameLoop s.advance (name.push c) fuel'
      else
        (name, s)
    | none => (name, s)

-- Helper: Collect version major digits until '.'.
private def collectVersionMajorLoop (s : ScannerState) (major : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (major, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '.' => (major, s.advance)
    | some c =>
      if c.isDigit then
        collectVersionMajorLoop s.advance (major.push c) fuel'
      else
        (major, s)
    | none => (major, s)

-- Helper: Collect version minor digits.
private def collectVersionMinorLoop (s : ScannerState) (minor : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (minor, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if c.isDigit then
        collectVersionMinorLoop s.advance (minor.push c) fuel'
      else
        (minor, s)
    | none => (minor, s)

-- Helper: Collect TAG directive handle (non-whitespace characters).
private def collectTagHandleDirectiveLoop (s : ScannerState) (handle : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (handle, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isWhiteSpace c then
        collectTagHandleDirectiveLoop s.advance (handle.push c) fuel'
      else
        (handle, s)
    | none => (handle, s)

-- Helper: Collect TAG directive prefix (non-whitespace, non-linebreak characters).
private def collectTagPrefixLoop (s : ScannerState) (pfx : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (pfx, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isWhiteSpace c && !isLineBreak c then
        collectTagPrefixLoop s.advance (pfx.push c) fuel'
      else
        (pfx, s)
    | none => (pfx, s)

/-- Scan a directive (`%YAML` or `%TAG`).

    **Implements** (YAML 1.2.2 §6.8):
    - `[82]  l-directive` = `"%" ( ns-yaml-directive | ns-tag-directive | ns-reserved-directive ) s-l-comments`
    - `[86]  ns-yaml-directive` = `"YAML" s-separate-in-line ns-yaml-version`
    - `[89]  ns-tag-directive`  = `"TAG" s-separate-in-line c-tag-handle s-separate-in-line ns-tag-prefix`
    - `[88]  ns-yaml-version`  = `ns-dec-digit+ "." ns-dec-digit+`
    - `[20]  c-directive` = `"%"`

    **Pre**: Scanner at `%` at column 0, `allowDirectives` is true.
    **Post**: Emits `.versionDirective major minor` or `.tagDirective handle prefix`.
    Sets `seenYamlDirective`, `directivesPresent` as appropriate.
    **Error**: `directiveAfterContent` (directive after document content without `...`),
    `duplicateYamlDirective` (second `%YAML` in same document),
    `directiveTrailingContent` (content after version string). -/
def scanDirective (s : ScannerState) : Except ScanError ScannerState := do
  -- §6.8: Directives are only allowed before a document (at stream start
  -- or after `...`). Reject directives after document content.
  if !s.allowDirectives then
    throw (.directiveAfterContent s.line)
  let startPos := s.currentPos
  let s_after_percent := s.advance  -- consume `%`
  let fuel := s.inputEnd - s_after_percent.offset
  let (name, s_after_name) := collectDirectiveNameLoop s_after_percent "" fuel
  let s_after_ws := skipWhitespace s_after_name
  if name == "YAML" then
    -- §6.8.1: At most one %YAML directive per document.
    if s.seenYamlDirective then
      throw (.duplicateYamlDirective s.line)
    let fuel_major := s.inputEnd - s_after_ws.offset
    let (major, s_after_dot) := collectVersionMajorLoop s_after_ws "" fuel_major
    let fuel_minor := s.inputEnd - s_after_dot.offset
    let (minor, s_after_version) := collectVersionMinorLoop s_after_dot "" fuel_minor
    -- §6.8.1: After version, only s-separate-in-line + comment, or linebreak/EOF.
    -- c-nb-comment-text (#) requires preceding s-separate-in-line (≥1 s-white).
    let colBeforeWs := s_after_version.col
    let s_validated := skipWhitespace s_after_version
    match s_validated.peek? with
    | some '#' =>
      -- Verify whitespace was consumed (s-separate-in-line before #)
      if s_validated.col == colBeforeWs then
        throw (.directiveTrailingContent s_validated.line s_validated.col)
    | some c => if !isLineBreak c then throw (.directiveTrailingContent s_validated.line s_validated.col)
    | none => pure ()       -- EOF: ok (orphan directive caught later)
    let s_with_token := s_validated.emitAt startPos (.versionDirective major.toNat! minor.toNat!)
    .ok { s_with_token with seenYamlDirective := true, directivesPresent := true }
  else if name == "TAG" then
    let fuel_handle := s.inputEnd - s_after_ws.offset
    let result := collectTagHandleDirectiveLoop s_after_ws "" fuel_handle
    let handle := result.1
    let s_after_handle := result.2
    let s_after_ws2 := skipWhitespace s_after_handle
    let fuel_prefix := s.inputEnd - s_after_ws2.offset
    let result2 := collectTagPrefixLoop s_after_ws2 "" fuel_prefix
    let tagPrefix := result2.1
    let s_after_prefix := result2.2
    let s_with_token := s_after_prefix.emitAt startPos (.tagDirective handle tagPrefix)
    .ok { s_with_token with directivesPresent := true }
  else
    .ok (skipToEndOfLine s_after_ws)

/-! ## Document Marker Scanning -/

/-- Scan a document-start marker `---`.

    **Implements** (YAML 1.2.2 §9.1.2):
    - `[202] c-directives-end` = `"---"`

    **Pre**: Scanner at `---` at column 0.
    **Post**: Unwinds all indents (emits `blockEnd` tokens), emits `documentStart`,
    advances past `---`. Resets `allowDirectives := false`, `simpleKeyAllowed := true`,
    `documentEverStarted := true`. -/
def scanDocumentStart (s : ScannerState) : ScannerState :=
  let s_unwound := unwindIndents s (-1)
  let s_key_disabled := { s_unwound with simpleKey := { possible := false } }
  let s_with_token := s_key_disabled.emit .documentStart
  let s_advanced := s_with_token.advanceN 3
  { s_advanced with
    simpleKeyAllowed := true
    allowDirectives := false
    seenYamlDirective := false
    directivesPresent := false
    documentEverStarted := true }

/-- Scan a document-end marker `...`.

    **Implements** (YAML 1.2.2 §9.1.2):
    - `[203] c-document-end` = `"..."`
    - `[204] l-document-suffix` = `c-document-end s-l-comments`

    **Pre**: Scanner at `...` at column 0.
    **Post**: Unwinds all indents, emits `documentEnd`, advances past `...`.
    Sets `allowDirectives := true` (re-enables directives for next document).
    **Error**: `directiveWithoutDocument` (if directives were present but no `---` followed),
    `trailingContentAfterDocEnd` (non-comment content on same line after `...`). -/
def scanDocumentEnd (s : ScannerState) : Except ScanError ScannerState := do
  -- §9.1.2: Document end marker `...` requires an open document.
  -- If directives were present but no `---` followed, the `...` cannot
  -- close a document that was never opened.
  if s.directivesPresent && !s.documentEverStarted then
    throw (.directiveWithoutDocument s.line)
  let s_unwound := unwindIndents s (-1)
  let s_key_disabled := { s_unwound with simpleKey := { possible := false } }
  let s_with_token := s_key_disabled.emit .documentEnd
  let s_advanced := s_with_token.advanceN 3
  let result := { s_advanced with
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

/-- Parse `n` hexadecimal digits and convert to a character.

    **Implements** (YAML 1.2.2 §5.7):
    - `[58] ns-esc-8-bit`  when `n = 2` (→ `\xHH`)
    - `[59] ns-esc-16-bit` when `n = 4` (→ `\uHHHH`)
    - `[60] ns-esc-32-bit` when `n = 8` (→ `\UHHHHHHHH`)

    **Pre**: Scanner positioned after `\x`, `\u`, or `\U`.
    **Post**: Advances past `n` hex digits, returns the decoded character.
    **Error**: `invalidHexEscape` (fewer than `n` hex digits available),
    `unicodeOutOfRange` (value ≥ U+110000). -/
def parseHexEscape (s : ScannerState) (n : Nat) : Except ScanError (Char × ScannerState) := do
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

/-- Process a single escape sequence after `\`.

    **Implements** (YAML 1.2.2 §5.7):
    - `[61] c-ns-esc-char` = `"\\" ( ns-esc-null | ... | ns-esc-32-bit )`
    - `[41] c-escape` = `"\\"`
    - `[42]`–`[60]` individual escape characters

    Supports all 20 named escapes (`\0`, `\a`, `\b`, `\t`, `\n`, `\v`, `\f`,
    `\r`, `\e`, `\ `, `\"`, `\/`, `\\`, `\N`, `\_`, `\L`, `\P`)
    plus the three hex escapes (`\x`, `\u`, `\U`).

    **Pre**: Scanner positioned at the character AFTER `\`.
    **Post**: Returns the decoded character and scanner advanced past the escape.
    **Error**: `unterminatedEscape` (EOF after `\`), `unknownEscape` (unrecognized escape character). -/
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
def trimTrailingWS (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse)

/-- Fold a newline in a quoted scalar (double or single) per YAML flow folding.

    **Implements** (YAML 1.2.2 §6.5):
    - `[73]  b-l-folded(n,c)` = `b-l-trimmed(n,c) | b-as-space`
    - `[74]  s-flow-folded(n)` = `s-separate-in-line? b-l-folded(n,FLOW-IN) s-flow-line-prefix(n)`
    - `[69]  b-l-trimmed(n,c)` = `b-non-content l-empty(n,c)+`
    - `[70]  b-as-space` = `b-break`

    A single newline becomes a space; consecutive empty lines produce `\n` each
    (the first is the `b-non-content` silent break).

    **Pre**: Scanner at a line break character inside a quoted scalar.
    **Post**: Consumes newline + blank lines + leading spaces on continuation line.
    Returns the folded replacement string (`" "` or `"\n"*`).
    **Error**: `tabInIndentation` if tab found in indentation zone of continuation line (§6.1). -/
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

/-- Scan a double-quoted scalar.

    **Implements** (YAML 1.2.2 §7.3.1):
    - `[107] c-double-quoted(n,c)` = `'"' nb-double-text(n,c) '"'`
    - `[108] nb-double-text(n,c)` = content chars, escape sequences `[61]`, flow folding `[73]`
    - `[110] nb-double-one-line` / `[111] s-double-escaped(n)` / `[112] s-double-break(n)`
    - `[19]  c-double-quote` = `'"'`

    Processes escape sequences via `processEscape`, line folding via `foldQuotedNewlines`.

    **Pre**: Scanner at opening `"`.
    **Post**: Advances past closing `"`, emits `.scalar content .doubleQuoted`.
    Sets `simpleKeyAllowed := false`.
    **Error**: `unterminatedScalar` (EOF/fuel before closing `"`),
    `documentMarkerInScalar` (document marker at col 0 inside scalar §9.1.2),
    `underIndentedScalar` (continuation line below current block indent §8.1),
    `trailingContent` (non-whitespace/comment/`:` after closing `"` in block context §7.3.2). -/
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

/-- Scan a single-quoted scalar.

    **Implements** (YAML 1.2.2 §7.3.2):
    - `[113] c-single-quoted(n,c)` = `"'" nb-single-text(n,c) "'"`
    - `[114] nb-single-text(n,c)` = content chars, `''` escape, flow folding `[73]`
    - `[118] c-quoted-quote` = `"''"` (escaped single quote)
    - `[18]  c-single-quote` = `"'"`

    The only escape is `''` → `'`.  Line folding is handled by `foldQuotedNewlines`.

    **Pre**: Scanner at opening `'`.
    **Post**: Advances past closing `'`, emits `.scalar content .singleQuoted`.
    Sets `simpleKeyAllowed := false`.
    **Error**: `unterminatedScalar`, `documentMarkerInScalar`, `underIndentedScalar`,
    `trailingContent` (same conditions as `scanDoubleQuoted`). -/
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

/-- Check if character `c` can follow `#` to prevent valid `ns-plain-safe`
    characters from being confused with plain scalars.  Used in `scanPlainScalar`.

    **Implements** (YAML 1.2.2 §7.3.3):
    - `[126] ns-plain-safe(c)` — excludes flow indicators in flow context -/
def isPlainSafe (c : Char) (inFlow : Bool) : Bool :=
  if inFlow then
    !isWhiteSpace c && !isLineBreak c && !isFlowIndicator c
  else
    !isWhiteSpace c && !isLineBreak c

/-- Scan a plain (unquoted) scalar.

    **Implements** (YAML 1.2.2 §7.3.3):
    - `[131] ns-plain(n,c)` = plain scalar content across potentially multiple lines
    - `[123] ns-plain-first(c)` — first character restrictions (via `canStartPlainScalar`)
    - `[126] ns-plain-safe(c)` — safe continuation characters (via `isPlainSafe`)
    - `[129] ns-plain-char(c)` — `:` and `#` context-sensitive handling
    - `[133] ns-plain-multi-line(c)` — continuation lines must be indented past block level

    Terminators: ` #` (comment), `: ` (value indicator), flow indicators (in flow),
    document boundaries (`---`/`...` at col 0), under-indented continuation.

    **Variable classification:**
    | Variable         | Kind     | Description |
    |------------------|----------|-------------|
    | `contentIndent`  | Position | Floor column for continuation lines |
    | `startPos`       | Pos      | Position for token attribution |

    **Pre**: Scanner at a character satisfying `canStartPlainScalar`.
    **Post**: Advances past all plain scalar content (including folded continuations),
    emits `.scalar content .plain`. Sets `simpleKeyAllowed := false`.
    **Error**: None directly (terminates by breaking). -/
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
inductive FoldState where
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
def foldBlockContent (raw : String) : String :=
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
  -- CONTRACT: parentIndent is the current block's indent level
  have h_parentIndent : parentIndent = s.currentIndent := rfl
  -- minContentIndent (Position) = n+1: spec §8.1.3 requires m ≥ 1
  let minContentIndent : Nat := (max 0 (parentIndent + 1)).toNat
  -- CONTRACT: minContentIndent ≥ 0 (trivially, as Nat)
  -- CONTRACT: minContentIndent is the floor for content indent
  have h_minFloor : (0 : Int) ≤ max 0 (parentIndent + 1) := by omega
  let (contentIndent, autoDetectErr?) := match explicitOffset with
    | some m =>
      -- Explicit: contentIndent (Position) = parentIndent (Position) + m (Distance)
      ((max 0 (parentIndent + (m : Int))).toNat, (none : Option ScanError))
    | none =>
      -- Auto-detect: scan ahead past blank lines to find first content line.
      -- The detected column must respect the floor (minContentIndent).
      -- Uses skipSpaces (not skipWhitespace) because s-indent uses spaces only [63].
      -- §8.1.3: "the content indentation level is equal to the number of
      -- leading spaces on the first non-empty line of the content."
      -- Whitespace-only lines (spaces + newline) are skipped; their max column
      -- is tracked to validate against the detected indent.
      Id.run do
        let mut probe := s'
        let mut maxWSCol : Nat := 0
        let mut maxWSLine : Nat := 0
        let fuel := s.inputEnd - probe.offset + 1
        for _ in [:fuel] do
          probe := skipSpaces probe
          match probe.peek? with
          | some c =>
            -- §6.1: Tab at col < minContentIndent is in the indentation zone
            -- where s-indent requires spaces only. Reject immediately.
            if c == '\t' && probe.col < minContentIndent then
              return (0, some (.tabInIndentation probe.line probe.col))
            if isLineBreak c then
              -- Whitespace-only line: track max column but skip for indent detection.
              if probe.col > maxWSCol then
                maxWSCol := probe.col
                maxWSLine := probe.line
              probe := consumeNewline probe
            else
              -- First non-empty line: set contentIndent.
              let detectedIndent := max minContentIndent probe.col
              -- Validate: preceding whitespace-only lines must not exceed
              -- the detected content indent.  Per §8.1.3, l-empty(n) lines
              -- have at most n spaces; lines with more can't be l-empty and
              -- have no nb-char content, so they're grammatically invalid.
              if maxWSCol > detectedIndent then
                return (0, some (.blockScalarIndentMismatch maxWSLine maxWSCol))
              return (detectedIndent, none)
          | none => break
        -- No content found.  Use the maximum whitespace-only column as
        -- the content indent (these lines are l-keep-empty/l-strip-empty
        -- and legitimately establish the indent for trailing whitespace).
        if maxWSCol > minContentIndent then
          return (maxWSCol, none)
        return (minContentIndent, none)
  if let some err := autoDetectErr? then
    throw err
  -- CONTRACT: contentIndent ≥ minContentIndent (§8.1.3: m ≥ 1).
  -- In the explicit case: parentIndent + m ≥ parentIndent + 1 since m ≥ 1.
  -- In the auto-detect case: detectedIndent = max minContentIndent probe.col ≥ minContentIndent.
  -- This invariant is checked at runtime via the auto-detect logic and
  -- the explicit case's arithmetic. See Proofs/ScannerContracts.lean for
  -- the formal statement and #guard verification.
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

/-- Record the current position as a potential implicit key.

    **Implements**: Part of YAML 1.2.2 §7.4 (implicit key tracking).
    - `[152] ns-s-implicit-yaml-key(c)` — the key is only confirmed later by `:`.

    If `simpleKeyAllowed` is true, saves the current token index and position.
    This saved key is resolved retroactively when `scanValue` encounters `:`.

    **Pre**: Called after `skipToContent` and indent check, before character dispatch.
    **Post**: Updates `simpleKey` if allowed, otherwise no-op. -/
def saveSimpleKey (st : ScannerState) : ScannerState :=
  -- §7.4: Do not record a new implicit key on the same line as an
  -- explicit `?` indicator.  Content on the `?` line is the explicit
  -- key's node, not a new implicit key (Root Cause A/B fix).
  -- On subsequent lines, saving is allowed — the content may start a
  -- new entry (e.g., `? a\n c:` where `c` is a new implicit key).
  if st.explicitKeyLine == some st.line then st
  else if st.simpleKeyAllowed && !st.inFlow then
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

end Lean4Yaml.Scanner
