/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Token
import Lean4Yaml.CharPredicates

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
open Lean4Yaml.CharPredicates

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

/-- Helper for peekAt? using structural recursion on `n`.

    **Termination**: Structurally recursive on `n`. -/
def ScannerState.peekAt?Loop (input : String) (inputEnd : Nat) (pos : String.Pos.Raw) (n : Nat) : Option Char :=
  match n with
  | 0 =>
    if pos.byteIdx < inputEnd then
      some (String.Pos.Raw.get input pos)
    else
      none
  | n' + 1 =>
    if pos.byteIdx < inputEnd then
      ScannerState.peekAt?Loop input inputEnd (String.Pos.Raw.next input pos) n'
    else
      none

/-- Peek at the character `n` positions ahead without consuming. -/
def ScannerState.peekAt? (s : ScannerState) (n : Nat) : Option Char :=
  ScannerState.peekAt?Loop s.input s.inputEnd ⟨s.offset⟩ n

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

/-- Helper for advanceN using structural recursion on `n`.

    **Termination**: Structurally recursive on `n`. -/
def ScannerState.advanceNLoop (s : ScannerState) (n : Nat) : ScannerState :=
  match n with
  | 0 => s
  | n' + 1 => ScannerState.advanceNLoop s.advance n'

/-- Advance past `n` characters. -/
def ScannerState.advanceN (s : ScannerState) (n : Nat) : ScannerState :=
  ScannerState.advanceNLoop s n

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

/-! ## Character Classification

    Character predicates are imported from `CharPredicates.lean` via
    `open Lean4Yaml.CharPredicates`. The `*Bool` names are used throughout:
    `isLineBreakBool`, `isWhiteSpaceBool`, `isBlankBool`,
    `isFlowIndicatorBool`, `isIndicatorBool`.
-/

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
def ScannerState.hasTabInPrecedingWhitespaceLoop (input : String) (pos : Nat) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if pos == 0 then false
    else
      let prevPos := (String.Pos.Raw.prev input ⟨pos⟩).byteIdx
      let c := String.Pos.Raw.get input ⟨prevPos⟩
      if c == '\t' then true
      else if c == ' ' then ScannerState.hasTabInPrecedingWhitespaceLoop input prevPos fuel'
      else false  -- non-whitespace character: stop scanning

def ScannerState.hasTabInPrecedingWhitespace (s : ScannerState) : Bool :=
  ScannerState.hasTabInPrecedingWhitespaceLoop s.input s.offset s.offset

/-- Helper for skipWhitespace using structural recursion.

    **Termination**: Structurally recursive on `fuel`. -/
def skipWhitespaceLoop (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some c => if isWhiteSpaceBool c then skipWhitespaceLoop s.advance fuel' else s
    | none => s
termination_by fuel

/-- Skip zero or more `s-white` characters (spaces + tabs).
    Implements `s-white*` — use for `s-separate-in-line` ([66]) contexts.
    **Not** for indentation. See `skipSpaces` for `s-indent`. -/
def skipWhitespace (s : ScannerState) : ScannerState :=
  skipWhitespaceLoop s (s.inputEnd - s.offset)

/-- Helper for skipSpaces using structural recursion.

    **Termination**: Structurally recursive on `fuel`. -/
def skipSpacesLoop (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some ' ' => skipSpacesLoop s.advance fuel'
    | _ => s
termination_by fuel

/-- Skip zero or more `s-space` characters (spaces only, no tabs).
    Implements `s-space*` — use for `s-indent(n)` ([63]) contexts.
    YAML §6.1: "tab characters must not be used in indentation". -/
def skipSpaces (s : ScannerState) : ScannerState :=
  skipSpacesLoop s (s.inputEnd - s.offset)

/-- Helper for skipToEndOfLine using structural recursion.

    **Termination**: Structurally recursive on `fuel`. -/
def skipToEndOfLineLoop (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some c => if isLineBreakBool c then s else skipToEndOfLineLoop s.advance fuel'
    | none => s
termination_by fuel

/-- Skip to the end of the current line (stop before line break). -/
def skipToEndOfLine (s : ScannerState) : ScannerState :=
  skipToEndOfLineLoop s (s.inputEnd - s.offset)

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

/-- Phase 1: Skip indentation and whitespace, returning the updated state.

    Returns `.ok s'` with the whitespace-consumed state, or `.error` on
    tab-as-indentation violations.

    Refactored from `do`+`mut` to explicit state threading so that `unfold`
    exposes proof-tractable structure (no monadic join points). -/
def skipToContentWs (s : ScannerState) : Except ScanError ScannerState :=
  -- After a newline, use skipSpaces for indentation (s-indent [63]: spaces only).
  -- Then check for tab-as-indentation, using currentIndent to determine the
  -- boundary between indentation territory and separation territory.
  if s.needIndentCheck then
    let s1 := skipSpaces s
    -- Key insight: once col > currentIndent, we've consumed enough spaces
    -- to be inside the current block's content area. Any tabs here are
    -- s-separate-in-line [66] (legal separation), not indentation.
    if (s1.col : Int) ≤ s1.currentIndent then
      -- Still at or below the current block's indent level.
      -- A tab here would extend into indentation territory — §6.1 violation.
      match s1.peek? with
      | some '\t' =>
        -- Peek past tabs/spaces to see what follows
        let probe := skipWhitespace s1
        match probe.peek? with
        | some '#' => .ok (skipWhitespace s1)      -- tab before comment: allowed
        | some c =>
          if isLineBreakBool c then .ok (skipWhitespace s1)  -- tab on blank line: allowed
          else
            -- Tab followed by content: tab used as indentation — forbidden §6.1
            .error (.tabInIndentation s1.line s1.col)
        | none => .ok (skipWhitespace s1)           -- tab before EOF: allowed
      | _ => .ok s1
    else
      -- Past indentation boundary or in flow context: tabs are legal separation
      .ok (skipWhitespace s1)
  else
    .ok (skipWhitespace s)

/-- Phase 2: Skip optional comment (from `#` to end of line).

    §6.7: `c-nb-comment-text` (#) requires preceding `s-separate-in-line`.
    `s-separate-in-line` = `s-white+` | `start-of-line`.
    Check raw input: `#` must be preceded by whitespace or be at column 0. -/
def skipToContentComment (s : ScannerState) : ScannerState :=
  match s.peek? with
  | some '#' =>
    let commentOk := s.col == 0 || match s.peekBack? with
      | some c => isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF'  -- BOM is transparent (§5.2)
      | none => true   -- start of input
    if commentOk then skipToEndOfLine s else s
  | _ => s

/-- Structural-recursive loop for `skipToContent`.

    Each iteration: (1) skip whitespace/indentation via `skipToContentWs`,
    (2) skip optional comment via `skipToContentComment`,
    (3) if line break: consume it and recurse; otherwise stop.

    **Proof-friendly design**: no `do`-notation, no `mut`, no monadic bind.
    Every intermediate state is an explicit `let`-binding, making `unfold`
    expose simple `match`/`if` trees that `split` can decompose. -/
def skipToContentLoop (s : ScannerState) (fuel : Nat) : Except ScanError ScannerState :=
  match fuel with
  | 0 => .ok s
  | fuel' + 1 =>
    match skipToContentWs s with
    | .error e => .error e
    | .ok s1 =>
      let s2 := skipToContentComment s1
      match s2.peek? with
      | some c =>
        if isLineBreakBool c then
          let s3 := consumeNewline s2
          -- §7.4.2: In flow sequences, implicit keys are restricted to a
          -- single line.  Don't re-enable simple keys on newline so that
          -- `saveSimpleKey` preserves (rather than overwrites) the pending
          -- key, allowing `scanValue` to detect the line mismatch.
          if !s3.isInFlowSequence then
            skipToContentLoop { s3 with simpleKeyAllowed := true } fuel'
          else
            skipToContentLoop s3 fuel'
        else .ok s2
      | none => .ok s2
termination_by fuel

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
def skipToContent (s : ScannerState) : Except ScanError ScannerState :=
  skipToContentLoop s (s.inputEnd - s.offset + 1)

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
     | some c => isBlankBool c

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
     | some c => isBlankBool c

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

/-- Find the last non-placeholder token value, skipping reservation slots.
    Returns `none` if there are no real tokens. -/
def lastRealTokenVal? (tokens : Array (Positioned YamlToken)) : Option YamlToken :=
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
def scanFlowEntry (s : ScannerState) : Except ScanError ScannerState := do
  -- §7.4: Leading comma (after flow-open) or consecutive commas are invalid.
  if let some lastTok := lastRealTokenVal? s.tokens then
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

/-! ### scanValue — value indicator `:` (§8.2.2, §7.4)

Scan a value indicator `:`.

**Implements** (YAML 1.2.2 §8.2.2, §7.4):
- `[192] ns-l-block-map-implicit-entry(n)`
- `[193] c-l-block-map-implicit-value(n)` = `":" ...`
- `[6]   c-mapping-value` = `":"`

**Refactored for verification**: Decomposed into four helper functions
(`scanValueClearKey`, `scanValueValidate`, `scanValuePrepare`,
`scanValueTabCheck`) so that each piece has a simple provable property
and the composed proof chains them with `omega`.
-/

/-- Clear a spurious simple-key when an explicit `?` key is pending and the
    saved position equals the current offset.  Example: `? a\n: b`.
    Pure state transformation — never modifies the token array. -/
def scanValueClearKey (s : ScannerState) : ScannerState :=
  if s.explicitKeyLine.isSome && s.simpleKey.possible
      && s.simpleKey.pos.offset == s.offset then
    { s with simpleKey := { possible := false } }
  else s

/-- Validate pre-conditions for `:` as a value indicator.
    Returns `Unit` on success, throws on violation.
    Does **not** modify the scanner state — only inspects it. -/
def scanValueValidate (s : ScannerState) : Except ScanError Unit := do
  -- §7.4: block-context multiline implicit key
  if s.simpleKey.possible && !s.inFlow && s.simpleKey.pos.line != s.line then
    throw (.invalidImplicitKey s.line)
  -- §7.4.2: flow-sequence multiline implicit key
  if s.simpleKey.possible && s.isInFlowSequence && s.explicitKeyLine.isNone
      && s.simpleKey.endLine != s.line then
    throw (.invalidImplicitKey s.line)
  -- §8.2.1: key at same indent as block sequence
  if s.simpleKey.possible && !s.inFlow then
    let keyCol : Int := s.simpleKey.pos.col
    if keyCol <= s.currentIndent then
      if let some top := s.indents.back? then
        if top.isSequence && keyCol == top.column then
          throw (.trailingContent s.simpleKey.pos.line s.simpleKey.pos.col)
  -- T833: missing comma in flow mapping
  if s.simpleKey.possible && s.inFlow && s.simpleKey.tokenIndex > 0 then
    if let some prevTok := s.tokens[s.simpleKey.tokenIndex - 1]? then
      if prevTok.val == .value && prevTok.pos.line != s.line then
        throw (.invalidFlowEntry s.line s.col)

/-- Build the prepared state: resolve a pending simple key by overwriting
    placeholder slots (via `Array.setIfInBounds`), optionally pushing indent
    for block mappings, or start a new mapping if no simple key.
    Tokens are preserved or grown (never shifted).

    **Note**: `let` bindings are inlined across `if` boundaries so that
    `split` can discharge each branch independently in proofs. -/
def scanValuePrepare (s : ScannerState) : ScannerState :=
  if s.simpleKey.possible then
    let idx := s.simpleKey.tokenIndex
    if !s.inFlow then
      if (s.simpleKey.pos.col : Int) > s.currentIndent then
        let tokens := s.tokens.setIfInBounds idx ⟨s.simpleKey.pos, .blockMappingStart⟩
                      |>.setIfInBounds (idx + 1) ⟨s.simpleKey.pos, .key⟩
        { s with
          tokens := tokens
          indents := s.indents.push { column := (s.simpleKey.pos.col : Int), isSequence := false }
          simpleKey := { possible := false } }
      else
        let tokens := s.tokens.setIfInBounds (idx + 1) ⟨s.simpleKey.pos, .key⟩
        { s with tokens := tokens, simpleKey := { possible := false } }
    else
      let tokens := s.tokens.setIfInBounds (idx + 1) ⟨s.simpleKey.pos, .key⟩
      { s with tokens := tokens, simpleKey := { possible := false } }
  else if s.explicitKeyLine.isSome then
    { s with simpleKey := { possible := false } }
  else
    if !s.inFlow then pushMappingIndent s s.col else s

/-- Check for illegal tab after explicit `:` at or below indent level (§6.1).
    `origCol`/`origIndent` come from the *original* state (before emit/advance);
    the peek is on the *advanced* state. -/
def scanValueTabCheck (origCol : Int) (origIndent : Int) (s_adv : ScannerState) : Except ScanError Unit :=
  if origCol ≤ origIndent && !s_adv.inFlow then
    if let some '\t' := s_adv.peek? then
      throw (.tabInIndentation s_adv.line s_adv.col)
    else .ok ()
  else .ok ()

def scanValue (s : ScannerState) : Except ScanError ScannerState := do
  let s_kc := scanValueClearKey s
  scanValueValidate s_kc
  let s_prepared := scanValuePrepare s_kc
  let s_with_token := s_prepared.emit .value
  let s_after_advance := s_with_token.advance
  scanValueTabCheck s.col s.currentIndent s_after_advance
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
def collectAnchorNameLoop (s : ScannerState) (name : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (name, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isFlowIndicatorBool c && !isWhiteSpaceBool c && !isLineBreakBool c then
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
def collectVerbatimTagLoop (s : ScannerState) (uri : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (uri, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '>' => (uri, s.advance)
    | some c => collectVerbatimTagLoop s.advance (uri.push c) fuel'
    | none => (uri, s)

-- Helper: Collect tag suffix characters (non-whitespace, non-flow).
def collectTagSuffixLoop (s : ScannerState) (suffix : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (suffix, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isWhiteSpaceBool c && !isLineBreakBool c && !isFlowIndicatorBool c then
        collectTagSuffixLoop s.advance (suffix.push c) fuel'
      else
        (suffix, s)
    | none => (suffix, s)

-- Helper: Collect tag handle characters until '!' or invalid char.
-- Returns (chars_before_bang, found_second_bang, state).
def collectTagHandleLoop (s : ScannerState) (chars : String) (fuel : Nat) : String × Bool × ScannerState :=
  match fuel with
  | 0 => (chars, false, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '!' => (chars, true, s.advance)
    | some c =>
      if !isWhiteSpaceBool c && !isLineBreakBool c && !isFlowIndicatorBool c then
        collectTagHandleLoop s.advance (chars.push c) fuel'
      else
        (chars, false, s)
    | none => (chars, false, s)

/-- Scan a verbatim tag `!<uri>`.  Pre: scanner after first `!`, peek = `<`. -/
def scanVerbatimTag (s : ScannerState) (startPos : YamlPos) : ScannerState :=
  let s_after_open := s.advance
  let fuel := startPos.offset + s.inputEnd - s_after_open.offset  -- conservative fuel
  let (uri, s_after_uri) := collectVerbatimTagLoop s_after_open "" fuel
  s_after_uri.emitAt startPos (.tag "" uri)

/-- Scan a secondary tag `!!suffix`.  Pre: scanner after first `!`, peek = `!`. -/
def scanSecondaryTag (s : ScannerState) (startPos : YamlPos) : ScannerState :=
  let s_after_second_bang := s.advance
  let fuel := startPos.offset + s.inputEnd - s_after_second_bang.offset
  let (suffix, s_after_suffix) := collectTagSuffixLoop s_after_second_bang "" fuel
  s_after_suffix.emitAt startPos (.tag "!!" suffix)

/-- Scan a named/primary tag `!handle!suffix` or `!suffix`.
    Pre: scanner after first `!`, peek ≠ `<` and ≠ `!`. -/
def scanNamedTag (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) : ScannerState :=
  let fuel := inputEnd - s.offset
  let (chars, foundBang, s_after_handle) := collectTagHandleLoop s "" fuel
  let (handle, suffix_or_chars) :=
    if foundBang then
      ("!" ++ chars ++ "!", "")
    else
      ("!", chars)
  let (suffix, s_after_suffix) :=
    if foundBang then
      let fuel' := inputEnd - s_after_handle.offset
      collectTagSuffixLoop s_after_handle "" fuel'
    else
      (suffix_or_chars, s_after_handle)
  s_after_suffix.emitAt startPos (.tag handle suffix)

/-- Scan a tag property (`!`, `!!suffix`, `!handle!suffix`, `!<uri>`).
    Dispatches to `scanVerbatimTag`, `scanSecondaryTag`, or `scanNamedTag`. -/
def scanTag (s : ScannerState) : ScannerState :=
  let startPos := s.currentPos
  let s_after_bang := s.advance  -- consume `!`
  let s_inner := match s_after_bang.peek? with
    | some '<' => scanVerbatimTag s_after_bang startPos
    | some '!' => scanSecondaryTag s_after_bang startPos
    | _        => scanNamedTag s_after_bang startPos s.inputEnd
  { s_inner with simpleKeyAllowed := false }

/-! ## Directive Scanning -/

-- Helper: Collect directive name (non-whitespace, non-linebreak characters).
def collectDirectiveNameLoop (s : ScannerState) (name : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (name, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isWhiteSpaceBool c && !isLineBreakBool c then
        collectDirectiveNameLoop s.advance (name.push c) fuel'
      else
        (name, s)
    | none => (name, s)

-- Helper: Collect version major digits until '.'.
def collectVersionMajorLoop (s : ScannerState) (major : String) (fuel : Nat) : String × ScannerState :=
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
def collectVersionMinorLoop (s : ScannerState) (minor : String) (fuel : Nat) : String × ScannerState :=
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
def collectTagHandleDirectiveLoop (s : ScannerState) (handle : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (handle, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isWhiteSpaceBool c then
        collectTagHandleDirectiveLoop s.advance (handle.push c) fuel'
      else
        (handle, s)
    | none => (handle, s)

-- Helper: Collect TAG directive prefix (non-whitespace, non-linebreak characters).
def collectTagPrefixLoop (s : ScannerState) (pfx : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (pfx, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isWhiteSpaceBool c && !isLineBreakBool c then
        collectTagPrefixLoop s.advance (pfx.push c) fuel'
      else
        (pfx, s)
    | none => (pfx, s)

/-- Handle `%YAML` directive: parse version, validate trailing content, emit token.

    **Implements** (YAML 1.2.2 §6.8.1):
    - `[86]  ns-yaml-directive` = `"YAML" s-separate-in-line ns-yaml-version`
    - `[88]  ns-yaml-version`  = `ns-dec-digit+ "." ns-dec-digit+`

    **Pre**: `s` is state after `%YAML` + whitespace skip; `startPos` is position of `%`.
    **Post**: Emits `.versionDirective major minor`, sets `seenYamlDirective`.
    **Error**: `duplicateYamlDirective`, `directiveTrailingContent`. -/
def scanYamlDirective (s : ScannerState) (s_after_ws : ScannerState) (startPos : YamlPos) :
    Except ScanError ScannerState := do
  if s.seenYamlDirective then
    throw (.duplicateYamlDirective s.line)
  let fuel_major := s.inputEnd - s_after_ws.offset
  let (major, s_after_dot) := collectVersionMajorLoop s_after_ws "" fuel_major
  let fuel_minor := s.inputEnd - s_after_dot.offset
  let (minor, s_after_version) := collectVersionMinorLoop s_after_dot "" fuel_minor
  let colBeforeWs := s_after_version.col
  let s_validated := skipWhitespace s_after_version
  match s_validated.peek? with
  | some '#' =>
    if s_validated.col == colBeforeWs then
      throw (.directiveTrailingContent s_validated.line s_validated.col)
  | some c => if !isLineBreakBool c then throw (.directiveTrailingContent s_validated.line s_validated.col)
  | none => pure ()
  let s_with_token := s_validated.emitAt startPos (.versionDirective major.toNat! minor.toNat!)
  .ok { s_with_token with seenYamlDirective := true, directivesPresent := true }

/-- Handle `%TAG` directive: parse handle and prefix, emit token.

    **Implements** (YAML 1.2.2 §6.8.2):
    - `[89]  ns-tag-directive` = `"TAG" s-separate-in-line c-tag-handle s-separate-in-line ns-tag-prefix`

    **Pre**: `s_after_ws` is state after `%TAG` + whitespace skip; `startPos` is position of `%`.
    **Post**: Emits `.tagDirective handle prefix`, sets `directivesPresent`. -/
def scanTagDirective (s : ScannerState) (s_after_ws : ScannerState) (startPos : YamlPos) :
    Except ScanError ScannerState := do
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

/-- Scan a directive (`%YAML` or `%TAG`).

    **Implements** (YAML 1.2.2 §6.8):
    - `[82]  l-directive` = `"%" ( ns-yaml-directive | ns-tag-directive | ns-reserved-directive ) s-l-comments`
    - `[20]  c-directive` = `"%"`

    **Decomposed for provability**: YAML and TAG handling are in
    `scanYamlDirective` and `scanTagDirective` respectively, each with ≤ 6
    branch points. This wrapper has only 3 branch points.

    **Pre**: Scanner at `%` at column 0, `allowDirectives` is true.
    **Post**: Emits `.versionDirective major minor` or `.tagDirective handle prefix`.
    Sets `seenYamlDirective`, `directivesPresent` as appropriate.
    **Error**: `directiveAfterContent` (directive after document content without `...`),
    `duplicateYamlDirective` (second `%YAML` in same document),
    `directiveTrailingContent` (content after version string). -/
def scanDirective (s : ScannerState) : Except ScanError ScannerState :=
  if !s.allowDirectives then
    .error (.directiveAfterContent s.line)
  else
    let startPos := s.currentPos
    let s_after_percent := s.advance
    let fuel := s.inputEnd - s_after_percent.offset
    let (name, s_after_name) := collectDirectiveNameLoop s_after_percent "" fuel
    let s_after_ws := skipWhitespace s_after_name
    if name == "YAML" then
      scanYamlDirective s s_after_ws startPos
    else if name == "TAG" then
      scanTagDirective s s_after_ws startPos
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

/-- Helper: skip whitespace (spaces + tabs) using structural recursion.
    Used by scanDocumentEnd for trailing content validation. -/
def skipDocEndWhitespace (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if c == ' ' || c == '\t' then skipDocEndWhitespace s.advance fuel'
      else s
    | none => s

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
  -- Skip whitespace on the same line (structural recursion via skipDocEndWhitespace)
  let s'' := skipDocEndWhitespace result (s.inputEnd - result.offset + 1)
  -- After whitespace, must be comment (#), newline, or EOF
  match s''.peek? with
  | none => pure ()  -- EOF is fine
  | some '#' => pure ()  -- comment is fine
  | some c =>
    if isLineBreakBool c then pure ()  -- newline is fine
    else throw (.trailingContentAfterDocEnd s''.line s''.col)
  .ok result

/-! ## Escape Sequence Processing -/

/-- Helper for parseHexEscape: collect up to `n` hex digits using structural recursion. -/
def collectHexDigitsLoop (s : ScannerState) (hex : String) (n : Nat) : String × ScannerState :=
  match n with
  | 0 => (hex, s)
  | n' + 1 =>
    match s.peek? with
    | some c =>
      if c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F') then
        collectHexDigitsLoop s.advance (hex.push c) n'
      else (hex, s)
    | none => (hex, s)

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
  let (hex, s') := collectHexDigitsLoop s "" n
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

/-- Helper for foldQuotedNewlines: count consecutive empty lines using structural recursion.

    Skips blank lines (spaces followed by line break), counting them.
    Returns on first non-blank line content or EOF.

    **Termination**: Structurally recursive on `fuel`. -/
def foldQuotedNewlinesLoop (s : ScannerState) (emptyCount : Nat) (fuel : Nat) :
    ScannerState × Nat :=
  match fuel with
  | 0 => (s, emptyCount)
  | fuel' + 1 =>
    let saved := s
    let s_skipped := skipSpaces s
    match s_skipped.peek? with
    | some c =>
      if isLineBreakBool c then
        foldQuotedNewlinesLoop (consumeNewline s_skipped) (emptyCount + 1) fuel'
      else (saved, emptyCount)
    | none => (s, emptyCount)

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
  let (s', emptyCount) := foldQuotedNewlinesLoop s' 0 (s.inputEnd - s'.offset + 1)
  -- §6.1: After consuming empty lines and leading spaces on the continuation
  -- line, check for tab-as-indentation.  If we haven't advanced past the
  -- current block indent level, a tab here is in the indentation zone.
  let s' := skipSpaces s'
  if !s'.inFlow && (s'.col : Int) ≤ s'.currentIndent then
    if let some '\t' := s'.peek? then
      throw (.tabInIndentation s'.line s'.col)
  let s' := skipWhitespace s'
  if emptyCount > 0 then
    return (String.ofList (List.replicate emptyCount '\n'), s')
  else
    return (" ", s')

-- Helper: Skip whitespace for trailing content validation
def skipTrailingSpaces (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if c == ' ' || c == '\t' then
        skipTrailingSpaces s.advance fuel'
      else
        s
    | none => s

-- Helper: Validate trailing content after closing quote (block context only)
def validateTrailingContent (s : ScannerState) (inputEnd : Nat) : Except ScanError Unit := do
  let probe := skipTrailingSpaces s (inputEnd - s.offset + 1)
  match probe.peek? with
  | none => pure ()
  | some c =>
    if isLineBreakBool c || c == '#' || c == ':' then
      pure ()
    else
      throw (.trailingContent probe.line probe.col)

-- Helper: Collect double-quoted content using structural recursion
def collectDoubleQuotedLoop (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    Except ScanError (String × ScannerState) :=
  match fuel with
  | 0 => .error (.unterminatedScalar .doubleQuoted startPos.line)
  | fuel' + 1 =>
    match s.peek? with
    | none => .error (.unterminatedScalar .doubleQuoted startPos.line)
    | some '"' =>
      -- Closing quote found
      .ok (content, s.advance)
    | some '\\' =>
      -- Escape sequence
      let s_after_backslash := s.advance
      match s_after_backslash.peek? with
      | some c =>
        if isLineBreakBool c then do
          -- Escaped line break: consume and skip whitespace
          let s_after_newline := consumeNewline s_after_backslash
          let s_after_ws := skipWhitespace s_after_newline
          collectDoubleQuotedLoop s_after_ws content fuel' startPos inFlow currentIndent inputEnd
        else do
          -- Regular escape sequence
          let (ch, s_after_escape) ← processEscape s_after_backslash
          let content' := content.push ch
          collectDoubleQuotedLoop s_after_escape content' fuel' startPos inFlow currentIndent inputEnd
      | none => .error (.unterminatedEscape s_after_backslash.line)
    | some c =>
      if isLineBreakBool c then do
        -- Line break: fold newlines
        let content_trimmed := trimTrailingWS content
        let (folded, s') ← foldQuotedNewlines s
        -- Validation: document markers at col 0 terminate
        if atDocumentStart s' || atDocumentEnd s' then
          throw (.documentMarkerInScalar .doubleQuoted startPos.line)
        -- Validation: continuation line must be indented past block level
        if (s'.col : Int) ≤ currentIndent then
          throw (.underIndentedScalar .doubleQuoted s'.line)
        let content' := content_trimmed ++ folded
        collectDoubleQuotedLoop s' content' fuel' startPos inFlow currentIndent inputEnd
      else
        -- Regular character
        let content' := content.push c
        collectDoubleQuotedLoop s.advance content' fuel' startPos inFlow currentIndent inputEnd

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
  let s_after_open := s.advance
  let fuel := s.inputEnd - s_after_open.offset + 1
  let (content, s_after_close) ← collectDoubleQuotedLoop s_after_open "" fuel startPos s.inFlow s.currentIndent s.inputEnd
  -- §7.3.2: In block context, validate trailing content
  if !s.inFlow then
    validateTrailingContent s_after_close s.inputEnd
  let s_with_token := s_after_close.emitAt startPos (.scalar content .doubleQuoted)
  .ok { s_with_token with simpleKeyAllowed := false }

-- Helper: Collect single-quoted content using structural recursion
def collectSingleQuotedLoop (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    Except ScanError (String × ScannerState) :=
  match fuel with
  | 0 => .error (.unterminatedScalar .singleQuoted startPos.line)
  | fuel' + 1 =>
    match s.peek? with
    | none => .error (.unterminatedScalar .singleQuoted startPos.line)
    | some '\'' =>
      let s_after_quote := s.advance
      match s_after_quote.peek? with
      | some '\'' =>
        -- Escaped quote: ''
        let content' := content.push '\''
        collectSingleQuotedLoop s_after_quote.advance content' fuel' startPos inFlow currentIndent inputEnd
      | _ =>
        -- Closing quote found
        .ok (content, s_after_quote)
    | some c =>
      if isLineBreakBool c then do
        -- Line break: fold newlines
        let content_trimmed := trimTrailingWS content
        let (folded, s') ← foldQuotedNewlines s
        -- Validation: document markers at col 0 terminate
        if atDocumentStart s' || atDocumentEnd s' then
          throw (.documentMarkerInScalar .singleQuoted startPos.line)
        -- Validation: continuation line must be indented past block level
        if (s'.col : Int) ≤ currentIndent then
          throw (.underIndentedScalar .singleQuoted s'.line)
        let content' := content_trimmed ++ folded
        collectSingleQuotedLoop s' content' fuel' startPos inFlow currentIndent inputEnd
      else
        -- Regular character
        let content' := content.push c
        collectSingleQuotedLoop s.advance content' fuel' startPos inFlow currentIndent inputEnd

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
  let s_after_open := s.advance
  let fuel := s.inputEnd - s_after_open.offset + 1
  let (content, s_after_close) ← collectSingleQuotedLoop s_after_open "" fuel startPos s.inFlow s.currentIndent s.inputEnd
  -- §7.3.2: In block context, validate trailing content
  if !s.inFlow then
    validateTrailingContent s_after_close s.inputEnd
  let s_with_token := s_after_close.emitAt startPos (.scalar content .singleQuoted)
  .ok { s_with_token with simpleKeyAllowed := false }

/-! ### Plain Scalar Character Predicates

    `canStartPlainScalarBool` and `isPlainSafeBool` are imported from
    `CharPredicates.lean` via `open Lean4Yaml.CharPredicates`.
-/

-- Helper: Skip blank lines and count them (for plain scalar block context)
def skipBlankLinesLoop (s : ScannerState) (cnt : Nat) (fuel : Nat) (inputEnd : Nat) :
    Nat × ScannerState :=
  match fuel with
  | 0 => (cnt, s)
  | fuel' + 1 =>
    let saved := s
    let s_after_spaces := skipSpaces s
    match s_after_spaces.peek? with
    | some c =>
      if isLineBreakBool c then
        let s_after_newline := consumeNewline s_after_spaces
        skipBlankLinesLoop s_after_newline (cnt + 1) fuel' inputEnd
      else
        (cnt, saved)
    | none => (cnt, s)

-- Result type for plain scalar collection
structure PlainScalarResult where
  content : String
  spaces : String
  state : ScannerState
  terminated : Bool

/-- Check if the current character terminates a plain scalar.
    Returns `some result` to terminate, `none` to continue scanning.

    Covers YAML 1.2.2 §7.3.3 termination conditions:
    - ` #` (comment after whitespace)
    - `: ` or `:` at EOF (value indicator)
    - Flow indicators in flow context
    - Document boundary (`---`/`...`) at column 0 -/
def collectPlainScalar_terminates? (c : Char) (s : ScannerState)
    (content spaces : String) (inFlow : Bool) : Option PlainScalarResult :=
  if c == '#' && spaces.length > 0 then
    some { content, spaces, state := s, terminated := true }
  else if c == ':' then
    let next := s.peekAt? 1
    let terminates := match next with
      | some n => isBlankBool n || (inFlow && isFlowIndicatorBool n)
      | none => true
    if terminates then
      some { content, spaces, state := s, terminated := true }
    else
      none
  else if inFlow && isFlowIndicatorBool c then
    some { content, spaces, state := s, terminated := true }
  else if s.col == 0 && atDocumentBoundary s then
    some { content, spaces, state := s, terminated := true }
  else
    none

/-- Handle a block-context line break during plain scalar collection.
    Returns `none` to terminate (under-indented or document boundary),
    or `some (content', s')` with folded content and new state to continue.

    Implements YAML 1.2.2 §7.3.3 block-context line folding:
    - Consume newline and skip blank lines
    - Check continuation indent and document boundaries
    - Fold: single empty line → space, multiple → newlines -/
def collectPlainScalar_handleBlockLineBreak (s : ScannerState)
    (content : String) (contentIndent : Nat) (inputEnd : Nat) :
    Option (String × ScannerState) :=
  let s_after_newline := consumeNewline s
  let bfuel := inputEnd - s_after_newline.offset + 1
  let (emptyCount, s_after_blanks) := skipBlankLinesLoop s_after_newline 0 bfuel inputEnd
  let s_after_spaces := skipSpaces s_after_blanks
  if s_after_spaces.col < contentIndent then
    none
  else if atDocumentBoundary s_after_spaces then
    none
  else
    let content' := if emptyCount > 0 then
      content ++ String.ofList (List.replicate emptyCount '\n')
    else
      content ++ " "
    some (content', s_after_spaces)

-- Helper: Collect plain scalar content using structural recursion
def collectPlainScalarLoop (s : ScannerState) (content : String) (spaces : String) (fuel : Nat)
    (inFlow : Bool) (contentIndent : Nat) (inputEnd : Nat) :
    Except ScanError PlainScalarResult :=
  match fuel with
  | 0 => .ok { content, spaces, state := s, terminated := false }
  | fuel' + 1 =>
    match s.peek? with
    | none => .ok { content, spaces, state := s, terminated := true }
    | some c =>
      match collectPlainScalar_terminates? c s content spaces inFlow with
      | some result => .ok result
      | none =>
        if isLineBreakBool c then
          if inFlow then do
            let (folded, s_after_fold) ← foldQuotedNewlines s
            match s_after_fold.peek? with
            | some '#' =>
              .ok { content, spaces, state := s_after_fold, terminated := true }
            | _ =>
              let content' := content ++ folded
              collectPlainScalarLoop s_after_fold content' "" fuel' inFlow contentIndent inputEnd
          else
            match collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd with
            | none =>
              .ok { content, spaces, state := s, terminated := true }
            | some (content', s') =>
              collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd
        else if isWhiteSpaceBool c then
          collectPlainScalarLoop s.advance content (spaces.push c) fuel' inFlow contentIndent inputEnd
        else
          if !isPlainSafeBool c inFlow then
            .ok { content, spaces, state := s, terminated := true }
          else
            let content' := content ++ spaces ++ (String.singleton c)
            collectPlainScalarLoop s.advance content' "" fuel' inFlow contentIndent inputEnd

/-- Scan a plain (unquoted) scalar.

    **Implements** (YAML 1.2.2 §7.3.3):
    - `[131] ns-plain(n,c)` = plain scalar content across potentially multiple lines
    - `[123] ns-plain-first(c)` — first character restrictions (via `canStartPlainScalarBool`)
    - `[126] ns-plain-safe(c)` — safe continuation characters (via `isPlainSafeBool`)
    - `[129] ns-plain-char(c)` — `:` and `#` context-sensitive handling
    - `[133] ns-plain-multi-line(c)` — continuation lines must be indented past block level

    Terminators: ` #` (comment), `: ` (value indicator), flow indicators (in flow),
    document boundaries (`---`/`...` at col 0), under-indented continuation.

    **Variable classification:**
    | Variable         | Kind     | Description |
    |------------------|----------|-------------|
    | `contentIndent`  | Position | Floor column for continuation lines |
    | `startPos`       | Pos      | Position for token attribution |

    **Pre**: Scanner at a character satisfying `canStartPlainScalarBool`.
    **Post**: Advances past all plain scalar content (including folded continuations),
    emits `.scalar content .plain`. Sets `simpleKeyAllowed := false`.
    **Error**: None directly (terminates by breaking). -/
def scanPlainScalar (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let inFlow := s.inFlow
  -- §7.3.3: Continuation lines must be indented past the current block level.
  let contentIndent := if inFlow then s.col
    else (max 0 (s.currentIndent + 1)).toNat
  let fuel := (s.inputEnd - s.offset + 1) * 2
  let result ← collectPlainScalarLoop s "" "" fuel inFlow contentIndent s.inputEnd
  -- Trim trailing whitespace: plain scalars never have trailing WS per §7.3.3
  let content_trimmed := trimTrailingWS result.content
  let s_with_token := result.state.emitAt startPos (.scalar content_trimmed .plain)
  .ok { s_with_token with simpleKeyAllowed := false }

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

-- Helper: Auto-detect block scalar content indentation
def autoDetectBlockScalarIndentLoop (probe : ScannerState) (maxWSCol maxWSLine : Nat)
    (minContentIndent : Nat) (fuel : Nat) (inputEnd : Nat) :
    Nat × Nat × ScannerState × Option ScanError :=
  match fuel with
  | 0 =>
    -- No content found. Use max whitespace column as indent
    if maxWSCol > minContentIndent then
      (maxWSCol, maxWSLine, probe, none)
    else
      (minContentIndent, maxWSLine, probe, none)
  | fuel' + 1 =>
    let probe_after_spaces := skipSpaces probe
    match probe_after_spaces.peek? with
    | some c =>
      -- Tab in indentation zone
      if c == '\t' && probe_after_spaces.col < minContentIndent then
        (0, maxWSLine, probe, some (.tabInIndentation probe_after_spaces.line probe_after_spaces.col))
      else if isLineBreakBool c then
        -- Whitespace-only line: track max column
        let maxWSCol' := if probe_after_spaces.col > maxWSCol then probe_after_spaces.col else maxWSCol
        let maxWSLine' := if probe_after_spaces.col > maxWSCol then probe_after_spaces.line else maxWSLine
        let probe' := consumeNewline probe_after_spaces
        autoDetectBlockScalarIndentLoop probe' maxWSCol' maxWSLine' minContentIndent fuel' inputEnd
      else
        -- First non-empty line: set contentIndent
        let detectedIndent := max minContentIndent probe_after_spaces.col
        -- Validate preceding whitespace-only lines
        if maxWSCol > detectedIndent then
          (0, maxWSLine, probe, some (.blockScalarIndentMismatch maxWSLine maxWSCol))
        else
          (detectedIndent, maxWSLine, probe, none)
    | none =>
      -- No more content
      if maxWSCol > minContentIndent then
        (maxWSCol, maxWSLine, probe, none)
      else
        (minContentIndent, maxWSLine, probe, none)

def autoDetectBlockScalarIndent (s : ScannerState) (minContentIndent : Nat) (inputEnd : Nat) :
    Nat × Option ScanError :=
  let fuel := inputEnd - s.offset + 1
  let (indent, _, _, err) := autoDetectBlockScalarIndentLoop s 0 0 minContentIndent fuel inputEnd
  (indent, err)

-- Helper: Consume exactly `count` spaces (for s-indent in block scalars)
def consumeExactSpaces (s : ScannerState) (count : Nat) : Nat × ScannerState :=
  match count with
  | 0 => (0, s)
  | count' + 1 =>
    match s.peek? with
    | some ' ' =>
      let (consumed, s') := consumeExactSpaces s.advance count'
      (consumed + 1, s')
    | _ => (0, s)

-- Helper: Collect content characters until line break
def collectLineContentLoop (s : ScannerState) (content : String) (fuel : Nat) :
    String × ScannerState :=
  match fuel with
  | 0 => (content, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if isLineBreakBool c then
        (content, s)
      else
        collectLineContentLoop s.advance (content.push c) fuel'
    | none => (content, s)

-- Helper: Collect block scalar raw content using structural recursion
def collectBlockScalarLoop (s : ScannerState) (rawContent : String) (fuel : Nat)
    (contentIndent : Nat) (inputEnd : Nat) :
    String × ScannerState :=
  match fuel with
  | 0 => (rawContent, s)
  | fuel' + 1 =>
    -- Check for document boundary
    if s.col == 0 && atDocumentBoundary s then
      (rawContent, s)
    else
      -- Try to consume s-indent(contentIndent): exactly contentIndent spaces
      let (spacesConsumed, s_after_spaces) := consumeExactSpaces s contentIndent
      match s_after_spaces.peek? with
      | none => (rawContent, s_after_spaces)
      | some c =>
        if isLineBreakBool c then
          -- l-empty line: fewer than contentIndent spaces followed by line break
          let rawContent' := rawContent.push '\n'
          let s' := consumeNewline s_after_spaces
          collectBlockScalarLoop s' rawContent' fuel' contentIndent inputEnd
        else if spacesConsumed < contentIndent && !isLineBreakBool c then
          -- Less-indented non-empty line: end of block scalar content
          (rawContent, s)
        else
          -- nb-char+: content characters until line break
          let innerFuel := inputEnd - s_after_spaces.offset + 1
          let (lineContent, s_after_line) := collectLineContentLoop s_after_spaces "" innerFuel
          let rawContent' := rawContent ++ lineContent
          -- Consume line break if present
          match s_after_line.peek? with
          | some c' =>
            if isLineBreakBool c' then
              let rawContent'' := rawContent'.push '\n'
              let s' := consumeNewline s_after_line
              collectBlockScalarLoop s' rawContent'' fuel' contentIndent inputEnd
            else
              collectBlockScalarLoop s_after_line rawContent' fuel' contentIndent inputEnd
          | none => (rawContent', s_after_line)

/-- Helper for scanBlockScalar header parsing using structural recursion.

    Parses up to `fuel` header characters: chomp indicator (`-`/`+`) and
    indentation indicator (digit 1-9) in either order per YAML §8.1 [162].

    **Termination**: Structurally recursive on `fuel`. -/
def parseBlockHeaderLoop (s : ScannerState) (chomp : ChompStyle) (explicitOffset : Option Nat)
    (fuel : Nat) : ChompStyle × Option Nat × ScannerState :=
  match fuel with
  | 0 => (chomp, explicitOffset, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '-' => parseBlockHeaderLoop s.advance .strip explicitOffset fuel'
    | some '+' => parseBlockHeaderLoop s.advance .keep explicitOffset fuel'
    | some c =>
      if c.isDigit && c != '0' then
        parseBlockHeaderLoop s.advance chomp (some (c.toNat - '0'.toNat)) fuel'
      else (chomp, explicitOffset, s)
    | none => (chomp, explicitOffset, s)

/-- Skip optional comment after block-scalar header whitespace.

    **Implements** part of `s-b-comment` (§6.7 / production [76]):
    `c-nb-comment-text` requires `#` preceded by whitespace.

    **Decomposed for provability**: 3 branch points (peek?, peekBack?, commentOk).
    Extracted from `scanBlockScalar` so proofs unfold only this piece. -/
def scanBlockScalarSkipComment (s : ScannerState) : ScannerState :=
  match s.peek? with
  | some '#' =>
    -- Check raw input: # must be preceded by whitespace (not at start-of-line here)
    let commentOk := match s.peekBack? with
      | some c => isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF'  -- BOM is transparent (§5.2)
      | none => false
    if commentOk then skipToEndOfLine s  -- c-nb-comment-text [77]: whitespace preceded `#`
    else s  -- `#` without preceding whitespace — not a comment
  | _ => s

/-- Consume required newline (or EOF) after block-scalar header.

    **Implements** `b-comment` (§6.7 / production [76]):
    expects a line break or end-of-input after the header line.

    **Decomposed for provability**: 3 branch points (peek?, isLineBreakBool, hasMore).
    Extracted from `scanBlockScalar` so proofs unfold only this piece. -/
def scanBlockScalarConsumeNewline (s : ScannerState) : Except ScanError ScannerState :=
  match s.peek? with
  | some c =>
    if isLineBreakBool c then .ok (consumeNewline s)
    else if !s.hasMore then .ok s
    else .error (.expectedNewline s.line)
  | none => .ok s

/-- Collect block-scalar body: detect indentation, collect content, apply chomp/fold, emit token.

    **Implements** (YAML 1.2.2 §8.1):
    - `[163] c-indentation-indicator(m)` — explicit or auto-detect
    - `[171] l-nb-literal-text(n)` / folded content
    - `[164] c-chomping-indicator(t)` — strip / clip / keep

    **Decomposed for provability**: ~5 branch points but most are pure string
    computation (chomp, fold) that don't affect scanner-state fields used in proofs.
    Extracted from `scanBlockScalar` so proofs for `simpleKey`, `simpleKeyStack`,
    `tokens` need only unfold this smaller definition.

    **Pre**: `s_after_newline` is past the header line; `s_orig` provides `currentIndent` and `inputEnd`.
    **Post**: Emits `.scalar content style`, clears simpleKey. -/
def scanBlockScalarBody (s_orig : ScannerState) (s_after_newline : ScannerState)
    (chomp : ChompStyle) (explicitOffset : Option Nat) (isLiteral : Bool) (startPos : YamlPos) :
    Except ScanError ScannerState :=
  let parentIndent : Int := s_orig.currentIndent
  let minContentIndent : Nat := (max 0 (parentIndent + 1)).toNat
  let (contentIndent, autoDetectErr?) := match explicitOffset with
    | some m =>
      ((max 0 (parentIndent + (m : Int))).toNat, (none : Option ScanError))
    | none =>
      autoDetectBlockScalarIndent s_after_newline minContentIndent s_orig.inputEnd
  match autoDetectErr? with
  | some err => .error err
  | none =>
    let fuel := s_orig.inputEnd - s_after_newline.offset + 1
    let (rawContent, s_after_content) := collectBlockScalarLoop s_after_newline "" fuel contentIndent s_orig.inputEnd
    let stripTrailingNewlines (str : String) : String :=
      String.ofList (str.toList.reverse.dropWhile (· == '\n') |>.reverse)
    let content := match chomp with
      | .strip => stripTrailingNewlines rawContent
      | .clip =>
        let stripped := stripTrailingNewlines rawContent
        if rawContent.endsWith "\n" then stripped ++ "\n" else stripped
      | .keep => rawContent
    let content := if isLiteral then content else foldBlockContent content
    let style := if isLiteral then ScalarStyle.literal else ScalarStyle.folded
    let s_with_token := s_after_content.emitAt startPos (.scalar content style)
    .ok { s_with_token with simpleKeyAllowed := true, simpleKey := { possible := false } }

/-- Scan a block scalar (literal `|` or folded `>`).

    **Implements** (YAML 1.2.2 §8.1):
    - `[170] c-l+literal(n)` = `"|" c-b-block-header(t,m) l-literal-content(n+m,t)`
    - `[174] c-l+folded(n)`  = `">" c-b-block-header(t,m) l-folded-content(n+m,t)`
    - `[162] c-b-block-header(t,m)` = `(c-indentation-indicator(m) c-chomping-indicator(t) | ...) s-b-comment`
    - `[163] c-indentation-indicator(m)` = `ns-dec-digit` (explicit) | `ε` (auto-detect)
    - `[164] c-chomping-indicator(t)` = `"-"` (STRIP) | `"+"` (KEEP) | `ε` (CLIP)
    - `[171] l-nb-literal-text(n)` = `l-empty(n,BLOCK-IN)* s-indent(n) nb-char+`
    - `[63]  s-indent(n)` = `s-space × n`  ← **spaces only**

    **Decomposed for provability**: Comment handling (`scanBlockScalarSkipComment`,
    3 branches), newline consumption (`scanBlockScalarConsumeNewline`, 3 branches),
    and body processing (`scanBlockScalarBody`, ≤5 branches) are each extracted.
    This wrapper has only 1 branch point (match on newline result), eliminating
    the need for `set_option maxHeartbeats 400000` in proofs.

    **Pre**: Scanner at `|` or `>`. `s.col` = `n` (parent indent level).
    **Post**: Scanner past block scalar content. Emits `.scalar content style`.
    **Error**: Missing newline after header. -/
def scanBlockScalar (s : ScannerState) : Except ScanError ScannerState :=
  let header := parseBlockHeaderLoop s.advance .clip none 2
  let s_after_comment := scanBlockScalarSkipComment (skipWhitespace header.2.2)
  match scanBlockScalarConsumeNewline s_after_comment with
  | .error e => .error e
  | .ok s_after_newline =>
    scanBlockScalarBody s s_after_newline header.1 header.2.1 (s.peek? == some '|') s.currentPos

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
  else if st.simpleKeyAllowed then
    -- Reserve 2 placeholder slots for potential .blockMappingStart + .key
    -- (block context) or .key + spare (flow context).
    let idx := st.tokens.size
    let ph : Positioned YamlToken := ⟨st.currentPos, .placeholder⟩
    let st := { st with tokens := st.tokens.push ph |>.push ph }
    { st with simpleKey := {
        possible := true
        tokenIndex := idx
        pos := st.currentPos
        endLine := st.line } }
  else st

/-- Check whether a block-entry indicator (`-`) is followed by a blank or EOF. -/
def isBlockEntryCandidate (s : ScannerState) : Bool :=
  match s.peekAt? 1 with
  | some n => isBlankBool n
  | none => true

/-- Check whether a key indicator (`?`) is followed by a blank, flow indicator, or EOF. -/
def isKeyCandidate (s : ScannerState) : Bool :=
  match s.peekAt? 1 with
  | some n => isBlankBool n || (s.inFlow && isFlowIndicatorBool n)
  | none => true

/-- Check whether a value indicator (`:`) should be recognized.
    In flow context with a possible simple key, always true.
    Otherwise, requires a blank, flow indicator, or EOF after. -/
def isValueCandidate (s : ScannerState) : Bool :=
  if s.inFlow && s.simpleKey.possible then true
  else match s.peekAt? 1 with
  | some n => isBlankBool n || (s.inFlow && isFlowIndicatorBool n)
  | none => true

/-- §7.5: After a flow collection close returns us to block context,
    validate that only whitespace, comments, `:`, or end-of-line follow
    on the same line. -/
def validateFlowClose (s' : ScannerState) : Except ScanError Unit := do
  if s'.flowLevel == 0 then
    let probe := skipTrailingSpaces s' (s'.inputEnd - s'.offset + 1)
    match probe.peek? with
    | none => pure ()
    | some pc =>
      if isLineBreakBool pc || pc == '#' || pc == ':' then pure ()
      else return ← .error (.trailingContent probe.line probe.col)

/-- Preprocessing phase of `scanNextToken`.

    Skips whitespace/comments, handles block indentation unwind,
    saves simple key position, and peeks at the next character.

    Returns `none` if input is exhausted, or `some (s', c)` where
    `s'` is the preprocessed state and `c` is the peeked character. -/
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
def scanNextToken_dispatchContent (s : ScannerState) (c : Char) :
    Except ScanError ScannerState := do
  if c == '&' then return scanAnchorOrAlias s true
  if c == '*' then return scanAnchorOrAlias s false
  if c == '!' then return scanTag s
  if c == '|' || c == '>' then
    let s' ← scanBlockScalar s
    return s'
  if c == '"' then
    let s' ← scanDoubleQuoted s
    -- §7.4: Quoted scalars can span lines; update simpleKey.endLine
    -- so scanValue can check key-end-line vs `:` line.
    let s' := if s'.simpleKey.possible then
      { s' with simpleKey := { s'.simpleKey with endLine := s'.line } }
    else s'
    return s'
  if c == '\'' then
    let s' ← scanSingleQuoted s
    let s' := if s'.simpleKey.possible then
      { s' with simpleKey := { s'.simpleKey with endLine := s'.line } }
    else s'
    return s'
  if canStartPlainScalarBool c (s.peekAt? 1) s.inFlow then
    let s' ← scanPlainScalar s; return s'
  .error (.unexpectedChar c s.line s.col)

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

/-- Like `scan` but filters out internal placeholder tokens.
    Use this for all user-facing output and tests. -/
def scanFiltered (input : String) : Except ScanError (Array (Positioned YamlToken)) :=
  match scan input with
  | .ok tokens => .ok (tokens.filter fun t => t.val != .placeholder)
  | .error e => .error e

end Lean4Yaml.Scanner
