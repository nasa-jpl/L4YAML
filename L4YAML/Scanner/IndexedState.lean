/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.IndexedScanner
import L4YAML.Token.Token

/-! # `IndexedState` — Phase 3 Step 5a scanner state (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6). Mirrors `L4YAML.Scanner.ScannerState`
(`L4YAML/Scanner/State.lean`) but threads `IxCursor input` instead of
the un-indexed (offset, line, col) triple, and accumulates an
indexed `TokenStream input` rather than `Array (Positioned YamlToken)`.

## Scope (Step 5a)

- The `ScannerStateIx input` structure.
- Initial state constructor `mk'`.
- Pure accessors (`peek?`, `peekAt?`, `peekBack?`, `hasMore`,
  `currentPos`, `inFlow`, `isInFlowSequence`, `currentIndent`).
- State-level navigation (`advance`, `advanceN`) — thin wrappers
  over the underlying `IxCursor`.
- Token emission (`emit`, `emitAt`) over `TokenStream input`.
- Indent-stack ops (`unwindIndentsIx`, `pushSequenceIndentIx`,
  `pushMappingIndentIx`).

## Indexing discipline

`input : String` is a type parameter. Two `ScannerStateIx input₁`
and `ScannerStateIx input₂` with `input₁ ≠ input₂` are different
types — positions cannot be confused at stage boundaries (D1 from
Blueprint 08).
-/

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.Indexed L4YAML.CharPredicates

/-! ## Indent and Simple-Key bookkeeping (re-exported from legacy) -/

/-- Re-export the legacy `IndentEntry` — column + isSequence flag.
    The shape is identical to `L4YAML.Scanner.IndentEntry`; we re-export
    so the staging file does not depend on `L4YAML.Scanner.State`. -/
structure IndentEntryIx where
  column : Int
  isSequence : Bool
  deriving Repr, BEq, Inhabited

/-- Simple-key tracking, indexed analogue of `L4YAML.Scanner.SimpleKeyState`.

    Indexed on `input` because the saved position is held as an
    `IxCursor input` rather than a bare `YamlPos`; this lets us
    construct `IxToken input` values at the saved position later
    (the cursor's `posBound` discharges the indexed-token bound). -/
structure SimpleKeyStateIx (input : String) where
  possible : Bool := false
  tokenIndex : Nat := 0
  /-- The cursor at the moment the potential key started. Captures
      position + the bound proof needed for indexed token construction. -/
  cursor : IxCursor input := IxCursor.start input
  endLine : Nat := 0

instance (input : String) : Inhabited (SimpleKeyStateIx input) where
  default := { cursor := IxCursor.start input }

/-- The saved position (offset/line/col) of the simple key. -/
@[inline] def SimpleKeyStateIx.pos {input : String} (sk : SimpleKeyStateIx input) :
    YamlPos := sk.cursor.pos

/-! ## `ScannerStateIx` -/

/-- The indexed scanner state: cursor + indent stack + flow tracking +
    simple-key bookkeeping + emitted-token accumulator. The token
    stream is `TokenStream input`, indexed by the same `input` as the
    cursor, so positions cannot be confused at stage boundaries. -/
structure ScannerStateIx (input : String) where
  /-- The current cursor (offset/line/col + bound). -/
  cursor : IxCursor input
  /-- Indent stack. Bottom sentinel `{ column := -1, isSequence := false }`. -/
  indents : Array IndentEntryIx := #[{ column := -1, isSequence := false }]
  /-- Flow nesting level. 0 = block context. -/
  flowLevel : Nat := 0
  /-- Emitted-token accumulator. -/
  tokens : L4YAML.Indexed.TokenStream input := L4YAML.Indexed.TokenStream.empty input
  /-- Simple-key tracking. -/
  simpleKey : SimpleKeyStateIx input := default
  /-- Stack of saved simple keys (one per enclosing flow level). -/
  simpleKeyStack : Array (SimpleKeyStateIx input) := #[]
  /-- Whether a simple key is allowed at the current position. -/
  simpleKeyAllowed : Bool := true
  /-- Whether we need to check indentation at the current position. -/
  needIndentCheck : Bool := true
  /-- Whether directives (`%YAML`, `%TAG`) are allowed at the current position. -/
  allowDirectives : Bool := true
  /-- Whether a `%YAML` directive has been seen in the current directive block. -/
  seenYamlDirective : Bool := false
  /-- Whether any directive has been emitted since the last `---`. -/
  directivesPresent : Bool := false
  /-- Whether a document has ever been started (`---` or implicit content). -/
  documentEverStarted : Bool := false
  /-- Flow-collection type stack: `true` = sequence, `false` = mapping. -/
  flowStack : Array Bool := #[]
  /-- Line number of the most recent unmatched `?` key indicator. -/
  explicitKeyLine : Option Nat := none
  /-- Anchor names defined in the current document. -/
  definedAnchors : Array String := #[]

namespace ScannerStateIx

/-- Build the initial scanner state from an input string.
    Cursor at offset 0, line 0, col 0; empty token stream; sentinel
    indent entry `{ column := -1 }`. -/
def mk' (input : String) : ScannerStateIx input where
  cursor := IxCursor.start input

/-! ## Cursor projections (state-level accessors)

These delegate to the underlying `IxCursor`. -/

/-- The current source position. -/
@[inline] def currentPos {input : String} (s : ScannerStateIx input) : YamlPos :=
  s.cursor.pos

/-- Whether the cursor has more input to read. -/
@[inline] def hasMore {input : String} (s : ScannerStateIx input) : Bool :=
  s.cursor.hasMore

/-- Peek at the current character. -/
@[inline] def peek? {input : String} (s : ScannerStateIx input) : Option Char :=
  s.cursor.peek?

/-- Peek `n` characters ahead. -/
@[inline] def peekAt? {input : String} (s : ScannerStateIx input) (n : Nat) :
    Option Char :=
  s.cursor.peekAt? n

/-- Peek at the character immediately before the cursor. -/
@[inline] def peekBack? {input : String} (s : ScannerStateIx input) : Option Char :=
  s.cursor.peekBack?

/-- Whether we are inside any flow collection (`flowLevel > 0`).

    Implements YAML 1.2.2 §7.4 `[136] in-flow(c)`. -/
@[inline] def inFlow {input : String} (s : ScannerStateIx input) : Bool :=
  s.flowLevel > 0

/-- Whether we are inside a flow sequence (innermost flow level is `[`).

    The innermost flow type is tracked by the back of `flowStack`
    (`true` for sequence, `false` for mapping). -/
@[inline] def isInFlowSequence {input : String} (s : ScannerStateIx input) : Bool :=
  s.flowLevel > 0 && s.flowStack.back? == some true

/-- The column of the innermost block collection's indent.
    Returns `-1` at stream level (before any block opens). -/
@[inline] def currentIndent {input : String} (s : ScannerStateIx input) : Int :=
  match s.indents.back? with
  | some e => e.column
  | none => -1

/-! ## Navigation -/

/-- Advance the cursor by one character (no state changes elsewhere). -/
@[inline] def advance {input : String} (s : ScannerStateIx input) : ScannerStateIx input :=
  { s with cursor := s.cursor.advance }

/-- Advance the cursor by `n` characters. -/
@[inline] def advanceN {input : String} (s : ScannerStateIx input) (n : Nat) :
    ScannerStateIx input :=
  { s with cursor := s.cursor.advanceN n }

/-! ## Token emission

`emit` pushes an `IxToken` for a zero-width point at the current
cursor position. `emitAt` uses a previously-saved position for the
token's start; the cursor's current position is used as the end. -/

/-- Emit a token whose source span is `[s.cursor.pos, s.cursor.pos)`
    (zero width). Used for virtual tokens that do not consume
    characters (e.g. `blockEnd`, `streamStart`, indicator points). -/
def emit {input : String} (s : ScannerStateIx input) (tok : YamlToken) :
    ScannerStateIx input :=
  let t : IxToken input :=
    IxToken.mk' (input := input) s.cursor.pos tok s.cursor.pos
      (Nat.le_refl _) s.cursor.posBound
  { s with tokens := s.tokens.push t }

/-- Emit a token whose source span starts at the saved `startPos`.
    The caller is responsible for `startPos.offset ≤ s.cursor.pos.offset`. -/
def emitAt {input : String} (s : ScannerStateIx input) (startPos : YamlPos)
    (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset) :
    ScannerStateIx input :=
  let t : IxToken input :=
    IxToken.mk' (input := input) startPos tok s.cursor.pos hOrder s.cursor.posBound
  { s with tokens := s.tokens.push t }

/-- Emit a zero-width token at the saved cursor `sk` (its `posBound`
    discharges the indexed-token bound obligation). Used for tokens
    constructed at the simple-key save position. -/
def emitAtCursor {input : String} (s : ScannerStateIx input)
    (sk : IxCursor input) (tok : YamlToken) : ScannerStateIx input :=
  let t : IxToken input :=
    IxToken.mk' (input := input) sk.pos tok sk.pos (Nat.le_refl _) sk.posBound
  { s with tokens := s.tokens.push t }

/-- Overwrite the token at index `i` with a zero-width token at the
    saved cursor `sk` carrying value `tok`. No-op if `i` is out of
    bounds. -/
def overwriteAtCursor {input : String} (s : ScannerStateIx input) (i : Nat)
    (sk : IxCursor input) (tok : YamlToken) : ScannerStateIx input :=
  let t : IxToken input :=
    IxToken.mk' (input := input) sk.pos tok sk.pos (Nat.le_refl _) sk.posBound
  { s with tokens := s.tokens.setIfInBounds i t }

/-! ## Indent-stack operations

`unwindIndentsIx`, `pushSequenceIndentIx`, `pushMappingIndentIx` —
indexed analogues of `Scanner/Indent.lean`. They emit virtual
`blockEnd` / `blockSequenceStart` / `blockMappingStart` tokens. -/

/-- Pop indent entries strictly greater than `col`, emitting `blockEnd`
    for each. Structurally recursive on `fuel`; the call site passes
    `s.indents.size` as the fuel. -/
def unwindIndentsLoopIx {input : String} (s : ScannerStateIx input) (col : Int) :
    Nat → ScannerStateIx input
  | 0 => s
  | fuel + 1 =>
    if s.currentIndent > col && s.indents.size > 1 then
      let s' := s.emit YamlToken.blockEnd
      let s' := { s' with indents := s'.indents.pop }
      unwindIndentsLoopIx s' col fuel
    else s

/-- Unwind the indent stack down to `col`. Pure state transformation
    over the token accumulator + indent stack; cursor unchanged.

    Implements YAML 1.2.2 §6.1 [64]/[65] (`s-indent(<n)`/`s-indent(≤n)`). -/
@[inline] def unwindIndentsIx {input : String} (s : ScannerStateIx input) (col : Int) :
    ScannerStateIx input :=
  unwindIndentsLoopIx s col s.indents.size

/-- Push a new sequence-indent entry if `col` is deeper than the current
    indent; emits `blockSequenceStart`. -/
def pushSequenceIndentIx {input : String} (s : ScannerStateIx input) (col : Int) :
    ScannerStateIx input :=
  if col > s.currentIndent then
    let s' := s.emit YamlToken.blockSequenceStart
    { s' with indents := s'.indents.push { column := col, isSequence := true } }
  else s

/-- Push a new mapping-indent entry if `col` is deeper than the current
    indent; emits `blockMappingStart`. -/
def pushMappingIndentIx {input : String} (s : ScannerStateIx input) (col : Int) :
    ScannerStateIx input :=
  if col > s.currentIndent then
    let s' := s.emit YamlToken.blockMappingStart
    { s' with indents := s'.indents.push { column := col, isSequence := false } }
  else s

/-! ## Whitespace skips at the state level

These wrap `IndexedScanner.skipSpaces` / `skipWhitespace` /
`skipToContent` to thread the state's other fields unchanged. They
do not emit tokens. -/

/-- Skip `s-space*` and update the cursor; return the count for
    indent tracking. -/
def skipSpacesS {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input × Nat :=
  let r := L4YAML.Scanner.Indexed.skipSpaces s.cursor
  ({ s with cursor := r.1 }, r.2)

/-- Skip `s-white*` (spaces + tabs). -/
@[inline] def skipWhitespaceS {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  { s with cursor := L4YAML.Scanner.Indexed.skipWhitespace s.cursor }

/-- Skip the composite `s-l-comments` (whitespace + `#`-comment + line
    break, recursing). -/
@[inline] def skipToContentS {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  { s with cursor := L4YAML.Scanner.Indexed.skipToContent s.cursor }

end ScannerStateIx

end L4YAML.Scanner.Indexed
