/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.IndexedScanner
public import L4YAML.Scanner.State
public import L4YAML.Token.Token

public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-! # `IndexedState` — Phase 3 Step 5a scanner state

Mirrors `L4YAML.Scanner.ScannerState` (`L4YAML/Scanner/State.lean`)
but threads `IxCursor input` instead of the un-indexed (offset, line,
col) triple, and accumulates an indexed `TokenStream input` rather
than `Array (Positioned YamlToken)`.

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
    so this file does not depend on `L4YAML.Scanner.State`. -/
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
  /-- Indexed twin of `ScannerState.pendingKeys`: one slot per `indents` level. -/
  pendingKeys : Array (Option Nat) := #[none]
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
  /-- Line number of the most recent block-context IMPLICIT value indicator
      (item 48).  `[194] c-l-block-map-implicit-value`'s value slot is
      `s-l+block-node` — no compact alternative, no same-line mapping — so a
      block-collection indicator or a second `:` on this line has no
      derivation.  The EXPLICIT value (`[192]`'s, whose slot is
      `s-l+block-indented` with the compact alternatives) does not set it,
      which is what keeps `? a⏎: - b` and `? a⏎: b: c` served. -/
  implicitValueLine : Option Nat := none
  /-- Line of the most recent `---` document-start marker (item 299).  §9.1.1's
      `[203] c-directives-end` line admits `s-l-comments` or one same-line
      node and nothing else, so a block indicator or value indicator
      dispatched with the marker still on the line has no derivation.  Set by
      `scanDocumentStart` and written by nothing else; never cleared, since
      lines only grow and a marker on an earlier line never reads as "on the
      line" again.  `markerOnLine` is the read the three block checks make. -/
  docStartLine : Option Nat := none
  /-- Column of the pending `?` (item 48), meaningful only while
      `explicitKeyLine` is set: an implicit `:` whose resolved key sits
      DEEPER than this column is inside the explicit key's own content
      (spec 8.19's multi-line compact keys), so the pending `?` survives it;
      at or left of it, a sibling entry has closed the `?`-entry. -/
  explicitKeyCol : Int := -1
  /-- Saved `(explicitKeyLine, explicitKeyCol)` pairs for enclosing flow
      nesting levels (item 98) — the explicit-key stamp is scoped to its own
      flow level.  Pushed on flow-open, popped on flow-close; twin of
      `L4YAML.Scanner.ScannerState.explicitKeyStack`. -/
  explicitKeyStack : Array (Option Nat × Int) := #[]
  /-- Anchor names defined in the current document. -/
  definedAnchors : Array String := #[]
  /-- Collected comments (position × text). Populated by
      `skipToContentSWithComments` (used by the comment-preserving
      scan entry point `scanWithCommentsIx`); stays empty for the
      ordinary `scanIx` / `scanFilteredIx` pipelines. -/
  comments : Array (YamlPos × String) := #[]

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

/-- Indexed twin of `ScannerState.markPendingKey`. -/
def markPendingKey {input : String} (s : ScannerStateIx input) (line : Nat) : ScannerStateIx input :=
  { s with pendingKeys := s.pendingKeys.set! (s.indents.size - 1) (some line) }

def indentColumns {input : String} (s : ScannerStateIx input) : Array Int := s.indents.map (·.column)

/-- Close every pending explicit key the content `c` under the cursor lands past
    (`PendingKeys.closeStale`). -/
def closeStaleAt {input : String} (s : ScannerStateIx input) (c : Char) : ScannerStateIx input :=
  { s with pendingKeys :=
      PendingKeys.closeStale s.indentColumns s.pendingKeys s.cursor.pos.col c (s.peekAt? 1) }

def clearPendingKeyAt {input : String} (s : ScannerStateIx input) (col : Int) : ScannerStateIx input :=
  { s with pendingKeys := PendingKeys.closeAt s.indentColumns s.pendingKeys col }

def innermostPendingKey {input : String} (s : ScannerStateIx input) : Option Nat × Int :=
  PendingKeys.innermost s.indentColumns s.pendingKeys

def readPendingKey {input : String} (s : ScannerStateIx input) : ScannerStateIx input :=
  { s with explicitKeyLine := s.innermostPendingKey.1, explicitKeyCol := s.innermostPendingKey.2 }

/-! ## Navigation -/

/-- Advance the cursor by one character (no state changes elsewhere). -/
@[inline] def advance {input : String} (s : ScannerStateIx input) : ScannerStateIx input :=
  { s with cursor := s.cursor.advance }

/-- Advance the cursor by `n` characters. -/
@[inline] def advanceN {input : String} (s : ScannerStateIx input) (n : Nat) :
    ScannerStateIx input :=
  { s with cursor := s.cursor.advanceN n }

/-- Indexed twin of `L4YAML.ScannerState.consumeBOM` (§5.2): consume the
    leading `[3] c-byte-order-mark` without spending a column, so that
    `[63] s-indent(n)` on the first line is counted from the character
    after it.  Only `pos.col` moves; `posBound` constrains `pos.offset`
    alone, so the cursor's well-formedness rides through untouched. -/
@[yaml_spec "5.2" 3 "c-byte-order-mark",
  yaml_spec "9.1.1" 202 "l-document-prefix"]
def consumeBOM {input : String} (s : ScannerStateIx input) : ScannerStateIx input :=
  let s := s.advance
  { s with cursor := { s.cursor with pos := { s.cursor.pos with col := 0 } } }

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

/-- Indexed twin of `L4YAML.Scanner.ScannerState.markerOnLine` (item 299): the
    `---` marker is on the cursor's line, off the `docStartLine` field
    `scanDocumentStartIx` writes. -/
@[yaml_spec "9.1.1" 203 "c-directives-end"]
def markerOnLine {input : String} (s : ScannerStateIx input) : Bool :=
  s.docStartLine == some s.cursor.pos.line

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
      let s' := { s' with indents := s'.indents.pop, pendingKeys := s'.pendingKeys.pop }
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
    { s' with indents := s'.indents.push { column := col, isSequence := true }, pendingKeys := s'.pendingKeys.push none }
  else s

/-- Push a new mapping-indent entry if `col` is deeper than the current
    indent; emits `blockMappingStart`. -/
def pushMappingIndentIx {input : String} (s : ScannerStateIx input) (col : Int) :
    ScannerStateIx input :=
  if col > s.currentIndent then
    let s' := s.emit YamlToken.blockMappingStart
    { s' with indents := s'.indents.push { column := col, isSequence := false }, pendingKeys := s'.pendingKeys.push none }
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
    break, recursing).

    Mirrors `L4YAML.Scanner.skipToContentLoop`'s side effects: whenever a
    line break is crossed, the legacy
    (`Scanner.consumeNewline` → `Scanner.skipToContentLoop`) sets
    `needIndentCheck := true` so the next `scanNextToken_preprocess`
    will run `unwindIndents` for block-context outdents, and (outside a
    flow sequence) sets `simpleKeyAllowed := true` so the next item on
    the new line can open an implicit key.

    The indexed `Indexed.skipToContent` operates purely on the cursor,
    so we re-apply both state-level effects here by detecting whether
    the line number changed.

    Step 6f.0: these newline-crossing resets were missing prior to the
    placeholder-filter restoration commit. Symptoms:
    - `a: 1\nb: 2` errored with `invalidImplicitKey` (missing
      `simpleKeyAllowed := true` reset).
    - Nested block sequences (`-\n  - a\n  - b\n-\n  - c`) failed to
      emit the closing `blockEnd` on outdent (missing
      `needIndentCheck := true` reset). -/
@[inline] def skipToContentS {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let newCursor := L4YAML.Scanner.Indexed.skipToContent s.cursor
  if newCursor.pos.line != s.cursor.pos.line then
    { s with cursor := newCursor,
              needIndentCheck := true,
              simpleKeyAllowed := if s.isInFlowSequence then s.simpleKeyAllowed else true }
  else
    { s with cursor := newCursor }

/-- Comment-preserving variant of `skipToContentS`. Advances the cursor
    past whitespace, comments, and line breaks while accumulating each
    comment's `(position, text)` pair into `s.comments`. Mirrors the
    legacy `Scanner.skipToContentLoop` + `skipToContentComment` pair
    that thread the side-channel `comments` array through
    `ScannerState` during `scanWithComments`.

    Used by the comment-preserving scan entry point
    (`scanWithCommentsIx` in `IndexedDispatch`). The ordinary scan
    pipeline calls `skipToContentS`, which discards comment text. -/
@[inline] def skipToContentSWithComments {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let (newCursor, newComments) :=
    L4YAML.Scanner.Indexed.skipToContentWithComments s.cursor s.comments
  if newCursor.pos.line != s.cursor.pos.line then
    { s with cursor := newCursor, comments := newComments,
              needIndentCheck := true,
              simpleKeyAllowed := if s.isInFlowSequence then s.simpleKeyAllowed else true }
  else
    { s with cursor := newCursor, comments := newComments }

/-! ## Tab-in-indentation backward scan (§6.1)

Indexed analogue of `ScannerState.hasTabInPrecedingWhitespace`
(`Scanner/Whitespace.lean`). Used by `scanBlockEntryIx` to enforce
YAML 1.2.2 §6.1: tabs must not be used in indentation. Scans
backward through the contiguous whitespace run immediately before
the cursor; returns `true` iff at least one `\t` appears in it.

Pure on `input` and the cursor offset — does not consume any
characters, does not modify state. -/

/-- Backward-scan loop (structurally recursive on `fuel`).

    `pos` is the byte offset at which we look one character back.
    The loop terminates when:
    - `pos = 0` (start of input): no tab found, returns `false`.
    - The character at `pos - 1` is `\t`: returns `true`.
    - The character at `pos - 1` is `' '`: continue scanning back.
    - Otherwise (non-whitespace): the indentation run ended, returns
      `false`.

    Caller passes `pos` as the fuel — guaranteed sufficient because
    each iteration strictly decreases `pos`. -/
@[yaml_spec "6.1"]
def hasTabInPrecedingWhitespaceLoop (input : String) (pos : Nat) :
    Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if pos == 0 then false
    else
      let prevPos := (String.Pos.Raw.prev input ⟨pos⟩).byteIdx
      let c := String.Pos.Raw.get input ⟨prevPos⟩
      if c == '\t' then true
      else if c == ' ' then hasTabInPrecedingWhitespaceLoop input prevPos fuel
      else false

/-- Detect a tab in the whitespace immediately before the cursor.
    Returns `true` iff any `\t` appears in the contiguous
    spaces-and-tabs run ending at the cursor. -/
@[yaml_spec "6.1"]
def hasTabInPrecedingWhitespace {input : String}
    (s : ScannerStateIx input) : Bool :=
  hasTabInPrecedingWhitespaceLoop input s.cursor.pos.offset s.cursor.pos.offset

/-- Indexed analogue of `ScannerState.tabInLineIndentLoop`: walk a FIXED `col`
    characters back, and report `false` the moment one of them is not an
    `s-white`.  `true` therefore says the run in front of the token is the
    line's own `[63] s-indent(n)`, and that it contains a tab. -/
@[yaml_spec "6.1" 63 "s-indent"]
def tabInLineIndentLoop (input : String) (pos : Nat) (col : Nat)
    (sawTab : Bool) : Bool :=
  match col with
  | 0 => sawTab
  | col' + 1 =>
    if pos == 0 then sawTab
    else
      let prevPos := (String.Pos.Raw.prev input ⟨pos⟩).byteIdx
      let c := String.Pos.Raw.get input ⟨prevPos⟩
      if c == '\t' then tabInLineIndentLoop input prevPos col' true
      else if c == ' ' then tabInLineIndentLoop input prevPos col' sawTab
      else false

/-- `true` when the entire line prefix in front of the cursor is whitespace
    and a TAB occurs in it. -/
@[yaml_spec "6.1" 63 "s-indent"]
def tabInLineIndent {input : String} (s : ScannerStateIx input) : Bool :=
  tabInLineIndentLoop input s.cursor.pos.offset s.cursor.pos.col false

end ScannerStateIx

end L4YAML.Scanner.Indexed

end Blanket
