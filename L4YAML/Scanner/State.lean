/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Token.Token
import L4YAML.Spec.CharPredicates

/-!
# Scanner State

The `ScannerState` structure and its low-level accessors — the substrate
on which every other scanner submodule operates.

Split from the monolithic `Scanner.lean` during Blueprint Initiative 1
Phase 2 (Scanner split).  See `Blueprint/03-code-organization.md`.

## Scope

- Structural types: `IndentEntry`, `SimpleKeyState`, `ScannerState`.
- Structural well-formedness invariant: `ScannerState.WellFormed`.
- Initial-state constructor: `ScannerState.mk'`.
- Navigation accessors: `peek?`, `peekAt?`, `peekBack?`, `advance`,
  `advanceN`, `hasMore`, `currentPos`, `inFlow`, `isInFlowSequence`,
  `currentIndent`.
- Token emission: `emit`, `emitAt`.

Nothing in this file consumes characters in a spec-productions sense —
those live in `Scanner/Whitespace.lean`, `Scanner/Indent.lean`, etc.
-/

namespace L4YAML.Scanner

open L4YAML
open L4YAML.CharPredicates

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
    and 1024 characters in block context.

    **Note (Initiative 3 / J.1)**: this structure is being phased out in
    favour of `PendingKeyEntry` + the `pendingKeys` side-channel.  It is
    retained here so existing scanner submodules continue to build during
    the J.1 → J.2 migration window; submodule call sites flip over
    individually in J.2. -/
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

/-! ### Pending-key side channel (Initiative 3 / Path C)

The append-only token stream architecture moves *implicit-key reservations*
out of the `tokens` array (where `setIfInBounds` retroactively rewrote
placeholder slots into `.blockMappingStart` / `.key`) and into a parallel
`pendingKeys : Array PendingKeyEntry` side-channel.  Strict append-only
semantics on both arrays make filter-monotonicity trivial by construction —
see `Blueprint/07-initiative-3-append-only.md`.

These types are defined in J.1; the scanner call sites that produce them
land in J.2; the proof corpus is re-discharged in J.3. -/

/-- Resolution kind of a pending implicit-key reservation.

    Determined at *resolution* time (when `:` confirms the key) — not at
    *save* time — because indentation may change between the two events.
    Linearisation expands `blockMappingStartAndKey` into the two-token
    sequence the parser expects. -/
inductive ResolutionKind where
  /-- Reservation is not (yet) confirmed by a following `:`.  Linearisation
      drops these — they are virtual until resolved. -/
  | unresolved
  /-- Confirmed by `:`; linearisation splices a single `.key` token.
      Used in flow context, and in block context when
      `keyCol ≤ currentIndent` (no new mapping is opened). -/
  | keyOnly
  /-- Confirmed by `:` in block context with `keyCol > currentIndent`.
      Linearisation splices `.blockMappingStart` followed by `.key`,
      matching the current scanner's two-slot placeholder rewrite. -/
  | blockMappingStartAndKey
deriving Repr, BEq, Inhabited

/-- One pending implicit-key reservation in the append-only model.

    Recorded by `saveSimpleKey` at the position of a candidate plain/flow
    scalar; later either resolved by `scanValuePrepare` (kind flips from
    `unresolved` to `keyOnly` / `blockMappingStartAndKey`) or left
    `unresolved` and dropped at linearisation.

    `insertBeforeIdx` names the *current* `tokens.size` at save time — i.e.
    the eventual array index of the candidate scalar in the raw `tokens`
    stream.  Linearisation walks `tokens`, and immediately before emitting
    `tokens[insertBeforeIdx]` it splices the resolved entries.  Save-time
    `tokens.size` values are strictly monotone across successive saves
    (each save is preceded by at least one new token), so the resulting
    `insertBeforeIdx` sequence is strictly monotone — the property the
    linearisation algorithm relies on. -/
structure PendingKeyEntry where
  /-- Index in `tokens` *before* which resolved entries are spliced. -/
  insertBeforeIdx : Nat
  /-- Source position of the candidate key. -/
  pos : YamlPos
  /-- Line on which the candidate key token ended (multi-line quoted
      scalars).  Used to enforce same-line `:` for implicit keys. -/
  endLine : Nat
  /-- Resolution status; flips at most once, from `unresolved` to a
      resolved kind, or stays `unresolved` and is dropped on linearise. -/
  kind : ResolutionKind
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
  /-- Simple key tracking (legacy; being phased out — see `pendingKeys`). -/
  simpleKey : SimpleKeyState := {}
  /-- Stack of saved simple keys for enclosing flow nesting levels.
      Pushed on flow-open (`[`, `{`), popped on flow-close (`]`, `}`).
      This allows a simple key (e.g., a flow mapping used as a key:
      `{a: b}: val`) to survive nested flow collection scanning.
      Legacy; being phased out — see `pendingKeyStack`. -/
  simpleKeyStack : Array SimpleKeyState := #[]
  /-- **Pending implicit-key reservations** (Initiative 3 / Path C).

      Append-only side-channel replacing the in-place placeholder rewrites
      done via `setIfInBounds` in the legacy model.  Each entry records
      where (`insertBeforeIdx`) and how (`kind`) a `.key` (and optionally
      `.blockMappingStart`) token will be spliced into the linearised
      output stream — but only if the entry's kind has been resolved by a
      following `:`.  Unresolved entries are dropped at `scanFiltered`.

      Save-time `insertBeforeIdx` values are strictly monotone across
      successive entries (each save is preceded by at least one newly
      pushed real token), giving the linearisation a clean splice-merge
      shape and making filter-monotonicity hold by construction. -/
  pendingKeys : Array PendingKeyEntry := #[]
  /-- Index into `pendingKeys` of the currently-active reservation, if
      any.  Mirrors the legacy `simpleKey.possible`-bit machinery: at most
      one reservation is the *active candidate* at any given point in
      scanning.  `none` means no reservation is currently in flight. -/
  pendingKeyActive : Option Nat := none
  /-- Stack of saved active-reservation indices, parallel to
      `simpleKeyStack`.  Pushed on flow-open / popped on flow-close so an
      outer reservation survives nested flow scanning. -/
  pendingKeyStack : Array (Option Nat) := #[]
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
  /-- Collected comments (position × text). Comments are stored here as a
      side-channel rather than in the token array so that all existing
      `preserves_tokens` proofs remain valid unchanged. -/
  comments : Array (YamlPos × String) := #[]
  /-- Anchor names defined in the current document (§7.1).
      Pushed by `scanAnchorOrAlias` when `isAnchor = true`.
      Checked by `scanAnchorOrAlias` when `isAnchor = false`.
      Reset on document boundaries (`scanDocumentStart`, `scanDocumentEnd`). -/
  definedAnchors : Array String := #[]
  deriving Repr, Inhabited

/-! ### State Invariants

The following predicate captures the structural invariants that every
well-formed `ScannerState` must satisfy.  Individual operations preserve
these invariants; see `Proofs/ScannerContracts.lean` for proofs.
-/

/-- Structural well-formedness invariant for `ScannerState`.

    These six conjuncts capture the essential invariants that all scanner
    operations must preserve:
    1. **Indent stack non-empty** — the sentinel `{ column := -1 }` is never popped.
    2. **Flow level = flow stack size** — `flowLevel` and `flowStack` stay in sync.
    3. **Simple key stack = flow stack size** — `simpleKeyStack` tracks flow nesting.
    4. **Offset bounded** — the scanner never reads past the input end.
    5. **Indent stack monotonic** — consecutive entries have strictly increasing columns.
    6. **Sentinel preserved** — the bottom entry is always `{ column := -1, isSequence := false }`. -/
def ScannerState.WellFormed (s : ScannerState) : Prop :=
  s.indents.size ≥ 1
  ∧ s.flowLevel = s.flowStack.size
  ∧ s.simpleKeyStack.size = s.flowStack.size
  ∧ s.offset ≤ s.inputEnd
  ∧ (∀ (i : Nat), (hi : i + 1 < s.indents.size) →
      (s.indents[i]'(by omega)).column < (s.indents[i + 1]'hi).column)
  ∧ (∀ (_ : 0 < s.indents.size), s.indents[0] = { column := -1, isSequence := false })

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
    Line breaks (`\n` and `\r`) reset col to 0 and increment line.
    Per YAML spec §5.4 [28], both CR and LF are line terminators. -/
def ScannerState.advance (s : ScannerState) : ScannerState :=
  if s.offset < s.inputEnd then
    let c := String.Pos.Raw.get s.input ⟨s.offset⟩
    let nextPos := String.Pos.Raw.next s.input ⟨s.offset⟩
    if c == '\n' then
      { s with offset := nextPos.byteIdx, line := s.line + 1, col := 0 }
    else if c == '\r' then
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

/-- Whether the scanner is inside a flow collection (`flowLevel > 0`).

    **Implements** (YAML 1.2.2 §7.4): `[136] in-flow(c)` context selector.
    When `flowLevel > 0`, the scanner uses flow-collection rules
    (FLOW-IN context) rather than block-collection rules (FLOW-OUT). -/
@[yaml_spec "7.4" 136 "in-flow(c)"]
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

/-! ### Pending-key resolution helper (Initiative 3 / Path C)

`setPendingKeyKind` resolves the active reservation by writing a new
`ResolutionKind` into the entry pointed at by `pendingKeyActive`.  Kept
as a top-level helper (rather than inlined into `scanValuePrepare`) so
that the J.2 dual-write does not introduce extra `split` levels into the
existing scanner-correctness proof corpus: proofs about `.offset`,
`.input`, `.tokens`, etc. treat the `pendingKeys := setPendingKeyKind …`
field assignment as opaque and discharge by record projection alone. -/
def setPendingKeyKind (pendingKeys : Array PendingKeyEntry)
    (active : Option Nat) (kind : ResolutionKind) : Array PendingKeyEntry :=
  match active with
  | none => pendingKeys
  | some i =>
    match pendingKeys[i]? with
    | none => pendingKeys
    | some e => pendingKeys.setIfInBounds i { e with kind := kind }

end L4YAML.Scanner
