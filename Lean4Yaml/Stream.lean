/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Parser
import Lean4Yaml.Types

/-!
# YAML Parser Stream

A position-aware character stream for YAML parsing, built on lean4-parser's
`Parser.Stream` type class.

## Design Rationale

The key insight that motivates this module is that YAML parsing bugs (like the
`skipToNextLine` regression in lean4-yaml) arise from **implicit position state**.
By encoding line, column, and line-state information directly in the stream's
`Position` type, we make it impossible to confuse:

- Trailing whitespace on the current line
- Leading indentation on the next line
- Mid-content position after a value

The `Parser.Stream` type class from lean4-parser requires only:
- `Position`: a lightweight type for saving/restoring state
- `getPosition`: extract position from stream
- `setPosition`: restore stream to a saved position
- `next?`: read one token and advance

Our stream tracks `(offset, line, col)` in the position, which means every
parser combinator automatically maintains line/column information without
any manual `peekColumn` or `getColumn` hacks.

## YAML-Specific Invariants

YAML 1.2.2 §6.1 (https://yaml.org/spec/1.2.2/#61-indentation-spaces):
"In YAML block styles, structure is determined by indentation."

Our stream makes this first-class:
- `col` always reflects the true column (0-based) after consuming a character
- Newlines reset `col` to 0 and increment `line`
- No separate "count spaces" function needed — just read `col` from position
-/

namespace Lean4Yaml

/-! ## Stream Types -/

/--
Position in a YAML stream.

Tracks byte offset (for efficient save/restore), line number, and column number.
Line and column are 0-based to match YAML spec conventions.
-/
structure YamlPos where
  /-- Byte offset into the source string -/
  offset : Nat
  /-- Current line number (0-based) -/
  line : Nat
  /-- Current column number (0-based) -/
  col : Nat
  deriving Repr, BEq, Inhabited, Hashable, DecidableEq

instance : Ord YamlPos where
  compare a b := compare a.offset b.offset

instance : LT YamlPos where
  lt a b := a.offset < b.offset

instance : LE YamlPos where
  le a b := a.offset ≤ b.offset

/--
A YAML character stream with automatic line/column tracking.

Wraps a `Substring.Raw` (the lean4-parser standard for string parsing)
with additional line/column state.
-/
structure YamlStream where
  /-- The underlying string data -/
  str : String
  /-- Current start position (byte offset) -/
  startPos : String.Pos.Raw
  /-- End position (byte offset), exclusive -/
  stopPos : String.Pos.Raw
  /-- Current line number (0-based) -/
  line : Nat
  /-- Current column number (0-based) -/
  col : Nat
  /-- Anchor name → resolved YamlValue map.
      Stored in the stream so it accumulates through parsing
      without being rolled back by `setPosition` (which only
      restores offset/line/col).  §6.9.2 / §7.1.

      Uses the `AnchorMap` abstraction from Types.lean, whose
      algebraic laws (`find?_insert`, `find?_insert_ne`, `find?_empty`)
      are the foundation for alias-resolution proofs. -/
  anchorMap : AnchorMap := AnchorMap.empty
  /-- Validation error detected during parsing.

      This is the **backtracking-safe** channel for fatal error reporting.
      Unlike `throwUnexpected` (which lean4-parser's `<|>`, `option?`, and
      `first` catch unconditionally), validation errors are stored in the
      stream state and survive position restore — exactly like `anchorMap`.

      **Assume/Guarantee contract**:
      - **Assume**: `validationError = none` at document start
        (enforced by `clearValidationError` in `document`).
      - **Guarantee**: if `validationError = some msg` after parsing,
        the input at that point was structurally invalid YAML.
      - **Invariant**: `setPosition` preserves `validationError`
        (proved by `setPosition_preserves_validationError`).

      First error wins: once set, subsequent `setValidationError` calls
      are no-ops. This captures the root cause, not downstream symptoms. -/
  validationError : Option String := none
  /-- Tag handles defined for the current document context.

      §6.8.2: Tag shorthand handles are scoped to the document where they
      are declared via `%TAG` directives.  The default handles `!` and `!!`
      are always available (§6.8.2.2, §6.8.2.3).

      Reset per document in `yamlStream` before calling `document`.
      Survives `setPosition` (only offset/line/col are restored). -/
  tagHandles : Array String := #["!", "!!"]
  deriving Repr

/-! ## Stream Instance -/

/--
Convert a raw string into a `YamlStream` starting at position 0.
-/
def YamlStream.ofString (s : String) : YamlStream where
  str := s
  startPos := ⟨0⟩
  stopPos := s.rawEndPos
  line := 0
  col := 0

/--
Check if the stream has more input.
-/
def YamlStream.hasNext (s : YamlStream) : Bool :=
  s.startPos < s.stopPos

/--
Read the next character and advance the stream.
Returns `none` if at end of input.
-/
def YamlStream.next? (s : YamlStream) : Option (Char × YamlStream) :=
  if s.startPos < s.stopPos then
    let c := String.Pos.Raw.get s.str s.startPos
    let nextPos := String.Pos.Raw.next s.str s.startPos
    let (newLine, newCol) :=
      if c == '\n' then (s.line + 1, 0)
      else (s.line, s.col + 1)
    some (c, { s with
      startPos := nextPos
      line := newLine
      col := newCol
    })
  else
    none

/-- Peek at the current character without consuming it. -/
def YamlStream.peek? (s : YamlStream) : Option Char :=
  if s.startPos < s.stopPos then
    some (String.Pos.Raw.get s.str s.startPos)
  else
    none

/-- Get the current position as a `YamlPos`. -/
def YamlStream.getPos (s : YamlStream) : YamlPos where
  offset := s.startPos.byteIdx
  line := s.line
  col := s.col

/-- Get remaining input as a string (for debugging). -/
def YamlStream.remaining (s : YamlStream) : String :=
  String.Pos.Raw.extract s.str s.startPos s.stopPos

/-! ## Parser.Stream Instance -/

/--
`Std.Stream` instance for `YamlStream`.

This makes `YamlStream` usable with the standard stream typeclass,
providing the `next?` method.
-/
instance : Std.Stream YamlStream Char where
  next? := YamlStream.next?

/--
`Parser.Stream` instance for `YamlStream`.

This is the key integration with lean4-parser. By using `YamlPos` as the
position type, every save/restore operation in backtracking preserves
line/column information automatically.

The position includes byte offset for O(1) restore, plus line/col for
O(1) position queries. Restore reconstructs the stream state from the
saved position by scanning for the correct line/col (which could be
optimized, but correctness is prioritized first).
-/
instance : Parser.Stream YamlStream Char where
  Position := YamlPos
  getPosition s := s.getPos
  setPosition s p :=
    -- Restore to saved position. Since we have the byte offset,
    -- we can restore the stream state directly.
    -- Note: `anchorMap` is NOT in `YamlPos`, so it is preserved.
    -- This is the backtracking-isolation invariant.
    { s with
      startPos := ⟨p.offset⟩
      line := p.line
      col := p.col }
  remaining s := s.stopPos.byteIdx - s.startPos.byteIdx

/-! ## Backtracking Isolation

The anchor map survives position-based backtracking because
`setPosition` only restores `startPos`, `line`, `col` — it
does NOT touch `anchorMap`. This means:

- `option?`, `lookAhead`, `<|>`, `first`, and all lean4-parser
  combinators that save/restore position preserve the anchor map.
- An anchor defined inside a failed parse branch remains available.
- This matches YAML semantics: anchors accumulate over a document.

The following theorems make this invariant machine-checkable.
-/

/-- **Backtracking isolation**: `setPosition` preserves the anchor map.
    This is the central correctness invariant for anchor/alias
    interaction with parser backtracking. -/
theorem setPosition_preserves_anchorMap (s : YamlStream) (p : YamlPos) :
    (Parser.Stream.setPosition s p).anchorMap = s.anchorMap := by
  rfl

/-- **`next?` preservation**: reading a character preserves the anchor map. -/
theorem next_preserves_anchorMap (s : YamlStream) (c : Char) (s' : YamlStream)
    (h : s.next? = some (c, s')) :
    s'.anchorMap = s.anchorMap := by
  simp only [YamlStream.next?] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ rfl
  · exact absurd h (by simp)

/-- **Backtracking isolation**: `setPosition` preserves validation errors.
    Together with `setPosition_preserves_anchorMap`, this proves that
    ALL stream-level state (anchor map + validation error) is orthogonal
    to position state. -/
theorem setPosition_preserves_validationError (s : YamlStream) (p : YamlPos) :
    (Parser.Stream.setPosition s p).validationError = s.validationError := by
  rfl

/-- **`next?` preservation**: reading a character preserves validation errors. -/
theorem next_preserves_validationError (s : YamlStream) (c : Char) (s' : YamlStream)
    (h : s.next? = some (c, s')) :
    s'.validationError = s.validationError := by
  simp only [YamlStream.next?] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ rfl
  · exact absurd h (by simp)

/-! ## YAML-Specific Position Utilities -/

/--
The current column in the stream.

This is a pure function on the stream state — no parsing, no side effects,
no consuming input. This is what makes verified indentation tracking possible.
-/
def YamlStream.column (s : YamlStream) : Nat := s.col

/--
The current line in the stream.
-/
def YamlStream.lineNum (s : YamlStream) : Nat := s.line

/-! ## Parser Type Abbreviations -/

/--
The YAML parser error type.

Uses lean4-parser's `Simple` error type which records position and error messages.
-/
abbrev YamlError := Parser.Error.Simple YamlStream Char

/--
The core YAML parser monad.

`YamlParser α` parses characters from a `YamlStream` producing a value of type `α`,
with `YamlError` for error reporting.

This is a pure function `YamlStream → Parser.Result YamlError YamlStream α`,
which means:
- No hidden state (everything is in `YamlStream`)
- Deterministic (same input → same output)
- Amenable to equational reasoning and proofs
-/
abbrev YamlParser := Parser YamlError YamlStream Char

/-! ## Basic Position Combinators -/

/--
Get the current column without consuming any input.

This replaces both `getColumn` (which consumed spaces) and `peekColumn`
(which saved/restored the iterator) from lean4-yaml. Here, column is
simply a property of the stream position.
-/
def currentCol : YamlParser Nat := do
  let pos ← Parser.getPosition
  return pos.col

/--
Get the current line without consuming any input.
-/
def currentLine : YamlParser Nat := do
  let pos ← Parser.getPosition
  return pos.line

/--
Get the full current position without consuming any input.
-/
def currentPos : YamlParser YamlPos :=
  Parser.getPosition

/-! ## Validation Error Combinators

The validation error mechanism provides a **backtracking-safe** channel
for fatal error reporting.  Unlike `throwUnexpected` (which lean4-parser's
`<|>`, `option?`, and `first` catch unconditionally), validation errors
are stored in the stream state and survive position restore.

This is the central mechanism for P1 strict validation — it enables
the parser to reject structurally invalid YAML even when the error
is detected inside a backtracking context.

Design follows the same pattern as `anchorMap`:
- Stored in `YamlStream`, not in `YamlPos`
- `setPosition` preserves it (proved by `setPosition_preserves_validationError`)
- `next?` preserves it (proved by `next_preserves_validationError`)
-/

/--
Set a validation error in the stream.  First error wins:
subsequent calls are no-ops if an error is already set.

**Pre-condition**: none (safe to call at any point).
**Post-condition**: `stream'.validationError ≠ none`.
-/
def setValidationError (msg : String) : YamlParser Unit := do
  let s ← Parser.getStream
  if s.validationError.isNone then
    Parser.setStream { s with validationError := some msg }

/--
Read the current validation error (if any).

**Contract**: pure read — does not consume input or modify state.
-/
def getValidationError : YamlParser (Option String) := do
  let s ← Parser.getStream
  return s.validationError

/--
Clear the validation error.  Used at document boundaries so that
each document starts with a clean validation state.

**Post-condition**: `stream'.validationError = none`.
-/
def clearValidationError : YamlParser Unit := do
  let s ← Parser.getStream
  Parser.setStream { s with validationError := none }

/-! ## Tag Handle Registry -/

/--
Set the tag handles for the current document context.

Called at the start of each document after parsing `%TAG` directives.
Includes the default handles `!` and `!!` plus any custom handles.
-/
def setTagHandles (handles : Array String) : YamlParser Unit := do
  let s ← Parser.getStream
  Parser.setStream { s with tagHandles := handles }

/--
Check if a tag handle is defined in the current document context.

Returns `true` if the handle is in the tag handle registry.
-/
def isTagHandleDefined (handle : String) : YamlParser Bool := do
  let s ← Parser.getStream
  return s.tagHandles.contains handle

end Lean4Yaml
