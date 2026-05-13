/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Indexed.CharStream
import L4YAML.Spec.CharPredicates

/-! # `IndexedScanner` — Phase 3 character/whitespace layer (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6). The legacy `L4YAML/Scanner/*.lean`
remains the production scanner for the duration of Phase 3 Steps 2–5.

## What this layer provides

The lowest-level recognisers over `IxCursor input`:

- **Layer A — character-class peeks**: `peekIsLineBreak`,
  `peekIsWhiteSpace`, `peekIsBlank`, `peekIsIndentChar` — each
  inspects the current character (if any) against a YAML 1.2.2
  character class from `Spec.CharPredicates`.

- **Layer B — whitespace runs**: `skipSpaces` (consume `s-space*`,
  returning the count for indent tracking) and `skipWhitespace`
  (consume `s-white*` = spaces + tabs, for `[66] s-separate-in-line`).

- **Layer C — line break**: `consumeLineBreak` advances past one
  `[28] b-break`, with the CRLF special case folded to a single line
  increment (matching legacy `ScannerState.consumeNewline`).

Whitespace and line breaks are *consumed*, not emitted as tokens
(matches the legacy convention: `YamlToken` has no whitespace
constructor; indentation changes produce *virtual* `blockEnd` /
`blockSequenceStart` / `blockMappingStart` tokens at higher layers).

## Termination

`skipSpaces` / `skipWhitespace` recurse on a `Nat` fuel parameter.
The entry points pass `input.utf8ByteSize` — a safe upper bound,
since each loop step that advances strictly increases the cursor
offset (`advance_offset_lt_of_hasMore` from `Indexed.CharStream`).
Termination correctness — that the cursor ends at a non-whitespace
or at end-of-input — is proven in
`L4YAML/Proofs/Scanner/IndexedWhitespace.lean`.
-/

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.CharPredicates L4YAML.Indexed

/-! ## Layer A — character-class peeks

Each `peekIs*` returns `true` exactly when the cursor's current
character is in the corresponding YAML 1.2.2 class. At end-of-input
all return `false` (no character to inspect). -/

/-- Cursor points at a §5.4 line-break character (`'\n'` or `'\r'`). -/
@[inline] def peekIsLineBreak {input : String} (c : IxCursor input) : Bool :=
  match c.peek? with
  | some ch => isLineBreakBool ch
  | none    => false

/-- Cursor points at a §5.5 whitespace character (space or tab). -/
@[inline] def peekIsWhiteSpace {input : String} (c : IxCursor input) : Bool :=
  match c.peek? with
  | some ch => isWhiteSpaceBool ch
  | none    => false

/-- Cursor points at a blank: whitespace or line break. -/
@[inline] def peekIsBlank {input : String} (c : IxCursor input) : Bool :=
  match c.peek? with
  | some ch => isBlankBool ch
  | none    => false

/-- Cursor points at a §6.1 indent character (space only — tabs are
    *not* indent characters per §6.1). -/
@[inline] def peekIsIndentChar {input : String} (c : IxCursor input) : Bool :=
  match c.peek? with
  | some ch => isIndentCharBool ch
  | none    => false

/-! ## Layer B — whitespace runs -/

/-- Inner loop for `skipSpaces`. Structurally recursive on `fuel`.
    Returns `(c', n)` where `c'` is the cursor after the run and
    `n` is the count of spaces consumed. -/
def skipSpacesLoop {input : String} (c : IxCursor input) :
    Nat → IxCursor input × Nat
  | 0          => (c, 0)
  | fuel + 1 =>
    if peekIsIndentChar c then
      let (c', n) := skipSpacesLoop c.advance fuel
      (c', n + 1)
    else
      (c, 0)

/-- Consume a maximal run of `s-space` characters (§6.1 indentation).
    Tabs are *not* consumed — they remain at the cursor. Returns the
    post-run cursor and the number of spaces consumed (Step 3's
    indent-tracking will use the count). -/
@[inline] def skipSpaces {input : String} (c : IxCursor input) :
    IxCursor input × Nat :=
  skipSpacesLoop c input.utf8ByteSize

/-- Inner loop for `skipWhitespace`. -/
def skipWhitespaceLoop {input : String} (c : IxCursor input) :
    Nat → IxCursor input
  | 0          => c
  | fuel + 1 =>
    if peekIsWhiteSpace c then
      skipWhitespaceLoop c.advance fuel
    else
      c

/-- Consume a maximal run of `s-white` characters (spaces *and* tabs,
    [66] s-separate-in-line). Used in flow context and after key/value
    indicators where tabs are permitted. -/
@[inline] def skipWhitespace {input : String} (c : IxCursor input) :
    IxCursor input :=
  skipWhitespaceLoop c input.utf8ByteSize

/-! ## Layer C — line-break consumption -/

/-- Consume one `[28] b-break`. Three cases:

    - LF (`'\n'`): single `advance`.
    - CR (`'\r'`) not followed by LF: single `advance`.
    - CRLF (`'\r' '\n'`): two `advance`s, but only one logical line
      bump. `IxCursor.advance` already increments `line` on `'\r'`;
      advancing the `'\n'` would bump again, so we override the line
      counter to keep the post-CRLF line equal to the post-CR line.

    At any non-break character (including end-of-input) the cursor is
    returned unchanged. Matches legacy `ScannerState.consumeNewline`.

    We use `if/else` rather than Char-literal patterns in the match
    to keep the proof obligations decidable on `Char` equality. -/
def consumeLineBreak {input : String} (c : IxCursor input) : IxCursor input :=
  match c.peek? with
  | none    => c
  | some ch =>
    if ch == '\n' then
      c.advance
    else if ch == '\r' then
      if c.peekAt? 1 == some '\n' then
        let cAfterCR := c.advance
        let cAfterLF := cAfterCR.advance
        { pos := { offset := cAfterLF.pos.offset
                   line   := cAfterCR.pos.line
                   col    := 0 }
          posBound := cAfterLF.posBound }
      else
        c.advance
    else
      c

end L4YAML.Scanner.Indexed
