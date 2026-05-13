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
    `n` is the count of spaces consumed. The body uses `.1`/`.2`
    projections rather than `let`-destructure so that `simp` /
    `rfl` reduction goes through cleanly in proofs. -/
def skipSpacesLoop {input : String} (c : IxCursor input) :
    Nat → IxCursor input × Nat
  | 0          => (c, 0)
  | fuel + 1 =>
    if peekIsIndentChar c then
      let r := skipSpacesLoop c.advance fuel
      (r.1, r.2 + 1)
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

/-! ## Layer B' — comment text (§6.6 [75] `c-nb-comment-text`)

Comment scanning is split into two halves:

- `skipCommentTextLoop` (here) — consume the body of a comment
  starting from *after* the `'#'`. The body is `nb-char*`
  ([27] `nb-char ::= c-printable - b-char - c-byte-order-mark`):
  every non-line-break, non-EOF character, with no inner
  validation of `c-printable` (that's a separate spec check, not
  scanning state).

- `skipToContent` (Layer D, below) — composite that consumes
  whitespace, a `'#'`-introduced comment if present, the line
  break, then recurses for the next line.

`skipCommentText` is its own loop because:

1. Its termination condition is *different* from `skipWhitespace`
   (stops at LF/CR, not at non-whitespace).
2. It does not produce a count — the comment text characters
   themselves are uninteresting for indent tracking (comments
   never establish indent).
3. Step 4 may want to capture comment text for round-tripping
   (the legacy scanner has a side-channel `comments` array); the
   capture is bolted onto `skipCommentTextLoop` then. -/

/-- Inner loop: consume characters until a line break (or EOF).
    Structurally recursive on `fuel`. -/
def skipCommentTextLoop {input : String} (c : IxCursor input) :
    Nat → IxCursor input
  | 0          => c
  | fuel + 1 =>
    if peekIsLineBreak c then c
    else
      match c.peek? with
      | none    => c
      | some _  => skipCommentTextLoop c.advance fuel

/-- Consume a comment body (`nb-char*`), stopping at the first
    line-break character or end-of-input. The leading `'#'` must
    already have been consumed by the caller (Layer D / dispatch). -/
@[inline] def skipCommentText {input : String} (c : IxCursor input) : IxCursor input :=
  skipCommentTextLoop c input.utf8ByteSize

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

/-! ## Layer D — composite line-comment dispatch
    (§6.6 [77] `s-b-comment`, §6.7 [79] `s-l-comments`)

`skipToContent` consumes the *between-token* whitespace:

1. `s-white*` — spaces and tabs (separation, not indentation).
2. An optional `'#'` comment to end-of-line.
3. A line break — if present, recurse on the next line.

Stops at the first character that is *content* (not whitespace,
not a comment, not a line break) or at end-of-input.

This matches the legacy `Scanner/Whitespace.lean::skipToContent`
*structurally* but without:

- The `needIndentCheck` flag (Step 3's indent-stack approach
  handles indent measurement explicitly, not via a flag).
- Tab-as-indentation error reporting (§6.1 tab error checks
  belong with the indent-stack at Step 4, where the current
  block's indent is known).
- The simple-key reset (a parser-layer concern; not in the
  scanner's character/line layer).

`skipToContent` therefore behaves correctly only as a *neutral*
consumer of skippable content — error reporting and simple-key
handling are layered on top in Step 4. -/

/-- Inner loop. Structurally recursive on `fuel`. The body is
    written without `let`-bindings (each call to `skipWhitespace c`
    is duplicated) so that `split` can decompose the `match` in
    proofs — Lean's elaborator opacifies `let`-bound expressions
    against the `split` tactic. -/
def skipToContentLoop {input : String} (c : IxCursor input) :
    Nat → IxCursor input
  | 0          => c
  | fuel + 1 =>
    -- After skipWhitespace, peek? is none, a line break, '#', or content.
    match (skipWhitespace c).peek? with
    | none    => skipWhitespace c
    | some ch =>
      if ch == '#' then
        skipToContentLoop
          (consumeLineBreak (skipCommentText (skipWhitespace c).advance)) fuel
      else if isLineBreakBool ch then
        skipToContentLoop (consumeLineBreak (skipWhitespace c)) fuel
      else
        skipWhitespace c

/-- Consume skippable inter-token content: whitespace, comments,
    and line breaks. Stops at the first content character or EOF.

    Matches `s-l-comments` ([79]) semantically; see legacy
    `Scanner/Whitespace.lean::skipToContent` for the error-aware
    counterpart that handles §6.1 tab violations. -/
@[inline] def skipToContent {input : String} (c : IxCursor input) : IxCursor input :=
  skipToContentLoop c (input.utf8ByteSize + 1)

/-! ## Layer E — scalar recognisers (§7.3, single-line subset)

Phase 3 Step 4a scope: quoted scalars (single- and double-) on a
single line, plus a single-line plain scalar. Multi-line folding,
plain scalars spanning multiple lines, and block scalars (literal +
folded) land in Step 4b.

Each quoted recogniser returns `Option (String × IxCursor input)`:
- `some (content, after)` — the matched scalar's resolved content
  and the cursor *after* the closing delimiter.
- `none` — recoverable failure (unterminated quote, invalid escape,
  multi-line content that Step 4a does not handle yet). Error
  reporting is layered on top in Step 5; the staging recognisers
  signal *failure* but do not classify *which* error.

The plain scalar recogniser is total (always returns) because plain
scalars terminate by *not finding* a continuation character; the
empty plain scalar is `("", c)` which is a valid (degenerate) match.

### Layer E1 — escape sequences (§5.7, single-char + hex)

`processEscapeIx` handles the 18 single-character escapes (`\0`, `\a`,
`\b`, `\t`, `\n`, `\v`, `\f`, `\r`, `\e`, `\ `, `\"`, `\/`, `\\`,
`\N`, `\_`, `\L`, `\P`, `\TAB`) and the three hex escapes (`\x`,
`\u`, `\U` with 2/4/8 hex digits). The cursor must already be
positioned *after* the leading `\`. -/

/-- Whether `c` is an ASCII hex digit (`0..9`, `a..f`, `A..F`). -/
@[inline] def isHexDigitBool (c : Char) : Bool :=
  c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

/-- Collect `n` hex digits from the cursor. Returns the digit string
    and the post-collection cursor. Stops early on non-hex or EOF —
    the caller checks the returned string's length against `n`. -/
def collectHexDigitsLoopIx {input : String} (c : IxCursor input)
    (hex : String) : Nat → String × IxCursor input
  | 0      => (hex, c)
  | n' + 1 =>
    match c.peek? with
    | some ch =>
      if isHexDigitBool ch then
        collectHexDigitsLoopIx c.advance (hex.push ch) n'
      else (hex, c)
    | none    => (hex, c)

/-- Hex-digit value, decoded under the assumption that the character
    is in `0..9 | a..f | A..F`. For non-hex inputs the result is
    undefined (in practice the caller has already filtered via
    `isHexDigitBool`). -/
@[inline] def hexDigitValue (ch : Char) : Nat :=
  if ch.isDigit then ch.toNat - '0'.toNat
  else if ch >= 'a' then ch.toNat - 'a'.toNat + 10
  else ch.toNat - 'A'.toNat + 10

/-- Fold a hex-digit string to its `Nat` value. Standalone so the
    `let val := ...` does not appear inside the `parseHexEscapeIx`
    body, where it would obstruct `split` in proofs (Reflection 37). -/
@[inline] def hexStringValue (hex : String) : Nat :=
  hex.foldl (fun acc ch => acc * 16 + hexDigitValue ch) 0

/-- Parse `n` hex digits and decode to a `Char`. Returns `none` if
    fewer than `n` digits are available or the value is ≥ 0x110000
    (outside the Unicode scalar range). -/
def parseHexEscapeIx {input : String} (c : IxCursor input) (n : Nat) :
    Option (Char × IxCursor input) :=
  if (collectHexDigitsLoopIx c "" n).1.length != n then
    none
  else if hexStringValue (collectHexDigitsLoopIx c "" n).1 < 0x110000 then
    some (Char.ofNat (hexStringValue (collectHexDigitsLoopIx c "" n).1),
          (collectHexDigitsLoopIx c "" n).2)
  else
    none

/-- The 18 single-character escapes of §5.7. `none` means the
    character is not a simple-escape indicator (could still be `'x'`,
    `'u'`, `'U'`, or unknown — `processEscapeIx` dispatches further). -/
def simpleEscapeChar (ch : Char) : Option Char :=
  if ch == '0'       then some '\x00'
  else if ch == 'a'  then some '\x07'
  else if ch == 'b'  then some '\x08'
  else if ch == 't'  then some '\t'
  else if ch == '\t' then some '\t'
  else if ch == 'n'  then some '\n'
  else if ch == 'v'  then some '\x0B'
  else if ch == 'f'  then some '\x0C'
  else if ch == 'r'  then some '\r'
  else if ch == 'e'  then some '\x1B'
  else if ch == ' '  then some ' '
  else if ch == '"'  then some '"'
  else if ch == '/'  then some '/'
  else if ch == '\\' then some '\\'
  else if ch == 'N'  then some '\x85'
  else if ch == '_'  then some '\xA0'
  else if ch == 'L'  then some (Char.ofNat 0x2028)
  else if ch == 'P'  then some (Char.ofNat 0x2029)
  else none

/-- Process a single escape sequence. Cursor is positioned at the
    character *after* the leading `\`. Returns the decoded character
    and the post-escape cursor, or `none` for unknown / malformed
    escapes (incl. EOF after the `\`). The split between
    `simpleEscapeChar` and the hex dispatch keeps the proof obligation
    tractable: monotonicity reduces to three branches at top level
    (simple → `c.advance`, hex → `parseHexEscapeIx`, unknown → `none`)
    rather than 21 sequentially-nested `if`s. -/
def processEscapeIx {input : String} (c : IxCursor input) :
    Option (Char × IxCursor input) :=
  match c.peek? with
  | none    => none
  | some ch =>
    match simpleEscapeChar ch with
    | some decoded => some (decoded, c.advance)
    | none =>
      if ch == 'x' then parseHexEscapeIx c.advance 2
      else if ch == 'u' then parseHexEscapeIx c.advance 4
      else if ch == 'U' then parseHexEscapeIx c.advance 8
      else none

/-! ### Layer E2 — double-quoted scalar (§7.3.1, single-line)

`collectDoubleQuotedLoopIx` consumes the body of a double-quoted
scalar starting from *after* the opening `"`. Stops at:
- `'"'`: closing quote — return content + cursor past the quote
- `'\\'`: escape — recurse with `processEscapeIx`'s result
- EOF or unhandled line break: `none` (Step 4a defers multi-line). -/

def collectDoubleQuotedLoopIx {input : String} (c : IxCursor input)
    (content : String) : Nat → Option (String × IxCursor input)
  | 0          => none
  | fuel + 1 =>
    match c.peek? with
    | none       => none
    | some '"'   => some (content, c.advance)
    | some '\\'  =>
      match processEscapeIx c.advance with
      | some (ch, cAfterEsc) =>
        collectDoubleQuotedLoopIx cAfterEsc (content.push ch) fuel
      | none => none
    | some ch    =>
      if isLineBreakBool ch then
        none
      else
        collectDoubleQuotedLoopIx c.advance (content.push ch) fuel

/-- Scan a single-line double-quoted scalar. Cursor must be at the
    opening `"`. -/
def scanDoubleQuotedIx {input : String} (c : IxCursor input) :
    Option (String × IxCursor input) :=
  match c.peek? with
  | some '"' =>
    collectDoubleQuotedLoopIx c.advance "" input.utf8ByteSize
  | _ => none

/-! ### Layer E3 — single-quoted scalar (§7.3.2, single-line)

`collectSingleQuotedLoopIx` consumes the body of a single-quoted
scalar starting from *after* the opening `'`. Stops at:
- `'\''` not followed by `'\''`: closing quote
- `'\''` followed by `'\''`: doubled-quote escape — emit one `'`
- EOF or unhandled line break: `none`. -/

def collectSingleQuotedLoopIx {input : String} (c : IxCursor input)
    (content : String) : Nat → Option (String × IxCursor input)
  | 0          => none
  | fuel + 1 =>
    match c.peek? with
    | none      => none
    | some '\'' =>
      match c.advance.peek? with
      | some '\'' =>
        collectSingleQuotedLoopIx c.advance.advance (content.push '\'') fuel
      | _ =>
        some (content, c.advance)
    | some ch    =>
      if isLineBreakBool ch then
        none
      else
        collectSingleQuotedLoopIx c.advance (content.push ch) fuel

/-- Scan a single-line single-quoted scalar. -/
def scanSingleQuotedIx {input : String} (c : IxCursor input) :
    Option (String × IxCursor input) :=
  match c.peek? with
  | some '\'' =>
    collectSingleQuotedLoopIx c.advance "" input.utf8ByteSize
  | _ => none

/-! ### Layer E4 — plain scalar (§7.3.3, single-line)

`collectPlainScalarLoopIx` consumes a single-line plain scalar starting
at a character satisfying `canStartPlainScalarBool`. The scalar
terminates at end-of-input, a line break (multi-line deferred to
Step 4b), `' #'`, `: ` / `:EOF` (block), or a flow indicator (flow).
Trailing whitespace is trimmed by the entry point `scanPlainScalarIx`. -/

/-- Trim trailing space/tab from a string. -/
def trimTrailingWSIx (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse)

/-- Helper: whether `:` at the cursor terminates a plain scalar
    (peeks one past the colon and applies the `inFlow` rule). -/
@[inline] def colonTerminatesPlain {input : String} (c : IxCursor input)
    (inFlow : Bool) : Bool :=
  match c.peekAt? 1 with
  | some n => isBlankBool n || (inFlow && isFlowIndicatorBool n)
  | none   => true

def collectPlainScalarLoopIx {input : String} (c : IxCursor input)
    (content : String) (spaces : String) (inFlow : Bool) :
    Nat → String × IxCursor input
  | 0          => (content ++ spaces, c)
  | fuel + 1 =>
    match c.peek? with
    | none    => (content ++ spaces, c)
    | some ch =>
      if ch == '#' && spaces.length > 0 then
        (content, c)
      else if ch == ':' && colonTerminatesPlain c inFlow then
        (content, c)
      else if ch == ':' then
        collectPlainScalarLoopIx c.advance
          (content ++ spaces ++ String.singleton ch) "" inFlow fuel
      else if inFlow && isFlowIndicatorBool ch then
        (content, c)
      else if isLineBreakBool ch then
        (content, c)
      else if isWhiteSpaceBool ch then
        collectPlainScalarLoopIx c.advance content (spaces.push ch) inFlow fuel
      else if !isPlainSafeBool ch inFlow then
        (content, c)
      else
        collectPlainScalarLoopIx c.advance
          (content ++ spaces ++ String.singleton ch) "" inFlow fuel

/-- Scan a single-line plain scalar starting at the cursor's current
    character. The caller is responsible for enforcing the
    `canStartPlainScalarBool` precondition at dispatch. -/
def scanPlainScalarIx {input : String} (c : IxCursor input) (inFlow : Bool) :
    String × IxCursor input :=
  let (raw, c') := collectPlainScalarLoopIx c "" "" inFlow input.utf8ByteSize
  (trimTrailingWSIx raw, c')

end L4YAML.Scanner.Indexed
