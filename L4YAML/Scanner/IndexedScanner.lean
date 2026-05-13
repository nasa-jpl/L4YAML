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

/-- Trim trailing space/tab from a string. -/
def trimTrailingWSIx (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse)

/-! ### Layer F1 — multi-line quoted scalar folding helpers

`foldQuotedNewlinesIx` is the line-fold step shared by double- and
single-quoted scalars when they span multiple lines (§6.5 [73] /
[74]). Given a cursor sitting at a line break, it:

1. Consumes the break.
2. Counts consecutive *blank* lines (whitespace + LF runs).
3. Skips leading whitespace on the next non-blank line.

Returns the **folded replacement** (`" "` for a single break,
`"\n"*emptyCount` for two or more) and the post-fold cursor. Error
reporting (tab in indentation §6.1) is deferred to the dispatcher
in line with Step 3's neutrality. -/

/-- Inner loop: count consecutive blank lines, advancing the cursor
    past each `s-space* b-break` run. Returns `(c', emptyCount)`.
    Structural recursion on `fuel`. The `(skipSpaces c).1` projection
    is duplicated rather than `let`-bound; binding would obstruct
    `split` in the monotonicity proof (Reflection 40 / 37). -/
def skipBlankLinesLoopIx {input : String} (c : IxCursor input)
    (emptyCount : Nat) : Nat → IxCursor input × Nat
  | 0          => (c, emptyCount)
  | fuel + 1 =>
    -- After skipSpaces, the cursor sits at LF / non-blank / EOF.
    match (skipSpaces c).1.peek? with
    | some ch =>
      if isLineBreakBool ch then
        skipBlankLinesLoopIx (consumeLineBreak (skipSpaces c).1) (emptyCount + 1) fuel
      else
        -- Hit content: yield the cursor *before* the blank-line
        -- whitespace was consumed (the caller's `skipSpaces` handles
        -- the continuation line's leading spaces explicitly).
        (c, emptyCount)
    | none    => (c, emptyCount)

/-- Fold a single quoted-scalar line break per §6.5. Cursor must be
    at the line-break character (caller has detected it). Returns
    `(folded, c')`:
    - `folded = " "` if exactly one line break with no intervening
      blank lines (`b-as-space` [70]).
    - `folded = String.ofList (List.replicate n '\n')` for `n ≥ 1`
      blank lines (`b-l-trimmed(n,c)` [69]). -/
def foldQuotedNewlinesIx {input : String} (c : IxCursor input) :
    String × IxCursor input :=
  -- Use `.1`/`.2` projections rather than `let`-destructure on the
  -- blank-line counter; the `let` would opacify proofs that try to
  -- `split` on the inner conditional (Reflection 40 / 37).
  if (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2 > 0 then
    (String.ofList
       (List.replicate
         (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2
         '\n'),
     skipWhitespace
       (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1)
  else
    (" ",
     skipWhitespace
       (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1)

/-! ### Layer E2 — double-quoted scalar (§7.3.1)

`collectDoubleQuotedLoopIx` consumes the body of a double-quoted
scalar starting from *after* the opening `"`. Stops at:
- `'"'`: closing quote — return content + cursor past the quote
- `'\\'` then line break: line-continuation escape — consume LF and
  leading whitespace, emit no character
- `'\\'` otherwise: escape — recurse with `processEscapeIx`'s result
- line break: fold per `foldQuotedNewlinesIx` (Layer F1), trim
  trailing whitespace of the current content, append the folded
  string, continue
- EOF: `none`. -/

def collectDoubleQuotedLoopIx {input : String} (c : IxCursor input)
    (content : String) : Nat → Option (String × IxCursor input)
  | 0          => none
  | fuel + 1 =>
    match c.peek? with
    | none       => none
    | some '"'   => some (content, c.advance)
    | some '\\'  =>
      -- Look at the character after the backslash to decide
      -- between line-continuation escape and normal escape.
      match c.advance.peek? with
      | some lbCh =>
        if isLineBreakBool lbCh then
          -- `\\<LF>` line-continuation: consume newline + leading WS,
          -- emit no character.
          collectDoubleQuotedLoopIx
            (skipWhitespace (consumeLineBreak c.advance)) content fuel
        else
          match processEscapeIx c.advance with
          | some (ch, cAfterEsc) =>
            collectDoubleQuotedLoopIx cAfterEsc (content.push ch) fuel
          | none => none
      | none => none
    | some ch    =>
      if isLineBreakBool ch then
        -- Multi-line continuation: trim trailing WS, fold the break.
        -- We use `.1`/`.2` projections rather than `let`-destructuring
        -- on the fold result; the `let` would be hoisted to `have`
        -- by elaboration and opacify the body to `split` in proofs
        -- (Reflection 40 / 37).
        collectDoubleQuotedLoopIx (foldQuotedNewlinesIx c).2
          (trimTrailingWSIx content ++ (foldQuotedNewlinesIx c).1) fuel
      else
        collectDoubleQuotedLoopIx c.advance (content.push ch) fuel

/-- Scan a double-quoted scalar. Cursor must be at the opening `"`.
    Multi-line folding (§6.5) is handled by
    `collectDoubleQuotedLoopIx`'s line-break branch. -/
def scanDoubleQuotedIx {input : String} (c : IxCursor input) :
    Option (String × IxCursor input) :=
  match c.peek? with
  | some '"' =>
    collectDoubleQuotedLoopIx c.advance "" input.utf8ByteSize
  | _ => none

/-! ### Layer E3 — single-quoted scalar (§7.3.2)

`collectSingleQuotedLoopIx` consumes the body of a single-quoted
scalar starting from *after* the opening `'`. Stops at:
- `'\''` not followed by `'\''`: closing quote
- `'\''` followed by `'\''`: doubled-quote escape — emit one `'`
- line break: fold per §6.5 (multi-line continuation)
- EOF: `none`. -/

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
        collectSingleQuotedLoopIx (foldQuotedNewlinesIx c).2
          (trimTrailingWSIx content ++ (foldQuotedNewlinesIx c).1) fuel
      else
        collectSingleQuotedLoopIx c.advance (content.push ch) fuel

/-- Scan a single-quoted scalar. Cursor must be at the opening `'`. -/
def scanSingleQuotedIx {input : String} (c : IxCursor input) :
    Option (String × IxCursor input) :=
  match c.peek? with
  | some '\'' =>
    collectSingleQuotedLoopIx c.advance "" input.utf8ByteSize
  | _ => none

/-! ### Layer E4 — plain scalar (§7.3.3)

`collectPlainScalarLoopIx` consumes a plain scalar starting at a
character satisfying `canStartPlainScalarBool`. The scalar
terminates at end-of-input, `' #'`, `: ` / `:EOF` (block) or
`:<flow-indicator>` (flow), or a flow indicator (flow). Line breaks
trigger multi-line continuation per Layer F2 below:

- In **flow** context, continuation uses `foldQuotedNewlinesIx`
  (newline → space, blanks → newlines).
- In **block** context, continuation uses `handleBlockLineBreakIx`
  with a `contentIndent` floor and document-boundary termination.

Trailing whitespace is trimmed by the entry point `scanPlainScalarIx`. -/

/-- Helper: whether `:` at the cursor terminates a plain scalar
    (peeks one past the colon and applies the `inFlow` rule). -/
@[inline] def colonTerminatesPlain {input : String} (c : IxCursor input)
    (inFlow : Bool) : Bool :=
  match c.peekAt? 1 with
  | some n => isBlankBool n || (inFlow && isFlowIndicatorBool n)
  | none   => true

/-! ### Layer F2 — document-boundary check + multi-line plain

`atDocumentBoundaryIx` mirrors `Scanner/Document.lean` for `IxCursor`:
returns `true` exactly when the cursor sits at column 0 of a `---`
or `...` marker (followed by blank or EOF). -/

/-- True iff cursor at col 0 is at a `---` document-start marker. -/
@[inline] def atDocumentStartIx {input : String} (c : IxCursor input) : Bool :=
  c.pos.col == 0
  && c.peekAt? 0 == some '-'
  && c.peekAt? 1 == some '-'
  && c.peekAt? 2 == some '-'
  && match c.peekAt? 3 with
     | none   => true
     | some d => isBlankBool d

/-- True iff cursor at col 0 is at a `...` document-end marker. -/
@[inline] def atDocumentEndIx {input : String} (c : IxCursor input) : Bool :=
  c.pos.col == 0
  && c.peekAt? 0 == some '.'
  && c.peekAt? 1 == some '.'
  && c.peekAt? 2 == some '.'
  && match c.peekAt? 3 with
     | none   => true
     | some d => isBlankBool d

/-- True iff cursor is at a document boundary (start or end marker). -/
@[inline] def atDocumentBoundaryIx {input : String} (c : IxCursor input) : Bool :=
  atDocumentStartIx c || atDocumentEndIx c

/-- Block-context line-break handler for plain scalars. Returns
    `none` if the continuation line is under-indented or hits a
    document boundary; otherwise `some (folded, c')` with the
    folded replacement string and the cursor at the continuation
    line's first non-whitespace character. Projections (`.1`/`.2`)
    are duplicated rather than `let`-bound — the `let` would
    obstruct `split` in the monotonicity proof (Reflection 40). -/
def handleBlockLineBreakIx {input : String} (c : IxCursor input)
    (contentIndent : Nat) : Option (String × IxCursor input) :=
  if (skipSpaces
        (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1.pos.col
       < contentIndent then
    none
  else if atDocumentBoundaryIx
            (skipSpaces
              (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1 then
    none
  else
    if (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2 > 0 then
      some (String.ofList
              (List.replicate
                (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2
                '\n'),
            (skipSpaces
              (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1)
    else
      some (" ",
            (skipSpaces
              (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1)

/-- Plain-scalar continuation loop. Adds a `contentIndent` parameter
    (continuation indent floor in block context) and folds line
    breaks into the content string. When folding in either context
    yields an empty continuation (no further non-terminator content),
    the loop terminates at the pre-fold cursor so the caller can
    decide what to do with the partially-collected content. -/
def collectPlainScalarLoopIx {input : String} (c : IxCursor input)
    (content : String) (spaces : String) (inFlow : Bool)
    (contentIndent : Nat) : Nat → String × IxCursor input
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
          (content ++ spaces ++ String.singleton ch) "" inFlow contentIndent fuel
      else if inFlow && isFlowIndicatorBool ch then
        (content, c)
      else if isLineBreakBool ch then
        if inFlow then
          collectPlainScalarLoopIx (foldQuotedNewlinesIx c).2
            (content ++ (foldQuotedNewlinesIx c).1) "" inFlow contentIndent fuel
        else
          match handleBlockLineBreakIx c contentIndent with
          | none => (content, c)
          | some (folded, cAfterFold) =>
            collectPlainScalarLoopIx cAfterFold (content ++ folded) "" inFlow contentIndent fuel
      else if isWhiteSpaceBool ch then
        collectPlainScalarLoopIx c.advance content (spaces.push ch) inFlow contentIndent fuel
      else if !isPlainSafeBool ch inFlow then
        (content, c)
      else
        collectPlainScalarLoopIx c.advance
          (content ++ spaces ++ String.singleton ch) "" inFlow contentIndent fuel

/-- Scan a plain scalar starting at the cursor's current character.
    The caller is responsible for enforcing the
    `canStartPlainScalarBool` precondition at dispatch.
    `contentIndent` is the continuation-line indent floor used for
    block context (caller supplies; flow context ignores it). -/
def scanPlainScalarIx {input : String} (c : IxCursor input)
    (inFlow : Bool) (contentIndent : Nat) :
    String × IxCursor input :=
  let (raw, c') := collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize
  (trimTrailingWSIx raw, c')

/-! ## Layer F3 — block scalars (§8.1, literal + folded)

Block scalars introduce the only scanner production that requires
an *enclosing* indent context (`parentIndent`). The body sits
*below* a header line of the form `('|' | '>') chomp? indent?
comment?`, with content indented strictly more than the parent.

The fold step (`foldBlockContent`) is a pure `String → String`
function over the raw line-stripped content: it operates on the
post-collection accumulator rather than on the cursor, so its
proof obligations are simple string-induction facts (deferred to
Step 5/6's content-correctness pass). Chomping (`strip` / `clip` /
`keep`) likewise acts on the raw string after collection.

The four-state fold machine `FoldState` (start / content / empty /
more) lives here as an inductive — making each case a named
constructor for pattern matching in proofs. -/

/-- States for folded block scalar newline processing (§8.1.3).
    Mirrors `Scanner/Scalar.lean::FoldState`. -/
inductive FoldState where
  | start   : FoldState
  | content : FoldState
  | empty   : FoldState
  | more    : FoldState
  deriving Repr, BEq

/-- Append `n` newlines to `acc`. Structurally recursive. -/
def appendNewlines (acc : String) : Nat → String
  | 0      => acc
  | n + 1 => appendNewlines (acc.push '\n') n

/-- Inner step of `foldBlockContent`. Walks the raw `List Char`,
    accumulating into `acc`, tracking `FoldState`, and counting
    pending newlines. The rules derive from YAML 1.2.2 [170]-[181];
    see legacy `Scanner/Scalar.lean::foldBlockContent` for the
    long-form table. -/
def foldBlockContentGo : List Char → String → FoldState → Nat → String
  | [],            acc, _,   _              => acc
  | '\n' :: rest,  acc, st,  pending        => foldBlockContentGo rest acc st (pending + 1)
  | c :: rest,     acc, st,  pending + 1    =>
    let isMore := c == ' '
    let newSt  := if isMore then FoldState.more else .content
    let acc'   := match st with
      | .start => appendNewlines acc (pending + 1)
      | .content =>
        if pending == 0 && !isMore then
          acc.push ' '
        else if pending == 0 && isMore then
          acc.push '\n'
        else if isMore then
          appendNewlines acc (pending + 1)
        else
          appendNewlines acc pending
      | .more  => appendNewlines acc (pending + 1)
      | .empty => appendNewlines acc (pending + 1)
    foldBlockContentGo rest (acc'.push c) newSt 0
  | c :: rest,     acc, st,  0              =>
    let newSt := match st with
      | .start => if c == ' ' then FoldState.more else .content
      | s      => s
    foldBlockContentGo rest (acc.push c) newSt 0

/-- Fold a raw block-scalar accumulator per §8.1.3 (the folded
    style; literal style skips this pass and uses the raw string
    directly). -/
@[inline] def foldBlockContent (raw : String) : String :=
  foldBlockContentGo raw.toList "" .start 0

/-- Consume exactly `count` spaces (and not tabs) starting at the
    cursor. Returns the number of spaces actually consumed (≤
    `count`) and the post-consumption cursor. -/
def consumeExactSpacesIx {input : String} (c : IxCursor input) :
    Nat → Nat × IxCursor input
  | 0          => (0, c)
  | count' + 1 =>
    if c.peek? == some ' ' then
      let (consumed, c') := consumeExactSpacesIx c.advance count'
      (consumed + 1, c')
    else
      (0, c)

/-- Consume characters until a line break or EOF, accumulating into
    `content`. Mirrors `collectLineContentLoop` from legacy. -/
def collectLineContentLoopIx {input : String} (c : IxCursor input)
    (content : String) : Nat → String × IxCursor input
  | 0          => (content, c)
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if isLineBreakBool ch then (content, c)
      else collectLineContentLoopIx c.advance (content.push ch) fuel
    | none    => (content, c)

/-- Auto-detect block-scalar content indentation. Probes whitespace
    runs and stops at the first non-empty line whose column ≥
    `minContentIndent`. Returns the detected indent + the input
    cursor *unchanged* (probe only — actual consumption is done by
    `collectBlockScalarLoopIx`). -/
def autoDetectBlockScalarIndentLoopIx {input : String} (probe : IxCursor input)
    (maxWSCol : Nat) (minContentIndent : Nat) :
    Nat → Nat
  | 0          =>
    if maxWSCol > minContentIndent then maxWSCol else minContentIndent
  | fuel + 1 =>
    let (probeAfterSp, _) := skipSpaces probe
    match probeAfterSp.peek? with
    | some c =>
      if isLineBreakBool c then
        let maxWSCol' := if probeAfterSp.pos.col > maxWSCol then probeAfterSp.pos.col else maxWSCol
        autoDetectBlockScalarIndentLoopIx (consumeLineBreak probeAfterSp)
          maxWSCol' minContentIndent fuel
      else
        if probeAfterSp.pos.col > minContentIndent then probeAfterSp.pos.col
        else minContentIndent
    | none   =>
      if maxWSCol > minContentIndent then maxWSCol else minContentIndent

/-- Entry point for indent auto-detection. -/
@[inline] def autoDetectBlockScalarIndentIx {input : String} (c : IxCursor input)
    (minContentIndent : Nat) : Nat :=
  autoDetectBlockScalarIndentLoopIx c 0 minContentIndent input.utf8ByteSize

/-- Inner loop of `collectBlockScalarLoopIx`. Consumes content
    line-by-line starting from a line boundary:
    1. Probe for document boundary (`---` / `...` at col 0) — stop.
    2. Consume up to `contentIndent` spaces of indent.
    3. If next char is a line break (= empty/short line) → append
       `'\n'` to the raw accumulator and recurse.
    4. If the line is *less* indented than `contentIndent` and not
       empty → stop (with the cursor *before* the indent probe).
    5. Otherwise collect content to the next line break, append
       `'\n'` if a break is found, and recurse.

    The indent-probe result and per-line collection result are
    referenced via `.1`/`.2` projections rather than `let`-destructured;
    `let`-binding would opacify `split` in the monotonicity proof
    (Reflection 40 / 37). -/
def collectBlockScalarLoopIx {input : String} (c : IxCursor input)
    (rawContent : String) (contentIndent : Nat) :
    Nat → String × IxCursor input
  | 0          => (rawContent, c)
  | fuel + 1 =>
    if c.pos.col == 0 && atDocumentBoundaryIx c then
      (rawContent, c)
    else
      match (consumeExactSpacesIx c contentIndent).2.peek? with
      | none    => (rawContent, (consumeExactSpacesIx c contentIndent).2)
      | some ch =>
        if isLineBreakBool ch then
          collectBlockScalarLoopIx
            (consumeLineBreak (consumeExactSpacesIx c contentIndent).2)
            (rawContent.push '\n') contentIndent fuel
        else if (consumeExactSpacesIx c contentIndent).1 < contentIndent then
          (rawContent, c)
        else
          match
              (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                input.utf8ByteSize).2.peek? with
          | some ch' =>
            if isLineBreakBool ch' then
              collectBlockScalarLoopIx
                (consumeLineBreak
                  (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                    input.utf8ByteSize).2)
                ((rawContent ++
                  (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                    input.utf8ByteSize).1).push '\n')
                contentIndent fuel
            else
              collectBlockScalarLoopIx
                (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                  input.utf8ByteSize).2
                (rawContent ++
                  (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                    input.utf8ByteSize).1)
                contentIndent fuel
          | none   =>
            (rawContent ++
              (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                input.utf8ByteSize).1,
             (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                input.utf8ByteSize).2)

/-- Parse the header characters that may follow `|` or `>`:
    chomping indicator (`-` strip / `+` keep) and an explicit
    indentation indicator (digit `1..9`). Either order is permitted.
    The fuel is the maximum number of header characters (2 is the
    spec maximum: one chomp + one indent). -/
def parseBlockHeaderLoopIx {input : String} (c : IxCursor input)
    (chomp : ChompStyle) (explicitOffset : Option Nat) :
    Nat → ChompStyle × Option Nat × IxCursor input
  | 0          => (chomp, explicitOffset, c)
  | fuel + 1 =>
    match c.peek? with
    | some '-' => parseBlockHeaderLoopIx c.advance .strip explicitOffset fuel
    | some '+' => parseBlockHeaderLoopIx c.advance .keep  explicitOffset fuel
    | some ch  =>
      if ch.isDigit && ch != '0' then
        parseBlockHeaderLoopIx c.advance chomp (some (ch.toNat - '0'.toNat)) fuel
      else (chomp, explicitOffset, c)
    | none     => (chomp, explicitOffset, c)

/-- Strip trailing `\n` characters from `s`. -/
def stripTrailingNewlines (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (· == '\n')).reverse)

/-- Apply chomping per §8.1.1: `strip` removes every trailing `\n`,
    `clip` keeps at most one trailing `\n`, `keep` preserves them. -/
def applyChomp (chomp : ChompStyle) (raw : String) : String :=
  match chomp with
  | .strip => stripTrailingNewlines raw
  | .clip  =>
    let stripped := stripTrailingNewlines raw
    if raw.endsWith "\n" then stripped ++ "\n" else stripped
  | .keep  => raw

/-- Helper: the post-header cursor for `scanBlockScalarIx`. Built
    as a chain `skipWhitespace ∘ (optional comment) ∘ consumeLineBreak`
    on top of `parseBlockHeaderLoopIx`'s output. Named so the proof
    can refer to it without rebuilding the chain each time. -/
def blockHeaderToBodyIx {input : String} (c : IxCursor input) : IxCursor input :=
  consumeLineBreak
    (if (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).peek?
         == some '#' then
       skipCommentText
         (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).advance
     else
       skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2)

/-- Scan a block scalar. The cursor must be at the introducer `|`
    (literal) or `>` (folded). Returns `(content, style, c')`
    where `style` is `.literal` or `.folded` and `c'` is the cursor
    after the block-scalar content.

    `parentIndent` is the column of the enclosing block (`s.col`
    at the introducer in the legacy scanner). Content lines must
    sit at indent ≥ `parentIndent + 1` (or the explicit indicator's
    offset if supplied).

    The intermediate cursors are not `let`-bound; they reference
    `blockHeaderToBodyIx c` and `parseBlockHeaderLoopIx`'s output
    via projection — the `let` would opacify `split` in the
    monotonicity proof (Reflection 40 / 37). -/
def scanBlockScalarIx {input : String} (c : IxCursor input)
    (parentIndent : Nat) :
    Option (String × ScalarStyle × IxCursor input) :=
  match c.peek? with
  | some ch =>
    if ch == '|' || ch == '>' then
      some
        ( (if ch == '|' then
             applyChomp (parseBlockHeaderLoopIx c.advance .clip none 2).1
               (collectBlockScalarLoopIx (blockHeaderToBodyIx c) ""
                 (match (parseBlockHeaderLoopIx c.advance .clip none 2).2.1 with
                   | some m => parentIndent + m
                   | none   =>
                     autoDetectBlockScalarIndentIx (blockHeaderToBodyIx c)
                       (parentIndent + 1))
                 input.utf8ByteSize).1
           else
             foldBlockContent
               (applyChomp (parseBlockHeaderLoopIx c.advance .clip none 2).1
                 (collectBlockScalarLoopIx (blockHeaderToBodyIx c) ""
                   (match (parseBlockHeaderLoopIx c.advance .clip none 2).2.1 with
                     | some m => parentIndent + m
                     | none   =>
                       autoDetectBlockScalarIndentIx (blockHeaderToBodyIx c)
                         (parentIndent + 1))
                   input.utf8ByteSize).1))
        , (if ch == '|' then ScalarStyle.literal else ScalarStyle.folded)
        , (collectBlockScalarLoopIx (blockHeaderToBodyIx c) ""
            (match (parseBlockHeaderLoopIx c.advance .clip none 2).2.1 with
              | some m => parentIndent + m
              | none   =>
                autoDetectBlockScalarIndentIx (blockHeaderToBodyIx c)
                  (parentIndent + 1))
            input.utf8ByteSize).2 )
    else
      none
  | none   => none

end L4YAML.Scanner.Indexed
