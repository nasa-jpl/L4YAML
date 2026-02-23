/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Parser
import Lean4Yaml.Stream

/-!
# YAML Character Classification & Basic Combinators

Character classification functions matching YAML 1.2.2
§5 (https://yaml.org/spec/1.2.2/#chapter-5-character-productions) and basic
parsing combinators built on lean4-parser.

All combinators are defined in terms of lean4-parser primitives,
which means they inherit the library's backtracking and error reporting
behavior automatically.
-/

namespace Lean4Yaml.Parse

open Parser
open Parser.Char

/-! ## Character Classification
  YAML 1.2.2 §5 (https://yaml.org/spec/1.2.2/#chapter-5-character-productions) -/

/-- YAML line break characters.

**YAML 1.2.2**: [26] b-char (§5.4, https://yaml.org/spec/1.2.2/#54-line-break-characters)
- [24] b-line-feed (LF) | [25] b-carriage-return (CR) -/
def isLineBreak (c : Char) : Bool :=
  c == '\n' || c == '\r'

/-- YAML white space.

**YAML 1.2.2**: [33] s-white (§5.5, https://yaml.org/spec/1.2.2/#55-white-space-characters)
- [31] s-space | [32] s-tab -/
def isWhiteSpace (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- YAML indicator characters.

**YAML 1.2.2**: [22] c-indicator (§5.3, https://yaml.org/spec/1.2.2/#53-indicator-characters) -/
def isIndicator (c : Char) : Bool :=
  c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
       '\'', '"', '%', '@', '`']

/-- Flow indicator characters.

**YAML 1.2.2**: [23] c-flow-indicator (§5.3, https://yaml.org/spec/1.2.2/#53-indicator-characters) -/
def isFlowIndicator (c : Char) : Bool :=
  c ∈ [',', '[', ']', '{', '}']

/-- Characters that can appear in anchor names.

**YAML 1.2.2**: [102] ns-anchor-char (§6.9.2, https://yaml.org/spec/1.2.2/#692-node-anchors)

P6 fix (8XYN): YAML §6.9.2 defines anchor names as `ns-anchor-char+`
    where `ns-anchor-char` is any character except flow indicators,
    whitespace, and line breaks.  The previous restriction to ASCII
    alphanumeric/hyphen/underscore was too narrow. -/
def isAnchorChar (c : Char) : Bool :=
  !isFlowIndicator c && !isWhiteSpace c && !isLineBreak c

/-- Characters forbidden at the start of a plain scalar.

**YAML 1.2.2**: [22] c-indicator (§5.3) — used as the exclusion set for [123] ns-plain-first(c). -/
def isForbiddenPlainStart (c : Char) : Bool :=
  isIndicator c

/--
Check if a character can start a plain scalar.

**YAML 1.2.2**: [123] ns-plain-first(c) (§7.3.3, https://yaml.org/spec/1.2.2/#733-plain-style)

Plain scalars cannot start with most indicators ([22] c-indicator).
Exception: `-`, `?`, `:` can start plain scalars if followed by a
non-space character ([34] ns-char).
-/
def canStartPlainScalar (c : Char) (next : Option Char) : Bool :=
  if c == '-' || c == '?' || c == ':' then
    match next with
    | some n => !isWhiteSpace n && !isLineBreak n
    | none => false
  else
    !isIndicator c && !isWhiteSpace c && !isLineBreak c

/-! ## Basic Parsers -/

/-- Parse a single space character -/
def space : YamlParser Char :=
  withErrorMessage "expected space" <| token ' '

/-- Parse a newline ([28] b-break): LF, CR, or CRLF -/
def newline : YamlParser Unit :=
  withErrorMessage "expected newline" do
    let c ← tokenFilter isLineBreak
    -- Handle CRLF as a single newline
    if c == '\r' then
      optional (token '\n') *> return
    else
      return

/-- Parse one or more spaces (not tabs, not newlines) -/
def spaces1 : YamlParser Nat := do
  let _ ← token ' '
  let n ← count (token ' ')
  return n + 1

/-- Skip zero or more horizontal white space characters (space and tab) -/
def skipHWhitespace : YamlParser Unit :=
  dropMany (tokenFilter isWhiteSpace)

/-- Skip zero or more space characters (not tabs) -/
def skipSpaces : YamlParser Unit :=
  dropMany (token ' ')

/-- Parse exactly `n` space characters for indentation -/
def indent (n : Nat) : YamlParser Unit :=
  withErrorMessage s!"expected {n} spaces of indentation" do
    drop n (token ' ')

/--
Count leading spaces without consuming them.

This is lean4-parser's `lookAhead` applied to space counting.
Unlike lean4-yaml's `peekColumn` hack, this is just normal backtracking.
-/
def peekIndent : YamlParser Nat :=
  lookAhead do
    let n ← count (token ' ')
    return n

/-- Parse a YAML comment: `#` to end of line.

**YAML 1.2.2**: [75] c-nb-comment-text (§6.7, https://yaml.org/spec/1.2.2/#67-comments) -/
def comment : YamlParser Unit :=
  withErrorMessage "expected comment" do
    let _ ← token '#'
    dropMany (tokenFilter (fun c => !isLineBreak c))

/-- Skip optional horizontal whitespace and an optional comment.

**YAML 1.2.2**: [77] s-b-comment (§6.7) -/
def skipTrailing : YamlParser Unit := do
  skipHWhitespace
  optional comment *> return

/-- Skip trailing whitespace, optional comment, and the newline.

**YAML 1.2.2**: [77] s-b-comment + [76] b-comment (§6.7) -/
def skipToNextLine : YamlParser Unit := do
  skipTrailing
  newline

/--
Skip blank lines and comment-only lines.
Stops at a line with actual content (or end of input).

P5 fix: use `skipHWhitespace` instead of `skipSpaces` so that
tab characters on blank/comment lines are handled correctly.
YAML §5.5 defines whitespace as space or tab.
-/
def skipBlankLines : YamlParser Unit := do
  let fuel := Stream.remaining (← getStream)
  go fuel
where
  go : Nat → YamlParser Unit
    | 0 => return ()
    | fuel + 1 => do
      match ← option? (lookAhead (skipHWhitespace *> (newline <|> (comment *> return)))) with
      | some _ =>
          skipHWhitespace
          optional comment *> return
          optional newline *> return
          go fuel
      | none => return

/-!
## Indentation Consumption

YAML 1.2.2 §6.1: tab characters must not be used in indentation.
`consumeIndent` enforces this as a validation error, not an exception.
-/

/--
Consume exactly `n` spaces of indentation, rejecting tabs.

**YAML 1.2.2**: [63] s-indent(n) (§6.1, https://yaml.org/spec/1.2.2/#61-indentation-spaces)
"In YAML block styles, structure is determined by indentation. ...
To maintain portability, tab characters must not be used in indentation."

This is the **only** way to consume indentation in the verified parser.
There is no ambiguous `skipSpace` that might eat indentation — the verified
architecture enforces that indentation is always consumed explicitly.

**Pre-condition**: stream is at the start of an indented line.
**Post-condition**: if tabs are detected, `validationError` is set.
  The `drop n (token ' ')` will fail naturally (via lean4-parser),
  causing caller to backtrack. The validation error persists through
  backtracking and is checked at the top level.

**Edge case `n = 0`**: per YAML 1.2.2 §6.1, `s-indent(n)` with `n = 0`
matches the empty string — no spaces are consumed and the parser always
succeeds.  This is spec-correct: at document level the indentation
parameter is `n = -1`, so content lines require `s-indent(n+m)` where
`m ≥ 1`, giving `s-indent(0)` for column-0 content.  Callers relying on
`consumeIndent` for stream progress must independently verify that at
least one content character follows (cf. the spec's `nb-char+`
requirement in `l-nb-literal-text` and `s-nb-folded-text`).
-/
def consumeIndent (n : Nat) : YamlParser Unit :=
  withErrorMessage s!"expected {n} spaces of indentation (tabs not allowed)" do
    -- Check for tab at start (YAML 1.2.2 §6.1, https://yaml.org/spec/1.2.2/#61-indentation-spaces)
    match ← option? (lookAhead (token '\t')) with
    | some _ =>
      setValidationError "tabs are not allowed for indentation (YAML 1.2.2 §6.1)"
      -- Let `drop n` below fail naturally: token ' ' won't match '\t',
      -- causing lean4-parser to signal no-match to the caller.
    | none => pure ()
    drop n (token ' ')

/--
Look ahead for tab characters in leading whitespace at the current position.

YAML 1.2.2 §6.1: tab characters must not be used in indentation.
This is a `lookAhead` — no input is consumed.  If a tab is found
among leading space characters (before the first non-whitespace),
a validation error is set.

Covers:
- Start-of-line indentation (`s-indent(n)`)
- Post-indicator whitespace where indentation is implied
- Flow continuation line prefixes (`s-flow-line-prefix(n)`)
-/
def checkNoTabIndent : YamlParser Unit := do
  let hasTab ← lookAhead do
    dropMany (token ' ')
    match ← option? anyToken with
    | some '\t' => pure true
    | _         => pure false
  if hasTab then
    setValidationError "tabs are not allowed for indentation (YAML 1.2.2 §6.1)"

/--
Check for tabs within the required indentation prefix.

YAML 1.2.2 §6.1: "Indentation is a zero or more space characters."
Tabs are NOT allowed within the first `minIndent` columns (the
s-indent(n) production).  Tabs appearing AFTER the required indentation
(as separation whitespace) are fine.

When `minIndent = 0`, no indentation is required and any leading tabs
are treated as separation whitespace — no error.

This is a `lookAhead` — no input is consumed.
-/
def checkIndentForTabs (minIndent : Nat) : YamlParser Unit := do
  if minIndent == 0 then return ()
  let hasTabInIndent ← lookAhead do
    let rec scan : Nat → YamlParser Bool
      | 0 => return false
      | remaining + 1 => do
        match ← option? anyToken with
        | some ' '  => scan remaining
        | some '\t' => return true
        | _         => return false
    scan minIndent
  if hasTabInIndent then
    setValidationError "tabs are not allowed for indentation (YAML 1.2.2 §6.1)"

/--
Scan leading whitespace for any tab character.  Returns `true` if a tab
is found among leading spaces/tabs before the first non-whitespace character.
This is a `lookAhead` — no input is consumed.
-/
def hasTabInWhitespace : YamlParser Bool :=
  lookAhead do
    dropMany (token ' ')
    match ← option? anyToken with
    | some '\t' => pure true
    | _         => pure false

/-! ## Dispatch Result

Three-valued dispatch result for block value parsing.
See ANALYSIS.md §2.A and LEAN4_STYLE.md § "Parser Error Design:
No Exceptions for Decisions".

Parser decisions are expressed as explicit return values, not exceptions:
- `matched`: a parser consumed input and produced a value
- `noMatch`: no parser recognized the input (try next alternative)
- `invalid`: input is structurally invalid (do not backtrack)

This works above lean4-parser's combinator level, where `<|>`, `option?`,
and `first` catch all `Result.error` unconditionally.
-/

/--
Three-valued result for dispatch decisions.

Each variant maps to a proof obligation:
- `matched val`: parser produced a result
- `noMatch`: no parser matched (justifies trying alternatives)
- `invalid msg`: input is invalid (provable dead-end, should not backtrack)

Callers must pattern-match on the result directly.  There is no
`.toParser` conversion — the "no exceptions for decisions" principle
requires that each call site explicitly handles all three variants.

**For `.invalid`**: callers must call `setValidationError msg` to
record the error in the stream (where it survives backtracking),
then return a fallback value.  The top-level parser checks the
stream's `validationError` field and rejects the input.
-/
inductive DispatchResult (α : Type) where
  | matched (val : α)
  | noMatch
  | invalid (msg : String)
  deriving Repr, Nonempty

/-! ## Plain Scalar Continuation Types

Multi-line plain scalar support (YAML 1.2.2 §7.3.3,
https://yaml.org/spec/1.2.2/#733-plain-style).

Plain scalars in block context can span multiple lines. Continuation lines
must be more indented than the parent structure's indentation level, and
must not start with structural indicators (sequence `- ` or mapping `key: `).

The continuation check is a pure `lookAhead` probe — it inspects the stream
without consuming input. The caller then decides whether to consume based
on the result. This check-then-consume separation makes termination proofs
easier: checking is non-consuming, consuming provably advances position.

See ANALYSIS.md §2.B.
-/

/--
Result of checking whether a plain scalar continues onto the next line.

Each variant describes what was found at the start of the next line:
- `notContinuing`: dedent, end of input, or document boundary
- `plainContinuation`: regular content continuation
- `afterEmpty n`: continuation after n empty/blank lines (paragraph breaks)
- `sequenceMarker`: line starts with `- ` (belongs to parent sequence)
- `mappingEntry`: line contains `: ` (belongs to parent mapping)
-/
inductive ContinuationCheck where
  | notContinuing
  | plainContinuation
  | afterEmpty (n : Nat)
  | sequenceMarker
  | mappingEntry
  deriving Repr, BEq, Nonempty

/-! ## Separator Detection -/

/--
Check if we're at a mapping value indicator (`: ` or `:\n` or `:` at EOF).

Does not consume any input.
-/
def atMappingSeparator : YamlParser Bool :=
  lookAhead do
    match ← option? (token ':') with
    | none => return false
    | some _ =>
        match ← option? anyToken with
        | none => return true  -- `:` at EOF
        | some c => return (isWhiteSpace c || isLineBreak c)

/--
Check if we're at a document start marker (`---` followed by whitespace/newline/EOF).

**YAML 1.2.2**: [197] c-directives-end (§9.1.2)

Does not consume any input.
-/
def atDocumentStart : YamlParser Bool :=
  lookAhead do
    match ← option? (chars "---") with
    | none => return false
    | some _ =>
        match ← option? anyToken with
        | none => return true
        | some c => return (isWhiteSpace c || isLineBreak c || c == '#')

/--
Check if we're at a document end marker (`...` followed by whitespace/newline/EOF).

**YAML 1.2.2**: [198] c-document-end (§9.1.3)

Does not consume any input.
-/
def atDocumentEnd : YamlParser Bool :=
  lookAhead do
    match ← option? (chars "...") with
    | none => return false
    | some _ =>
        match ← option? anyToken with
        | none => return true
        | some c => return (isWhiteSpace c || isLineBreak c || c == '#')

/--
Check if we're at either document boundary marker.
-/
def atDocumentBoundary : YamlParser Bool := do
  let start ← atDocumentStart
  if start then return true
  atDocumentEnd

/-! ## Indentation Validation

These helpers detect structural indicators at wrong indentation levels.
They support the "three-valued error recovery" pattern from the lean4-yaml
cross-project analysis (ANALYSIS.md §2.A): instead of silently ending a
collection when the indentation doesn't match, we check if the remaining
content looks like a wrongly-indented indicator and raise a hard error.

This prevents invalid YAML from being silently accepted when backtracking
falls through to a plain scalar parser.
-/

/--
Check if the current position has a sequence indicator (`- ` or `-\n` or `-` at EOF).

Does not consume any input. Returns `true` if the content at the current
position is a valid block sequence item indicator.
-/
def hasSequenceIndicator : YamlParser Bool :=
  lookAhead do
    match ← option? (token '-') with
    | none => return false
    | some _ =>
        match ← option? anyToken with
        | none => return true  -- `-` at EOF
        | some c => return (isWhiteSpace c || isLineBreak c)

/--
Validate that there is no wrongly-indented block sequence indicator.

When a block sequence loop terminates because `col ≠ seqIndent`, this
check detects if there's a `- ` indicator at the wrong column. If found,
it records a validation error in the stream (survives backtracking).

Only checks when `col > seqIndent` (over-indented). Under-indented
indicators at `col < seqIndent` may belong to a parent-level sequence
and are handled correctly by the parent's own loop.

**Pre-condition**: `col ≠ seqIndent`.
**Post-condition**: if a wrongly-indented sequence indicator is found,
  `stream'.validationError = some msg`.

See: ANALYSIS.md §2.A "Three-Valued Error Recovery"
-/
def validateNoWrongIndentSeq (seqIndent : Nat) (col : Nat) : YamlParser Unit := do
  if col > seqIndent then
    let hasSeq ← hasSequenceIndicator
    if hasSeq then
      setValidationError
        s!"sequence item at column {col}, expected column {seqIndent} (wrong indentation)"

/--
Validate that there is no wrongly-indented block mapping indicator.

Similar to `validateNoWrongIndentSeq`, but checks for mapping key patterns
(content followed by `: `).

The `scanForColon` parameter is a parser that detects a mapping key pattern,
passed in to avoid circular imports with Block.lean's `detectMappingKey`.

**Pre-condition**: `col ≠ mapIndent`.
**Post-condition**: if a wrongly-indented mapping indicator is found,
  `stream'.validationError = some msg`.

See: ANALYSIS.md §2.A "Three-Valued Error Recovery"
-/
def validateNoWrongIndentMap (mapIndent : Nat) (col : Nat)
    (scanForColon : YamlParser Bool) : YamlParser Unit := do
  if col > mapIndent then
    let hasMap ← lookAhead scanForColon
    if hasMap then
      setValidationError
        s!"mapping entry at column {col}, expected column {mapIndent} (wrong indentation)"

/-! ## Plain Scalar Continuation Check

The check-then-consume continuation probe for multi-line plain scalars.
Defined here (after `atDocumentBoundary`, `hasSequenceIndicator`) to
avoid forward references.

See ANALYSIS.md §2.B.
-/

/--
Check whether a plain scalar continues onto the next line(s).

This is a pure `lookAhead` probe — it does NOT consume any input.
`contentIndent` is the indentation level at which the scalar's content
started; continuation lines must be at or beyond this level
(`col >= contentIndent`, equivalently `col < contentIndent` → stop).

**P6 fix (document-level continuation)**: Previously this function took
`baseIndent` (= contentIndent − 1) and checked `col <= baseIndent`.
At document level, YAML's indentation parameter is n = −1, so
`contentIndent = 0` and `baseIndent` saturated at 0 (Nat), incorrectly
blocking col-0 continuation.  Using `col < contentIndent` with
`contentIndent : Nat` avoids the saturation: when `contentIndent = 0`,
`col < 0` is always false for `Nat`, correctly allowing every column.

Decision algorithm:
1. Check for newline — if none, not continuing
2. Count consecutive empty/blank lines
3. Check indentation of next content line — must be ≥ contentIndent
4. Check for document boundaries (`---`, `...`) — stops continuation
5. Check for sequence marker (`- `) — not a continuation
6. Check for mapping entry (`key: `) — not a continuation
7. Otherwise, it's a continuation (possibly after empty lines)

**YAML 1.2.2**: [131] s-ns-plain-next-line(n,c) look-ahead (§7.3.3)
-/
def checkContinuation (contentIndent : Nat) : YamlParser ContinuationCheck :=
  lookAhead do
    -- Must be at a line break to continue
    match ← option? newline with
    | none => return .notContinuing
    | some _ =>
      -- Count empty/blank lines
      let fuel ← Stream.remaining <$> getStream
      let emptyCount ← countEmptyLines fuel 0
      -- Check indentation of the next content line
      skipSpaces
      let col ← currentCol
      if col < contentIndent then
        return .notContinuing
      -- Check for document boundaries
      let atBoundary ← atDocumentBoundary
      if atBoundary then
        return .notContinuing
      -- Check for sequence marker: `- ` or `-\n` or `-` at EOF
      -- P6 fix (AB8U): only check when the continuation line is DEEPER than
      -- the content indent.  At col == contentIndent, `-` is a valid
      -- `ns-plain-char` per YAML §7.3.3 and the continuation line is part
      -- of the plain scalar (e.g., `- single multiline\n - sequence entry`
      -- where ` - sequence entry` at col 1 == contentIndent 1 is scalar
      -- content, not a block indicator).
      if col > contentIndent then
        let hasSeq ← hasSequenceIndicator
        if hasSeq then
          return .sequenceMarker
      -- Check for mapping entry: scan for `: ` pattern on this line
      let fuel' ← Stream.remaining <$> getStream
      let hasMap ← scanForMappingSeparator fuel'
      if hasMap then
        return .mappingEntry
      -- It's a continuation
      if emptyCount > 0 then
        return .afterEmpty emptyCount
      else
        return .plainContinuation
where
  /-- Count consecutive empty or blank lines (lines with only whitespace).
      P5 fix: use `skipHWhitespace` instead of `skipSpaces` so that
      tab-only lines (like NB6Z) are recognized as blank lines.
      YAML §5.5 defines whitespace as space or tab; §6.5 line folding
      treats lines with only whitespace as blank (paragraph separators). -/
  countEmptyLines : Nat → Nat → YamlParser Nat
    | 0, n => return n
    | fuel + 1, n => do
      match ← option? (lookAhead (skipHWhitespace *> newline)) with
      | some _ =>
        skipHWhitespace
        newline
        countEmptyLines fuel (n + 1)
      | none => return n
  /-- Skip over balanced flow brackets.  `depth` counts nesting level;
      when it reaches 0, the matching close bracket has been consumed.
      Uses fuel (stream remaining) for termination since depth can increase. -/
  skipFlowBrackets : Nat → Nat → YamlParser Unit
    | 0, _ => return ()
    | _, 0 => return ()
    | fuel + 1, depth => do
      match ← option? anyToken with
      | none => return ()  -- unclosed collection at EOF, bail out
      | some c =>
        if c == '}' || c == ']' then skipFlowBrackets fuel (depth - 1)
        else if c == '{' || c == '[' then skipFlowBrackets fuel (depth + 1)
        else if isLineBreak c then return ()  -- unclosed collection at EOL
        else skipFlowBrackets fuel depth
  /-- P6 fix: use lookAhead for the char after `:` so that adjacent colons
      (`::`) are properly handled.  The second `:` is re-examined as a
      potential separator on the next iteration.  Mirrors the fix in
      `detectMappingKey`. -/
  scanLoop : Nat → YamlParser Bool
    | 0 => return false
    | fuel + 1 => do
      match ← option? anyToken with
      | none => return false
      | some ':' =>
        match ← option? (lookAhead anyToken) with
        | none => return true  -- `:` at EOF
        | some c =>
          if isWhiteSpace c || isLineBreak c then return true
          else scanLoop fuel  -- don't consume peeked char; next iteration handles it
      | some c =>
        if isLineBreak c then return false
        else if c == '"' || c == '\'' then return false  -- Don't scan through quotes
        -- Flow-aware: skip balanced flow collections
        else if c == '{' || c == '[' then do
          skipFlowBrackets fuel 1
          scanLoop fuel
        else scanLoop fuel
  /-- Scan the current line for a mapping separator (`: ` or `:\n` or `:` at EOF).
      Does not cross line boundaries.  Flow-aware: skips balanced `{...}`/`[...]`
      content to avoid false positives from `: ` inside flow collections. -/
  scanForMappingSeparator (fuel : Nat) : YamlParser Bool :=
    scanLoop fuel

end Lean4Yaml.Parse
