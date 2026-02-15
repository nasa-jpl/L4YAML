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

/-- YAML line break characters
(§5.4, https://yaml.org/spec/1.2.2/#54-line-break-characters): LF or CR -/
def isLineBreak (c : Char) : Bool :=
  c == '\n' || c == '\r'

/-- YAML white space
(§5.5, https://yaml.org/spec/1.2.2/#55-white-space-characters): space or tab -/
def isWhiteSpace (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- YAML indicator characters
(§5.3, https://yaml.org/spec/1.2.2/#53-indicator-characters) -/
def isIndicator (c : Char) : Bool :=
  c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
       '\'', '"', '%', '@', '`']

/-- Flow indicator characters
(§5.3, https://yaml.org/spec/1.2.2/#53-indicator-characters) -/
def isFlowIndicator (c : Char) : Bool :=
  c ∈ [',', '[', ']', '{', '}']

/-- Characters that can appear in anchor names -/
def isAnchorChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_'

/-- Characters forbidden at the start of a plain scalar -/
def isForbiddenPlainStart (c : Char) : Bool :=
  isIndicator c

/--
Check if a character can start a plain scalar.

YAML 1.2.2 §7.3.3 (https://yaml.org/spec/1.2.2/#733-plain-style):
Plain scalars cannot start with most indicators.
Exception: `-`, `?`, `:` can start plain scalars if followed by a
non-space character.
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

/-- Parse a newline (LF, CR, or CRLF) -/
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

/-- Parse a YAML comment: `#` to end of line -/
def comment : YamlParser Unit :=
  withErrorMessage "expected comment" do
    let _ ← token '#'
    dropMany (tokenFilter (fun c => !isLineBreak c))

/-- Skip optional horizontal whitespace and an optional comment -/
def skipTrailing : YamlParser Unit := do
  skipHWhitespace
  optional comment *> return

/-- Skip trailing whitespace, optional comment, and the newline -/
def skipToNextLine : YamlParser Unit := do
  skipTrailing
  newline

/--
Skip blank lines and comment-only lines.
Stops at a line with actual content (or end of input).
-/
partial def skipBlankLines : YamlParser Unit := do
  match ← option? (lookAhead (skipSpaces *> (newline <|> (comment *> return)))) with
  | some _ =>
      skipSpaces
      optional comment *> return
      optional newline *> return
      skipBlankLines
  | none => return

/--
Consume exactly `n` spaces of indentation, rejecting tabs.

YAML 1.2.2 §6.1 (https://yaml.org/spec/1.2.2/#61-indentation-spaces):
"In YAML block styles, structure is determined by indentation. ...
To maintain portability, tab characters must not be used in indentation."

This is the **only** way to consume indentation in the verified parser.
There is no ambiguous `skipSpace` that might eat indentation — the verified
architecture enforces that indentation is always consumed explicitly.
-/
def consumeIndent (n : Nat) : YamlParser Unit :=
  withErrorMessage s!"expected {n} spaces of indentation (tabs not allowed)" do
    -- Check for tab at start (YAML 1.2.2 §6.1, https://yaml.org/spec/1.2.2/#61-indentation-spaces)
    match ← option? (lookAhead (token '\t')) with
    | some _ => throwUnexpectedWithMessage (msg := "tabs are not allowed for indentation")
    | none => drop n (token ' ')

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
it raises a hard error instead of silently ending the sequence.

Only checks when `col > seqIndent` (over-indented). Under-indented
indicators at `col < seqIndent` may belong to a parent-level sequence
and are handled correctly by the parent's own loop.

See: ANALYSIS.md §2.A "Three-Valued Error Recovery"
-/
def validateNoWrongIndentSeq (seqIndent : Nat) (col : Nat) : YamlParser Unit := do
  if col > seqIndent then
    let hasSeq ← hasSequenceIndicator
    if hasSeq then
      withErrorMessage
        s!"sequence item at column {col}, expected column {seqIndent} (wrong indentation)"
        throwUnexpected

/--
Validate that there is no wrongly-indented block mapping indicator.

Similar to `validateNoWrongIndentSeq`, but checks for mapping key patterns
(content followed by `: `).

The `scanForColon` parameter is a parser that detects a mapping key pattern,
passed in to avoid circular imports with Block.lean's `detectMappingKey`.

See: ANALYSIS.md §2.A "Three-Valued Error Recovery"
-/
def validateNoWrongIndentMap (mapIndent : Nat) (col : Nat)
    (scanForColon : YamlParser Bool) : YamlParser Unit := do
  if col > mapIndent then
    let hasMap ← lookAhead scanForColon
    if hasMap then
      withErrorMessage
        s!"mapping entry at column {col}, expected column {mapIndent} (wrong indentation)"
        throwUnexpected

end Lean4Yaml.Parse
