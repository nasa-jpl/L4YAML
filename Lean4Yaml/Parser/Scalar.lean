/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators

/-!
# YAML Scalar Parsers

Parsers for the five YAML scalar styles
(YAML 1.2.2 §7, https://yaml.org/spec/1.2.2/#chapter-7-flow-style-productions and
§8, https://yaml.org/spec/1.2.2/#chapter-8-block-style-productions):
- Plain (unquoted)
- Single-quoted
- Double-quoted
- Literal block (`|`)
- Folded block (`>`)

## Design Principles

1. **Explicit indentation**: Block scalars use `currentCol` (not `peekColumn`)
   to determine indentation. The column is always accurate because it's
   tracked by the `YamlStream` itself.

2. **No implicit space consumption**: The `consumeIndent` combinator from
   Combinators.lean is used instead of generic `skipSpace`, preventing
   the class of bugs demonstrated by `skipToNextLine`.

3. **`withCapture` for provenance**: Where possible, we use lean4-parser's
   `withCapture` to track the source segment of each scalar.
-/

namespace Lean4Yaml.Parse

open Parser
open Parser.Char
open Lean4Yaml

/-! ## Double-Quoted Scalars
  §7.3.1 (https://yaml.org/spec/1.2.2/#731-double-quoted-style) -/

/--
Parse a YAML escape sequence inside a double-quoted scalar.

YAML 1.2.2 §5.7 (https://yaml.org/spec/1.2.2/#57-escaped-characters):
Escape sequences start with `\` followed by an
escape character. Returns the character the sequence represents.
-/
def escapeSequence : YamlParser Char :=
  withErrorMessage "expected escape sequence" do
    let _ ← char '\\'
    let c ← anyToken
    match c with
    | '0'  => return '\x00'  -- null
    | 'a'  => return '\x07'  -- bell
    | 'b'  => return '\x08'  -- backspace
    | 't'  => return '\t'    -- tab
    | '\t' => return '\t'    -- also tab (literal tab)
    | 'n'  => return '\n'    -- line feed
    | 'v'  => return '\x0b'  -- vertical tab
    | 'f'  => return '\x0c'  -- form feed
    | 'r'  => return '\r'    -- carriage return
    | 'e'  => return '\x1b'  -- escape
    | ' '  => return ' '     -- space
    | '"'  => return '"'     -- double quote
    | '/'  => return '/'     -- slash
    | '\\' => return '\\'    -- backslash
    | 'N'  => return '\x85'  -- next line (NEL)
    | '_'  => return '\xa0'  -- non-breaking space
    | 'x'  => unicodeEscape 2 -- 2-digit hex
    | 'u'  => unicodeEscape 4 -- 4-digit hex
    | 'U'  => unicodeEscape 8 -- 8-digit hex
    | _    =>
      -- Unknown escape character: record validation error, return literal char.
      setValidationError s!"unknown escape character: {c}"
      return c
where
  /-- Parse `n` hex digits and convert to a Char -/
  unicodeEscape (n : Nat) : YamlParser Char := do
    let mut code : Nat := 0
    for _ in [:n] do
      let d ← Char.ASCII.hexDigit
      code := code * 16 + d.val
    if h : code.toUInt32.isValidChar then
      return ⟨code.toUInt32, h⟩
    else
      -- Invalid unicode code point: record validation error, return replacement char.
      setValidationError s!"invalid unicode code point: {code}"
      return '\uFFFD'

/-! ## Quoted Scalar Fold Result Type -/

/--
Result of folding newlines in a quoted scalar continuation line.

YAML 1.2.2 §9.1.2 production [206] defines `c-forbidden`: the sequences
`--- ` and `... ` at column 0 (start-of-line) followed by whitespace,
line break, or end-of-input are document boundary markers that terminate
document content. Inside a quoted scalar, encountering `c-forbidden` on
a continuation line means the scalar was never closed — this is
definitively invalid YAML.

Without an explicit result type, backtracking would swallow the error
and some enclosing combinator might silently accept part of the input.
This follows the same explicit-result-type pattern as:
- `DispatchResult`: three-valued dispatch (matched/noMatch/invalid)
- `DocumentResult`: document parsing (parsed/endOfStream/stalled)
- `ContinuationCheck`: plain scalar continuation classification

See ANALYSIS.md §2.F and §6 table.
-/
inductive FoldResult where
  /-- Successfully folded the continuation. `result` is the accumulated
      string with the fold applied (space or preserved newlines). -/
  | folded (result : String)
  /-- Found a `c-forbidden` document boundary indicator (`---` or `...`)
      at column 0 on a continuation line. The quoted scalar is unterminated.
      This is definitively invalid — not a backtracking opportunity. -/
  | forbidden (msg : String)
  deriving Repr, Nonempty

/--
Fold newlines in a quoted scalar
(§6.5, https://yaml.org/spec/1.2.2/#65-line-folding;
 §7.3.1 [112-113], https://yaml.org/spec/1.2.2/#731-double-quoted-style;
 §7.3.2 [124], https://yaml.org/spec/1.2.2/#732-single-quoted-style).

Called after `collectChars` has already consumed the line break character.
At entry, the stream is at the beginning of the next line.

YAML flow folding rules:
- Trailing whitespace on the line before the break is trimmed from `acc`
- A single line break not followed by an empty line folds to a space
- Each empty (blank) line contributes a preserved newline
- Leading whitespace on the continuation line is consumed (not content)

Before consuming whitespace on each continuation line, checks for
`c-forbidden` (§9.1.2 [206]): `---` or `...` at column 0 followed by
whitespace/newline/EOF. Returns `FoldResult.forbidden` if detected.
-/
partial def foldQuotedNewlines (acc : String) : YamlParser FoldResult := do
  -- Step 1: Trim trailing whitespace (spaces + tabs) from acc
  -- (YAML §7.3.1: "All leading and trailing white space characters
  --  on each line are excluded from the content")
  let trimmed := trimTrailingWhitespace acc
  -- Step 2: Count blank lines by consuming whitespace + newlines
  let result ← loop trimmed 0
  return result
where
  /-- Remove trailing space and tab characters from a string. -/
  trimTrailingWhitespace (s : String) : String :=
    let chars := s.toList
    let trimmed := chars.reverse.dropWhile (fun c => c == ' ' || c == '\t')
    String.ofList trimmed.reverse
  /-- Loop: skip whitespace, check for newline (blank line) or content. -/
  loop (result : String) (blankCount : Nat) : YamlParser FoldResult := do
    -- Check for c-forbidden at the start of each continuation line
    let pos ← currentPos
    if pos.col == 0 then
      let boundary ← atDocumentBoundary
      if boundary then
        return .forbidden
          s!"unterminated quoted scalar: document boundary at line {pos.line + 1}"
    -- Skip leading whitespace (spaces AND tabs) on this line
    skipHWhitespace
    -- Check if this line is blank (another newline follows)
    match ← option? newline with
    | some _ =>
      -- This was a blank line → count it and continue
      loop result (blankCount + 1)
    | none =>
      -- Found content on this line (leading whitespace already consumed)
      if blankCount > 0 then
        -- Blank lines present → preserved newlines (one per blank line)
        let mut r := result
        for _ in [:blankCount] do
          r := r.push '\n'
        return .folded r
      else
        -- No blank lines → single line break folds to a space
        return .folded (result.push ' ')

/--
Parse a double-quoted scalar
(§7.3.1, https://yaml.org/spec/1.2.2/#731-double-quoted-style).

Double-quoted scalars support escape sequences and line folding.
Returns the processed content.
-/
partial def doubleQuotedScalar : YamlParser YamlValue :=
  withErrorMessage "expected double-quoted scalar" do
    let _ ← char '"'
    let content ← collectChars ""
    return .scalar { content, style := .doubleQuoted }
where
  collectChars (acc : String) : YamlParser String := do
    match ← anyToken with
    | '"' => return acc
    | '\\' => do
        let c ← anyToken
        match c with
        | '\n' => do
            -- Escaped line break (line continuation, §5.7 [112]):
            -- backslash + newline → trim trailing ws, skip leading ws, emit nothing
            let trimmed := trimTrailingWs acc
            skipHWhitespace
            collectChars trimmed
        | '\r' => do
            -- Escaped CRLF line break
            let _ ← option? (token '\n')
            let trimmed := trimTrailingWs acc
            skipHWhitespace
            collectChars trimmed
        | _ => do
            let escaped ← processEscape c
            collectChars (acc.push escaped)
    | '\n' => do
        -- Line folding (c-forbidden checked inside foldQuotedNewlines)
        match ← foldQuotedNewlines acc with
        | .folded result => collectChars result
        | .forbidden msg =>
          setValidationError msg
          return acc
    | '\r' => do
        let _ ← option? (token '\n')  -- CRLF
        match ← foldQuotedNewlines acc with
        | .folded result => collectChars result
        | .forbidden msg =>
          setValidationError msg
          return acc
    | c => collectChars (acc.push c)
  processEscape (c : Char) : YamlParser Char := do
    match c with
    | '0'  => return '\x00'
    | 'a'  => return '\x07'
    | 'b'  => return '\x08'
    | 't'  => return '\t'
    | '\t' => return '\t'
    | 'n'  => return '\n'
    | 'v'  => return '\x0b'
    | 'f'  => return '\x0c'
    | 'r'  => return '\r'
    | 'e'  => return '\x1b'
    | ' '  => return ' '
    | '"'  => return '"'
    | '/'  => return '/'
    | '\\' => return '\\'
    | 'N'  => return '\x85'
    | '_'  => return '\xa0'
    | 'x'  => unicodeEscapeInline 2
    | 'u'  => unicodeEscapeInline 4
    | 'U'  => unicodeEscapeInline 8
    | _    =>
      -- Unknown escape: record validation error, return literal char.
      setValidationError s!"unknown escape: \\{c}"
      return c
  unicodeEscapeInline (n : Nat) : YamlParser Char := do
    let mut code : Nat := 0
    for _ in [:n] do
      let d ← Char.ASCII.hexDigit
      code := code * 16 + d.val
    if h : code.toUInt32.isValidChar then
      return ⟨code.toUInt32, h⟩
    else
      -- Invalid unicode: record validation error, return replacement char.
      setValidationError s!"invalid unicode: {code}"
      return '\uFFFD'
  /-- Trim trailing whitespace (spaces and tabs) from a string. -/
  trimTrailingWs (s : String) : String :=
    let chars := s.toList
    let trimmed := chars.reverse.dropWhile (fun c => c == ' ' || c == '\t')
    String.ofList trimmed.reverse

/-! ## Single-Quoted Scalars
  §7.3.2 (https://yaml.org/spec/1.2.2/#732-single-quoted-style) -/

/--
Parse a single-quoted scalar
(§7.3.2, https://yaml.org/spec/1.2.2/#732-single-quoted-style).

The only escape in single-quoted scalars is `''` → `'`.
Line folding follows the same rules as double-quoted scalars.
-/
partial def singleQuotedScalar : YamlParser YamlValue :=
  withErrorMessage "expected single-quoted scalar" do
    let _ ← char '\''
    let content ← collectChars ""
    return .scalar { content, style := .singleQuoted }
where
  collectChars (acc : String) : YamlParser String := do
    match ← anyToken with
    | '\'' =>
        -- Check for escaped quote ('')
        match ← option? (char '\'') with
        | some _ => collectChars (acc.push '\'')
        | none => return acc
    | '\n' => do
        -- Line folding (c-forbidden checked inside foldQuotedNewlines)
        match ← foldQuotedNewlines acc with
        | .folded result => collectChars result
        | .forbidden msg =>
          setValidationError msg
          return acc
    | '\r' => do
        let _ ← option? (token '\n')
        match ← foldQuotedNewlines acc with
        | .folded result => collectChars result
        | .forbidden msg =>
          setValidationError msg
          return acc
    | c => collectChars (acc.push c)

/-! ## Plain Scalars
  §7.3.3 (https://yaml.org/spec/1.2.2/#733-plain-style) -/

/--
Check if a character can appear in a plain scalar at this position.

YAML 1.2.2 §7.3.3 (https://yaml.org/spec/1.2.2/#733-plain-style):
Plain scalars cannot contain certain indicator
characters. In flow context, flow indicators are also forbidden.

The `#` character is only allowed if preceded by a non-space.
The `:` character is only allowed if followed by a non-space.
-/
def isPlainSafe (c : Char) (inFlow : Bool) : Bool :=
  if isLineBreak c || isWhiteSpace c then false
  else if inFlow && isFlowIndicator c then false
  else true

/--
Parse a plain (unquoted) scalar
(§7.3.3, https://yaml.org/spec/1.2.2/#733-plain-style).

Plain scalars are context-dependent. They end at:
- Flow indicators (in flow context)
- `: ` or `:` followed by whitespace/newline (mapping separator)
- ` #` (comment)
- End of line (unless the next line is indented enough for continuation)

In block context, plain scalars can span multiple lines. Continuation
lines must be more indented than `baseIndent` (the parent structure's
indentation level). Line breaks between content lines are folded to
spaces (§6.5). Empty lines produce paragraph breaks (`\n`).

In flow context, scalars are single-line (stop at flow indicators).

Parameters:
- `inFlow`: whether we're inside a flow collection (`[...]` or `{...}`)
- `baseIndent`: parent structure's indentation level (for continuation)
-/
partial def plainScalarContent (inFlow : Bool) (baseIndent : Nat) : YamlParser String :=
  withErrorMessage "expected plain scalar" do
    -- Pre-validate: check that first char can start a plain scalar.
    -- For -/?/:, also check that the next char is not whitespace/linebreak/EOF.
    -- Done in lookAhead so nothing is consumed if the start is invalid;
    -- the enclosing `first`/`<|>` sees a clean no-match.
    let validStart ← lookAhead do
      let c ← anyToken
      if !(isPlainSafe c inFlow && !isIndicator c ||
           c == '-' || c == '?' || c == ':') then
        return false
      if c == '-' || c == '?' || c == ':' then
        match ← option? anyToken with
        | some nc => return !(isWhiteSpace nc || isLineBreak nc)
        | none => return false
      return true
    if !validStart then
      -- Signal no-match via lean4-parser's combinator mechanism.
      -- `notFollowedBy (pure ())` always fails (pure always succeeds,
      -- so notFollowedBy rejects it).  This is lean4-parser's own
      -- combinator — no `throwUnexpected` in our code.
      notFollowedBy (pure ())
      return ""  -- unreachable
    -- Actually consume the first character (validated by lookAhead above)
    let first ← anyToken
    -- Collect the first line
    let firstLine ← collectPlain (String.ofList [first]) false
    let firstLine := firstLine.trimAsciiEnd.toString
    -- In flow context, allow multi-line continuation (§7.3.3)
    -- but with flow-specific termination rules
    if inFlow then
      collectFlowLines firstLine
    else
      -- In block context, check for multi-line continuation
      collectLines firstLine
where
  /-- Collect characters on a single line of a plain scalar. -/
  collectPlain (acc : String) (lastWasSpace : Bool) : YamlParser String := do
    match ← option? (lookAhead anyToken) with
    | none => return acc
    | some c =>
      if isLineBreak c then
        return acc
      else if c == '#' && lastWasSpace then
        -- ` #` starts a comment → end of plain scalar
        return acc
      else if c == ':' then
        -- Peek past `:` to check for mapping separator
        -- In flow context, `:` followed by a flow indicator is also a separator (§7.3.3)
        let isMapSep ← lookAhead do
          let _ ← anyToken  -- consume ':'
          match ← option? anyToken with
          | some nc => return (isWhiteSpace nc || isLineBreak nc || (inFlow && isFlowIndicator nc))
          | none => return true  -- `:` at EOF
        if isMapSep then
          return acc
        else
          let _ ← anyToken  -- actually consume the ':'
          collectPlain (acc.push c) false
      else if inFlow && isFlowIndicator c then
        -- Don't consume the flow indicator — caller needs it
        return acc
      else if isWhiteSpace c then
        let _ ← anyToken  -- actually consume
        collectPlain (acc.push c) true
      else
        let _ ← anyToken  -- actually consume
        collectPlain (acc.push c) false
  /-- Collect continuation lines, folding per YAML §6.5 line folding rules.
      Adjacent non-empty lines are joined with a space.
      Empty lines produce `\n` (paragraph breaks). -/
  collectLines (acc : String) : YamlParser String := do
    let check ← checkContinuation baseIndent
    match check with
    | .notContinuing => return acc
    | .sequenceMarker => return acc
    | .mappingEntry => return acc
    | .plainContinuation =>
      -- Consume the newline and leading whitespace
      newline
      skipHWhitespace
      -- Collect the next line
      let line ← collectPlain "" false
      let line := line.trimAsciiEnd.toString
      if line.isEmpty then
        -- Degenerate: empty content line → treat as end
        return acc
      -- Space-fold: join with a single space
      collectLines (acc ++ " " ++ line)
    | .afterEmpty emptyCount =>
      -- Consume the newline
      newline
      -- Skip the empty/blank lines (consume them)
      consumeEmptyLines emptyCount
      -- Consume indentation on the content line
      skipHWhitespace
      -- Collect the next line
      let line ← collectPlain "" false
      let line := line.trimAsciiEnd.toString
      if line.isEmpty then
        return acc
      -- Paragraph break: each empty line produces a \n
      let breaks := String.ofList (List.replicate emptyCount '\n')
      collectLines (acc ++ breaks ++ line)
  /-- Consume n empty/blank lines (newlines already counted by checkContinuation). -/
  consumeEmptyLines (n : Nat) : YamlParser Unit := do
    for _ in [:n] do
      skipSpaces
      let _ ← option? newline
  /-- Collect continuation lines in **flow** context (§7.3.3).
      Flow plain scalars can span multiple lines.  Continuation rules are
      simpler than block: no indentation threshold, but lines starting with
      a flow indicator (`,`, `[`, `]`, `{`, `}`) terminate the scalar.
      Lines are space-folded (joined with a single space). -/
  collectFlowLines (acc : String) : YamlParser String := do
    -- Must be at a line break to continue
    match ← option? (lookAhead newline) with
    | none => return acc
    | some _ =>
      -- Look ahead past the newline + whitespace to see what's on the next line
      let continues ← lookAhead do
        newline
        -- Skip blank lines (flow continuation ignores them as space-fold)
        let mut emptyLines := 0
        let mut loop := true
        while loop do
          skipSpaces
          match ← option? (lookAhead newline) with
          | some _ => newline; emptyLines := emptyLines + 1
          | none => loop := false
        skipSpaces
        -- Check what the first non-whitespace char on the content line is
        match ← option? (lookAhead anyToken) with
        | none => return false  -- EOF ends the scalar
        | some c =>
          -- Flow indicators end the scalar
          if isFlowIndicator c then return false
          -- Document boundaries end the scalar
          if c == '-' || c == '.' then
            let atBound ← atDocumentBoundary
            if atBound then return false
          return true
      if !continues then return acc
      -- Actually consume the newline + whitespace
      newline
      -- Consume any blank lines
      let mut emptyLines := 0
      let mut loop := true
      while loop do
        skipSpaces
        match ← option? (lookAhead newline) with
        | some _ => newline; emptyLines := emptyLines + 1
        | none => loop := false
      skipHWhitespace
      -- Collect next line's content
      let line ← collectPlain "" false
      let line := line.trimAsciiEnd.toString
      if line.isEmpty then return acc
      -- Space-fold or paragraph-break
      if emptyLines > 0 then
        let breaks := String.ofList (List.replicate emptyLines '\n')
        collectFlowLines (acc ++ breaks ++ line)
      else
        collectFlowLines (acc ++ " " ++ line)

/--
Parse a plain scalar (single-line only, for use as mapping key).

Mapping keys must be single-line per YAML 1.2.2 §7.3.3.
-/
partial def plainScalarSingleLine (inFlow : Bool) : YamlParser String :=
  withErrorMessage "expected plain scalar" do
    -- Pre-validate: same lookAhead pattern as plainScalarContent.
    let validStart ← lookAhead do
      let c ← anyToken
      if !(isPlainSafe c inFlow && !isIndicator c ||
           c == '-' || c == '?' || c == ':') then
        return false
      if c == '-' || c == '?' || c == ':' then
        match ← option? anyToken with
        | some nc => return !(isWhiteSpace nc || isLineBreak nc)
        | none => return false
      return true
    if !validStart then
      notFollowedBy (pure ())
      return ""  -- unreachable
    let first ← anyToken
    let rest ← collectPlain (String.ofList [first]) false
    return rest.trimAsciiEnd.toString
where
  collectPlain (acc : String) (lastWasSpace : Bool) : YamlParser String := do
    match ← option? (lookAhead anyToken) with
    | none => return acc
    | some c =>
      if isLineBreak c then
        return acc
      else if c == '#' && lastWasSpace then
        return acc
      else if c == ':' then
        -- In flow context, `:` followed by a flow indicator is also a separator (§7.3.3)
        let isMapSep ← lookAhead do
          let _ ← anyToken
          match ← option? anyToken with
          | some nc => return (isWhiteSpace nc || isLineBreak nc || (inFlow && isFlowIndicator nc))
          | none => return true
        if isMapSep then
          return acc
        else
          let _ ← anyToken
          collectPlain (acc.push c) false
      else if inFlow && isFlowIndicator c then
        return acc
      else if isWhiteSpace c then
        let _ ← anyToken
        collectPlain (acc.push c) true
      else
        let _ ← anyToken
        collectPlain (acc.push c) false

/--
Parse a plain scalar and wrap it as a YamlValue.

In block context, supports multi-line continuation with line folding.
The `baseIndent` parameter is the parent structure's indentation level;
continuation lines must be strictly more indented.

In flow context, scalars are single-line.
-/
partial def plainScalar (inFlow : Bool) (baseIndent : Nat := 0) : YamlParser YamlValue := do
  let content ← plainScalarContent inFlow baseIndent
  if content.isEmpty then
    -- Defensive: should never happen since plainScalarContent's first char
    -- was validated by lookAhead.  Record as validation error.
    setValidationError "internal: empty plain scalar content"
    return .null
  return .scalar { content, style := .plain }

/-! ## Block Scalars
  §8.1 (https://yaml.org/spec/1.2.2/#81-block-scalar-styles) -/

/-- Chomping behavior for block scalars -/
inductive ChompIndicator where
  | strip  -- `-`: remove all trailing newlines
  | clip   -- default: single trailing newline
  | keep   -- `+`: keep all trailing newlines
  deriving Repr, BEq

/--
Parse the block scalar header
(§8.1.1, https://yaml.org/spec/1.2.2/#811-block-scalar-headers).

The header follows the `|` or `>` indicator:
```
| or >           # chomp = clip (default)
|- or >-         # chomp = strip
|+ or >+         # chomp = keep
|2 or >2         # explicit indentation
|2- or >-2       # both explicit indentation and chomp
```

Returns `(indentation, chomp)` where indentation is `none` for auto-detect.
-/
def blockScalarHeader : YamlParser (Option Nat × ChompIndicator) := do
  let mut indent : Option Nat := none
  let mut chomp := ChompIndicator.clip
  -- Parse optional indentation indicator and chomp indicator (in any order).
  -- Use lookAhead to peek without consuming, then consume only valid header chars.
  for _ in [:2] do
    match ← option? (lookAhead anyToken) with
    | some '-' => let _ ← anyToken; chomp := .strip
    | some '+' => let _ ← anyToken; chomp := .keep
    | some c =>
      if c >= '1' && c <= '9' then
        let _ ← anyToken
        indent := some (c.toNat - '0'.toNat)
      else
        -- Not a header character; lookAhead did not consume it
        break
    | none => pure ()
  -- Skip trailing whitespace and optional comment
  skipTrailing
  -- Must have a newline (or EOF) after header
  let _ ← option? newline
  return (indent, chomp)

/--
Auto-detect the indentation level of a block scalar.

YAML 1.2.2 §8.1.3 (https://yaml.org/spec/1.2.2/#813-folded-style):
The indentation is determined by the first non-empty line.
Skip blank lines to find the first content line.
Returns the number of leading spaces on that line.
-/
partial def autoDetectIndent (minIndent : Nat) : YamlParser Nat :=
  lookAhead do
    -- Skip blank lines
    loop
where
  loop : YamlParser Nat := do
    let col ← currentCol
    -- Count spaces
    let spaces ← count (token ' ')
    let totalCol := col + spaces
    match ← option? newline with
    | some _ =>
      -- Empty line, continue looking
      loop
    | none =>
      -- Found content line
      if totalCol >= minIndent then
        return totalCol
      else
        return minIndent

/--
Parse block scalar content lines.

Each content line must be indented at exactly `indent` spaces
(relative to the start of the block).
Empty lines (with fewer spaces) are preserved as newlines.

Returns the raw content string.
-/
partial def blockScalarContent (indent : Nat) : YamlParser String := do
  collectLines "" true
where
  collectLines (acc : String) (first : Bool) : YamlParser String := do
    -- Try to read the next line
    match ← option? (blockScalarLine indent first) with
    | some line =>
      let acc' := if first then line else acc ++ "\n" ++ line
      collectLines acc' false
    | none =>
      return acc

  blockScalarLine (indent : Nat) (_first : Bool) : YamlParser String := do
    -- Check for blank line
    match ← option? (lookAhead newline) with
    | some _ =>
      newline
      return ""
    | none =>
      -- Must have at least `indent` spaces
      consumeIndent indent
      -- Collect the rest of the line
      let content ← takeLineContent
      return content

  takeLineContent : YamlParser String := do
    let mut acc := ""
    let mut done := false
    while !done do
      match ← option? anyToken with
      | some c =>
        if isLineBreak c then
          done := true
        else
          acc := acc.push c
      | none => done := true
    return acc

/--
Apply chomping to block scalar content.

- **strip**: Remove all trailing newlines
- **clip**: Keep exactly one trailing newline
- **keep**: Keep all trailing newlines
-/
def applyChomp (content : String) (chomp : ChompIndicator) : String :=
  match chomp with
  | .strip => content.trimAsciiEnd.toString
  | .clip =>
    let trimmed := content.trimAsciiEnd.toString
    if trimmed.isEmpty then "" else trimmed.push '\n'
  | .keep => content

/--
Process literal block scalar content
(§8.1.2, https://yaml.org/spec/1.2.2/#812-literal-style).

Literal scalars preserve line breaks as-is.
-/
def processLiteral (raw : String) : String := raw

/--
Process folded block scalar content
(§8.1.3, https://yaml.org/spec/1.2.2/#813-folded-style).

Folded scalars replace single line breaks between content lines with spaces.
Empty lines (producing double newlines) are preserved.
Lines with extra indentation (more-indented) preserve their line break.
-/
def processFolded (raw : String) : String :=
  let lines := raw.splitOn "\n"
  go lines "" true
where
  go : List String → String → Bool → String
  | [], acc, _ => acc
  | [last], acc, first =>
    if first then last
    else if last.isEmpty then acc
    else acc ++ " " ++ last
  | line :: rest, acc, first =>
    if first then
      go rest line false
    else if line.isEmpty then
      -- Empty line: preserve newline
      go rest (acc.push '\n') false
    else if line.front == ' ' then
      -- More-indented line: preserve newline
      go rest (acc ++ "\n" ++ line) false
    else
      -- Normal fold: join with space
      go rest (acc ++ " " ++ line) false

/--
Parse a block scalar (literal `|` or folded `>`).

YAML 1.2.2 §8.1 (https://yaml.org/spec/1.2.2/#81-block-scalar-styles):
Block scalars begin with a `|` (literal) or `>`
(folded) indicator, followed by an optional header specifying
indentation and chomping behavior.
-/
partial def blockScalar (parentIndent : Nat) : YamlParser YamlValue :=
  withErrorMessage "expected block scalar" do
    -- Parse the indicator
    let indicator ← first [char '|', char '>']
    let style := if indicator == '|' then ScalarStyle.literal else ScalarStyle.folded
    -- Parse header
    let (explicitIndent, chomp) ← blockScalarHeader
    -- Determine actual indentation
    let indent ← match explicitIndent with
      | some n => pure (parentIndent + n)
      | none => autoDetectIndent (parentIndent + 1)
    -- Parse content
    let raw ← blockScalarContent indent
    -- Apply style-specific processing
    let processed := match style with
      | .literal => processLiteral raw
      | .folded => processFolded raw
      | _ => raw  -- unreachable but Lean needs it
    -- Apply chomping
    let content := applyChomp processed chomp
    return .scalar { content, style }

end Lean4Yaml.Parse
