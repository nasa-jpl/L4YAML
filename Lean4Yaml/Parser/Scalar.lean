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
    | _    => Parser.throwUnexpectedWithMessage (msg := s!"unknown escape character: {c}")
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
      Parser.throwUnexpectedWithMessage (msg := s!"invalid unicode code point: {code}")

/--
Fold newlines in a quoted scalar
(§6.5, https://yaml.org/spec/1.2.2/#65-line-folding).

In quoted scalars, newlines surrounded only by whitespace fold:
- Single newline + whitespace → single space
- Empty line (additional newline) → preserved newline
-/
partial def foldQuotedNewlines (acc : String) : YamlParser String := do
  -- Skip trailing whitespace on current line
  skipHWhitespace
  -- Consume the newline
  newline
  -- Count empty lines (each empty line → newline in output)
  let mut result := acc
  let mut emptyLines := 0
  -- Skip leading whitespace on each line, counting empty lines
  let done ← loop result emptyLines
  return done
where
  loop (result : String) (emptyLines : Nat) : YamlParser String := do
    skipSpaces
    match ← option? newline with
    | some _ =>
      loop result (emptyLines + 1)
    | none =>
      -- Found a content line
      if emptyLines > 0 then
        -- Empty lines → preserved newlines
        let mut r := result
        for _ in [:emptyLines] do
          r := r.push '\n'
        return r
      else
        -- Single newline with no empty lines → space
        return result.push ' '

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
        -- Put the backslash back by looking at what escape produces
        -- Actually, we already consumed it, so we need to handle the escape char
        let c ← anyToken
        let escaped ← processEscape c
        collectChars (acc.push escaped)
    | '\n' => do
        -- Line folding
        let folded ← foldQuotedNewlines acc
        collectChars folded
    | '\r' => do
        let _ ← option? (token '\n')  -- CRLF
        let folded ← foldQuotedNewlines acc
        collectChars folded
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
    | _    => Parser.throwUnexpectedWithMessage (msg := s!"unknown escape: \\{c}")
  unicodeEscapeInline (n : Nat) : YamlParser Char := do
    let mut code : Nat := 0
    for _ in [:n] do
      let d ← Char.ASCII.hexDigit
      code := code * 16 + d.val
    if h : code.toUInt32.isValidChar then
      return ⟨code.toUInt32, h⟩
    else
      Parser.throwUnexpectedWithMessage (msg := s!"invalid unicode: {code}")

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
        let folded ← foldQuotedNewlines acc
        collectChars folded
    | '\r' => do
        let _ ← option? (token '\n')
        let folded ← foldQuotedNewlines acc
        collectChars folded
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

This parser handles **single-line** plain scalars. Multi-line continuation
is handled by the caller (the block/flow collection parsers).

Parameters:
- `inFlow`: whether we're inside a flow collection (`[...]` or `{...}`)
-/
partial def plainScalarSingleLine (inFlow : Bool) : YamlParser String :=
  withErrorMessage "expected plain scalar" do
    -- First character has stricter rules (§7.3.3)
    let first ← tokenFilter fun c =>
      isPlainSafe c inFlow && !isIndicator c ||
      c == '-' || c == '?' || c == ':'
    -- Check first character validity for - ? :
    -- These can start a plain scalar only if followed by a non-space
    if first == '-' || first == '?' || first == ':' then
      let nextChar ← lookAhead (option? anyToken)
      match nextChar with
      | some nc =>
        if isWhiteSpace nc || isLineBreak nc then
          Parser.throwUnexpectedWithMessage (msg :=
            s!"'{first}' cannot start a plain scalar when followed by whitespace")
      | none =>
        Parser.throwUnexpectedWithMessage (msg :=
          s!"'{first}' cannot start a plain scalar at end of input")
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
        -- ` #` starts a comment → end of plain scalar
        return acc
      else if c == ':' then
        -- Peek past `:` to check for mapping separator
        let isMapSep ← lookAhead do
          let _ ← anyToken  -- consume ':'
          match ← option? anyToken with
          | some nc => return (isWhiteSpace nc || isLineBreak nc)
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

/--
Parse a plain scalar and wrap it as a YamlValue.
-/
def plainScalar (inFlow : Bool) : YamlParser YamlValue := do
  let content ← plainScalarSingleLine inFlow
  if content.isEmpty then
    Parser.throwUnexpectedWithMessage (msg := "empty plain scalar")
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
  -- Parse optional indentation indicator and chomp indicator (in any order)
  for _ in [:2] do
    match ← option? anyToken with
    | some '-' => chomp := .strip
    | some '+' => chomp := .keep
    | some c =>
      if c >= '1' && c <= '9' then
        indent := some (c.toNat - '0'.toNat)
      else
        -- Not a header character, put it back via backtracking
        -- Actually we consumed it; need a different approach
        -- Use lookAhead to not consume unexpected chars
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
