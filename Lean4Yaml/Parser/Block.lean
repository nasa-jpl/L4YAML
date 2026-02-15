/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Flow

/-!
# YAML Block Collection Parsers

Parsers for YAML block-style collections
(§8.2, https://yaml.org/spec/1.2.2/#82-block-collection-styles):
- Block sequences (§8.2.1, https://yaml.org/spec/1.2.2/#821-block-sequences): lines starting with `- `
- Block mappings (§8.2.2, https://yaml.org/spec/1.2.2/#822-block-mappings): lines with `key: value`

## Indentation-Based Parsing

Block collections are parsed based on indentation levels. The key design
principle here is that **indentation is always checked through the column
tracked by `YamlStream`**, never by counting spaces separately.

This directly prevents the `skipToNextLine` regression that occurred in
lean4-yaml, where a function couldn't distinguish between:
- Trailing whitespace after a value (should be ignored)
- Leading indentation on the next line (meaningful for block structure)

In this verified parser, the column is always known from the stream state.
The `consumeIndent n` combinator explicitly consumes exactly `n` spaces,
and `currentCol` reads the column without consuming anything.

## Mutual Recursion

Block values, block sequences, and block mappings are mutually recursive:
- A block sequence item can contain a block mapping
- A block mapping value can contain a block sequence
- Either can contain flow collections or scalars

We use `partial def` for now; termination proofs are separate
(`Lean4Yaml.Proofs.Termination`).
-/

namespace Lean4Yaml.Parse

open Parser
open Parser.Char
open Lean4Yaml

/-! ## Block Value Parsing -/

mutual

/--
Parse any YAML value in block context.

The `minIndent` parameter specifies the minimum indentation level
for this value's content. Content at or below this level belongs
to a parent structure.

Dispatch order:
1. Flow collections (`[`, `{`)
2. Block scalar indicators (`|`, `>`)
3. Quoted scalars (`"`, `'`)
4. Block collections detected by indentation
5. Plain scalars (fallback)
-/
partial def blockValue (minIndent : Nat) : YamlParser YamlValue :=
  withErrorMessage "expected YAML value" do
    -- Skip blank lines before the value
    skipBlankLines
    -- Peek at the first character to dispatch
    let c ← lookAhead anyToken
    match c with
    | '[' => flowSequence
    | '{' => flowMapping
    | '|' => blockScalar minIndent
    | '>' => blockScalar minIndent
    | '"' => doubleQuotedScalar
    | '\'' => singleQuotedScalar
    | '-' => do
      -- Could be a block sequence indicator or a plain scalar starting with `-`
      let isSeq ← lookAhead do
        let _ ← char '-'
        match ← option? anyToken with
        | some c => return isWhiteSpace c || isLineBreak c
        | none => return true
      if isSeq then
        blockSequence minIndent
      else
        plainScalar (inFlow := false)
    | _ => do
      -- Could be a block mapping or a plain scalar
      -- Try to detect mapping by looking for `: ` pattern
      let isMap ← lookAhead do
        detectMappingKey (inFlow := false)
      if isMap then
        blockMapping minIndent
      else
        plainScalar (inFlow := false)

/--
Parse a block sequence
(§8.2.1, https://yaml.org/spec/1.2.2/#821-block-sequences).

```yaml
- item1
- item2
- nested:
    key: value
```

Each item starts with `- ` at the same indentation level.
The content of each item is a block value indented relative to the `-`.
-/
partial def blockSequence (minIndent : Nat) : YamlParser YamlValue :=
  withErrorMessage "expected block sequence" do
    -- Detect the indentation of the first `-`
    skipBlankLines
    let seqIndent ← currentCol
    if seqIndent < minIndent then
      withErrorMessage s!"block sequence at column {seqIndent} is less than minimum indent {minIndent}" throwUnexpected
    let items ← blockSequenceItems seqIndent #[]
    return .sequence .block items

/--
Parse block sequence items at a fixed indentation level.
-/
partial def blockSequenceItems (seqIndent : Nat) (acc : Array YamlValue) :
    YamlParser (Array YamlValue) := do
  skipBlankLines
  -- Check if the next line starts at the sequence indentation
  let col ← currentCol
  if col != seqIndent then
    -- No more items at this level
    return acc
  -- Check for the `-` indicator
  match ← option? (char '-') with
  | none => return acc
  | some _ =>
    -- Must be followed by whitespace, newline, or EOF
    match ← option? (lookAhead anyToken) with
    | some c =>
      if !isWhiteSpace c && !isLineBreak c then
        -- Not a valid sequence indicator (e.g., could be `---`)
        return acc
    | none => pure ()
    -- Parse whitespace after the dash
    skipHWhitespace
    -- The content is indented relative to the dash position
    let contentIndent := seqIndent + 1
    -- Parse the item value (could be on same line or next line)
    let hasNewline ← test newline
    let item ← if hasNewline then do
      blockValue contentIndent
    else
      -- Value on same line as `-`
      let col' ← currentCol
      blockValueSameLine col' contentIndent
    blockSequenceItems seqIndent (acc.push item)

/--
Parse a block value that starts on the same line as its indicator.

For example:
```yaml
- value on same line
key: value on same line
```

The `startCol` is the column where the value starts.
The `contentIndent` is the minimum indentation for continuation lines.
-/
partial def blockValueSameLine (_startCol : Nat) (contentIndent : Nat) : YamlParser YamlValue := do
  let c ← lookAhead anyToken
  match c with
  | '[' => flowSequence
  | '{' => flowMapping
  | '|' => blockScalar contentIndent
  | '>' => blockScalar contentIndent
  | '"' => doubleQuotedScalar
  | '\'' => singleQuotedScalar
  | '-' => do
    let isSeq ← lookAhead do
      let _ ← char '-'
      match ← option? anyToken with
      | some c => return isWhiteSpace c || isLineBreak c
      | none => return true
    if isSeq then
      blockSequence contentIndent
    else
      plainScalar (inFlow := false)
  | _ => do
    let isMap ← lookAhead do
      detectMappingKey (inFlow := false)
    if isMap then
      blockMapping contentIndent
    else
      plainScalar (inFlow := false)

/--
Parse a block mapping
(§8.2.2, https://yaml.org/spec/1.2.2/#822-block-mappings).

```yaml
key1: value1
key2: value2
nested:
  inner_key: inner_value
```

Each entry has a key and value separated by `: `.
All keys at the same level must have the same indentation.
-/
partial def blockMapping (minIndent : Nat) : YamlParser YamlValue :=
  withErrorMessage "expected block mapping" do
    skipBlankLines
    let mapIndent ← currentCol
    if mapIndent < minIndent then
      withErrorMessage s!"block mapping at column {mapIndent} is less than minimum indent {minIndent}" throwUnexpected
    let pairs ← blockMappingEntries mapIndent #[]
    return .mapping .block pairs

/--
Parse block mapping entries at a fixed indentation level.
-/
partial def blockMappingEntries (mapIndent : Nat)
    (acc : Array (YamlValue × YamlValue)) :
    YamlParser (Array (YamlValue × YamlValue)) := do
  skipBlankLines
  -- Check if at the mapping indentation
  let col ← currentCol
  if col != mapIndent then
    return acc
  -- Check if we're at a document boundary
  let atBoundary ← atDocumentBoundary
  if atBoundary then return acc
  -- Try to parse a mapping entry
  match ← option? (blockMappingEntry mapIndent) with
  | none => return acc
  | some entry =>
    blockMappingEntries mapIndent (acc.push entry)

/--
Parse a single block mapping entry.

Handles both simple keys (`key: value`) and complex keys (`? key\n: value`).
-/
partial def blockMappingEntry (mapIndent : Nat) :
    YamlParser (YamlValue × YamlValue) := do
  -- Check for complex key indicator `?`
  match ← option? (char '?') with
  | some _ =>
    -- Complex key
    skipHWhitespace
    let key ← blockValue (mapIndent + 1)
    skipBlankLines
    consumeIndent mapIndent
    let _ ← char ':'
    skipHWhitespace
    let hasNewline ← test newline
    let value ← if hasNewline then
      blockValue (mapIndent + 1)
    else do
      let col ← currentCol
      blockValueSameLine col (mapIndent + 1)
    return (key, value)
  | none =>
    -- Simple key
    let key ← blockMappingKey
    let _ ← char ':'
    skipHWhitespace
    -- Value could be on the same line or the next line
    let hasNewline ← test newline
    let value ← if hasNewline then
      blockValue (mapIndent + 1)
    else do
      let col ← currentCol
      blockValueSameLine col (mapIndent + 1)
    return (key, value)

/--
Parse a simple block mapping key.

Simple keys are single-line and cannot contain certain indicators.
They end at `: ` (mapping value indicator).
-/
partial def blockMappingKey : YamlParser YamlValue := do
  first [
    doubleQuotedScalar,
    singleQuotedScalar,
    do
      -- Plain key: collect until `:`
      let content ← plainMappingKey
      return YamlValue.plainScalar content
  ]
where
  plainMappingKey : YamlParser String := do
    let mut acc := ""
    let mut done := false
    while !done do
      match ← option? anyToken with
      | none => done := true
      | some ':' =>
        -- Check if followed by whitespace (mapping separator)
        match ← lookAhead (option? anyToken) with
        | some c =>
          if isWhiteSpace c || isLineBreak c then
            done := true
          else
            acc := acc.push ':'
        | none =>
          -- End of input after `:` — it's a mapping separator
          done := true
      | some c =>
        if isLineBreak c then
          done := true
        else if c == '#' && acc.endsWith " " then
          -- Comment
          done := true
        else
          acc := acc.push c
    return acc.trimAsciiEnd.toString

/--
Detect if the current position is at a mapping key.

Looks ahead for a `key: ` or `key:\n` pattern without consuming input.
This helps disambiguate between plain scalars and block mappings.
-/
partial def detectMappingKey (inFlow : Bool) : YamlParser Bool := do
  -- Try to find `: ` or `:\n` on this line
  detectLoop
where
  detectLoop : YamlParser Bool := do
    match ← option? anyToken with
    | none => return false
    | some ':' =>
      match ← option? anyToken with
      | none => return true  -- `:` at EOF
      | some c => return (isWhiteSpace c || isLineBreak c)
    | some c =>
      if isLineBreak c then return false
      else if c == '"' || c == '\'' then return false  -- Don't scan through quotes
      else if inFlow && isFlowIndicator c then return false
      else detectLoop

end

end Lean4Yaml.Parse
