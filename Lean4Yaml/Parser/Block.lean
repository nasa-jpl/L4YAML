/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Anchor
import Lean4Yaml.Parser.Tag
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
Dispatch to the appropriate parser based on the first character.

Returns `DispatchResult` to make three-valued semantics explicit
(see ANALYSIS.md §2.A and LEAN4_STYLE.md § "Parser Error Design"):
- `.matched val`: a parser consumed input and produced a value
- `.noMatch`: no parser recognized the input (currently unreachable since
  plain scalar is the fallback, but present for structural completeness)
- `.invalid msg`: input was recognized but structurally invalid

Dispatch order:
1. Flow collections (`[`, `{`)
2. Block scalar indicators (`|`, `>`)
3. Quoted scalars (`"`, `'`)
4. Block collections detected by structural indicators
5. Plain scalars (fallback)

This is the shared dispatch logic for both `blockValue` and
`blockValueSameLine`, eliminating the duplicated match statement.
-/
partial def dispatchByChar (contentIndent : Nat) : YamlParser (DispatchResult YamlValue) := do
  let c ← lookAhead anyToken
  match c with
  | '[' => return .matched (← flowSequence)
  | '{' => return .matched (← flowMapping)
  | '|' => return .matched (← blockScalar contentIndent)
  | '>' => return .matched (← blockScalar contentIndent)
  | '"' => return .matched (← doubleQuotedScalar)
  | '\'' => return .matched (← singleQuotedScalar)
  | '&' => do
    -- Anchor prefix: parse name, then parse the following value.
    -- The value may be on the same line or the next line(s).
    let name ← parseAnchorPrefix
    -- Check for tag after anchor: `&anchor !tag value` (§6.9)
    let tagName ← do
      match ← option? (lookAhead (token '!')) with
      | some _ => pure (some (← parseTagPrefix))
      | none => pure none
    -- Check if the actual value is on the next line
    match ← option? (lookAhead anyToken) with
    | some c =>
      if isLineBreak c then
        -- Value on next line: use blockValue which handles
        -- blank lines, indentation, and dispatching.
        -- blockValue returns Option — none means under-indented.
        let bv ← blockValue contentIndent
        let val := bv.getD .null
        let val := match tagName with | some t => val.withTag t | none => val
        storeAnchor name val
        return .matched val
      else
        -- Value on same line: dispatch normally
        let result ← dispatchByChar contentIndent
        match result with
        | .matched val =>
          let val := match tagName with | some t => val.withTag t | none => val
          storeAnchor name val
          return .matched val
        | other => return other
    | none =>
      -- Anchor at end of input: the anchored node is null
      let val := match tagName with
        | some t => YamlValue.null.withTag t
        | none => YamlValue.null
      storeAnchor name val
      return .matched val
  | '*' => do
    -- Alias: resolve to previously anchored value
    let val ← parseAlias
    return .matched val
  | '!' => do
    -- Tag prefix: parse tag, then parse the following value.
    -- Handles all forms: `!<uri>`, `!!type`, `!local`, `!handle!suffix`
    let tag ← parseTagPrefix
    -- Check for anchor after tag: `!tag &anchor value` (§6.9)
    let anchorName ← do
      match ← option? (lookAhead (token '&')) with
      | some _ => pure (some (← parseAnchorPrefix))
      | none => pure none
    -- Check if the actual value is on the next line
    match ← option? (lookAhead anyToken) with
    | some c =>
      if isLineBreak c then
        -- blockValue returns Option — none means under-indented.
        let bv ← blockValue contentIndent
        let val := bv.getD .null
        let val := val.withTag tag
        match anchorName with
        | some name => storeAnchor name val
        | none => pure ()
        return .matched val
      else
        let result ← dispatchByChar contentIndent
        match result with
        | .matched val =>
          let val := val.withTag tag
          match anchorName with
          | some name => storeAnchor name val
          | none => pure ()
          return .matched val
        | other => return other
    | none =>
      let val := YamlValue.null.withTag tag
      match anchorName with
      | some name => storeAnchor name val
      | none => pure ()
      return .matched val
  | '?' => do
    -- Explicit key indicator (§8.2.2, https://yaml.org/spec/1.2.2/#822-block-mappings)
    -- `?` followed by whitespace/newline/EOF indicates an explicit mapping key.
    -- `?` followed by non-whitespace is a plain scalar starting with `?`.
    let isExplicitKey ← lookAhead do
      let _ ← char '?'
      match ← option? anyToken with
      | some c => return isWhiteSpace c || isLineBreak c
      | none => return true
    if isExplicitKey then
      match ← blockMapping contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      let baseIndent := if contentIndent > 0 then contentIndent - 1 else 0
      return .matched (← plainScalar (inFlow := false) (baseIndent := baseIndent))
  | '-' => do
    -- Could be a block sequence indicator or a plain scalar starting with `-`
    let isSeq ← lookAhead do
      let _ ← char '-'
      match ← option? anyToken with
      | some c => return isWhiteSpace c || isLineBreak c
      | none => return true
    if isSeq then
      match ← blockSequence contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      -- baseIndent for continuation is the parent structure's indent level.
      -- contentIndent = parentIndent + 1, so baseIndent = contentIndent - 1.
      -- For top-level (contentIndent = 0), baseIndent = 0 means col > 0 required.
      let baseIndent := if contentIndent > 0 then contentIndent - 1 else 0
      return .matched (← plainScalar (inFlow := false) (baseIndent := baseIndent))
  | _ => do
    -- Could be a block mapping or a plain scalar
    let isMap ← lookAhead do
      detectMappingKey (inFlow := false)
    if isMap then
      match ← blockMapping contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      let baseIndent := if contentIndent > 0 then contentIndent - 1 else 0
      return .matched (← plainScalar (inFlow := false) (baseIndent := baseIndent))

/--
Parse any YAML value in block context.

The `minIndent` parameter specifies the minimum indentation level
for this value's content. Content at or below this level belongs
to a parent structure.

Returns `Option YamlValue`:
- `some val`: successfully parsed a value
- `none`: no value at this indentation level (content is under-indented
  or absent — belongs to a parent structure)

For `DispatchResult.invalid` from `dispatchByChar`, the validation error
is recorded in the stream (survives backtracking) and `none` is returned.

**Pre-condition**: stream is positioned after any leading structure indicators.
**Post-condition**: if `some val`, input was consumed and `val` is the parsed
  block value.  If `none`, no content was consumed at this indent level.
  If `dispatchByChar` returned `.invalid`, `stream'.validationError ≠ none`.
-/
partial def blockValue (minIndent : Nat) : YamlParser (Option YamlValue) := do
  skipBlankLines
  skipHWhitespace
  let col ← currentCol
  -- Content below minimum indentation belongs to a parent structure.
  -- This is a structural decision, not an error.
  if col < minIndent then
    return none
  let result ← dispatchByChar col
  match result with
  | .matched val => return some val
  | .noMatch => return none
  | .invalid msg =>
    setValidationError msg
    return none

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
partial def blockSequence (minIndent : Nat) : YamlParser (Option YamlValue) :=
  withErrorMessage "expected block sequence" do
    -- Detect the indentation of the first `-`
    skipBlankLines
    let seqIndent ← currentCol
    if seqIndent < minIndent then
      return none
    let items ← blockSequenceItems seqIndent #[]
    return some (.sequence .block items)

/--
Parse block sequence items at a fixed indentation level.
-/
partial def blockSequenceItems (seqIndent : Nat) (acc : Array YamlValue) :
    YamlParser (Array YamlValue) := do
  skipBlankLines
  -- Consume leading indentation to reach content
  skipHWhitespace
  -- Check if the next line starts at the sequence indentation
  let col ← currentCol
  if col != seqIndent then
    -- Detect wrongly-indented sequence indicators (ANALYSIS.md §2.A).
    -- Only checks over-indented (col > seqIndent); under-indented belongs
    -- to a parent structure and is handled by returning acc.
    validateNoWrongIndentSeq seqIndent col
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
      let bv ← blockValue contentIndent
      pure (bv.getD .null)
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

Delegates to `dispatchByChar`, sharing the dispatch logic with `blockValue`.
Handles `DispatchResult` directly — no `.toParser` conversion.

**Post-condition**: always returns a `YamlValue` (`.null` for noMatch/invalid).
  If `.invalid`, `stream'.validationError ≠ none`.
-/
partial def blockValueSameLine (_startCol : Nat) (contentIndent : Nat) : YamlParser YamlValue := do
  let result ← dispatchByChar contentIndent
  match result with
  | .matched val => return val
  | .noMatch => return YamlValue.null
  | .invalid msg =>
    setValidationError msg
    return YamlValue.null

/--
Parse a block mapping
(§8.2.2, https://yaml.org/spec/1.2.2/#822-block-mappings).

Returns `Option YamlValue`:
- `some (.mapping .block pairs)`: successfully parsed
- `none`: mapping found but at wrong indentation
  (belongs to a parent structure)

**Pre-condition**: stream is at or near a mapping key.
**Post-condition**: if `some`, consumed the mapping.  If `none`,
  no input consumed at this indent level.
-/
partial def blockMapping (minIndent : Nat) : YamlParser (Option YamlValue) :=
  withErrorMessage "expected block mapping" do
    skipBlankLines
    let mapIndent ← currentCol
    if mapIndent < minIndent then
      return none
    let pairs ← blockMappingEntries mapIndent #[]
    return some (.mapping .block pairs)

/--
Parse block mapping entries at a fixed indentation level.
-/
partial def blockMappingEntries (mapIndent : Nat)
    (acc : Array (YamlValue × YamlValue)) :
    YamlParser (Array (YamlValue × YamlValue)) := do
  skipBlankLines
  -- Consume leading indentation to reach content
  skipHWhitespace
  -- Check if at the mapping indentation
  let col ← currentCol
  if col != mapIndent then
    -- Detect wrongly-indented structural indicators (ANALYSIS.md §2.A).
    validateNoWrongIndentSeq mapIndent col
    validateNoWrongIndentMap mapIndent col (detectMappingKey (inFlow := false))
    return acc
  -- Check if we're at a document boundary
  let atBoundary ← atDocumentBoundary
  if atBoundary then return acc
  -- Check for explicit key indicator `?` — this is always a valid entry start
  -- even though detectMappingKey wouldn't find a `: ` on the `?` line.
  let isExplicitKey ← lookAhead do
    match ← option? (token '?') with
    | none => pure false
    | some _ =>
      match ← option? anyToken with
      | some c => pure (isWhiteSpace c || isLineBreak c)
      | none => pure true
  if isExplicitKey then
    match ← option? (blockMappingEntry mapIndent) with
    | none => return acc
    | some entry =>
      blockMappingEntries mapIndent (acc.push entry)
  else
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
  -- (§8.2.2, https://yaml.org/spec/1.2.2/#822-block-mappings)
  match ← option? (char '?') with
  | some _ =>
    -- Complex/explicit key
    skipHWhitespace
    -- Determine if key is on same line or next line
    let hasNewlineAfterQ ← test newline
    -- Parse the key, which may be null if `?` is alone or followed by `:`
    let key ← if hasNewlineAfterQ then do
      -- Key on next line(s): check for empty key (`:` at mapIndent) first
      let isEmptyKey ← lookAhead do
        skipBlankLines
        skipHWhitespace
        let col ← currentCol
        if col != mapIndent then pure false
        else do
          match ← option? (token ':') with
          | none => pure false
          | some _ =>
            match ← option? anyToken with
            | none => pure true
            | some c => pure (isWhiteSpace c || isLineBreak c)
      if isEmptyKey then
        pure YamlValue.null
      else
        -- Key content on next line(s), use mapIndent to allow
        -- zero-indented sequences as keys (§8.2.2 BLOCK-OUT context)
        let bv ← blockValue mapIndent
        pure (bv.getD .null)
    else do
      -- Key on same line as `?`: parse at mapIndent + 1
      match ← option? (lookAhead anyToken) with
      | none => pure YamlValue.null
      | some _ =>
        let col ← currentCol
        match ← option? (blockValueSameLine col (mapIndent + 1)) with
        | some v => pure v
        | none => pure YamlValue.null
    -- Look for optional `:` at mapIndent for the value
    skipBlankLines
    skipHWhitespace
    let col ← currentCol
    let hasColon ← if col == mapIndent then do
      lookAhead do
        match ← option? (token ':') with
        | none => pure false
        | some _ =>
          match ← option? anyToken with
          | none => pure true
          | some c => pure (isWhiteSpace c || isLineBreak c)
    else
      pure false
    if hasColon then do
      let _ ← char ':'
      skipHWhitespace
      let hasNewline ← test newline
      let value ← if hasNewline then do
        -- Value on next line: use mapIndent (BLOCK-OUT context)
        -- allows sequences at mapIndent level
        let bv ← blockValue mapIndent
        pure (bv.getD .null)
      else do
        let col' ← currentCol
        blockValueSameLine col' (mapIndent + 1)
      return (key, value)
    else
      -- No `:` found — value is implicitly null
      return (key, YamlValue.null)
  | none =>
    -- Simple key
    let key ← blockMappingKey
    let _ ← char ':'
    skipHWhitespace
    -- Value could be on the same line or the next line
    let hasNewline ← test newline
    let value ← if hasNewline then
      let bv ← blockValue (mapIndent + 1)
      pure (bv.getD .null)
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
  -- Check for alias as mapping key
  match ← option? (lookAhead (token '*')) with
  | some _ => parseAlias
  | none =>
  -- Check for tag on mapping key: `!tag key: value` (§6.9)
  match ← option? (lookAhead (token '!')) with
  | some _ => do
    let tag ← parseTagPrefix
    -- Check for anchor after tag: `!tag &anchor key: value`
    let anchorName ← do
      match ← option? (lookAhead (token '&')) with
      | some _ => pure (some (← parseAnchorPrefix))
      | none => pure none
    let key ← first [
      doubleQuotedScalar,
      singleQuotedScalar,
      do
        let content ← plainMappingKey
        return YamlValue.plainScalar content
    ]
    let key := key.withTag tag
    match anchorName with
    | some name => storeAnchor name key
    | none => pure ()
    return key
  | none =>
  -- Check for anchor on mapping key
  match ← option? (lookAhead (token '&')) with
  | some _ => do
    let name ← parseAnchorPrefix
    -- Check for tag after anchor: `&anchor !tag key: value`
    let tagName ← do
      match ← option? (lookAhead (token '!')) with
      | some _ => pure (some (← parseTagPrefix))
      | none => pure none
    let key ← first [
      doubleQuotedScalar,
      singleQuotedScalar,
      do
        let content ← plainMappingKey
        return YamlValue.plainScalar content
    ]
    let key := match tagName with | some t => key.withTag t | none => key
    storeAnchor name key
    return key
  | none =>
  first [
    doubleQuotedScalar,
    singleQuotedScalar,
    do
      let content ← plainMappingKey
      return YamlValue.plainScalar content
  ]
where
  plainMappingKey : YamlParser String := do
    let mut acc := ""
    let mut done := false
    while !done do
      match ← option? (lookAhead anyToken) with
      | none => done := true
      | some ':' =>
        -- Check if followed by whitespace (mapping separator)
        let isMapSep ← lookAhead do
          let _ ← anyToken  -- consume ':'
          match ← option? anyToken with
          | some c => return (isWhiteSpace c || isLineBreak c)
          | none => return true  -- `:` at EOF
        if isMapSep then
          done := true
        else
          let _ ← anyToken  -- actually consume the ':'
          acc := acc.push ':'
      | some c =>
        if isLineBreak c then
          done := true
        else if c == '#' && acc.endsWith " " then
          -- Comment
          done := true
        else
          let _ ← anyToken  -- actually consume
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
