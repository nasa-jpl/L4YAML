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
import Lean4Yaml.YamlSpec

/-!
# YAML Block Collection Parsers

Parsers for YAML block-style collections.

**YAML 1.2.2**: [180]-[196] (§8.2, https://yaml.org/spec/1.2.2/#82-block-collection-styles)
- [180] c-l-block-seq(n) / [183] l+block-sequence(n) (§8.2.1)
- [184] l+block-mapping(n) (§8.2.2)
- [196] l-bare-document (§9.1.4)

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

This is the shared dispatch logic for both `blockValueImpl fuel` and
`blockValueSameLineImpl fuel`, eliminating the duplicated match statement.
-/
def dispatchByCharImpl (fuel : Nat) (contentIndent : Nat) (scalarIndent : Nat := contentIndent) : YamlParser (DispatchResult YamlValue) :=
  match fuel with
  | 0 => pure .noMatch
  | fuel + 1 => do
  -- P5 fix: handle EOF gracefully instead of crashing on `lookAhead anyToken`.
  -- At EOF, no value can be dispatched — return `.noMatch`.
  match ← option? (lookAhead anyToken) with
  | none => return .noMatch
  | some c =>
  match c with
  | '[' => do
    -- P6 fix (M2N8): flow sequence could be a mapping key (`[]: x`).
    -- Check if the flow sequence is followed by `: ` mapping separator.
    -- §7.4 / C2SP: implicit keys must not span multiple lines, so we also
    -- verify the flow collection starts and ends on the same line.
    let isMap ← lookAhead do
      let startLine ← currentLine
      let _ ← flowSequence
      let endLine ← currentLine
      if endLine != startLine then return false  -- multiline key rejected
      skipHWhitespace
      match ← option? (token ':') with
      | none => pure false
      | some _ =>
        match ← option? anyToken with
        | none => pure true
        | some c => pure (isWhiteSpace c || isLineBreak c)
    if isMap then
      match ← blockMappingImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      return .matched (← flowSequence contentIndent)
  | '{' => do
    -- P6 fix: flow mapping as mapping key (same pattern as `[`).
    -- §7.4 / C2SP: implicit keys must not span multiple lines.
    let isMap ← lookAhead do
      let startLine ← currentLine
      let _ ← flowMapping
      let endLine ← currentLine
      if endLine != startLine then return false  -- multiline key rejected
      skipHWhitespace
      match ← option? (token ':') with
      | none => pure false
      | some _ =>
        match ← option? anyToken with
        | none => pure true
        | some c => pure (isWhiteSpace c || isLineBreak c)
    if isMap then
      match ← blockMappingImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      return .matched (← flowMapping contentIndent)
  | '|' => return .matched (← blockScalar contentIndent)
  | '>' => return .matched (← blockScalar contentIndent)
  | '"' => do
    -- T3 fix (ANALYSIS.md §2.I): A line starting with `"` could be a quoted
    -- mapping key (`"key": value`).  Check for mapping pattern first; only
    -- fall back to standalone scalar if no `: ` follows the quoted string.
    -- P6 fix (DBG4): parse the COMPLETE quoted string before checking for
    -- `: `.  The old `detectMappingKeyImpl fuel` scan would find `: ` inside the
    -- quoted string content (e.g., `"a: b"`) and falsely detect a mapping.
    let isMap ← lookAhead do
      let _ ← doubleQuotedScalar
      skipHWhitespace
      match ← option? (token ':') with
      | none => pure false
      | some _ =>
        match ← option? anyToken with
        | none => pure true
        | some c => pure (isWhiteSpace c || isLineBreak c)
    if isMap then
      match ← blockMappingImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      return .matched (← doubleQuotedScalar contentIndent)
  | '\'' => do
    -- T3 fix: same logic as `"` — single-quoted keys like `'key': value`.
    -- P6 fix (DBG4): parse the complete quoted string before `:` check.
    let isMap ← lookAhead do
      let _ ← singleQuotedScalar
      skipHWhitespace
      match ← option? (token ':') with
      | none => pure false
      | some _ =>
        match ← option? anyToken with
        | none => pure true
        | some c => pure (isWhiteSpace c || isLineBreak c)
    if isMap then
      match ← blockMappingImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      return .matched (← singleQuotedScalar contentIndent)
  | '&' => do
    -- P6 fix: If `&anchor key: value` forms a mapping entry, the anchor
    -- belongs to the key scalar, not the entire mapping.  Check for
    -- mapping-key pattern first and route to blockMappingImpl fuel whose
    -- blockMappingKeyImpl fuel already handles anchor-on-key (§6.9).
    --
    -- Guarantee: `detectMappingKeyImpl fuel` is flow-aware — it skips over balanced
    -- `{...}` and `[...]` content, so `&map {a: 1, b: 2}` is correctly
    -- classified as non-mapping (no `: ` outside flow braces).
    let isMapKey ← lookAhead (detectMappingKeyImpl fuel (inFlow := false))
    if isMapKey then
      match ← blockMappingImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
    -- The value may be on the same line or the next line(s).
    let name ← parseAnchorPrefix
    -- Check for tag after anchor: `&anchor !tag value` (§6.9)
    let tagName ← do
      match ← option? (lookAhead (token '!')) with
      | some _ => pure (some (← parseTagPrefix))
      | none => pure none
    -- Check if the actual value is on the next line (or after a comment)
    -- P6 fix: handle `&anchor # comment\n value` pattern.
    skipHWhitespace
    let hasComment ← do
      match ← option? (lookAhead anyToken) with
      | some '#' => optional comment *> return; pure true
      | _ => pure false
    let atNewline := hasComment || (← do
      match ← option? (lookAhead anyToken) with
      | some c => pure (isLineBreak c)
      | none => pure true)
    -- P7 fix (SR86): §6.9.2 — an alias cannot be anchored.
    -- `&b *a` is invalid: an alias resolves to an existing node,
    -- not a new content node that can carry its own anchor.
    match ← option? (lookAhead (token '*')) with
    | some _ =>
      setValidationError "an alias (*) cannot carry an anchor (&)"
      let val ← parseAlias
      storeAnchor name val
      return .matched val
    | none => pure ()
    if atNewline then
        -- P7 check (4JVG): §6.9.2 — a node can have at most one anchor.
        -- `&outer\n  &inner value` → both anchors on same node → invalid.
        -- `&outer\n  &inner key: val` → &outer on mapping, &inner on key → valid.
        let doubleAnchor ← lookAhead do
          skipBlankLines
          skipHWhitespace
          match ← option? (char '&') with
          | some _ =>
            -- Skip anchor name characters
            dropMany (tokenFilter fun c => !isWhiteSpace c && !isLineBreak c)
            skipHWhitespace
            -- If what follows is a mapping key, the inner anchor is on
            -- a different node (the key), so it's OK.
            let isMK ← detectMappingKeyImpl fuel (inFlow := false)
            return !isMK
          | none => return false
        if doubleAnchor then
          setValidationError "a node can have at most one anchor"
        -- Value on next line: use blockValueImpl fuel which handles
        -- blank lines, indentation, and dispatching.
        -- blockValueImpl fuel returns Option — none means under-indented.
        let bv ← blockValueImpl fuel contentIndent
        let val := bv.getD .null
        let val := match tagName with | some t => val.withTag t | none => val
        storeAnchor name val
        return .matched (val.withAnchor name)
    else
        -- Value on same line: dispatch normally
        let result ← dispatchByCharImpl fuel contentIndent
        match result with
        | .matched val =>
          -- P7 check (SY6V): §8.1 — block collections after node
          -- properties require a newline separator (s-l-comments).
          -- `&anchor - seq_entry` is invalid; the block sequence must
          -- start on the next line.  Flow collections are fine inline.
          match val with
          | .sequence .block _ | .mapping .block _ _ =>
            setValidationError "block collection must start on a new line after anchor"
          | _ => pure ()
          let val := match tagName with | some t => val.withTag t | none => val
          storeAnchor name val
          return .matched (val.withAnchor name)
        | other => return other
  | '*' => do
    -- P6 fix (26DV): If `*alias : value` forms a mapping entry, the alias
    -- is the mapping key.  Check for mapping pattern first; blockMappingKeyImpl fuel
    -- already handles `*alias` as a key (§6.9.2).
    let isMapKey ← lookAhead (detectMappingKeyImpl fuel (inFlow := false))
    if isMapKey then
      match ← blockMappingImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      -- Standalone alias: resolve to previously anchored value
      let val ← parseAlias
      return .matched val
  | '!' => do
    -- P6 fix: If `!tag key: value` forms a mapping entry, the tag
    -- belongs to the key scalar, not the entire mapping.  Route to
    -- blockMappingImpl fuel whose blockMappingKeyImpl fuel handles tag-on-key (§6.9).
    --
    -- Guarantee: `detectMappingKeyImpl fuel` is flow-aware — it skips over balanced
    -- `{...}` and `[...]` content, so `!!map {a: 1}` is correctly
    -- classified as non-mapping (no `: ` outside flow braces).
    let isMapKey ← lookAhead (detectMappingKeyImpl fuel (inFlow := false))
    if isMapKey then
      match ← blockMappingImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
    -- Handles all forms: `!<uri>`, `!!type`, `!local`, `!handle!suffix`
    let tag ← parseTagPrefix
    -- Check for anchor after tag: `!tag &anchor value` (§6.9)
    let anchorName ← do
      match ← option? (lookAhead (token '&')) with
      | some _ => pure (some (← parseAnchorPrefix))
      | none => pure none
    -- Check if the actual value is on the next line (or after a comment)
    -- P6 fix (735Y): `!!map # comment` followed by block content.
    -- Skip whitespace and check for comment or newline.
    skipHWhitespace
    let hasComment ← do
      match ← option? (lookAhead anyToken) with
      | some '#' => optional comment *> return; pure true
      | _ => pure false
    let atNewline := hasComment || (← do
      match ← option? (lookAhead anyToken) with
      | some c => pure (isLineBreak c)
      | none => pure true)
    if atNewline then
        -- blockValueImpl fuel returns Option — none means under-indented.
        let bv ← blockValueImpl fuel contentIndent
        let val := bv.getD .null
        let val := val.withTag tag
        match anchorName with
        | some name => storeAnchor name val
        | none => pure ()
        let val := match anchorName with | some name => val.withAnchor name | none => val
        return .matched val
    else
        let result ← dispatchByCharImpl fuel contentIndent
        match result with
        | .matched val =>
          let val := val.withTag tag
          match anchorName with
          | some name => storeAnchor name val
          | none => pure ()
          let val := match anchorName with | some name => val.withAnchor name | none => val
          return .matched val
        | other => return other
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
      match ← blockMappingImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      -- T3 fix: `?foo: value` is a plain mapping key starting with `?`.
      -- Check for mapping pattern before falling back to plain scalar.
      let isMap ← lookAhead do detectMappingKeyImpl fuel (inFlow := false)
      if isMap then
        match ← blockMappingImpl fuel contentIndent with
        | some val => return .matched val
        | none => return .noMatch
      else
        -- P7 fix (236B): use scalarIndent (= content column from blockValueImpl fuel)
        -- for plain scalar continuation.  §8.1 flow-in-block uses n+1 for
        -- the indentation of continuation lines.
        return .matched (← plainScalar (inFlow := false) (contentIndent := scalarIndent))
  | '-' => do
    -- Could be a block sequence indicator or a plain scalar starting with `-`
    let isSeq ← lookAhead do
      let _ ← char '-'
      match ← option? anyToken with
      | some c => return isWhiteSpace c || isLineBreak c
      | none => return true
    if isSeq then
      match ← blockSequenceImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      -- T3 fix: `-foo: value` is a plain mapping key starting with `-`.
      let isMap ← lookAhead do detectMappingKeyImpl fuel (inFlow := false)
      if isMap then
        match ← blockMappingImpl fuel contentIndent with
        | some val => return .matched val
        | none => return .noMatch
      else
        -- P7 fix (236B): use scalarIndent.
        return .matched (← plainScalar (inFlow := false) (contentIndent := scalarIndent))
  | _ => do
    -- Could be a block mapping or a plain scalar
    let isMap ← lookAhead do
      detectMappingKeyImpl fuel (inFlow := false)
    if isMap then
      match ← blockMappingImpl fuel contentIndent with
      | some val => return .matched val
      | none => return .noMatch
    else
      -- P7 fix (236B): use scalarIndent.
      return .matched (← plainScalar (inFlow := false) (contentIndent := scalarIndent))

/--
Parse any YAML value in block context.

**YAML 1.2.2**: [192] s-l+block-node(n,c) / [196] l-bare-document (§8.2/§9.1.4)
- [193] s-l+block-in-block(n,c)
- [194] s-l+flow-in-block(n)
- [159] s-b-block-scalar(n,c)

The `minIndent` parameter specifies the minimum indentation level
for this value's content. Content at or below this level belongs
to a parent structure.

Returns `Option YamlValue`:
- `some val`: successfully parsed a value
- `none`: no value at this indentation level (content is under-indented
  or absent — belongs to a parent structure)

For `DispatchResult.invalid` from `dispatchByCharImpl fuel`, the validation error
is recorded in the stream (survives backtracking) and `none` is returned.

**Pre-condition**: stream is positioned after any leading structure indicators.
**Post-condition**: if `some val`, input was consumed and `val` is the parsed
  block value.  If `none`, no content was consumed at this indent level.
  If `dispatchByCharImpl fuel` returned `.invalid`, `stream'.validationError ≠ none`.
-/
@[yaml_spec "8.2" 192 "s-l+block-node(n,c)"]
def blockValueImpl (fuel : Nat) (minIndent : Nat) (propertyMinIndent : Nat := minIndent)
    : YamlParser (Option YamlValue) :=
  match fuel with
  | 0 => pure none
  | fuel + 1 => do
  skipBlankLines
  -- P10b: §6.1 — tabs are not allowed for indentation
  checkIndentForTabs minIndent
  skipHWhitespace
  let col ← currentCol
  -- Content below minimum indentation belongs to a parent structure.
  -- This is a structural decision, not an error.
  -- P6 fix (57H4): YAML §8.2.1 seq-spaces(n, block-out) = n-1.
  -- A block sequence indicator `-` is allowed one column before the normal
  -- minimum indent.  This is the compact notation where `-` at column n
  -- is valid for a parent at column n+1, because `-` plus space constitute
  -- the content's indentation.  We compute an effective indent that is
  -- reduced by 1 when a sequence indicator is found at that position.
  let effectiveMinIndent ← do
    if col < minIndent then
      if col + 1 == minIndent then
        let isSeq ← lookAhead do
          match ← option? anyToken with
          | some '-' =>
            match ← option? anyToken with
            | some c => pure (isWhiteSpace c || isLineBreak c)
            | none => pure true  -- `-` at EOF
          | _ => pure false
        if isSeq then pure col  -- seq-spaces exception
        else return none
      else
        return none
    else
      pure minIndent
  -- P6 fix: Check for document boundary (`---` or `...`) BEFORE dispatching.
  -- Without this, `---` is sent to the `-` branch of `dispatchByCharImpl fuel` where
  -- `isSeq` is false (`-` followed by `-`, not whitespace), causing `---`
  -- to be parsed as a plain scalar.  Fixes NKF9 (multi-document empty keys).
  let atBoundary ← lookAhead (atDocumentBoundary)
  if atBoundary then
    return none
  -- P10b (G9HC): §8.2.2 — node properties (anchors `&`, tags `!`) in a
  -- block‐collection value must be at indent n+1.  When called from a
  -- mapping value, `propertyMinIndent = mapIndent + 1`.  The default
  -- (`minIndent`) is benign for other contexts.
  let isProperty ← lookAhead do
    match ← option? anyToken with
    | some '&' | some '!' => pure true
    | _ => pure false
  if isProperty && col < propertyMinIndent then
    setValidationError "node property must be indented past parent structure (§8.2.2)"
  -- T1 fix (ANALYSIS.md §2.I): pass effective indent — the structural
  -- indentation context.  After `--- >`, col = 4 but minIndent = 0,
  -- and block scalars need the structural context to compute content
  -- indentation correctly (spec's n parameter).
  -- P7 fix (236B): pass the content column as `scalarIndent` so that
  -- plain scalar continuation correctly uses the first content line's
  -- indentation.  §8.1 `s-l-flow-in-block(n)` uses `n+1` which in
  -- practice means the content column.  This prevents `foo:\n  bar\ninvalid`
  -- from folding `invalid` (at col 0) into the scalar `bar` (at col 2).
  let result ← dispatchByCharImpl fuel effectiveMinIndent (scalarIndent := col)
  match result with
  | .matched val => return some val
  | .noMatch => return none
  | .invalid msg =>
    setValidationError msg
    return none

/--
Parse a block sequence.

**YAML 1.2.2**: [183] l+block-sequence(n) (§8.2.1, https://yaml.org/spec/1.2.2/#821-block-sequences)
- [180] c-l-block-seq-entry(n)
- [181] s-b-block-seq(n): seq-spaces(n,c) = n-1 for BLOCK-OUT, n for BLOCK-IN

```yaml
- item1
- item2
- nested:
    key: value
```

Each item starts with `- ` at the same indentation level.
The content of each item is a block value indented relative to the `-`.
-/
@[yaml_spec "8.2.1" 183 "l+block-sequence(n)"]
def blockSequenceImpl (fuel : Nat) (minIndent : Nat) : YamlParser (Option YamlValue) :=
  match fuel with
  | 0 => pure none
  | fuel + 1 =>
  withErrorMessage "expected block sequence" do
    -- Detect the indentation of the first `-`
    skipBlankLines
    let seqIndent ← currentCol
    if seqIndent < minIndent then
      return none
    let items ← blockSequenceItemsImpl fuel seqIndent #[]
    return some (.sequence .block items)

/--
Parse block sequence items at a fixed indentation level.

**YAML 1.2.2**: [180] c-l-block-seq-entry(n) (§8.2.1)
-/
@[yaml_spec "8.2.1" 180 "c-l-block-seq-entry(n)"]
def blockSequenceItemsImpl (fuel : Nat) (seqIndent : Nat) (acc : Array YamlValue) :
    YamlParser (Array YamlValue) :=
  match fuel with
  | 0 => pure acc
  | fuel + 1 => do
  skipBlankLines
  -- P10b: §6.1 — tabs are not allowed for indentation
  checkIndentForTabs seqIndent
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
  -- P5 fix: check for document boundary (`---` or `...`) before consuming
  -- the `-` indicator.  Without this, `blockSequenceItemsImpl fuel` consumes the
  -- first `-` of `---`, corrupting the document start marker.
  let atBoundary ← atDocumentBoundary
  if atBoundary then return acc
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
    -- P10b: §6.1 — check for tabs in separation whitespace after `-`.
    -- If the whitespace contains a tab AND the next content is a block
    -- structure indicator (dash+ws, question+ws, or mapping key),
    -- the tab is creating indentation for a nested block, which violates §6.1.
    -- Tabs followed by plain content (like `-\t-1`) are fine (separation ws).
    let hasSepTab ← hasTabInWhitespace
    skipHWhitespace
    if hasSepTab then do
      let isBlockIndicator ← lookAhead do
        match ← option? anyToken with
        | some '-' | some '?' =>
          match ← option? anyToken with
          | none => pure true
          | some c => pure (isWhiteSpace c || isLineBreak c)
        | _ => pure false
      let isMK ← lookAhead (detectMappingKeyImpl fuel (inFlow := false))
      if isBlockIndicator || isMK then
        setValidationError "tabs are not allowed for indentation (YAML 1.2.2 §6.1)"
    -- The content is indented relative to the dash position
    let contentIndent := seqIndent + 1
    -- P6 fix (W42U): handle comment at value position.
    -- `- # Empty` means the value is null (or on the next line).
    -- Consume the comment so it doesn't confuse dispatchByCharImpl fuel.
    let hasComment ← do
      match ← option? (lookAhead anyToken) with
      | some '#' => optional comment *> return; pure true
      | _ => pure false
    -- Parse the item value (could be on same line or next line)
    let hasNewline := hasComment || (← test newline)
    let item ← if hasNewline then do
      let bv ← blockValueImpl fuel contentIndent
      pure (bv.getD .null)
    else
      -- Value on same line as `-`
      let col' ← currentCol
      blockValueSameLineImpl fuel col' contentIndent
    blockSequenceItemsImpl fuel seqIndent (acc.push item)

/--
Parse a block value that starts on the same line as its indicator.

For example:
```yaml
- value on same line
key: value on same line
```

The `startCol` is the column where the value starts.
The `contentIndent` is the minimum indentation for continuation lines.

Delegates to `dispatchByCharImpl fuel`, sharing the dispatch logic with `blockValueImpl fuel`.
Handles `DispatchResult` directly — no `.toParser` conversion.

**Post-condition**: always returns a `YamlValue` (`.null` for noMatch/invalid).
  If `.invalid`, `stream'.validationError ≠ none`.
-/
def blockValueSameLineImpl (fuel : Nat) (_startCol : Nat) (contentIndent : Nat) : YamlParser YamlValue :=
  match fuel with
  | 0 => pure .null
  | fuel + 1 => do
  let result ← dispatchByCharImpl fuel contentIndent
  match result with
  | .matched val =>
    -- P7 fix (SU5Z): §6.7 — after a value on the same line, `#` must be
    -- preceded by whitespace.  Catches `key: "value"#` where `#`
    -- immediately follows the trailing `"` with no space.
    let preCol ← currentCol
    skipHWhitespace
    let postCol ← currentCol
    match ← option? (lookAhead anyToken) with
    | some '#' =>
      if postCol == preCol then
        setValidationError "comment '#' must be preceded by whitespace (§6.7)"
    | _ => pure ()
    return val
  | .noMatch => return YamlValue.null
  | .invalid msg =>
    setValidationError msg
    return YamlValue.null

/--
Parse a block mapping.

**YAML 1.2.2**: [184] l+block-mapping(n) (§8.2.2, https://yaml.org/spec/1.2.2/#822-block-mappings)
- [185] ns-l-block-map-entry(n)

Returns `Option YamlValue`:
- `some (.mapping .block pairs)`: successfully parsed
- `none`: mapping found but at wrong indentation
  (belongs to a parent structure)

**Pre-condition**: stream is at or near a mapping key.
**Post-condition**: if `some`, consumed the mapping.  If `none`,
  no input consumed at this indent level.
-/
@[yaml_spec "8.2.2" 184 "l+block-mapping(n)"]
def blockMappingImpl (fuel : Nat) (minIndent : Nat) : YamlParser (Option YamlValue) :=
  match fuel with
  | 0 => pure none
  | fuel + 1 =>
  withErrorMessage "expected block mapping" do
    skipBlankLines
    let mapIndent ← currentCol
    if mapIndent < minIndent then
      return none
    let pairs ← blockMappingEntriesImpl fuel mapIndent #[]
    return some (.mapping .block pairs)

/--
Parse block mapping entries at a fixed indentation level.

**YAML 1.2.2**: [185] ns-l-block-map-entry(n) (§8.2.2)
-/
@[yaml_spec "8.2.2" 185 "ns-l-block-map-entry(n)"]
def blockMappingEntriesImpl (fuel : Nat) (mapIndent : Nat)
    (acc : Array (YamlValue × YamlValue)) :
    YamlParser (Array (YamlValue × YamlValue)) :=
  match fuel with
  | 0 => pure acc
  | fuel + 1 => do
  skipBlankLines
  -- P10b: §6.1 — tabs are not allowed for indentation
  checkIndentForTabs mapIndent
  -- Consume leading indentation to reach content
  skipHWhitespace
  -- Check if at the mapping indentation
  let col ← currentCol
  if col != mapIndent then
    -- Detect wrongly-indented structural indicators (ANALYSIS.md §2.A).
    validateNoWrongIndentSeq mapIndent col
    validateNoWrongIndentMap mapIndent col (detectMappingKeyImpl fuel (inFlow := false))
    return acc
  -- Check if we're at a document boundary
  let atBoundary ← atDocumentBoundary
  if atBoundary then return acc
  -- Check for explicit key indicator `?` — this is always a valid entry start
  -- even though detectMappingKeyImpl fuel wouldn't find a `: ` on the `?` line.
  let isExplicitKey ← lookAhead do
    match ← option? (token '?') with
    | none => pure false
    | some _ =>
      match ← option? anyToken with
      | some c => pure (isWhiteSpace c || isLineBreak c)
      | none => pure true
  if isExplicitKey then
    match ← option? (blockMappingEntryImpl fuel mapIndent) with
    | none => return acc
    | some entry =>
      blockMappingEntriesImpl fuel mapIndent (acc.push entry)
  else
  -- Try to parse a mapping entry
  match ← option? (blockMappingEntryImpl fuel mapIndent) with
  | none => return acc
  | some entry =>
    blockMappingEntriesImpl fuel mapIndent (acc.push entry)

/--
Parse a single block mapping entry.

**YAML 1.2.2**: [185] ns-l-block-map-entry(n) (§8.2.2)
- [186] ns-l-block-map-explicit-entry(n): `? key\n: value`
- [188] ns-l-block-map-implicit-entry(n): `key: value`
- [189] ns-s-block-map-implicit-key

Handles both simple keys (`key: value`) and complex keys (`? key\n: value`).
-/
@[yaml_spec "8.2.2" 185 "ns-l-block-map-entry(n)"]
def blockMappingEntryImpl (fuel : Nat) (mapIndent : Nat) :
    YamlParser (YamlValue × YamlValue) :=
  match fuel with
  | 0 => pure (.null, .null)
  | fuel + 1 => do
  -- Check for complex key indicator `?`
  -- (§8.2.2, https://yaml.org/spec/1.2.2/#822-block-mappings)
  match ← option? (char '?') with
  | some _ =>
    -- Complex/explicit key
    -- P10b: §6.1 — check for tabs in separation whitespace after `?`
    let hasSepTabQ ← hasTabInWhitespace
    skipHWhitespace
    if hasSepTabQ then do
      let isBlockIndicator ← lookAhead do
        match ← option? anyToken with
        | some '-' | some '?' =>
          match ← option? anyToken with
          | none => pure true
          | some c => pure (isWhiteSpace c || isLineBreak c)
        | _ => pure false
      let isMK ← lookAhead (detectMappingKeyImpl fuel (inFlow := false))
      if isBlockIndicator || isMK then
        setValidationError "tabs are not allowed for indentation (YAML 1.2.2 §6.1)"
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
        let bv ← blockValueImpl fuel mapIndent (propertyMinIndent := mapIndent + 1)
        pure (bv.getD .null)
    else do
      -- Key on same line as `?`: parse at mapIndent + 1
      match ← option? (lookAhead anyToken) with
      | none => pure YamlValue.null
      | some _ =>
        let col ← currentCol
        match ← option? (blockValueSameLineImpl fuel col (mapIndent + 1)) with
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
      -- P10b: §6.1 — check for tabs in separation whitespace after `:`
      let hasSepTabC ← hasTabInWhitespace
      skipHWhitespace
      if hasSepTabC then do
        let isBlockIndicator ← lookAhead do
          match ← option? anyToken with
          | some '-' | some '?' =>
            match ← option? anyToken with
            | none => pure true
            | some c => pure (isWhiteSpace c || isLineBreak c)
          | _ => pure false
        let isMK ← lookAhead (detectMappingKeyImpl fuel (inFlow := false))
        if isBlockIndicator || isMK then
          setValidationError "tabs are not allowed for indentation (YAML 1.2.2 §6.1)"
      -- A `#` comment after `:` means the value is on the next line (§6.7).
      let hasComment ← do
        match ← option? (lookAhead anyToken) with
        | some '#' => optional comment *> return; pure true
        | _ => pure false
      let hasNewline := hasComment || (← test newline)
      let value ← if hasNewline then do
        -- Value on next line: use mapIndent (BLOCK-OUT context)
        -- allows sequences at mapIndent level
        let bv ← blockValueImpl fuel mapIndent (propertyMinIndent := mapIndent + 1)
        pure (bv.getD .null)
      else do
        let col' ← currentCol
        blockValueSameLineImpl fuel col' (mapIndent + 1)
      return (key, value)
    else
      -- No `:` found — value is implicitly null
      return (key, YamlValue.null)
  | none =>
    -- Simple key
    let key ← blockMappingKeyImpl fuel
    -- P5 fix: allow optional whitespace between the key and the mapping
    -- value indicator `:` (§7.3.2).  Quoted keys often have a space
    -- before `:` (e.g., `"key" : value`, `'key' : value`).
    skipHWhitespace
    let _ ← char ':'
    -- P10b: §6.1 — check for tabs in separation whitespace after `:`
    let hasSepTabS ← hasTabInWhitespace
    skipHWhitespace
    if hasSepTabS then do
      let isBlockIndicator ← lookAhead do
        match ← option? anyToken with
        | some '-' | some '?' =>
          match ← option? anyToken with
          | none => pure true
          | some c => pure (isWhiteSpace c || isLineBreak c)
        | _ => pure false
      let isMK ← lookAhead (detectMappingKeyImpl fuel (inFlow := false))
      if isBlockIndicator || isMK then
        setValidationError "tabs are not allowed for indentation (YAML 1.2.2 §6.1)"
    -- Value could be on the same line or the next line.
    -- A `#` comment after `:` means the value is on the next line (§6.7).
    let hasComment ← do
      match ← option? (lookAhead anyToken) with
      | some '#' => optional comment *> return; pure true
      | _ => pure false
    let hasNewline := hasComment || (← test newline)
    -- P7 pre-check (5U3A): §8.2.1 — a block sequence indicator (`- `)
    -- directly on the same line as a mapping key is invalid.
    -- `key: - item` must be rejected; the sequence must start on the next
    -- line or use flow notation `[item]`.
    -- This is a PRE-check (before parsing the value) to correctly allow
    -- `key: &anchor\n  - item` where the anchor is on the same line but
    -- the block sequence starts on the next line.
    if !hasNewline then
      let isSeqIndicator ← lookAhead do
        match ← option? (char '-') with
        | some _ =>
          match ← option? anyToken with
          | some c => return (isWhiteSpace c || isLineBreak c)
          | none => return true  -- `-` at EOF
        | none => return false
      if isSeqIndicator then
        setValidationError "block sequence cannot start on the same line as mapping key"
      -- P7 pre-check (ZCZ6/ZL4Z): §8.2.1 — a block mapping cannot start
      -- as an inline value on the same line as a mapping key.
      -- `a: b: c` and `a: 'b': c` are invalid; the nested mapping must
      -- be on the next line.  This is a PRE-check (before parsing) to
      -- correctly allow `key: &anchor\n  nested_key: val` where the
      -- anchor is on the same line but the mapping starts on the next.
      let isMappingOnSameLine ← lookAhead (detectMappingKeyImpl fuel (inFlow := false))
      if isMappingOnSameLine then
        setValidationError "block mapping cannot start on the same line as a mapping value"
    let value ← if hasNewline then
      -- BLOCK-OUT context (§8.2.2): next-line value allows sequences
      -- at the mapping's own indentation level (mapIndent), not mapIndent + 1.
      -- This handles `foo:\n- 42` where `-` is at mapIndent.
      let bv ← blockValueImpl fuel mapIndent (propertyMinIndent := mapIndent + 1)
      pure (bv.getD .null)
    else do
      let col ← currentCol
      blockValueSameLineImpl fuel col (mapIndent + 1)
    return (key, value)

/--
Parse a simple block mapping key.

**YAML 1.2.2**: [189] ns-s-block-map-implicit-key (§8.2.2)
- Uses [128] ns-plain(n,BLOCK-KEY) for implicit keys

Simple keys are single-line and cannot contain certain indicators.
They end at `: ` (mapping value indicator).
-/
@[yaml_spec "8.2.2" 189 "ns-s-block-map-implicit-key"]
def blockMappingKeyImpl (fuel : Nat) : YamlParser YamlValue :=
  match fuel with
  | 0 => pure .null
  | fuel + 1 => do
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
        let content ← plainMappingKey fuel
        return YamlValue.plainScalar content
    ]
    let key := key.withTag tag
    match anchorName with
    | some name => storeAnchor name key
    | none => pure ()
    let key := match anchorName with | some name => key.withAnchor name | none => key
    return key
  | none =>
  -- Check for anchor on mapping key
  match ← option? (lookAhead (token '&')) with
  | some _ => do
    let name ← parseAnchorPrefix
    -- P7 fix (SU74): §6.9.2 — an alias cannot carry an anchor.
    -- `&b *alias : value` is invalid as a mapping key.
    match ← option? (lookAhead (token '*')) with
    | some _ =>
      setValidationError "an alias (*) cannot carry an anchor (&)"
      let key ← parseAlias
      storeAnchor name key
      return key
    | none => pure ()
    -- Check for tag after anchor: `&anchor !tag key: value`
    let tagName ← do
      match ← option? (lookAhead (token '!')) with
      | some _ => pure (some (← parseTagPrefix))
      | none => pure none
    let key ← first [
      doubleQuotedScalar,
      singleQuotedScalar,
      do
        let content ← plainMappingKey fuel
        return YamlValue.plainScalar content
    ]
    let key := match tagName with | some t => key.withTag t | none => key
    storeAnchor name key
    return (key.withAnchor name)
  | none =>
  first [
    flowSequence,       -- P6 fix (M2N8): flow sequence as mapping key (`[]: x`)
    flowMapping,        -- P6 fix: flow mapping as mapping key (`{}: x`)
    do  -- P7 fix (7LBH): §7.4 — implicit block mapping key must not span
        -- multiple lines.  Record start/end line of quoted scalar.
      let startLine ← currentLine
      let val ← doubleQuotedScalar
      let endLine ← currentLine
      if endLine != startLine then
        setValidationError "implicit block mapping key must not span multiple lines (§7.4)"
      return val,
    do  -- P7 fix (D49Q): same multiline check for single-quoted keys
      let startLine ← currentLine
      let val ← singleQuotedScalar
      let endLine ← currentLine
      if endLine != startLine then
        setValidationError "implicit block mapping key must not span multiple lines (§7.4)"
      return val,
    do
      let content ← plainMappingKey fuel
      return YamlValue.plainScalar content
  ]
where
  plainMappingKey (fuel : Nat) : YamlParser String := do
    let mut acc := ""
    for _ in [:fuel] do
      match ← option? (lookAhead anyToken) with
      | none => break
      | some ':' =>
        -- Check if followed by whitespace (mapping separator)
        let isMapSep ← lookAhead do
          let _ ← anyToken  -- consume ':'
          match ← option? anyToken with
          | some c => return (isWhiteSpace c || isLineBreak c)
          | none => return true  -- `:` at EOF
        if isMapSep then
          break
        else
          let _ ← anyToken  -- actually consume the ':'
          acc := acc.push ':'
      | some c =>
        if isLineBreak c then
          break
        else if c == '#' && acc.endsWith " " then
          -- Comment
          break
        else
          let _ ← anyToken  -- actually consume
          acc := acc.push c
    return acc.trimAsciiEnd.toString

/--
Detect if the current position is at a mapping key.

Looks ahead for a `key: ` or `key:\n` pattern without consuming input.
This helps disambiguate between plain scalars and block mappings.

**T4 fix (ANALYSIS.md §2.I)**: Scans past non-separator colons (`:` followed
by non-whitespace) and quote characters that appear mid-key.  The original
implementation bailed on the first `:` whose successor was not whitespace and
on any `'`/`"`, producing false negatives for keys like `a"b: v`, `key::: v`.

**Flow-aware (P6 fix)**: When encountering `{` or `[`, skips to the matching
close bracket (respecting nesting) instead of scanning character-by-character.
This prevents false positives from `: ` inside flow collections such as
`&map {a: 1, b: 2}` or `!!map {a: 1}`.  Without this, `detectMappingKeyImpl fuel`
would find `: 1` inside the braces and falsely classify the input as a mapping.

### A/G Contract

**Assume (A1)**: Called inside `lookAhead` — all input consumption is rolled back.

**Guarantee (G1)**: Returns `true` iff a `: ` or `:\n` separator exists on the
current line OUTSIDE any balanced flow brackets `{...}` / `[...]`.

**Guarantee (G2)**: Does not consume input (enforced by `lookAhead` at call site).
-/
def detectMappingKeyImpl (fuel : Nat) (inFlow : Bool) : YamlParser Bool :=
  match fuel with
  | 0 => pure false
  | fuel + 1 => do
  -- Try to find `: ` or `:\n` on this line (skipping flow content)
  detectLoop fuel
where
  /-- Skip over balanced flow brackets.  `depth` counts nesting level;
      when it reaches 0, the matching close bracket has been consumed. -/
  skipFlowBrackets : Nat → Nat → YamlParser Unit
    | 0, _ => return ()
    | fuel + 1, depth => do
      if depth == 0 then return ()
      match ← option? anyToken with
      | none => return ()  -- unclosed collection at EOF, bail out
      | some c =>
        if c == '}' || c == ']' then skipFlowBrackets fuel (depth - 1)
        else if c == '{' || c == '[' then skipFlowBrackets fuel (depth + 1)
        else skipFlowBrackets fuel depth
  /-- Skip over a double-quoted string (after opening `"` consumed).
      Handles `\\` escape sequences so `\"` doesn't terminate early. -/
  skipDoubleQuoted : Nat → YamlParser Unit
    | 0 => return ()
    | fuel + 1 => do
      match ← option? anyToken with
      | none => return ()       -- unclosed quote at EOF
      | some '"' => return ()   -- closing quote
      | some '\\' =>            -- escape: skip next char
        let _ ← option? anyToken
        skipDoubleQuoted fuel
      | some _ => skipDoubleQuoted fuel
  /-- Skip over a single-quoted string (after opening `'` consumed).
      Handles `''` escape (the only escape in single-quoted scalars). -/
  skipSingleQuoted : Nat → YamlParser Unit
    | 0 => return ()
    | fuel + 1 => do
      match ← option? anyToken with
      | none => return ()       -- unclosed quote at EOF
      | some '\'' =>
        -- Check for '' escape (two consecutive single quotes)
        match ← option? (lookAhead (char '\'')) with
        | some _ => let _ ← anyToken; skipSingleQuoted fuel
        | none => return ()     -- closing quote
      | some _ => skipSingleQuoted fuel
  detectLoop : Nat → YamlParser Bool
    | 0 => return false
    | fuel + 1 => do
      -- `afterWs` tracks whether the previous character was whitespace
      -- (or this is the start of the scan). Quotes are only treated as
      -- string-start when preceded by whitespace; mid-word quotes like
      -- `a!"` are plain-scalar characters (T4).
      detectLoopWs fuel true
  detectLoopWs : Nat → Bool → YamlParser Bool
    | 0, _ => return false
    | fuel + 1, afterWs => do
      match ← option? anyToken with
      | none => return false
      | some ':' =>
        -- P6 fix: use lookAhead to peek the char after `:` without consuming it.
        -- This way, if the char after `:` is itself `:`, the NEXT detectLoop
        -- iteration re-examines it as a potential separator.  Fixes `::` which
        -- should be mapping key `:` → null value (UKK6).
        match ← option? (lookAhead anyToken) with
        | none => return true  -- `:` at EOF → mapping separator
        | some c =>
          if isWhiteSpace c || isLineBreak c then return true
          -- Not a separator — continue scanning without consuming the peeked char
          else detectLoopWs fuel false
      | some c =>
        if isLineBreak c then return false
        else if inFlow && isFlowIndicator c then return false
        -- Flow-aware: skip over balanced flow collections to avoid false
        -- positives from `:` inside braces/brackets (e.g., `{a: 1}`).
        else if c == '{' || c == '[' then do
          skipFlowBrackets fuel 1
          detectLoopWs fuel true
        -- Quote-aware (P8 fix): skip over quoted strings to avoid false
        -- positives from `: ` inside quoted scalars (e.g., `!!str "a: b"`).
        -- Only activate when the quote follows whitespace (afterWs), so
        -- mid-word quotes in plain scalars (e.g., `a!"#$...`) are not
        -- misinterpreted as string delimiters.
        else if afterWs && c == '"' then do
          skipDoubleQuoted fuel
          detectLoopWs fuel true
        else if afterWs && c == '\'' then do
          skipSingleQuoted fuel
          detectLoopWs fuel true
        else detectLoopWs fuel (isWhiteSpace c)

end

/-- Dispatch to parser by character (wrapper with fuel). -/
def dispatchByChar (contentIndent : Nat) (scalarIndent : Nat := contentIndent) : YamlParser (DispatchResult YamlValue) := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  dispatchByCharImpl fuel contentIndent scalarIndent

/-- Parse a block value (wrapper with fuel). -/
def blockValue (minIndent : Nat) (propertyMinIndent : Nat := minIndent) : YamlParser (Option YamlValue) := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  blockValueImpl fuel minIndent propertyMinIndent

/-- Parse a block sequence (wrapper with fuel). -/
def blockSequence (minIndent : Nat) : YamlParser (Option YamlValue) := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  blockSequenceImpl fuel minIndent

/-- Parse a block mapping (wrapper with fuel). -/
def blockMapping (minIndent : Nat) : YamlParser (Option YamlValue) := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  blockMappingImpl fuel minIndent

/-- Parse block sequence items (wrapper with fuel). -/
def blockSequenceItems (seqIndent : Nat) (acc : Array YamlValue) : YamlParser (Array YamlValue) := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  blockSequenceItemsImpl fuel seqIndent acc

/-- Parse a block value on the same line (wrapper with fuel). -/
def blockValueSameLine (startCol : Nat) (contentIndent : Nat) : YamlParser YamlValue := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  blockValueSameLineImpl fuel startCol contentIndent

/-- Parse block mapping entries (wrapper with fuel). -/
def blockMappingEntries (mapIndent : Nat) (acc : Array (YamlValue × YamlValue)) : YamlParser (Array (YamlValue × YamlValue)) := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  blockMappingEntriesImpl fuel mapIndent acc

/-- Parse a block mapping entry (wrapper with fuel). -/
def blockMappingEntry (mapIndent : Nat) : YamlParser (YamlValue × YamlValue) := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  blockMappingEntryImpl fuel mapIndent

/-- Parse a block mapping key (wrapper with fuel). -/
def blockMappingKey : YamlParser YamlValue := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  blockMappingKeyImpl fuel

/-- Detect if current position is a mapping key (wrapper with fuel). -/
def detectMappingKey (inFlow : Bool) : YamlParser Bool := do
  let fuel := 4 * Stream.remaining (← getStream) + 4
  detectMappingKeyImpl fuel inFlow

end Lean4Yaml.Parse
