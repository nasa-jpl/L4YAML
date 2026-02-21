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

/-!
# YAML Flow Collection Parsers

Parsers for YAML flow-style collections
(§7.4, https://yaml.org/spec/1.2.2/#74-flow-collection-styles):
- Flow sequences: `[item1, item2, ...]`
- Flow mappings: `{key1: value1, key2: value2, ...}`

Flow collections use explicit brackets and commas for structure,
similar to JSON syntax. They can be nested and can contain any
YAML value type.

## Key Differences from JSON

1. Plain (unquoted) scalars are allowed as both keys and values
2. Extra commas are technically not allowed (but many parsers accept them)
3. Complex keys are allowed (preceded by `?`)
4. Values can be flow collections or scalars

## Mutual Recursion

Flow values, flow sequences, and flow mappings are mutually recursive
since a flow sequence item can be a flow mapping and vice versa.
The top-level `flowValue` dispatches to the appropriate sub-parser.
-/

namespace Lean4Yaml.Parse

open Parser
open Parser.Char
open Lean4Yaml

/-! ## Forward Declaration

Flow values can contain flow collections, which contain flow values.
We use `partial` to handle this mutual recursion. Termination proofs
will be added in `Lean4Yaml.Proofs.Termination`.
-/

/--
Skip whitespace that can appear between flow collection elements.

In flow context, both spaces and newlines are allowed between elements.

Per YAML §6.7, a comment `#` must be "separated from other tokens by
white space characters."  We only treat `#` as a comment start if
whitespace was consumed before it (or it appears at column 0, i.e.
start of a line).
-/
partial def flowWhitespace (minIndent : Nat := 0) : YamlParser Unit := do
  let lineBefore ← currentLine
  let colBefore ← currentCol
  let posBefore ← currentPos
  -- Consume whitespace + newlines.
  let rec consumeWs : YamlParser Unit := do
    match ← option? (tokenFilter fun c => isWhiteSpace c || isLineBreak c) with
    | none => pure ()
    | some _ => consumeWs
  consumeWs
  let lineAfter ← currentLine
  let colAfter ← currentCol
  let posAfter ← currentPos
  -- P10 fix (9C9N, VJP3): §7.4 / s-flow-line-prefix(n) — continuation
  -- content in flow collections must respect block context indentation.
  -- Only check when we've actually moved to a new line.
  if minIndent > 0 && lineAfter > lineBefore then
    if colAfter < minIndent then
      setValidationError
        s!"flow collection content at column {colAfter} is less than required indent {minIndent}"
    else
      -- P10b (Y79Y): §6.1 — tabs in the indent area of a continuation line
      -- are illegal.  Only check when the content is NOT a flow closing
      -- indicator (']' or '}'), since tabs before those are just
      -- separation whitespace, not indentation.
      let isFlowClose ← lookAhead do
        match ← option? anyToken with
        | some ']' | some '}' => pure true
        | _ => pure false
      if !isFlowClose then
        -- Save current position, rewind to before whitespace, advance
        -- to the start of the last line, check for tabs, then restore.
        Parser.setPosition posBefore
        let rec advanceToLine : YamlParser Unit := do
          let l ← currentLine
          if l >= lineAfter then return ()
          match ← option? anyToken with
          | none => return ()
          | some _ => advanceToLine
        advanceToLine
        checkIndentForTabs minIndent
        Parser.setPosition posAfter
  match ← option? (lookAhead (token '#')) with
  | some _ =>
    -- §6.7: `#` is only a comment if preceded by whitespace.
    -- If no whitespace was consumed AND we're not at column 0
    -- (start of line), then `#` is not a valid comment.
    let atLineStart := colAfter == 0
    let wsConsumed := (colBefore != colAfter) || atLineStart
    if wsConsumed then
      comment
      flowWhitespace minIndent
    else
      -- `#` without preceding whitespace — not a valid comment.
      -- Let the caller handle it (will trigger a validation error
      -- when the unexpected char is encountered).
      return
  | none => return

/--
Parse a flow scalar value (used inside flow collections).

This parses any scalar type: double-quoted, single-quoted, or plain.
Plain scalars in flow context are terminated by `,`, `]`, `}`.
Also handles aliases (`*name`) as values.
-/
def flowScalar : YamlParser YamlValue :=
  first [
    parseAlias,
    doubleQuotedScalar,
    singleQuotedScalar,
    plainScalar (inFlow := true)
  ]

mutual

/--
Parse a flow value
(§7.4, https://yaml.org/spec/1.2.2/#74-flow-collection-styles).

A flow value is either:
- A scalar (plain, single-quoted, or double-quoted)
- A flow sequence `[...]`
- A flow mapping `{...}`
-/
partial def flowValue (minIndent : Nat := 0) : YamlParser YamlValue :=
  withErrorMessage "expected flow value" do
    flowWhitespace minIndent
    -- P7 fix (N782): §9.1.4/§7.4 — document markers (`---`/`...`) at the
    -- start of a line are c-forbidden content inside flow collections.
    -- They terminate the document, not continue the flow.
    let col ← currentCol
    if col == 0 then do
      let atBound ← lookAhead atDocumentBoundary
      if atBound then do
        setValidationError "document markers ('---'/'...') are forbidden inside flow collections"
        return .null
    -- Check for tag prefix (!tag) on flow values (§6.9)
    match ← option? (lookAhead (token '!')) with
    | some _ => do
      let tag ← parseTagPrefix
      flowWhitespace minIndent
      -- Check for anchor after tag: `!tag &anchor value`
      let anchorName ← do
        match ← option? (lookAhead (token '&')) with
        | some _ =>
          let name ← parseAnchorPrefix
          flowWhitespace minIndent
          pure (some name)
        | none => pure none
      -- P6 fix (WZ62): After tag/anchor, the value may be empty in flow context.
      -- E.g. `!!str,` → tag on null.  If next char is a flow delimiter,
      -- return null with the tag/anchor applied.
      let val ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']' || c == '}')) with
      | some _ => pure YamlValue.null
      | none => first [
          flowSequence minIndent,
          flowMapping minIndent,
          flowScalar
        ]
      let val := val.withTag tag
      match anchorName with
      | some name => storeAnchor name val
      | none => pure ()
      return val
    | none =>
    -- Check for anchor prefix (&name) on flow values
    match ← option? (lookAhead (token '&')) with
    | some _ => do
      let name ← parseAnchorPrefix
      flowWhitespace minIndent
      -- Check for tag after anchor: `&anchor !tag value`
      let tagName ← do
        match ← option? (lookAhead (token '!')) with
        | some _ =>
          let tag ← parseTagPrefix
          flowWhitespace minIndent
          pure (some tag)
        | none => pure none
      -- P6 fix: anchor on empty flow value (e.g. `&a ,` → null with anchor)
      let val ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']' || c == '}')) with
      | some _ => pure YamlValue.null
      | none => first [
          flowSequence minIndent,
          flowMapping minIndent,
          flowScalar
        ]
      let val := match tagName with | some t => val.withTag t | none => val
      storeAnchor name val
      return val
    | none =>
    first [
      flowSequence minIndent,
      flowMapping minIndent,
      flowScalar
    ]

/--
Parse a flow sequence
(§7.4.1, https://yaml.org/spec/1.2.2/#741-flow-sequences).

```yaml
[item1, item2, item3]
```

Items are separated by commas with optional whitespace.
Nested flow collections are supported.
-/
partial def flowSequence (minIndent : Nat := 0) : YamlParser YamlValue :=
  withErrorMessage "expected flow sequence" do
    let _ ← char '['
    flowWhitespace minIndent
    -- Check for empty sequence
    match ← option? (char ']') with
    | some _ => return .sequence .flow #[]
    | none =>
      let items ← flowSequenceItems #[] minIndent
      return .sequence .flow items

/--
Parse flow sequence items, separated by commas.

Handles:
- Regular flow values: `[a, b, c]`
- Explicit key entries: `[? key : value]` (§7.4.2)
- **Implicit single-pair mappings**: `[key : value]` (§7.5)
- **Empty implicit keys**: `[: value]` (§7.4.2)

Per §7.5, a flow sequence entry can be a single key:value pair
without braces, creating an implicit single-pair flow mapping.

**Pre-condition**: `[` already consumed; whitespace skipped.
**Post-condition**: items collected up to and including `]`.
-/
partial def flowSequenceItems (acc : Array YamlValue) (minIndent : Nat := 0) : YamlParser (Array YamlValue) := do
  -- Check for explicit key `?` in flow sequence — creates single-pair mapping
  -- (§7.4.2, https://yaml.org/spec/1.2.2/#742-flow-mappings)
  let isExplicitKey ← lookAhead do
    match ← option? (token '?') with
    | none => pure false
    | some _ =>
      match ← option? anyToken with
      | none => pure true
      | some c => pure (isWhiteSpace c || isLineBreak c)
  -- Check for empty implicit key `: value` at start of entry (§7.4.2)
  let isEmptyKey ← if isExplicitKey then pure false else lookAhead do
    match ← option? (token ':') with
    | none => pure false
    | some _ =>
      match ← option? anyToken with
      | none => pure true
      | some c => pure (isWhiteSpace c || isLineBreak c || isFlowIndicator c)
  let item ← if isExplicitKey then do
    -- Parse as single-pair mapping: `? key : value`
    let _ ← char '?'
    flowWhitespace minIndent
    let key ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']' || c == ':')) with
    | some _ => pure YamlValue.null
    | none => flowValue minIndent
    flowWhitespace minIndent
    match ← option? (char ':') with
    | some _ =>
      flowWhitespace minIndent
      let value ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']')) with
      | some _ => pure YamlValue.null
      | none => flowValue minIndent
      pure (.mapping .flow #[(key, value)])
    | none => pure (.mapping .flow #[(key, YamlValue.null)])
  else if isEmptyKey then do
    -- Empty implicit key: `: value` → mapping with null key
    let _ ← char ':'
    flowWhitespace minIndent
    let value ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']')) with
    | some _ => pure YamlValue.null
    | none => flowValue minIndent
    pure (.mapping .flow #[(YamlValue.null, value)])
  else do
    -- Parse a flow value, then check for implicit mapping `:` (§7.5)
    -- Record the line where the key starts — per §7.4, in flow context
    -- an implicit key and its `:` must be on the same line.
    let keyLine ← currentLine
    let val ← flowValue minIndent
    flowWhitespace minIndent
    -- Check if this is an implicit single-pair mapping: `key : value`
    -- Per §7.4, after a JSON-like key (flow collection, quoted scalar),
    -- the `:` does NOT require trailing whitespace.
    let isJsonLikeKey : Bool := match val with
      | .sequence .. | .mapping .. => true  -- flow collection
      | .scalar s => s.style == .doubleQuoted || s.style == .singleQuoted
    let colonLine ← currentLine
    let isImplicitMapping ← lookAhead do
      match ← option? (token ':') with
      | none => pure false
      | some _ =>
        if isJsonLikeKey then pure true  -- JSON-like: no whitespace needed
        else match ← option? anyToken with
        | none => pure true
        | some c => pure (isWhiteSpace c || isLineBreak c || isFlowIndicator c)
    -- §7.4: In flow context, an implicit key must not span multiple lines.
    -- If the `:` is on a different line than the key, reject.
    if isImplicitMapping && colonLine != keyLine then do
      setValidationError "implicit flow key and ':' must be on the same line"
      pure val
    else if isImplicitMapping then do
      let _ ← char ':'
      flowWhitespace minIndent
      let value ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']')) with
      | some _ => pure YamlValue.null
      | none => flowValue minIndent
      pure (.mapping .flow #[(val, value)])
    else
      pure val
  flowWhitespace minIndent
  match ← anyToken with
  | ',' =>
    flowWhitespace minIndent
    -- Check for trailing comma before `]`
    match ← option? (char ']') with
    | some _ => return acc.push item
    | none => flowSequenceItems (acc.push item) minIndent
  | ']' => return acc.push item
  | c =>
    -- Invalid delimiter: record validation error and return what we have.
    -- The error survives backtracking and is checked at the top level.
    setValidationError s!"expected ',' or ']' in flow sequence, got '{c}'"
    return acc.push item

/--
Parse a flow mapping
(§7.4.2, https://yaml.org/spec/1.2.2/#742-flow-mappings).

```yaml
{key1: value1, key2: value2}
```

Keys can be scalars or complex keys (preceded by `?`).
-/
partial def flowMapping (minIndent : Nat := 0) : YamlParser YamlValue :=
  withErrorMessage "expected flow mapping" do
    let _ ← char '{'
    flowWhitespace minIndent
    -- Check for empty mapping
    match ← option? (char '}') with
    | some _ => return .mapping .flow #[]
    | none =>
      let pairs ← flowMappingEntries #[] minIndent
      return .mapping .flow pairs

/--
Parse flow mapping entries, separated by commas.
-/
partial def flowMappingEntries (acc : Array (YamlValue × YamlValue)) (minIndent : Nat := 0) :
    YamlParser (Array (YamlValue × YamlValue)) := do
  let (k, v) ← flowMappingEntry minIndent
  flowWhitespace minIndent
  match ← anyToken with
  | ',' =>
    flowWhitespace minIndent
    -- Check for trailing comma before `}`
    match ← option? (char '}') with
    | some _ => return acc.push (k, v)
    | none => flowMappingEntries (acc.push (k, v)) minIndent
  | '}' => return acc.push (k, v)
  | c =>
    -- Invalid delimiter: record validation error and return what we have.
    setValidationError s!"expected ',' or '}}' in flow mapping, got '{c}'"
    return acc.push (k, v)

/--
Parse a single flow mapping entry (`key: value` or `? key : value`).

Handles:
- `? key : value` — explicit key with value
- `? key` — explicit key with null value
- `?` — bare explicit key indicator (null key, null value)
- `key : value` — implicit key
- `: value` — empty key with value (§7.4.2)
-/
partial def flowMappingEntry (minIndent : Nat := 0) : YamlParser (YamlValue × YamlValue) := do
  flowWhitespace minIndent
  -- Check for explicit key indicator `?`
  match ← option? (char '?') with
  | some _ =>
    flowWhitespace minIndent
    -- Check for bare `?` (null key) — next char is `,`, `}`, or `:`
    let key ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}' || c == ':')) with
    | some _ => pure YamlValue.null
    | none => flowValue minIndent
    flowWhitespace minIndent
    match ← option? (char ':') with
    | some _ =>
      flowWhitespace minIndent
      match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}')) with
      | some _ => return (key, YamlValue.null)
      | none =>
        let value ← flowValue minIndent
        return (key, value)
    | none => return (key, YamlValue.null)
  | none =>
  -- Check for empty key: `:` at start means null key with a value
  match ← option? (lookAhead (token ':')) with
  | some _ =>
    -- Verify it's a mapping separator (`:` followed by whitespace or flow indicator)
    let isSep ← lookAhead do
      let _ ← anyToken  -- consume ':'
      match ← option? anyToken with
      | none => return true
      | some c => return (isWhiteSpace c || isLineBreak c || isFlowIndicator c)
    if isSep then do
      let _ ← char ':'
      flowWhitespace minIndent
      match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}')) with
      | some _ => return (YamlValue.null, YamlValue.null)
      | none =>
        let value ← flowValue minIndent
        return (YamlValue.null, value)
    else do
      -- `:` not a separator, parse as scalar key
      let key ← flowScalar
      flowWhitespace minIndent
      -- After a quoted scalar key, check for JSON-like `:` (no whitespace needed)
      let isJsonKey : Bool := match key with
        | .scalar s => s.style == .doubleQuoted || s.style == .singleQuoted
        | _ => false
      let hasColon ← if isJsonKey then do
        match ← option? (lookAhead (token ':')) with
        | some _ => pure true
        | none => pure false
      else
        match ← option? (char ':') with
        | some _ => pure true
        | none => pure false
      if hasColon then do
        if isJsonKey then let _ ← char ':'  -- consume the `:` we only peeked
        flowWhitespace minIndent
        match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}')) with
        | some _ => return (key, YamlValue.null)
        | none =>
          let value ← flowValue minIndent
          return (key, value)
      else return (key, YamlValue.null)
  | none =>
  -- Normal implicit key — collections can be keys (§7.4.2).
  -- P6 fix: also handle anchored/aliased/tagged keys by checking for
  -- `&`/`*`/`!` prefix.  X38W: `&a [...]` as key; CN3R: `&c c`;
  -- WZ62: `!!str` as key.
  let key ← do
    -- Check for tag prefix on key
    match ← option? (lookAhead (token '!')) with
    | some _ =>
      let tag ← parseTagPrefix
      flowWhitespace minIndent
      -- Tag may be followed by anchor
      let anchorName ← do
        match ← option? (lookAhead (token '&')) with
        | some _ =>
          let name ← parseAnchorPrefix
          flowWhitespace minIndent
          pure (some name)
        | none => pure none
      -- Tag on empty key: next is `:` or flow delimiter
      let val ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']' || c == '}' || c == ':')) with
      | some _ => pure YamlValue.null
      | none => first [flowSequence, flowMapping minIndent, flowScalar]
      let val := val.withTag tag
      match anchorName with
      | some name => storeAnchor name val
      | none => pure ()
      pure val
    | none =>
    -- Check for anchor prefix on key
    match ← option? (lookAhead (token '&')) with
    | some _ =>
      let name ← parseAnchorPrefix
      flowWhitespace minIndent
      -- Anchor on empty key: next is `:` or flow delimiter
      let val ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']' || c == '}' || c == ':')) with
      | some _ => pure YamlValue.null
      | none => first [flowSequence, flowMapping minIndent, flowScalar]
      storeAnchor name val
      pure val
    | none =>
    -- Check for alias as key
    match ← option? (lookAhead (token '*')) with
    | some _ => parseAlias
    | none => first [flowSequence, flowMapping minIndent, flowScalar]
  flowWhitespace minIndent
  -- After a JSON-like key (collection, quoted scalar, tagged, or null),
  -- `:` doesn't need whitespace separation
  let isJsonKey : Bool := match key with
    | .sequence .. | .mapping .. | .null => true
    | .scalar s => s.style == .doubleQuoted || s.style == .singleQuoted
                   || s.tag != none
  let hasColon ← if isJsonKey then do
    match ← option? (lookAhead (token ':')) with
    | some _ => pure true
    | none => pure false
  else do
    -- Plain scalar key: `:` needs whitespace separation
    let isSep ← lookAhead do
      match ← option? (token ':') with
      | none => pure false
      | some _ =>
        match ← option? anyToken with
        | none => pure true
        | some c => pure (isWhiteSpace c || isLineBreak c || isFlowIndicator c)
    pure isSep
  if hasColon then do
    let _ ← char ':'
    flowWhitespace minIndent
    match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}')) with
    | some _ => return (key, YamlValue.null)
    | none =>
      let value ← flowValue minIndent
      return (key, value)
  else return (key, YamlValue.null)

end

end Lean4Yaml.Parse
