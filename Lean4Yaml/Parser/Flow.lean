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
-/
partial def flowWhitespace : YamlParser Unit := do
  dropMany (tokenFilter fun c => isWhiteSpace c || isLineBreak c)
  match ← option? (lookAhead (token '#')) with
  | some _ =>
    comment
    flowWhitespace
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
partial def flowValue : YamlParser YamlValue :=
  withErrorMessage "expected flow value" do
    flowWhitespace
    -- Check for tag prefix (!tag) on flow values (§6.9)
    match ← option? (lookAhead (token '!')) with
    | some _ => do
      let tag ← parseTagPrefix
      flowWhitespace
      -- Check for anchor after tag: `!tag &anchor value`
      let anchorName ← do
        match ← option? (lookAhead (token '&')) with
        | some _ =>
          let name ← parseAnchorPrefix
          flowWhitespace
          pure (some name)
        | none => pure none
      let val ← first [
        flowSequence,
        flowMapping,
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
      flowWhitespace
      -- Check for tag after anchor: `&anchor !tag value`
      let tagName ← do
        match ← option? (lookAhead (token '!')) with
        | some _ =>
          let tag ← parseTagPrefix
          flowWhitespace
          pure (some tag)
        | none => pure none
      let val ← first [
        flowSequence,
        flowMapping,
        flowScalar
      ]
      let val := match tagName with | some t => val.withTag t | none => val
      storeAnchor name val
      return val
    | none =>
    first [
      flowSequence,
      flowMapping,
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
partial def flowSequence : YamlParser YamlValue :=
  withErrorMessage "expected flow sequence" do
    let _ ← char '['
    flowWhitespace
    -- Check for empty sequence
    match ← option? (char ']') with
    | some _ => return .sequence .flow #[]
    | none =>
      let items ← flowSequenceItems #[]
      return .sequence .flow items

/--
Parse flow sequence items, separated by commas.

Handles single-pair explicit entries: `[? key : value]` creates a
flow sequence containing a single-pair mapping (§7.4, §7.5).
-/
partial def flowSequenceItems (acc : Array YamlValue) : YamlParser (Array YamlValue) := do
  -- Check for explicit key `?` in flow sequence — creates single-pair mapping
  -- (§7.4.2, https://yaml.org/spec/1.2.2/#742-flow-mappings)
  let isExplicitKey ← lookAhead do
    match ← option? (token '?') with
    | none => pure false
    | some _ =>
      match ← option? anyToken with
      | none => pure true
      | some c => pure (isWhiteSpace c || isLineBreak c)
  let item ← if isExplicitKey then do
    -- Parse as single-pair mapping: `? key : value`
    let _ ← char '?'
    flowWhitespace
    let key ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']' || c == ':')) with
    | some _ => pure YamlValue.null
    | none => flowValue
    flowWhitespace
    match ← option? (char ':') with
    | some _ =>
      flowWhitespace
      let value ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == ']')) with
      | some _ => pure YamlValue.null
      | none => flowValue
      pure (.mapping .flow #[(key, value)])
    | none => pure (.mapping .flow #[(key, YamlValue.null)])
  else
    flowValue
  flowWhitespace
  match ← anyToken with
  | ',' =>
    flowWhitespace
    -- Check for trailing comma before `]`
    match ← option? (char ']') with
    | some _ => return acc.push item
    | none => flowSequenceItems (acc.push item)
  | ']' => return acc.push item
  | c => withErrorMessage s!"expected ',' or ']' in flow sequence, got '{c}'" throwUnexpected

/--
Parse a flow mapping
(§7.4.2, https://yaml.org/spec/1.2.2/#742-flow-mappings).

```yaml
{key1: value1, key2: value2}
```

Keys can be scalars or complex keys (preceded by `?`).
-/
partial def flowMapping : YamlParser YamlValue :=
  withErrorMessage "expected flow mapping" do
    let _ ← char '{'
    flowWhitespace
    -- Check for empty mapping
    match ← option? (char '}') with
    | some _ => return .mapping .flow #[]
    | none =>
      let pairs ← flowMappingEntries #[]
      return .mapping .flow pairs

/--
Parse flow mapping entries, separated by commas.
-/
partial def flowMappingEntries (acc : Array (YamlValue × YamlValue)) :
    YamlParser (Array (YamlValue × YamlValue)) := do
  let (k, v) ← flowMappingEntry
  flowWhitespace
  match ← anyToken with
  | ',' =>
    flowWhitespace
    -- Check for trailing comma before `}`
    match ← option? (char '}') with
    | some _ => return acc.push (k, v)
    | none => flowMappingEntries (acc.push (k, v))
  | '}' => return acc.push (k, v)
  | c => withErrorMessage s!"expected ',' or '}}' in flow mapping, got '{c}'" throwUnexpected

/--
Parse a single flow mapping entry (`key: value` or `? key : value`).

Handles:
- `? key : value` — explicit key with value
- `? key` — explicit key with null value  
- `?` — bare explicit key indicator (null key, null value)
- `key : value` — implicit key
- `: value` — empty key with value (§7.4.2)
-/
partial def flowMappingEntry : YamlParser (YamlValue × YamlValue) := do
  flowWhitespace
  -- Check for explicit key indicator `?`
  match ← option? (char '?') with
  | some _ =>
    flowWhitespace
    -- Check for bare `?` (null key) — next char is `,`, `}`, or `:`
    let key ← match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}' || c == ':')) with
    | some _ => pure YamlValue.null
    | none => flowValue
    flowWhitespace
    match ← option? (char ':') with
    | some _ =>
      flowWhitespace
      match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}')) with
      | some _ => return (key, YamlValue.null)
      | none =>
        let value ← flowValue
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
      flowWhitespace
      match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}')) with
      | some _ => return (YamlValue.null, YamlValue.null)
      | none =>
        let value ← flowValue
        return (YamlValue.null, value)
    else do
      -- `:` not a separator, parse as scalar key
      let key ← flowScalar
      flowWhitespace
      match ← option? (char ':') with
      | some _ =>
        flowWhitespace
        match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}')) with
        | some _ => return (key, YamlValue.null)
        | none =>
          let value ← flowValue
          return (key, value)
      | none => return (key, YamlValue.null)
  | none =>
  -- Normal implicit key
  let key ← flowScalar
  flowWhitespace
  match ← option? (char ':') with
  | some _ =>
    flowWhitespace
    match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}')) with
    | some _ => return (key, YamlValue.null)
    | none =>
      let value ← flowValue
      return (key, value)
  | none => return (key, YamlValue.null)

end

end Lean4Yaml.Parse
