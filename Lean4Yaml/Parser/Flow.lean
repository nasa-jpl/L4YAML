/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar

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
-/
def flowScalar : YamlParser YamlValue :=
  first [
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
-/
partial def flowSequenceItems (acc : Array YamlValue) : YamlParser (Array YamlValue) := do
  let item ← flowValue
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
-/
partial def flowMappingEntry : YamlParser (YamlValue × YamlValue) := do
  flowWhitespace
  -- Check for explicit key indicator `?`
  let key ← do
    match ← option? (char '?') with
    | some _ => flowWhitespace; flowValue
    | none => flowScalar
  flowWhitespace
  -- Parse the `: value` part (the value is optional — if missing, it's null)
  match ← option? (char ':') with
  | some _ =>
    flowWhitespace
    -- Check if value follows or we hit a separator/closing bracket
    match ← option? (lookAhead (tokenFilter fun c => c == ',' || c == '}')) with
    | some _ =>
      -- No value: `key:` with implicit null value
      return (key, YamlValue.null)
    | none =>
      let value ← flowValue
      return (key, value)
  | none =>
    -- Implicit key in flow sequence context (e.g., `[a : b, c : d]`)
    -- For now, treat as a bare value — the key is the value, with empty mapping
    -- Actually, this shouldn't happen in a flow mapping entry
    return (key, YamlValue.null)

end

end Lean4Yaml.Parse
