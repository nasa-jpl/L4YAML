/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.YamlSpec

/-!
# YAML Anchor & Alias Parsers

Parsers for YAML anchors (`&name`) and aliases (`*name`).

**YAML 1.2.2**:
- [99] c-ns-anchor-property / [100] c-anchor / [101] ns-anchor-name / [102] ns-anchor-char (§6.9.2)
- [103] c-ns-alias-node / [14] c-alias (§7.1)

References:
- §6.9.2 Node Anchors: https://yaml.org/spec/1.2.2/#692-node-anchors
- §7.1 Alias Nodes: https://yaml.org/spec/1.2.2/#71-alias-nodes

## Design

**Eager substitution**: Aliases resolve to value copies at parse time.
There is no distinct "alias node" in the AST — `*name` looks up the
anchor map and returns the previously stored `YamlValue`.

**Anchor map in `YamlStream`**: The anchor map is stored in the stream
itself (not in `Position`), so `setPosition` (used by backtracking)
restores offset/line/col but preserves the accumulated anchor map.
This is proved by `setPosition_preserves_anchorMap` in Stream.lean.

**Pure data layer**: `storeAnchor` and `lookupAnchor` delegate to
`AnchorMap.insert` and `AnchorMap.find?` (defined in Types.lean),
whose algebraic laws (`find?_insert`, `find?_insert_ne`, `find?_empty`)
are the foundation for alias-resolution proofs.

## Contracts

1. **`storeAnchor name val`** — after execution,
   `AnchorMap.find? anchorMap name = some val` (by `find?_insert`)
2. **`lookupAnchor name`** — pure read; position unchanged
3. **`parseAlias`** — succeeds iff anchor is defined; consumes `*` + name
4. **`resetAnchorMap`** — clears all bindings; used at document boundaries

## Spec References

- §6.9.2 Node Anchors: https://yaml.org/spec/1.2.2/#692-node-anchors
- §7.1 Alias Nodes: https://yaml.org/spec/1.2.2/#71-alias-nodes
- §3.2.2.2 Anchors are scoped to a single document
-/

namespace Lean4Yaml.Parse

open Parser
open Parser.Char
open Lean4Yaml

/-! ## Anchor Name Parsing

**YAML 1.2.2**: [101] ns-anchor-name = [102] ns-anchor-char+ (§6.9.2)

Anchor names consist of non-empty sequences of
characters that are not flow indicators, whitespace, or line breaks.
In practice, most implementations restrict to `[a-zA-Z0-9_-]`.
-/

/--
Parse an anchor name: one or more `ns-anchor-char` characters.

**YAML 1.2.2**: [101] ns-anchor-name (§6.9.2, https://yaml.org/spec/1.2.2/#692-node-anchors)
- [102] ns-anchor-char: `ns-char - c-flow-indicator`
-/
@[yaml_spec "6.9.2" 101 "ns-anchor-name"]
def anchorName : YamlParser String :=
  withErrorMessage "expected anchor name" do
    let chars ← takeMany1 (tokenFilter isAnchorChar)
    return String.ofList chars.toList

/-! ## Anchor Map Operations

These combinators use `Parser.getStream` / `Parser.setStream` to
access the `YamlStream.anchorMap` field.  They delegate to
`AnchorMap.insert` / `AnchorMap.find?` (Types.lean), keeping the
parser-level code free of array manipulation.

**Position contract**: `storeAnchor` and `lookupAnchor` modify only
`anchorMap`, never `startPos`/`line`/`col`.  Combined with
`setPosition_preserves_anchorMap`, this means anchor state is
orthogonal to position state — a clean separation for proofs.
-/

/--
Store an anchor binding in the stream's anchor map.

Before storing, any alias nodes within `val` are resolved against the
current anchor map.  This ensures the map always contains fully-resolved
values — a prerequisite for the single-pass **Compose** step (§3.1).

**Post-condition** (from `AnchorMap.find?_insert`):
  `AnchorMap.find? (updated map) name = some resolved`

Replaces any existing binding for the same name (YAML allows
anchor name reuse within a document, §3.2.2.2).
-/
def storeAnchor (name : String) (val : YamlValue) : YamlParser Unit := do
  let s ← getStream
  let resolved := val.resolveAliases s.anchorMap
  setStream { s with anchorMap := AnchorMap.insert s.anchorMap name resolved }

/--
Look up an anchor in the stream's anchor map.

**Contract**: pure read — does not consume input, does not
modify position or anchor map.
-/
def lookupAnchor (name : String) : YamlParser (Option YamlValue) := do
  let s ← getStream
  return AnchorMap.find? s.anchorMap name

/--
Reset the anchor map to empty.

Called at document boundaries to enforce document-scoped anchors
(YAML 1.2.2 §3.2.2.2).

**Post-condition** (from `AnchorMap.find?_empty`):
  `∀ name, AnchorMap.find? (reset map) name = none`
-/
def resetAnchorMap : YamlParser Unit := do
  let s ← getStream
  setStream { s with anchorMap := AnchorMap.empty }

/--
Retrieve the current anchor map from the stream.

**Contract**: pure read — does not consume input, does not
modify position or anchor map.

Used by `document` to capture the anchor map into `YamlDocument.anchors`
before returning, enabling the **Compose** step (§3.1) to resolve aliases.
-/
def getAnchorMap : YamlParser AnchorMap := do
  let s ← getStream
  return s.anchorMap

/-! ## Alias Parsing

**YAML 1.2.2**: [103] c-ns-alias-node (§7.1, https://yaml.org/spec/1.2.2/#71-alias-nodes)
- [14] c-alias (`*`) + [101] ns-anchor-name

An alias node is denoted by `*anchor-name`. It refers to the most
recent node with the corresponding anchor.
-/

/--
Parse an alias node: `*name`.

**YAML 1.2.2**: [103] c-ns-alias-node (§7.1)
- [14] c-alias (`*`) + [101] ns-anchor-name

Returns `.alias name` — the serialization-tree form.
The **Compose** step (§3.1) later resolves this to the anchored value.

**Validation**: if the anchor is undefined, a validation error is recorded
in the stream (survives backtracking). The alias node is still returned.
The top-level parser checks `validationError` and rejects the input.
-/
@[yaml_spec "7.1" 103 "c-ns-alias-node"]
def parseAlias : YamlParser YamlValue :=
  withErrorMessage "expected alias (*name)" do
    let _ ← char '*'
    let name ← anchorName
    -- Validate: anchor must be defined before use (§7.1).
    match ← lookupAnchor name with
    | some _ => pure ()
    | none => setValidationError s!"undefined anchor: *{name}"
    return .alias name

/-! ## Anchor Prefix Parsing

**YAML 1.2.2**: [99] c-ns-anchor-property (§6.9.2, https://yaml.org/spec/1.2.2/#692-node-anchors)
- [100] c-anchor (`&`) + [101] ns-anchor-name

`&name` followed by whitespace, then the content node.

The anchor name is parsed and returned. The caller is responsible
for parsing the following value and calling `storeAnchor`.
-/

/--
Parse an anchor prefix: `&name` followed by optional whitespace.

**YAML 1.2.2**: [99] c-ns-anchor-property (§6.9.2)
- [100] c-anchor (`&`) + [101] ns-anchor-name

Returns the anchor name. Does not store anything — the caller
must parse the value and call `storeAnchor name value`.
-/
@[yaml_spec "6.9.2" 99 "c-ns-anchor-property"]
def parseAnchorPrefix : YamlParser String :=
  withErrorMessage "expected anchor (&name)" do
    let _ ← char '&'
    let name ← anchorName
    skipHWhitespace
    return name

end Lean4Yaml.Parse
