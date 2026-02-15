/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# YAML Value Types

Core AST types for representing YAML documents.

These types are intentionally identical to `LeanYaml.YamlValue` from lean4-yaml,
enabling the Schema/FromToYaml/Deriving/Emitter layers to be shared between
the original (unverified) and verified parser implementations.
-/

namespace Lean4Yaml

/-! ## Scalar Styles -/

/--
The five scalar styles defined in YAML 1.2.2
§7 (https://yaml.org/spec/1.2.2/#chapter-7-flow-style-productions) and
§8 (https://yaml.org/spec/1.2.2/#chapter-8-block-style-productions).

- **Plain**: Unquoted scalars determined by context
- **Single-quoted**: Literal strings with `''` escape only
- **Double-quoted**: Strings with full escape sequence support
- **Literal**: Block scalar preserving line breaks (`|`)
- **Folded**: Block scalar folding line breaks to spaces (`>`)
-/
inductive ScalarStyle where
  | plain
  | singleQuoted
  | doubleQuoted
  | literal
  | folded
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/--
A YAML scalar with style information.

We preserve style to support round-trip serialization.
The `tag` field supports explicit typing (e.g., `!!str`, `!!int`).
-/
structure Scalar where
  content : String
  style : ScalarStyle
  tag : Option String := none
  deriving Repr, BEq, Inhabited

/-! ## Collection Styles -/

/--
Block vs flow style for collections.

- **Block**: Indentation-based (`- item` or `key: value`)
- **Flow**: Bracketed JSON-like (`[item]` or `{key: value}`)
-/
inductive CollectionStyle where
  | block
  | flow
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/-! ## Core YAML Values -/

/--
Core YAML value types.

YAML 1.2.2 §3.2.1 (https://yaml.org/spec/1.2.2/#3211-nodes) defines three node kinds:
- **Scalar**: Opaque data (strings, numbers, booleans, null, etc.)
- **Sequence**: Ordered collection of nodes
- **Mapping**: Collection of key-value pairs

Each node can carry an optional tag for explicit type annotation.
-/
inductive YamlValue where
  | scalar (s : Scalar)
  | sequence (style : CollectionStyle) (items : Array YamlValue) (tag : Option String := none)
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue)) (tag : Option String := none)
  deriving Repr, BEq, Inhabited

/-! ## Directives -/

/-- YAML directives: `%YAML 1.2` and `%TAG !handle! prefix` -/
inductive Directive where
  | yaml (version : String)
  | tag (handle : String) (tagPrefix : String)
  deriving Repr, BEq, DecidableEq

/-! ## Documents -/

/--
A YAML document with optional directives.

YAML streams can contain multiple documents separated by `---` markers.
-/
structure YamlDocument where
  value : YamlValue
  directives : Array Directive := #[]
  deriving Repr, BEq

/-! ## Convenience Constructors -/

/-- Create a plain scalar value -/
def YamlValue.plainScalar (content : String) : YamlValue :=
  .scalar { content, style := .plain }

/-- Create a quoted scalar value -/
def YamlValue.quotedScalar (content : String) (style : ScalarStyle := .doubleQuoted) : YamlValue :=
  .scalar { content, style }

/-- Create a flow sequence -/
def YamlValue.flowSequence (items : Array YamlValue) : YamlValue :=
  .sequence .flow items

/-- Create a block sequence -/
def YamlValue.blockSequence (items : Array YamlValue) : YamlValue :=
  .sequence .block items

/-- Create a flow mapping -/
def YamlValue.flowMapping (pairs : Array (YamlValue × YamlValue)) : YamlValue :=
  .mapping .flow pairs

/-- Create a block mapping -/
def YamlValue.blockMapping (pairs : Array (YamlValue × YamlValue)) : YamlValue :=
  .mapping .block pairs

/-- Create the null value -/
def YamlValue.null : YamlValue :=
  .scalar { content := "", style := .plain, tag := some "!!null" }

/-! ## Value Inspection -/

/-- Check if a value is a scalar -/
def YamlValue.isScalar : YamlValue → Bool
  | .scalar _ => true
  | _ => false

/-- Check if a value is a sequence -/
def YamlValue.isSequence : YamlValue → Bool
  | .sequence .. => true
  | _ => false

/-- Check if a value is a mapping -/
def YamlValue.isMapping : YamlValue → Bool
  | .mapping .. => true
  | _ => false

/-- Extract scalar content if value is a scalar -/
def YamlValue.asString? : YamlValue → Option String
  | .scalar s => some s.content
  | _ => none

/-- Extract sequence items if value is a sequence -/
def YamlValue.asArray? : YamlValue → Option (Array YamlValue)
  | .sequence _ items _ => some items
  | _ => none

/-- Extract mapping pairs if value is a mapping -/
def YamlValue.asPairs? : YamlValue → Option (Array (YamlValue × YamlValue))
  | .mapping _ pairs _ => some pairs
  | _ => none

/-- Look up a key in a mapping by string content -/
def YamlValue.lookup? (v : YamlValue) (key : String) : Option YamlValue :=
  match v with
  | .mapping _ pairs _ =>
    pairs.findSome? fun (k, v) =>
      match k with
      | .scalar s => if s.content == key then some v else none
      | _ => none
  | _ => none

end Lean4Yaml
