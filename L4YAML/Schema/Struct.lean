/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Schema.FromToYaml

/-!
# Struct Support for FromYaml/ToYaml

Helper functions for implementing `FromYaml`/`ToYaml` instances for custom structures.

## Usage Pattern

For a structure like:
```lean
structure Config where
  host : String
  port : Nat
  enabled : Bool
```

Add instances manually:
```lean
instance : FromYaml Config where
  fromYaml? v := do
    let obj ← getMapping v
    return {
      host := ← getField obj "host"
      port := ← getField obj "port"
      enabled := ← getField obj "enabled"
    }

instance : ToYaml Config where
  toYaml cfg := mkMapping [
    ("host", toYaml cfg.host),
    ("port", toYaml cfg.port),
    ("enabled", toYaml cfg.enabled)
  ]
```

Or use `deriving FromYaml, ToYaml` (see `L4YAML/Schema/Deriving.lean`).
-/

namespace L4YAML.Schema

open L4YAML

/-! ## Mapping Extraction -/

/-- Extract mapping pairs from a `YamlValue`, or return an error. -/
def getMapping (v : YamlValue) : Except SchemaError (Array (YamlValue × YamlValue)) :=
  match v with
  | .mapping _ pairs _ _ => .ok pairs
  | _ => .error (.notAMapping v)

/-- Get scalar content from a `YamlValue`. -/
def getScalarContent (v : YamlValue) : Option String :=
  match v with
  | .scalar s => some s.content
  | _ => none

/-- Get string from a `YamlValue` for enum parsing. -/
def getString (v : YamlValue) : Except SchemaError String :=
  match v with
  | .scalar s => .ok s.content
  | _ => .error (.notAScalar v)

/-! ## Field Access -/

/-- Find a field in a mapping by string key. -/
def findField (pairs : Array (YamlValue × YamlValue)) (fieldName : String) : Option YamlValue :=
  pairs.findSome? fun (k, v) =>
    if getScalarContent k == some fieldName then some v else none

/-- Get and parse a required field from a mapping.
    Returns an error if the field is missing or cannot be converted. -/
def getField {α : Type} [FromYaml α] (pairs : Array (YamlValue × YamlValue)) (fieldName : String) :
    Except SchemaError α := do
  match findField pairs fieldName with
  | some v =>
      match fromYaml? v with
      | .ok val => .ok val
      | .error e => .error (.fieldConversionError fieldName e)
  | none => .error (.missingField fieldName)

/-- Get and parse an optional field from a mapping.
    Returns `none` if the field is missing or explicitly null. -/
def getFieldOpt {α : Type} [FromYaml α] (pairs : Array (YamlValue × YamlValue)) (fieldName : String) :
    Except SchemaError (Option α) := do
  match findField pairs fieldName with
  | some v =>
      match v with
      | .scalar s =>
          if (s.content.isEmpty || s.content == "null" || s.content == "~") && s.tag.isNone then
            .ok none
          else
            match fromYaml? v with
            | .ok val => .ok (some val)
            | .error e => .error (.fieldConversionError fieldName e)
      | _ =>
          match fromYaml? v with
          | .ok val => .ok (some val)
          | .error e => .error (.fieldConversionError fieldName e)
  | none => .ok none

/-! ## Mapping Construction -/

/-- Create a YAML mapping from a list of key-value pairs. -/
def mkMapping (pairs : List (String × YamlValue)) : YamlValue :=
  let yamlPairs := pairs.toArray.map fun (k, v) =>
    let key := YamlValue.scalar {
      content := k
      style := .plain
    }
    (key, v)
  YamlValue.mapping .block yamlPairs

/-- Add a field to an accumulator of mapping pairs. -/
def addField {α : Type} [ToYaml α] (acc : Array (YamlValue × YamlValue)) (name : String) (value : α) :
    Array (YamlValue × YamlValue) :=
  let key := YamlValue.scalar { content := name, style := .plain }
  acc.push (key, toYaml value)

/-- Add an optional field (skip if `none`). -/
def addFieldOpt {α : Type} [ToYaml α] (acc : Array (YamlValue × YamlValue)) (name : String) (value : Option α) :
    Array (YamlValue × YamlValue) :=
  match value with
  | some v => addField acc name v
  | none => acc

end L4YAML.Schema
