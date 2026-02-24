import Lean4Yaml.Types
import Lean4Yaml.Schema
import Std.Data.HashMap

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# FromYaml and ToYaml Type Classes

Type classes for converting between YAML and Lean types, inspired by Lean's
`FromJson`/`ToJson` pattern.

## Architecture

Three typeclasses form the conversion pipeline:
- `FromYamlType` — conversion from resolved `YamlType` (post-schema-resolution)
- `FromYaml` — conversion from raw `YamlValue` (pre-resolution)
- `ToYaml` — conversion from Lean type to `YamlValue`

The default `FromYaml` instance bridges to `FromYamlType` via `Schema.resolve`,
so most users only need to implement `FromYamlType`.

## Instances Provided

- **Primitives**: `Unit`, `Bool`, `Int`, `Nat`, `String`, `Float`
- **Collections**: `Array α`, `List α`, `Option α`
- **Maps**: `Std.HashMap String α`
-/

namespace Lean4Yaml.Schema

universe u

/-! ## Type Classes -/

/-- Convert from a resolved `YamlType` (post-schema-resolution).
    Most types should implement this — the default `FromYaml` instance
    handles `resolve` automatically. -/
class FromYamlType (α : Type u) where
  fromYamlType? : YamlType → Except String α

export FromYamlType (fromYamlType?)

/-- Convert from a raw `YamlValue` (pre-resolution).
    The default instance delegates to `FromYamlType` via `Schema.resolve`.
    Override for types that need direct access to style/tag metadata. -/
class FromYaml (α : Type u) where
  fromYaml? : YamlValue → Except String α

export FromYaml (fromYaml?)

/-- Convert a Lean value to a `YamlValue` for serialization. -/
class ToYaml (α : Type u) where
  toYaml : α → YamlValue

export ToYaml (toYaml)

/-! ## Default Implementation: FromYamlType → FromYaml via resolve -/

instance {α : Type u} [FromYamlType α] : FromYaml α where
  fromYaml? v := fromYamlType? (resolve v)

/-! ## Primitive Type Instances -/

instance : FromYamlType Unit where
  fromYamlType? | .null => .ok ()
                | v => .error s!"expected null, got {repr v}"

instance : ToYaml Unit where
  toYaml _ := YamlValue.scalar { content := "null", style := .plain }

instance : FromYamlType Bool where
  fromYamlType? | .bool b => .ok b
                | v => .error s!"expected boolean, got {repr v}"

instance : ToYaml Bool where
  toYaml b := YamlValue.scalar {
    content := if b then "true" else "false",
    style := .plain
  }

instance : FromYamlType Int where
  fromYamlType? | .int n => .ok n
                | v => .error s!"expected integer, got {repr v}"

instance : ToYaml Int where
  toYaml n := YamlValue.scalar {
    content := toString n,
    style := .plain
  }

instance : FromYamlType Nat where
  fromYamlType? | .int n =>
                    if n >= 0 then .ok n.toNat
                    else .error s!"expected non-negative integer, got {n}"
                | v => .error s!"expected integer, got {repr v}"

instance : ToYaml Nat where
  toYaml n := YamlValue.scalar {
    content := toString n,
    style := .plain
  }

instance : FromYamlType String where
  fromYamlType? | .str s => .ok s
                | v => .error s!"expected string, got {repr v}"

instance : ToYaml String where
  toYaml s := YamlValue.scalar {
    content := s,
    style := .plain
  }

instance : FromYamlType Float where
  fromYamlType? | .float f => .ok f.toFloat
                | .int n => .ok (Float.ofInt n)
                | v => .error s!"expected float, got {repr v}"

instance : ToYaml Float where
  toYaml f := YamlValue.scalar {
    content := toString f,
    style := .plain
  }

/-! ## Collection Instances -/

instance {α : Type u} [FromYamlType α] : FromYamlType (Array α) where
  fromYamlType? | .seq items => items.mapM fromYamlType?
                | v => .error s!"expected sequence, got {repr v}"

instance {α : Type u} [ToYaml α] : ToYaml (Array α) where
  toYaml arr := YamlValue.sequence .block (arr.map toYaml)

instance {α : Type u} [FromYamlType α] : FromYamlType (List α) where
  fromYamlType? v := (fromYamlType? v : Except String (Array α)).map Array.toList

instance {α : Type u} [ToYaml α] : ToYaml (List α) where
  toYaml list := toYaml list.toArray

instance {α : Type u} [FromYamlType α] : FromYamlType (Option α) where
  fromYamlType? | .null => .ok none
                | v => some <$> fromYamlType? v

instance {α : Type u} [ToYaml α] : ToYaml (Option α) where
  toYaml | none => YamlValue.scalar { content := "null", style := .plain }
         | some a => toYaml a

/-! ## HashMap Instances -/

/-- Convert a `YamlType` to a string key for HashMap use. -/
private def yamlTypeToString? : YamlType → Except String String
  | .str s => .ok s
  | .int n => .ok (toString n)
  | .bool b => .ok (toString b)
  | .null => .ok "null"
  | v => .error s!"HashMap keys must be strings or convertible to strings, got {repr v}"

instance {α : Type} [FromYamlType α] : FromYamlType (Std.HashMap String α) where
  fromYamlType?
    | .map pairs => do
        pairs.foldlM (init := ({} : Std.HashMap String α)) fun acc pair => do
          let (keyType, valType) := pair
          let key ← yamlTypeToString? keyType
          let val ← fromYamlType? valType
          pure (acc.insert key val)
    | v => .error s!"expected mapping, got {repr v}"

instance {α : Type u} [ToYaml α] : ToYaml (Std.HashMap String α) where
  toYaml hm :=
    let pairs := hm.toArray.map fun (k, v) =>
      (YamlValue.scalar { content := k, style := .plain }, toYaml v)
    YamlValue.mapping .block pairs

/-- Direct `FromYaml` instance for `HashMap String String` without schema resolution.
    Reads key/value directly from the raw `YamlValue` mapping. -/
instance : FromYaml (Std.HashMap String String) where
  fromYaml?
    | .mapping _ pairs _ _ => do
        let mut result : Std.HashMap String String := {}
        for (keyVal, valueVal) in pairs do
          let key ← match keyVal with
            | .scalar s => .ok s.content
            | _ => .error s!"HashMap keys must be scalars, got {repr keyVal}"
          let value ← match valueVal with
            | .scalar s => .ok s.content
            | _ => .error s!"HashMap String String values must be scalars, got {repr valueVal}"
          result := result.insert key value
        pure result
    | v => .error s!"expected mapping, got {repr v}"

/-- Generic direct `FromYaml` instance for `HashMap String α` without schema resolution. -/
instance {α : Type} [FromYaml α] : FromYaml (Std.HashMap String α) where
  fromYaml?
    | .mapping _ pairs _ _ => do
        let mut result : Std.HashMap String α := {}
        for (keyVal, valueVal) in pairs do
          let key ← match keyVal with
            | .scalar s => .ok s.content
            | _ => .error s!"HashMap keys must be scalars, got {repr keyVal}"
          let value ← fromYaml? valueVal
          result := result.insert key value
        pure result
    | v => .error s!"expected mapping, got {repr v}"

end Lean4Yaml.Schema
