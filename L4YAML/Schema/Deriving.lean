/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Lean
public import L4YAML.Schema.FromToYaml
public import L4YAML.Schema.Struct

@[expose] public section Blanket

/-!
# Automatic Deriving for FromYaml and ToYaml

This module provides derive handlers that automatically generate `FromYaml` and `ToYaml`
instances for structures and simple enums.

## Usage

```lean
structure Config where
  host : String
  port : Nat
  enabled : Bool
  age : Option Nat        -- Optional fields automatically detected!
  deriving L4YAML.Schema.FromYaml, L4YAML.Schema.ToYaml

-- Usage works automatically:
let config ← parseAs Config yamlString
let yaml := toYaml config
```

## Features

- Automatic field extraction from YAML mappings
- **Automatic detection of `Option` fields** — uses `getFieldOpt` for `Option α` types
- Handles nested structures (if they also have `FromYaml`/`ToYaml` instances)
- Field name → YAML key mapping (uses exact field names)
- Simple enums (0-ary constructors) mapped to/from string names

## Module-system consumers

The handlers are registered with `meta initialize`, so a plain `import L4YAML` from a
`module` file is enough to use `deriving`.  The instances are built as syntax rather
than as source text, so a type declared outside a `public section` — whose name is
private-mangled to `_private.<module>.0.<name>` — derives like any other.
-/

namespace L4YAML.Deriving

open Lean Elab Command Meta
open Lean.Parser.Term

/-! ## Helper Functions -/

/-- Last component of a name, seen through private mangling:
    `_private.M.0.Color.red` ↦ `"red"`. -/
meta def shortName (n : Name) : String :=
  match privateToUserName n with
  | .str _ s => s
  | n' => n'.toString

/-- Check if a field type is `Option α` by inspecting the projection function. -/
meta def isOptionField (structName : Name) (fieldName : Name) : CommandElabM Bool := do
  -- Get the projection function for this field
  let projName := structName ++ fieldName
  let env ← getEnv

  match env.find? projName with
  | none => return false
  | some info =>
      -- The projection function has type: structName → fieldType
      -- We need to get the return type (fieldType) and check if it's Option
      let fieldType := info.type

      -- Run in MetaM context to use whnf
      liftTermElabM do
        -- The type is a function type, so get the result type
        forallTelescopeReducing fieldType fun _ resultType => do
          let resultType ← whnf resultType
          -- Check if it's an application of Option
          return resultType.isAppOf ``Option

/-- Constructors of `declName` if it is an inductive whose constructors all take no
    arguments; `none` otherwise.  Structures are inductives too, so test for a
    structure first. -/
meta def simpleEnumCtors? (declName : Name) : CommandElabM (Option (Array Name)) := do
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? declName | return none
  for ctor in indVal.ctors do
    let some ctorInfo := env.find? ctor | return none
    let hasArgs : Bool ← liftTermElabM do
      forallTelescopeReducing ctorInfo.type fun args _ => pure (args.size > 0)
    if hasArgs then
      logError s!"'{declName}' has constructors with parameters. Only simple enums (0-ary constructors) are currently supported."
      return none
  return some indVal.ctors.toArray

/-! ## FromYaml Derive Handler -/

/-- Generate a `FromYaml` instance for a simple enum: the scalar's string content
    selects the constructor of that name. -/
meta def mkFromYamlEnumInstance (declName : Name) (ctors : Array Name) : CommandElabM Bool := do
  let mut alts : Array (TSyntax ``matchAlt) := #[]
  for ctor in ctors do
    let lit := Syntax.mkStrLit (shortName ctor)
    alts := alts.push (← `(matchAltExpr| | $lit:str => .ok $(mkIdent ctor)))
  let declShort := Syntax.mkStrLit (shortName declName)
  alts := alts.push (← `(matchAltExpr|
    | other => .error (L4YAML.SchemaError.unknownVariant other $declShort)))
  elabCommand (← `(instance : L4YAML.Schema.FromYaml $(mkIdent declName) where
    fromYaml? v := L4YAML.Schema.getString v >>= fun str =>
      match str with $alts:matchAlt*))
  return true

/-- Generate a `FromYaml` instance for a structure: one `getField`/`getFieldOpt` per
    field, chained with `>>=`, ending in a structure instance. -/
meta def mkFromYamlStructInstance (declName : Name) (fields : Array Name) : CommandElabM Bool := do
  let pairs := mkIdent `pairs
  let fids := fields.map mkIdent
  let mut body : Term ← `(pure { $[$fids:ident := $(id fids)],* })
  for f in fields.reverse do
    let fid := mkIdent f
    let key := Syntax.mkStrLit f.toString
    let getter ← if (← isOptionField declName f) then
      `(L4YAML.Schema.getFieldOpt $pairs $key)
    else
      `(L4YAML.Schema.getField $pairs $key)
    body ← `($getter >>= fun $fid:ident => $body)
  elabCommand (← `(instance : L4YAML.Schema.FromYaml $(mkIdent declName) where
    fromYaml? v := L4YAML.Schema.getMapping v >>= fun $pairs:ident => $body))
  return true

/-- Derive `FromYaml` for a structure or a simple enum. -/
meta def mkFromYamlInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  let declName := declNames[0]!
  if let some info := getStructureInfo? (← getEnv) declName then
    return ← mkFromYamlStructInstance declName info.fieldNames
  if let some ctors ← simpleEnumCtors? declName then
    return ← mkFromYamlEnumInstance declName ctors
  logError s!"'{declName}' is not a structure or simple enum"
  return false

/-- Derive handler registration for FromYaml. -/
meta initialize
  registerDerivingHandler ``L4YAML.Schema.FromYaml mkFromYamlInstanceHandler

/-! ## ToYaml Derive Handler -/

/-- Generate a `ToYaml` instance for a simple enum: a plain scalar carrying the
    constructor's name. -/
meta def mkToYamlEnumInstance (declName : Name) (ctors : Array Name) : CommandElabM Bool := do
  let mut alts : Array (TSyntax ``matchAlt) := #[]
  for ctor in ctors do
    let lit := Syntax.mkStrLit (shortName ctor)
    alts := alts.push (← `(matchAltExpr| | $(mkIdent ctor) => $lit:str))
  elabCommand (← `(instance : L4YAML.Schema.ToYaml $(mkIdent declName) where
    toYaml v := L4YAML.YamlValue.scalar {
      content := match v with $alts:matchAlt*,
      style := L4YAML.ScalarStyle.plain,
      tag := none
    }))
  return true

/-- Generate a `ToYaml` instance for a structure: a mapping with one entry per field,
    in declaration order. -/
meta def mkToYamlStructInstance (declName : Name) (fields : Array Name) : CommandElabM Bool := do
  let cfg := mkIdent `cfg
  let mut entries : Array Term := #[]
  for f in fields do
    let key := Syntax.mkStrLit f.toString
    entries := entries.push (← `(($key, L4YAML.Schema.toYaml ($cfg).$(mkIdent f))))
  elabCommand (← `(instance : L4YAML.Schema.ToYaml $(mkIdent declName) where
    toYaml $cfg:ident := L4YAML.Schema.mkMapping [$entries,*]))
  return true

/-- Derive `ToYaml` for a structure or a simple enum. -/
meta def mkToYamlInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  let declName := declNames[0]!
  if let some info := getStructureInfo? (← getEnv) declName then
    return ← mkToYamlStructInstance declName info.fieldNames
  if let some ctors ← simpleEnumCtors? declName then
    return ← mkToYamlEnumInstance declName ctors
  logError s!"'{declName}' is not a structure or simple enum"
  return false

/-- Derive handler registration for ToYaml. -/
meta initialize
  registerDerivingHandler ``L4YAML.Schema.ToYaml mkToYamlInstanceHandler

end L4YAML.Deriving

end Blanket
