/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import Lean4Yaml.Schema.FromToYaml
import Lean4Yaml.Schema.Struct

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
  deriving Lean4Yaml.Schema.FromYaml, Lean4Yaml.Schema.ToYaml

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
-/

namespace Lean4Yaml.Deriving

open Lean Elab Command Meta

/-! ## Helper Functions -/

/-- Check if a field type is `Option α` by inspecting the projection function. -/
def isOptionField (structName : Name) (fieldName : Name) : CommandElabM Bool := do
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

/-! ## FromYaml Derive Handler -/

/-- Generate FromYaml instance for a simple enum (inductive with only 0-ary constructors). -/
def mkFromYamlEnumInstance (declName : Name) (ctors : Array Name) : CommandElabM Bool := do
  let getLastComponent (n : Name) : String :=
    n.toString.splitOn "." |>.getLast!

  -- Build code as string for enum parsing
  let mut code := s!"instance : Lean4Yaml.Schema.FromYaml {declName} where\n"
  code := code ++ "  fromYaml? v := do\n"
  code := code ++ "    let str ← Lean4Yaml.Schema.getString v\n"
  code := code ++ "    match str with\n"

  for ctor in ctors do
    let ctorName := getLastComponent ctor
    code := code ++ s!"    | \"{ctorName}\" => .ok {ctor}\n"

  let ctorNames := String.intercalate ", " (ctors.map getLastComponent |>.toList)
  let declShort := getLastComponent declName
  code := code ++ s!"    | other => .error (\"Invalid {declShort} value: \" ++ other ++ \". Expected one of: {ctorNames}\")\n"

  match Parser.runParserCategory (← getEnv) `command code with
  | .ok codeSyntax => elabCommand codeSyntax
  | .error err =>
      logError s!"Failed to parse generated code: {err}"
      return false

  return true

/-- Generate FromYaml instance for a structure. -/
def mkFromYamlInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false

  let declName := declNames[0]!
  let env ← getEnv

  -- Check if it's a structure FIRST (structures are also inductives in Lean)
  if let some info := getStructureInfo? env declName then
    let fields := info.fieldNames

    let mut code := s!"instance : Lean4Yaml.Schema.FromYaml {declName} where\n"
    code := code ++ "  fromYaml? v := do\n"
    code := code ++ "    let pairs ← Lean4Yaml.Schema.getMapping v\n"

    for fieldName in fields do
      let fieldNameStr := fieldName.toString
      let isOpt ← isOptionField declName fieldName

      if isOpt then
        code := code ++ s!"    let {fieldName} ← Lean4Yaml.Schema.getFieldOpt pairs \"{fieldNameStr}\"\n"
      else
        code := code ++ s!"    let {fieldName} ← Lean4Yaml.Schema.getField pairs \"{fieldNameStr}\"\n"

    code := code ++ "    return {\n"
    for i in [:fields.size] do
      let fieldName := fields[i]!
      code := code ++ s!"      {fieldName} := {fieldName}"
      if i < fields.size - 1 then
        code := code ++ ",\n"
      else
        code := code ++ "\n"
    code := code ++ "    }\n"

    match Parser.runParserCategory (← getEnv) `command code with
    | .ok codeSyntax => elabCommand codeSyntax
    | .error err =>
        logError s!"Failed to parse generated code: {err}"
        return false

    return true

  -- Check if it's an inductive (enum/sum type)
  if let some inductInfo := env.find? declName then
    if inductInfo.isInductive then
      let some (.inductInfo indVal) := env.find? declName
        | return false

      let ctors := indVal.ctors

      -- Check if all constructors are 0-ary (simple enum)
      let mut allZeroAry := true
      for ctor in ctors do
        let some ctorInfo := env.find? ctor
          | return false
        let hasArgs : Bool ← liftTermElabM do
          forallTelescopeReducing ctorInfo.type fun args _ => do
            pure (args.size > 0)
        if hasArgs == true then
          allZeroAry := false
          break

      if allZeroAry then
        return ← mkFromYamlEnumInstance declName ctors.toArray
      else
        logError s!"'{declName}' has constructors with parameters. Only simple enums (0-ary constructors) are currently supported."
        return false

  logError s!"'{declName}' is not a structure or simple enum"
  return false

/-- Derive handler registration for FromYaml. -/
initialize
  registerDerivingHandler ``Lean4Yaml.Schema.FromYaml mkFromYamlInstanceHandler

/-! ## ToYaml Derive Handler -/

/-- Generate ToYaml instance for a simple enum. -/
def mkToYamlEnumInstance (declName : Name) (ctors : Array Name) : CommandElabM Bool := do
  let getLastComponent (n : Name) : String :=
    n.toString.splitOn "." |>.getLast!

  let mut code := s!"instance : Lean4Yaml.Schema.ToYaml {declName} where\n"
  code := code ++ "  toYaml v :=\n"
  code := code ++ "    let str := match v with\n"

  for ctor in ctors do
    let ctorName := getLastComponent ctor
    code := code ++ s!"    | {ctor} => \"{ctorName}\"\n"

  code := code ++ "    Lean4Yaml.YamlValue.scalar {\n"
  code := code ++ "      content := str,\n"
  code := code ++ "      style := Lean4Yaml.ScalarStyle.plain,\n"
  code := code ++ "      tag := none\n"
  code := code ++ "    }\n"

  match Parser.runParserCategory (← getEnv) `command code with
  | .ok codeSyntax => elabCommand codeSyntax
  | .error err =>
      logError s!"Failed to parse generated code: {err}"
      return false

  return true

/-- Generate ToYaml instance for a structure. -/
def mkToYamlInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false

  let declName := declNames[0]!
  let env ← getEnv

  -- Check if it's a structure FIRST (structures are also inductives in Lean)
  if let some info := getStructureInfo? env declName then
    let fields := info.fieldNames

    let mut code := s!"instance : Lean4Yaml.Schema.ToYaml {declName} where\n"
    code := code ++ "  toYaml cfg := Lean4Yaml.Schema.mkMapping [\n"

    for i in [:fields.size] do
      let fieldName := fields[i]!
      let fieldNameStr := fieldName.toString
      code := code ++ s!"    (\"{fieldNameStr}\", Lean4Yaml.Schema.toYaml cfg.{fieldName})"
      if i < fields.size - 1 then
        code := code ++ ",\n"
      else
        code := code ++ "\n"
    code := code ++ "  ]\n"

    match Parser.runParserCategory (← getEnv) `command code with
    | .ok codeSyntax => elabCommand codeSyntax
    | .error err =>
        logError s!"Failed to parse generated code: {err}"
        return false

    return true

  -- Check if it's an inductive (enum/sum type)
  if let some inductInfo := env.find? declName then
    if inductInfo.isInductive then
      let some (.inductInfo indVal) := env.find? declName
        | return false

      let ctors := indVal.ctors

      -- Check if all constructors are 0-ary (simple enum)
      let mut allZeroAry := true
      for ctor in ctors do
        let some ctorInfo := env.find? ctor
          | return false
        let hasArgs : Bool ← liftTermElabM do
          forallTelescopeReducing ctorInfo.type fun args _ => do
            pure (args.size > 0)
        if hasArgs == true then
          allZeroAry := false
          break

      if allZeroAry then
        return ← mkToYamlEnumInstance declName ctors.toArray
      else
        logError s!"'{declName}' has constructors with parameters. Only simple enums (0-ary constructors) are currently supported."
        return false

  logError s!"'{declName}' is not a structure or simple enum"
  return false

/-- Derive handler registration for ToYaml. -/
initialize
  registerDerivingHandler ``Lean4Yaml.Schema.ToYaml mkToYamlInstanceHandler

end Lean4Yaml.Deriving
