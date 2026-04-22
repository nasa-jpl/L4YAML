import L4YAML.Schema.Schema
import L4YAML.Schema.FromToYaml
import L4YAML.Parser.Composition

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Convenience API for Typed YAML Parsing

High-level functions for parsing YAML directly into Lean types.

## Usage

```lean
-- Parse YAML string into a specific type
let config ← L4YAML.parseAs AppConfig yamlString

-- Convert Lean value to YAML
let yamlValue := L4YAML.toYaml myConfig

-- Parse with automatic schema resolution
let typed ← L4YAML.parseTyped yamlString
```
-/

namespace L4YAML

/-! ## Typed Parsing -/

/-- Parse YAML string and convert to a specific Lean type.
    Combines `parseYamlSingle` with `FromYaml` conversion.
    Returns `YamlError` which can be either a `ScanError` (parse failure)
    or a `SchemaError` (type conversion failure). -/
def parseAs (α : Type) [Schema.FromYaml α] (s : String) : Except YamlError α := do
  let yaml ← (TokenParser.parseYamlSingle s).mapError YamlError.scanError
  (Schema.fromYaml? yaml).mapError YamlError.schemaError

/-- Convert a Lean value to a `YamlValue` for serialization. -/
def toYaml {α : Type} [Schema.ToYaml α] (value : α) : YamlValue :=
  Schema.toYaml value

/-- Parse YAML string with automatic schema resolution to `YamlType`. -/
def parseTyped (s : String) : Except ScanError Schema.YamlType := do
  let yaml ← TokenParser.parseYamlSingle s
  pure (Schema.resolve yaml)

end L4YAML
