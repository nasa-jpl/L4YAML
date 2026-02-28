import Lean4Yaml.Schema
import Lean4Yaml.Schema.FromToYaml
import Lean4Yaml.TokenParser

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
let config ← Lean4Yaml.parseAs AppConfig yamlString

-- Convert Lean value to YAML
let yamlValue := Lean4Yaml.toYaml myConfig

-- Parse with automatic schema resolution
let typed ← Lean4Yaml.parseTyped yamlString
```
-/

namespace Lean4Yaml

/-! ## Typed Parsing -/

/-- Parse YAML string and convert to a specific Lean type.
    Combines `parseYamlSingle` with `FromYaml` conversion. -/
def parseAs (α : Type) [Schema.FromYaml α] (s : String) : Except String α := do
  let yaml ← TokenParser.parseYamlSingle s
  Schema.fromYaml? yaml

/-- Convert a Lean value to a `YamlValue` for serialization. -/
def toYaml {α : Type} [Schema.ToYaml α] (value : α) : YamlValue :=
  Schema.toYaml value

/-- Parse YAML string with automatic schema resolution to `YamlType`. -/
def parseTyped (s : String) : Except String Schema.YamlType := do
  let yaml ← TokenParser.parseYamlSingle s
  pure (Schema.resolve yaml)

end Lean4Yaml
