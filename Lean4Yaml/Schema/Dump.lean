import Lean4Yaml.Types
import Lean4Yaml.Schema
import Lean4Yaml.Schema.FromToYaml
import Lean4Yaml.Schema.Struct
import Lean4Yaml.Dump
import Lean4Yaml.Emitter
import Lean4Yaml.TokenParser

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Schema ↔ Dump Integration (Phase 7.4)

Connects the `ToYaml` typeclass (Phase 7.2) with the style-aware dump
function (Phase 6) to provide the complete serialization pipeline:

```
α → YamlValue → String
```

## Key Functions

- `dumpTyped` — serialize a Lean value to a YAML string via `ToYaml + dump`
- `dumpAs` — serialize with default config (convenience alias)
- `dumpDocument` — serialize a value as a full YAML document with directives
- `roundTripTyped` — dump → parse → fromYaml round-trip for validation
- `contentRoundTrips` — dump → parse → contentEq check (proof-oriented)

## Architecture

The pipeline composes three independently verified layers:

1. **ToYaml** (`α → YamlValue`): typeclass-driven, produces plain scalars
   and block collections. Verified by type system coherence.
2. **dump** (`YamlValue → DumpConfig → String`): style-aware serializer
   with auto-quoting of reserved words and special characters.
   Verified by `Proofs/DumpRoundTrip.lean` (71 theorems + 40 guards).
3. **parseYamlSingle** (`String → Except String YamlValue`): the parser.
   Verified by `Proofs/Soundness.lean` and round-trip guards.

This module composes layers 1+2 and optionally 1+2+3 (for `roundTripTyped`).

## Zero Axioms

All functions are total. No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Schema.Dump

open Lean4Yaml
open Lean4Yaml.Dump
open Lean4Yaml.Emit
open Lean4Yaml.TokenParser

/-! ## Core Serialization Pipeline -/

/--
Serialize a Lean value to a YAML string.

Composes `ToYaml.toYaml` with the style-aware `dump` function.
This is the primary user-facing serialization entry point.

## Example
```lean
dumpTyped true           -- produces: "\"true\""
dumpTyped (42 : Nat)     -- produces: "42"
dumpTyped ["a", "b"]     -- produces: "- a\n- b"
```
-/
def dumpTyped {α : Type} [ToYaml α] (value : α) (cfg : DumpConfig := {}) : String :=
  dump (toYaml value) cfg

/--
Serialize a Lean value to a YAML string with default config.

Convenience alias for `dumpTyped value {}`.
-/
def dumpAs {α : Type} [ToYaml α] (value : α) : String :=
  dumpTyped value

/-! ## Document-Level Serialization -/

/--
Serialize a Lean value as a full YAML document with optional directives.

Wraps the value in a `YamlDocument` and delegates to `Lean4Yaml.Dump.dumpDocument`.

## Example
```lean
dumpTypedDocument (42 : Nat) (directives := #[.yaml "1.2"])
-- produces: "%YAML 1.2\n---\n42"
```
-/
def dumpTypedDocument {α : Type} [ToYaml α]
    (value : α) (cfg : DumpConfig := {})
    (directives : Array Directive := #[]) : String :=
  Lean4Yaml.Dump.dumpDocument { value := toYaml value, directives } cfg

/--
Serialize multiple Lean values as a YAML document stream.

## Example
```lean
dumpTypedDocuments [(1 : Nat), 2, 3]
-- produces: "1\n---\n2\n---\n3\n..."
```
-/
def dumpTypedDocuments {α : Type} [ToYaml α]
    (values : List α) (cfg : DumpConfig := {}) : String :=
  let docs := values.toArray.map fun v => ({ value := toYaml v } : YamlDocument)
  Lean4Yaml.Dump.dumpDocuments docs cfg

/-! ## Round-Trip Validation -/

/--
Dump → Parse → FromYaml round-trip.

Serializes a Lean value to YAML, parses it back, and converts to the
target type. Useful for validating that the serialization pipeline
preserves semantic content.

Returns `.error` if either the parse or the `FromYaml` conversion fails.
-/
def roundTripTyped (α : Type) {β : Type} [ToYaml β] [FromYaml α]
    (value : β) (cfg : DumpConfig := {}) : Except YamlError α := do
  let yaml ← (parseYamlSingle (dumpTyped value cfg)).mapError YamlError.scanError
  (fromYaml? yaml).mapError YamlError.schemaError

/--
Dump → Parse → contentEq round-trip check.

Verifies that the YAML produced by `dump (toYaml a)` parses back to a
content-equivalent `YamlValue`. This is the key property that the
proofs target:

```
∀ (a : α) [ToYaml α],
  contentRoundTrips a cfg = true
  → parse (dump (toYaml a) cfg) = .ok v'
  ∧ contentEq (toYaml a) v' = true
```
-/
def contentRoundTrips {α : Type} [ToYaml α]
    (value : α) (cfg : DumpConfig := {}) : Bool :=
  match parseYamlSingle (dumpTyped value cfg) with
  | .ok v' => contentEq (toYaml value) v'
  | .error _ => false

/-! ## Typed Round-Trip with Content Equivalence -/

/--
Full typed round-trip: α → YamlValue → String → YamlValue → α.

Returns `(parsedYaml, contentMatch, typedResult)` for detailed diagnostics.
-/
def roundTripDiagnostics {α : Type} [ToYaml α] [FromYaml α]
    (value : α) (cfg : DumpConfig := {}) :
    String × (Except ScanError (YamlValue × Bool × Except SchemaError α)) :=
  let yamlStr := dumpTyped value cfg
  let result := do
    let parsed ← parseYamlSingle yamlStr
    let ceq := contentEq (toYaml value) parsed
    let typed := fromYaml? parsed
    pure (parsed, ceq, typed)
  (yamlStr, result)

/-! ## Config Helpers -/

/-- Default config producing minimal, human-readable YAML. -/
def defaultConfig : DumpConfig := {}

/-- Config for flow-style output (compact, JSON-like). -/
def flowConfig : DumpConfig := { defaultStyle := .flow }

/-- Config for explicit double-quoting of all scalars. -/
def quotedConfig : DumpConfig := { scalarStyle := .doubleQuoted }

/-- Config with custom indentation width. -/
def indentConfig (n : Nat) : DumpConfig := { indent := n }

end Lean4Yaml.Schema.Dump

/-! ## Compile-Time Guards -/

section SchemaDumpGuards

open Lean4Yaml
open Lean4Yaml.Schema
open Lean4Yaml.Schema.Dump
open Lean4Yaml.Dump
open Lean4Yaml.Emit

/-! ### Primitive serialization -/


/-! ### Reserved word auto-quoting through ToYaml -/


/-! ### String with special characters -/


/-! ### Collection serialization -/


/-! ### Nested collection -/


/-! ### Option serialization -/


/-! ### Config overrides -/


/-! ### Content round-trip checks -/


/-! ### Document serialization -/


/-! ### Multi-document serialization -/


end SchemaDumpGuards
