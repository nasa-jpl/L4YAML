import Lean4Yaml.Proofs.SchemaDump

namespace Lean4Yaml.Proofs.SchemaDump

open Lean4Yaml
open Lean4Yaml.Schema
open Lean4Yaml.Schema.Dump
open Lean4Yaml.Dump
open Lean4Yaml.Emit
open Lean4Yaml.TokenParser

#guard toYaml true == YamlValue.scalar { content := "true", style := .plain }
#guard toYaml false == YamlValue.scalar { content := "false", style := .plain }
#guard toYaml (42 : Nat) == YamlValue.scalar { content := "42", style := .plain }
#guard toYaml () == YamlValue.scalar { content := "null", style := .plain }
#guard toYaml "hello" == YamlValue.scalar { content := "hello", style := .plain }
-- Empty string: content round-trips but typed round-trip fails because
-- schema resolution maps "" → null (YAML semantics). Expected behavior.
#guard contentRoundTrips (α := String) ""
section SchemaDumpExtendedGuards

-- Strings with various special characters
#guard contentRoundTrips "has #comment"
#guard contentRoundTrips "{flow}"
#guard contentRoundTrips "[array]"
#guard contentRoundTrips "tab\there"

-- Nat edge cases
#guard contentRoundTrips (1 : Nat)
#guard contentRoundTrips (999 : Nat)

-- Int edge cases
#guard contentRoundTrips (0 : Int)
#guard contentRoundTrips (-1 : Int)

-- Nested structures
#guard contentRoundTrips (#[#["a"]] : Array (Array String))
#guard contentRoundTrips (#[(#[] : Array String)] : Array (Array String))

-- Various config combinations
#guard contentRoundTrips (42 : Nat) (cfg := { scalarStyle := .doubleQuoted })
#guard contentRoundTrips (42 : Nat) (cfg := { scalarStyle := .singleQuoted })
#guard contentRoundTrips (#["a"] : Array String) (cfg := { indent := 4 })

end SchemaDumpExtendedGuards

end Lean4Yaml.Proofs.SchemaDump
