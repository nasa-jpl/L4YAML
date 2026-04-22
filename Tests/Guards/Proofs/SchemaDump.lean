import L4YAML.Proofs.Schema.SchemaDump

namespace L4YAML.Proofs.SchemaDump

open L4YAML
open L4YAML.Schema
open L4YAML.Schema.Dump
open L4YAML.Dump
open L4YAML.Emit
open L4YAML.TokenParser

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

-- Option content round-trips (§5b)
#guard contentRoundTrips (some () : Option Unit)
#guard contentRoundTrips (none : Option String)
#guard contentRoundTrips (some (42 : Nat) : Option Nat)
#guard contentRoundTrips (some "hello" : Option String)

-- Typed round-trips
#guard contentRoundTrips "abc"
#guard contentRoundTrips (0 : Int)
#guard contentRoundTrips (1 : Nat)
#guard contentRoundTrips (some true : Option Bool)
#guard contentRoundTrips (some false : Option Bool)

end L4YAML.Proofs.SchemaDump
