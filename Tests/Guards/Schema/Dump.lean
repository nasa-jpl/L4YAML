import L4YAML.Schema.Dump

namespace L4YAML.Schema.Dump

open L4YAML
open L4YAML.Dump
open L4YAML.Emit
open L4YAML.TokenParser
open L4YAML.Schema
open L4YAML.Schema.Dump

#guard dumpTyped true == "\"true\""
#guard dumpTyped false == "\"false\""
#guard dumpTyped (42 : Nat) == "42"
#guard dumpTyped (0 : Nat) == "0"
#guard dumpTyped (-7 : Int) == "\"-7\""
#guard dumpTyped (100 : Int) == "100"
#guard dumpTyped "hello" == "hello"
#guard dumpTyped "world" == "world"
#guard dumpTyped () == "\"null\""
-- Bool → "true"/"false" → dump auto-quotes reserved words
#guard dumpAs true == "\"true\""
#guard dumpAs false == "\"false\""

-- Unit → "null" → dump auto-quotes
#guard dumpAs () == "\"null\""
#guard dumpTyped "key: value" == "\"key: value\""
#guard dumpTyped "" == "\"\""
#guard dumpTyped "simple" == "simple"
#guard dumpTyped (#["a", "b"] : Array String) == "- a\n- b"
#guard dumpTyped (#["x"] : Array String) == "- x"
#guard dumpTyped (#[] : Array String) == "[]"
#guard dumpTyped (["a", "b"] : List String) == "- a\n- b"
#guard dumpTyped (#[#["a", "b"], #["c"]] : Array (Array String)) ==
  "-\n  - a\n  - b\n-\n  - c"
#guard dumpTyped (some "hello" : Option String) == "hello"
#guard dumpTyped (none : Option String) == "\"null\""
#guard dumpTyped (some (42 : Nat) : Option Nat) == "42"
#guard dumpTyped "hello" flowConfig == "[hello]" ∨
      dumpTyped "hello" flowConfig == "hello"
-- Plain scalar is not affected by flow config (only collections)
#guard dumpTyped "hello" { scalarStyle := .doubleQuoted } == "\"hello\""
#guard dumpTyped "hello" { scalarStyle := .singleQuoted } == "'hello'"
-- Primitives round-trip through dump→parse→contentEq
#guard contentRoundTrips true
#guard contentRoundTrips false
#guard contentRoundTrips (42 : Nat)
#guard contentRoundTrips (0 : Nat)
#guard contentRoundTrips (-7 : Int)
#guard contentRoundTrips "hello"
#guard contentRoundTrips "world"
#guard contentRoundTrips "simple"
#guard contentRoundTrips ""
#guard contentRoundTrips "key: value"

-- Collections round-trip
#guard contentRoundTrips (#["a", "b"] : Array String)
#guard contentRoundTrips (#["x"] : Array String)
#guard contentRoundTrips (#[] : Array String)
#guard contentRoundTrips (["a", "b"] : List String)

-- Nested structures round-trip
#guard contentRoundTrips (#[#["a", "b"], #["c"]] : Array (Array String))

-- Options round-trip
#guard contentRoundTrips (some "hello" : Option String)
#guard contentRoundTrips (some (42 : Nat) : Option Nat)
#guard dumpTypedDocument (42 : Nat) == "42"
#guard dumpTypedDocument (42 : Nat) (directives := #[.yaml "1.2"]) ==
  "%YAML 1.2\n---\n42"
#guard dumpTypedDocument "hello" (directives := #[.yaml "1.2"]) ==
  "%YAML 1.2\n---\nhello"
#guard dumpTypedDocuments ([] : List Nat) == ""
#guard dumpTypedDocuments [(1 : Nat)] == "1"
#guard dumpTypedDocuments [(1 : Nat), 2] == "1\n---\n2\n..."

end L4YAML.Schema.Dump
