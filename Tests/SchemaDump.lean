module

public import L4YAML.Spec.Types
public import L4YAML.Schema.Schema
public import L4YAML.Schema.FromToYaml
public import L4YAML.Schema.Dump
public import L4YAML.Schema.Api
public import L4YAML.Schema.Deriving
public import L4YAML.Output.Json
public import L4YAML.Config.Config
public import L4YAML.Output.Dump
public import L4YAML.Output.Emitter
public import L4YAML.Parser.Composition
public import Tests.VerifiedResult

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Schema ↔ Dump Integration Tests

Runtime verification tests for the `ToYaml + dump` pipeline (Phase 7.4).
These mirror the `native_decide` theorems and `#guard` checks in
`Proofs/SchemaDump.lean` and `Schema/Dump.lean`, providing explicit
coverage tracking in the HTML dashboard.

## Categories

1. **Primitive serialization** — `dumpTyped` output for built-in types
2. **Collection serialization** — arrays, lists, nested structures
3. **Option serialization** — some/none handling
4. **Content round-trip** — dump→parse→contentEq for all types
5. **Typed round-trip** — α→String→α for built-in types
6. **Document serialization** — directives, multi-document support
7. **Config variations** — quoting styles, indentation, flow mode
-/

open L4YAML
open L4YAML.Schema
open L4YAML.Schema.Dump
open L4YAML.Dump
open L4YAML.Emit
open L4YAML.TokenParser
open Tests

namespace Tests.SchemaDump

/-! ## §1: Primitive Serialization -/

def testPrimitives (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Primitive serialization"

  check state "Bool true → true (bare, not a string)"
    (dumpTyped true == "true")
  check state "Bool false → false (bare, not a string)"
    (dumpTyped false == "false")
  check state "Nat 0 → 0"
    (dumpTyped (0 : Nat) == "0")
  check state "Nat 42 → 42"
    (dumpTyped (42 : Nat) == "42")
  check state "Nat 999 → 999"
    (dumpTyped (999 : Nat) == "999")
  check state "Int -7 → -7 (plain, leading minus allowed)"
    (dumpTyped (-7 : Int) == "-7")
  check state "Int 100 → 100"
    (dumpTyped (100 : Int) == "100")
  check state "Int 0 → 0"
    (dumpTyped (0 : Int) == "0")
  check state "String simple → plain"
    (dumpTyped "hello" == "hello")
  check state "String with space → plain"
    (dumpTyped "two words" == "two words")
  check state "String empty → \"\""
    (dumpTyped "" == "\"\"")
  check state "String colon-space → quoted"
    (dumpTyped "key: value" == "\"key: value\"")
  check state "Unit → null (bare, not a string)"
    (dumpTyped () == "null")
  check state "String \"null\" → quoted (a string that spells null)"
    (dumpTyped "null" == "\"null\"")
  check state "String \"true\" → quoted (a string that spells a bool)"
    (dumpTyped "true" == "\"true\"")

/-! ## §2: Collection Serialization -/

def testCollections (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Collection serialization"

  check state "Array String [a,b] → block sequence"
    (dumpTyped (#["a", "b"] : Array String) == "- a\n- b")
  check state "Array String [x] → singleton block"
    (dumpTyped (#["x"] : Array String) == "- x")
  check state "Array String [] → []"
    (dumpTyped (#[] : Array String) == "[]")
  check state "List String [a,b] → block sequence"
    (dumpTyped (["a", "b"] : List String) == "- a\n- b")
  check state "Nested Array → nested block"
    (dumpTyped (#[#["a", "b"], #["c"]] : Array (Array String)) ==
      "-\n  - a\n  - b\n-\n  - c")
  check state "Array Nat [1,2,3] → block sequence"
    (dumpTyped (#[(1 : Nat), 2, 3] : Array Nat) == "- 1\n- 2\n- 3")
  check state "Array Bool → block of bare booleans"
    (dumpTyped (#[true, false] : Array Bool) == "- true\n- false")

/-! ## §3: Option Serialization -/

def testOptions (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Option serialization"

  check state "some String → plain scalar"
    (dumpTyped (some "hello" : Option String) == "hello")
  check state "none String → null (bare)"
    (dumpTyped (none : Option String) == "null")
  check state "some Nat → plain scalar"
    (dumpTyped (some (42 : Nat) : Option Nat) == "42")
  check state "none Nat → null (bare)"
    (dumpTyped (none : Option Nat) == "null")
  check state "some Bool → bare boolean"
    (dumpTyped (some true : Option Bool) == "true")

/-! ## §4: Content Round-Trip -/

def testContentRoundTrip (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Content round-trip (dump→parse→contentEq)"

  -- Primitives
  check state "Bool true round-trips"
    (contentRoundTrips true)
  check state "Bool false round-trips"
    (contentRoundTrips false)
  check state "Nat 0 round-trips"
    (contentRoundTrips (0 : Nat))
  check state "Nat 42 round-trips"
    (contentRoundTrips (42 : Nat))
  check state "Nat 999 round-trips"
    (contentRoundTrips (999 : Nat))
  check state "Int -7 round-trips"
    (contentRoundTrips (-7 : Int))
  check state "Int 100 round-trips"
    (contentRoundTrips (100 : Int))
  check state "String simple round-trips"
    (contentRoundTrips "hello")
  check state "String with space round-trips"
    (contentRoundTrips "two words")
  check state "String empty round-trips"
    (contentRoundTrips "")
  check state "String colon-space round-trips"
    (contentRoundTrips "key: value")
  check state "String has #comment round-trips"
    (contentRoundTrips "has #comment")
  check state "String {flow} round-trips"
    (contentRoundTrips "{flow}")
  check state "String [array] round-trips"
    (contentRoundTrips "[array]")
  check state "Unit round-trips"
    (contentRoundTrips ())

  -- Collections
  check state "Array [a,b] round-trips"
    (contentRoundTrips (#["a", "b"] : Array String))
  check state "Array [x] round-trips"
    (contentRoundTrips (#["x"] : Array String))
  check state "Array [] round-trips"
    (contentRoundTrips (#[] : Array String))
  check state "List [a,b] round-trips"
    (contentRoundTrips (["a", "b"] : List String))
  check state "Nested arrays round-trip"
    (contentRoundTrips (#[#["a", "b"], #["c"]] : Array (Array String)))

  -- Options
  check state "Option some String round-trips"
    (contentRoundTrips (some "hello" : Option String))
  check state "Option some Nat round-trips"
    (contentRoundTrips (some (42 : Nat) : Option Nat))

/-! ## §5: Typed Round-Trip -/

/-- Helper: check that typed round-trip returns the expected value. -/
def roundTripsTo {α : Type} [ToYaml α] [FromYaml α] [BEq α]
    (value : α) (cfg : DumpConfig := {}) : Bool :=
  match roundTripTyped α value cfg with
  | .ok v => v == value
  | .error _ => false

def testTypedRoundTrip (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Typed round-trip (α→String→α)"

  check state "Bool true → String → Bool"
    (roundTripsTo true)
  check state "Bool false → String → Bool"
    (roundTripsTo false)
  check state "Nat 42 → String → Nat"
    (roundTripsTo (42 : Nat))
  check state "Nat 0 → String → Nat"
    (roundTripsTo (0 : Nat))
  check state "Int 100 → String → Int"
    (roundTripsTo (100 : Int))
  check state "Int -7 → String → Int"
    (roundTripsTo (-7 : Int))
  check state "String hello → String → String"
    (roundTripsTo "hello")
  check state "String \"\" → String → String (quoted, so not null)"
    (roundTripsTo "")
  check state "String \"true\" → String → String (quoted, so not a bool)"
    (roundTripsTo "true")
  check state "String \"null\" → String → String (quoted, so not null)"
    (roundTripsTo "null")
  check state "String \"42\" → String → String (quoted, so not an int)"
    (roundTripsTo "42")
  check state "String colon-space → String → String"
    (roundTripsTo "key: value")
  check state "Unit → String → Unit"
    (roundTripsTo ())

/-! ## §6: Document Serialization -/

def testDocuments (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Document serialization"

  check state "dumpTypedDocument Nat no directives"
    (dumpTypedDocument (42 : Nat) == "42")
  check state "dumpTypedDocument Nat with YAML directive"
    (dumpTypedDocument (42 : Nat) (directives := #[.yaml "1.2"]) ==
      "%YAML 1.2\n---\n42")
  check state "dumpTypedDocument String with directive"
    (dumpTypedDocument "hello" (directives := #[.yaml "1.2"]) ==
      "%YAML 1.2\n---\nhello")
  check state "dumpTypedDocuments empty"
    (dumpTypedDocuments ([] : List Nat) == "")
  check state "dumpTypedDocuments single"
    (dumpTypedDocuments [(1 : Nat)] == "1")
  check state "dumpTypedDocuments two"
    (dumpTypedDocuments [(1 : Nat), 2] == "1\n---\n2\n...")

/-! ## §7: Config Variations -/

def testConfigVariations (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Config variations"

  check state "double-quoted config"
    (dumpTyped "hello" { scalarStyle := .doubleQuoted } == "\"hello\"")
  check state "single-quoted config"
    (dumpTyped "hello" { scalarStyle := .singleQuoted } == "'hello'")
  check state "custom indent array"
    (dumpTyped (#["a"] : Array String) { indent := 4 } == "- a")

  -- Config round-trips
  check state "double-quoted round-trips"
    (contentRoundTrips "hello" { scalarStyle := .doubleQuoted })
  check state "single-quoted round-trips"
    (contentRoundTrips "hello" { scalarStyle := .singleQuoted })
  check state "indent 4 array round-trips"
    (contentRoundTrips (#["a", "b"] : Array String) { indent := 4 })

/-! ## §8: Scalar Style and Core Schema Intent

YAML 1.2.2 §10.3.2 types only *plain* untagged scalars; a quoted scalar is a
string.  `toYaml` records non-string intent with a Core Schema tag and string
intent with quoting, so the dumped text means the same thing to `parseAs`, to
`yamlToJson`, and to any other Core Schema reader. -/

structure OptField where
  x : Option String
deriving BEq, L4YAML.Schema.FromYaml, L4YAML.Schema.ToYaml

/-- `parseAs` succeeded with exactly `a`. -/
def parsesTo {α : Type} [BEq α] (r : Except YamlError α) (a : α) : Bool :=
  match r with
  | .ok b => b == a
  | .error _ => false

def parseFails {α : Type} (r : Except YamlError α) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

/-- Core Schema JSON of a YAML text, or `none` on a scan error. -/
def jsonOf (yaml : String) : Option String :=
  (L4YAML.Json.streamToJson yaml).toOption

def testStyleAware (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Scalar style and Core Schema intent"

  -- Quoted scalars are strings, whatever they spell
  check state "parseAs String \"42\" → \"42\""
    (parsesTo (parseAs String "\"42\"\n") "42")
  check state "parseAs String \"true\" → \"true\""
    (parsesTo (parseAs String "\"true\"\n") "true")
  check state "parseAs String 'null' → \"null\""
    (parsesTo (parseAs String "'null'\n") "null")
  check state "parseAs Bool \"true\" is an error (it is a string)"
    (parseFails (parseAs Bool "\"true\"\n"))
  check state "parseAs Bool true → true"
    (parsesTo (parseAs Bool "true\n") true)
  check state "parseAs Bool !!bool \"true\" → true (explicit tag wins)"
    (parsesTo (parseAs Bool "!!bool \"true\"\n") true)
  check state "parseAs Nat \"42\" is an error"
    (parseFails (parseAs Nat "\"42\"\n"))

  -- Option: only a null-typed scalar is `none`
  check state "parseAs (Option String) null → none"
    (parsesTo (parseAs (Option String) "null\n") (none : Option String))
  check state "parseAs (Option String) ~ → none"
    (parsesTo (parseAs (Option String) "~\n") (none : Option String))
  check state "parseAs (Option String) \"null\" → some \"null\""
    (parsesTo (parseAs (Option String) "\"null\"\n") (some "null"))
  check state "field x: null → none"
    (parsesTo (parseAs OptField "x: null\n") ⟨none⟩)
  check state "field x: (empty) → none"
    (parsesTo (parseAs OptField "x:\n") ⟨none⟩)
  check state "field x: \"null\" → some \"null\""
    (parsesTo (parseAs OptField "x: \"null\"\n") ⟨some "null"⟩)
  check state "field x: \"\" → some \"\""
    (parsesTo (parseAs OptField "x: \"\"\n") ⟨some ""⟩)

  -- Dumps say what they mean
  check state "dump none field → x: null"
    (dumpTyped (⟨none⟩ : OptField) == "x: null")
  check state "dump some \"null\" field → x: \"null\""
    (dumpTyped (⟨some "null"⟩ : OptField) == "x: \"null\"")
  check state "dump some \"\" field → x: \"\""
    (dumpTyped (⟨some ""⟩ : OptField) == "x: \"\"")
  check state "none field round-trips"
    (roundTripsTo (⟨none⟩ : OptField))
  check state "some \"null\" field round-trips"
    (roundTripsTo (⟨some "null"⟩ : OptField))
  check state "Float 1.5 → 1.500000"
    (dumpTyped (1.5 : Float) == "1.500000")
  check state "Float +inf → .inf"
    (dumpTyped (1.0 / 0.0 : Float) == ".inf")
  check state "Float -inf → -.inf"
    (dumpTyped (-1.0 / 0.0 : Float) == "-.inf")
  check state "Float NaN → .nan"
    (dumpTyped (0.0 / 0.0 : Float) == ".nan")
  check state "Float 1.5 round-trips"
    (roundTripsTo (1.5 : Float))

  -- Parsed untagged numbers keep their type through dump (leading sign stays plain)
  check state "plain -7 (untagged) dumps plain"
    (dump (.plainScalar "-7") == "-7")
  check state "plain -1.5 (untagged) dumps plain"
    (dump (.plainScalar "-1.5") == "-1.5")
  check state "plain -7 round-trips as an int"
    (match parseYamlSingle (dump (.plainScalar "-7")) with
     | .ok v => (resolve v).isInt
     | .error _ => false)
  check state "plain -x (a string) is still quoted"
    (dump (.plainScalar "-x") == "\"-x\"")
  check state "HashMap key 0xFF stays the string \"0xFF\" in JSON"
    (jsonOf (dumpTyped ((Std.HashMap.emptyWithCapacity 1).insert "0xFF" (1 : Nat))) ==
      some "{\"0xFF\":1}")
  check state "HashMap key true stays a string key"
    (dumpTyped ((Std.HashMap.emptyWithCapacity 1).insert "true" (1 : Nat)) == "\"true\": 1")

  check state "DumpConfig YAML round-trip keeps plainCoreScalars := false"
    (match parseAs DumpConfig (dumpTyped ({ plainCoreScalars := false } : DumpConfig)) with
     | .ok c => c.plainCoreScalars == false
     | .error _ => false)

  -- The JSON axis reads the dumps the same way
  check state "yamlToJson (dumpTyped true) = true"
    (jsonOf (dumpTyped true) == some "true")
  check state "yamlToJson (dumpTyped \"true\") = \"true\""
    (jsonOf (dumpTyped "true") == some "\"true\"")
  check state "yamlToJson (dumpTyped none) = null"
    (jsonOf (dumpTyped (none : Option String)) == some "null")
  check state "yamlToJson (dumpTyped -7) = -7"
    (jsonOf (dumpTyped (-7 : Int)) == some "-7")
  check state "yamlToJson (dump some \"null\" field) = {\"x\":\"null\"}"
    (jsonOf (dumpTyped (⟨some "null"⟩ : OptField)) == some "{\"x\":\"null\"}")
  check state "yamlToJson (dump none field) = {\"x\":null}"
    (jsonOf (dumpTyped (⟨none⟩ : OptField)) == some "{\"x\":null}")

/-- Collect all schema-dump integration test results. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testPrimitives state
  testCollections state
  testOptions state
  testContentRoundTrip state
  testTypedRoundTrip state
  testDocuments state
  testConfigVariations state
  testStyleAware state
  let results ← finish state
  return {
    name := "schemadump"
    label := "Schema ↔ Dump Integration"
    sourceFile := "Tests/SchemaDump.lean"
    tests := results
  }

end Tests.SchemaDump

end Blanket
