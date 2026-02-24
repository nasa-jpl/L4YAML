import LeanYaml

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Typed YAML Parsing Examples

Demonstrates the FromYaml/ToYaml type class system for type-safe YAML parsing.
-/

namespace TypedExamples

open LeanYaml

/-! ## Basic Type Parsing -/

/-- Example: Parse boolean from YAML -/
def exampleBool : IO Unit := do
  let yaml := "enabled: true"
  match parseAs Bool yaml with
  | .ok value => IO.println s!"Parsed bool: {value}"
  | .error msg => IO.println s!"Error: {msg}"

/-- Example: Parse integer from YAML -/
def exampleInt : IO Unit := do
  let yaml := "count: 42"
  match parseAs Int yaml with
  | .ok value => IO.println s!"Parsed int: {value}"
  | .error msg => IO.println s!"Error: {msg}"

/-- Example: Parse string from YAML -/
def exampleString : IO Unit := do
  let yaml := "name: Alice"
  match parseAs String yaml with
  | .ok value => IO.println s!"Parsed string: {value}"
  | .error msg => IO.println s!"Error: {msg}"

/-- Example: Parse natural number from YAML -/
def exampleNat : IO Unit := do
  let yaml := "age: 25"
  match parseAs Nat yaml with
  | .ok value => IO.println s!"Parsed nat: {value}"
  | .error msg => IO.println s!"Error: {msg}"

/-! ## Collection Parsing -/

/-- Example: Parse array of integers -/
def exampleArray : IO Unit := do
  let yaml := "[1, 2, 3, 4, 5]"
  match parseAs (Array Int) yaml with
  | .ok values => IO.println s!"Parsed array: {values}"
  | .error msg => IO.println s!"Error: {msg}"

/-- Example: Parse list of strings -/
def exampleList : IO Unit := do
  let yaml := "- apple\n- banana\n- cherry"
  match parseAs (List String) yaml with
  | .ok values => IO.println s!"Parsed list: {values}"
  | .error msg => IO.println s!"Error: {msg}"

/-- Example: Parse optional value (present) -/
def exampleOptionPresent : IO Unit := do
  let yaml := "value: 123"
  match parseAs (Option Int) yaml with
  | .ok value => IO.println s!"Parsed option: {value}"
  | .error msg => IO.println s!"Error: {msg}"

/-- Example: Parse optional value (null) -/
def exampleOptionNull : IO Unit := do
  let yaml := "value: null"
  match parseAs (Option Int) yaml with
  | .ok value => IO.println s!"Parsed option: {value}"
  | .error msg => IO.println s!"Error: {msg}"

/-! ## Error Handling -/

/-- Example: Type mismatch error -/
def exampleTypeMismatch : IO Unit := do
  let yaml := "value: not_a_number"
  match parseAs Int yaml with
  | .ok value => IO.println s!"Parsed: {value}"
  | .error msg => IO.println s!"Expected error: {msg}"

/-- Example: Negative number to Nat error -/
def exampleNegativeNat : IO Unit := do
  let yaml := "value: -5"
  match parseAs Nat yaml with
  | .ok value => IO.println s!"Parsed: {value}"
  | .error msg => IO.println s!"Expected error: {msg}"

/-! ## ToYaml Examples -/

/-- Example: Convert Lean value to YAML -/
def exampleToYaml : IO Unit := do
  let value : Array Int := #[1, 2, 3]
  let yamlValue := toYaml value
  IO.println s!"YAML value: {repr yamlValue}"

/-- Example: Round-trip conversion -/
def exampleRoundTrip : IO Unit := do
  let original : List String := ["foo", "bar", "baz"]
  let yamlValue := toYaml original
  IO.println s!"Original: {original}"
  IO.println s!"YAML: {repr yamlValue}"
  -- Note: To complete round-trip, would need to serialize yamlValue to string

/-! ## Core Schema Examples -/

/-- Example: Automatic type detection with Core Schema -/
def exampleCoreSchema : IO Unit := do
  let yaml := "
values:
  - true
  - 42
  - 3.14
  - hello
  - null
"
  match parseTyped yaml with
  | .ok typed => IO.println s!"Typed value: {repr typed}"
  | .error msg => IO.println s!"Error: {msg}"

/-! ## Main Runner -/

def main : IO Unit := do
  IO.println "=== Basic Type Parsing ==="
  exampleBool
  exampleInt
  exampleString
  exampleNat

  IO.println "\n=== Collection Parsing ==="
  exampleArray
  exampleList
  exampleOptionPresent
  exampleOptionNull

  IO.println "\n=== Error Handling ==="
  exampleTypeMismatch
  exampleNegativeNat

  IO.println "\n=== ToYaml Examples ==="
  exampleToYaml
  exampleRoundTrip

  IO.println "\n=== Core Schema ==="
  exampleCoreSchema

end TypedExamples
