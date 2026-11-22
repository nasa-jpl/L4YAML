/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML
public import Tests.VerifiedResult

/-!
# Deriving `FromYaml`/`ToYaml` from a module-system consumer

This suite is itself a `module` file that reaches the library through a plain
`public import L4YAML` — no `meta import` — the way a downstream package built
with `requiresModuleSystem := true` would.  Its types are declared outside any
`public section` on purpose, so their names are private-mangled
(`_private.Tests.DerivingConsumer.0.Point`); one structure is public for
contrast.  The checks cover:

1. the deriving handlers are registered for such an importer;
2. the generated instances elaborate for private and public names, for
   structures (nested, `Option` fields) and for simple enums;
3. the derived instances round-trip through `toYaml` → `dump` → `parseAs`.
-/

open L4YAML L4YAML.Schema L4YAML.Schema.Dump Tests

namespace Tests.DerivingConsumer

inductive Color where
  | red
  | green
  | blue
deriving Repr, BEq, L4YAML.Schema.FromYaml, L4YAML.Schema.ToYaml

structure Point where
  x : Nat
  y : Nat
  label : Option String := none
deriving Repr, BEq, L4YAML.Schema.FromYaml, L4YAML.Schema.ToYaml

structure Shape where
  name : String
  origin : Point
  colors : Array Color
  weight : Option Nat := none
deriving Repr, BEq, L4YAML.Schema.FromYaml, L4YAML.Schema.ToYaml

public section

structure Config where
  host : String
  port : Nat
  tags : List String
deriving Repr, BEq, L4YAML.Schema.FromYaml, L4YAML.Schema.ToYaml

end

/-- `parseAs α (dumpTyped a)` gives back `a`. -/
def roundTrips {α : Type} [BEq α] [FromYaml α] [ToYaml α] (a : α) : Bool :=
  match parseAs α (dumpTyped a) with
  | .ok b => b == a
  | .error _ => false

def isError {α : Type} : Except YamlError α → Bool
  | .error _ => true
  | .ok _ => false

/-- The parse succeeded with exactly `a`. -/
def parsesTo {α : Type} [BEq α] (r : Except YamlError α) (a : α) : Bool :=
  match r with
  | .ok b => b == a
  | .error _ => false

def testParse (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Parsing into private-named types"

  check state "structure, required fields only"
    (parsesTo (parseAs Point "x: 1\ny: 2\n") { x := 1, y := 2 })
  check state "structure, optional field present"
    (parsesTo (parseAs Point "x: 1\ny: 2\nlabel: origin\n") { x := 1, y := 2, label := some "origin" })
  check state "structure, missing required field is an error"
    (isError (parseAs Point "x: 1\n"))
  check state "enum, known constructor"
    (parsesTo (parseAs Color "green") .green)
  check state "enum, unknown constructor is an error"
    (isError (parseAs Color "purple"))
  check state "nested structure with an array of enums"
    (parsesTo (parseAs Shape "name: tri\norigin:\n  x: 0\n  y: 0\ncolors:\n  - red\n  - blue\n")
      { name := "tri", origin := { x := 0, y := 0 }, colors := #[.red, .blue] })

def testDump (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Dumping private-named types"

  check state "structure fields in declaration order"
    (dumpTyped ({ x := 1, y := 2, label := some "origin" } : Point) == "x: 1\ny: 2\nlabel: origin")
  check state "enum as its constructor name"
    (dumpTyped Color.blue == "blue")
  check state "nested structure"
    (dumpTyped ({ name := "tri", origin := { x := 0, y := 0, label := some "o" }, colors := #[.red],
                  weight := some 2 } : Shape) ==
      "name: tri\norigin:\n  x: 0\n  y: 0\n  label: o\ncolors:\n  - red\nweight: 2")

def testRoundTrip (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Round trip"

  check state "private structure" (roundTrips ({ x := 3, y := 4, label := some "p" } : Point))
  check state "private structure, optional field absent" (roundTrips ({ x := 3, y := 4 } : Point))
  check state "private enum" (roundTrips Color.red)
  check state "private nested structure"
    (roundTrips ({ name := "sq", origin := { x := 1, y := 1 }, colors := #[.green, .blue],
                   weight := some 7 } : Shape))
  check state "public structure"
    (roundTrips ({ host := "localhost", port := 8080, tags := ["a", "b"] } : Config))

/-- Collect all module-consumer deriving test results. -/
public def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testParse state
  testDump state
  testRoundTrip state
  let results ← finish state
  return {
    name := "derivingconsumer"
    label := "Deriving from a module consumer"
    sourceFile := "Tests/DerivingConsumer.lean"
    tests := results
  }

end Tests.DerivingConsumer
