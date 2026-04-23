import L4YAML.Proofs.RoundTrip.RoundTripComposition

namespace L4YAML.Proofs.RoundTripComposition

open L4YAML
open L4YAML.Schema
open L4YAML.Dump

-- §5: End-to-end resolve round-trip: dump → parse → resolve == resolve

-- Plain scalars
#guard resolveRoundTrips (.plainScalar "hello")
#guard resolveRoundTrips (.plainScalar "world")
#guard resolveRoundTrips (.plainScalar "")
#guard resolveRoundTrips (.plainScalar "foo bar")
#guard resolveRoundTrips (.plainScalar "some-identifier")
#guard resolveRoundTrips (.plainScalar "a/b/c")

-- Reserved words (auto-quoted, parser recovers intent)
#guard resolveRoundTrips (.plainScalar "true")
#guard resolveRoundTrips (.plainScalar "false")
#guard resolveRoundTrips (.plainScalar "null")
#guard resolveRoundTrips (.plainScalar "42")
#guard resolveRoundTrips (.plainScalar "-7")
#guard resolveRoundTrips (.plainScalar "0")
#guard resolveRoundTrips (.plainScalar "3.14")
#guard resolveRoundTrips (.plainScalar ".inf")
#guard resolveRoundTrips (.plainScalar ".nan")

-- Special characters (require quoting)
#guard resolveRoundTrips (.plainScalar "key: value")
#guard resolveRoundTrips (.plainScalar "line1\nline2")
#guard resolveRoundTrips (.plainScalar "tab\there")
#guard resolveRoundTrips (.plainScalar "# not a comment")

-- Double-quoted scalars
#guard resolveRoundTrips (.scalar ⟨"hello", .doubleQuoted, none, none, none⟩)
#guard resolveRoundTrips (.scalar ⟨"escaped: \n", .doubleQuoted, none, none, none⟩)

-- Flow sequences
#guard resolveRoundTrips (.sequence .flow #[])
#guard resolveRoundTrips (.sequence .flow #[.plainScalar "a"])
#guard resolveRoundTrips (.sequence .flow #[.plainScalar "a", .plainScalar "b"] none)
#guard resolveRoundTrips (.sequence .flow #[.plainScalar "x", .plainScalar "y", .plainScalar "z"] none)

-- Block sequences
#guard resolveRoundTrips (.sequence .block #[])
#guard resolveRoundTrips (.sequence .block #[.plainScalar "a"] none)
#guard resolveRoundTrips (.sequence .block #[.plainScalar "a", .plainScalar "b"] none)

-- Flow mappings
#guard resolveRoundTrips (.mapping .flow #[])
#guard resolveRoundTrips (.mapping .flow #[(.plainScalar "key", .plainScalar "val")] none)
#guard resolveRoundTrips (.mapping .flow
  #[(.plainScalar "a", .plainScalar "1"), (.plainScalar "b", .plainScalar "2")] none)

-- Block mappings
#guard resolveRoundTrips (.mapping .block #[])
#guard resolveRoundTrips (.mapping .block #[(.plainScalar "k", .plainScalar "v")] none)
#guard resolveRoundTrips (.mapping .block
  #[(.plainScalar "x", .plainScalar "1"), (.plainScalar "y", .plainScalar "2")] none)

-- Nested structures
#guard resolveRoundTrips (.mapping .block
  #[(.plainScalar "items",
     .sequence .block #[.plainScalar "a", .plainScalar "b"] none)] none)
#guard resolveRoundTrips (.sequence .block
  #[.mapping .flow #[(.plainScalar "k", .plainScalar "v")] none] none)
#guard resolveRoundTrips (.mapping .block
  #[(.plainScalar "nested",
     .mapping .block #[(.plainScalar "inner", .plainScalar "val")] none)] none)

-- DumpConfig variations
#guard resolveRoundTrips (.plainScalar "hello") { scalarStyle := .doubleQuoted }
#guard resolveRoundTrips (.plainScalar "hello") { scalarStyle := .singleQuoted }
#guard resolveRoundTrips (.sequence .block #[.plainScalar "a"] none) { defaultStyle := .flow }

-- §6: Typed round-trips: toYaml → dump → parse → resolve
#guard resolveRoundTripsTyped true
#guard resolveRoundTripsTyped false
#guard resolveRoundTripsTyped (0 : Nat)
#guard resolveRoundTripsTyped (42 : Nat)
#guard resolveRoundTripsTyped (100 : Int)
#guard resolveRoundTripsTyped (-7 : Int)
#guard resolveRoundTripsTyped "hello"
#guard resolveRoundTripsTyped ""
#guard resolveRoundTripsTyped ()
#guard resolveRoundTripsTyped (some "hello" : Option String)
#guard resolveRoundTripsTyped (none : Option String)
#guard resolveRoundTripsTyped (#["a", "b"] : Array String)
#guard resolveRoundTripsTyped (#[] : Array String)
#guard resolveRoundTripsTyped (["x", "y"] : List String)
#guard resolveRoundTripsTyped (#[#["a", "b"], #["c"]] : Array (Array String))

end L4YAML.Proofs.RoundTripComposition
