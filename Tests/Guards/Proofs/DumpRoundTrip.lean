import L4YAML.Proofs.Output.DumpRoundTrip

namespace L4YAML.Proofs.DumpRoundTrip

open L4YAML
open L4YAML.Dump
open L4YAML.Emit
open L4YAML.TokenParser

private def dumpRoundTrips (v : YamlValue) (cfg : DumpConfig := {}) : Bool :=
  match parseYamlSingle (dump v cfg) with
  | .ok v' => contentEq v v'
  | .error _ => false

-- ═══════════════════════════════════════════════════════════════════
-- §4a: Plain scalar round-trips
-- ═══════════════════════════════════════════════════════════════════

#guard dumpRoundTrips (.plainScalar "hello")
#guard dumpRoundTrips (.plainScalar "world")
#guard dumpRoundTrips (.plainScalar "two words")
#guard dumpRoundTrips (.plainScalar "123")
#guard dumpRoundTrips (.plainScalar "foo-bar_baz")

-- ═══════════════════════════════════════════════════════════════════
-- §4b: Auto-quoted scalar round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Reserved words: auto-quoted → parsed as double-quoted string → content match
#guard dumpRoundTrips (.plainScalar "true")
#guard dumpRoundTrips (.plainScalar "false")
#guard dumpRoundTrips (.plainScalar "null")
#guard dumpRoundTrips (.plainScalar "yes")
#guard dumpRoundTrips (.plainScalar "~")

-- Empty string: auto-quoted as `""`
#guard dumpRoundTrips (.plainScalar "")

-- Special characters: auto-quoted
#guard dumpRoundTrips (.plainScalar "key: value")
#guard dumpRoundTrips (.plainScalar "has #comment")
#guard dumpRoundTrips (.plainScalar "{flow}")
#guard dumpRoundTrips (.plainScalar "[array]")

-- ═══════════════════════════════════════════════════════════════════
-- §4c: Double-quoted config round-trips
-- ═══════════════════════════════════════════════════════════════════

#guard dumpRoundTrips (.plainScalar "hello") { scalarStyle := .doubleQuoted }
#guard dumpRoundTrips (.plainScalar "special chars!") { scalarStyle := .doubleQuoted }

-- ═══════════════════════════════════════════════════════════════════
-- §4d: Single-quoted config round-trips
-- ═══════════════════════════════════════════════════════════════════

#guard dumpRoundTrips (.plainScalar "hello") { scalarStyle := .singleQuoted }
#guard dumpRoundTrips (.plainScalar "it's") { scalarStyle := .singleQuoted }

-- ═══════════════════════════════════════════════════════════════════
-- §4e: Flow collection round-trips
-- ═══════════════════════════════════════════════════════════════════

#guard dumpRoundTrips (.sequence .flow #[])
#guard dumpRoundTrips (.sequence .flow #[.plainScalar "a"])
#guard dumpRoundTrips (.sequence .flow #[.plainScalar "a", .plainScalar "b"])
#guard dumpRoundTrips (.mapping .flow #[])
#guard dumpRoundTrips (.mapping .flow #[
  (.plainScalar "k", .plainScalar "v")])
#guard dumpRoundTrips (.mapping .flow #[
  (.plainScalar "k1", .plainScalar "v1"),
  (.plainScalar "k2", .plainScalar "v2")])

-- ═══════════════════════════════════════════════════════════════════
-- §4f: Block sequence round-trips
-- ═══════════════════════════════════════════════════════════════════

#guard dumpRoundTrips (.sequence .block #[.plainScalar "a"])
#guard dumpRoundTrips (.sequence .block #[.plainScalar "a", .plainScalar "b"])
#guard dumpRoundTrips (.sequence .block #[
  .plainScalar "x", .plainScalar "y", .plainScalar "z"])

-- ═══════════════════════════════════════════════════════════════════
-- §4g: Block mapping round-trips
-- ═══════════════════════════════════════════════════════════════════

#guard dumpRoundTrips (.mapping .block #[
  (.plainScalar "key", .plainScalar "val")])
#guard dumpRoundTrips (.mapping .block #[
  (.plainScalar "a", .plainScalar "1"),
  (.plainScalar "b", .plainScalar "2")])

-- ═══════════════════════════════════════════════════════════════════
-- §4h: Nested structure round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Mapping with sequence value
#guard dumpRoundTrips (.mapping .block #[
  (.plainScalar "items", .sequence .block #[
    .plainScalar "a", .plainScalar "b"])])

-- Mapping with nested mapping value
#guard dumpRoundTrips (.mapping .block #[
  (.plainScalar "outer", .mapping .block #[
    (.plainScalar "inner", .plainScalar "val")])])

-- Mapping with flow sequence value (mixed block/flow)
#guard dumpRoundTrips (.mapping .block #[
  (.plainScalar "list", .sequence .flow #[.plainScalar "a", .plainScalar "b"])])

-- Flow collection with nested flow
#guard dumpRoundTrips (.sequence .flow #[
  .sequence .flow #[.plainScalar "a"] ,
  .mapping .flow #[(.plainScalar "k", .plainScalar "v")]])

-- ═══════════════════════════════════════════════════════════════════
-- §4i: Escape round-trips through dump
-- ═══════════════════════════════════════════════════════════════════

-- Control characters that get escaped in double-quoted context
#guard dumpRoundTrips (.plainScalar "tab\there")
#guard dumpRoundTrips (.plainScalar "back\\slash")
#guard dumpRoundTrips (.plainScalar "say \"hi\"")

-- ═══════════════════════════════════════════════════════════════════
-- §4j: Config overrides round-trip
-- ═══════════════════════════════════════════════════════════════════

-- Flow config on block values
#guard dumpRoundTrips (.sequence .block #[.plainScalar "a"]) { defaultStyle := .flow }
#guard dumpRoundTrips (.mapping .block #[(.plainScalar "k", .plainScalar "v")])
  { defaultStyle := .flow }

-- Custom indent (does not affect content)
#guard dumpRoundTrips (.mapping .block #[
  (.plainScalar "key", .sequence .block #[.plainScalar "a"])]) { indent := 4 }

end L4YAML.Proofs.DumpRoundTrip
