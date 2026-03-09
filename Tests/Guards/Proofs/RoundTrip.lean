import Lean4Yaml.Proofs.RoundTrip

namespace Lean4Yaml.Proofs.RoundTrip

open Lean4Yaml
open Lean4Yaml.Emit
open Lean4Yaml.Grammar
open Lean4Yaml.TokenParser

private def roundTrips (v : YamlValue) : Bool :=
  match parseYamlSingle (emit v) with
  | .ok v' => contentEq v v'
  | .error _ => false

-- ═══════════════════════════════════════════════════════════════════
-- §4a: Scalar round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Simple ASCII words
#guard roundTrips (.scalar ⟨"hello", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"hello", .doubleQuoted, none, none, none⟩)
#guard roundTrips (.scalar ⟨"hello", .singleQuoted, none, none, none⟩)
#guard roundTrips (.scalar ⟨"world", .plain, none, none, none⟩)

-- Empty scalar
#guard roundTrips (.scalar ⟨"", .plain, none, none, none⟩)

-- Single character
#guard roundTrips (.scalar ⟨"x", .plain, none, none, none⟩)

-- Spaces and punctuation
#guard roundTrips (.scalar ⟨"hello world", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"a b c", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"foo-bar_baz", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"123", .plain, none, none, none⟩)

-- Special characters requiring escaping
#guard roundTrips (.scalar ⟨"line1\nline2", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"tab\there", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"back\\slash", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"say \"hi\"", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"cr\rhere", .plain, none, none, none⟩)

-- Multiple special characters
#guard roundTrips (.scalar ⟨"a\nb\nc", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"\"\\\"", .plain, none, none, none⟩)

-- Unicode
#guard roundTrips (.scalar ⟨"α", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"日本語", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"emoji: 🎉", .plain, none, none, none⟩)

-- YAML special characters (safe inside double quotes)
#guard roundTrips (.scalar ⟨"key: value", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"- item", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"# not a comment", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"[a, b]", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"{k: v}", .plain, none, none, none⟩)

-- ═══════════════════════════════════════════════════════════════════
-- §4b: Flow sequence round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Empty sequence
#guard roundTrips (.sequence .flow #[] none)

-- Single element
#guard roundTrips (.sequence .flow #[.scalar ⟨"a", .plain, none, none, none⟩] none)

-- Multiple elements
#guard roundTrips (.sequence .flow #[
  .scalar ⟨"a", .plain, none, none, none⟩,
  .scalar ⟨"b", .plain, none, none, none⟩,
  .scalar ⟨"c", .plain, none, none, none⟩
] none)

-- Elements with special characters
#guard roundTrips (.sequence .flow #[
  .scalar ⟨"hello world", .plain, none, none, none⟩,
  .scalar ⟨"line\nbreak", .plain, none, none, none⟩
] none)

-- Block-style sequence (emitter converts to flow, content preserved)
#guard roundTrips (.sequence .block #[
  .scalar ⟨"x", .plain, none, none, none⟩,
  .scalar ⟨"y", .plain, none, none, none⟩
] none)

-- ═══════════════════════════════════════════════════════════════════
-- §4c: Flow mapping round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Empty mapping
#guard roundTrips (.mapping .flow #[] none)

-- Single entry
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"key", .plain, none, none, none⟩, .scalar ⟨"value", .plain, none, none, none⟩)
] none)

-- Multiple entries
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"name", .plain, none, none, none⟩, .scalar ⟨"Alice", .plain, none, none, none⟩),
  (.scalar ⟨"age", .plain, none, none, none⟩, .scalar ⟨"30", .plain, none, none, none⟩)
] none)

-- Block-style mapping (emitter converts to flow, content preserved)
#guard roundTrips (.mapping .block #[
  (.scalar ⟨"a", .plain, none, none, none⟩, .scalar ⟨"1", .plain, none, none, none⟩)
] none)

-- ═══════════════════════════════════════════════════════════════════
-- §4d: Nested structure round-trips
-- ═══════════════════════════════════════════════════════════════════

-- Sequence of sequences
#guard roundTrips (.sequence .flow #[
  .sequence .flow #[.scalar ⟨"a", .plain, none, none, none⟩] none,
  .sequence .flow #[.scalar ⟨"b", .plain, none, none, none⟩] none
] none)

-- Mapping with sequence value
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"items", .plain, none, none, none⟩,
   .sequence .flow #[.scalar ⟨"x", .plain, none, none, none⟩,
                     .scalar ⟨"y", .plain, none, none, none⟩] none)
] none)

-- Mapping with mapping value
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"outer", .plain, none, none, none⟩,
   .mapping .flow #[
     (.scalar ⟨"inner", .plain, none, none, none⟩, .scalar ⟨"val", .plain, none, none, none⟩)
   ] none)
] none)

-- Sequence containing a mapping
#guard roundTrips (.sequence .flow #[
  .mapping .flow #[
    (.scalar ⟨"k", .plain, none, none, none⟩, .scalar ⟨"v", .plain, none, none, none⟩)
  ] none
] none)

-- Three levels deep
#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"a", .plain, none, none, none⟩,
   .mapping .flow #[
     (.scalar ⟨"b", .plain, none, none, none⟩,
      .sequence .flow #[.scalar ⟨"c", .plain, none, none, none⟩] none)
   ] none)
] none)

-- ═══════════════════════════════════════════════════════════════════
-- §4e: Edge cases
-- ═══════════════════════════════════════════════════════════════════

-- Scalar containing YAML document markers (safe inside double quotes)
#guard roundTrips (.scalar ⟨"---", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"...", .plain, none, none, none⟩)

-- Scalar containing colons and dashes
#guard roundTrips (.scalar ⟨"a: b: c", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"- - -", .plain, none, none, none⟩)

-- Scalar containing brackets and braces
#guard roundTrips (.scalar ⟨"[1, 2, 3]", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"{key: val}", .plain, none, none, none⟩)

-- Scalar with null byte
#guard roundTrips (.scalar ⟨"\x00", .plain, none, none, none⟩)

-- Scalar with all named-escape characters
#guard roundTrips (.scalar ⟨"\x00\x07\x08\t\n\x0b\x0c\r\x1b", .plain, none, none, none⟩)
-- ═══════════════════════════════════════════════════════════════════
-- §9a: Deep nesting (4 levels)
-- ═══════════════════════════════════════════════════════════════════

#guard roundTrips (.sequence .flow #[
  .mapping .flow #[
    (.scalar ⟨"a", .plain, none, none, none⟩,
     .sequence .flow #[
       .mapping .flow #[
         (.scalar ⟨"deep", .plain, none, none, none⟩,
          .scalar ⟨"value", .plain, none, none, none⟩)] none] none)] none] none)

-- ═══════════════════════════════════════════════════════════════════
-- §9b: Wide collections (8+ elements)
-- ═══════════════════════════════════════════════════════════════════

#guard roundTrips (.sequence .flow #[
  .scalar ⟨"1", .plain, none, none, none⟩, .scalar ⟨"2", .plain, none, none, none⟩,
  .scalar ⟨"3", .plain, none, none, none⟩, .scalar ⟨"4", .plain, none, none, none⟩,
  .scalar ⟨"5", .plain, none, none, none⟩, .scalar ⟨"6", .plain, none, none, none⟩,
  .scalar ⟨"7", .plain, none, none, none⟩, .scalar ⟨"8", .plain, none, none, none⟩] none)

#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"k1", .plain, none, none, none⟩, .scalar ⟨"v1", .plain, none, none, none⟩),
  (.scalar ⟨"k2", .plain, none, none, none⟩, .scalar ⟨"v2", .plain, none, none, none⟩),
  (.scalar ⟨"k3", .plain, none, none, none⟩, .scalar ⟨"v3", .plain, none, none, none⟩),
  (.scalar ⟨"k4", .plain, none, none, none⟩, .scalar ⟨"v4", .plain, none, none, none⟩)] none)

-- ═══════════════════════════════════════════════════════════════════
-- §9c: Mixed nesting patterns
-- ═══════════════════════════════════════════════════════════════════

#guard roundTrips (.mapping .flow #[
  (.scalar ⟨"seq", .plain, none, none, none⟩,
   .sequence .flow #[.scalar ⟨"a", .plain, none, none, none⟩, .scalar ⟨"b", .plain, none, none, none⟩] none),
  (.scalar ⟨"map", .plain, none, none, none⟩,
   .mapping .flow #[(.scalar ⟨"x", .plain, none, none, none⟩, .scalar ⟨"y", .plain, none, none, none⟩)] none),
  (.scalar ⟨"scalar", .plain, none, none, none⟩,
   .scalar ⟨"plain", .plain, none, none, none⟩)] none)

-- ═══════════════════════════════════════════════════════════════════
-- §9d: Unicode scalars
-- ═══════════════════════════════════════════════════════════════════

#guard roundTrips (.scalar ⟨"こんにちは世界", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"α β γ δ ε", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"🎉🎊🎈", .plain, none, none, none⟩)

-- ═══════════════════════════════════════════════════════════════════
-- §9e: Printable ASCII and whitespace
-- ═══════════════════════════════════════════════════════════════════

#guard roundTrips (.scalar ⟨"!@#$%^&*()_+-=[]{}|;':,./<>?`~", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"  leading", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"trailing  ", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"  both  ", .plain, none, none, none⟩)
#guard roundTrips (.scalar ⟨"multi  spaces", .plain, none, none, none⟩)

end Lean4Yaml.Proofs.RoundTrip
