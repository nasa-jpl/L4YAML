import L4YAML.Proofs.ScannerEmitBridge

namespace L4YAML.Proofs.ScannerEmitBridge

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.TokenParser

private def stripEqRoundTrips (n : ValidNode) : Bool :=
  let v := toYamlValue n
  match parseYamlRaw (emit v) with
  | .ok docs =>
    match docs.toList with
    | d :: _ => stripAnnotations d.value == stripAnnotations v
    | [] => false
  | .error _ => false
private def emitParseSucceeds (n : ValidNode) : Bool :=
  let v := toYamlValue n
  match parseYamlRaw (emit v) with
  | .ok docs => docs.size == 1
  | .error _ => false

-- ═══════════════════════════════════════════════════════════════════
-- §4a: Double-quoted scalar canonical roundtrips
-- ═══════════════════════════════════════════════════════════════════

-- Empty DQ scalar
#guard canonicalRoundTrips (.doubleQuoted "")
#guard emitParseSucceeds (.doubleQuoted "")

-- Simple ASCII
#guard canonicalRoundTrips (.doubleQuoted "hello")
#guard canonicalRoundTrips (.doubleQuoted "world")
#guard canonicalRoundTrips (.doubleQuoted "a")

-- Spaces and punctuation
#guard canonicalRoundTrips (.doubleQuoted "hello world")
#guard canonicalRoundTrips (.doubleQuoted "foo-bar_baz")
#guard canonicalRoundTrips (.doubleQuoted "123")

-- Special characters requiring escaping
#guard canonicalRoundTrips (.doubleQuoted "line1\nline2")
#guard canonicalRoundTrips (.doubleQuoted "tab\there")
#guard canonicalRoundTrips (.doubleQuoted "back\\slash")
#guard canonicalRoundTrips (.doubleQuoted "say \"hi\"")

-- Unicode
#guard canonicalRoundTrips (.doubleQuoted "α")
#guard canonicalRoundTrips (.doubleQuoted "日本語")
#guard canonicalRoundTrips (.doubleQuoted "🎉")

-- YAML-significant characters (safe in DQ)
#guard canonicalRoundTrips (.doubleQuoted "key: value")
#guard canonicalRoundTrips (.doubleQuoted "- item")
#guard canonicalRoundTrips (.doubleQuoted "# comment")
#guard canonicalRoundTrips (.doubleQuoted "[a, b]")
#guard canonicalRoundTrips (.doubleQuoted "{k: v}")

-- stripAnnotations equality holds for DQ scalars
#guard stripEqRoundTrips (.doubleQuoted "hello")
#guard stripEqRoundTrips (.doubleQuoted "")
#guard stripEqRoundTrips (.doubleQuoted "line\nbreak")

-- ═══════════════════════════════════════════════════════════════════
-- §4b: Flow sequence canonical roundtrips
-- ═══════════════════════════════════════════════════════════════════

-- Empty flow sequence
#guard canonicalRoundTrips (.flowSeq [])
#guard stripEqRoundTrips (.flowSeq [])

-- Single element
#guard canonicalRoundTrips (.flowSeq [.doubleQuoted "a"])
#guard stripEqRoundTrips (.flowSeq [.doubleQuoted "a"])

-- Multiple elements
#guard canonicalRoundTrips (.flowSeq [.doubleQuoted "a", .doubleQuoted "b", .doubleQuoted "c"])
#guard stripEqRoundTrips (.flowSeq [.doubleQuoted "a", .doubleQuoted "b"])

-- ═══════════════════════════════════════════════════════════════════
-- §4c: Flow mapping canonical roundtrips
-- ═══════════════════════════════════════════════════════════════════

-- Empty flow mapping
#guard canonicalRoundTrips (.flowMap [])
#guard stripEqRoundTrips (.flowMap [])

-- Single entry
#guard canonicalRoundTrips (.flowMap [(.doubleQuoted "key", .doubleQuoted "value")])
#guard stripEqRoundTrips (.flowMap [(.doubleQuoted "key", .doubleQuoted "value")])

-- Multiple entries
#guard canonicalRoundTrips (.flowMap [
  (.doubleQuoted "name", .doubleQuoted "Alice"),
  (.doubleQuoted "age", .doubleQuoted "30")])
#guard stripEqRoundTrips (.flowMap [
  (.doubleQuoted "name", .doubleQuoted "Alice"),
  (.doubleQuoted "age", .doubleQuoted "30")])

-- ═══════════════════════════════════════════════════════════════════
-- §4d: Nested structure canonical roundtrips
-- ═══════════════════════════════════════════════════════════════════

-- Sequence of sequences
#guard canonicalRoundTrips (.flowSeq [
  .flowSeq [.doubleQuoted "a"],
  .flowSeq [.doubleQuoted "b"]])
#guard stripEqRoundTrips (.flowSeq [
  .flowSeq [.doubleQuoted "a"],
  .flowSeq [.doubleQuoted "b"]])

-- Mapping with sequence value
#guard canonicalRoundTrips (.flowMap [
  (.doubleQuoted "items", .flowSeq [.doubleQuoted "x", .doubleQuoted "y"])])
#guard stripEqRoundTrips (.flowMap [
  (.doubleQuoted "items", .flowSeq [.doubleQuoted "x", .doubleQuoted "y"])])

-- Mapping with mapping value
#guard canonicalRoundTrips (.flowMap [
  (.doubleQuoted "outer",
   .flowMap [(.doubleQuoted "inner", .doubleQuoted "val")])])

-- Sequence containing a mapping
#guard canonicalRoundTrips (.flowSeq [
  .flowMap [(.doubleQuoted "k", .doubleQuoted "v")]])

-- Three levels deep
#guard canonicalRoundTrips (.flowMap [
  (.doubleQuoted "a",
   .flowMap [(.doubleQuoted "b",
     .flowSeq [.doubleQuoted "c"])])])
#guard stripEqRoundTrips (.flowMap [
  (.doubleQuoted "a",
   .flowMap [(.doubleQuoted "b",
     .flowSeq [.doubleQuoted "c"])])])

-- Four levels deep
#guard canonicalRoundTrips (.flowSeq [
  .flowMap [(.doubleQuoted "a",
    .flowSeq [.flowMap [
      (.doubleQuoted "deep", .doubleQuoted "value")]])]])

-- ═══════════════════════════════════════════════════════════════════
-- §4e: Edge cases
-- ═══════════════════════════════════════════════════════════════════

-- Null byte
#guard canonicalRoundTrips (.doubleQuoted "\x00")

-- All named escape characters
#guard canonicalRoundTrips (.doubleQuoted "\x00\x07\x08\t\n\x0b\x0c\r\x1b")

-- Document markers (safe in DQ)
#guard canonicalRoundTrips (.doubleQuoted "---")
#guard canonicalRoundTrips (.doubleQuoted "...")

-- Wide collection (8 elements)
#guard canonicalRoundTrips (.flowSeq [
  .doubleQuoted "1", .doubleQuoted "2", .doubleQuoted "3", .doubleQuoted "4",
  .doubleQuoted "5", .doubleQuoted "6", .doubleQuoted "7", .doubleQuoted "8"])

-- Wide mapping (4 entries)
#guard canonicalRoundTrips (.flowMap [
  (.doubleQuoted "k1", .doubleQuoted "v1"),
  (.doubleQuoted "k2", .doubleQuoted "v2"),
  (.doubleQuoted "k3", .doubleQuoted "v3"),
  (.doubleQuoted "k4", .doubleQuoted "v4")])
-- Single-quoted scalars (content preserved, style changes DQ)
#guard canonicalRoundTrips (.singleQuoted "hello")
#guard canonicalRoundTrips (.singleQuoted "")
#guard canonicalRoundTrips (.singleQuoted "with spaces")

-- Block sequences (content preserved, converted to flow)
#guard canonicalRoundTrips (.blockSeq 2 [.doubleQuoted "a", .doubleQuoted "b"])

-- Block mappings (content preserved, converted to flow)
#guard canonicalRoundTrips (.blockMap 2 [
  (.doubleQuoted "key", .doubleQuoted "value")])

-- Mixed: block collection with DQ scalars
#guard canonicalRoundTrips (.blockSeq 2 [
  .flowMap [(.doubleQuoted "k", .doubleQuoted "v")]])

-- Flow/block mixing in nested structures
#guard canonicalRoundTrips (.flowMap [
  (.doubleQuoted "seq", .flowSeq [.doubleQuoted "a", .doubleQuoted "b"]),
  (.doubleQuoted "map", .flowMap [(.doubleQuoted "x", .doubleQuoted "y")]),
  (.doubleQuoted "scalar", .doubleQuoted "plain")])

-- ═══════════════════════════════════════════════════════════════════
-- §5b: Emit-stripAnnotations interaction (#guard)
-- ═══════════════════════════════════════════════════════════════════

-- Verify emit_stripAnnotations computationally for tagged values
#guard emit (stripAnnotations (.scalar ⟨"hello", .plain, some "!str", some "a1", none⟩))
    == emit (.scalar ⟨"hello", .plain, some "!str", some "a1", none⟩)

#guard emit (stripAnnotations (.scalar ⟨"hello", .doubleQuoted, some "tag", some "anchor",
    some ⟨.strip, some 4⟩⟩)) == emit (.scalar ⟨"hello", .doubleQuoted, some "tag", some "anchor",
    some ⟨.strip, some 4⟩⟩)

-- Annotated sequence
#guard emit (stripAnnotations (.sequence .flow
    #[.scalar ⟨"a", .plain, none, none, none⟩] (some "!seq") (some "anch")))
  == emit (.sequence .flow
    #[.scalar ⟨"a", .plain, none, none, none⟩] (some "!seq") (some "anch"))

-- Annotated mapping
#guard emit (stripAnnotations (.mapping .flow
    #[(.scalar ⟨"k", .plain, none, none, none⟩,
       .scalar ⟨"v", .plain, none, none, none⟩)] (some "!map") (some "m1")))
  == emit (.mapping .flow
    #[(.scalar ⟨"k", .plain, none, none, none⟩,
       .scalar ⟨"v", .plain, none, none, none⟩)] (some "!map") (some "m1"))

-- ═══════════════════════════════════════════════════════════════════
-- §5c: contentEq_implies_emit_eq (#guard)
-- ═══════════════════════════════════════════════════════════════════

-- Same content, different styles → same emit output
#guard emit (.scalar ⟨"hello", .plain, none, none, none⟩)
    == emit (.scalar ⟨"hello", .doubleQuoted, none, none, none⟩)

#guard emit (.scalar ⟨"hello", .singleQuoted, some "!str", none, none⟩)
    == emit (.scalar ⟨"hello", .literal, none, some "a1", some ⟨.strip, some 2⟩⟩)

-- Different collection styles → same emit output
#guard emit (.sequence .block #[.scalar ⟨"x", .plain, none, none, none⟩] none)
    == emit (.sequence .flow #[.scalar ⟨"x", .doubleQuoted, some "!str", none, none⟩] (some "!seq"))

end L4YAML.Proofs.ScannerEmitBridge
