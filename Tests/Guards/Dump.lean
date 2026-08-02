import L4YAML.Output.Dump

namespace L4YAML.Dump

open Lean L4YAML
open L4YAML L4YAML.Dump

#guard dump (.plainScalar "hello") == "hello"
#guard dump (.plainScalar "simple") == "simple"
#guard dump (.plainScalar "two words") == "two words"
#guard dump (.plainScalar "true") == "\"true\""
#guard dump (.plainScalar "false") == "\"false\""
#guard dump (.plainScalar "null") == "\"null\""
#guard dump (.plainScalar "yes") == "\"yes\""
#guard dump (.plainScalar "~") == "\"~\""
#guard dump (.plainScalar "") == "\"\""
#guard dump (.plainScalar "key: value") == "\"key: value\""
#guard dump (.plainScalar "has #comment") == "\"has #comment\""
-- ns-char tightening (2026-08): non-printables and BOM are not plain-safe;
-- non-printables are hex-escaped in double-quoted output (raw controls
-- violate nb-json [2]), while BOM is nb-json-valid and stays raw.
#guard !(isPlainSafe ("a" ++ String.singleton (Char.ofNat 0x01) ++ "b"))
#guard !(isPlainSafe ("a" ++ String.singleton (Char.ofNat 0xFEFF) ++ "b"))
#guard dump (.plainScalar ("a" ++ String.singleton (Char.ofNat 0x01) ++ "b"))
  == "\"a\\x01b\""
-- nb-char [27]: multiline content with controls/BOM cannot be carried in a
-- literal block scalar; falls back to double-quoted with escapes.
#guard dump (.plainScalar ("a\nb" ++ String.singleton (Char.ofNat 0x01)))
  == "\"a\\nb\\x01\""
#guard dump (.plainScalar "a\nb") == "|\n  a\n  b"
-- explicit single-quoted config with non-printables falls back to double-quoted
#guard dump (.plainScalar ("a" ++ String.singleton (Char.ofNat 0x01)))
    { scalarStyle := .singleQuoted } == "\"a\\x01\""
#guard dump (.plainScalar ("a" ++ String.singleton (Char.ofNat 0xFEFF) ++ "b"))
  == "\"a" ++ String.singleton (Char.ofNat 0xFEFF) ++ "b\""
#guard dump (.plainScalar "{flow}") == "\"{flow}\""
#guard dump (.plainScalar "[array]") == "\"[array]\""
#guard dump (.plainScalar "true") { allowReservedPlain := true } == "true"
#guard dump (.plainScalar "false") { allowReservedPlain := true } == "false"
#guard dump (.plainScalar "null") { allowReservedPlain := true } == "null"
#guard dump (.plainScalar "yes") { allowReservedPlain := true } == "yes"
#guard dump (.plainScalar "~") { allowReservedPlain := true } == "~"
-- Non-reserved special chars are still quoted even with allowReservedPlain
#guard dump (.plainScalar "key: value") { allowReservedPlain := true } == "\"key: value\""
#guard dump (.plainScalar "{flow}") { allowReservedPlain := true } == "\"{flow}\""
#guard dump (.quotedScalar "hello" .doubleQuoted) == "hello"
#guard dump (.quotedScalar "line\nnewline" .doubleQuoted) == "|\n  line\n  newline"
#guard dump (.plainScalar "hello") { scalarStyle := .singleQuoted } == "'hello'"
#guard dump (.plainScalar "it's") { scalarStyle := .singleQuoted } == "'it''s'"
#guard dump (.scalar ⟨"line1\nline2", .literal, none, none, none⟩) ==
  "|\n  line1\n  line2"

#guard dump (.scalar ⟨"line1\nline2", .literal, none, none,
  some ⟨.strip, none⟩⟩) == "|-\n  line1\n  line2"

#guard dump (.scalar ⟨"line1\nline2", .literal, none, none,
  some ⟨.keep, none⟩⟩) == "|+\n  line1\n  line2"
#guard dump (.scalar ⟨"line1\nline2", .folded, none, none, none⟩) ==
  ">\n  line1\n  line2"
#guard dump (.plainScalar "multi\nline") == "|\n  multi\n  line"
#guard dump (.alias "anchor1") == "*anchor1"
#guard dump (.scalar ⟨"value", .plain, none, some "a1", none⟩) == "&a1 value"
#guard dump (.scalar ⟨"42", .plain, some "!!int", none, none⟩) == "!!int 42"
#guard dump (.sequence .flow #[.plainScalar "a", .plainScalar "b"]) == "[a, b]"
#guard dump (.mapping .flow #[(.plainScalar "k", .plainScalar "v")]) == "{k: v}"
#guard dump (.sequence .flow #[]) == "[]"
#guard dump (.mapping .flow #[]) == "{}"
#guard dump (.sequence .block #[.plainScalar "a", .plainScalar "b"]) ==
  "- a\n- b"

#guard dump (.sequence .block #[.plainScalar "x"]) == "- x"
#guard dump (.mapping .block #[
    (.plainScalar "key1", .plainScalar "val1"),
    (.plainScalar "key2", .plainScalar "val2")
  ]) == "key1: val1\nkey2: val2"
#guard dump (.mapping .block #[
    (.plainScalar "items", .sequence .block #[
      .plainScalar "a", .plainScalar "b"
    ])
  ]) == "items:\n  - a\n  - b"
#guard dump (.mapping .block #[
    (.plainScalar "outer", .mapping .block #[
      (.plainScalar "inner", .plainScalar "val")
    ])
  ]) == "outer:\n  inner: val"
#guard dump (.sequence .block #[.plainScalar "a"]) { defaultStyle := .flow } ==
  "[a]"

#guard dump (.mapping .block #[(.plainScalar "k", .plainScalar "v")])
  { defaultStyle := .flow } == "{k: v}"
#guard dump (.sequence .block #[]) == "[]"
#guard dump (.mapping .block #[]) == "{}"
-- Mapping with mix of empty and non-empty values
#guard dump (.mapping .block #[
    (.plainScalar "name", .plainScalar "test"),
    (.plainScalar "items", .sequence .block #[]),
    (.plainScalar "meta", .mapping .block #[])
  ]) { omitEmpty := true } == "name: test"

-- All fields empty → renders as empty mapping
#guard dump (.mapping .block #[
    (.plainScalar "items", .sequence .block #[]),
    (.plainScalar "meta", .mapping .block #[])
  ]) { omitEmpty := true } == "{}"

-- Without omitEmpty, empty fields are preserved
#guard dump (.mapping .block #[
    (.plainScalar "name", .plainScalar "test"),
    (.plainScalar "items", .sequence .block #[])
  ]) == "name: test\nitems:\n  []"

-- Non-empty collections are preserved with omitEmpty
#guard dump (.mapping .block #[
    (.plainScalar "a", .plainScalar "v1"),
    (.plainScalar "b", .sequence .block #[.plainScalar "x"]),
    (.plainScalar "c", .sequence .block #[])
  ]) { omitEmpty := true } == "a: v1\nb:\n  - x"
#guard dump (.mapping .block #[
    (.plainScalar "list", .sequence .flow #[.plainScalar "a", .plainScalar "b"])
  ]) == "list: [a, b]"
#guard dump (.plainScalar "hello") { scalarStyle := .doubleQuoted } ==
  "\"hello\""
#guard dump (.mapping .block #[
    (.plainScalar "key", .sequence .block #[.plainScalar "a"])
  ]) { indent := 4 } == "key:\n    - a"
private def doc1 : YamlDocument := { value := .plainScalar "hello" }
private def doc2 : YamlDocument :=
  { value := .plainScalar "hello", directives := #[.yaml "1.2"] }
private def doc3 : YamlDocument :=
  { value := .mapping .block #[(.plainScalar "k", .plainScalar "v")],
    directives := #[.yaml "1.2"] }
private def doc4 : YamlDocument :=
  { value := .plainScalar "val",
    directives := #[.yaml "1.2", .tag "!e!" "tag:example.com,2000:"] }
private def docA : YamlDocument := { value := .plainScalar "a" }
private def docB : YamlDocument := { value := .plainScalar "b" }
private def docC : YamlDocument := { value := .plainScalar "c" }
private def docOnly : YamlDocument := { value := .plainScalar "only" }
private def docMap : YamlDocument :=
  { value := .mapping .block #[(.plainScalar "x", .plainScalar "1")] }
private def docSeq : YamlDocument :=
  { value := .sequence .block #[.plainScalar "y"] }
private def docADir : YamlDocument :=
  { value := .plainScalar "a", directives := #[.yaml "1.2"] }

#guard dumpDocument doc1 == "hello"
#guard dumpDocument doc2 == "%YAML 1.2\n---\nhello"
#guard dumpDocument doc3 == "%YAML 1.2\n---\nk: v"
#guard dumpDocument doc4 ==
  "%YAML 1.2\n%TAG !e! tag:example.com,2000:\n---\nval"
#guard dumpDocuments #[] == ""
#guard dumpDocuments #[docOnly] == "only"
#guard dumpDocuments #[docA, docB] == "a\n---\nb\n..."
#guard dumpDocuments #[docA, docB, docC] == "a\n---\nb\n---\nc\n..."
#guard dumpDocuments #[docMap, docSeq] == "x: 1\n---\n- y\n..."
#guard dumpDocuments #[docADir, docB] ==
  "%YAML 1.2\n---\na\n---\nb\n..."
#guard dumpDirective (.yaml "1.2") == "%YAML 1.2"
#guard dumpDirective (.tag "!!" "tag:yaml.org,2002:") ==
  "%TAG !! tag:yaml.org,2002:"
-- Single mapping in sequence: compact
#guard dump (.sequence .block #[
    .mapping .block #[(.plainScalar "name", .plainScalar "first")]
  ]) { compactSequenceMap := true } == "- name: first"

-- Without compactSequenceMap: newline after dash
#guard dump (.sequence .block #[
    .mapping .block #[(.plainScalar "name", .plainScalar "first")]
  ]) == "-\n  name: first"

-- Two mappings in sequence: compact
#guard dump (.sequence .block #[
    .mapping .block #[(.plainScalar "name", .plainScalar "a")],
    .mapping .block #[(.plainScalar "name", .plainScalar "b")]
  ]) { compactSequenceMap := true } == "- name: a\n- name: b"

-- Multi-key mapping: first key shares `-`, second key aligns
#guard dump (.sequence .block #[
    .mapping .block #[
      (.plainScalar "name", .plainScalar "mobility"),
      (.plainScalar "groups", .sequence .block #[.plainScalar "x", .plainScalar "y"])
    ]
  ]) { compactSequenceMap := true } ==
  "- name: mobility\n  groups:\n    - x\n    - y"

-- Empty mapping still renders as `- {}`
#guard dump (.sequence .block #[
    .mapping .block #[]
  ]) { compactSequenceMap := true } == "- {}"

-- Nested: mapping key whose value is a compact sequence
#guard dump (.mapping .block #[
    (.plainScalar "stacks", .sequence .block #[
      .mapping .block #[
        (.plainScalar "name", .plainScalar "mobility"),
        (.plainScalar "groups", .sequence .block #[.plainScalar "a"])
      ]
    ])
  ]) { compactSequenceMap := true } ==
  "stacks:\n  - name: mobility\n    groups:\n      - a"

-- Scalar items in sequence are unaffected by compactSequenceMap
#guard dump (.sequence .block #[.plainScalar "a", .plainScalar "b"])
  { compactSequenceMap := true } == "- a\n- b"

/-! ### scalarStyle preserve: honor node style, keep core-schema type

The type-fidelity config used by the Python binding's `safe_dump`
(`{ scalarStyle := .preserve, allowReservedPlain := true }`): each
scalar re-emits in its own style, so quoting — and therefore the type
a core-schema consumer resolves — survives a load→dump round trip. -/

-- Plain stays plain, including leading '-' (ns-plain-first
-- refinement `isPlainSafePreserve`; plain `-1` must not re-quote
-- into a string) and reserved words under allowReservedPlain.
#guard dump (.plainScalar "-1")
  { scalarStyle := .preserve, allowReservedPlain := true } == "-1"
#guard dump (.plainScalar "-3.14")
  { scalarStyle := .preserve, allowReservedPlain := true } == "-3.14"
#guard dump (.plainScalar "-.inf")
  { scalarStyle := .preserve, allowReservedPlain := true } == "-.inf"
#guard dump (.plainScalar "true")
  { scalarStyle := .preserve, allowReservedPlain := true } == "true"
#guard dump (.plainScalar "42") { scalarStyle := .preserve } == "42"
-- Without allowReservedPlain, reserved words still quote.
#guard dump (.plainScalar "true") { scalarStyle := .preserve } == "\"true\""
-- Plain content that is not plain-safe still quotes ('- x' is a
-- sequence-entry lookalike; empty needs quotes).
#guard dump (.plainScalar "- x") { scalarStyle := .preserve } == "\"- x\""
#guard dump (.plainScalar "key: value")
  { scalarStyle := .preserve } == "\"key: value\""
#guard dump (.plainScalar "") { scalarStyle := .preserve } == "\"\""
-- Quoted stays quoted: '42' must not re-emit plain (type would flip
-- string→int under core-schema resolution).
#guard dump (.quotedScalar "42" .singleQuoted)
  { scalarStyle := .preserve } == "'42'"
#guard dump (.quotedScalar "true" .singleQuoted)
  { scalarStyle := .preserve, allowReservedPlain := true } == "'true'"
#guard dump (.quotedScalar "42" .doubleQuoted)
  { scalarStyle := .preserve } == "\"42\""
-- Block styles not honored by the newline case quote to stay strings
-- (`>- 42` must not become plain 42).
#guard dump (.scalar ⟨"42", .folded, none, none, none⟩)
  { scalarStyle := .preserve, allowReservedPlain := true } == "\"42\""
#guard dump (.scalar ⟨"true", .literal, none, none, none⟩)
  { scalarStyle := .preserve, allowReservedPlain := true } == "\"true\""
-- Single-quoted content that single quotes cannot carry verbatim
-- (CR/C0 controls, newlines) falls back to escaped double quotes.
#guard dump (.scalar ⟨"a\rb", .singleQuoted, none, none, none⟩)
  { scalarStyle := .preserve } == "\"a\\rb\""
#guard dump (.scalar ⟨"line1\nline2", .singleQuoted, none, none, none⟩)
  { scalarStyle := .preserve } == "\"line1\\nline2\""

end L4YAML.Dump
