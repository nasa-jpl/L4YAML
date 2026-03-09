import Lean4Yaml.Dump

namespace Lean4Yaml.Dump

open Lean Lean4Yaml
open Lean4Yaml Lean4Yaml.Dump

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

end Lean4Yaml.Dump
