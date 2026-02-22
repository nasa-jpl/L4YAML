/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Parser.Document

/-!
# yaml-test-suite Compile-Time Guards — Error Stage

Auto-generated from yaml-test-suite test files by `gen-suite-guards.py`.
Each `#guard` is evaluated by Lean's kernel during `lake build`.

**92 guards** covering all passing error tests.

These are Phase 4 of the verification plan: yaml-test-suite as compile-time proofs.
-/

namespace Lean4Yaml.Proofs.SuiteGuards.Error

open Lean4Yaml.Parse

-- 236B:0 Invalid value after mapping
#guard match parseYaml "foo:\n  bar\ninvalid\n" with
  | .ok _ => false
  | .error _ => true

-- 2CMS:0 Invalid mapping in plain multiline
#guard match parseYaml "this\n is\n  invalid: x\n" with
  | .ok _ => false
  | .error _ => true

-- 2G84:0 Literal modifers
#guard match parseYaml "--- |0\n" with
  | .ok _ => false
  | .error _ => true

-- 2G84:1 
#guard match parseYaml "--- |10\n\n" with
  | .ok _ => false
  | .error _ => true

-- 3HFZ:0 Invalid content after document end marker
#guard match parseYaml "---\nkey: value\n... invalid\n" with
  | .ok _ => false
  | .error _ => true

-- 4EJS:0 Invalid tabs as indendation in a mapping
#guard match parseYaml "---\na:\n\tb:\n\t\tc: value\n" with
  | .ok _ => false
  | .error _ => true

-- 4H7K:0 Flow sequence with invalid extra closing bracket
#guard match parseYaml "---\n[ a, b, c ] ]\n" with
  | .ok _ => false
  | .error _ => true

-- 4HVU:0 Wrong indendation in Sequence
#guard match parseYaml "key:\n   - ok\n   - also ok\n  - wrong\n" with
  | .ok _ => false
  | .error _ => true

-- 4JVG:0 Scalar value with two anchors
#guard match parseYaml "top1: &node1\n  &k1 key1: val1\ntop2: &node2\n  &v2 val2\n" with
  | .ok _ => false
  | .error _ => true

-- 55WF:0 Invalid escape in double quoted string
#guard match parseYaml "---\n\"\\.\"\n" with
  | .ok _ => false
  | .error _ => true

-- 5LLU:0 Block scalar with wrong indented line after spaces only
#guard match parseYaml "block scalar: >\n \n  \n   \n invalid\n" with
  | .ok _ => false
  | .error _ => true

-- 5TRB:0 Invalid document-start marker in doublequoted tring
#guard match parseYaml "---\n\"\n---\n\"\n" with
  | .ok _ => false
  | .error _ => true

-- 5U3A:0 Sequence on same Line as Mapping Key
#guard match parseYaml "key: - a\n     - b\n" with
  | .ok _ => false
  | .error _ => true

-- 62EZ:0 Invalid block mapping key on same line as previous key
#guard match parseYaml "---\nx: { y: z }in: valid\n" with
  | .ok _ => false
  | .error _ => true

-- 6JTT:0 Flow sequence without closing bracket
#guard match parseYaml "---\n[ [ a, b, c ]\n" with
  | .ok _ => false
  | .error _ => true

-- 6S55:0 Invalid scalar at the end of sequence
#guard match parseYaml "key:\n - bar\n - baz\n invalid\n" with
  | .ok _ => false
  | .error _ => true

-- 7LBH:0 Multiline double quoted implicit keys
#guard match parseYaml "\"a\\nb\": 1\n\"c\n d\": 1\n" with
  | .ok _ => false
  | .error _ => true

-- 7MNF:0 Missing colon
#guard match parseYaml "top1:\n  key1: val1\ntop2\n" with
  | .ok _ => false
  | .error _ => true

-- 8XDJ:0 Comment in plain multiline value
#guard match parseYaml "key: word1\n#  xxx\n  word2\n" with
  | .ok _ => false
  | .error _ => true

-- 9C9N:0 Wrong indented flow sequence
#guard match parseYaml "---\nflow: [a,\nb,\nc]\n" with
  | .ok _ => false
  | .error _ => true

-- 9CWY:0 Invalid scalar at the end of mapping
#guard match parseYaml "key:\n - item1\n - item2\ninvalid\n" with
  | .ok _ => false
  | .error _ => true

-- 9HCY:0 Need document footer before directives
#guard match parseYaml "!foo \"bar\"\n%TAG ! tag:example.com,2000:app/\n---\n!foo \"bar\"\n" with
  | .ok _ => false
  | .error _ => true

-- 9JBA:0 Invalid comment after end of flow sequence
#guard match parseYaml "---\n[ a, b, c, ]#invalid\n" with
  | .ok _ => false
  | .error _ => true

-- 9KBC:0 Mapping starting at --- line
#guard match parseYaml "--- key1: value1\n    key2: value2\n" with
  | .ok _ => false
  | .error _ => true

-- 9MAG:0 Flow sequence with invalid comma at the beginning
#guard match parseYaml "---\n[ , a, b, c ]\n" with
  | .ok _ => false
  | .error _ => true

-- 9MMA:0 Directive by itself with no document
#guard match parseYaml "%YAML 1.2\n" with
  | .ok _ => false
  | .error _ => true

-- 9MQT:1 
#guard match parseYaml "--- \"a\n... x\nb\"\n" with
  | .ok _ => false
  | .error _ => true

-- B63P:0 Directive without document
#guard match parseYaml "%YAML 1.2\n...\n" with
  | .ok _ => false
  | .error _ => true

-- BD7L:0 Invalid mapping after sequence
#guard match parseYaml "- item1\n- item2\ninvalid: x\n" with
  | .ok _ => false
  | .error _ => true

-- BF9H:0 Trailing comment in multiline plain scalar
#guard match parseYaml "---\nplain: a\n       b # end of scalar\n       c\n" with
  | .ok _ => false
  | .error _ => true

-- BS4K:0 Comment between plain scalar lines
#guard match parseYaml "word1  # comment\nword2\n" with
  | .ok _ => false
  | .error _ => true

-- C2SP:0 Flow Mapping Key on two lines
#guard match parseYaml "[23\n]: 42\n" with
  | .ok _ => false
  | .error _ => true

-- CML9:0 Missing comma in flow
#guard match parseYaml "key: [ word1\n#  xxx\n  word2 ]\n" with
  | .ok _ => false
  | .error _ => true

-- CTN5:0 Flow sequence with invalid extra comma
#guard match parseYaml "---\n[ a, b, c, , ]\n" with
  | .ok _ => false
  | .error _ => true

-- CVW2:0 Invalid comment after comma
#guard match parseYaml "---\n[ a, b, c,#invalid\n]\n" with
  | .ok _ => false
  | .error _ => true

-- CXX2:0 Mapping with anchor on document start line
#guard match parseYaml "--- &anchor a: b\n" with
  | .ok _ => false
  | .error _ => true

-- D49Q:0 Multiline single quoted implicit keys
#guard match parseYaml "'a\\nb': 1\n'c\n d': 1\n" with
  | .ok _ => false
  | .error _ => true

-- DK4H:0 Implicit key followed by newline
#guard match parseYaml "---\n[ key\n  : value ]\n" with
  | .ok _ => false
  | .error _ => true

-- DK95:1 
#guard match parseYaml "foo: \"bar\n\tbaz\"\n" with
  | .ok _ => false
  | .error _ => true

-- DK95:6 
#guard match parseYaml "foo:\n  a: 1\n  \tb: 2\n" with
  | .ok _ => false
  | .error _ => true

-- DMG6:0 Wrong indendation in Map
#guard match parseYaml "key:\n  ok: 1\n wrong: 2\n" with
  | .ok _ => false
  | .error _ => true

-- EB22:0 Missing document-end marker before directive
#guard match parseYaml "---\nscalar1 # comment\n%YAML 1.2\n---\nscalar2\n" with
  | .ok _ => false
  | .error _ => true

-- EW3V:0 Wrong indendation in mapping
#guard match parseYaml "k1: v1\n k2: v2\n" with
  | .ok _ => false
  | .error _ => true

-- G5U8:0 Plain dashes in flow sequence
#guard match parseYaml "---\n- [-, -]\n" with
  | .ok _ => false
  | .error _ => true

-- G7JE:0 Multiline implicit keys
#guard match parseYaml "a\\nb: 1\nc\n d: 1\n" with
  | .ok _ => false
  | .error _ => true

-- G9HC:0 Invalid anchor in zero indented sequence
#guard match parseYaml "---\nseq:\n&anchor\n- a\n- b\n" with
  | .ok _ => false
  | .error _ => true

-- GDY7:0 Comment that looks like a mapping key
#guard match parseYaml "key: value\nthis is #not a: key\n" with
  | .ok _ => false
  | .error _ => true

-- GT5M:0 Node anchor in sequence
#guard match parseYaml "- item1\n&node\n- item2\n" with
  | .ok _ => false
  | .error _ => true

-- H7J7:0 Node anchor not indented
#guard match parseYaml "key: &x\n!!map\n  a: b\n" with
  | .ok _ => false
  | .error _ => true

-- HRE5:0 Double quoted scalar with escaped single quote
#guard match parseYaml "---\ndouble: \"quoted \\' scalar\"\n" with
  | .ok _ => false
  | .error _ => true

-- HU3P:0 Invalid Mapping in plain scalar
#guard match parseYaml "key:\n  word1 word2\n  no: key\n" with
  | .ok _ => false
  | .error _ => true

-- JKF3:0 Multiline unidented double quoted block key
#guard match parseYaml "- - \"bar\nbar\": x\n" with
  | .ok _ => false
  | .error _ => true

-- JY7Z:0 Trailing content that looks like a mapping
#guard match parseYaml "key1: \"quoted1\"\nkey2: \"quoted2\" no key: nor value\nkey3: \"quoted3\"\n" with
  | .ok _ => false
  | .error _ => true

-- KS4U:0 Invalid item after end of flow sequence
#guard match parseYaml "---\n[\nsequence item\n]\ninvalid item\n" with
  | .ok _ => false
  | .error _ => true

-- LHL4:0 Invalid tag
#guard match parseYaml "---\n!invalid{}tag scalar\n" with
  | .ok _ => false
  | .error _ => true

-- MUS6:0 Directive variants
#guard match parseYaml "%YAML 1.1#...\n---\n" with
  | .ok _ => false
  | .error _ => true

-- MUS6:1 
#guard match parseYaml "%YAML 1.2\n---\n%YAML 1.2\n---\n" with
  | .ok _ => false
  | .error _ => true

-- N4JP:0 Bad indentation in mapping
#guard match parseYaml "map:\n  key1: \"quoted1\"\n key2: \"bad indentation\"\n" with
  | .ok _ => false
  | .error _ => true

-- N782:0 Invalid document markers in flow style
#guard match parseYaml "[\n--- ,\n...\n]\n" with
  | .ok _ => false
  | .error _ => true

-- P2EQ:0 Invalid sequene item on same line as previous item
#guard match parseYaml "---\n- { y: z }- invalid\n" with
  | .ok _ => false
  | .error _ => true

-- Q4CL:0 Trailing content after quoted value
#guard match parseYaml "key1: \"quoted1\"\nkey2: \"quoted2\" trailing content\nkey3: \"quoted3\"\n" with
  | .ok _ => false
  | .error _ => true

-- QB6E:0 Wrong indented multiline quoted scalar
#guard match parseYaml "---\nquoted: \"a\nb\nc\"\n" with
  | .ok _ => false
  | .error _ => true

-- QLJ7:0 Tag shorthand used in documents but only defined in the first
#guard match parseYaml "%TAG !prefix! tag:example.com,2011:\n--- !prefix!A\na: b\n--- !prefix!B\nc: d\n--- !prefix!C\ne: f\n" with
  | .ok _ => false
  | .error _ => true

-- RHX7:0 YAML directive without document end marker
#guard match parseYaml "---\nkey: value\n%YAML 1.2\n---\n" with
  | .ok _ => false
  | .error _ => true

-- RXY3:0 Invalid document-end marker in single quoted string
#guard match parseYaml "---\n'\n...\n'\n" with
  | .ok _ => false
  | .error _ => true

-- S4GJ:0 Invalid text after block scalar indicator
#guard match parseYaml "---\nfolded: > first line\n  second line\n" with
  | .ok _ => false
  | .error _ => true

-- S98Z:0 Block scalar with more spaces than first content line
#guard match parseYaml "empty block scalar: >\n \n  \n   \n # comment\n" with
  | .ok _ => false
  | .error _ => true

-- SF5V:0 Duplicate YAML directive
#guard match parseYaml "%YAML 1.2\n%YAML 1.2\n---\n" with
  | .ok _ => false
  | .error _ => true

-- SR86:0 Anchor plus Alias
#guard match parseYaml "key1: &a value\nkey2: &b *a\n" with
  | .ok _ => false
  | .error _ => true

-- SU5Z:0 Comment without whitespace after doublequoted scalar
#guard match parseYaml "key: \"value\"# invalid comment\n" with
  | .ok _ => false
  | .error _ => true

-- SU74:0 Anchor and alias as mapping key
#guard match parseYaml "key1: &alias value1\n&b *alias : value2\n" with
  | .ok _ => false
  | .error _ => true

-- SY6V:0 Anchor before sequence entry on same line
#guard match parseYaml "&anchor - sequence entry\n" with
  | .ok _ => false
  | .error _ => true

-- T833:0 Flow mapping missing a separating comma
#guard match parseYaml "---\n{\n foo: 1\n bar: 2 }\n" with
  | .ok _ => false
  | .error _ => true

-- TD5N:0 Invalid scalar after sequence
#guard match parseYaml "- item1\n- item2\ninvalid\n" with
  | .ok _ => false
  | .error _ => true

-- U44R:0 Bad indentation in mapping (2)
#guard match parseYaml "map:\n  key1: \"quoted1\"\n   key2: \"bad indentation\"\n" with
  | .ok _ => false
  | .error _ => true

-- U99R:0 Invalid comma in tag
#guard match parseYaml "- !!str, xxx\n" with
  | .ok _ => false
  | .error _ => true

-- VJP3:0 Flow collections over many lines
#guard match parseYaml "k: {\nk\n:\nv\n}\n" with
  | .ok _ => false
  | .error _ => true

-- W9L4:0 Literal block scalar with more spaces in first line
#guard match parseYaml "---\nblock scalar: |\n     \n  more spaces at the beginning\n  are invalid\n" with
  | .ok _ => false
  | .error _ => true

-- X4QW:0 Comment without whitespace after block scalar indicator
#guard match parseYaml "block: ># comment\n  scalar\n" with
  | .ok _ => false
  | .error _ => true

-- Y79Y:0 Tabs in various contexts
#guard match parseYaml "foo: |\n\t\nbar: 1\n" with
  | .ok _ => false
  | .error _ => true

-- Y79Y:3 
#guard match parseYaml "- [\n\tfoo,\n foo\n ]\n" with
  | .ok _ => false
  | .error _ => true

-- Y79Y:4 
#guard match parseYaml "-\t-\n\n" with
  | .ok _ => false
  | .error _ => true

-- Y79Y:5 
#guard match parseYaml "- \t-\n\n" with
  | .ok _ => false
  | .error _ => true

-- Y79Y:6 
#guard match parseYaml "?\t-\n\n" with
  | .ok _ => false
  | .error _ => true

-- Y79Y:7 
#guard match parseYaml "? -\n:\t-\n\n" with
  | .ok _ => false
  | .error _ => true

-- Y79Y:8 
#guard match parseYaml "?\tkey:\n\n" with
  | .ok _ => false
  | .error _ => true

-- Y79Y:9 
#guard match parseYaml "? key:\n:\tkey:\n\n" with
  | .ok _ => false
  | .error _ => true

-- YJV2:0 Dash in flow sequence
#guard match parseYaml "[-]\n" with
  | .ok _ => false
  | .error _ => true

-- ZCZ6:0 Invalid mapping in plain single line value
#guard match parseYaml "a: b: c: d\n" with
  | .ok _ => false
  | .error _ => true

-- ZL4Z:0 Invalid nested mapping
#guard match parseYaml "---\na: 'b': c\n" with
  | .ok _ => false
  | .error _ => true

-- ZVH3:0 Wrong indented sequence item
#guard match parseYaml "- key: value\n - item1\n" with
  | .ok _ => false
  | .error _ => true

-- ZXT5:0 Implicit key followed by newline and adjacent value
#guard match parseYaml "[ \"key\"\n  :value ]\n" with
  | .ok _ => false
  | .error _ => true

end Lean4Yaml.Proofs.SuiteGuards.Error
