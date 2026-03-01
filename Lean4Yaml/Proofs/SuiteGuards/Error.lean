/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.TokenParser

/-!
# yaml-test-suite Compile-Time Guards — Error Stage

Auto-generated from yaml-test-suite test files by `gen-suite-guards.py`.
Each `#guard` is evaluated by Lean's kernel during `lake build`.

**95 guards** covering all passing error tests.

These are Phase 4 of the verification plan: yaml-test-suite as compile-time proofs.
-/

namespace Lean4Yaml.Proofs.SuiteGuards.Error

open Lean4Yaml.TokenParser

-- 236B:0 [UP] Invalid value after mapping
#guard match parseYaml "foo:\n  bar\ninvalid\n" with
  | .ok _ => true
  | .error _ => false

-- 2CMS:0 [UP] Invalid mapping in plain multiline
#guard match parseYaml "this\n is\n  invalid: x\n" with
  | .ok _ => true
  | .error _ => false

-- 2G84:0 Literal modifers
#guard match parseYaml "--- |0\n" with
  | .ok _ => false
  | .error _ => true

-- 2G84:1
#guard match parseYaml "--- |10\n\n" with
  | .ok _ => false
  | .error _ => true

-- 3HFZ:0 [UP] Invalid content after document end marker
#guard match parseYaml "---\nkey: value\n... invalid\n" with
  | .ok _ => true
  | .error _ => false

-- 4EJS:0 Invalid tabs as indendation in a mapping
#guard match parseYaml "---\na:\n\tb:\n\t\tc: value\n" with
  | .ok _ => false
  | .error _ => true

-- 4H7K:0 [UP] Flow sequence with invalid extra closing bracket
#guard match parseYaml "---\n[ a, b, c ] ]\n" with
  | .ok _ => true
  | .error _ => false

-- 4HVU:0 [UP] Wrong indendation in Sequence
#guard match parseYaml "key:\n   - ok\n   - also ok\n  - wrong\n" with
  | .ok _ => true
  | .error _ => false

-- 4JVG:0 [UP] Scalar value with two anchors
#guard match parseYaml "top1: &node1\n  &k1 key1: val1\ntop2: &node2\n  &v2 val2\n" with
  | .ok _ => true
  | .error _ => false

-- 55WF:0 Invalid escape in double quoted string
#guard match parseYaml "---\n\"\\.\"\n" with
  | .ok _ => false
  | .error _ => true

-- 5LLU:0 [UP] Block scalar with wrong indented line after spaces only
#guard match parseYaml "block scalar: >\n \n  \n   \n invalid\n" with
  | .ok _ => true
  | .error _ => false

-- 5TRB:0 [UP] Invalid document-start marker in doublequoted tring
#guard match parseYaml "---\n\"\n---\n\"\n" with
  | .ok _ => true
  | .error _ => false

-- 5U3A:0 [UP] Sequence on same Line as Mapping Key
#guard match parseYaml "key: - a\n     - b\n" with
  | .ok _ => true
  | .error _ => false

-- 62EZ:0 [UP] Invalid block mapping key on same line as previous key
#guard match parseYaml "---\nx: { y: z }in: valid\n" with
  | .ok _ => true
  | .error _ => false

-- 6JTT:0 [UP] Flow sequence without closing bracket
#guard match parseYaml "---\n[ [ a, b, c ]\n" with
  | .ok _ => true
  | .error _ => false

-- 6S55:0 [UP] Invalid scalar at the end of sequence
#guard match parseYaml "key:\n - bar\n - baz\n invalid\n" with
  | .ok _ => true
  | .error _ => false

-- 7LBH:0 [UP] Multiline double quoted implicit keys
#guard match parseYaml "\"a\\nb\": 1\n\"c\n d\": 1\n" with
  | .ok _ => true
  | .error _ => false

-- 7MNF:0 [UP] Missing colon
#guard match parseYaml "top1:\n  key1: val1\ntop2\n" with
  | .ok _ => true
  | .error _ => false

-- 8XDJ:0 [UP] Comment in plain multiline value
#guard match parseYaml "key: word1\n#  xxx\n  word2\n" with
  | .ok _ => true
  | .error _ => false

-- 9C9N:0 [UP] Wrong indented flow sequence
#guard match parseYaml "---\nflow: [a,\nb,\nc]\n" with
  | .ok _ => true
  | .error _ => false

-- 9CWY:0 [UP] Invalid scalar at the end of mapping
#guard match parseYaml "key:\n - item1\n - item2\ninvalid\n" with
  | .ok _ => true
  | .error _ => false

-- 9HCY:0 Need document footer before directives
#guard match parseYaml "!foo \"bar\"\n%TAG ! tag:example.com,2000:app/\n---\n!foo \"bar\"\n" with
  | .ok _ => false
  | .error _ => true

-- 9JBA:0 Invalid comment after end of flow sequence
#guard match parseYaml "---\n[ a, b, c, ]#invalid\n" with
  | .ok _ => false
  | .error _ => true

-- 9KBC:0 [UP] Mapping starting at --- line
#guard match parseYaml "--- key1: value1\n    key2: value2\n" with
  | .ok _ => true
  | .error _ => false

-- 9MAG:0 [UP] Flow sequence with invalid comma at the beginning
#guard match parseYaml "---\n[ , a, b, c ]\n" with
  | .ok _ => true
  | .error _ => false

-- 9MMA:0 Directive by itself with no document
#guard match parseYaml "%YAML 1.2\n" with
  | .ok _ => false
  | .error _ => true

-- 9MQT:1 [UP]
#guard match parseYaml "--- \"a\n... x\nb\"\n" with
  | .ok _ => true
  | .error _ => false

-- B63P:0 Directive without document
#guard match parseYaml "%YAML 1.2\n...\n" with
  | .ok _ => false
  | .error _ => true

-- BD7L:0 [UP] Invalid mapping after sequence
#guard match parseYaml "- item1\n- item2\ninvalid: x\n" with
  | .ok _ => true
  | .error _ => false

-- BF9H:0 [UP] Trailing comment in multiline plain scalar
#guard match parseYaml "---\nplain: a\n       b # end of scalar\n       c\n" with
  | .ok _ => true
  | .error _ => false

-- BS4K:0 [UP] Comment between plain scalar lines
#guard match parseYaml "word1  # comment\nword2\n" with
  | .ok _ => true
  | .error _ => false

-- C2SP:0 [UP] Flow Mapping Key on two lines
#guard match parseYaml "[23\n]: 42\n" with
  | .ok _ => true
  | .error _ => false

-- CML9:0 [UP] Missing comma in flow
#guard match parseYaml "key: [ word1\n#  xxx\n  word2 ]\n" with
  | .ok _ => true
  | .error _ => false

-- CQ3W:0 Double quoted string without closing quote
#guard match parseYaml "---\nkey: \"missing closing quote\n" with
  | .ok _ => false
  | .error _ => true

-- CTN5:0 [UP] Flow sequence with invalid extra comma
#guard match parseYaml "---\n[ a, b, c, , ]\n" with
  | .ok _ => true
  | .error _ => false

-- CVW2:0 Invalid comment after comma
#guard match parseYaml "---\n[ a, b, c,#invalid\n]\n" with
  | .ok _ => false
  | .error _ => true

-- CXX2:0 [UP] Mapping with anchor on document start line
#guard match parseYaml "--- &anchor a: b\n" with
  | .ok _ => true
  | .error _ => false

-- D49Q:0 [UP] Multiline single quoted implicit keys
#guard match parseYaml "'a\\nb': 1\n'c\n d': 1\n" with
  | .ok _ => true
  | .error _ => false

-- DK4H:0 [UP] Implicit key followed by newline
#guard match parseYaml "---\n[ key\n  : value ]\n" with
  | .ok _ => true
  | .error _ => false

-- DK95:1 [UP]
#guard match parseYaml "foo: \"bar\n\tbaz\"\n" with
  | .ok _ => true
  | .error _ => false

-- DK95:6
#guard match parseYaml "foo:\n  a: 1\n  \tb: 2\n" with
  | .ok _ => false
  | .error _ => true

-- DMG6:0 [UP] Wrong indendation in Map
#guard match parseYaml "key:\n  ok: 1\n wrong: 2\n" with
  | .ok _ => true
  | .error _ => false

-- EB22:0 Missing document-end marker before directive
#guard match parseYaml "---\nscalar1 # comment\n%YAML 1.2\n---\nscalar2\n" with
  | .ok _ => false
  | .error _ => true

-- EW3V:0 [UP] Wrong indendation in mapping
#guard match parseYaml "k1: v1\n k2: v2\n" with
  | .ok _ => true
  | .error _ => false

-- G5U8:0 Plain dashes in flow sequence
#guard match parseYaml "---\n- [-, -]\n" with
  | .ok _ => false
  | .error _ => true

-- G7JE:0 [UP] Multiline implicit keys
#guard match parseYaml "a\\nb: 1\nc\n d: 1\n" with
  | .ok _ => true
  | .error _ => false

-- G9HC:0 [UP] Invalid anchor in zero indented sequence
#guard match parseYaml "---\nseq:\n&anchor\n- a\n- b\n" with
  | .ok _ => true
  | .error _ => false

-- GDY7:0 [UP] Comment that looks like a mapping key
#guard match parseYaml "key: value\nthis is #not a: key\n" with
  | .ok _ => true
  | .error _ => false

-- GT5M:0 [UP] Node anchor in sequence
#guard match parseYaml "- item1\n&node\n- item2\n" with
  | .ok _ => true
  | .error _ => false

-- H7J7:0 [UP] Node anchor not indented
#guard match parseYaml "key: &x\n!!map\n  a: b\n" with
  | .ok _ => true
  | .error _ => false

-- H7TQ:0 Extra words on %YAML directive
#guard match parseYaml "%YAML 1.2 foo\n---\n" with
  | .ok _ => false
  | .error _ => true

-- HRE5:0 Double quoted scalar with escaped single quote
#guard match parseYaml "---\ndouble: \"quoted \\' scalar\"\n" with
  | .ok _ => false
  | .error _ => true

-- HU3P:0 [UP] Invalid Mapping in plain scalar
#guard match parseYaml "key:\n  word1 word2\n  no: key\n" with
  | .ok _ => true
  | .error _ => false

-- JKF3:0 [UP] Multiline unidented double quoted block key
#guard match parseYaml "- - \"bar\nbar\": x\n" with
  | .ok _ => true
  | .error _ => false

-- JY7Z:0 [UP] Trailing content that looks like a mapping
#guard match parseYaml "key1: \"quoted1\"\nkey2: \"quoted2\" no key: nor value\nkey3: \"quoted3\"\n" with
  | .ok _ => true
  | .error _ => false

-- KS4U:0 [UP] Invalid item after end of flow sequence
#guard match parseYaml "---\n[\nsequence item\n]\ninvalid item\n" with
  | .ok _ => true
  | .error _ => false

-- LHL4:0 [UP] Invalid tag
#guard match parseYaml "---\n!invalid{}tag scalar\n" with
  | .ok _ => true
  | .error _ => false

-- MUS6:0 Directive variants
#guard match parseYaml "%YAML 1.1#...\n---\n" with
  | .ok _ => false
  | .error _ => true

-- MUS6:1
#guard match parseYaml "%YAML 1.2\n---\n%YAML 1.2\n---\n" with
  | .ok _ => false
  | .error _ => true

-- N4JP:0 [UP] Bad indentation in mapping
#guard match parseYaml "map:\n  key1: \"quoted1\"\n key2: \"bad indentation\"\n" with
  | .ok _ => true
  | .error _ => false

-- N782:0 [UP] Invalid document markers in flow style
#guard match parseYaml "[\n--- ,\n...\n]\n" with
  | .ok _ => true
  | .error _ => false

-- P2EQ:0 [UP] Invalid sequene item on same line as previous item
#guard match parseYaml "---\n- { y: z }- invalid\n" with
  | .ok _ => true
  | .error _ => false

-- Q4CL:0 [UP] Trailing content after quoted value
#guard match parseYaml "key1: \"quoted1\"\nkey2: \"quoted2\" trailing content\nkey3: \"quoted3\"\n" with
  | .ok _ => true
  | .error _ => false

-- QB6E:0 [UP] Wrong indented multiline quoted scalar
#guard match parseYaml "---\nquoted: \"a\nb\nc\"\n" with
  | .ok _ => true
  | .error _ => false

-- QLJ7:0 [UP] Tag shorthand used in documents but only defined in the first
#guard match parseYaml "%TAG !prefix! tag:example.com,2011:\n--- !prefix!A\na: b\n--- !prefix!B\nc: d\n--- !prefix!C\ne: f\n" with
  | .ok _ => true
  | .error _ => false

-- RHX7:0 YAML directive without document end marker
#guard match parseYaml "---\nkey: value\n%YAML 1.2\n---\n" with
  | .ok _ => false
  | .error _ => true

-- RXY3:0 [UP] Invalid document-end marker in single quoted string
#guard match parseYaml "---\n'\n...\n'\n" with
  | .ok _ => true
  | .error _ => false

-- S4GJ:0 Invalid text after block scalar indicator
#guard match parseYaml "---\nfolded: > first line\n  second line\n" with
  | .ok _ => false
  | .error _ => true

-- S98Z:0 [UP] Block scalar with more spaces than first content line
#guard match parseYaml "empty block scalar: >\n \n  \n   \n # comment\n" with
  | .ok _ => true
  | .error _ => false

-- SF5V:0 Duplicate YAML directive
#guard match parseYaml "%YAML 1.2\n%YAML 1.2\n---\n" with
  | .ok _ => false
  | .error _ => true

-- SR86:0 [UP] Anchor plus Alias
#guard match parseYaml "key1: &a value\nkey2: &b *a\n" with
  | .ok _ => true
  | .error _ => false

-- SU5Z:0 Comment without whitespace after doublequoted scalar
#guard match parseYaml "key: \"value\"# invalid comment\n" with
  | .ok _ => false
  | .error _ => true

-- SU74:0 [UP] Anchor and alias as mapping key
#guard match parseYaml "key1: &alias value1\n&b *alias : value2\n" with
  | .ok _ => true
  | .error _ => false

-- SY6V:0 [UP] Anchor before sequence entry on same line
#guard match parseYaml "&anchor - sequence entry\n" with
  | .ok _ => true
  | .error _ => false

-- T833:0 [UP] Flow mapping missing a separating comma
#guard match parseYaml "---\n{\n foo: 1\n bar: 2 }\n" with
  | .ok _ => true
  | .error _ => false

-- TD5N:0 [UP] Invalid scalar after sequence
#guard match parseYaml "- item1\n- item2\ninvalid\n" with
  | .ok _ => true
  | .error _ => false

-- U44R:0 [UP] Bad indentation in mapping (2)
#guard match parseYaml "map:\n  key1: \"quoted1\"\n   key2: \"bad indentation\"\n" with
  | .ok _ => true
  | .error _ => false

-- U99R:0 [UP] Invalid comma in tag
#guard match parseYaml "- !!str, xxx\n" with
  | .ok _ => true
  | .error _ => false

-- VJP3:0 [UP] Flow collections over many lines
#guard match parseYaml "k: {\nk\n:\nv\n}\n" with
  | .ok _ => true
  | .error _ => false

-- W9L4:0 [UP] Literal block scalar with more spaces in first line
#guard match parseYaml "---\nblock scalar: |\n     \n  more spaces at the beginning\n  are invalid\n" with
  | .ok _ => true
  | .error _ => false

-- X4QW:0 Comment without whitespace after block scalar indicator
#guard match parseYaml "block: ># comment\n  scalar\n" with
  | .ok _ => false
  | .error _ => true

-- Y79Y:0 [UP] Tabs in various contexts
#guard match parseYaml "foo: |\n\t\nbar: 1\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:3 [UP]
#guard match parseYaml "- [\n\tfoo,\n foo\n ]\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:4 [UP]
#guard match parseYaml "-\t-\n\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:5 [UP]
#guard match parseYaml "- \t-\n\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:6 [UP]
#guard match parseYaml "?\t-\n\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:7 [UP]
#guard match parseYaml "? -\n:\t-\n\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:8 [UP]
#guard match parseYaml "?\tkey:\n\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:9 [UP]
#guard match parseYaml "? key:\n:\tkey:\n\n" with
  | .ok _ => true
  | .error _ => false

-- YJV2:0 Dash in flow sequence
#guard match parseYaml "[-]\n" with
  | .ok _ => false
  | .error _ => true

-- ZCZ6:0 [UP] Invalid mapping in plain single line value
#guard match parseYaml "a: b: c: d\n" with
  | .ok _ => true
  | .error _ => false

-- ZL4Z:0 [UP] Invalid nested mapping
#guard match parseYaml "---\na: 'b': c\n" with
  | .ok _ => true
  | .error _ => false

-- ZVH3:0 [UP] Wrong indented sequence item
#guard match parseYaml "- key: value\n - item1\n" with
  | .ok _ => true
  | .error _ => false

-- ZXT5:0 [UP] Implicit key followed by newline and adjacent value
#guard match parseYaml "[ \"key\"\n  :value ]\n" with
  | .ok _ => true
  | .error _ => false

-- ZYU8:2
#guard match parseYaml "%YAML 1.1 1.2\n---\n" with
  | .ok _ => false
  | .error _ => true

end Lean4Yaml.Proofs.SuiteGuards.Error
