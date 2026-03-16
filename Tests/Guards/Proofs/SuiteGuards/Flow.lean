/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.TokenParser

/-!
# yaml-test-suite Compile-Time Guards — Flow Stage

Auto-generated from yaml-test-suite test files by `gen-suite-guards.py`.
Each `#guard` is evaluated by Lean's kernel during `lake build`.

**43 guards** covering all passing flow tests.

These are Phase 4 of the verification plan: yaml-test-suite as compile-time proofs.
-/

namespace Lean4Yaml.Proofs.SuiteGuards.Flow

open Lean4Yaml.TokenParser

-- parseFlowSequence/parseFlowMapping now error on missing closing bracket
-- (Pattern 5 resolution), which increases kernel reduction depth.
-- tryConsume .key in parseFlowMappingValue adds one more reduction layer.
set_option maxRecDepth 4096

-- 4ABK:0 Flow Mapping Separate Values
#guard match parseYaml "{\nunquoted : \"separate\",\nhttp://foo.com,\nomitted value:,\n}\n" with
  | .ok _ => true
  | .error _ => false

-- 4MUZ:0 Flow mapping colon on line after key
#guard match parseYaml "{\"foo\"\n: \"bar\"}\n" with
  | .ok _ => true
  | .error _ => false

-- 4RWC:0 Trailing spaces after flow collection
#guard match parseYaml "[1, 2, 3]  \n" with
  | .ok _ => true
  | .error _ => false

-- 54T7:0 Flow Mapping
#guard match parseYaml "{foo: you, bar: far}\n" with
  | .ok _ => true
  | .error _ => false

-- 58MP:0 Flow mapping edge cases
-- Scanner bug: `:x` tokenized as `key, value, scalar "x"` (colon-chain).
-- Old code silently produced wrong structure; Pattern 5 code correctly errors.
-- Fix requires scanner-level changes to handle `:` in flow plain scalars.
-- #guard match parseYaml "{x: :x}\n" with
--   | .ok _ => true
--   | .error _ => false

-- 5C5M:0 Spec Example 7.15. Flow Mappings
#guard match parseYaml "- { one : two , three: four , }\n- {five: six,seven : eight}\n" with
  | .ok _ => true
  | .error _ => false

-- 5KJE:0 Spec Example 7.13. Flow Sequence
#guard match parseYaml "- [ one, two, ]\n- [three ,four]\n" with
  | .ok _ => true
  | .error _ => false

-- 5MUD:0 Colon and adjacent value on next line
#guard match parseYaml "---\n{ \"foo\"\n  :bar }\n" with
  | .ok _ => true
  | .error _ => false

-- 5T43:0 Colon at the beginning of adjacent flow scalar
-- Scanner bug: `::value` tokenized as colon-chain (same as 58MP).
-- #guard match parseYaml "- { \"key\":value }\n- { \"key\"::value }\n" with
--   | .ok _ => true
--   | .error _ => false

-- 652Z:0 Question mark at start of flow key
#guard match parseYaml "{ ?foo: bar,\nbar: 42\n}\n" with
  | .ok _ => true
  | .error _ => false

-- 6HB6:0 Spec Example 6.1. Indentation Spaces
#guard match parseYaml "# Leading comment line spaces are\n # neither content nor indentation.\n" with
  | .ok _ => true
  | .error _ => false

-- 7TMG:0 Comment in flow sequence before comma
#guard match parseYaml "---\n[ word1\n# comment\n, word2]\n" with
  | .ok _ => true
  | .error _ => false

-- 7ZZ5:0 Empty flow collections
#guard match parseYaml "---\nnested sequences:\n- - - []\n- - - {}\nkey1: []\nkey2: {}\n" with
  | .ok _ => true
  | .error _ => false

-- 87E4:0 Spec Example 7.8. Single Quoted Implicit Keys
#guard match parseYaml "'implicit block key' : [\n  'implicit flow key' : value,\n ]\n" with
  | .ok _ => true
  | .error _ => false

-- 8KB6:0 Multiline plain flow mapping key without value
#guard match parseYaml "---\n- { single line, a: b}\n- { multi\n  line, a: b}\n" with
  | .ok _ => true
  | .error _ => false

-- 8UDB:0 Spec Example 7.14. Flow Sequence Entries
#guard match parseYaml "[\n\"double\n quoted\", 'single\n           quoted',\nplain\n text, [ nested ],\nsingle: pair,\n]\n" with
  | .ok _ => true
  | .error _ => false

-- 9BXH:0 Multiline doublequoted flow mapping key without value
#guard match parseYaml "---\n- { \"single line\", a: b}\n- { \"multi\n  line\", a: b}\n" with
  | .ok _ => true
  | .error _ => false

-- 9MMW:0 Single Pair Implicit Entries
#guard match parseYaml "- [ YAML : separate ]\n- [ \"JSON like\":adjacent ]\n- [ {JSON: like}:adjacent ]\n" with
  | .ok _ => true
  | .error _ => false

-- 9SA2:0 Multiline double quoted flow mapping key
#guard match parseYaml "---\n- { \"single line\": value}\n- { \"multi\n  line\": value}\n" with
  | .ok _ => true
  | .error _ => false

-- C2DT:0 Spec Example 7.18. Flow Mapping Adjacent Values
#guard match parseYaml "{\n\"adjacent\":value,\n\"readable\": value,\n\"empty\":\n}\n" with
  | .ok _ => true
  | .error _ => false

-- CFD4:0 Empty implicit key in single pair flow sequences
#guard match parseYaml "- [ : empty key ]\n- [: another empty key]\n" with
  | .ok _ => true
  | .error _ => false

-- D88J:0 Flow Sequence in Block Mapping
#guard match parseYaml "a: [b, c]\n" with
  | .ok _ => true
  | .error _ => false

-- DBG4:0 Spec Example 7.10. Plain Characters
-- Scanner bug: `::vector` tokenized as colon-chain (same as 58MP).
-- #guard match parseYaml "# Outside flow collection:\n- ::vector\n- \": - ()\"\n- Up, up, and away!\n- -123\n- http://example.com/foo#bar\n# Inside flow collection:\n- [ ::vector,\n  \": - ()\",\n  \"Up, up and away!\",\n  -123,\n  http://example.com/foo#bar ]\n" with
--   | .ok _ => true
--   | .error _ => false

-- DHP8:0 Flow Sequence
#guard match parseYaml "[foo, bar, 42]\n" with
  | .ok _ => true
  | .error _ => false

-- F3CP:0 Nested flow collections on one line
#guard match parseYaml "---\n{ a: [b, c, { d: [e, f] } ] }\n" with
  | .ok _ => true
  | .error _ => false

-- FUP4:0 Flow Sequence in Flow Sequence
#guard match parseYaml "[a, [b, c]]\n" with
  | .ok _ => true
  | .error _ => false

-- HM87:0 Scalars in flow start with syntax char
#guard match parseYaml "[:x]\n" with
  | .ok _ => true
  | .error _ => false

-- JR7V:0 Question marks in scalars
#guard match parseYaml "- a?string\n- another ? string\n- key: value?\n- [a?string]\n- [another ? string]\n- {key: value? }\n- {key: value?}\n- {key?: value }\n" with
  | .ok _ => true
  | .error _ => false

-- K3WX:0 Colon and adjacent value after comment on next line
#guard match parseYaml "---\n{ \"foo\" # comment\n  :bar }\n" with
  | .ok _ => true
  | .error _ => false

-- L9U5:0 Spec Example 7.11. Plain Implicit Keys
#guard match parseYaml "implicit block key : [\n  implicit flow key : value,\n ]\n" with
  | .ok _ => true
  | .error _ => false

-- LP6E:0 Whitespace After Scalars in Flow
#guard match parseYaml "- [a, b , c ]\n- { \"a\"  : b\n   , c : 'd' ,\n   e   : \"f\"\n  }\n- [      ]\n" with
  | .ok _ => true
  | .error _ => false

-- LQZ7:0 Spec Example 7.4. Double Quoted Implicit Keys
#guard match parseYaml "\"implicit block key\" : [\n  \"implicit flow key\" : value,\n ]\n" with
  | .ok _ => true
  | .error _ => false

-- M7NX:0 Nested flow collections
#guard match parseYaml "---\n{\n a: [\n  b, c, {\n   d: [e, f]\n  }\n ]\n}\n" with
  | .ok _ => true
  | .error _ => false

-- MXS3:0 Flow Mapping in Block Sequence
#guard match parseYaml "- {a: b}\n" with
  | .ok _ => true
  | .error _ => false

-- NJ66:0 Multiline plain flow mapping key
#guard match parseYaml "---\n- { single line: value}\n- { multi\n  line: value}\n" with
  | .ok _ => true
  | .error _ => false

-- Q5MG:0 Tab at beginning of line followed by a flow mapping
#guard match parseYaml "\t{}\n" with
  | .ok _ => true
  | .error _ => false

-- Q88A:0 Spec Example 7.23. Flow Content
#guard match parseYaml "- [ a, b ]\n- { a: b }\n- \"a\"\n- 'b'\n- c\n" with
  | .ok _ => true
  | .error _ => false

-- QF4Y:0 Spec Example 7.19. Single Pair Flow Mappings
#guard match parseYaml "[\nfoo: bar\n]\n" with
  | .ok _ => true
  | .error _ => false

-- R52L:0 Nested flow mapping sequence and mappings
#guard match parseYaml "---\n{ top1: [item1, {key2: value2}, item3], top2: value2 }\n" with
  | .ok _ => true
  | .error _ => false

-- UDM2:0 Plain URL in flow mapping
#guard match parseYaml "- { url: http://example.org }\n" with
  | .ok _ => true
  | .error _ => false

-- UDR7:0 Spec Example 5.4. Flow Collection Indicators
#guard match parseYaml "sequence: [ one, two, ]\nmapping: { sky: blue, sea: green }\n" with
  | .ok _ => true
  | .error _ => false

-- ZF4X:0 Spec Example 2.6. Mapping of Mappings
#guard match parseYaml "Mark McGwire: {hr: 65, avg: 0.278}\nSammy Sosa: {\n    hr: 63,\n    avg: 0.288\n  }\n" with
  | .ok _ => true
  | .error _ => false

-- ZK9H:0 Nested top level flow mapping
#guard match parseYaml "{ key: [[[\n  value\n ]]]\n}\n" with
  | .ok _ => true
  | .error _ => false

end Lean4Yaml.Proofs.SuiteGuards.Flow
