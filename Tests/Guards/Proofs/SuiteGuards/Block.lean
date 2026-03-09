/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.TokenParser

/-!
# yaml-test-suite Compile-Time Guards — Block Stage

Auto-generated from yaml-test-suite test files by `gen-suite-guards.py`.
Each `#guard` is evaluated by Lean's kernel during `lake build`.

**82 guards** covering all passing block tests.

These are Phase 4 of the verification plan: yaml-test-suite as compile-time proofs.
-/

namespace Lean4Yaml.Proofs.SuiteGuards.Block

open Lean4Yaml.TokenParser

-- 229Q:0 Spec Example 2.4. Sequence of Mappings
#guard match parseYaml "-\n  name: Mark McGwire\n  hr:   65\n  avg:  0.278\n-\n  name: Sammy Sosa\n  hr:   63\n  avg:  0.288\n" with
  | .ok _ => true
  | .error _ => false

-- 2G84:2 
#guard match parseYaml "--- |1-\n" with
  | .ok _ => true
  | .error _ => false

-- 2G84:3 
#guard match parseYaml "--- |1+\n" with
  | .ok _ => true
  | .error _ => false

-- 2JQS:0 Block Mapping with Missing Keys
#guard match parseYaml ": a\n: b\n" with
  | .ok _ => true
  | .error _ => false

-- 3ALJ:0 Block Sequence in Block Sequence
#guard match parseYaml "- - s1_i1\n  - s1_i2\n- s2\n" with
  | .ok _ => true
  | .error _ => false

-- 3RLN:1 
#guard match parseYaml "\"2 leading\n    \\\ttab\"\n" with
  | .ok _ => true
  | .error _ => false

-- 3RLN:2 
#guard match parseYaml "\"3 leading\n    \ttab\"\n" with
  | .ok _ => true
  | .error _ => false

-- 3RLN:3 
#guard match parseYaml "\"4 leading\n    \\t  tab\"\n" with
  | .ok _ => true
  | .error _ => false

-- 3RLN:4 
#guard match parseYaml "\"5 leading\n    \\\t  tab\"\n" with
  | .ok _ => true
  | .error _ => false

-- 3RLN:5 
#guard match parseYaml "\"6 leading\n    \t  tab\"\n" with
  | .ok _ => true
  | .error _ => false

-- 4MUZ:1 
#guard match parseYaml "{\"foo\"\n: bar}\n" with
  | .ok _ => true
  | .error _ => false

-- 4MUZ:2 
#guard match parseYaml "{foo\n: bar}\n" with
  | .ok _ => true
  | .error _ => false

-- 5NYZ:0 Spec Example 6.9. Separated Comment
#guard match parseYaml "key:    # Comment\n  value\n" with
  | .ok _ => true
  | .error _ => false

-- 65WH:0 Single Entry Block Sequence
#guard match parseYaml "- foo\n" with
  | .ok _ => true
  | .error _ => false

-- 6BCT:0 Spec Example 6.3. Separation Spaces
#guard match parseYaml "- foo:\t bar\n- - baz\n  -\tbaz\n" with
  | .ok _ => true
  | .error _ => false

-- 6CA3:0 Tab indented top flow
#guard match parseYaml "\t[\n\t]\n" with
  | .ok _ => true
  | .error _ => false

-- 8QBE:0 Block Sequence in Block Mapping
#guard match parseYaml "key:\n - item1\n - item2\n" with
  | .ok _ => true
  | .error _ => false

-- 93JH:0 Block Mappings in Block Sequence
#guard match parseYaml "- key: value\n  key2: value2\n-\n  key3: value3\n" with
  | .ok _ => true
  | .error _ => false

-- 96NN:1 
#guard match parseYaml "foo: |-\n \tbar\n\n" with
  | .ok _ => true
  | .error _ => false

-- 98YD:0 Spec Example 5.5. Comment Indicator
#guard match parseYaml "# Comment only.\n" with
  | .ok _ => true
  | .error _ => false

-- 9FMG:0 Multi-level Mapping Indent
#guard match parseYaml "a:\n  b:\n    c: d\n  e:\n    f: g\nh: i\n" with
  | .ok _ => true
  | .error _ => false

-- 9J7A:0 Simple Mapping Indent
#guard match parseYaml "foo:\n  bar: baz\n" with
  | .ok _ => true
  | .error _ => false

-- 9U5K:0 Spec Example 2.12. Compact Nested Mapping
#guard match parseYaml "---\n# Products purchased\n- item    : Super Hoop\n  quantity: 1\n- item    : Basketball\n  quantity: 4\n- item    : Big Shoes\n  quantity: 1\n" with
  | .ok _ => true
  | .error _ => false

-- AZ63:0 Sequence With Same Indentation as Parent Mapping
#guard match parseYaml "one:\n- 2\n- 3\nfour: 5\n" with
  | .ok _ => true
  | .error _ => false

-- AZW3:0 Lookahead test cases
#guard match parseYaml "- bla\"keks: foo\n- bla]keks: foo\n" with
  | .ok _ => true
  | .error _ => false

-- D9TU:0 Single Pair Block Mapping
#guard match parseYaml "foo: bar\n" with
  | .ok _ => true
  | .error _ => false

-- DC7X:0 Various trailing tabs
#guard match parseYaml "a: b\t\nseq:\t\n - a\t\nc: d\t#X\n" with
  | .ok _ => true
  | .error _ => false

-- DE56:1 
#guard match parseYaml "\"2 trailing\\t  \n    tab\"\n" with
  | .ok _ => true
  | .error _ => false

-- DE56:2 
#guard match parseYaml "\"3 trailing\\\t\n    tab\"\n" with
  | .ok _ => true
  | .error _ => false

-- DE56:3 
#guard match parseYaml "\"4 trailing\\\t  \n    tab\"\n" with
  | .ok _ => true
  | .error _ => false

-- DE56:4 
#guard match parseYaml "\"5 trailing\t\n    tab\"\n" with
  | .ok _ => true
  | .error _ => false

-- DE56:5 
#guard match parseYaml "\"6 trailing\t  \n    tab\"\n" with
  | .ok _ => true
  | .error _ => false

-- DK95:0 Tabs that look like indentation
#guard match parseYaml "foo:\n \tbar\n" with
  | .ok _ => true
  | .error _ => false

-- DK95:2 
#guard match parseYaml "foo: \"bar\n  \tbaz\"\n" with
  | .ok _ => true
  | .error _ => false

-- DK95:4 
#guard match parseYaml "foo: 1\n\t\nbar: 2\n" with
  | .ok _ => true
  | .error _ => false

-- DK95:5 
#guard match parseYaml "foo: 1\n \t\nbar: 2\n" with
  | .ok _ => true
  | .error _ => false

-- DK95:7 
#guard match parseYaml "%YAML 1.2\n\t\n---\n" with
  | .ok _ => true
  | .error _ => false

-- DK95:8 
#guard match parseYaml "foo: \"bar\n \t \t baz \t \t \"\n" with
  | .ok _ => true
  | .error _ => false

-- FQ7F:0 Spec Example 2.1. Sequence of Scalars
#guard match parseYaml "- Mark McGwire\n- Sammy Sosa\n- Ken Griffey\n" with
  | .ok _ => true
  | .error _ => false

-- HM87:1 
#guard match parseYaml "[?x]\n" with
  | .ok _ => true
  | .error _ => false

-- J3BT:0 Spec Example 5.12. Tabs and Spaces
#guard match parseYaml "# Tabs and spaces\nquoted: \"Quoted \t\"\nblock:\t|\n  void main() {\n  \tprintf(\"Hello, world!\\n\");\n  }\n" with
  | .ok _ => true
  | .error _ => false

-- J5UC:0 Multiple Pair Block Mapping
#guard match parseYaml "foo: blue\nbar: arrr\nbaz: jazz\n" with
  | .ok _ => true
  | .error _ => false

-- J7VC:0 Empty Lines Between Mapping Elements
#guard match parseYaml "one: 2\n\n\nthree: 4\n" with
  | .ok _ => true
  | .error _ => false

-- J9HZ:0 Spec Example 2.9. Single Document with Two Comments
#guard match parseYaml "---\nhr: # 1998 hr ranking\n  - Mark McGwire\n  - Sammy Sosa\nrbi:\n  # 1998 rbi ranking\n  - Sammy Sosa\n  - Ken Griffey\n" with
  | .ok _ => true
  | .error _ => false

-- JEF9:1 
#guard match parseYaml "- |+\n   \n" with
  | .ok _ => true
  | .error _ => false

-- JEF9:2 
#guard match parseYaml "- |+\n   \n" with
  | .ok _ => true
  | .error _ => false

-- JQ4R:0 Spec Example 8.14. Block Sequence
#guard match parseYaml "block sequence:\n  - one\n  - two : three\n" with
  | .ok _ => true
  | .error _ => false

-- K4SU:0 Multiple Entry Block Sequence
#guard match parseYaml "- foo\n- bar\n- 42\n" with
  | .ok _ => true
  | .error _ => false

-- KH5V:1 
#guard match parseYaml "\"2 inline\\\ttab\"\n" with
  | .ok _ => true
  | .error _ => false

-- KH5V:2 
#guard match parseYaml "\"3 inline\ttab\"\n" with
  | .ok _ => true
  | .error _ => false

-- KMK3:0 Block Submapping
#guard match parseYaml "foo:\n  bar: 1\nbaz: 2\n" with
  | .ok _ => true
  | .error _ => false

-- L24T:0 Trailing line of spaces
#guard match parseYaml "foo: |\n  x\n   \n" with
  | .ok _ => true
  | .error _ => false

-- L24T:1 
#guard match parseYaml "foo: |\n  x\n   \n" with
  | .ok _ => true
  | .error _ => false

-- L383:0 Two scalar docs with trailing comments
#guard match parseYaml "--- foo  # comment\n--- foo  # comment\n" with
  | .ok _ => true
  | .error _ => false

-- M2N8:0 Question mark edge cases
#guard match parseYaml "- ? : x\n" with
  | .ok _ => true
  | .error _ => false

-- M2N8:1 
#guard match parseYaml "? []: x\n" with
  | .ok _ => true
  | .error _ => false

-- M6YH:0 Block sequence indentation
#guard match parseYaml "- |\n x\n-\n foo: bar\n-\n - 42\n" with
  | .ok _ => true
  | .error _ => false

-- MUS6:2 
#guard match parseYaml "%YAML  1.1\n---\n" with
  | .ok _ => true
  | .error _ => false

-- MUS6:3 
#guard match parseYaml "%YAML \t 1.1\n---\n\n" with
  | .ok _ => true
  | .error _ => false

-- MUS6:4 
#guard match parseYaml "%YAML 1.1  # comment\n---\n\n" with
  | .ok _ => true
  | .error _ => false

-- MUS6:5 
#guard match parseYaml "%YAM 1.1\n---\n\n" with
  | .ok _ => true
  | .error _ => false

-- MUS6:6 
#guard match parseYaml "%YAMLL 1.1\n---\n\n" with
  | .ok _ => true
  | .error _ => false

-- NHX8:0 Empty Lines at End of Document
#guard match parseYaml ":\n\n\n" with
  | .ok _ => true
  | .error _ => false

-- NKF9:0 Empty keys in block and flow mapping
#guard match parseYaml "---\nkey: value\n: empty key\n---\n{\n key: value, : empty key\n}\n---\n# empty key and value\n:\n---\n# empty key and value\n{ : }\n" with
  | .ok _ => true
  | .error _ => false

-- P94K:0 Spec Example 6.11. Multi-Line Comments
#guard match parseYaml "key:    # Comment\n        # lines\n  value\n\n\n" with
  | .ok _ => true
  | .error _ => false

-- PBJ2:0 Spec Example 2.3. Mapping Scalars to Sequences
#guard match parseYaml "american:\n  - Boston Red Sox\n  - Detroit Tigers\n  - New York Yankees\nnational:\n  - New York Mets\n  - Chicago Cubs\n  - Atlanta Braves\n" with
  | .ok _ => true
  | .error _ => false

-- RLU9:0 Sequence Indent
#guard match parseYaml "foo:\n- 42\nbar:\n  - 44\n" with
  | .ok _ => true
  | .error _ => false

-- S3PD:0 Spec Example 8.18. Implicit Block Mapping Entries
#guard match parseYaml "plain key: in-line value\n: # Both empty\n\"quoted key\":\n- entry\n" with
  | .ok _ => true
  | .error _ => false

-- SM9W:0 Single character streams
#guard match parseYaml "-\n" with
  | .ok _ => true
  | .error _ => false

-- SM9W:1 
#guard match parseYaml ":\n" with
  | .ok _ => true
  | .error _ => false

-- TE2A:0 Spec Example 8.16. Block Mappings
#guard match parseYaml "block mapping:\n key: value\n" with
  | .ok _ => true
  | .error _ => false

-- UKK6:0 Syntax character edge cases
#guard match parseYaml "- :\n" with
  | .ok _ => true
  | .error _ => false

-- UKK6:1 
#guard match parseYaml "::\n" with
  | .ok _ => true
  | .error _ => false

-- UKK6:2 
#guard match parseYaml "!\n" with
  | .ok _ => true
  | .error _ => false

-- UV7Q:0 Legal tab after indentation
#guard match parseYaml "x:\n - x\n  \tx\n" with
  | .ok _ => true
  | .error _ => false

-- VJP3:1 
#guard match parseYaml "k: {\n k\n :\n v\n }\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:1 
#guard match parseYaml "foo: |\n \t\nbar: 1\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:2 
#guard match parseYaml "- [\n\t\n foo\n ]\n" with
  | .ok _ => true
  | .error _ => false

-- Y79Y:10 
#guard match parseYaml "-\t-1\n" with
  | .ok _ => true
  | .error _ => false

-- YD5X:0 Spec Example 2.5. Sequence of Sequences
#guard match parseYaml "- [name        , hr, avg  ]\n- [Mark McGwire, 65, 0.278]\n- [Sammy Sosa  , 63, 0.288]\n" with
  | .ok _ => true
  | .error _ => false

-- ZYU8:1 
#guard match parseYaml "%***\n---\n\n" with
  | .ok _ => true
  | .error _ => false

-- ZYU8:3 
#guard match parseYaml "%YAML 1.12345\n---\n\n" with
  | .ok _ => true
  | .error _ => false

end Lean4Yaml.Proofs.SuiteGuards.Block
