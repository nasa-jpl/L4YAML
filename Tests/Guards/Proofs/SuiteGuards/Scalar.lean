/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.TokenParser

/-!
# yaml-test-suite Compile-Time Guards — Scalar Stage

Auto-generated from yaml-test-suite test files by `gen-suite-guards.py`.
Each `#guard` is evaluated by Lean's kernel during `lake build`.

**57 guards** covering all passing scalar tests.

These are Phase 4 of the verification plan: yaml-test-suite as compile-time proofs.
-/

namespace L4YAML.Proofs.SuiteGuards.Scalar

open L4YAML.TokenParser

-- 2EBW:0 Allowed characters in keys
#guard match parseYaml "a!\"#$%&'()*+,-./09:;<=>?@AZ[\\]^_`az{|}~: safe\n?foo: safe question mark\n:foo: safe colon\n-foo: safe dash\nthis is#not: a comment\n" with
  | .ok _ => true
  | .error _ => false

-- 36F6:0 Multiline plain scalar with empty line
#guard match parseYaml "---\nplain: a\n b\n\n c\n" with
  | .ok _ => true
  | .error _ => false

-- 3MYT:0 Plain Scalar looking like key, comment, anchor and tag
#guard match parseYaml "---\nk:#foo\n &a !t s\n" with
  | .ok _ => true
  | .error _ => false

-- 3RLN:0 Leading tabs in double quoted
#guard match parseYaml "\"1 leading\n    \\ttab\"\n" with
  | .ok _ => true
  | .error _ => false

-- 3UYS:0 Escaped slash in double quotes
#guard match parseYaml "escaped slash: \"a\\/b\"\n" with
  | .ok _ => true
  | .error _ => false

-- 4CQQ:0 Spec Example 2.18. Multi-line Flow Scalars
#guard match parseYaml "plain:\n  This unquoted scalar\n  spans many lines.\n\nquoted: \"So does this\n  quoted scalar.\\n\"\n" with
  | .ok _ => true
  | .error _ => false

-- 4V8U:0 Plain scalar with backslashes
#guard match parseYaml "---\nplain\\value\\with\\backslashes\n" with
  | .ok _ => true
  | .error _ => false

-- 4WA9:0 Literal scalars
#guard match parseYaml "- aaa: |2\n    xxx\n  bbb: |\n    xxx\n" with
  | .ok _ => true
  | .error _ => false

-- 4ZYM:0 Spec Example 6.4. Line Prefixes
#guard match parseYaml "plain: text\n  lines\nquoted: \"text\n  \tlines\"\nblock: |\n  text\n   \tlines\n" with
  | .ok _ => true
  | .error _ => false

-- 5BVJ:0 Spec Example 5.7. Block Scalar Indicators
#guard match parseYaml "literal: |\n  some\n  text\nfolded: >\n  some\n  text\n" with
  | .ok _ => true
  | .error _ => false

-- 5GBF:0 Spec Example 6.5. Empty Lines
#guard match parseYaml "Folding:\n  \"Empty line\n   \t\n  as a line feed\"\nChomping: |\n  Clipped empty lines\n \n\n" with
  | .ok _ => true
  | .error _ => false

-- 6FWR:0 Block Scalar Keep
#guard match parseYaml "--- |+\n ab\n \n  \n...\n" with
  | .ok _ => true
  | .error _ => false

-- 6H3V:0 Backslashes in singlequotes
#guard match parseYaml "'foo: bar\\': baz'\n" with
  | .ok _ => true
  | .error _ => false

-- 6JQW:0 Spec Example 2.13. In literals, newlines are preserved
#guard match parseYaml "# ASCII Art\n--- |\n  \\//||\\/||\n  // ||  ||__\n" with
  | .ok _ => true
  | .error _ => false

-- 6SLA:0 Allowed characters in quoted mapping key
#guard match parseYaml "\"foo\\nbar:baz\\tx \\\\$%^&*()x\": 23\n'x\\ny:z\\tx $%^&*()x': 24\n" with
  | .ok _ => true
  | .error _ => false

-- 6VJK:0 Spec Example 2.15. Folded newlines are preserved for "more indented" and blank lines
#guard match parseYaml ">\n Sammy Sosa completed another\n fine season with great stats.\n\n   63 Home Runs\n   0.288 Batting Average\n\n What a year!\n" with
  | .ok _ => true
  | .error _ => false

-- 7A4E:0 Spec Example 7.6. Double Quoted Lines
#guard match parseYaml "\" 1st non-empty\n\n 2nd non-empty \n\t3rd non-empty \"\n" with
  | .ok _ => true
  | .error _ => false

-- 7T8X:0 Spec Example 8.10. Folded Lines - 8.13. Final Empty Lines
#guard match parseYaml ">\n\n folded\n line\n\n next\n line\n   * bullet\n\n   * list\n   * lines\n\n last\n line\n\n# Comment\n" with
  | .ok _ => true
  | .error _ => false

-- 8CWC:0 Plain mapping key ending with colon
#guard match parseYaml "---\nkey ends with two colons::: value\n" with
  | .ok _ => true
  | .error _ => false

-- 8G76:0 Spec Example 6.10. Comment Lines
#guard match parseYaml "# Comment\n" with
  | .ok _ => true
  | .error _ => false

-- 96L6:0 Spec Example 2.14. In the folded scalars, newlines become spaces
#guard match parseYaml "--- >\n  Mark McGwire's\n  year was crippled\n  by a knee injury.\n" with
  | .ok _ => true
  | .error _ => false

-- 96NN:0 Leading tab content in literals
#guard match parseYaml "foo: |-\n \tbar\n" with
  | .ok _ => true
  | .error _ => false

-- 9MQT:0 Scalar doc with '...' in content
#guard match parseYaml "--- \"a\n...x\nb\"\n" with
  | .ok _ => true
  | .error _ => false

-- 9SHH:0 Spec Example 5.8. Quoted Scalar Indicators
#guard match parseYaml "single: 'text'\ndouble: \"text\"\n" with
  | .ok _ => true
  | .error _ => false

-- A6F9:0 Spec Example 8.4. Chomping Final Line Break
#guard match parseYaml "strip: |-\n  text\nclip: |\n  text\nkeep: |+\n  text\n" with
  | .ok _ => true
  | .error _ => false

-- A984:0 Multiline Scalar in Mapping
#guard match parseYaml "a: b\n c\nd:\n e\n  f\n" with
  | .ok _ => true
  | .error _ => false

-- AB8U:0 Sequence entry that looks like two with wrong indentation
#guard match parseYaml "- single multiline\n - sequence entry\n" with
  | .ok _ => true
  | .error _ => false

-- CPZ3:0 Doublequoted scalar starting with a tab
#guard match parseYaml "---\ntab: \"\\tstring\"\n" with
  | .ok _ => true
  | .error _ => false

-- D83L:0 Block scalar indicator order
#guard match parseYaml "- |2-\n  explicit indent and chomp\n- |-2\n  chomp and explicit indent\n" with
  | .ok _ => true
  | .error _ => false

-- DE56:0 Trailing tabs in double quoted
#guard match parseYaml "\"1 trailing\\t\n    tab\"\n" with
  | .ok _ => true
  | .error _ => false

-- DK3J:0 Zero indented block scalar with line that looks like a comment
#guard match parseYaml "--- >\nline1\n# no comment\nline3\n" with
  | .ok _ => true
  | .error _ => false

-- F6MC:0 More indented lines at the beginning of folded block scalars
#guard match parseYaml "---\na: >2\n   more indented\n  regular\nb: >2\n\n\n   more indented\n  regular\n" with
  | .ok _ => true
  | .error _ => false

-- F8F9:0 Spec Example 8.5. Chomping Trailing Lines
#guard match parseYaml "# Strip\n # Comments:\n" with
  | .ok _ => true
  | .error _ => false

-- FBC9:0 Allowed characters in plain scalars
#guard match parseYaml "safe: a!\"#$%&'()*+,-./09:;<=>?@AZ[\\]^_`az{|}~\n     !\"#$%&'()*+,-./09:;<=>?@AZ[\\]^_`az{|}~\nsafe question mark: ?foo\nsafe colon: :foo\nsafe dash: -foo\n" with
  | .ok _ => true
  | .error _ => false

-- FP8R:0 Zero indented block scalar
#guard match parseYaml "--- >\nline1\nline2\nline3\n" with
  | .ok _ => true
  | .error _ => false

-- G4RS:0 Spec Example 2.17. Quoted Scalars
#guard match parseYaml "unicode: \"Sosa did fine.\\u263A\"\ncontrol: \"\\b1998\\t1999\\t2000\\n\"\nhex esc: \"\\x0d\\x0a is \\r\\n\"\n\nsingle: '\"Howdy!\" he cried.'\nquoted: ' # Not a ''comment''.'\ntie-fighter: '|\\-*-/|'\n" with
  | .ok _ => true
  | .error _ => false

-- H2RW:0 Blank lines
#guard match parseYaml "foo: 1\n\nbar: 2\n    \ntext: |\n  a\n    \n  b\n\n  c\n \n  d\n" with
  | .ok _ => true
  | .error _ => false

-- H3Z8:0 Literal unicode
#guard match parseYaml "---\nwanted: love \u2665 and peace \u262E\n" with
  | .ok _ => true
  | .error _ => false

-- HMK4:0 Spec Example 2.16. Indentation determines scope
#guard match parseYaml "name: Mark McGwire\naccomplishment: >\n  Mark set a major league\n  home run record in 1998.\nstats: |\n  65 Home Runs\n  0.278 Batting Average\n" with
  | .ok _ => true
  | .error _ => false

-- HS5T:0 Spec Example 7.12. Plain Lines
#guard match parseYaml "1st non-empty\n\n 2nd non-empty \n\t3rd non-empty\n" with
  | .ok _ => true
  | .error _ => false

-- JEF9:0 Trailing whitespace in streams
#guard match parseYaml "- |+\n\n\n" with
  | .ok _ => true
  | .error _ => false

-- K858:0 Spec Example 8.6. Empty Scalar Chomping
#guard match parseYaml "strip: >-\n\nclip: >\n\nkeep: |+\n\n" with
  | .ok _ => true
  | .error _ => false

-- KH5V:0 Inline tabs in double quoted
#guard match parseYaml "\"1 inline\\ttab\"\n" with
  | .ok _ => true
  | .error _ => false

-- M29M:0 Literal Block Scalar
#guard match parseYaml "a: |\n ab\n \n cd\n ef\n \n\n...\n" with
  | .ok _ => true
  | .error _ => false

-- M9B4:0 Spec Example 8.7. Literal Scalar
#guard match parseYaml "|\n literal\n \ttext\n\n\n" with
  | .ok _ => true
  | .error _ => false

-- MJS9:0 Spec Example 6.7. Block Folding
#guard match parseYaml ">\n  foo \n \n  \t bar\n\n  baz\n" with
  | .ok _ => true
  | .error _ => false

-- MZX3:0 Non-Specific Tags on Scalars
#guard match parseYaml "- plain\n- \"double quoted\"\n- 'single quoted'\n- >\n  block\n- plain again\n" with
  | .ok _ => true
  | .error _ => false

-- NAT4:0 Various empty or newline only quoted strings
#guard match parseYaml "---\na: '\n  '\nb: '  \n  '\nc: \"\n  \"\nd: \"  \n  \"\ne: '\n\n  '\nf: \"\n\n  \"\ng: '\n\n\n  '\nh: \"\n\n\n  \"\n" with
  | .ok _ => true
  | .error _ => false

-- NB6Z:0 Multiline plain value with tabs on empty lines
#guard match parseYaml "key:\n  value\n  with\n  \t\n  tabs\n" with
  | .ok _ => true
  | .error _ => false

-- NP9H:0 Spec Example 7.5. Double Quoted Line Breaks
#guard match parseYaml "\"folded \nto a space,\t\n \nto a line feed, or \t\\\n \\ \tnon-content\"\n" with
  | .ok _ => true
  | .error _ => false

-- P2AD:0 Spec Example 8.1. Block Scalar Header
#guard match parseYaml "- | # Empty header\u2193\n literal\n- >1 # Indentation indicator\u2193\n  folded\n- |+ # Chomping indicator\u2193\n keep\n\n- >1- # Both indicators\u2193\n  strip\n" with
  | .ok _ => true
  | .error _ => false

-- PRH3:0 Spec Example 7.9. Single Quoted Lines
#guard match parseYaml "' 1st non-empty\n\n 2nd non-empty \n\t3rd non-empty '\n" with
  | .ok _ => true
  | .error _ => false

-- R4YG:0 Spec Example 8.2. Block Indentation Indicator
#guard match parseYaml "- |\n detected\n- >\n \n  \n  # detected\n- |1\n  explicit\n- >\n \t\n detected\n" with
  | .ok _ => true
  | .error _ => false

-- S7BG:0 Colon followed by comma
#guard match parseYaml "---\n- :,\n" with
  | .ok _ => true
  | .error _ => false

-- SYW4:0 Spec Example 2.2. Mapping Scalars to Scalars
#guard match parseYaml "hr:  65    # Home runs\navg: 0.278 # Batting average\nrbi: 147   # Runs Batted In\n" with
  | .ok _ => true
  | .error _ => false

-- TL85:0 Spec Example 6.8. Flow Folding
#guard match parseYaml "\"\n  foo \n \n  \t bar\n\n  baz\n\"\n" with
  | .ok _ => true
  | .error _ => false

-- W42U:0 Spec Example 8.15. Block Sequence Entry Types
#guard match parseYaml "- # Empty\n- |\n block node\n- - one # Compact\n  - two # sequence\n- one: two # Compact mapping\n" with
  | .ok _ => true
  | .error _ => false

end L4YAML.Proofs.SuiteGuards.Scalar
