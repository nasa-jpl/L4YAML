/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.TokenParser

/-!
# yaml-test-suite Compile-Time Guards — Advanced Stage

Auto-generated from yaml-test-suite test files by `gen-suite-guards.py`.
Each `#guard` is evaluated by Lean's kernel during `lake build`.

**64 guards** covering all passing advanced tests.

These are Phase 4 of the verification plan: yaml-test-suite as compile-time proofs.
-/

namespace Lean4Yaml.Proofs.SuiteGuards.Advanced

open Lean4Yaml.TokenParser

-- 26DV:0 Whitespace around colon in mappings
#guard match parseYaml "\"top1\" : \n  \"key1\" : &alias1 scalar1\n'top2' : \n  'key2' : &alias2 scalar2\ntop3: &node3 \n  *alias1 : scalar3\ntop4: \n  *alias2 : scalar4\ntop5   :    \n  scalar5\ntop6: \n  &anchor6 'key6' : scalar6\n" with
  | .ok _ => true
  | .error _ => false

-- 2AUY:0 Tags in Block Sequence
#guard match parseYaml "- !!str a\n- b\n- !!int 42\n- d\n" with
  | .ok _ => true
  | .error _ => false

-- 2XXW:0 Spec Example 2.25. Unordered Sets
#guard match parseYaml "# Sets are represented as a\n# Mapping where each key is\n# associated with a null value\n--- !!set\n? Mark McGwire\n? Sammy Sosa\n? Ken Griff\n" with
  | .ok _ => true
  | .error _ => false

-- 33X3:0 Three explicit integers in a block sequence
#guard match parseYaml "---\n- !!int 1\n- !!int -2\n- !!int 33\n" with
  | .ok _ => true
  | .error _ => false

-- 35KP:0 Tags for Root Objects
#guard match parseYaml "--- !!map\n? a\n: b\n--- !!seq\n- !!str c\n--- !!str\nd\ne\n" with
  | .ok _ => true
  | .error _ => false

-- 3GZX:0 Spec Example 7.1. Alias Nodes
#guard match parseYaml "First occurrence: &anchor Foo\nSecond occurrence: *anchor\nOverride anchor: &anchor Bar\nReuse anchor: *anchor\n" with
  | .ok _ => true
  | .error _ => false

-- 3R3P:0 Single block sequence with anchor
#guard match parseYaml "&sequence\n- a\n" with
  | .ok _ => true
  | .error _ => false

-- 4FJ6:0 Nested implicit complex keys
#guard match parseYaml "---\n[\n  [ a, [ [[b,c]]: d, e]]: 23\n]\n" with
  | .ok _ => true
  | .error _ => false

-- 565N:0 Construct Binary
#guard match parseYaml "canonical: !!binary \"\\\n R0lGODlhDAAMAIQAAP//9/X17unp5WZmZgAAAOfn515eXvPz7Y6OjuDg4J+fn5\\\n OTk6enp56enmlpaWNjY6Ojo4SEhP/++f/++f/++f/++f/++f/++f/++f/++f/+\\\n +f/++f/++f/++f/++f/++SH+Dk1hZGUgd2l0aCBHSU1QACwAAAAADAAMAAAFLC\\\n AgjoEwnuNAFOhpEMTRiggcz4BNJHrv/zCFcLiwMWYNG84BwwEeECcgggoBADs=\"\ngeneric: !!binary |\n R0lGODlhDAAMAIQAAP//9/X17unp5WZmZgAAAOfn515eXvPz7Y6OjuDg4J+fn5\n OTk6enp56enmlpaWNjY6Ojo4SEhP/++f/++f/++f/++f/++f/++f/++f/++f/+\n +f/++f/++f/++f/++f/++SH+Dk1hZGUgd2l0aCBHSU1QACwAAAAADAAMAAAFLC\n AgjoEwnuNAFOhpEMTRiggcz4BNJHrv/zCFcLiwMWYNG84BwwEeECcgggoBADs=\ndescription:\n The binary value above is a tiny arrow encoded as a gif image.\n" with
  | .ok _ => true
  | .error _ => false

-- 57H4:0 Spec Example 8.22. Block Collection Nodes
#guard match parseYaml "sequence: !!seq\n- entry\n- !!seq\n - nested\nmapping: !!map\n foo: bar\n" with
  | .ok _ => true
  | .error _ => false

-- 5TYM:0 Spec Example 6.21. Local Tag Prefix
#guard match parseYaml "%TAG !m! !my-\n--- # Bulb here\n!m!light fluorescent\n...\n%TAG !m! !my-\n--- # Color here\n!m!light green\n" with
  | .ok _ => true
  | .error _ => false

-- 5WE3:0 Spec Example 8.17. Explicit Block Mapping Entries
#guard match parseYaml "? explicit key # Empty value\n? |\n  block key\n: - one # Explicit compact\n  - two # block value\n" with
  | .ok _ => true
  | .error _ => false

-- 6BFJ:0 Mapping, key and flow sequence item anchors
#guard match parseYaml "---\n&mapping\n&key [ &item a, b, c ]: value\n" with
  | .ok _ => true
  | .error _ => false

-- 6CK3:0 Spec Example 6.26. Tag Shorthands
#guard match parseYaml "%TAG !e! tag:example.com,2000:app/\n---\n- !local foo\n- !!str bar\n- !e!tag%21 baz\n" with
  | .ok _ => true
  | .error _ => false

-- 6JWB:0 Tags for Block Objects
#guard match parseYaml "foo: !!seq\n  - !!str a\n  - !!map\n    key: !!str value\n" with
  | .ok _ => true
  | .error _ => false

-- 6KGN:0 Anchor for empty node
#guard match parseYaml "---\na: &anchor\nb: *anchor\n" with
  | .ok _ => true
  | .error _ => false

-- 6M2F:0 Aliases in Explicit Block Mapping
#guard match parseYaml "? &a a\n: &b b\n: *a\n" with
  | .ok _ => true
  | .error _ => false

-- 6PBE:0 Zero-indented sequences in explicit mapping keys
#guard match parseYaml "---\n?\n- a\n- b\n:\n- c\n- d\n" with
  | .ok _ => true
  | .error _ => false

-- 735Y:0 Spec Example 8.20. Block Node Types
#guard match parseYaml "-\n  \"flow in block\"\n- >\n Block scalar\n- !!map # Block collection\n  foo : bar\n" with
  | .ok _ => true
  | .error _ => false

-- 74H7:0 Tags in Implicit Mapping
#guard match parseYaml "!!str a: b\nc: !!int 42\ne: !!str f\ng: h\n!!str 23: !!bool false\n" with
  | .ok _ => true
  | .error _ => false

-- 7BUB:0 Spec Example 2.10. Node for “Sammy Sosa” appears twice in this document
#guard match parseYaml "---\nhr:\n  - Mark McGwire\n  # Following node labeled SS\n  - &SS Sammy Sosa\nrbi:\n  - *SS # Subsequent occurrence\n  - Ken Griffey\n" with
  | .ok _ => true
  | .error _ => false

-- 7FWL:0 Spec Example 6.24. Verbatim Tags
#guard match parseYaml "!<tag:yaml.org,2002:str> foo :\n  !<!bar> baz\n" with
  | .ok _ => true
  | .error _ => false

-- 7W2P:0 Block Mapping with Missing Values
#guard match parseYaml "? a\n? b\nc:\n" with
  | .ok _ => true
  | .error _ => false

-- 8XYN:0 Anchor with unicode character
#guard match parseYaml "---\n- &😁 unicode anchor\n" with
  | .ok _ => true
  | .error _ => false

-- A2M4:0 Spec Example 6.2. Indentation Indicators
#guard match parseYaml "? a\n: -\tb\n  -  -\tc\n     - d\n" with
  | .ok _ => true
  | .error _ => false

-- C4HZ:0 Spec Example 2.24. Global Tags
#guard match parseYaml "%TAG ! tag:clarkevans.com,2002:\n--- !shape\n  # Use the ! handle for presenting\n  # tag:clarkevans.com,2002:circle\n- !circle\n  center: &ORIGIN {x: 73, y: 129}\n  radius: 7\n- !line\n  start: *ORIGIN\n  finish: { x: 89, y: 102 }\n- !label\n  start: *ORIGIN\n  color: 0xFFEEBB\n  text: Pretty vector drawing.\n" with
  | .ok _ => true
  | .error _ => false

-- CC74:0 Spec Example 6.20. Tag Handles
#guard match parseYaml "%TAG !e! tag:example.com,2000:app/\n---\n!e!foo \"bar\"\n" with
  | .ok _ => true
  | .error _ => false

-- CN3R:0 Various location of anchors in flow sequence
#guard match parseYaml "&flowseq [\n a: b,\n &c c: d,\n { &e e: f },\n &g { g: h }\n]\n" with
  | .ok _ => true
  | .error _ => false

-- CT4Q:0 Spec Example 7.20. Single Pair Explicit Entry
#guard match parseYaml "[\n? foo\n bar : baz\n]\n" with
  | .ok _ => true
  | .error _ => false

-- CUP7:0 Spec Example 5.6. Node Property Indicators
#guard match parseYaml "anchored: !local &anchor value\nalias: *anchor\n" with
  | .ok _ => true
  | .error _ => false

-- DFF7:0 Spec Example 7.16. Flow Mapping Entries
#guard match parseYaml "{\n? explicit: entry,\nimplicit: entry,\n?\n}\n" with
  | .ok _ => true
  | .error _ => false

-- E76Z:0 Aliases in Implicit Block Mapping
#guard match parseYaml "&a a: &b b\n*b : *a\n" with
  | .ok _ => true
  | .error _ => false

-- EHF6:0 Tags for Flow Objects
#guard match parseYaml "!!map {\n  k: !!seq\n  [ a, !!str b]\n}\n" with
  | .ok _ => true
  | .error _ => false

-- F2C7:0 Anchors and Tags
#guard match parseYaml "- &a !!str a\n- !!int 2\n- !!int &c 4\n- &d d\n" with
  | .ok _ => true
  | .error _ => false

-- FH7J:0 Tags on Empty Scalars
#guard match parseYaml "- !!str\n-\n  !!null : a\n  b: !!str\n- !!str : !!null\n" with
  | .ok _ => true
  | .error _ => false

-- FRK4:0 Spec Example 7.3. Completely Empty Flow Nodes
#guard match parseYaml "{\n  ? foo :,\n  : bar,\n}\n" with
  | .ok _ => true
  | .error _ => false

-- FTA2:0 Single block sequence with anchor and explicit document start
#guard match parseYaml "--- &sequence\n- a\n" with
  | .ok _ => true
  | .error _ => false

-- GH63:0 Mixed Block Mapping (explicit to implicit)
#guard match parseYaml "? a\n: 1.3\nfifteen: d\n" with
  | .ok _ => true
  | .error _ => false

-- HMQ5:0 Spec Example 6.23. Node Properties
#guard match parseYaml "!!str &a1 \"foo\":\n  !!str bar\n&a2 baz : *a1\n" with
  | .ok _ => true
  | .error _ => false

-- J7PZ:0 Spec Example 2.26. Ordered Mappings
#guard match parseYaml "# The !!omap tag is one of the optional types\n# introduced for YAML 1.1. In 1.2, it is not\n# part of the standard tags and should not be\n# enabled by default.\n# Ordered maps are represented as\n# A sequence of mappings, with\n# each mapping having one key\n--- !!omap\n- Mark McGwire: 65\n- Sammy Sosa: 63\n- Ken Griffy: 58\n" with
  | .ok _ => true
  | .error _ => false

-- JS2J:0 Spec Example 6.29. Node Anchors
#guard match parseYaml "First occurrence: &anchor Value\nSecond occurrence: *anchor\n" with
  | .ok _ => true
  | .error _ => false

-- JTV5:0 Block Mapping with Multiline Scalars
#guard match parseYaml "? a\n  true\n: null\n  d\n? e\n  42\n" with
  | .ok _ => true
  | .error _ => false

-- KK5P:0 Various combinations of explicit block mappings
#guard match parseYaml "complex1:\n  ? - a\ncomplex2:\n  ? - a\n  : b\ncomplex3:\n  ? - a\n  : >\n    b\ncomplex4:\n  ? >\n    a\n  :\ncomplex5:\n  ? - a\n  : - b\n" with
  | .ok _ => true
  | .error _ => false

-- L94M:0 Tags in Explicit Mapping
#guard match parseYaml "? !!str a\n: !!int 47\n? c\n: !!str d\n" with
  | .ok _ => true
  | .error _ => false

-- LE5A:0 Spec Example 7.24. Flow Nodes
#guard match parseYaml "- !!str \"a\"\n- 'b'\n- &anchor \"c\"\n- *anchor\n- !!str\n" with
  | .ok _ => true
  | .error _ => false

-- M5DY:0 Spec Example 2.11. Mapping between Sequences
#guard match parseYaml "? - Detroit Tigers\n  - Chicago cubs\n:\n  - 2001-07-23\n\n? [ New York Yankees,\n    Atlanta Braves ]\n: [ 2001-07-02, 2001-08-12,\n    2001-08-14 ]\n" with
  | .ok _ => true
  | .error _ => false

-- P76L:0 Spec Example 6.19. Secondary Tag Handle
#guard match parseYaml "%TAG !! tag:example.com,2000:app/\n---\n!!int 1 - 3 # Interval, not integer\n" with
  | .ok _ => true
  | .error _ => false

-- PW8X:0 Anchors on Empty Scalars
#guard match parseYaml "- &a\n- a\n-\n  &a : a\n  b: &b\n-\n  &c : &a\n-\n  ? &d\n-\n  ? &e\n  : &a\n" with
  | .ok _ => true
  | .error _ => false

-- RR7F:0 Mixed Block Mapping (implicit to explicit)
#guard match parseYaml "a: 4.2\n? d\n: 23\n" with
  | .ok _ => true
  | .error _ => false

-- S4JQ:0 Spec Example 6.28. Non-Specific Tags
#guard match parseYaml "# Assuming conventional resolution:\n- \"12\"\n- 12\n- ! 12\n" with
  | .ok _ => true
  | .error _ => false

-- S9E8:0 Spec Example 5.3. Block Structure Indicators
#guard match parseYaml "sequence:\n- one\n- two\nmapping:\n  ? sky\n  : blue\n  sea : green\n" with
  | .ok _ => true
  | .error _ => false

-- SBG9:0 Flow Sequence in Flow Mapping
#guard match parseYaml "{a: [b, c], [d, e]: f}\n" with
  | .ok _ => true
  | .error _ => false

-- SKE5:0 Anchor before zero indented sequence
#guard match parseYaml "---\nseq:\n &anchor\n- a\n- b\n" with
  | .ok _ => true
  | .error _ => false

-- U3C3:0 Spec Example 6.16. “TAG” directive
#guard match parseYaml "%TAG !yaml! tag:yaml.org,2002:\n---\n!yaml!str \"foo\"\n" with
  | .ok _ => true
  | .error _ => false

-- UGM3:0 Spec Example 2.27. Invoice
#guard match parseYaml "--- !<tag:clarkevans.com,2002:invoice>\ninvoice: 34843\ndate   : 2001-01-23\nbill-to: &id001\n    given  : Chris\n    family : Dumars\n    address:\n        lines: |\n            458 Walkman Dr.\n            Suite #292\n        city    : Royal Oak\n        state   : MI\n        postal  : 48046\nship-to: *id001\nproduct:\n    - sku         : BL394D\n      quantity    : 4\n      description : Basketball\n      price       : 450.00\n    - sku         : BL4438H\n      quantity    : 1\n      description : Super Hoop\n      price       : 2392.00\ntax  : 251.42\ntotal: 4443.52\ncomments:\n    Late afternoon is best.\n    Backup contact is Nancy\n    Billsmer @ 338-4338.\n" with
  | .ok _ => true
  | .error _ => false

-- V55R:0 Aliases in Block Sequence
#guard match parseYaml "- &a a\n- &b b\n- *a\n- *b\n" with
  | .ok _ => true
  | .error _ => false

-- V9D5:0 Spec Example 8.19. Compact Block Mappings
#guard match parseYaml "- sun: yellow\n- ? earth: blue\n  : moon: white\n" with
  | .ok _ => true
  | .error _ => false

-- WZ62:0 Spec Example 7.2. Empty Content
#guard match parseYaml "{\n  foo : !!str,\n  !!str : bar,\n}\n" with
  | .ok _ => true
  | .error _ => false

-- X38W:0 Aliases in Flow Objects
#guard match parseYaml "{ &a [a, &b b]: *b, *a : [c, *b, d]}\n" with
  | .ok _ => true
  | .error _ => false

-- X8DW:0 Explicit key and value seperated by comment
#guard match parseYaml "---\n? key\n# comment\n: value\n" with
  | .ok _ => true
  | .error _ => false

-- Y2GN:0 Anchor with colon in the middle
#guard match parseYaml "---\nkey: &an:chor value\n" with
  | .ok _ => true
  | .error _ => false

-- Z9M4:0 Spec Example 6.22. Global Tag Prefix
#guard match parseYaml "%TAG !e! tag:example.com,2000:app/\n---\n- !e!foo \"bar\"\n" with
  | .ok _ => true
  | .error _ => false

-- ZH7C:0 Anchors in Mapping
#guard match parseYaml "&a a: b\nc: &d d\n" with
  | .ok _ => true
  | .error _ => false

-- ZWK4:0 Key with anchor after missing explicit mapping value
#guard match parseYaml "---\na: 1\n? b\n&anchor c: 3\n" with
  | .ok _ => true
  | .error _ => false

end Lean4Yaml.Proofs.SuiteGuards.Advanced
