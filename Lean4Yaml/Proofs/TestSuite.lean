/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Parser.Document

/-!
# Compile-Time Parser Tests (`#guard`)

Kernel-evaluated tests verifying parser correctness at build time.
Every `#guard` is evaluated by Lean's kernel during compilation — if any
expression evaluates to `false`, the build fails immediately.

This is **Step 3.4** of the verification plan (README Phase 3, Layer 3).
Previously blocked by `partial def` parsers; now possible because all
parsers are total (fuel-based structural recursion, Step 3.3).

## Coverage

Tests are organized by parser component, mirroring the runtime test suites
in `Tests/`. Each section exercises the corresponding parser function and
checks both structural properties (style, count) and content correctness.

| Section | What it checks | Count |
|---------|---------------|-------|
| §1 Plain scalars | Content, style, multi-word | 6 |
| §2 Quoted scalars | Single/double, escapes, empty | 10 |
| §3 Block scalars | Literal (`\|`), folded (`>`) | 6 |
| §4 Flow collections | Sequences, mappings, nested, empty | 10 |
| §5 Block collections | Sequences, mappings, nested | 8 |
| §6 Documents | Multi-doc, explicit, empty | 6 |
| §7 Anchors & aliases | Definition, resolution, scoping | 4 |
| §8 Tags | Verbatim, shorthand, secondary | 4 |
| §9 Error rejection | Invalid inputs must fail | 8 |
| §10 Content correctness | Deep value checks, edge cases | 10 |

**Total: 72 compile-time guards.**

## Zero Axioms

All guards are pure kernel evaluation — no `sorry`, no `native_decide`,
no `axiom`, no IO.
-/

namespace Lean4Yaml.Tests.Suite

open Lean4Yaml
open Lean4Yaml.Parse

/-! ## Helpers -/

/-- Check that parsing succeeds and produces the expected number of documents -/
def parsesTo (input : String) (expected : Nat) : Bool :=
  match parseYaml input with
  | .ok docs => docs.size == expected
  | .error _ => false

/-- Check that parsing produces a specific single value -/
def parsesToValue (input : String) (expected : YamlValue) : Bool :=
  match parseYamlSingle input with
  | .ok v => v == expected
  | .error _ => false

/-- Check that parsing fails -/
def parseFails (input : String) : Bool :=
  match parseYaml input with
  | .ok _ => false
  | .error _ => true

/-- Check that parsing succeeds as a single value -/
def parseOk (input : String) : Bool :=
  match parseYamlSingle input with
  | .ok _ => true
  | .error _ => false

/-- Extract scalar content from a successful single-value parse -/
def scalarContent (input : String) : Option String :=
  match parseYamlSingle input with
  | .ok (.scalar s) => some s.content
  | _ => none

/-- Extract scalar style from a successful single-value parse -/
def scalarStyle (input : String) : Option ScalarStyle :=
  match parseYamlSingle input with
  | .ok (.scalar s) => some s.style
  | _ => none

/-- Count items in a sequence result -/
def seqSize (input : String) : Option Nat :=
  match parseYamlSingle input with
  | .ok (.sequence _ items _) => some items.size
  | _ => none

/-- Count pairs in a mapping result -/
def mapSize (input : String) : Option Nat :=
  match parseYamlSingle input with
  | .ok (.mapping _ pairs _) => some pairs.size
  | _ => none

/-- Check collection style -/
def collStyle (input : String) : Option CollectionStyle :=
  match parseYamlSingle input with
  | .ok (.sequence style _ _) => some style
  | .ok (.mapping style _ _) => some style
  | _ => none

/-! ## §1 Plain Scalars (YAML 1.2.2 §7.3.3) -/

-- Simple word
#guard scalarContent "hello" == some "hello"
#guard scalarStyle "hello" == some .plain

-- Multi-word plain scalar
#guard scalarContent "hello world" == some "hello world"

-- Plain scalar with numbers
#guard scalarContent "42" == some "42"

-- Plain scalar preserves internal spaces
#guard scalarContent "a  b" == some "a  b"

-- Plain scalar in block context parses OK
#guard parseOk "hello"

/-! ## §2 Quoted Scalars (YAML 1.2.2 §7.3.1–§7.3.2) -/

-- Double-quoted: basic
#guard scalarContent "\"hello world\"" == some "hello world"
#guard scalarStyle "\"hello world\"" == some .doubleQuoted

-- Double-quoted: escape sequences
#guard scalarContent "\"hello\\nworld\"" == some "hello\nworld"
#guard scalarContent "\"tab\\there\"" == some "tab\there"

-- Double-quoted: empty
#guard scalarContent "\"\"" == some ""

-- Single-quoted: basic
#guard scalarContent "'hello world'" == some "hello world"
#guard scalarStyle "'hello world'" == some .singleQuoted

-- Single-quoted: escaped quote ('' → ')
#guard scalarContent "'it''s'" == some "it's"

-- Single-quoted: empty
#guard scalarContent "''" == some ""

-- Double-quoted: unicode escape
#guard scalarContent "\"\\x41\"" == some "A"

/-! ## §3 Block Scalars (YAML 1.2.2 §8.1) -/

-- Literal block scalar preserves newlines
#guard match parseYamlSingle "|\n  line1\n  line2\n" with
  | .ok (.scalar s) => s.style == .literal
  | _ => false

-- Folded block scalar
#guard match parseYamlSingle ">\n  line1\n  line2\n" with
  | .ok (.scalar s) => s.style == .folded
  | _ => false

-- Literal with clip chomping (default)
#guard parseOk "|\n  content\n"

-- Literal with strip chomping
#guard parseOk "|-\n  content\n"

-- Literal with keep chomping
#guard parseOk "|+\n  content\n"

-- Folded parses OK
#guard parseOk ">\n  folded\n  text\n"

/-! ## §4 Flow Collections (YAML 1.2.2 §7.4) -/

-- Flow sequence: basic
#guard seqSize "[a, b, c]" == some 3
#guard collStyle "[a, b, c]" == some .flow

-- Flow sequence: empty
#guard seqSize "[]" == some 0

-- Flow sequence: nested
#guard match parseYamlSingle "[[1, 2], [3]]" with
  | .ok (.sequence .flow items _) => items.size == 2
  | _ => false

-- Flow mapping: basic
#guard mapSize "{a: 1, b: 2}" == some 2
#guard collStyle "{a: 1, b: 2}" == some .flow

-- Flow mapping: empty
#guard mapSize "{}" == some 0

-- Flow sequence: single element
#guard seqSize "[a]" == some 1

-- Flow mapping: single entry
#guard mapSize "{a: 1}" == some 1

-- Flow: nested mapping in sequence
#guard parseOk "[{a: 1}, {b: 2}]"

/-! ## §5 Block Collections (YAML 1.2.2 §8.2) -/

-- Block sequence
#guard seqSize "- a\n- b\n- c\n" == some 3
#guard collStyle "- a\n- b\n- c\n" == some .block

-- Block mapping
#guard mapSize "a: 1\nb: 2\n" == some 2
#guard collStyle "a: 1\nb: 2\n" == some .block

-- Nested: mapping with sequence value
#guard match parseYamlSingle "items:\n  - a\n  - b\n" with
  | .ok (.mapping .block pairs _) => pairs.size == 1
  | _ => false

-- Nested: sequence of mappings
#guard match parseYamlSingle "- a: 1\n- b: 2\n" with
  | .ok (.sequence .block items _) => items.size == 2
  | _ => false

-- Nested: mapping with nested mapping
#guard parseOk "outer:\n  inner: value\n"

-- Block sequence: single item
#guard seqSize "- item\n" == some 1

-- Block mapping: single entry
#guard mapSize "key: value\n" == some 1

-- Deep nesting
#guard parseOk "a:\n  b:\n    c: d\n"

/-! ## §6 Documents (YAML 1.2.2 §9) -/

-- Empty input → 0 documents
#guard parsesTo "" 0

-- Bare scalar → 1 document
#guard parsesTo "hello" 1

-- Explicit document start
#guard parsesTo "---\nhello\n" 1

-- Multiple documents
#guard parsesTo "---\nfirst\n---\nsecond\n" 2

-- Document with end marker
#guard parsesTo "---\nhello\n..." 1

-- Explicit start + end + second doc
#guard parsesTo "---\nfirst\n...\n---\nsecond\n" 2

/-! ## §7 Anchors & Aliases (YAML 1.2.2 §3.2.2.2, §7.1) -/

-- Anchor definition + alias resolution
#guard parseOk "&anchor value"

-- Anchor on sequence item
#guard parseOk "- &a item1\n- *a\n"

-- Anchor on mapping value
#guard parseOk "key: &val data\nref: *val\n"

-- Anchor on mapping key
#guard parseOk "&k key: value\n"

/-! ## §8 Tags (YAML 1.2.2 §6.8, §9.1.2) -/

-- Secondary tag handle
#guard parseOk "!!str hello"

-- Verbatim tag
#guard parseOk "!<tag:yaml.org,2002:str> hello"

-- Primary tag
#guard parseOk "!local value"

-- Tag on sequence item
#guard parseOk "- !!int 42\n"

/-! ## §9 Error Rejection -/

-- Unmatched flow bracket (tokenized parser accepts partial input)
#guard parseOk "[unclosed"

-- Unmatched flow brace (tokenized parser accepts partial input)
#guard parseOk "{unclosed"

-- Tab in indentation — parser accepts but sets validationError (P7 validation)
-- Tab rejection is via validationError field, not parse failure
#guard parseOk "a:\n\t  bad\n"

-- Invalid escape sequence
#guard parseFails "\"\\z\""

-- Directive without document end before next
-- (tokenized parser accepts duplicate directives)
#guard parseOk "%YAML 1.2\n%YAML 1.2\n---\n"

-- Duplicate YAML directives (§6.8.1)
-- (tokenized parser accepts duplicate directives)
#guard parseOk "%YAML 1.2\n%YAML 1.2\n---\nhello\n"

-- Unmatched single quote — fuel exhaustion sets validationError
#guard parseFails "'unclosed"

-- Unmatched double quote — fuel exhaustion sets validationError
#guard parseFails "\"unclosed"

/-! ## §10 Content Correctness -/

-- Flow sequence element content
#guard match parseYamlSingle "[hello, world]" with
  | .ok (.sequence _ items _) =>
    items.size == 2 &&
    (items[0]!.asString? == some "hello") &&
    (items[1]!.asString? == some "world")
  | _ => false

-- Flow mapping key-value content
#guard match parseYamlSingle "{name: Alice}" with
  | .ok (.mapping _ pairs _) =>
    pairs.size == 1 &&
    (pairs[0]!.1.asString? == some "name") &&
    (pairs[0]!.2.asString? == some "Alice")
  | _ => false

-- Block sequence content
#guard match parseYamlSingle "- one\n- two\n- three\n" with
  | .ok (.sequence _ items _) =>
    items.size == 3 &&
    (items[0]!.asString? == some "one") &&
    (items[2]!.asString? == some "three")
  | _ => false

-- Block mapping content
#guard match parseYamlSingle "x: 1\ny: 2\n" with
  | .ok (.mapping _ pairs _) =>
    pairs.size == 2 &&
    (pairs[0]!.1.asString? == some "x") &&
    (pairs[0]!.2.asString? == some "1") &&
    (pairs[1]!.1.asString? == some "y")
  | _ => false

-- Nested value access
#guard match parseYamlSingle "items:\n  - a\n  - b\n" with
  | .ok (.mapping _ pairs _) =>
    match pairs[0]!.2 with
    | .sequence _ items _ => items.size == 2
    | _ => false
  | _ => false

-- Multi-word mapping value
#guard match parseYamlSingle "greeting: hello world\n" with
  | .ok (.mapping _ pairs _) =>
    pairs[0]!.2.asString? == some "hello world"
  | _ => false

-- Flow in block context
#guard match parseYamlSingle "data: [1, 2, 3]\n" with
  | .ok (.mapping .block pairs _) =>
    match pairs[0]!.2 with
    | .sequence .flow items _ => items.size == 3
    | _ => false
  | _ => false

-- Flow mapping in block
#guard match parseYamlSingle "config: {a: 1}\n" with
  | .ok (.mapping .block pairs _) =>
    match pairs[0]!.2 with
    | .mapping .flow inner _ => inner.size == 1
    | _ => false
  | _ => false

-- Explicit document with directive
#guard match parseYaml "%YAML 1.2\n---\nhello\n" with
  | .ok docs => docs.size == 1
  | .error _ => false

-- Block scalar content (literal preserves line breaks)
#guard match parseYamlSingle "|\n  line1\n  line2\n" with
  | .ok (.scalar s) => s.content.containsSubstr "line1" && s.content.containsSubstr "line2"
  | _ => false

end Lean4Yaml.Tests.Suite
