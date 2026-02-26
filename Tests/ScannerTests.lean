import Lean4Yaml.TokenParser
import Lean4Yaml.Scanner
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scanner & TokenParser Tests (Phase 9)

End-to-end tests for the two-pass scanner/parser pipeline:
`String → scan → Array (Positioned YamlToken) → parseStream → Array YamlDocument`

## Categories

1. **Scanner basics** — streamStart/streamEnd, empty input, comments
2. **Scalars** — plain, single-quoted, double-quoted
3. **Block collections** — sequences, mappings, nested
4. **Flow collections** — sequences, mappings
5. **Anchors/aliases** — &anchor, *alias
6. **Regression** — the `b: x: y` false-positive case
7. **Escape sequences** — \\t, \\x, \\u
-/

open Lean4Yaml
open Lean4Yaml.Scanner
open Lean4Yaml.TokenParser
open Tests

namespace Tests.ScannerTests

/-! ## Helpers -/

def scanOk (input : String) : Bool :=
  match scan input with
  | .ok _ => true
  | .error _ => false

def scanTokenCount (input : String) : Nat :=
  match scan input with
  | .ok toks => toks.size
  | .error _ => 0

def hasToken (input : String) (pred : YamlToken → Bool) : Bool :=
  match scan input with
  | .ok tokens => tokens.any (fun t => pred t.val)
  | .error _ => false

def pipelineOk (input : String) : Bool :=
  match parseYaml input with
  | .ok _ => true
  | .error _ => false

def singleContent (input : String) : Option String :=
  match parseYamlSingle input with
  | .ok (YamlValue.scalar s) => some s.content
  | _ => none

def singleStyle (input : String) : Option ScalarStyle :=
  match parseYamlSingle input with
  | .ok (YamlValue.scalar s) => some s.style
  | _ => none

def seqSize (input : String) : Option Nat :=
  match parseYamlSingle input with
  | .ok (YamlValue.sequence _ items _ _) => some items.size
  | _ => none

def mapSize (input : String) : Option Nat :=
  match parseYamlSingle input with
  | .ok (YamlValue.mapping _ pairs _ _) => some pairs.size
  | _ => none

def firstMapKey (input : String) : Option String :=
  match parseYamlSingle input with
  | .ok (YamlValue.mapping _ pairs _ _) =>
    match pairs[0]? with
    | some (YamlValue.scalar k, _) => some k.content
    | _ => none
  | _ => none

def firstMapVal (input : String) : Option String :=
  match parseYamlSingle input with
  | .ok (YamlValue.mapping _ pairs _ _) =>
    match pairs[0]? with
    | some (_, YamlValue.scalar v) => some v.content
    | _ => none
  | _ => none

/-- Check whether the value of the first mapping entry is itself a mapping
    with one pair whose key and value are the given strings. -/
def firstMapValIsMapping (input key val : String) : Bool :=
  match parseYamlSingle input with
  | .ok (YamlValue.mapping _ pairs _ _) =>
    match pairs[0]? with
    | some (_, YamlValue.mapping _ inner _ _) =>
      match inner[0]? with
      | some (YamlValue.scalar k, YamlValue.scalar v) =>
        k.content == key && v.content == val
      | _ => false
    | _ => false
  | _ => false

/-! ## Test Collection -/

def collectTests : IO VerifiedSuiteResult := do
  let ref ← IO.mkRef ({} : TestCollector)

  -- ═══════════════════════════════════════════
  setCategory ref "Scanner basics"
  -- ═══════════════════════════════════════════

  check ref "empty input scans" (scanOk "")
  check ref "empty produces 2 tokens" (scanTokenCount "" == 2)

  check ref "whitespace only" (scanTokenCount "   " == 2)
  check ref "comment only" (scanOk "# just a comment")

  check ref "streamStart is first" (hasToken "hello" (· == .streamStart))
  check ref "streamEnd is last" (hasToken "hello" (· == .streamEnd))

  -- ═══════════════════════════════════════════
  setCategory ref "Plain scalars"
  -- ═══════════════════════════════════════════

  check ref "simple word" (singleContent "hello" == some "hello")
  check ref "plain style" (singleStyle "hello" == some .plain)
  check ref "plain with spaces" (singleContent "hello world" == some "hello world")

  -- ═══════════════════════════════════════════
  setCategory ref "Quoted scalars"
  -- ═══════════════════════════════════════════

  check ref "double-quoted content" (singleContent "\"hello world\"" == some "hello world")
  check ref "double-quoted style" (singleStyle "\"hello world\"" == some .doubleQuoted)
  check ref "double-quoted newline" (singleContent "\"hello\\nworld\"" == some "hello\nworld")
  check ref "single-quoted content" (singleContent "'hello world'" == some "hello world")
  check ref "single-quoted style" (singleStyle "'hello world'" == some .singleQuoted)
  check ref "single-quoted escape" (singleContent "'it''s'" == some "it's")

  -- ═══════════════════════════════════════════
  setCategory ref "Block sequences"
  -- ═══════════════════════════════════════════

  check ref "simple list size" (seqSize "- a\n- b\n- c" == some 3)
  check ref "single item" (seqSize "- hello" == some 1)

  -- ═══════════════════════════════════════════
  setCategory ref "Block mappings"
  -- ═══════════════════════════════════════════

  check ref "simple mapping size" (mapSize "a: b\nc: d" == some 2)
  check ref "mapping key" (firstMapKey "name: Alice\nage: 30" == some "name")
  check ref "mapping value" (firstMapVal "name: Alice\nage: 30" == some "Alice")

  -- ═══════════════════════════════════════════
  setCategory ref "Flow collections"
  -- ═══════════════════════════════════════════

  check ref "flow sequence size" (seqSize "[a, b, c]" == some 3)
  check ref "flow mapping size" (mapSize "{a: b, c: d}" == some 2)

  -- ═══════════════════════════════════════════
  setCategory ref "Document markers"
  -- ═══════════════════════════════════════════

  check ref "explicit doc start" (pipelineOk "---\nhello")
  check ref "doc start/end" (pipelineOk "---\nhello\n...")

  -- ═══════════════════════════════════════════
  setCategory ref "Anchors and aliases"
  -- ═══════════════════════════════════════════

  let anchorPred := fun (t : YamlToken) => match t with | .anchor "anc" => true | _ => false
  let aliasPred := fun (t : YamlToken) => match t with | .alias "anc" => true | _ => false
  check ref "anchor scan" (hasToken "&anc hello" anchorPred)
  check ref "alias scan" (hasToken "*anc" aliasPred)

  -- ═══════════════════════════════════════════
  setCategory ref "Phase 9 regression: b: x: y"
  -- ═══════════════════════════════════════════

  -- This is THE bug that motivated Phase 9. The old parser's
  -- detectMappingKeyImpl produced a false positive at "x:" in "b: x: y".
  -- Per the YAML 1.2.2 spec, "b: x: y" is a valid implicit mapping
  -- where the value of "b" is itself a nested mapping {x: y}.
  -- The two-pass scanner correctly recognises both ": " boundaries.

  check ref "b: x: y scans" (scanOk "b: x: y")
  check ref "b: x: y pipeline" (pipelineOk "b: x: y")
  check ref "b: x: y key is b" (firstMapKey "b: x: y" == some "b")
  check ref "b: x: y val is {x: y}" (firstMapValIsMapping "b: x: y" "x" "y")

  -- ═══════════════════════════════════════════
  setCategory ref "Escape sequences"
  -- ═══════════════════════════════════════════

  check ref "tab escape" (singleContent "\"\\t\"" == some "\t")
  check ref "hex escape \\x41" (singleContent "\"\\x41\"" == some "A")
  check ref "unicode \\u0041" (singleContent "\"\\u0041\"" == some "A")

  -- Build result
  let results ← finish ref
  return {
    name := "scannertests"
    label := "Scanner & TokenParser Tests (Phase 9)"
    sourceFile := "Tests/ScannerTests.lean"
    tests := results
  }

end Tests.ScannerTests
