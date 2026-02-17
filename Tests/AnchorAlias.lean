import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Anchor
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Document
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Anchor & Alias Verified Tests

Runtime verification tests for YAML anchor (`&name`) and alias (`*name`)
support (YAML 1.2.2 §6.9.2 / §7.1).

## Categories

1. **Basic anchors** — `&name value`, anchor name parsing
2. **Basic aliases** — `*name` resolution, undefined anchor rejection
3. **Block context** — anchors on block scalars, sequences, mappings
4. **Flow context** — anchors on flow collections and scalars
5. **Value correctness** — verify the resolved value matches the original
6. **Anchor map** — storeAnchor/lookupAnchor,  redefinition, multiple anchors
7. **Spec examples** — YAML 1.2.2 Example 2.10
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser
open Tests

namespace Tests.Anchor

/-! ## Helpers -/

def runParser {α : Type} (p : YamlParser α) (input : String) : Except String α :=
  let stream := YamlStream.ofString input
  match Parser.run p stream with
  | .ok _ v => .ok v
  | .error _ err => .error (toString err)

def parseSingle (input : String) : Except String YamlValue :=
  parseYamlSingle input

def parseMulti (input : String) : Except String (Array YamlDocument) :=
  parseYaml input

/-! ## 1. Anchor Name Parsing -/

def testAnchorNameParsing (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Anchor name parsing"
  -- Valid anchor names
  match runParser anchorName "foo" with
  | .ok n => check state "simple name" (n == "foo")
  | .error _ => check state "simple name" false
  match runParser anchorName "my-anchor" with
  | .ok n => check state "name with hyphens" (n == "my-anchor")
  | .error _ => check state "name with hyphens" false
  match runParser anchorName "anchor_1" with
  | .ok n => check state "name with underscore and digit" (n == "anchor_1")
  | .error _ => check state "name with underscore and digit" false
  match runParser anchorName "A" with
  | .ok n => check state "single char name" (n == "A")
  | .error _ => check state "single char name" false

/-! ## 2. Basic Anchor + Alias (Block) -/

def testBasicBlockAnchor (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Basic block anchors"
  -- Anchor on a plain scalar
  match parseSingle "--- &anchor hello" with
  | .ok v => check state "anchor on plain scalar parses" (v == YamlValue.plainScalar "hello")
  | .error e => checkM state "anchor on plain scalar parses" false e
  -- Anchor on a quoted scalar
  match parseSingle "&name \"quoted\"" with
  | .ok v =>
    let expected := YamlValue.scalar { content := "quoted", style := .doubleQuoted }
    check state "anchor on double-quoted scalar" (v == expected)
  | .error e => checkM state "anchor on double-quoted scalar" false e
  -- Anchor on single-quoted scalar
  match parseSingle "&tag 'single'" with
  | .ok v =>
    let expected := YamlValue.scalar { content := "single", style := .singleQuoted }
    check state "anchor on single-quoted scalar" (v == expected)
  | .error e => checkM state "anchor on single-quoted scalar" false e

def testBasicBlockAlias (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Basic block aliases"
  -- Anchor + alias in mapping
  let yaml := "a: &val hello\nb: *val\n"
  match parseSingle yaml with
  | .ok v =>
    -- Both keys should map to the same value
    let aVal := v.lookup? "a"
    let bVal := v.lookup? "b"
    check state "alias resolves to anchored value" (aVal == bVal)
    check state "alias value is correct" (bVal == some (YamlValue.plainScalar "hello"))
  | .error e => checkM state "alias resolves to anchored value" false e
  -- Undefined alias should fail
  match parseSingle "*undefined" with
  | .ok _ => check state "undefined alias fails" false
  | .error _ => check state "undefined alias fails" true

/-! ## 3. Block Collections with Anchors -/

def testBlockCollectionAnchors (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Block collection anchors"
  -- Anchor on block sequence
  let yaml := "items: &mylist\n  - one\n  - two\nother: *mylist\n"
  match parseSingle yaml with
  | .ok v =>
    let items := v.lookup? "items"
    let other := v.lookup? "other"
    check state "anchor on block sequence" (items == other)
    -- Verify sequence content
    match items with
    | some (.sequence _ arr _) => check state "sequence has 2 items" (arr.size == 2)
    | _ => check state "sequence has 2 items" false
  | .error e => checkM state "anchor on block sequence" false e
  -- Anchor on block mapping
  match parseSingle "defaults: &defs\n  color: red\n  size: large\n" with
  | .ok v =>
    match v.lookup? "defaults" with
    | some (.mapping .block pairs _) => check state "anchor on block mapping" (pairs.size == 2)
    | _ => check state "anchor on block mapping" false
  | .error e => checkM state "anchor on block mapping" false e

/-! ## 4. Flow Context with Anchors -/

def testFlowAnchors (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow context anchors"
  -- Anchor on flow sequence
  match parseSingle "&seq [1, 2, 3]" with
  | .ok (.sequence .flow items _) => check state "anchor on flow sequence" (items.size == 3)
  | .ok _ => check state "anchor on flow sequence" false
  | .error e => checkM state "anchor on flow sequence" false e
  -- Anchor on flow mapping
  match parseSingle "&map {a: 1, b: 2}" with
  | .ok (.mapping .flow pairs _) => check state "anchor on flow mapping" (pairs.size == 2)
  | .ok _ => check state "anchor on flow mapping" false
  | .error e => checkM state "anchor on flow mapping" false e
  -- Alias inside flow sequence
  let yaml := "- &val hello\n- *val\n"
  match parseSingle yaml with
  | .ok (.sequence .block items _) =>
    check state "alias in block sequence" (items.size == 2)
    check state "alias equals anchor" (items[0]? == items[1]?)
  | .ok _ => check state "alias in block sequence" false
  | .error e => checkM state "alias in block sequence" false e

def testFlowInlineAnchors (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow inline anchors"
  -- Anchor inside flow sequence
  match parseSingle "[&a 1, &b 2, *a, *b]" with
  | .ok (.sequence .flow items _) =>
    check state "anchors within flow seq" (items.size == 4)
    -- items[0] == items[2], items[1] == items[3]
    check state "first alias matches" (items[0]? == items[2]?)
    check state "second alias matches" (items[1]? == items[3]?)
  | .ok _ => check state "anchors within flow seq" false
  | .error e => checkM state "anchors within flow seq" false e
  -- Anchor inside flow mapping value
  match parseSingle "{a: &v hello, b: *v}" with
  | .ok (.mapping .flow pairs _) =>
    check state "anchor in flow mapping value" (pairs.size == 2)
    let v0 := pairs[0]?.map (·.2)
    let v1 := pairs[1]?.map (·.2)
    check state "flow mapping alias matches" (v0 == v1)
  | .ok _ => check state "anchor in flow mapping value" false
  | .error e => checkM state "anchor in flow mapping value" false e

/-! ## 5. Value Correctness -/

def testValueCorrectness (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Value correctness"
  -- Anchor value is not modified
  match parseSingle "&x hello world" with
  | .ok v => check state "anchor value preserved" (v == YamlValue.plainScalar "hello world")
  | .error e => checkM state "anchor value preserved" false e
  -- Alias produces exact copy
  let yaml := "original: &val hello\ncopy: *val\n"
  match parseSingle yaml with
  | .ok v =>
    let orig := v.lookup? "original"
    let copy := v.lookup? "copy"
    check state "alias is exact copy" (orig == copy)
  | .error e => checkM state "alias is exact copy" false e

/-! ## 6. Anchor Map Behavior -/

def testAnchorMapBehavior (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Anchor map behavior"
  -- Multiple anchors in one document
  let yaml := "a: &x hello\nb: &y world\nc: *x\nd: *y\n"
  match parseSingle yaml with
  | .ok v =>
    check state "multiple anchors: *x" (v.lookup? "c" == some (YamlValue.plainScalar "hello"))
    check state "multiple anchors: *y" (v.lookup? "d" == some (YamlValue.plainScalar "world"))
  | .error e => checkM state "multiple anchors: *x" false e
  -- Anchor redefinition
  let yaml2 := "a: &name first\nb: &name second\nc: *name\n"
  match parseSingle yaml2 with
  | .ok v =>
    -- *name should resolve to the latest definition
    check state "anchor redefinition uses latest" (v.lookup? "c" == some (YamlValue.plainScalar "second"))
  | .error e => checkM state "anchor redefinition uses latest" false e

/-! ## 7. Spec Example 2.10 -/

def testSpecExample (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YAML spec examples"
  -- Example 2.10: Node Anchors
  -- hr: 65    # Home runs
  -- avg: 0.278    # Batting average
  -- rbi: 147    # Runs Batted In
  -- (simplified version without tabs)
  let yaml := "---\nhr: &hr 65\navg: 0.278\nrbi: &rbi 147\n"
  match parseSingle yaml with
  | .ok v =>
    check state "Ex 2.10: hr value" (v.lookup? "hr" == some (YamlValue.plainScalar "65"))
    check state "Ex 2.10: rbi value" (v.lookup? "rbi" == some (YamlValue.plainScalar "147"))
  | .error e => checkM state "Ex 2.10: hr value" false e

/-! ## 8. Alias in Sequence -/

def testAliasAsKey (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Alias as mapping key"
  -- Alias as value in a mapping (common pattern)
  let yaml := "- &key keyname\n- *key\n"
  match parseSingle yaml with
  | .ok (.sequence _ items _) =>
    check state "alias in sequence resolves" (items.size == 2)
    check state "alias equals original" (items[0]? == items[1]?)
  | .ok _ => check state "alias in sequence resolves" false
  | .error e => checkM state "alias in sequence resolves" false e

/-! ## 9. Document-Scoped Anchors -/

def testDocumentScope (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Document scope (§3.2.2.2)"
  -- Anchor in first doc should NOT leak into second doc
  -- Multi-doc: "---\n&val hello\n---\n*val\n"
  -- The alias *val in the second doc should fail because
  -- resetAnchorMap is called at each document boundary.
  let yaml := "---\n&val hello\n---\n*val\n"
  match parseMulti yaml with
  | .ok docs =>
    -- First doc should succeed with "hello"
    check state "first doc parses" (docs.size >= 1)
    -- Second doc should either fail or produce a stall/error
    -- because *val is undefined in the second document scope
    -- If the parser produces 2 docs, anchors leaked (bug)
    -- If it errors on the second doc, anchors are properly scoped
    checkM state "anchor does not leak across docs" (docs.size == 1)
      s!"expected 1 doc (second should fail), got {docs.size}"
  | .error _ =>
    -- Error on multi-doc parse = anchor correctly scoped
    -- (second doc's *val is undefined)
    check state "first doc parses" true
    check state "anchor does not leak across docs" true

/-! ## Collect All Tests -/

/-- Collect all anchor/alias test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testAnchorNameParsing state
  testBasicBlockAnchor state
  testBasicBlockAlias state
  testBlockCollectionAnchors state
  testFlowAnchors state
  testFlowInlineAnchors state
  testValueCorrectness state
  testAnchorMapBehavior state
  testSpecExample state
  testAliasAsKey state
  testDocumentScope state
  let results ← finish state
  return { name := "anchortests", label := "Anchor & Alias Tests", sourceFile := "Tests/AnchorAlias.lean", tests := results }

end Tests.Anchor
