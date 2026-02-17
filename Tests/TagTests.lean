import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Tag
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
# Tag Verified Tests

Runtime verification tests for YAML tag support
(YAML 1.2.2 §6.9.2 / §6.8.1 / §6.8.2).

## Categories

1. **Tag prefix parsing** — all tag forms (`!`, `!!`, `!<>`, `!handle!`)
2. **Block tags** — tags on block scalars, sequences, mappings
3. **Flow tags** — tags on flow collections and scalars
4. **Tag + anchor ordering** — `!tag &anchor value` and `&anchor !tag value`
5. **Mapping key tags** — tags on block mapping keys
6. **withTag helper** — unit tests for `YamlValue.withTag`
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser
open Tests

namespace Tests.Tag

/-! ## Helpers -/

def runParser {α : Type} (p : YamlParser α) (input : String) : Except String α :=
  let stream := YamlStream.ofString input
  match Parser.run p stream with
  | .ok _ v => .ok v
  | .error _ err => .error (toString err)

def parseSingle (input : String) : Except String YamlValue :=
  parseYamlSingle input

/-- Check if a YamlValue has a specific tag -/
def hasTag (v : YamlValue) (tag : String) : Bool :=
  match v with
  | .scalar s => s.tag == some tag
  | .sequence _ _ t => t == some tag
  | .mapping _ _ t => t == some tag

/-- Extract the tag from a YamlValue -/
def getTag (v : YamlValue) : Option String :=
  match v with
  | .scalar s => s.tag
  | .sequence _ _ t => t
  | .mapping _ _ t => t

/-- Extract scalar content regardless of tag -/
def content (v : YamlValue) : Option String :=
  match v with
  | .scalar s => some s.content
  | _ => none

/-! ## 1. Tag Prefix Parsing -/

def testTagPrefixParsing (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Tag prefix parsing"

  -- Non-specific tag
  match runParser parseTagPrefix "! " with
  | .ok t => check state "non-specific tag" (t == "!")
  | .error e => checkM state "non-specific tag" false e

  -- Secondary handle: !!str
  match runParser parseTagPrefix "!!str " with
  | .ok t => check state "secondary handle !!str" (t == "!!str")
  | .error e => checkM state "secondary handle !!str" false e

  -- Secondary handle: !!int
  match runParser parseTagPrefix "!!int " with
  | .ok t => check state "secondary handle !!int" (t == "!!int")
  | .error e => checkM state "secondary handle !!int" false e

  -- Secondary handle: !!map
  match runParser parseTagPrefix "!!map " with
  | .ok t => check state "secondary handle !!map" (t == "!!map")
  | .error e => checkM state "secondary handle !!map" false e

  -- Secondary handle: !!seq
  match runParser parseTagPrefix "!!seq " with
  | .ok t => check state "secondary handle !!seq" (t == "!!seq")
  | .error e => checkM state "secondary handle !!seq" false e

  -- Primary local tag: !local
  match runParser parseTagPrefix "!local " with
  | .ok t => check state "primary local tag !local" (t == "!local")
  | .error e => checkM state "primary local tag !local" false e

  -- Verbatim tag
  match runParser parseTagPrefix "!<tag:yaml.org,2002:str> " with
  | .ok t => check state "verbatim tag" (t == "!<tag:yaml.org,2002:str>")
  | .error e => checkM state "verbatim tag" false e

  -- Named handle tag: !e!tag
  match runParser parseTagPrefix "!e!tag " with
  | .ok t => check state "named handle !e!tag" (t == "!e!tag")
  | .error e => checkM state "named handle !e!tag" false e

/-! ## 2. Block Tags -/

def testBlockTags (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Block tags"

  -- Tag on plain scalar
  match parseSingle "!!str hello" with
  | .ok v =>
    check state "!!str on plain scalar parses" (content v == some "hello")
    check state "!!str tag present" (hasTag v "!!str")
  | .error e => checkM state "!!str on plain scalar parses" false e

  -- Tag on double-quoted scalar
  match parseSingle "!!str \"hello\"" with
  | .ok v =>
    check state "!!str on dquoted scalar" (content v == some "hello")
    check state "!!str tag on dquoted" (hasTag v "!!str")
  | .error e => checkM state "!!str on dquoted scalar" false e

  -- Tag on single-quoted scalar
  match parseSingle "!!str 'hello'" with
  | .ok v =>
    check state "!!str on squoted scalar" (content v == some "hello")
    check state "!!str tag on squoted" (hasTag v "!!str")
  | .error e => checkM state "!!str on squoted scalar" false e

  -- Tag on block sequence
  match parseSingle "!!seq\n- a\n- b" with
  | .ok v =>
    check state "!!seq on block sequence" (v.isSequence)
    check state "!!seq tag present" (hasTag v "!!seq")
  | .error e => checkM state "!!seq on block sequence" false e

  -- Tag on block mapping
  match parseSingle "!!map\na: 1\nb: 2" with
  | .ok v =>
    check state "!!map on block mapping" (v.isMapping)
    check state "!!map tag present" (hasTag v "!!map")
  | .error e => checkM state "!!map on block mapping" false e

  -- Non-specific tag on scalar
  match parseSingle "! hello" with
  | .ok v =>
    check state "non-specific tag on scalar" (content v == some "hello")
    check state "non-specific tag value" (hasTag v "!")
  | .error e => checkM state "non-specific tag on scalar" false e

  -- Tag on value in mapping
  match parseSingle "key: !!int 42" with
  | .ok v =>
    let val := v.lookup? "key"
    match val with
    | some inner =>
      check state "tag on mapping value" (content inner == some "42")
      check state "tag on mapping value present" (hasTag inner "!!int")
    | none => check state "tag on mapping value" false
  | .error e => checkM state "tag on mapping value" false e

  -- Tag on sequence item
  match parseSingle "- !!str hello\n- !!int 42" with
  | .ok v =>
    match v.asArray? with
    | some items =>
      if h : items.size ≥ 2 then
        check state "tag on seq item 0" (hasTag items[0] "!!str")
        check state "tag on seq item 1" (hasTag items[1] "!!int")
      else
        check state "tag on seq items" false
    | none => check state "tag on seq items" false
  | .error e => checkM state "tag on sequence items" false e

/-! ## 3. Flow Tags -/

def testFlowTags (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow tags"

  -- Tag on flow sequence
  match parseSingle "!!seq [a, b]" with
  | .ok v =>
    check state "!!seq on flow sequence" (v.isSequence)
    check state "!!seq tag on flow seq" (hasTag v "!!seq")
  | .error e => checkM state "!!seq on flow sequence" false e

  -- Tag on flow mapping
  match parseSingle "!!map {a: 1}" with
  | .ok v =>
    check state "!!map on flow mapping" (v.isMapping)
    check state "!!map tag on flow map" (hasTag v "!!map")
  | .error e => checkM state "!!map on flow mapping" false e

  -- Tag on flow scalar value
  match parseSingle "{a: !!int 42}" with
  | .ok v =>
    let val := v.lookup? "a"
    match val with
    | some inner =>
      check state "tag in flow mapping value" (content inner == some "42")
      check state "tag in flow value present" (hasTag inner "!!int")
    | none => check state "tag in flow mapping value" false
  | .error e => checkM state "tag in flow mapping value" false e

/-! ## 4. Tag + Anchor Ordering -/

def testTagAnchorOrdering (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Tag + anchor ordering"

  -- Tag then anchor: `!tag &anchor value`
  match parseSingle "a: !!str &val hello\nb: *val" with
  | .ok v =>
    let aVal := v.lookup? "a"
    let bVal := v.lookup? "b"
    check state "tag-then-anchor: value correct" (aVal.bind content == some "hello")
    check state "tag-then-anchor: tag present" (aVal.map (hasTag · "!!str") == some true)
    check state "tag-then-anchor: alias resolves" (bVal.bind content == some "hello")
  | .error e => checkM state "tag-then-anchor parses" false e

  -- Anchor then tag: `&anchor !tag value`
  match parseSingle "a: &val !!str hello\nb: *val" with
  | .ok v =>
    let aVal := v.lookup? "a"
    let bVal := v.lookup? "b"
    check state "anchor-then-tag: value correct" (aVal.bind content == some "hello")
    check state "anchor-then-tag: tag present" (aVal.map (hasTag · "!!str") == some true)
    check state "anchor-then-tag: alias resolves" (bVal.bind content == some "hello")
  | .error e => checkM state "anchor-then-tag parses" false e

/-! ## 5. Mapping Key Tags -/

def testMappingKeyTags (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Mapping key tags"

  -- Tag on mapping key (key-level tag requires multi-entry mapping
  -- so the key tag is parsed inside blockMappingKey, not dispatchByChar)
  match parseSingle "a: b\n!!str key: value" with
  | .ok v =>
    match v.asPairs? with
    | some pairs =>
      if h : pairs.size ≥ 2 then
        let (k, _val) := pairs[1]
        check state "tag on mapping key" (hasTag k "!!str")
        check state "mapping key content" (content k == some "key")
      else
        check state "tag on mapping key" false
    | none => check state "tag on mapping key" false
  | .error e => checkM state "tag on mapping key" false e

/-! ## 6. withTag Helper -/

def testWithTag (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "withTag helper"

  -- withTag on scalar
  let s := YamlValue.plainScalar "hello"
  let tagged := s.withTag "!!str"
  check state "withTag scalar" (hasTag tagged "!!str")
  check state "withTag scalar content" (content tagged == some "hello")

  -- withTag on sequence
  let seq := YamlValue.sequence .block #[YamlValue.plainScalar "a"]
  let tagged := seq.withTag "!!seq"
  check state "withTag sequence" (hasTag tagged "!!seq")
  check state "withTag sequence items" (seq.asArray? == tagged.asArray?)

  -- withTag on mapping
  let m := YamlValue.mapping .block #[(YamlValue.plainScalar "k", YamlValue.plainScalar "v")]
  let tagged := m.withTag "!!map"
  check state "withTag mapping" (hasTag tagged "!!map")
  check state "withTag mapping pairs" (m.asPairs? == tagged.asPairs?)

/-! ## Collect All Tests -/

/-- Collect all tag test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testTagPrefixParsing state
  testBlockTags state
  testFlowTags state
  testTagAnchorOrdering state
  testMappingKeyTags state
  testWithTag state
  let results ← finish state
  return { name := "tagtests", label := "Tag Tests", sourceFile := "Tests/TagTests.lean", tests := results }

end Tests.Tag
