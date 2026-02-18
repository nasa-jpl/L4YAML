import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Anchor
import Lean4Yaml.Parser.Tag
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Document
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Flow Completeness Verified Tests

Runtime verification tests for YAML flow collection features
(YAML 1.2.2 §7.4–§7.5).

## Categories

1. **Implicit single-pair entries** — `[key: value]` (§7.5)
2. **JSON-like key detection** — `["key":value]`, `[{k: v}:value]` (§7.4)
3. **Empty implicit keys** — `[: value]` (null key in flow sequence)
4. **Multi-line flow plain scalars** — scalars spanning lines in flow context (§7.3.3)
5. **Mixed flow sequence entries** — sequences with mixed scalar/mapping items
6. **Flow mapping with collection keys** — `{[1,2]: value}` (§7.4.2)
7. **yaml-test-suite regressions** — specific IDs: 87E4, 8KB6, 8UDB, 9MMW, L9U5, LQZ7, QF4Y, NJ66, CFD4
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser
open Tests

namespace Tests.Flow

/-! ## Helpers -/

def parseSingle (input : String) : Except String YamlValue :=
  parseYamlSingle input

def content (v : YamlValue) : Option String :=
  match v with
  | .scalar s => some s.content
  | _ => none

def isNull (v : YamlValue) : Bool :=
  match v with
  | .scalar s => s.content == "" && s.style == .plain
  | _ => false

def seqItemAt? (v : YamlValue) (idx : Nat) : Option YamlValue :=
  match v.asArray? with
  | some items => items[idx]?
  | none => none

def pairAt? (v : YamlValue) (idx : Nat) : Option (YamlValue × YamlValue) :=
  match v.asPairs? with
  | some pairs => pairs[idx]?
  | none => none

def keyAt? (v : YamlValue) (idx : Nat) : Option String :=
  match pairAt? v idx with
  | some (k, _) => content k
  | none => none

def valAt? (v : YamlValue) (idx : Nat) : Option String :=
  match pairAt? v idx with
  | some (_, v) => content v
  | none => none

def pairCount (v : YamlValue) : Nat :=
  match v.asPairs? with
  | some pairs => pairs.size
  | none => 0

def seqCount (v : YamlValue) : Nat :=
  match v.asArray? with
  | some items => items.size
  | none => 0

/-! ## 1. Implicit Single-Pair Entries (§7.5) -/

def testImplicitSinglePair (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Implicit single-pair entries"

  -- Plain scalar key: value in flow sequence
  match parseSingle "[ a : b ]" with
  | .ok v =>
    check state "[a : b] is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "[a : b] item is mapping" (item.isMapping)
      check state "[a : b] key" (keyAt? item 0 == some "a")
      check state "[a : b] value" (valAt? item 0 == some "b")
    | none => check state "[a : b] has item" false
  | .error e => checkM state "[a : b] parses" false e

  -- Multiple entries: plain key: value
  match parseSingle "[ one: 1, two: 2 ]" with
  | .ok v =>
    check state "[one:1, two:2] is sequence" (v.isSequence)
    check state "[one:1, two:2] count" (seqCount v == 2)
    match seqItemAt? v 0 with
    | some item =>
      check state "[one:1] key" (keyAt? item 0 == some "one")
      check state "[one:1] value" (valAt? item 0 == some "1")
    | none => check state "[one:1] has item" false
    match seqItemAt? v 1 with
    | some item =>
      check state "[two:2] key" (keyAt? item 0 == some "two")
      check state "[two:2] value" (valAt? item 0 == some "2")
    | none => check state "[two:2] has item" false
  | .error e => checkM state "[one:1, two:2] parses" false e

  -- Key with no value (null)
  match parseSingle "[ key: ]" with
  | .ok v =>
    check state "[key:] is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "[key:] item is mapping" (item.isMapping)
      check state "[key:] key" (keyAt? item 0 == some "key")
      match pairAt? item 0 with
      | some (_, val) => check state "[key:] null value" (isNull val)
      | none => check state "[key:] has pair" false
    | none => check state "[key:] has item" false
  | .error e => checkM state "[key:] parses" false e

  -- YAML separate style: `YAML : separate`
  match parseSingle "[ YAML : separate ]" with
  | .ok v =>
    check state "[YAML : separate] is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "[YAML : separate] key" (keyAt? item 0 == some "YAML")
      check state "[YAML : separate] value" (valAt? item 0 == some "separate")
    | none => check state "[YAML : separate] has item" false
  | .error e => checkM state "[YAML : separate] parses" false e

/-! ## 2. JSON-like Key Detection (§7.4) -/

def testJsonLikeKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "JSON-like key detection"

  -- Double-quoted key adjacent to `:`
  match parseSingle "[\"JSON like\":adjacent]" with
  | .ok v =>
    check state "[\"JSON like\":adjacent] is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "[\"JSON like\":adjacent] is mapping" (item.isMapping)
      check state "[\"JSON like\":adjacent] key" (keyAt? item 0 == some "JSON like")
      check state "[\"JSON like\":adjacent] value" (valAt? item 0 == some "adjacent")
    | none => check state "[\"JSON like\":adjacent] has item" false
  | .error e => checkM state "[\"JSON like\":adjacent] parses" false e

  -- Single-quoted key adjacent to `:`
  match parseSingle "['single':val]" with
  | .ok v =>
    check state "['single':val] is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "['single':val] is mapping" (item.isMapping)
      check state "['single':val] key" (keyAt? item 0 == some "single")
      check state "['single':val] value" (valAt? item 0 == some "val")
    | none => check state "['single':val] has item" false
  | .error e => checkM state "['single':val] parses" false e

  -- Double-quoted key with space before `:` in flow mapping
  match parseSingle "{\"key\" :value}" with
  | .ok v =>
    check state "{\"key\" :value} is mapping" (v.isMapping)
    check state "{\"key\" :value} key" (keyAt? v 0 == some "key")
    check state "{\"key\" :value} value" (valAt? v 0 == some "value")
  | .error e => checkM state "{\"key\" :value} parses" false e

  -- Double-quoted key adjacent in flow mapping
  match parseSingle "{\"key\":value}" with
  | .ok v =>
    check state "{\"key\":value} is mapping" (v.isMapping)
    check state "{\"key\":value} key" (keyAt? v 0 == some "key")
    check state "{\"key\":value} value" (valAt? v 0 == some "value")
  | .error e => checkM state "{\"key\":value} parses" false e

/-! ## 3. Empty Implicit Keys in Flow Sequence -/

def testEmptyImplicitKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Empty implicit keys"

  -- Empty key `: value` in flow sequence (CFD4 pattern)
  match parseSingle "[: value]" with
  | .ok v =>
    check state "[: value] is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "[: value] is mapping" (item.isMapping)
      match pairAt? item 0 with
      | some (k, val) =>
        check state "[: value] null key" (isNull k)
        check state "[: value] value" (content val == some "value")
      | none => check state "[: value] has pair" false
    | none => check state "[: value] has item" false
  | .error e => checkM state "[: value] parses" false e

  -- Empty key with null value in flow sequence
  match parseSingle "[:, a]" with
  | .ok v =>
    check state "[:, a] is sequence" (v.isSequence)
    check state "[:, a] count" (seqCount v == 2)
    match seqItemAt? v 0 with
    | some item =>
      check state "[:, a] first is mapping" (item.isMapping)
      match pairAt? item 0 with
      | some (k, val) =>
        check state "[:] null key" (isNull k)
        check state "[:] null value" (isNull val)
      | none => check state "[:] has pair" false
    | none => check state "[:, a] has first item" false
  | .error e => checkM state "[:, a] parses" false e

/-! ## 4. Multi-line Flow Plain Scalars (§7.3.3) -/

def testMultilineFlowScalars (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Multi-line flow scalars"

  -- Plain scalar continued on next line in flow mapping (NJ66/8KB6 pattern)
  match parseSingle "{\n  multi\n  line : value\n}" with
  | .ok v =>
    check state "{multi line: value} is mapping" (v.isMapping)
    check state "{multi line: value} key" (keyAt? v 0 == some "multi line")
    check state "{multi line: value} value" (valAt? v 0 == some "value")
  | .error e => checkM state "{multi line: value} parses" false e

  -- Plain scalar value continued on next line in flow mapping
  match parseSingle "{ key :\n  multi\n  line\n}" with
  | .ok v =>
    check state "{key: multi line} is mapping" (v.isMapping)
    check state "{key: multi line} key" (keyAt? v 0 == some "key")
    check state "{key: multi line} value" (valAt? v 0 == some "multi line")
  | .error e => checkM state "{key: multi line} parses" false e

  -- Plain scalar in flow sequence spanning lines
  match parseSingle "[\n  multi\n  line\n]" with
  | .ok v =>
    check state "[multi line] is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "[multi line] content" (content item == some "multi line")
    | none => check state "[multi line] has item" false
  | .error e => checkM state "[multi line] parses" false e

/-! ## 5. Mixed Flow Sequence Entries -/

def testMixedFlowSequence (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Mixed flow sequence entries"

  -- Mix of scalar items and implicit mappings (8UDB pattern)
  match parseSingle "[a, b: c, d]" with
  | .ok v =>
    check state "[a, b:c, d] is sequence" (v.isSequence)
    check state "[a, b:c, d] count" (seqCount v == 3)
    match seqItemAt? v 0 with
    | some item => check state "[a, b:c, d] first is scalar a" (content item == some "a")
    | none => check state "[a, b:c, d] has first" false
    match seqItemAt? v 1 with
    | some item =>
      check state "[a, b:c, d] second is mapping" (item.isMapping)
      check state "[a, b:c, d] second key" (keyAt? item 0 == some "b")
      check state "[a, b:c, d] second value" (valAt? item 0 == some "c")
    | none => check state "[a, b:c, d] has second" false
    match seqItemAt? v 2 with
    | some item => check state "[a, b:c, d] third is scalar d" (content item == some "d")
    | none => check state "[a, b:c, d] has third" false
  | .error e => checkM state "[a, b:c, d] parses" false e

  -- Trailing comma
  match parseSingle "[a, b: c,]" with
  | .ok v =>
    check state "[a, b:c,] is sequence" (v.isSequence)
    check state "[a, b:c,] count" (seqCount v == 2)
  | .error e => checkM state "[a, b:c,] parses" false e

/-! ## 6. Flow Mapping with Collection Keys (§7.4.2) -/

def testFlowMappingCollectionKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow mapping collection keys"

  -- Flow sequence as a mapping key
  match parseSingle "{[1, 2]: pair}" with
  | .ok v =>
    check state "{[1,2]: pair} is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "{[1,2]: pair} key is sequence" (k.isSequence)
      check state "{[1,2]: pair} value" (content val == some "pair")
    | none => check state "{[1,2]: pair} has pair" false
  | .error e => checkM state "{[1,2]: pair} parses" false e

  -- Flow mapping as a mapping key
  match parseSingle "{{a: b}: nested}" with
  | .ok v =>
    check state "{{a:b}: nested} is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "{{a:b}: nested} key is mapping" (k.isMapping)
      check state "{{a:b}: nested} value" (content val == some "nested")
    | none => check state "{{a:b}: nested} has pair" false
  | .error e => checkM state "{{a:b}: nested} parses" false e

/-! ## 7. yaml-test-suite Regressions -/

def testSuiteRegressions (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Suite regressions"

  -- 87E4: Implicit single-quoted keys in flow sequence
  match parseSingle "['implicit block key' : value]" with
  | .ok v =>
    check state "87E4 is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "87E4 item is mapping" (item.isMapping)
      check state "87E4 key" (keyAt? item 0 == some "implicit block key")
      check state "87E4 value" (valAt? item 0 == some "value")
    | none => check state "87E4 has item" false
  | .error e => checkM state "87E4 parses" false e

  -- L9U5: Implicit plain keys in flow sequence
  match parseSingle "[ a : b ]" with
  | .ok v =>
    check state "L9U5 is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "L9U5 key" (keyAt? item 0 == some "a")
      check state "L9U5 value" (valAt? item 0 == some "b")
    | none => check state "L9U5 has item" false
  | .error e => checkM state "L9U5 parses" false e

  -- LQZ7: Implicit double-quoted keys in flow sequence
  match parseSingle "[\"a\" : b]" with
  | .ok v =>
    check state "LQZ7 is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "LQZ7 key" (keyAt? item 0 == some "a")
      check state "LQZ7 value" (valAt? item 0 == some "b")
    | none => check state "LQZ7 has item" false
  | .error e => checkM state "LQZ7 parses" false e

  -- QF4Y: Single-pair flow mapping in sequence
  match parseSingle "[foo: bar]" with
  | .ok v =>
    check state "QF4Y is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "QF4Y item is mapping" (item.isMapping)
      check state "QF4Y key" (keyAt? item 0 == some "foo")
      check state "QF4Y value" (valAt? item 0 == some "bar")
    | none => check state "QF4Y has item" false
  | .error e => checkM state "QF4Y parses" false e

  -- 8UDB: Mixed flow sequence entries
  match parseSingle "[a, b: c, d]" with
  | .ok v =>
    check state "8UDB is sequence" (v.isSequence)
    check state "8UDB count" (seqCount v == 3)
  | .error e => checkM state "8UDB parses" false e

  -- 8KB6: Multi-line flow mapping key
  match parseSingle "{\n  multi\n  line : value\n}" with
  | .ok v =>
    check state "8KB6 is mapping" (v.isMapping)
    check state "8KB6 key" (keyAt? v 0 == some "multi line")
  | .error e => checkM state "8KB6 parses" false e

  -- NJ66: Multi-line flow mapping key
  match parseSingle "{\n  multi\n  line : value,\n  another : entry\n}" with
  | .ok v =>
    check state "NJ66 is mapping" (v.isMapping)
    check state "NJ66 pair count" (pairCount v == 2)
    check state "NJ66 first key" (keyAt? v 0 == some "multi line")
    check state "NJ66 second key" (keyAt? v 1 == some "another")
  | .error e => checkM state "NJ66 parses" false e

  -- CFD4: Empty implicit key in flow sequence
  match parseSingle "[: value]" with
  | .ok v =>
    check state "CFD4 is sequence" (v.isSequence)
    match seqItemAt? v 0 with
    | some item =>
      check state "CFD4 is mapping" (item.isMapping)
      match pairAt? item 0 with
      | some (k, _) => check state "CFD4 null key" (isNull k)
      | none => check state "CFD4 has pair" false
    | none => check state "CFD4 has item" false
  | .error e => checkM state "CFD4 parses" false e

/-! ## Collect All Tests -/

/-- Collect all flow test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testImplicitSinglePair state
  testJsonLikeKeys state
  testEmptyImplicitKeys state
  testMultilineFlowScalars state
  testMixedFlowSequence state
  testFlowMappingCollectionKeys state
  testSuiteRegressions state
  let results ← finish state
  return { name := "flowtests", label := "Flow Completeness Tests",
           sourceFile := "Tests/FlowTests.lean", tests := results }

end Tests.Flow
