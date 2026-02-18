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
# Explicit Key Verified Tests

Runtime verification tests for YAML explicit key (`?`) support
(YAML 1.2.2 §8.2.2, https://yaml.org/spec/1.2.2/#822-block-mappings).

## Categories

1. **Basic explicit keys** — `? key\n: value` with scalar keys
2. **Missing value** — `? key` with no `:` (value is null)
3. **Next-line keys** — `?\n<key on next line>`
4. **Complex keys** — sequences and mappings as keys
5. **Explicit key + anchors** — `? &name key` and anchored entries
6. **Mixed explicit/implicit** — `? a\n: b\nimplicit: c`
7. **Comments between key and value** — `? key\n# comment\n: val`
8. **Flow explicit keys** — `{? key : value}` and bare `?`
9. **Flow sequence explicit entries** — `[? key : value]`
10. **Empty keys** — `: value` with null key in flow
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser
open Tests

namespace Tests.ExplicitKey

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

/-! ## 1. Basic Explicit Keys -/

def testBasicExplicitKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Basic explicit keys"

  -- Simple explicit key with value on next line
  match parseSingle "? a\n: b" with
  | .ok v =>
    check state "? a : b parses as mapping" (v.isMapping)
    check state "? a : b key" (keyAt? v 0 == some "a")
    check state "? a : b value" (valAt? v 0 == some "b")
  | .error e => checkM state "? a : b parses" false e

  -- Explicit key with value on same line as colon
  match parseSingle "? a\n: 1.3" with
  | .ok v =>
    check state "? a : 1.3 key" (keyAt? v 0 == some "a")
    check state "? a : 1.3 value" (valAt? v 0 == some "1.3")
  | .error e => checkM state "? a : 1.3 parses" false e

  -- Explicit key with inline value (5WE3 pattern)
  match parseSingle "? explicit key" with
  | .ok v =>
    check state "? explicit key (no colon)" (v.isMapping)
    check state "? explicit key: key content" (keyAt? v 0 == some "explicit key")
  | .error e => checkM state "? explicit key parses" false e

/-! ## 2. Missing Value (null) -/

def testMissingValue (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Missing value (null)"

  -- Single explicit key with no value
  match parseSingle "? a" with
  | .ok v =>
    check state "? a produces mapping" (v.isMapping)
    check state "? a key" (keyAt? v 0 == some "a")
    match pairAt? v 0 with
    | some (_, val) => check state "? a value is null" (isNull val)
    | none => check state "? a has pair" false
  | .error e => checkM state "? a parses" false e

  -- Consecutive explicit keys without values (7W2P pattern)
  match parseSingle "? a\n? b" with
  | .ok v =>
    check state "? a ? b key count" (pairCount v == 2)
    check state "? a ? b first key" (keyAt? v 0 == some "a")
    check state "? a ? b second key" (keyAt? v 1 == some "b")
  | .error e => checkM state "? a ? b parses" false e

/-! ## 3. Next-Line Keys -/

def testNextLineKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Next-line keys"

  -- Key on next line is a sequence (6PBE pattern)
  match parseSingle "---\n?\n- a\n- b\n:\n- c\n- d" with
  | .ok v =>
    check state "6PBE key is sequence" (match pairAt? v 0 with | some (k, _) => k.isSequence | none => false)
    check state "6PBE value is sequence" (match pairAt? v 0 with | some (_, val) => val.isSequence | none => false)
  | .error e => checkM state "6PBE parses" false e

  -- Bare ? on its own line, : on its own line
  match parseSingle "?\n: value" with
  | .ok v =>
    check state "bare ? + : value" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "bare ? key is null" (isNull k)
      check state "bare ? : value" (content val == some "value")
    | none => check state "bare ? has pair" false
  | .error e => checkM state "bare ? + : value parses" false e

/-! ## 4. Complex Keys -/

def testComplexKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Complex keys"

  -- Multi-line plain scalar key (JTV5 pattern)
  match parseSingle "? a\n  true\n: null\n  d" with
  | .ok v =>
    check state "JTV5 multiline key" (keyAt? v 0 == some "a true")
    check state "JTV5 multiline value" (valAt? v 0 == some "null d")
  | .error e => checkM state "JTV5 parses" false e

  -- Mapping as complex key (V9D5 pattern)
  match parseSingle "- sun: yellow\n- ? earth: blue\n  : moon: white" with
  | .ok v =>
    check state "V9D5 parses" (v.isSequence)
    match v.asArray? with
    | some items =>
      if h : items.size ≥ 2 then
        check state "V9D5 first item is mapping" (items[0].isMapping)
        check state "V9D5 second item is mapping" (items[1].isMapping)
      else check state "V9D5 item count" false
    | none => check state "V9D5 as array" false
  | .error e => checkM state "V9D5 parses" false e

  -- Sequence as key (M5DY pattern)
  match parseSingle "? - Detroit Tigers\n  - Chicago cubs\n:\n  - 2001-07-23" with
  | .ok v =>
    check state "M5DY key is sequence" (match pairAt? v 0 with | some (k, _) => k.isSequence | none => false)
    check state "M5DY value is sequence" (match pairAt? v 0 with | some (_, val) => val.isSequence | none => false)
  | .error e => checkM state "M5DY parses" false e

/-! ## 5. Explicit Key + Anchors -/

def testExplicitKeyAnchors (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Explicit key + anchors"

  -- Anchor on explicit key (6M2F pattern)
  match parseSingle "? &a a\n: &b b" with
  | .ok v =>
    check state "6M2F key" (keyAt? v 0 == some "a")
    check state "6M2F value" (valAt? v 0 == some "b")
  | .error e => checkM state "6M2F parses" false e

  -- Anchor on explicit key with null value (PW8X ? &d pattern)
  match parseSingle "a: 1\n? &d\nb: 2" with
  | .ok v =>
    -- Should parse ? &d as explicit key with anchor, value null
    check state "? &d produces mapping" (v.isMapping)
  | .error e => checkM state "? &d in mapping parses" false e

  -- Explicit key with anchor, colon with anchor (PW8X ? &e : &a pattern)
  match parseSingle "? &e\n: &a" with
  | .ok v =>
    check state "? &e : &a parses" (v.isMapping)
  | .error e => checkM state "? &e : &a parses" false e

/-! ## 6. Mixed Explicit/Implicit Keys -/

def testMixedKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Mixed explicit/implicit keys"

  -- Explicit key followed by implicit key (GH63 pattern)
  match parseSingle "? a\n: 1.3\nfifteen: d" with
  | .ok v =>
    check state "GH63 pair count" (pairCount v == 2)
    check state "GH63 explicit key" (keyAt? v 0 == some "a")
    check state "GH63 explicit value" (valAt? v 0 == some "1.3")
    check state "GH63 implicit key" (keyAt? v 1 == some "fifteen")
    check state "GH63 implicit value" (valAt? v 1 == some "d")
  | .error e => checkM state "GH63 parses" false e

  -- Explicit key with missing value then implicit key (ZWK4 pattern)
  match parseSingle "---\na: 1\n? b\n&anchor c: 3" with
  | .ok v =>
    check state "ZWK4 pair count" (pairCount v == 3)
    check state "ZWK4 first key" (keyAt? v 0 == some "a")
    check state "ZWK4 first value" (valAt? v 0 == some "1")
    check state "ZWK4 explicit key" (keyAt? v 1 == some "b")
    check state "ZWK4 third key" (keyAt? v 2 == some "c")
    check state "ZWK4 third value" (valAt? v 2 == some "3")
  | .error e => checkM state "ZWK4 parses" false e

/-! ## 7. Comments Between Key and Value -/

def testCommentsInExplicitKey (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Comments between key and value"

  -- Comment between ? key and : value (X8DW pattern)
  match parseSingle "---\n? key\n# comment\n: value" with
  | .ok v =>
    check state "X8DW key" (keyAt? v 0 == some "key")
    check state "X8DW value" (valAt? v 0 == some "value")
  | .error e => checkM state "X8DW parses" false e

  -- Comment after explicit key value (5WE3 pattern, first entry)
  match parseSingle "? explicit key # Empty value" with
  | .ok v =>
    check state "? key # comment" (keyAt? v 0 == some "explicit key")
  | .error e => checkM state "? key # comment parses" false e

/-! ## 8. Flow Explicit Keys -/

def testFlowExplicitKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow explicit keys"

  -- Explicit key in flow mapping (DFF7 pattern)
  match parseSingle "{\n? explicit: entry,\nimplicit: entry,\n?\n}" with
  | .ok v =>
    check state "DFF7 parses as mapping" (v.isMapping)
    check state "DFF7 pair count" (pairCount v == 3)
    check state "DFF7 explicit key" (keyAt? v 0 == some "explicit")
    check state "DFF7 explicit value" (valAt? v 0 == some "entry")
    check state "DFF7 implicit key" (keyAt? v 1 == some "implicit")
    check state "DFF7 bare ? null key" (match pairAt? v 2 with | some (k, _) => isNull k | none => false)
  | .error e => checkM state "DFF7 parses" false e

  -- Explicit key with null value in flow (FRK4 pattern)
  match parseSingle "{\n  ? foo :,\n  : bar,\n}" with
  | .ok v =>
    check state "FRK4 parses" (v.isMapping)
    check state "FRK4 pair count" (pairCount v == 2)
    check state "FRK4 first key" (keyAt? v 0 == some "foo")
    match pairAt? v 0 with
    | some (_, val) => check state "FRK4 first value is null" (isNull val)
    | none => check state "FRK4 first pair exists" false
    check state "FRK4 empty key value" (valAt? v 1 == some "bar")
  | .error e => checkM state "FRK4 parses" false e

  -- Simple explicit key in flow mapping
  match parseSingle "{? a : b}" with
  | .ok v =>
    check state "{? a : b} key" (keyAt? v 0 == some "a")
    check state "{? a : b} value" (valAt? v 0 == some "b")
  | .error e => checkM state "{? a : b} parses" false e

/-! ## 9. Flow Sequence Explicit Entries -/

def testFlowSeqExplicitEntries (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow sequence explicit entries"

  -- Explicit key in flow sequence creates single-pair mapping
  match parseSingle "[? a : b]" with
  | .ok v =>
    check state "[? a : b] is sequence" (v.isSequence)
    match v.asArray? with
    | some items =>
      if h : items.size ≥ 1 then
        check state "[? a : b] item is mapping" (items[0].isMapping)
      else check state "[? a : b] item count" false
    | none => check state "[? a : b] as array" false
  | .error e => checkM state "[? a : b] parses" false e

  -- Bare ? in flow sequence
  match parseSingle "[? ]" with
  | .ok v =>
    check state "[?] is sequence" (v.isSequence)
    match v.asArray? with
    | some items =>
      if h : items.size ≥ 1 then
        check state "[?] item is mapping" (items[0].isMapping)
      else check state "[?] item count" false
    | none => check state "[?] as array" false
  | .error e => checkM state "[?] parses" false e

/-! ## 10. Empty Keys (Flow) -/

def testEmptyKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Empty keys (flow)"

  -- Empty key with value in flow mapping
  match parseSingle "{: bar}" with
  | .ok v =>
    check state "{: bar} parses" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "{: bar} empty key" (isNull k)
      check state "{: bar} value" (content val == some "bar")
    | none => check state "{: bar} has pair" false
  | .error e => checkM state "{: bar} parses" false e

  -- Empty key with null value
  match parseSingle "{:}" with
  | .ok v =>
    check state "{:} parses" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "{:} empty key" (isNull k)
      check state "{:} null value" (isNull val)
    | none => check state "{:} has pair" false
  | .error e => checkM state "{:} parses" false e

/-! ## Collect All Tests -/

/-- Collect all explicit key test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testBasicExplicitKeys state
  testMissingValue state
  testNextLineKeys state
  testComplexKeys state
  testExplicitKeyAnchors state
  testMixedKeys state
  testCommentsInExplicitKey state
  testFlowExplicitKeys state
  testFlowSeqExplicitEntries state
  testEmptyKeys state
  let results ← finish state
  return { name := "explicittests", label := "Explicit Key Tests",
           sourceFile := "Tests/ExplicitKeyTests.lean", tests := results }

end Tests.ExplicitKey
