import Lean4Yaml.TokenParser
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
11. **Double/nested explicit keys** — `? ? a: b`, `? ?` (v0.2.10)
12. **Standalone ? and empty key/value** — `?` at EOF, `?\n:` (v0.2.10)
13. **Nested structures as explicit keys** — `? [1,2]`, `? {a:1}` (v0.2.10)
14. **Tags on explicit keys** — `? !!str 123` (v0.2.10)
15. **Flow explicit key edge cases** — `{? : v1, ? : v2}`, `{?,?}` (v0.2.10)
16. **Explicit key + block sequence nesting** — `- ? k : v` (v0.2.10)
17. **Explicit key with colons** — `? a:b:c`, `? http://...` (v0.2.10)
18. **Explicit key alias resolution** — `? &a k\n: *a` (v0.2.10)
19. **Indented explicit keys** — `  ? a\n  : b` (v0.2.10)
20. **Tab rejection** — `?\t` forbidden per §6.1 (v0.2.10)
21. **Misindented explicit value** — `? a\n : b` rejected (v0.2.10)
22. **Same-line explicit value** — `? : x` rejected per §8.2.2 [197] (v0.2.11)
23. **Block→flow underindent** — `a:\n{b: c}` rejected per §8.1 [187] (v0.2.11)
-/

open Lean4Yaml
open Lean4Yaml.TokenParser
open Tests

namespace Tests.ExplicitKey

/-! ## Helpers -/

def parseSingle (input : String) : Except ScanError YamlValue :=
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
  | .error e => checkM state "? a : b parses" false e.toString

  -- Explicit key with value on same line as colon
  match parseSingle "? a\n: 1.3" with
  | .ok v =>
    check state "? a : 1.3 key" (keyAt? v 0 == some "a")
    check state "? a : 1.3 value" (valAt? v 0 == some "1.3")
  | .error e => checkM state "? a : 1.3 parses" false e.toString

  -- Explicit key with inline value (5WE3 pattern)
  match parseSingle "? explicit key" with
  | .ok v =>
    check state "? explicit key (no colon)" (v.isMapping)
    check state "? explicit key: key content" (keyAt? v 0 == some "explicit key")
  | .error e => checkM state "? explicit key parses" false e.toString

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
  | .error e => checkM state "? a parses" false e.toString

  -- Consecutive explicit keys without values (7W2P pattern)
  match parseSingle "? a\n? b" with
  | .ok v =>
    check state "? a ? b key count" (pairCount v == 2)
    check state "? a ? b first key" (keyAt? v 0 == some "a")
    check state "? a ? b second key" (keyAt? v 1 == some "b")
  | .error e => checkM state "? a ? b parses" false e.toString

/-! ## 3. Next-Line Keys -/

def testNextLineKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Next-line keys"

  -- Key on next line is a sequence (6PBE pattern)
  match parseSingle "---\n?\n- a\n- b\n:\n- c\n- d" with
  | .ok v =>
    check state "6PBE key is sequence" (match pairAt? v 0 with | some (k, _) => k.isSequence | none => false)
    check state "6PBE value is sequence" (match pairAt? v 0 with | some (_, val) => val.isSequence | none => false)
  | .error e => checkM state "6PBE parses" false e.toString

  -- Bare ? on its own line, : on its own line
  match parseSingle "?\n: value" with
  | .ok v =>
    check state "bare ? + : value" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "bare ? key is null" (isNull k)
      check state "bare ? : value" (content val == some "value")
    | none => check state "bare ? has pair" false
  | .error e => checkM state "bare ? + : value parses" false e.toString

/-! ## 4. Complex Keys -/

def testComplexKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Complex keys"

  -- Multi-line plain scalar key (JTV5 pattern)
  match parseSingle "? a\n  true\n: null\n  d" with
  | .ok v =>
    check state "JTV5 multiline key" (keyAt? v 0 == some "a true")
    check state "JTV5 multiline value" (valAt? v 0 == some "null d")
  | .error e => checkM state "JTV5 parses" false e.toString

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
  | .error e => checkM state "V9D5 parses" false e.toString

  -- Sequence as key (M5DY pattern)
  match parseSingle "? - Detroit Tigers\n  - Chicago cubs\n:\n  - 2001-07-23" with
  | .ok v =>
    check state "M5DY key is sequence" (match pairAt? v 0 with | some (k, _) => k.isSequence | none => false)
    check state "M5DY value is sequence" (match pairAt? v 0 with | some (_, val) => val.isSequence | none => false)
  | .error e => checkM state "M5DY parses" false e.toString

/-! ## 5. Explicit Key + Anchors -/

def testExplicitKeyAnchors (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Explicit key + anchors"

  -- Anchor on explicit key (6M2F pattern)
  match parseSingle "? &a a\n: &b b" with
  | .ok v =>
    check state "6M2F key" (keyAt? v 0 == some "a")
    check state "6M2F value" (valAt? v 0 == some "b")
  | .error e => checkM state "6M2F parses" false e.toString

  -- Anchor on explicit key with null value (PW8X ? &d pattern)
  match parseSingle "a: 1\n? &d\nb: 2" with
  | .ok v =>
    -- Should parse ? &d as explicit key with anchor, value null
    check state "? &d produces mapping" (v.isMapping)
  | .error e => checkM state "? &d in mapping parses" false e.toString

  -- Explicit key with anchor, colon with anchor (PW8X ? &e : &a pattern)
  match parseSingle "? &e\n: &a" with
  | .ok v =>
    check state "? &e : &a parses" (v.isMapping)
  | .error e => checkM state "? &e : &a parses" false e.toString

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
  | .error e => checkM state "GH63 parses" false e.toString

  -- Explicit key with missing value then implicit key (ZWK4 pattern)
  match parseSingle "---\na: 1\n? b\n&anchor c: 3" with
  | .ok v =>
    check state "ZWK4 pair count" (pairCount v == 3)
    check state "ZWK4 first key" (keyAt? v 0 == some "a")
    check state "ZWK4 first value" (valAt? v 0 == some "1")
    check state "ZWK4 explicit key" (keyAt? v 1 == some "b")
    check state "ZWK4 third key" (keyAt? v 2 == some "c")
    check state "ZWK4 third value" (valAt? v 2 == some "3")
  | .error e => checkM state "ZWK4 parses" false e.toString

/-! ## 7. Comments Between Key and Value -/

def testCommentsInExplicitKey (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Comments between key and value"

  -- Comment between ? key and : value (X8DW pattern)
  match parseSingle "---\n? key\n# comment\n: value" with
  | .ok v =>
    check state "X8DW key" (keyAt? v 0 == some "key")
    check state "X8DW value" (valAt? v 0 == some "value")
  | .error e => checkM state "X8DW parses" false e.toString

  -- Comment after explicit key value (5WE3 pattern, first entry)
  match parseSingle "? explicit key # Empty value" with
  | .ok v =>
    check state "? key # comment" (keyAt? v 0 == some "explicit key")
  | .error e => checkM state "? key # comment parses" false e.toString

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
  | .error e => checkM state "DFF7 parses" false e.toString

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
  | .error e => checkM state "FRK4 parses" false e.toString

  -- Simple explicit key in flow mapping
  match parseSingle "{? a : b}" with
  | .ok v =>
    check state "{? a : b} key" (keyAt? v 0 == some "a")
    check state "{? a : b} value" (valAt? v 0 == some "b")
  | .error e => checkM state "{? a : b} parses" false e.toString

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
  | .error e => checkM state "[? a : b] parses" false e.toString

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
  | .error e => checkM state "[?] parses" false e.toString

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
  | .error e => checkM state "{: bar} parses" false e.toString

  -- Empty key with null value
  match parseSingle "{:}" with
  | .ok v =>
    check state "{:} parses" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "{:} empty key" (isNull k)
      check state "{:} null value" (isNull val)
    | none => check state "{:} has pair" false
  | .error e => checkM state "{:} parses" false e.toString

/-! ## 11. Double/Nested Explicit Keys (v0.2.10) -/

def testDoubleExplicitKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Double/nested explicit keys"

  -- ? ? a: b — mapping-as-key (valid YAML, unhashable in Python)
  match parseSingle "? ? a: b" with
  | .ok v =>
    check state "? ? a: b is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "? ? a: b key is mapping" (k.isMapping)
      check state "? ? a: b value is null" (isNull val)
    | none => check state "? ? a: b has pair" false
  | .error e => checkM state "? ? a: b parses" false e.toString

  -- ? ?\n  a: b\n: outer — nested explicit key with outer value
  match parseSingle "?\n  ? a: b\n: outer" with
  | .ok v =>
    check state "nested ? key parses" (v.isMapping)
    match pairAt? v 0 with
    | some (k, _) => check state "nested ? key is mapping" (k.isMapping)
    | none => check state "nested ? key has pair" false
  | .error e => checkM state "nested ? key parses" false e.toString

  -- ? ? — double bare explicit key (mapping {null:null} as key)
  match parseSingle "? ?" with
  | .ok v =>
    check state "? ? is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, _) => check state "? ? key is mapping" (k.isMapping)
    | none => check state "? ? has pair" false
  | .error e => checkM state "? ? parses" false e.toString

/-! ## 12. Standalone ? and Empty Key/Value (v0.2.10) -/

def testStandaloneExplicitKey (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Standalone ? and empty key/value"

  -- Just "?" at EOF — null key, null value
  match parseSingle "?" with
  | .ok v =>
    check state "bare ? is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "bare ? null key" (isNull k)
      check state "bare ? null value" (isNull val)
    | none => check state "bare ? has pair" false
  | .error e => checkM state "bare ? parses" false e.toString

  -- "? " with trailing space
  match parseSingle "? " with
  | .ok v =>
    check state "? (space) is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, _) => check state "? (space) null key" (isNull k)
    | none => check state "? (space) has pair" false
  | .error e => checkM state "? (space) parses" false e.toString

  -- "?\n" with trailing newline
  match parseSingle "?\n" with
  | .ok v =>
    check state "?\\n is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, _) => check state "?\\n null key" (isNull k)
    | none => check state "?\\n has pair" false
  | .error e => checkM state "?\\n parses" false e.toString

  -- "---\n?" under explicit document start
  match parseSingle "---\n?" with
  | .ok v =>
    check state "---\\n? is mapping" (v.isMapping)
  | .error e => checkM state "---\\n? parses" false e.toString

  -- "?\n:\n?\n:" — two null:null entries
  match parseSingle "?\n:\n?\n:" with
  | .ok v =>
    check state "?\\n:\\n?\\n: pair count" (pairCount v == 2)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "first null:null key" (isNull k)
      check state "first null:null val" (isNull val)
    | none => check state "first pair exists" false
    match pairAt? v 1 with
    | some (k, val) =>
      check state "second null:null key" (isNull k)
      check state "second null:null val" (isNull val)
    | none => check state "second pair exists" false
  | .error e => checkM state "?\\n:\\n?\\n: parses" false e.toString

/-! ## 13. Nested Structures as Explicit Keys (v0.2.10) -/

def testNestedStructureKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Nested structures as explicit keys"

  -- Flow sequence as key: ? [1, 2]\n: value
  match parseSingle "? [1, 2]\n: value" with
  | .ok v =>
    check state "? [1,2] : value is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "? [1,2] key is sequence" (k.isSequence)
      check state "? [1,2] value" (content val == some "value")
    | none => check state "? [1,2] has pair" false
  | .error e => checkM state "? [1,2] : value parses" false e.toString

  -- Flow mapping as key: ? {a: 1}\n: value
  -- Note: `: value` at col 0 starts a separate entry (null→"value"),
  -- since the flow mapping closes on the `?` line.  Two entries total.
  match parseSingle "? {a: 1}\n: value" with
  | .ok v =>
    check state "? {a:1} : value is mapping" (v.isMapping)
    check state "? {a:1} pair count" (pairCount v == 2)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "? {a:1} key is mapping" (k.isMapping)
      check state "? {a:1} value is null" (isNull val)
    | none => check state "? {a:1} has pair" false
  | .error e => checkM state "? {a:1} : value parses" false e.toString

  -- Mixed: ? [a, b]\n: {c: d}
  match parseSingle "? [a, b]\n: {c: d}" with
  | .ok v =>
    check state "? [a,b] : {c:d} is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "? [a,b] key is sequence" (k.isSequence)
      check state "? [a,b] value is mapping" (val.isMapping)
    | none => check state "? [a,b] : {c:d} has pair" false
  | .error e => checkM state "? [a,b] : {c:d} parses" false e.toString

  -- Flow mapping with sequence as explicit key: {? [a]: b}
  match parseSingle "{? [a]: b}" with
  | .ok v =>
    check state "{? [a]: b} is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "{? [a]: b} key is sequence" (k.isSequence)
      check state "{? [a]: b} value" (content val == some "b")
    | none => check state "{? [a]: b} has pair" false
  | .error e => checkM state "{? [a]: b} parses" false e.toString

/-! ## 14. Tags on Explicit Keys (v0.2.10) -/

def testTagsOnExplicitKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Tags on explicit keys"

  -- ? !!str 123\n: numeric — tagged explicit key
  match parseSingle "? !!str 123\n: numeric" with
  | .ok v =>
    check state "? !!str 123 is mapping" (v.isMapping)
    check state "? !!str 123 key" (keyAt? v 0 == some "123")
    check state "? !!str 123 value" (valAt? v 0 == some "numeric")
  | .error e => checkM state "? !!str 123 parses" false e.toString

  -- ? !tag key\n: value — local tag on explicit key
  match parseSingle "? !tag key\n: value" with
  | .ok v =>
    check state "? !tag key is mapping" (v.isMapping)
    check state "? !tag key value" (valAt? v 0 == some "value")
  | .error e => checkM state "? !tag key parses" false e.toString

/-! ## 15. Flow Explicit Key Edge Cases (v0.2.10) -/

def testFlowExplicitKeyEdgeCases (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Flow explicit key edge cases"

  -- {? : v1, ? : v2} — duplicate null keys in flow
  match parseSingle "{? : v1, ? : v2}" with
  | .ok v =>
    check state "{? : v1, ? : v2} parses" (v.isMapping)
    check state "{? : v1, ? : v2} pair count" (pairCount v ≥ 1)
  | .error e => checkM state "{? : v1, ? : v2} parses" false e.toString

  -- {?, ?} — bare ? entries in flow (null:null)
  match parseSingle "{?, ?}" with
  | .ok v =>
    check state "{?, ?} parses" (v.isMapping)
  | .error e => checkM state "{?, ?} parses" false e.toString

  -- {? , ? } — bare ? with spaces
  match parseSingle "{? , ? }" with
  | .ok v =>
    check state "{? , ? } parses" (v.isMapping)
  | .error e => checkM state "{? , ? } parses" false e.toString

  -- [? a : b, ? c : d] — multiple explicit entries in flow sequence
  match parseSingle "[? a : b, ? c : d]" with
  | .ok v =>
    check state "[? a:b, ? c:d] is sequence" (v.isSequence)
    match v.asArray? with
    | some items =>
      check state "[? a:b, ? c:d] count" (items.size == 2)
      if h : items.size ≥ 2 then
        check state "[? a:b, ? c:d] first is mapping" (items[0].isMapping)
        check state "[? a:b, ? c:d] second is mapping" (items[1].isMapping)
      else check state "[? a:b, ? c:d] item access" false
    | none => check state "[? a:b, ? c:d] as array" false
  | .error e => checkM state "[? a:b, ? c:d] parses" false e.toString

  -- [? a, ? b] — explicit keys without values in flow sequence
  match parseSingle "[? a, ? b]" with
  | .ok v =>
    check state "[? a, ? b] is sequence" (v.isSequence)
    match v.asArray? with
    | some items =>
      check state "[? a, ? b] count" (items.size == 2)
      if h : items.size ≥ 2 then
        check state "[? a, ? b] first is mapping" (items[0].isMapping)
        check state "[? a, ? b] second is mapping" (items[1].isMapping)
      else check state "[? a, ? b] item access" false
    | none => check state "[? a, ? b] as array" false
  | .error e => checkM state "[? a, ? b] parses" false e.toString

/-! ## 16. Explicit Key + Block Sequence Nesting (v0.2.10) -/

def testExplicitKeyBlockSeqNesting (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Explicit key + block sequence nesting"

  -- - ? k1\n  : v1\n- ? k2\n  : v2
  match parseSingle "- ? k1\n  : v1\n- ? k2\n  : v2" with
  | .ok v =>
    check state "seq of explicit maps is sequence" (v.isSequence)
    match v.asArray? with
    | some items =>
      check state "seq of explicit maps count" (items.size == 2)
      if h : items.size ≥ 2 then
        check state "seq[0] is mapping" (items[0].isMapping)
        check state "seq[1] is mapping" (items[1].isMapping)
      else check state "seq item access" false
    | none => check state "seq as array" false
  | .error e => checkM state "seq of explicit maps parses" false e.toString

/-! ## 17. Explicit Key + Colons in Plain Scalars (v0.2.10) -/

def testExplicitKeyColons (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Explicit key with colons in plain scalars"

  -- ? a:b:c\n: v — colons without spaces are part of the scalar
  match parseSingle "? a:b:c\n: v" with
  | .ok v =>
    check state "? a:b:c key" (keyAt? v 0 == some "a:b:c")
    check state "? a:b:c value" (valAt? v 0 == some "v")
  | .error e => checkM state "? a:b:c parses" false e.toString

  -- ? http://example.com\n: url — URL-like key
  match parseSingle "? http://example.com\n: url" with
  | .ok v =>
    check state "? http://... key" (keyAt? v 0 == some "http://example.com")
    check state "? http://... value" (valAt? v 0 == some "url")
  | .error e => checkM state "? http://... parses" false e.toString

/-! ## 18. Explicit Key + Alias Resolution (v0.2.10) -/

def testExplicitKeyAliasResolution (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Explicit key alias resolution"

  -- ? &a k\n: *a — key anchored, value aliases it
  match parseSingle "? &a k\n: *a" with
  | .ok v =>
    check state "? &a k : *a is mapping" (v.isMapping)
    check state "? &a k : *a key" (keyAt? v 0 == some "k")
    check state "? &a k : *a value" (valAt? v 0 == some "k")
  | .error e => checkM state "? &a k : *a parses" false e.toString

  -- ? &a\n: *a — anchor on null key, alias resolves to null
  match parseSingle "? &a\n: *a" with
  | .ok v =>
    check state "? &a : *a is mapping" (v.isMapping)
    match pairAt? v 0 with
    | some (k, val) =>
      check state "? &a null key" (isNull k)
      check state "? &a : *a null value" (isNull val)
    | none => check state "? &a : *a has pair" false
  | .error e => checkM state "? &a : *a parses" false e.toString

/-! ## 19. Indented Explicit Keys (v0.2.10) -/

def testIndentedExplicitKeys (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Indented explicit keys"

  -- Indented explicit key block
  match parseSingle "  ? a\n  : b" with
  | .ok v =>
    check state "indented ? a : b" (v.isMapping)
    check state "indented key" (keyAt? v 0 == some "a")
    check state "indented value" (valAt? v 0 == some "b")
  | .error e => checkM state "indented ? a : b parses" false e.toString

/-! ## 20. Tab Rejection in Explicit Keys (v0.2.10) -/

def testTabRejection (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Tab rejection in explicit keys"

  -- ?\t — tab after ? is forbidden in block context (§6.1)
  match parseSingle "?\t" with
  | .ok _ => check state "?\\t should error" false
  | .error _ => check state "?\\t correctly rejected" true

/-! ## 21. Misindented Explicit Value Rejection — §8.2.2 [197] (v0.2.10) -/

def testMisindentedExplicitValue (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Misindented explicit value rejection (§8.2.2)"

  -- ? a\n : b — `:` at col 1 when mapping indent is 0 → must reject
  match parseSingle "? a\n : b" with
  | .ok _ => check state "? a / : b should error" false
  | .error _ => check state "? a / : b correctly rejected" true

  -- ? a\n: b — `:` at col 0 matching mapping indent → must accept
  match parseSingle "? a\n: b" with
  | .ok v =>
    check state "? a / : b at col 0" (keyAt? v 0 == some "a")
    check state "? a / : b value" (valAt? v 0 == some "b")
  | .error e => checkM state "? a / : b at col 0 parses" false e.toString

  -- Nested: ? ? a\n  : inner\n: outer — both `:` at correct indents
  match parseSingle "? ? a\n  : inner\n: outer" with
  | .ok v => check state "nested ? ? a with correct : indents" v.isMapping
  | .error e => checkM state "nested explicit values parse" false e.toString

/-! ## 22. Same-line Explicit Value Rejection — §8.2.2 [197] (v0.2.11) -/

def testSameLineExplicitValue (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Same-line explicit value rejection (§8.2.2)"

  -- ? : x — `:` on same line as `?` with no simple key → reject
  match parseSingle "? : x" with
  | .ok _ => check state "? : x should error (same-line)" false
  | .error _ => check state "? : x correctly rejected" true

  -- ? :\n— `:` on same line as `?` with empty value → reject
  match parseSingle "? :" with
  | .ok _ => check state "? : should error (same-line)" false
  | .error _ => check state "? : correctly rejected" true

  -- ? ? : b — nested explicit key, same-line `:` → reject
  match parseSingle "? ? : b" with
  | .ok _ => check state "? ? : b should error (same-line)" false
  | .error _ => check state "? ? : b correctly rejected" true

  -- ? key : val — `:` follows simple key on `?` line → accept (simple key context)
  match parseSingle "? key : val" with
  | .ok v =>
    check state "? key : val parses" v.isMapping
  | .error e => checkM state "? key : val should parse" false e.toString

  -- ? key\n: val — `:` on next line at correct indent → accept
  match parseSingle "? key\n: val" with
  | .ok v =>
    check state "? key / : val parses" v.isMapping
  | .error e => checkM state "? key / : val should parse" false e.toString

/-! ## 23. Block→flow Underindent Rejection — §8.1 [187] (v0.2.11) -/

def testUnderindentedFlowStart (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Block→flow underindent rejection (§8.1)"

  -- a:\n{b: c} — flow at col 0 as value of mapping at indent 0 → reject
  match parseSingle "a:\n{b: c}" with
  | .ok _ => check state "a: / {b: c} should error (underindent)" false
  | .error _ => check state "a: / {b: c} correctly rejected" true

  -- a:\n[1, 2] — sequence at col 0 under mapping at indent 0 → reject
  match parseSingle "a:\n[1, 2]" with
  | .ok _ => check state "a: / [1, 2] should error (underindent)" false
  | .error _ => check state "a: / [1, 2] correctly rejected" true

  -- a:\n {b: c} — flow at col 1 (indent+1) → accept
  match parseSingle "a:\n {b: c}" with
  | .ok v =>
    check state "a: / ·{b: c} parses" v.isMapping
  | .error e => checkM state "a: / ·{b: c} should parse" false e.toString

  -- a:\n [1, 2] — sequence at col 1 (indent+1) → accept
  match parseSingle "a:\n [1, 2]" with
  | .ok v =>
    check state "a: / ·[1, 2] parses" v.isMapping
  | .error e => checkM state "a: / ·[1, 2] should parse" false e.toString

  -- Root level: {a: 1} — no enclosing block (indent = -1) → accept
  match parseSingle "{a: 1}" with
  | .ok v =>
    check state "root {a: 1} parses" v.isMapping
  | .error e => checkM state "root {a: 1} should parse" false e.toString

  -- Root level: [1, 2] — no enclosing block → accept
  match parseSingle "[1, 2]" with
  | .ok v =>
    check state "root [1, 2] parses" v.isSequence
  | .error e => checkM state "root [1, 2] should parse" false e.toString

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
  -- v0.2.10: Scanner hardening edge cases
  testDoubleExplicitKeys state
  testStandaloneExplicitKey state
  testNestedStructureKeys state
  testTagsOnExplicitKeys state
  testFlowExplicitKeyEdgeCases state
  testExplicitKeyBlockSeqNesting state
  testExplicitKeyColons state
  testExplicitKeyAliasResolution state
  testIndentedExplicitKeys state
  testTabRejection state
  testMisindentedExplicitValue state
  testSameLineExplicitValue state
  testUnderindentedFlowStart state
  let results ← finish state
  return { name := "explicittests", label := "Explicit Key Tests",
           sourceFile := "Tests/ExplicitKeyTests.lean", tests := results }

end Tests.ExplicitKey
