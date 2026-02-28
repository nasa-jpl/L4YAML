import Lean4Yaml
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-- Check whether `s` contains `sub` as a substring. -/
private def _root_.String.containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-!
# Raw Parse / Compose Smoke Tests

Verifies the YAML 1.2.2 §3.1 processing model:
- **Parse** (`parseYamlRaw` / `parseYamlSingleRaw`): produces a serialization
  tree with `.alias name` nodes and `anchor` fields preserved.
- **Compose** (`YamlDocument.compose`): resolves aliases and strips anchors,
  producing a clean representation graph.

These tests ensure that the two layers are correctly separated and that
the composed output matches the legacy `parseYaml` / `parseYamlSingle`.

## Categories

1. Raw parse preserves aliases
2. Raw parse preserves anchor fields
3. Raw parse captures anchor map
4. Compose resolves aliases
5. Compose strips anchors
6. Raw → dump preserves anchors/aliases
7. Compose → dump produces clean output
8. Multi-document anchor scoping
-/

open Lean4Yaml
open Lean4Yaml.TokenParser
open Tests

namespace Tests.RawParse

/-! ## Helpers -/

/-- Check whether a `YamlValue` tree contains any `.alias` node. -/
private def hasAlias : YamlValue → Bool
  | .alias _ => true
  | .sequence _ items _ _ => hasList items.toList
  | .mapping _ pairs _ _ => hasPairs pairs.toList
  | .scalar _ => false
where
  hasList : List YamlValue → Bool
    | [] => false
    | v :: vs => hasAlias v || hasList vs
  hasPairs : List (YamlValue × YamlValue) → Bool
    | [] => false
    | (k, v) :: rest => hasAlias k || hasAlias v || hasPairs rest

/-- Check whether a `YamlValue` tree has any non-`none` anchor field. -/
private def hasAnchorField : YamlValue → Bool
  | .scalar s => s.anchor.isSome
  | .sequence _ items _ a => a.isSome || hasFieldList items.toList
  | .mapping _ pairs _ a => a.isSome || hasFieldPairs pairs.toList
  | .alias _ => false
where
  hasFieldList : List YamlValue → Bool
    | [] => false
    | v :: vs => hasAnchorField v || hasFieldList vs
  hasFieldPairs : List (YamlValue × YamlValue) → Bool
    | [] => false
    | (k, v) :: rest => hasAnchorField k || hasAnchorField v || hasFieldPairs rest

/-- Extract the alias name if the value is `.alias`. -/
private def aliasName? : YamlValue → Option String
  | .alias n => some n
  | _ => none

/-- Extract the anchor name from a scalar. -/
private def scalarAnchor? : YamlValue → Option String
  | .scalar s => s.anchor
  | _ => none

/-- Extract anchor from a sequence or mapping. -/
private def collectionAnchor? : YamlValue → Option String
  | .sequence _ _ _ a => a
  | .mapping _ _ _ a => a
  | _ => none

/-! ## 1. Raw Parse Preserves Aliases -/

def testRawPreservesAliases (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Raw parse preserves aliases"
  -- Simple scalar alias
  let yaml := "a: &val hello\nb: *val\n"
  match parseYamlSingleRaw yaml with
  | .ok doc =>
    let bVal := doc.value.lookup? "b"
    match bVal with
    | some v =>
      check state "alias node preserved in raw" (v.isAlias)
      check state "alias name is 'val'" (aliasName? v == some "val")
    | none => check state "alias node preserved in raw" false
  | .error e => checkM state "alias node preserved in raw" false e

  -- Alias inside sequence
  let yaml2 := "- &item hello\n- *item\n"
  match parseYamlSingleRaw yaml2 with
  | .ok doc =>
    match doc.value.asArray? with
    | some items =>
      check state "alias in sequence preserved" (items.size == 2)
      check state "second element is alias" (items[1]?.map (·.isAlias) == some true)
    | none => check state "alias in sequence preserved" false
  | .error e => checkM state "alias in sequence preserved" false e

  -- Flow context alias
  let yaml3 := "{a: &x 1, b: *x}"
  match parseYamlSingleRaw yaml3 with
  | .ok doc =>
    let bVal := doc.value.lookup? "b"
    check state "flow alias preserved" (bVal.map (·.isAlias) == some true)
  | .error e => checkM state "flow alias preserved" false e

/-! ## 2. Raw Parse Preserves Anchor Fields -/

def testRawPreservesAnchors (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Raw parse preserves anchor fields"
  -- Anchor on plain scalar
  let yaml := "--- &myanchor hello"
  match parseYamlSingleRaw yaml with
  | .ok doc =>
    check state "scalar anchor field set" (scalarAnchor? doc.value == some "myanchor")
  | .error e => checkM state "scalar anchor field set" false e

  -- Anchor on block sequence
  let yaml2 := "items: &mylist\n  - one\n  - two\n"
  match parseYamlSingleRaw yaml2 with
  | .ok doc =>
    match doc.value.lookup? "items" with
    | some v => check state "sequence anchor field set" (collectionAnchor? v == some "mylist")
    | none => check state "sequence anchor field set" false
  | .error e => checkM state "sequence anchor field set" false e

  -- Anchor on flow mapping
  let yaml3 := "&m {a: 1, b: 2}"
  match parseYamlSingleRaw yaml3 with
  | .ok doc =>
    check state "flow mapping anchor field set" (collectionAnchor? doc.value == some "m")
  | .error e => checkM state "flow mapping anchor field set" false e

/-! ## 3. Raw Parse Captures Anchor Map -/

def testRawCapturesAnchorMap (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Raw parse captures anchor map"
  -- Single anchor
  let yaml := "&anchor hello"
  match parseYamlSingleRaw yaml with
  | .ok doc =>
    check state "anchor map non-empty" (doc.anchors.size > 0)
    let found := doc.anchors.findSome? (fun (n, _) => if n == "anchor" then some true else none)
    check state "anchor map has 'anchor'" (found == some true)
  | .error e => checkM state "anchor map non-empty" false e

  -- Multiple anchors
  let yaml2 := "a: &x hello\nb: &y world\nc: *x\nd: *y\n"
  match parseYamlSingleRaw yaml2 with
  | .ok doc =>
    check state "anchor map has 2+ entries" (doc.anchors.size >= 2)
    let hasX := doc.anchors.any (fun (n, _) => n == "x")
    let hasY := doc.anchors.any (fun (n, _) => n == "y")
    check state "anchor map has 'x'" hasX
    check state "anchor map has 'y'" hasY
  | .error e => checkM state "anchor map has 2+ entries" false e

  -- Anchor map values are resolved (no nested aliases)
  let yaml3 := "a: &a hello\nb: &b [*a, world]\nc: *b\n"
  match parseYamlSingleRaw yaml3 with
  | .ok doc =>
    -- The stored value for 'b' should have *a resolved to "hello"
    match doc.anchors.findSome? (fun (n, v) => if n == "b" then some v else none) with
    | some bVal =>
      check state "anchor map value has no aliases" (!hasAlias bVal)
    | none => check state "anchor map value has no aliases" false
  | .error e => checkM state "anchor map value has no aliases" false e

/-! ## 4. Compose Resolves Aliases -/

def testComposeResolvesAliases (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Compose resolves aliases"
  -- Basic alias resolution
  let yaml := "a: &val hello\nb: *val\n"
  match parseYamlSingleRaw yaml with
  | .ok rawDoc =>
    let composed := rawDoc.compose
    check state "composed has no aliases" (!hasAlias composed.value)
    let bVal := composed.value.lookup? "b"
    check state "alias resolved to value" (bVal == some (YamlValue.plainScalar "hello"))
  | .error e => checkM state "composed has no aliases" false e

  -- Composed matches parseYamlSingle
  match parseYamlSingleRaw yaml, parseYamlSingle yaml with
  | .ok rawDoc, .ok composed =>
    check state "compose matches parseYamlSingle" (rawDoc.compose.value == composed)
  | _, _ => check state "compose matches parseYamlSingle" false

/-! ## 5. Compose Strips Anchors -/

def testComposeStripsAnchors (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Compose strips anchors"
  let yaml := "&top\na: &x hello\nb: &y [1, 2]\nc: *x\n"
  match parseYamlSingleRaw yaml with
  | .ok rawDoc =>
    -- Raw should have anchors
    check state "raw tree has anchor fields" (hasAnchorField rawDoc.value)
    -- Composed should have none
    let composed := rawDoc.compose
    check state "composed tree has no anchor fields" (!hasAnchorField composed.value)
    check state "composed anchor map is empty" (composed.anchors.size == 0)
  | .error e => checkM state "raw tree has anchor fields" false e

/-! ## 6. Raw → Dump Preserves Anchors/Aliases -/

def testRawDumpPreserves (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Raw dump preserves anchors/aliases"
  -- Dump the raw serialization tree — should contain &/# markers
  let yaml := "a: &val hello\nb: *val\n"
  match parseYamlSingleRaw yaml with
  | .ok doc =>
    let dumped := Dump.dump doc.value
    check state "dump contains &val" (dumped.containsSubstr "&val")
    check state "dump contains *val" (dumped.containsSubstr "*val")
  | .error e => checkM state "dump contains &val" false e

  -- Sequence with anchor
  let yaml2 := "&seq\n- one\n- two\n"
  match parseYamlSingleRaw yaml2 with
  | .ok doc =>
    let dumped := Dump.dump doc.value
    check state "dump contains &seq" (dumped.containsSubstr "&seq")
  | .error e => checkM state "dump contains &seq" false e

/-! ## 7. Compose → Dump Produces Clean Output -/

def testComposedDumpClean (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Composed dump is clean"
  let yaml := "a: &val hello\nb: *val\n"
  match parseYamlSingleRaw yaml with
  | .ok doc =>
    let composed := doc.compose
    let dumped := Dump.dump composed.value
    check state "composed dump has no &" (!dumped.containsSubstr "&val")
    check state "composed dump has no *" (!dumped.containsSubstr "*val")
    -- Both a and b should have the same value
    check state "composed dump has 'hello' twice"
      ((dumped.splitOn "hello").length == 3)  -- "a: hello\nb: hello\n" splits to 3 parts
  | .error e => checkM state "composed dump has no &" false e

/-! ## 8. Multi-Document Anchor Scoping -/

def testMultiDocScoping (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Multi-doc anchor scoping (raw)"
  -- Each document should have its own anchor map
  let yaml := "---\n&a hello\n---\n&a world\n"
  match parseYamlRaw yaml with
  | .ok docs =>
    check state "two documents parsed" (docs.size == 2)
    if docs.size == 2 then
      -- Each doc should have 'a' in its own anchor map
      let anchors0 := docs[0]!.anchors
      let anchors1 := docs[1]!.anchors
      let a0 := anchors0.findSome? (fun (n, v) => if n == "a" then some v else none)
      let a1 := anchors1.findSome? (fun (n, v) => if n == "a" then some v else none)
      check state "doc0 anchor 'a' = hello"
        (a0 == some (YamlValue.plainScalar "hello"))
      check state "doc1 anchor 'a' = world"
        (a1 == some (YamlValue.plainScalar "world"))
    else
      check state "doc0 anchor 'a' = hello" false
  | .error e => checkM state "two documents parsed" false e

/-! ## Collect All Tests -/

/-- Collect all raw parse / compose test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testRawPreservesAliases state
  testRawPreservesAnchors state
  testRawCapturesAnchorMap state
  testComposeResolvesAliases state
  testComposeStripsAnchors state
  testRawDumpPreserves state
  testComposedDumpClean state
  testMultiDocScoping state
  let results ← finish state
  return {
    name := "rawparsetests"
    label := "Raw Parse / Compose Tests"
    sourceFile := "Tests/RawParseTests.lean"
    tests := results
  }

end Tests.RawParse
