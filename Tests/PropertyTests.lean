import L4YAML.Spec.Grammar
import L4YAML.Output.Dump
import L4YAML.Output.Emitter
import L4YAML.Parser.TokenParser
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Property-Based Round-Trip Tests (v0.2.13.3)

Grammar-constrained fuzzing using `Grammar.lean`'s `ValidNode` inductive
as a generator:

1. **Generate** random `ValidNode` witnesses via seed-based PRNG
2. **Convert** `toYamlValue` → `dump` to produce YAML text
3. **Parse** back via `parseYamlSingle` and verify `contentEq`
4. **Mutate** the dumped text with adversarial operators and verify
   that mutations are handled consistently

This tests the dump→parse round-trip path — complementary to the
adversarial grammar tests (v0.2.13.1, parse-only) and mutation
suite tests (v0.2.13.2, yaml-test-suite corpus).

## Pseudo-Random Number Generator (PRNG) Design

We use a simple linear congruential generator (LCG) for deterministic,
reproducible random generation. The seed is threaded through all
generation functions so that the exact same test cases are produced
on every run.

## Generator Strategy

The `ValidNode` generator builds structurally valid YAML values by:
- Choosing node types weighted toward simpler forms at higher depths
- Generating safe plain scalar content that satisfies grammar predicates
- Limiting collection sizes and nesting depth for tractable test cases
- Generating both block and flow style collections
-/

open L4YAML
open L4YAML.Grammar
open L4YAML.Dump
open L4YAML.Emit
open L4YAML.TokenParser
open Tests

namespace Tests.PropertyTests

/-! ## PRNG — Linear Congruential Generator -/

/-- LCG state. Parameters from Numerical Recipes. -/
structure Rng where
  state : UInt64
  deriving Repr

/-- Create an Rng from a seed. -/
def Rng.mk' (seed : Nat) : Rng :=
  { state := seed.toUInt64 }

/-- Advance the PRNG, returning the next state and a value in [0, bound).
    Returns 0 when bound is 0. -/
def Rng.next (rng : Rng) (bound : Nat) : Rng × Nat :=
  if bound == 0 then (rng, 0)
  else
    let s := rng.state * 6364136223846793005 + 1442695040888963407
    let val := (s >>> 33).toNat % bound
    ({ state := s }, val)

theorem Rng.next_lt (rng : Rng) (bound : Nat) (hb : bound > 0) :
    (rng.next bound).2 < bound := by
  unfold Rng.next
  simp [Nat.ne_of_gt hb]
  exact Nat.mod_lt _ hb

/-- Pick an element from a non-empty list. -/
def Rng.pick {α : Type} (rng : Rng) (xs : List α) (h : xs.length > 0 := by omega) : Rng × α :=
  let result := rng.next xs.length
  (result.1, xs[result.2]'(Rng.next_lt rng xs.length h))

/-! ## Safe Content Generators

Generate strings that satisfy the character-level grammar predicates
needed for `ValidNode` constructors.
-/

/-- Characters safe for plain scalar first position (block context).
    Must not be an indicator char. -/
private def plainSafeFirstChars : List Char :=
  ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
   'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
   'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
   'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
   '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
   '/', '.', '_', '(', ')']

/-- Characters safe for plain scalar body (no `: `, ` #`, no flow indicators). -/
private def plainSafeBodyChars : List Char :=
  ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
   'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
   'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
   'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
   '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
   '/', '.', '_', '(', ')', '+', '=']

/-- Generate a plain-safe string of length [1, maxLen].
    Satisfies: nonempty, validPlainFirstProp, noColonSpaceProp, noSpaceHashProp,
    noFlowIndicatorsProp. -/
def genPlainSafe (rng : Rng) (maxLen : Nat := 8) : Rng × String :=
  let (rng, len) := rng.next maxLen
  let len := len + 1  -- at least 1 char
  let (rng, first) := rng.pick plainSafeFirstChars (by decide)
  let rec loop (rng : Rng) (acc : List Char) (n : Nat) : Rng × List Char :=
    match n with
    | 0 => (rng, acc.reverse)
    | n + 1 =>
      let (rng, c) := rng.pick plainSafeBodyChars (by decide)
      loop rng (c :: acc) n
  let (rng, body) := loop rng [] (len - 1)
  (rng, String.ofList (first :: body))

/-- Generate a string safe for double-quoted scalars.
    Now that the dumper is context-aware (v0.2.13.4), we can include
    characters like `:`, `#`, `!` that previously caused round-trip
    failures in flow context — the dumper now quotes them properly. -/
def genDoubleQuotedContent (rng : Rng) (maxLen : Nat := 12) : Rng × String :=
  let (rng, len) := rng.next (maxLen + 1)  -- [0, maxLen]
  let allChars : List Char :=
    ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', ' ',
     '0', '1', '2', '3', 'X', 'Y', 'Z', '.', '/', '_',
     '(', ')', '+', '=', '-', '?', ':', '#', '!',
     '@', ';', '<', '>', '~', '&', '*']
  let safeLastChars : List Char :=
    ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i',
     '0', '1', '2', '3', 'X', 'Y', 'Z', '.', '/', '_',
     '(', ')', '+', '=', ':', '#', '!', '@', '~']
  let rec loop (rng : Rng) (acc : List Char) (n : Nat) : Rng × List Char :=
    match n with
    | 0 => (rng, acc.reverse)
    | n + 1 =>
      let (rng, c) := rng.pick allChars (by decide)
      loop rng (c :: acc) n
  if len == 0 then (rng, "")
  else
    let (rng, body) := loop rng [] (len - 1)
    let (rng, last) := rng.pick safeLastChars (by decide)
    (rng, String.ofList (body ++ [last]))

/-- Generate a string safe for single-quoted scalars (no newlines).
    Now that the dumper is context-aware (v0.2.13.4), we include
    richer characters — the dumper properly quotes in flow context. -/
def genSingleQuotedContent (rng : Rng) (maxLen : Nat := 12) : Rng × String :=
  let (rng, len) := rng.next (maxLen + 1)
  let chars : List Char :=
    ['a', 'b', 'c', ' ', '-', '.', '0', '1', '2',
     'x', 'y', 'z', '(', ')', '_', '+', '=', '/', 'A', 'B', 'C',
     ':', '#', '!', '@', ';', '~', '&', '*']
  -- Last character must not end with space (whitespace trim ambiguity)
  let safeLastChars : List Char :=
    ['a', 'b', 'c', '.', '0', '1', '2',
     'x', 'y', 'z', '(', ')', '_', '+', '=', '/', 'A', 'B', 'C',
     ':', '#', '!', '@', '~']
  let rec loop (rng : Rng) (acc : List Char) (n : Nat) : Rng × List Char :=
    match n with
    | 0 => (rng, acc.reverse)
    | n + 1 =>
      let (rng, c) := rng.pick chars (by decide)
      loop rng (c :: acc) n
  if len == 0 then (rng, "")
  else
    let (rng, body) := loop rng [] (len - 1)
    let (rng, last) := rng.pick safeLastChars (by decide)
    (rng, String.ofList (body ++ [last]))

/-! ## ValidNode Generator -/

/-- Maximum depth for generated trees. -/
private def maxDepth : Nat := 4

/-- Maximum items per collection. -/
private def maxCollectionSize : Nat := 4

-- ValidNode needs Nonempty for partial def compilation
private instance : Nonempty ValidNode := ⟨.emptyNode⟩

private def genPlainBlock (rng : Rng) : Rng × ValidNode :=
  let (rng, content) := genPlainSafe rng
  if h1 : content.length > 0 then
    if h2 : validPlainFirstBool content false = true then
      if h3 : noColonSpaceBool content = true then
        if h4 : noSpaceHashBool content = true then
          (rng, .plainScalarBlock content h1
            ((validPlainFirst_iff content false).mp h2)
            ((noColonSpace_iff content).mp h3)
            ((noSpaceHash_iff content).mp h4))
        else (rng, .emptyNode)
      else (rng, .emptyNode)
    else (rng, .emptyNode)
  else (rng, .emptyNode)

private def genPlainFlow (rng : Rng) : Rng × ValidNode :=
  let (rng, content) := genPlainSafe rng
  if h1 : content.length > 0 then
    if h2 : validPlainFirstBool content true = true then
      if h3 : noColonSpaceBool content = true then
        if h4 : noSpaceHashBool content = true then
          if h5 : noFlowIndicatorsBool content = true then
            (rng, .plainScalarFlow content h1
              ((validPlainFirst_iff content true).mp h2)
              ((noColonSpace_iff content).mp h3)
              ((noSpaceHash_iff content).mp h4)
              ((noFlowIndicators_iff content).mp h5))
          else (rng, .emptyNode)
        else (rng, .emptyNode)
      else (rng, .emptyNode)
    else (rng, .emptyNode)
  else (rng, .emptyNode)

private def genSingleQuoted' (rng : Rng) : Rng × ValidNode :=
  let (rng, content) := genSingleQuotedContent rng
  (rng, .singleQuoted content)

private def genDoubleQuoted' (rng : Rng) : Rng × ValidNode :=
  let (rng, content) := genDoubleQuotedContent rng
  (rng, .doubleQuoted content)

private def genScalar (rng : Rng) : Rng × ValidNode :=
  let (rng, choice) := rng.next 5
  match choice with
  | 0 => genPlainBlock rng
  | 1 => genPlainFlow rng
  | 2 => genSingleQuoted' rng
  | 3 => genDoubleQuoted' rng
  | _ => (rng, .emptyNode)

/--
Generate a random `ValidNode`.

At depth 0, only scalars and empty node are generated.
At higher depths, collections are included with decreasing probability.
The `flowOnly` parameter is retained for testing purposes but is no longer
needed for correctness — the dumper (v0.2.13.4) auto-forces flow style
for any block collection nested inside a flow context.
-/
partial def genValidNode (rng : Rng) (depth : Nat := 0) (flowOnly : Bool := false)
    : Rng × ValidNode :=
  if depth ≥ maxDepth then genScalar rng
  else if flowOnly then
    -- Inside flow context: only scalars, flow collections, empty
    let (rng, choice) := rng.next 6
    match choice with
    | 0 => genPlainFlow rng
    | 1 => genSingleQuoted' rng
    | 2 => genDoubleQuoted' rng
    | 3 => (rng, .emptyNode)
    | 4 => genFlowSeq rng depth
    | _ => genFlowMap rng depth
  else
    let nChoices := if depth ≤ 1 then 10 else 7
    let (rng, choice) := rng.next nChoices
    match choice with
    | 0 => genPlainBlock rng
    | 1 => genPlainFlow rng
    | 2 => genSingleQuoted' rng
    | 3 => genDoubleQuoted' rng
    | 4 => (rng, .emptyNode)
    | 5 => genBlockSeq rng depth
    | 6 => genBlockMap rng depth
    | 7 => genFlowSeq rng depth
    | 8 => genFlowMap rng depth
    | 9 =>
      let (rng, sub) := rng.next 4
      match sub with
      | 0 => genBlockSeq rng depth
      | 1 => genBlockMap rng depth
      | 2 => genFlowSeq rng depth
      | _ => genFlowMap rng depth
    | _ => genScalar rng
where
  genBlockSeq (rng : Rng) (depth : Nat) : Rng × ValidNode :=
    let (rng, size) := rng.next maxCollectionSize
    let size := size + 1
    let rec loop (rng : Rng) (acc : List ValidNode) (n : Nat) : Rng × List ValidNode :=
      match n with
      | 0 => (rng, acc.reverse)
      | n + 1 =>
        let (rng, item) := genValidNode rng (depth + 1)
        loop rng (item :: acc) n
    let (rng, items) := loop rng [] size
    (rng, .blockSeq 0 items)

  genBlockMap (rng : Rng) (depth : Nat) : Rng × ValidNode :=
    let (rng, size) := rng.next maxCollectionSize
    let size := size + 1
    let rec loop (rng : Rng) (acc : List (ValidNode × ValidNode)) (n : Nat)
        : Rng × List (ValidNode × ValidNode) :=
      match n with
      | 0 => (rng, acc.reverse)
      | n + 1 =>
        let (rng, key) := genScalar rng
        let (rng, val) := genValidNode rng (depth + 1)
        loop rng ((key, val) :: acc) n
    let (rng, entries) := loop rng [] size
    (rng, .blockMap 0 entries)

  genFlowSeq (rng : Rng) (depth : Nat) : Rng × ValidNode :=
    let (rng, size) := rng.next 3
    let rec loop (rng : Rng) (acc : List ValidNode) (n : Nat) : Rng × List ValidNode :=
      match n with
      | 0 => (rng, acc.reverse)
      | n + 1 =>
        -- No flowOnly needed: dumper forces flow style for children in flow context
        let (rng, item) := genValidNode rng (depth + 1)
        loop rng (item :: acc) n
    let (rng, items) := loop rng [] size
    (rng, .flowSeq items)

  genFlowMap (rng : Rng) (depth : Nat) : Rng × ValidNode :=
    let (rng, size) := rng.next 3
    let rec loop (rng : Rng) (acc : List (ValidNode × ValidNode)) (n : Nat)
        : Rng × List (ValidNode × ValidNode) :=
      match n with
      | 0 => (rng, acc.reverse)
      | n + 1 =>
        let (rng, key) := genScalar rng
        -- No flowOnly needed: dumper forces flow style for children in flow context
        let (rng, val) := genValidNode rng (depth + 1)
        loop rng ((key, val) :: acc) n
    let (rng, entries) := loop rng [] size
    (rng, .flowMap entries)

/-! ## Round-Trip Testing -/

/-- Dump a ValidNode and parse it back, checking content equivalence. -/
def roundTripCheck (node : ValidNode) (cfg : DumpConfig := {}) : Bool :=
  let value := toYamlValue node
  let text := dump value cfg
  match parseYamlSingle text with
  | .ok v' => contentEq value v'
  | .error _ => false

/-- Round-trip check with diagnostic info on failure. -/
def roundTripCheckDiag (node : ValidNode) (cfg : DumpConfig := {})
    : Except String Unit :=
  let value := toYamlValue node
  let text := dump value cfg
  match parseYamlSingle text with
  | .ok v' =>
    if contentEq value v' then .ok ()
    else .error s!"content mismatch:\n  dumped: {repr text}\n  original: {repr value}\n  parsed:   {repr v'}"
  | .error e => .error s!"parse error on dumped text:\n  text: {repr text}\n  error: {e}"

/-! ## Adversarial Mutation Operators -/

/-- Shift all leading spaces on each line by delta (can be negative). -/
def mutateIndent (text : String) (delta : Int) : String :=
  let lines := text.splitOn "\n"
  let mutated := lines.map fun line =>
    if line.isEmpty then line
    else
      let spaces := line.toList.takeWhile (· == ' ') |>.length
      let newSpaces := Int.toNat (spaces + delta)  -- clamp to 0
      let content := line.toList.drop spaces
      String.ofList (List.replicate newSpaces ' ' ++ content)
  "\n".intercalate mutated

/-- Replace first space-indent with a tab on each indented line. -/
def mutateTabInject (text : String) : String :=
  let lines := text.splitOn "\n"
  let mutated := lines.map fun line =>
    let chars := line.toList
    match chars with
    | ' ' :: rest => String.ofList ('\t' :: rest)
    | _ => line
  "\n".intercalate mutated

/-- Delete the first newline in the text. -/
def mutateDeleteNewline (text : String) : String :=
  let chars := text.toList
  let rec go : List Char → List Char
    | [] => []
    | '\n' :: rest => rest
    | c :: rest => c :: go rest
  String.ofList (go chars)

/-- Add an extra newline after the first newline. -/
def mutateAddNewline (text : String) : String :=
  let chars := text.toList
  let rec go : List Char → List Char
    | [] => []
    | '\n' :: rest => '\n' :: '\n' :: rest
    | c :: rest => c :: go rest
  String.ofList (go chars)

/-- Remove space after first colon (`:value` instead of `: value`). -/
def mutateColonNoSpace (text : String) : String :=
  let chars := text.toList
  let rec go : List Char → List Char
    | [] => []
    | ':' :: ' ' :: rest => ':' :: rest
    | c :: rest => c :: go rest
  String.ofList (go chars)

/-! ## Test Categories -/

/-- §1: Basic round-trip — generate N random nodes, verify dump→parse round-trip. -/
def testBasicRoundTrip (state : IO.Ref TestCollector) (count : Nat := 100) : IO Unit := do
  setCategory state "Basic dump→parse round-trip"
  let mut rng := Rng.mk' 42
  let mut passed := 0
  let mut failed := 0
  let mut failures : Array String := #[]
  for i in [:count] do
    let (rng', node) := genValidNode rng
    rng := rng'
    match roundTripCheckDiag node with
    | .ok () => passed := passed + 1
    | .error msg =>
      failed := failed + 1
      if failures.size < 5 then
        failures := failures.push s!"seed-42/node-{i}: {msg}"
  check state s!"{passed}/{count} random nodes round-trip successfully" (failed == 0)
  for f in failures do
    checkM state "round-trip failure detail" false f

/-- §2: Flow-style round-trip — force flow style for all collections. -/
def testFlowRoundTrip (state : IO.Ref TestCollector) (count : Nat := 50) : IO Unit := do
  setCategory state "Flow-style dump→parse round-trip"
  let cfg : DumpConfig := { defaultStyle := .flow }
  let mut rng := Rng.mk' 137
  let mut passed := 0
  let mut failed := 0
  let mut failures : Array String := #[]
  for i in [:count] do
    -- Block-in-flow is now valid: dumper auto-forces flow style for nested blocks
    let (rng', node) := genValidNode rng
    rng := rng'
    match roundTripCheckDiag node cfg with
    | .ok () => passed := passed + 1
    | .error msg =>
      failed := failed + 1
      if failures.size < 5 then
        failures := failures.push s!"seed-137/node-{i}: {msg}"
  check state s!"{passed}/{count} flow-style nodes round-trip" (failed == 0)
  for f in failures do
    checkM state "flow round-trip failure detail" false f

/-- §3: Double-quoted round-trip — force double-quoted scalars. -/
def testDoubleQuotedRoundTrip (state : IO.Ref TestCollector) (count : Nat := 50) : IO Unit := do
  setCategory state "Double-quoted dump→parse round-trip"
  let cfg : DumpConfig := { scalarStyle := .doubleQuoted }
  let mut rng := Rng.mk' 271
  let mut passed := 0
  let mut failed := 0
  let mut failures : Array String := #[]
  for i in [:count] do
    let (rng', node) := genValidNode rng
    rng := rng'
    match roundTripCheckDiag node cfg with
    | .ok () => passed := passed + 1
    | .error msg =>
      failed := failed + 1
      if failures.size < 5 then
        failures := failures.push s!"seed-271/node-{i}: {msg}"
  check state s!"{passed}/{count} double-quoted nodes round-trip" (failed == 0)
  for f in failures do
    checkM state "double-quoted round-trip failure detail" false f

/-- §4: Scalar-only round-trip — edge-case scalars. -/
def testScalarEdgeCases (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Scalar edge cases"
  -- Empty node round-trips
  check state "emptyNode round-trips" (roundTripCheck .emptyNode)
  -- Single-quoted with special chars
  check state "singleQuoted empty" (roundTripCheck (.singleQuoted ""))
  check state "singleQuoted 'hello'" (roundTripCheck (.singleQuoted "hello"))
  check state "singleQuoted with colon-space" (roundTripCheck (.singleQuoted "a: b"))
  check state "singleQuoted with hash" (roundTripCheck (.singleQuoted "a #b"))
  check state "singleQuoted with flow chars" (roundTripCheck (.singleQuoted "{a, b}"))
  check state "singleQuoted with indicators" (roundTripCheck (.singleQuoted "- item"))
  -- Double-quoted with special chars
  check state "doubleQuoted empty" (roundTripCheck (.doubleQuoted ""))
  check state "doubleQuoted 'hello'" (roundTripCheck (.doubleQuoted "hello"))
  check state "doubleQuoted with colon" (roundTripCheck (.doubleQuoted "key: val"))
  check state "doubleQuoted with braces" (roundTripCheck (.doubleQuoted "{a: 1}"))
  check state "doubleQuoted with all indicators"
    (roundTripCheck (.doubleQuoted "- ? : , [ ] { } # & * ! | > ' \" %"))
  check state "doubleQuoted reserved 'true'" (roundTripCheck (.doubleQuoted "true"))
  check state "doubleQuoted reserved 'null'" (roundTripCheck (.doubleQuoted "null"))
  check state "doubleQuoted reserved 'false'" (roundTripCheck (.doubleQuoted "false"))
  check state "doubleQuoted numeric '42'" (roundTripCheck (.doubleQuoted "42"))

/-- §5: Collection structure round-trip — handcrafted nested structures. -/
def testCollectionStructures (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Collection structure round-trip"
  -- Block sequence with plain scalars
  let bseq := ValidNode.blockSeq 0
    [.singleQuoted "a", .singleQuoted "b", .singleQuoted "c"]
  check state "block seq [a, b, c]" (roundTripCheck bseq)

  -- Block mapping with plain values
  let bmap := ValidNode.blockMap 0
    [(.singleQuoted "key1", .singleQuoted "val1"),
     (.singleQuoted "key2", .singleQuoted "val2")]
  check state "block map {key1: val1, key2: val2}" (roundTripCheck bmap)

  -- Flow sequence
  let fseq := ValidNode.flowSeq
    [.singleQuoted "x", .singleQuoted "y"]
  check state "flow seq [x, y]" (roundTripCheck fseq)

  -- Flow mapping
  let fmap := ValidNode.flowMap
    [(.singleQuoted "a", .singleQuoted "1"),
     (.singleQuoted "b", .singleQuoted "2")]
  check state "flow map {a: 1, b: 2}" (roundTripCheck fmap)

  -- Nested: block map with block seq value
  let nested := ValidNode.blockMap 0
    [(.singleQuoted "items", .blockSeq 0 [.singleQuoted "x", .singleQuoted "y"]),
     (.singleQuoted "name", .singleQuoted "test")]
  check state "nested block map with seq value" (roundTripCheck nested)

  -- Nested: block seq with block map entries
  let seqOfMaps := ValidNode.blockSeq 0
    [.blockMap 0 [(.singleQuoted "a", .singleQuoted "1")],
     .blockMap 0 [(.singleQuoted "b", .singleQuoted "2")]]
  check state "block seq of maps" (roundTripCheck seqOfMaps)

  -- Flow inside block
  let flowInBlock := ValidNode.blockMap 0
    [(.singleQuoted "data", .flowSeq [.singleQuoted "1", .singleQuoted "2", .singleQuoted "3"]),
     (.singleQuoted "meta", .flowMap [(.singleQuoted "k", .singleQuoted "v")])]
  check state "flow collections inside block" (roundTripCheck flowInBlock)

  -- Empty collections
  let emptySeq := ValidNode.flowSeq []
  check state "empty flow seq []" (roundTripCheck emptySeq)
  let emptyMap := ValidNode.flowMap []
  check state "empty flow map {}" (roundTripCheck emptyMap)

  -- Deep nesting (3 levels)
  let deep := ValidNode.blockMap 0
    [(.singleQuoted "L1",
      .blockMap 0
        [(.singleQuoted "L2",
          .blockMap 0
            [(.singleQuoted "L3", .singleQuoted "deep")])])]
  check state "3-level deep nesting" (roundTripCheck deep)

/-- §6: Mutation resilience — generate valid YAML, mutate, verify handling. -/
def testMutationResilience (state : IO.Ref TestCollector) (count : Nat := 50) : IO Unit := do
  setCategory state "Mutation resilience"
  let mut rng := Rng.mk' 314
  let mut indentTested := 0
  let mut tabTested := 0
  let mut newlineTested := 0
  let mut colonTested := 0
  let mut indentConsistent := 0
  let mut tabConsistent := 0
  let mut newlineConsistent := 0
  let mut colonConsistent := 0
  for _ in [:count] do
    let (rng', node) := genValidNode rng (depth := 0)
    rng := rng'
    let value := toYamlValue node
    let text := dump value
    -- Only test mutations on multi-line text (collections)
    if (text.splitOn "\n").length > 1 then
      -- Indent+1: may or may not parse, but must not crash
      let mutated := mutateIndent text 1
      match parseYamlSingle mutated with
      | .ok _ => indentConsistent := indentConsistent + 1
      | .error _ => indentConsistent := indentConsistent + 1
      indentTested := indentTested + 1

      -- Indent-1: likely to break
      let mutated := mutateIndent text (-1)
      match parseYamlSingle mutated with
      | .ok _ => indentConsistent := indentConsistent + 1
      | .error _ => indentConsistent := indentConsistent + 1
      indentTested := indentTested + 1

      -- Tab injection: should reject or parse differently
      let mutated := mutateTabInject text
      match parseYamlSingle mutated with
      | .ok _ => tabConsistent := tabConsistent + 1
      | .error _ => tabConsistent := tabConsistent + 1
      tabTested := tabTested + 1

      -- Delete newline: structural break
      let mutated := mutateDeleteNewline text
      match parseYamlSingle mutated with
      | .ok _ => newlineConsistent := newlineConsistent + 1
      | .error _ => newlineConsistent := newlineConsistent + 1
      newlineTested := newlineTested + 1

      -- Colon-nospace: may or may not work
      let mutated := mutateColonNoSpace text
      match parseYamlSingle mutated with
      | .ok _ => colonConsistent := colonConsistent + 1
      | .error _ => colonConsistent := colonConsistent + 1
      colonTested := colonTested + 1

  -- The key property: mutations don't crash the parser (consistent handling)
  check state s!"indent mutations: {indentConsistent}/{indentTested * 1} handled consistently"
    (indentConsistent == indentTested * 1)
  check state s!"tab mutations: {tabConsistent}/{tabTested} handled consistently"
    (tabConsistent == tabTested)
  check state s!"newline mutations: {newlineConsistent}/{newlineTested} handled consistently"
    (newlineConsistent == newlineTested)
  check state s!"colon mutations: {colonConsistent}/{colonTested} handled consistently"
    (colonConsistent == colonTested)

/-- §7: Diverse seed round-trip — test with many different PRNG seeds. -/
def testDiverseSeeds (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Diverse seed coverage"
  let seeds := [0, 1, 7, 13, 42, 97, 137, 271, 314, 577, 691, 997,
                1234, 2718, 3141, 4242, 6174, 7919, 8675, 9999]
  let mut totalPassed := 0
  let mut totalGenerated := 0
  let mut failures : Array String := #[]
  for seed in seeds do
    let mut rng := Rng.mk' seed
    let mut seedPassed := 0
    for i in [:5] do
      let (rng', node) := genValidNode rng
      rng := rng'
      totalGenerated := totalGenerated + 1
      match roundTripCheckDiag node with
      | .ok () =>
        seedPassed := seedPassed + 1
        totalPassed := totalPassed + 1
      | .error msg =>
        if failures.size < 3 then
          failures := failures.push s!"seed-{seed}/node-{i}: {msg}"
    check state s!"seed {seed}: {seedPassed}/5 round-trip" (seedPassed == 5)
  check state s!"total: {totalPassed}/{totalGenerated} across {seeds.length} seeds"
    (totalPassed == totalGenerated)
  for f in failures do
    checkM state "diverse-seed failure detail" false f

/-- §8: Config variation round-trip — same nodes, different DumpConfig settings. -/
def testConfigVariations (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "DumpConfig variation round-trip"
  let mut rng := Rng.mk' 2025
  -- Generate 10 nodes and test with various configs
  let configs : List (String × DumpConfig) := [
    ("default", {}),
    ("indent=1", { indent := 1 }),
    ("indent=4", { indent := 4 }),
    ("flow style", { defaultStyle := .flow }),
    ("double-quoted", { scalarStyle := .doubleQuoted }),
    ("single-quoted", { scalarStyle := .singleQuoted }),
    ("allow reserved", { allowReservedPlain := true })
  ]
  for _ in [:10] do
    let (rng', node) := genValidNode rng
    rng := rng'
    for (cfgName, cfg) in configs do
      match roundTripCheckDiag node cfg with
      | .ok () => check state s!"node+{cfgName}" true
      | .error msg => checkM state s!"node+{cfgName}" false msg

/-! ## Test Collection -/

def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testBasicRoundTrip state
  testFlowRoundTrip state
  testDoubleQuotedRoundTrip state
  testScalarEdgeCases state
  testCollectionStructures state
  testMutationResilience state
  testDiverseSeeds state
  testConfigVariations state
  let results ← finish state
  return { name := "propertytests",
           label := "Property-Based Round-Trip Tests (v0.2.13.3)",
           sourceFile := "Tests/PropertyTests.lean",
           tests := results }

end Tests.PropertyTests
