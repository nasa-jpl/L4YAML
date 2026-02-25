/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Stream
import Parser.Iterators
import Tests.VerifiedResult

/-!
# StreamIterator Tests

Demonstrates the `Std.Data.Iterators` integration enabled by lean4-parser
PR#97 (`std-iterators` branch).  Since `YamlStream` has a
`LawfulParserStream` instance (proved in `Stream.lean`), we can use
`StreamIterator` for provably terminating `for` loops over stream tokens.

## What this enables

- `for tok in (StreamIterator.mk stream).iter do ...` — provably terminating
- `Finite (StreamIterator YamlStream Char) Id` — well-founded iteration
- Standard `Std.Data.Iterators` consumers (`fold`, `toList`, etc.)
- No fuel parameter needed for iteration — termination is from `remaining`
-/

open Lean4Yaml
open Parser.Stream
open Tests

namespace Tests.IteratorTests

/-! ## Helper: collect all characters from a `YamlStream` via `StreamIterator` -/

/--
Collect all characters from a `YamlStream` using a `for` loop over
`StreamIterator`.  This is the canonical usage pattern enabled by PR#97.

The `for` loop terminates because:
1. `LawfulParserStream YamlStream Char` proves `remaining` decreases
2. `Finite (StreamIterator YamlStream Char) Id` witnesses well-foundedness
3. `IteratorLoop` provides the `for` loop instance
-/
def collectChars (input : String) : Array Char := Id.run do
  let stream := YamlStream.ofString input
  let mut acc : Array Char := #[]
  for tok in (StreamIterator.mk stream).iter do
    acc := acc.push tok
  return acc

/--
Count characters in a `YamlStream` using `StreamIterator`.
-/
def countChars (input : String) : Nat := Id.run do
  let stream := YamlStream.ofString input
  let mut n : Nat := 0
  for _tok in (StreamIterator.mk stream).iter do
    n := n + 1
  return n

/--
Collect characters matching a predicate using `StreamIterator`.
-/
def collectFiltered (input : String) (pred : Char → Bool) : Array Char := Id.run do
  let stream := YamlStream.ofString input
  let mut acc : Array Char := #[]
  for tok in (StreamIterator.mk stream).iter do
    if pred tok then
      acc := acc.push tok
  return acc

/-! ## Compile-time guards: `StreamIterator` correctness -/

-- Basic character collection
#guard collectChars "" == #[]
#guard collectChars "a" == #['a']
#guard collectChars "abc" == #['a', 'b', 'c']
#guard collectChars "hello" == #['h', 'e', 'l', 'l', 'o']

-- Multi-byte UTF-8 characters
#guard collectChars "αβγ" == #['α', 'β', 'γ']
#guard collectChars "日本語" == #['日', '本', '語']

-- Newlines and whitespace
#guard collectChars "a\nb" == #['a', '\n', 'b']
#guard collectChars "  " == #[' ', ' ']
#guard collectChars "\t" == #['\t']

-- Character counting
#guard countChars "" == 0
#guard countChars "hello" == 5
#guard countChars "αβγ" == 3
#guard countChars "a\nb\nc" == 5

-- Filtered collection
#guard collectFiltered "hello world" (· != ' ') == #['h', 'e', 'l', 'l', 'o', 'w', 'o', 'r', 'l', 'd']
#guard collectFiltered "abc123" Char.isAlpha == #['a', 'b', 'c']
#guard collectFiltered "abc123" Char.isDigit == #['1', '2', '3']

-- YAML-relevant patterns
#guard collectFiltered "key: value\n" (· != '\n') == #['k', 'e', 'y', ':', ' ', 'v', 'a', 'l', 'u', 'e']
#guard countChars "- item1\n- item2\n" == 16

/-! ## Runtime test suite -/

/-- Collect all iterator test results. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  setCategory state "StreamIterator basics"

  -- Test 1: Empty stream yields no characters
  check state "empty stream" (collectChars "" == #[])

  -- Test 2: Single character
  check state "single char" (collectChars "x" == #['x'])

  -- Test 3: ASCII string round-trip
  let input := "hello world"
  let chars := collectChars input
  check state "ASCII round-trip" (String.ofList chars.toList == input)

  -- Test 4: Multi-byte UTF-8
  let utf8Input := "αβγδ"
  let utf8Chars := collectChars utf8Input
  check state "UTF-8 chars" (String.ofList utf8Chars.toList == utf8Input)

  -- Test 5: Count agrees with String.length
  check state "count vs length" (countChars "test string" == "test string".length)

  -- Test 6: Newline handling
  let nlInput := "line1\nline2\nline3"
  let nlChars := collectChars nlInput
  check state "newlines preserved" (String.ofList nlChars.toList == nlInput)

  setCategory state "StreamIterator filtered"

  -- Test 7: Filter non-whitespace
  let filtered := collectFiltered "a b c" (fun c => c != ' ')
  check state "filter spaces" (filtered == #['a', 'b', 'c'])

  -- Test 8: Filter digits from YAML content
  let digits := collectFiltered "port: 8080" Char.isDigit
  check state "filter digits" (digits == #['8', '0', '8', '0'])

  -- Test 9: Large input
  let largeInput := String.ofList (List.replicate 1000 'x')
  check state "1000 chars count" (countChars largeInput == 1000)

  -- Test 10: YAML document markers
  let yamlDoc := "---\nkey: value\n..."
  check state "YAML doc chars" (countChars yamlDoc == yamlDoc.length)

  let results ← finish state
  return {
    name := "iteratortests"
    label := "StreamIterator (Std.Data.Iterators)"
    sourceFile := "Tests/IteratorTests.lean"
    tests := results
  }

end Tests.IteratorTests
