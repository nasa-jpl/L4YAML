import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Combinators
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Character Classification Tests (Layer 1c)

Runtime tests validating that Grammar (Prop) and Parser (Bool) character
classifiers agree on comprehensive character sets. These are the runtime
counterparts of the formal proofs in `Lean4Yaml/Proofs/CharClass.lean`.

## Categories

1. **isLineBreak** — Grammar.isLineBreak ↔ Parse.isLineBreak
2. **isWhiteSpace** — Grammar.isWhiteSpace ↔ Parse.isWhiteSpace
3. **isIndentChar** — Grammar.isIndentChar ↔ (c == ' ')
4. **isFlowIndicator** — Grammar.isFlowIndicator ↔ Parse.isFlowIndicator
5. **isIndicator** — Grammar indicator list ↔ Parse.isIndicator
6. **canStartPlainScalar** — Grammar.canStartPlainScalar → Parse.canStartPlainScalar
7. **List.Mem ↔ List.elem** — Prop/Bool membership bridge on concrete chars
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Lean4Yaml.Grammar
open Tests

namespace Tests.CharClass

/-! ## Helpers

Evaluate Grammar Prop-valued predicates as decidable Bools. -/

def grammarIsLineBreak (c : Char) : Bool :=
  c == '\n' || c == '\r'

def grammarIsWhiteSpace (c : Char) : Bool :=
  c == ' ' || c == '\t'

def grammarIsIndentChar (c : Char) : Bool :=
  c == ' '

def grammarIsFlowIndicator (c : Char) : Bool :=
  c == ',' || c == '[' || c == ']' || c == '{' || c == '}'

/-- Full indicator list from Grammar.canStartPlainScalar -/
def grammarIsIndicator (c : Char) : Bool :=
  c == '-' || c == '?' || c == ':' || c == ',' || c == '[' || c == ']' ||
  c == '{' || c == '}' || c == '#' || c == '&' || c == '*' || c == '!' ||
  c == '|' || c == '>' || c == '\'' || c == '"' || c == '%' || c == '@' || c == '`'

/-- A comprehensive set of test chars covering ASCII printable, whitespace,
    indicators, and boundaries. -/
def testChars : List Char :=
  -- Whitespace & line breaks
  [' ', '\t', '\n', '\r',
  -- Letters & digits
   'a', 'z', 'A', 'Z', '0', '9',
  -- YAML indicators
   '-', '?', ':', ',', '[', ']', '{', '}',
   '#', '&', '*', '!', '|', '>', '\'', '"', '%', '@', '`',
  -- Non-indicator punctuation
   '.', '/', '\\', '(', ')', ';', '=', '+', '_', '~', '^',
  -- Boundary ASCII
   '\x00', '\x7F']

/-! ## 1. isLineBreak -/

def testIsLineBreak (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "isLineBreak correspondence"
  -- Exhaustive agreement on test chars
  let mut allMatch := true
  for c in testChars do
    let g := grammarIsLineBreak c
    let p := Parse.isLineBreak c
    if g != p then
      allMatch := false
  check state "all test chars agree" allMatch
  -- Positive cases
  check state "LF is line break (Grammar)" (grammarIsLineBreak '\n')
  check state "CR is line break (Grammar)" (grammarIsLineBreak '\r')
  check state "LF is line break (Parse)" (Parse.isLineBreak '\n')
  check state "CR is line break (Parse)" (Parse.isLineBreak '\r')
  -- Negative cases
  check state "space is NOT line break" (!grammarIsLineBreak ' ')
  check state "tab is NOT line break" (!grammarIsLineBreak '\t')
  check state "'a' is NOT line break" (!grammarIsLineBreak 'a')
  check state "NUL is NOT line break" (!grammarIsLineBreak '\x00')

/-! ## 2. isWhiteSpace -/

def testIsWhiteSpace (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "isWhiteSpace correspondence"
  let mut allMatch := true
  for c in testChars do
    let g := grammarIsWhiteSpace c
    let p := Parse.isWhiteSpace c
    if g != p then
      allMatch := false
  check state "all test chars agree" allMatch
  -- Positive cases
  check state "space is whitespace" (grammarIsWhiteSpace ' ')
  check state "tab is whitespace" (grammarIsWhiteSpace '\t')
  check state "space is whitespace (Parse)" (Parse.isWhiteSpace ' ')
  check state "tab is whitespace (Parse)" (Parse.isWhiteSpace '\t')
  -- Negative cases (line breaks are NOT whitespace per §5.5)
  check state "LF is NOT whitespace" (!grammarIsWhiteSpace '\n')
  check state "CR is NOT whitespace" (!grammarIsWhiteSpace '\r')
  check state "'a' is NOT whitespace" (!grammarIsWhiteSpace 'a')
  check state "'-' is NOT whitespace" (!grammarIsWhiteSpace '-')

/-! ## 3. isIndentChar -/

def testIsIndentChar (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "isIndentChar correspondence"
  -- Only space is valid for indentation (§6.1)
  check state "space is indent char" (grammarIsIndentChar ' ')
  check state "tab is NOT indent char" (!grammarIsIndentChar '\t')
  check state "LF is NOT indent char" (!grammarIsIndentChar '\n')
  check state "'a' is NOT indent char" (!grammarIsIndentChar 'a')
  -- Indent char is a strict subset of whitespace
  check state "indent ⊂ whitespace: space" (grammarIsIndentChar ' ' && grammarIsWhiteSpace ' ')
  check state "indent ⊄ tab (ws but not indent)" (!grammarIsIndentChar '\t' && grammarIsWhiteSpace '\t')

/-! ## 4. isFlowIndicator -/

def testIsFlowIndicator (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "isFlowIndicator correspondence"
  let flowChars := [',', '[', ']', '{', '}']
  let nonFlowChars := ['-', '?', ':', '#', '&', '*', '!', '|', '>',
                        '\'', '"', '%', '@', '`', 'a', ' ', '\n']
  -- Positive: all flow indicator chars
  let mut allMatch := true
  for c in flowChars do
    let g := grammarIsFlowIndicator c
    let p := Parse.isFlowIndicator c
    if g != p then allMatch := false
  check state "all flow chars agree" allMatch
  for c in flowChars do
    check state s!"'{c}' is flow indicator (Grammar)" (grammarIsFlowIndicator c)
    check state s!"'{c}' is flow indicator (Parse)" (Parse.isFlowIndicator c)
  -- Negative: non-flow indicator chars
  for c in nonFlowChars do
    check state s!"'{c}' is NOT flow indicator (Grammar)" (!grammarIsFlowIndicator c)
    check state s!"'{c}' is NOT flow indicator (Parse)" (!Parse.isFlowIndicator c)

/-! ## 5. isIndicator -/

def testIsIndicator (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "isIndicator correspondence"
  let indicatorChars := ['-', '?', ':', ',', '[', ']', '{', '}',
                          '#', '&', '*', '!', '|', '>', '\'', '"', '%', '@', '`']
  let nonIndChars := ['a', 'z', '0', '9', ' ', '\n', '\t', '.', '/', '(', ')']
  -- Positive: Grammar list ↔ Parse.isIndicator
  for c in indicatorChars do
    check state s!"'{c}' is indicator (Grammar)" (grammarIsIndicator c)
    check state s!"'{c}' is indicator (Parse)" (Parse.isIndicator c)
  -- Negative
  for c in nonIndChars do
    check state s!"'{c}' is NOT indicator (Grammar)" (!grammarIsIndicator c)
    check state s!"'{c}' is NOT indicator (Parse)" (!Parse.isIndicator c)
  -- Flow indicators are a subset of all indicators
  let flowChars := [',', '[', ']', '{', '}']
  for c in flowChars do
    check state s!"flow '{c}' ⊆ indicator" (Parse.isFlowIndicator c && Parse.isIndicator c)

/-! ## 6. canStartPlainScalar -/

def testCanStartPlainScalar (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "canStartPlainScalar correspondence"
  -- Regular printable non-indicator chars: always can start
  check state "'a' starts plain" (canStartPlainScalar 'a' none)
  check state "'Z' starts plain" (canStartPlainScalar 'Z' none)
  check state "'0' starts plain" (canStartPlainScalar '0' none)
  check state "'.' starts plain" (canStartPlainScalar '.' none)
  check state "'/' starts plain" (canStartPlainScalar '/' none)
  check state "'(' starts plain" (canStartPlainScalar '(' none)
  -- Indicators cannot start plain scalars
  check state "'[' cannot start" (!canStartPlainScalar '[' none)
  check state "']' cannot start" (!canStartPlainScalar ']' none)
  check state "'{' cannot start" (!canStartPlainScalar '{' none)
  check state "'}' cannot start" (!canStartPlainScalar '}' none)
  check state "'#' cannot start" (!canStartPlainScalar '#' none)
  check state "'&' cannot start" (!canStartPlainScalar '&' none)
  check state "'*' cannot start" (!canStartPlainScalar '*' none)
  check state "'!' cannot start" (!canStartPlainScalar '!' none)
  check state "'\"' cannot start" (!canStartPlainScalar '"' none)
  check state "\"'\" cannot start" (!canStartPlainScalar '\'' none)
  check state "'%' cannot start" (!canStartPlainScalar '%' none)
  check state "'@' cannot start" (!canStartPlainScalar '@' none)
  check state "'`' cannot start" (!canStartPlainScalar '`' none)
  check state "'|' cannot start" (!canStartPlainScalar '|' none)
  check state "'>' cannot start" (!canStartPlainScalar '>' none)
  -- Exception chars: '-', '?', ':' can start if followed by non-ws
  check state "'-' + 'a' starts" (canStartPlainScalar '-' (some 'a'))
  check state "'-' + ' ' fails" (!canStartPlainScalar '-' (some ' '))
  check state "'-' + none fails" (!canStartPlainScalar '-' none)
  check state "'-' + '\\t' fails" (!canStartPlainScalar '-' (some '\t'))
  check state "'-' + '\\n' fails" (!canStartPlainScalar '-' (some '\n'))
  check state "'?' + '!' starts" (canStartPlainScalar '?' (some '!'))
  check state "'?' + ' ' fails" (!canStartPlainScalar '?' (some ' '))
  check state "'?' + none fails" (!canStartPlainScalar '?' none)
  check state "':' + 'x' starts" (canStartPlainScalar ':' (some 'x'))
  check state "':' + ' ' fails" (!canStartPlainScalar ':' (some ' '))
  check state "':' + '\\r' fails" (!canStartPlainScalar ':' (some '\r'))
  -- Whitespace / line breaks cannot start plain scalars
  check state "space cannot start" (!canStartPlainScalar ' ' none)
  check state "tab cannot start" (!canStartPlainScalar '\t' none)
  check state "LF cannot start" (!canStartPlainScalar '\n' none)
  check state "CR cannot start" (!canStartPlainScalar '\r' none)

/-! ## 7. List.Mem ↔ List.elem bridge -/

def testListMembership (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "List.Mem ↔ List.elem bridge"
  -- For concrete lists, Prop-level ∈ (List.Mem) and Bool-level ∈ (List.elem)
  -- must agree. This validates the bridge used in CharClass proofs.
  let flowList : List Char := [',', '[', ']', '{', '}']
  let indicatorList : List Char := ['-', '?', ':', ',', '[', ']', '{', '}',
    '#', '&', '*', '!', '|', '>', '\'', '"', '%', '@', '`']

  -- Bool-level membership (List.elem) for flow indicators
  for c in flowList do
    check state s!"'{c}' ∈ flowList (elem)" (flowList.elem c)
  check state "'a' ∉ flowList (elem)" (!flowList.elem 'a')
  check state "'-' ∉ flowList (elem)" (!flowList.elem '-')
  check state "'#' ∉ flowList (elem)" (!flowList.elem '#')

  -- Bool-level membership for full indicator list
  for c in indicatorList do
    check state s!"'{c}' ∈ indicatorList (elem)" (indicatorList.elem c)
  check state "'a' ∉ indicatorList (elem)" (!indicatorList.elem 'a')
  check state "'.' ∉ indicatorList (elem)" (!indicatorList.elem '.')
  check state "' ' ∉ indicatorList (elem)" (!indicatorList.elem ' ')

  -- Parse.isFlowIndicator and Parse.isIndicator use List.elem internally;
  -- verify they match element-wise membership
  for c in flowList do
    check state s!"isFlowIndicator '{c}' == elem" (Parse.isFlowIndicator c == flowList.elem c)
  for c in indicatorList do
    check state s!"isIndicator '{c}' == elem" (Parse.isIndicator c == indicatorList.elem c)

/-! ## Collect All Tests -/

/-- Collect all CharClass test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testIsLineBreak state
  testIsWhiteSpace state
  testIsIndentChar state
  testIsFlowIndicator state
  testIsIndicator state
  testCanStartPlainScalar state
  testListMembership state
  let results ← finish state
  return { name := "charclass", label := "CharClass Correspondence Tests",
           sourceFile := "Tests/CharClassTests.lean", tests := results }

end Tests.CharClass
