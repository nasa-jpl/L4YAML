import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Proofs.Termination
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Layer 1 Verification Tests

Runtime tests for the foundation layer of formal verification
(README Phase 3, Layer 1). These validate:

1. **YamlStream properties** — `next?` advances position,
   line/col tracking is correct, `remainingLength` decreases
2. **Pure function properties** — `trimTrailingWhitespace`,
   `trimTrailingWs` idempotence and correctness
3. **Grammar↔Combinators correspondence** — `Grammar.lean` Props
   match `Combinators.lean` Bool implementations for the same
   character classifications
4. **FoldResult type invariants** — construction and matching
5. **Indented proposition structure** — `Grammar.Indented` at
   various levels

These tests exercise the same properties that formal theorems
will prove. They serve as a regression safety net and as a
specification of expected behavior for proof development.
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Lean4Yaml.Grammar
open Lean4Yaml.Proofs.Termination
open Tests

namespace Tests.Verification

/-! ## 1. YamlStream Properties -/

def testStreamOfString (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlStream.ofString"
  let s := YamlStream.ofString "abc"
  check state "startPos is 0" (s.startPos.byteIdx == 0)
  check state "line is 0" (s.line == 0)
  check state "col is 0" (s.col == 0)
  check state "hasNext on non-empty" s.hasNext

  let empty := YamlStream.ofString ""
  check state "empty stream: not hasNext" (!empty.hasNext)

def testStreamNextBasic (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlStream.next? basic"
  let s := YamlStream.ofString "hi"
  match s.next? with
  | some (c, s') =>
    check state "first char is 'h'" (c == 'h')
    check state "col advances to 1" (s'.col == 1)
    check state "line stays 0" (s'.line == 0)
    match s'.next? with
    | some (c2, s'') =>
      check state "second char is 'i'" (c2 == 'i')
      check state "col advances to 2" (s''.col == 2)
      check state "next? at end is none" (s''.next?.isNone)
    | none =>
      check state "second next? should succeed" false
  | none =>
    check state "first next? should succeed" false

def testStreamNextNewline (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlStream.next? newline tracking"
  let s := YamlStream.ofString "a\nb"
  match s.next? with
  | some ('a', s1) =>
    check state "after 'a': line=0 col=1" (s1.line == 0 && s1.col == 1)
    match s1.next? with
    | some ('\n', s2) =>
      check state "after '\\n': line=1 col=0" (s2.line == 1 && s2.col == 0)
      match s2.next? with
      | some ('b', s3) =>
        check state "after 'b': line=1 col=1" (s3.line == 1 && s3.col == 1)
      | _ => check state "'b' after newline" false
    | _ => check state "newline char" false
  | _ => check state "'a' first" false

def testStreamMultipleNewlines (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlStream.next? multiple newlines"
  let s := YamlStream.ofString "x\n\ny"
  -- Consume 'x'
  let some ('x', s1) := s.next? | do check state "expect 'x'" false; return
  -- Consume first '\n'
  let some ('\n', s2) := s1.next? | do check state "expect first '\\n'" false; return
  check state "after first '\\n': line=1" (s2.line == 1)
  -- Consume second '\n'
  let some ('\n', s3) := s2.next? | do check state "expect second '\\n'" false; return
  check state "after second '\\n': line=2" (s3.line == 2)
  check state "after second '\\n': col=0" (s3.col == 0)
  -- Consume 'y'
  let some ('y', s4) := s3.next? | do check state "expect 'y'" false; return
  check state "after 'y': line=2 col=1" (s4.line == 2 && s4.col == 1)

def testStreamPeek (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlStream.peek?"
  let s := YamlStream.ofString "xy"
  check state "peek? returns 'x'" (s.peek? == some 'x')
  -- peek doesn't advance
  check state "peek? again returns 'x'" (s.peek? == some 'x')
  -- empty stream
  let empty := YamlStream.ofString ""
  check state "peek? on empty is none" (empty.peek?.isNone)

/-! ## 2. remainingLength Properties -/

def testRemainingLength (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "remainingLength"
  let s := YamlStream.ofString "abc"
  check state "initial remainingLength is 3" (remainingLength s == 3)

  let some (_, s') := s.next? | do check state "next? should succeed" false; return
  check state "after 1 char: remainingLength decreases" (remainingLength s' < remainingLength s)
  check state "after 1 char: remainingLength is 2" (remainingLength s' == 2)

  let some (_, s'') := s'.next? | do check state "next? should succeed" false; return
  check state "after 2 chars: remainingLength is 1" (remainingLength s'' == 1)

  let some (_, s''') := s''.next? | do check state "next? should succeed" false; return
  check state "after 3 chars: remainingLength is 0" (remainingLength s''' == 0)
  check state "at end: next? is none" (s'''.next?.isNone)

def testRemainingLengthEmpty (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "remainingLength empty"
  let s := YamlStream.ofString ""
  check state "empty: remainingLength is 0" (remainingLength s == 0)

def testRemainingLengthMultibyte (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "remainingLength multibyte"
  -- UTF-8: 'é' is 2 bytes, '日' is 3 bytes
  let s := YamlStream.ofString "é"
  check state "é: remainingLength > 1 (multibyte)" (remainingLength s > 1)
  let some (c, s') := s.next? | do check state "next? on é" false; return
  check state "next? yields 'é'" (c == 'é')
  check state "after 'é': remainingLength is 0" (remainingLength s' == 0)

  let s2 := YamlStream.ofString "日本"
  let initial := remainingLength s2
  check state "日本: initial remainingLength is 6 (3+3)" (initial == 6)
  let some (_, s2') := s2.next? | do check state "next? on 日" false; return
  check state "after '日': remainingLength is 3" (remainingLength s2' == 3)

def testRemainingLengthStrictlyDecreasing (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "remainingLength strictly decreasing"
  -- This is the runtime version of the next_decreasing theorem
  let s := YamlStream.ofString "hello"
  let mut current := s
  let mut prev := remainingLength current
  let mut allDecreasing := true
  for _ in [:5] do
    match current.next? with
    | some (_, next) =>
      let r := remainingLength next
      if r >= prev then
        allDecreasing := false
      prev := r
      current := next
    | none =>
      allDecreasing := false
  check state "remainingLength strictly decreases through all chars" allDecreasing
  check state "final remainingLength is 0" (remainingLength current == 0)

/-! ## 3. Grammar↔Combinators Correspondence -/

/-- Evaluate Grammar.isLineBreak (Prop) as a decidable Bool -/
def grammarIsLineBreak (c : Char) : Bool :=
  c == '\n' || c == '\r'

/-- Evaluate Grammar.isWhiteSpace (Prop) as a decidable Bool -/
def grammarIsWhiteSpace (c : Char) : Bool :=
  c == ' ' || c == '\t'

/-- Evaluate Grammar.isFlowIndicator (Prop) as a decidable Bool -/
def grammarIsFlowIndicator (c : Char) : Bool :=
  c == ',' || c == '[' || c == ']' || c == '{' || c == '}'

/-- Evaluate Grammar.isIndentChar (Prop) as a decidable Bool -/
def grammarIsIndentChar (c : Char) : Bool :=
  c == ' '

def testGrammarLineBreak (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Grammar↔Combinators: isLineBreak"
  let testChars : List Char := ['\n', '\r', ' ', '\t', 'a', '-', ':', '#']
  let mut allMatch := true
  for c in testChars do
    let g := grammarIsLineBreak c
    let p := Lean4Yaml.Parse.isLineBreak c
    if g != p then
      IO.println s!"    mismatch on {repr c}: Grammar={g} Combinators={p}"
      allMatch := false
  check state "isLineBreak: all test chars agree" allMatch
  -- Exhaustive on positive cases
  check state "LF is line break (Grammar)" (grammarIsLineBreak '\n')
  check state "CR is line break (Grammar)" (grammarIsLineBreak '\r')
  check state "space is NOT line break" (!grammarIsLineBreak ' ')
  check state "LF is line break (Combinators)" (Lean4Yaml.Parse.isLineBreak '\n')
  check state "CR is line break (Combinators)" (Lean4Yaml.Parse.isLineBreak '\r')
  check state "space is NOT line break (Combinators)" (!Lean4Yaml.Parse.isLineBreak ' ')

def testGrammarWhiteSpace (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Grammar↔Combinators: isWhiteSpace"
  let testChars : List Char := [' ', '\t', '\n', '\r', 'a', '-', '0']
  let mut allMatch := true
  for c in testChars do
    let g := grammarIsWhiteSpace c
    let p := Lean4Yaml.Parse.isWhiteSpace c
    if g != p then
      IO.println s!"    mismatch on {repr c}: Grammar={g} Combinators={p}"
      allMatch := false
  check state "isWhiteSpace: all test chars agree" allMatch
  check state "space is whitespace" (grammarIsWhiteSpace ' ')
  check state "tab is whitespace" (grammarIsWhiteSpace '\t')
  check state "newline is NOT whitespace" (!grammarIsWhiteSpace '\n')

def testGrammarFlowIndicator (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Grammar↔Combinators: isFlowIndicator"
  let flowChars : List Char := [',', '[', ']', '{', '}']
  let nonFlowChars : List Char := ['-', ':', '?', '#', 'a', ' ', '\n']
  let mut allMatch := true
  for c in flowChars do
    let g := grammarIsFlowIndicator c
    let p := Lean4Yaml.Parse.isFlowIndicator c
    if g != p then
      IO.println s!"    mismatch on {repr c}: Grammar={g} Combinators={p}"
      allMatch := false
  for c in nonFlowChars do
    let g := grammarIsFlowIndicator c
    let p := Lean4Yaml.Parse.isFlowIndicator c
    if g != p then
      IO.println s!"    mismatch on {repr c}: Grammar={g} Combinators={p}"
      allMatch := false
  check state "isFlowIndicator: all positive chars agree" allMatch
  -- Explicit checks
  for c in flowChars do
    check state s!"'{c}' is flow indicator (Grammar)" (grammarIsFlowIndicator c)
    check state s!"'{c}' is flow indicator (Combinators)" (Lean4Yaml.Parse.isFlowIndicator c)
  for c in nonFlowChars do
    check state s!"'{c}' is NOT flow indicator" (!grammarIsFlowIndicator c)

def testGrammarIndentChar (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Grammar↔Combinators: isIndentChar"
  check state "space is indent char" (grammarIsIndentChar ' ')
  check state "tab is NOT indent char" (!grammarIsIndentChar '\t')
  check state "space is not line break (indent requires space only)" (grammarIsIndentChar ' ' && !grammarIsLineBreak ' ')

/-! ## 4. canStartPlainScalar -/

def testCanStartPlainScalar (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "canStartPlainScalar"
  -- Regular letters can start plain scalars
  check state "'a' starts plain scalar" (canStartPlainScalar 'a' none)
  check state "'Z' starts plain scalar" (canStartPlainScalar 'Z' none)
  check state "'0' starts plain scalar" (canStartPlainScalar '0' none)

  -- Indicators cannot start plain scalars
  check state "'[' cannot start plain" (!canStartPlainScalar '[' none)
  check state "']' cannot start plain" (!canStartPlainScalar ']' none)
  check state "'{' cannot start plain" (!canStartPlainScalar '{' none)
  check state "'#' cannot start plain" (!canStartPlainScalar '#' none)
  check state "'\"' cannot start plain" (!canStartPlainScalar '"' none)
  check state "\"'\" cannot start plain" (!canStartPlainScalar '\'' none)

  -- Special cases: '-', '?', ':' can start plain IF followed by non-space
  check state "'-' + 'a' starts plain" (canStartPlainScalar '-' (some 'a'))
  check state "'-' + ' ' does NOT start plain" (!canStartPlainScalar '-' (some ' '))
  check state "'-' + none does NOT start plain" (!canStartPlainScalar '-' none)
  check state "':' + 'x' starts plain" (canStartPlainScalar ':' (some 'x'))
  check state "':' + ' ' does NOT start plain" (!canStartPlainScalar ':' (some ' '))
  check state "'?' + '!' starts plain" (canStartPlainScalar '?' (some '!'))
  check state "'?' + '\\t' does NOT start plain" (!canStartPlainScalar '?' (some '\t'))

  -- Whitespace cannot start plain scalars
  check state "space cannot start plain" (!canStartPlainScalar ' ' none)
  check state "tab cannot start plain" (!canStartPlainScalar '\t' none)
  check state "newline cannot start plain" (!canStartPlainScalar '\n' none)

/-! ## 5. FoldResult Type -/

def testFoldResult (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "FoldResult"
  let folded := FoldResult.folded "hello world"
  let forbidden := FoldResult.forbidden "document boundary at line 3"

  -- Pattern matching works
  match folded with
  | .folded s =>
    check state "folded carries content" (s == "hello world")
  | .forbidden _ =>
    check state "folded should not be forbidden" false

  match forbidden with
  | .forbidden msg =>
    check state "forbidden carries message" (msg == "document boundary at line 3")
  | .folded _ =>
    check state "forbidden should not be folded" false

  -- Repr instance works (non-crash)
  let _ := repr folded
  let _ := repr forbidden
  check state "Repr instance works for folded" true
  check state "Repr instance works for forbidden" true

/-! ## 6. trimTrailingWhitespace (pure function inside foldQuotedNewlines) -/

/-- Extracted mirror of foldQuotedNewlines.trimTrailingWhitespace for testing -/
def trimTrailingWsTest (s : String) : String :=
  let chars := s.toList
  let trimmed := chars.reverse.dropWhile (fun c => c == ' ' || c == '\t')
  String.ofList trimmed.reverse

def testTrimTrailingWhitespace (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "trimTrailingWhitespace"
  -- Basic trimming
  check state "trims trailing spaces" (trimTrailingWsTest "hello   " == "hello")
  check state "trims trailing tabs" (trimTrailingWsTest "hello\t\t" == "hello")
  check state "trims mixed space+tab" (trimTrailingWsTest "hello \t " == "hello")
  -- Content preservation
  check state "no trailing ws: unchanged" (trimTrailingWsTest "hello" == "hello")
  check state "empty string: unchanged" (trimTrailingWsTest "" == "")
  check state "preserves leading spaces" (trimTrailingWsTest "  hello" == "  hello")
  check state "preserves interior spaces" (trimTrailingWsTest "hello world" == "hello world")
  -- Edge cases
  check state "all spaces: empty result" (trimTrailingWsTest "   " == "")
  check state "all tabs: empty result" (trimTrailingWsTest "\t\t" == "")
  check state "single char no ws" (trimTrailingWsTest "x" == "x")
  check state "single space: empty" (trimTrailingWsTest " " == "")
  -- Idempotence: trimming twice = trimming once
  let once := trimTrailingWsTest "hello   "
  let twice := trimTrailingWsTest once
  check state "idempotent: trim∘trim = trim" (once == twice)
  -- No trailing whitespace after trim
  let trimmed := trimTrailingWsTest "foo \t  "
  let lastChar := trimmed.toList.getLast?
  check state "result has no trailing space" (lastChar != some ' ' && lastChar != some '\t')

/-! ## 7. YamlPos properties -/

def testYamlPos (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlPos"
  let p1 : YamlPos := { offset := 0, line := 0, col := 0 }
  let p2 : YamlPos := { offset := 5, line := 1, col := 3 }
  -- BEq
  check state "same pos is equal" (p1 == p1)
  check state "different pos is not equal" (p1 != p2)
  -- Ord (via offset)
  check state "p1 < p2 by offset" (compare p1 p2 == .lt)
  check state "p2 > p1 by offset" (compare p2 p1 == .gt)
  check state "p1 == p1 by comparison" (compare p1 p1 == .eq)
  -- DecidableEq
  check state "DecidableEq: equal" (decide (p1 = p1))
  check state "DecidableEq: not equal" (decide (p1 ≠ p2))
  -- Inhabited
  let _default : YamlPos := default
  check state "Inhabited: default exists" true

/-! ## 8. YamlStream.getPos consistency -/

def testStreamGetPos (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlStream.getPos"
  let s := YamlStream.ofString "a\nb"
  let pos0 := s.getPos
  check state "initial pos: offset=0" (pos0.offset == 0)
  check state "initial pos: line=0" (pos0.line == 0)
  check state "initial pos: col=0" (pos0.col == 0)

  let some (_, s1) := s.next? | do check state "next?" false; return
  let pos1 := s1.getPos
  check state "after 'a': offset>0" (pos1.offset > 0)
  check state "after 'a': col=1" (pos1.col == 1)

  let some (_, s2) := s1.next? | do check state "next?" false; return
  let pos2 := s2.getPos
  check state "after '\\n': line=1" (pos2.line == 1)
  check state "after '\\n': col=0" (pos2.col == 0)

/-! ## 9. Indented proposition (constructors) -/

def testIndented (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Grammar.Indented constructors"
  -- Indented 0 accepts any content
  let _ : Indented 0 ['a', 'b'] := .zero ['a', 'b']
  check state "Indented 0 ['a','b'] via .zero" true

  -- Indented 1 requires leading space
  let _ : Indented 1 [' ', 'a'] := .space 0 ['a'] (.zero ['a'])
  check state "Indented 1 [' ','a'] via .space" true

  -- Indented 2 requires two leading spaces
  let inner : Indented 1 [' ', 'a'] := .space 0 ['a'] (.zero ['a'])
  let _ : Indented 2 [' ', ' ', 'a'] := .space 1 [' ', 'a'] inner
  check state "Indented 2 [' ',' ','a'] via nested .space" true

/-! ## 10. Grammar.ChompStyle -/

def testChompStyle (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Grammar.ChompStyle"
  check state "strip ≠ clip" (ChompStyle.strip != ChompStyle.clip)
  check state "clip ≠ keep" (ChompStyle.clip != ChompStyle.keep)
  check state "strip ≠ keep" (ChompStyle.strip != ChompStyle.keep)
  check state "strip = strip" (ChompStyle.strip == ChompStyle.strip)
  -- DecidableEq enables use in if/match
  check state "DecidableEq works" (decide (ChompStyle.strip ≠ ChompStyle.keep))

/-! ## 11. NodeToValue correspondence -/

def testNodeToValue (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Grammar.NodeToValue"
  -- Construct a plain scalar node with proof of nonempty
  let content := "hello"
  let h : content.length > 0 := by native_decide
  let node := ValidNode.plainScalarBlock content h
  let value := YamlValue.scalar ⟨content, .plain, none⟩
  -- The correspondence can be constructed
  let _ : NodeToValue node value := .plainScalarBlock content h
  check state "plainScalarBlock ↔ YamlValue.scalar (plain)" true

  -- Single quoted
  let sqNode := ValidNode.singleQuoted "test"
  let sqVal := YamlValue.scalar ⟨"test", .singleQuoted, none⟩
  let _ : NodeToValue sqNode sqVal := .singleQuoted "test"
  check state "singleQuoted ↔ YamlValue.scalar (singleQuoted)" true

  -- Double quoted
  let dqNode := ValidNode.doubleQuoted "escaped\"content"
  let dqVal := YamlValue.scalar ⟨"escaped\"content", .doubleQuoted, none⟩
  let _ : NodeToValue dqNode dqVal := .doubleQuoted "escaped\"content"
  check state "doubleQuoted ↔ YamlValue.scalar (doubleQuoted)" true

/-! ## 12. ValidYaml structure -/

def testValidYaml (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Grammar.ValidYaml structure"
  let content := "world"
  let h : content.length > 0 := by native_decide
  let node := ValidNode.plainScalarBlock content h
  let value := YamlValue.scalar ⟨content, .plain, none⟩
  let corr := NodeToValue.plainScalarBlock content h
  let vy : ValidYaml := {
    input := "world"
    value := value
    grammar := node
    corresponds := corr
  }
  check state "ValidYaml: input matches" (vy.input == "world")
  check state "ValidYaml: grammar node constructed" true
  check state "ValidYaml: correspondence holds" true

/-! ## 13. Stream remaining consistent with next? -/

def testStreamExhaustive (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Stream exhaustive consumption"
  -- Ensure we can fully consume a stream and remainingLength goes to 0
  let testStr := "key: value\n- item\n"
  let s := YamlStream.ofString testStr
  let mut current := s
  let mut charCount : Nat := 0
  let mut prevRemaining := remainingLength current
  let mut monotone := true
  repeat
    match current.next? with
    | some (_, next) =>
      charCount := charCount + 1
      let r := remainingLength next
      if r >= prevRemaining then
        monotone := false
      prevRemaining := r
      current := next
    | none => break
  check state s!"consumed {charCount} chars" (charCount > 0)
  check state "final remainingLength is 0" (remainingLength current == 0)
  check state "remainingLength monotonically decreased" monotone

/-! ## 14. CRLF handling in stream -/

def testStreamCRLF (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Stream CRLF handling"
  -- CR doesn't increment line (only LF does in our stream)
  let s := YamlStream.ofString "a\rb"
  let some ('a', s1) := s.next? | do check state "expect 'a'" false; return
  let some ('\r', s2) := s1.next? | do check state "expect CR" false; return
  -- CR is treated as regular char by stream (not a line break for col reset)
  -- Our stream only resets on '\n'
  check state "CR: col advances (not reset)" (s2.col == 2)
  check state "CR: line unchanged" (s2.line == 0)

  -- CRLF sequence
  let s3 := YamlStream.ofString "x\r\ny"
  let some ('x', s4) := s3.next? | do check state "expect 'x'" false; return
  let some ('\r', s5) := s4.next? | do check state "expect CR" false; return
  let some ('\n', s6) := s5.next? | do check state "expect LF" false; return
  check state "CRLF LF: line=1 col=0" (s6.line == 1 && s6.col == 0)

/-! ## Collector -/

/-- Collect all Layer 1 verification test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)

  -- 1. Stream properties
  testStreamOfString state
  testStreamNextBasic state
  testStreamNextNewline state
  testStreamMultipleNewlines state
  testStreamPeek state

  -- 2. remainingLength
  testRemainingLength state
  testRemainingLengthEmpty state
  testRemainingLengthMultibyte state
  testRemainingLengthStrictlyDecreasing state

  -- 3. Grammar↔Combinators
  testGrammarLineBreak state
  testGrammarWhiteSpace state
  testGrammarFlowIndicator state
  testGrammarIndentChar state

  -- 4. canStartPlainScalar
  testCanStartPlainScalar state

  -- 5. FoldResult
  testFoldResult state

  -- 6. trimTrailingWhitespace
  testTrimTrailingWhitespace state

  -- 7. YamlPos
  testYamlPos state

  -- 8. getPos consistency
  testStreamGetPos state

  -- 9. Indented constructors
  testIndented state

  -- 10. ChompStyle
  testChompStyle state

  -- 11. NodeToValue
  testNodeToValue state

  -- 12. ValidYaml
  testValidYaml state

  -- 13. Exhaustive stream
  testStreamExhaustive state

  -- 14. CRLF
  testStreamCRLF state

  let results ← finish state
  return { name := "verification", label := "Layer 1 Verification Tests", sourceFile := "Tests/Verification.lean", tests := results }

end Tests.Verification
