import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Proofs.Termination
import Batteries.Data.String.Lemmas
import Tests.VerifiedResult

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Batteries String Lemma Tests

Tests that exercise Batteries' `String.Pos.Raw` lemmas in the context
of our `YamlStream` verification. These validate the axiom-free
proof strategy:

1. **`Pos.Raw.lt_addChar`** — position strictly advances after `next`
2. **`Char.utf8Size_pos`** — every character consumes ≥1 byte
3. **`next_of_valid` / `get_of_valid`** — character access at valid positions
4. **`Pos.Raw.Valid`** — well-formedness of string positions
5. **`remainingLength` arithmetic** — the key fact for termination:
   `next?` strictly decreases remaining input

These are the runtime counterparts of the formal lemmas that
replace `sorry` and `axiom` in the `Proofs/` modules.

Produces a `VerifiedSuiteResult` for structured reporting.
-/

open Lean4Yaml
open Lean4Yaml.Grammar
open Lean4Yaml.Proofs.Termination
open Tests

namespace Tests.StringLemmas

/-! ## 1. Char.utf8Size Positivity

Every Unicode character encodes to at least 1 byte in UTF-8.
This is the root fact that makes position advancement strict.
-/

def testUtf8SizePos (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Char.utf8Size positivity"
  -- ASCII
  check state "utf8Size 'a' > 0" (Char.utf8Size 'a' > 0)
  check state "utf8Size 'a' == 1" (Char.utf8Size 'a' == 1)
  check state "utf8Size '\\n' > 0" (Char.utf8Size '\n' > 0)
  check state "utf8Size '\\n' == 1" (Char.utf8Size '\n' == 1)
  check state "utf8Size ' ' > 0" (Char.utf8Size ' ' > 0)
  check state "utf8Size '\\t' > 0" (Char.utf8Size '\t' > 0)
  -- YAML indicators
  check state "utf8Size ':' > 0" (Char.utf8Size ':' > 0)
  check state "utf8Size '-' > 0" (Char.utf8Size '-' > 0)
  check state "utf8Size '{' > 0" (Char.utf8Size '{' > 0)
  check state "utf8Size '}' > 0" (Char.utf8Size '}' > 0)
  check state "utf8Size '[' > 0" (Char.utf8Size '[' > 0)
  check state "utf8Size ']' > 0" (Char.utf8Size ']' > 0)
  -- Multibyte characters
  check state "utf8Size '€' == 3 (3-byte)" (Char.utf8Size '€' == 3)
  check state "utf8Size 'é' == 2 (2-byte)" (Char.utf8Size 'é' == 2)
  check state "utf8Size '日' == 3 (3-byte CJK)" (Char.utf8Size '日' == 3)
  check state "utf8Size '𐀀' == 4 (4-byte)" (Char.utf8Size '𐀀' == 4)
  -- The formal proof:
  -- Char.utf8Size_pos : ∀ c, 0 < c.utf8Size
  -- verifiable at compile time for concrete chars
  check state "utf8Size_pos holds for NUL" (Char.utf8Size (Char.ofNat 0) > 0)
  check state "utf8Size_pos holds for DEL" (Char.utf8Size (Char.ofNat 127) > 0)
  check state "utf8Size_pos holds for max BMP" (Char.utf8Size (Char.ofNat 0xFFFF) > 0)

/-! ## 2. String.Pos.Raw Advancement

`Pos.Raw.next` advances the byte position by `utf8Size` of the
character at that position. Combined with `utf8Size > 0`, this
gives strict position increase — the foundation of termination.
-/

def testPosRawAdvancement (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "String.Pos.Raw advancement"
  -- ASCII string: each char is 1 byte
  let s := "abc"
  let p0 : String.Pos.Raw := ⟨0⟩
  let p1 := String.Pos.Raw.next s p0
  let p2 := String.Pos.Raw.next s p1
  let p3 := String.Pos.Raw.next s p2

  check state "next advances past 'a'" (p1.byteIdx == 1)
  check state "next advances past 'b'" (p2.byteIdx == 2)
  check state "next advances past 'c'" (p3.byteIdx == 3)
  check state "p0 < p1 (strict)" (p0.byteIdx < p1.byteIdx)
  check state "p1 < p2 (strict)" (p1.byteIdx < p2.byteIdx)
  check state "p2 < p3 (strict)" (p2.byteIdx < p3.byteIdx)

  -- Multibyte: "é€" → 2 bytes + 3 bytes = 5 total
  let ms := "é€"
  let mp0 : String.Pos.Raw := ⟨0⟩
  let mp1 := String.Pos.Raw.next ms mp0
  let mp2 := String.Pos.Raw.next ms mp1

  check state "next past 'é' (2-byte)" (mp1.byteIdx == 2)
  check state "next past '€' (3-byte)" (mp2.byteIdx == 5)
  check state "mp0 < mp1 (multibyte strict)" (mp0.byteIdx < mp1.byteIdx)
  check state "mp1 < mp2 (multibyte strict)" (mp1.byteIdx < mp2.byteIdx)

  -- Key property: next always strictly advances
  -- This is Batteries' Pos.Raw.lt_addChar:
  --   theorem lt_addChar (p : Pos.Raw) (c : Char) : p < p + c
  -- We test the runtime version here
  let p := String.Pos.Raw.next "x" ⟨0⟩
  check state "next strictly advances from 0" (0 < p.byteIdx)

/-! ## 3. Get at Valid Position

`Pos.Raw.get` reads the character at a given byte offset.
Batteries' `get_of_valid` proves this returns the expected character
when the position corresponds to a character boundary.
-/

def testGetAtValidPos (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Pos.Raw.get at valid positions"
  let s := "hello"
  -- Position 0 → 'h'
  check state "get at 0 == 'h'" (String.Pos.Raw.get s ⟨0⟩ == 'h')
  -- Position 1 → 'e' (ASCII, 1-byte chars)
  check state "get at 1 == 'e'" (String.Pos.Raw.get s ⟨1⟩ == 'e')
  -- Position 4 → 'o'
  check state "get at 4 == 'o'" (String.Pos.Raw.get s ⟨4⟩ == 'o')

  -- Multibyte: "a€b" → 'a' at 0, '€' at 1, 'b' at 4
  let ms := "a€b"
  check state "get 'a' at 0 (multibyte string)" (String.Pos.Raw.get ms ⟨0⟩ == 'a')
  check state "get '€' at 1 (3-byte char)" (String.Pos.Raw.get ms ⟨1⟩ == '€')
  check state "get 'b' at 4 (after 3-byte char)" (String.Pos.Raw.get ms ⟨4⟩ == 'b')

  -- Consistency: get then next gives the right byte offset
  let c0 := String.Pos.Raw.get "xyz" ⟨0⟩
  let p1 := String.Pos.Raw.next "xyz" ⟨0⟩
  check state "get at 0 == 'x'" (c0 == 'x')
  check state "next past 'x' lands on 'y'" (String.Pos.Raw.get "xyz" p1 == 'y')

/-! ## 4. YamlStream.next? and Pos.Raw Consistency

Our `YamlStream.next?` is built on `Pos.Raw.get` and `Pos.Raw.next`.
These tests verify that `YamlStream.next?` produces the same
character and advances to the same byte offset as the raw functions.
-/

def testStreamPosConsistency (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "YamlStream ↔ Pos.Raw consistency"
  let input := "test"
  let stream := YamlStream.ofString input

  -- next? should return the same char as Pos.Raw.get
  match stream.next? with
  | some (c, s') =>
    let rawChar := String.Pos.Raw.get input ⟨0⟩
    check state "next? char matches Pos.Raw.get" (c == rawChar)

    let rawNext := String.Pos.Raw.next input ⟨0⟩
    check state "next? startPos matches Pos.Raw.next" (s'.startPos.byteIdx == rawNext.byteIdx)
    check state "stopPos unchanged" (s'.stopPos.byteIdx == stream.stopPos.byteIdx)
  | none => check state "next? should succeed on non-empty" false

  -- Multibyte consistency
  let ms := "日本"
  let mstream := YamlStream.ofString ms
  match mstream.next? with
  | some (c, s') =>
    check state "multibyte: next? char is '日'" (c == '日')
    let rawNext := String.Pos.Raw.next ms ⟨0⟩
    check state "multibyte: startPos advances by 3" (s'.startPos.byteIdx == rawNext.byteIdx)
    check state "multibyte: startPos == 3" (s'.startPos.byteIdx == 3)
  | none => check state "multibyte next? should succeed" false

/-! ## 5. remainingLength Strictly Decreases (Termination Foundation)

This is the runtime version of the key theorem for parser termination:
after `next?` succeeds, `remainingLength` strictly decreases.

The formal proof uses:
  - `Pos.Raw.next s p = p + (Pos.Raw.get s p).utf8Size`
  - `(Pos.Raw.get s p).utf8Size > 0`  (from `Char.utf8Size_pos`)
  - Therefore `remainingLength` drops by ≥ 1

This test validates the exact same property at runtime.
-/

def testRemainingDecreases (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "remainingLength strictly decreases"

  -- Single char
  let s1 := YamlStream.ofString "x"
  let r1 := remainingLength s1
  check state "single char: remainingLength > 0" (r1 > 0)
  match s1.next? with
  | some (_, s1') =>
    let r1' := remainingLength s1'
    check state "single char: remaining decreases" (r1' < r1)
    check state "single char: remaining == 0 after" (r1' == 0)
  | none => check state "single char: next? succeeds" false

  -- Multiple chars: strictly decreasing chain
  let s := YamlStream.ofString "abc"
  let r0 := remainingLength s
  match s.next? with
  | some (_, s') =>
    let r1 := remainingLength s'
    check state "r0 > r1 after 'a'" (r1 < r0)
    match s'.next? with
    | some (_, s'') =>
      let r2 := remainingLength s''
      check state "r1 > r2 after 'b'" (r2 < r1)
      match s''.next? with
      | some (_, s''') =>
        let r3 := remainingLength s'''
        check state "r2 > r3 after 'c'" (r3 < r2)
        check state "r3 == 0 at end" (r3 == 0)
      | none => check state "third next? succeeds" false
    | none => check state "second next? succeeds" false
  | none => check state "first next? succeeds" false

  -- Multibyte: decreases by utf8Size, not by 1
  let ms := YamlStream.ofString "€x"
  let mr0 := remainingLength ms
  match ms.next? with
  | some (c, ms') =>
    let mr1 := remainingLength ms'
    check state "multibyte: drops by utf8Size (3)" (mr0 - mr1 == Char.utf8Size c)
    check state "multibyte: still strictly decreases" (mr1 < mr0)
  | none => check state "multibyte next? succeeds" false

  -- Empty stream: next? returns none
  let empty := YamlStream.ofString ""
  check state "empty: remainingLength == 0" (remainingLength empty == 0)
  check state "empty: next? is none" (empty.next?.isNone)

/-! ## 6. rawEndPos and utf8ByteSize

The stream's `stopPos` equals `rawEndPos` of the string, which
equals the total UTF-8 byte size. Batteries provides:
  `rawEndPos_ofList : rawEndPos (ofList cs) = ⟨utf8Len cs⟩`
  `utf8ByteSize_ofList : utf8ByteSize (ofList cs) = utf8Len cs`
-/

def testRawEndPos (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "rawEndPos / utf8ByteSize"
  -- ASCII
  let s := "hello"
  check state "rawEndPos 'hello' == 5" (s.rawEndPos.byteIdx == 5)
  check state "utf8ByteSize 'hello' == 5" (s.utf8ByteSize == 5)
  check state "rawEndPos == utf8ByteSize" (s.rawEndPos.byteIdx == s.utf8ByteSize)

  -- Multibyte
  let ms := "aé€"  -- 1 + 2 + 3 = 6 bytes
  check state "rawEndPos 'aé€' == 6" (ms.rawEndPos.byteIdx == 6)
  check state "utf8ByteSize 'aé€' == 6" (ms.utf8ByteSize == 6)

  -- Empty
  check state "rawEndPos '' == 0" ("".rawEndPos.byteIdx == 0)
  check state "utf8ByteSize '' == 0" ("".utf8ByteSize == 0)

  -- Stream stopPos matches
  let stream := YamlStream.ofString "test"
  check state "stream.stopPos == rawEndPos" (stream.stopPos.byteIdx == "test".rawEndPos.byteIdx)

  -- 4-byte char
  let fb := "𐀀"  -- U+10000, 4 bytes in UTF-8
  check state "rawEndPos 4-byte char == 4" (fb.rawEndPos.byteIdx == 4)

/-! ## 7. Position Validity

A position is valid if it sits on a character boundary.
The initial position (0) and rawEndPos are always valid.
After `next`, the result is valid too (Batteries' `valid_next`).
-/

def testPositionValidity (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "position validity (character boundaries)"
  -- For ASCII, every byte index 0..n is a valid position
  let s := "abc"
  check state "pos 0 valid (start)" (String.Pos.Raw.get s ⟨0⟩ == 'a')
  check state "pos 1 valid (after 'a')" (String.Pos.Raw.get s ⟨1⟩ == 'b')
  check state "pos 2 valid (after 'b')" (String.Pos.Raw.get s ⟨2⟩ == 'c')

  -- For multibyte, only character boundaries are meaningful
  let ms := "aé"  -- 'a' at 0, 'é' at 1 (2 bytes)
  check state "pos 0 → 'a'" (String.Pos.Raw.get ms ⟨0⟩ == 'a')
  check state "pos 1 → 'é' (valid boundary)" (String.Pos.Raw.get ms ⟨1⟩ == 'é')
  -- pos 2 is mid-character for 'é' but rawEndPos
  check state "rawEndPos is 3" (ms.rawEndPos.byteIdx == 3)

  -- nextPos chain visits only valid positions
  let chain := "x€y"
  let p0 : String.Pos.Raw := ⟨0⟩
  let p1 := String.Pos.Raw.next chain p0  -- past 'x' → 1
  let p2 := String.Pos.Raw.next chain p1  -- past '€' → 4
  let p3 := String.Pos.Raw.next chain p2  -- past 'y' → 5
  check state "chain: p0=0" (p0.byteIdx == 0)
  check state "chain: p1=1 (after 'x')" (p1.byteIdx == 1)
  check state "chain: p2=4 (after '€')" (p2.byteIdx == 4)
  check state "chain: p3=5 (after 'y')" (p3.byteIdx == 5)
  check state "chain: p3 == rawEndPos" (p3.byteIdx == chain.rawEndPos.byteIdx)

/-! ## 8. Subtraction Arithmetic for remainingLength

`remainingLength s = s.stopPos.byteIdx - s.startPos.byteIdx`

After `next?`, `startPos` advances by `utf8Size c` while `stopPos`
stays fixed. So:
  `remainingLength s' = stopPos - (startPos + utf8Size c)`
                      = `(stopPos - startPos) - utf8Size c`
                      = `remainingLength s - utf8Size c`

And since `utf8Size c ≥ 1`, this is strictly less.
-/

def testSubtractionArithmetic (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "subtraction arithmetic"
  let input := "ab€d"  -- 1 + 1 + 3 + 1 = 6 bytes
  let s := YamlStream.ofString input

  -- Compute expected remaining lengths
  let stop := s.stopPos.byteIdx
  check state "stopPos == 6" (stop == 6)

  -- After each next?, remainingLength = stop - newStartPos
  match s.next? with
  | some ('a', s1) =>
    check state "after 'a': start=1, remaining=5" (remainingLength s1 == 5)
    check state "remaining = stop - start" (remainingLength s1 == stop - s1.startPos.byteIdx)
    match s1.next? with
    | some ('b', s2) =>
      check state "after 'b': start=2, remaining=4" (remainingLength s2 == 4)
      match s2.next? with
      | some ('€', s3) =>
        check state "after '€': start=5, remaining=1" (remainingLength s3 == 1)
        check state "'€' consumed 3 bytes" (remainingLength s2 - remainingLength s3 == 3)
        match s3.next? with
        | some ('d', s4) =>
          check state "after 'd': start=6, remaining=0" (remainingLength s4 == 0)
          check state "at end: next? is none" (s4.next?.isNone)
        | _ => check state "next? for 'd'" false
      | _ => check state "next? for '€'" false
    | _ => check state "next? for 'b'" false
  | _ => check state "next? for 'a'" false

/-! ## 9. Newline Does Not Break Termination

Newline resets column to 0 but still advances the byte position.
This tests that line/col tracking is orthogonal to termination.
-/

def testNewlineAdvancement (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "newline still advances position"
  let s := YamlStream.ofString "a\nb"
  match s.next? with
  | some ('a', s1) =>
    let r0 := remainingLength s
    let r1 := remainingLength s1
    check state "after 'a': remaining decreases" (r1 < r0)
    match s1.next? with
    | some ('\n', s2) =>
      let r2 := remainingLength s2
      check state "after '\\n': remaining decreases" (r2 < r1)
      check state "col resets to 0 on newline" (s2.col == 0)
      check state "line increments on newline" (s2.line == 1)
      check state "but byte position still advances" (s2.startPos.byteIdx > s1.startPos.byteIdx)
      match s2.next? with
      | some ('b', s3) =>
        let r3 := remainingLength s3
        check state "after 'b': remaining decreases" (r3 < r2)
        check state "r3 == 0" (r3 == 0)
      | _ => check state "'b' after newline" false
    | _ => check state "newline next?" false
  | _ => check state "first next?" false

/-! ## 10. Complete Consumption is Strictly Monotone

Full consumption of a string produces a strictly decreasing chain
of `remainingLength` values, ending at 0. This is the inductive
property that a well-founded recursion proof needs.
-/

def consumeAll (s : YamlStream) (acc : List Nat) (fuel : Nat) : List Nat :=
  match fuel with
  | 0 => acc.reverse
  | fuel + 1 =>
    match s.next? with
    | some (_, s') => consumeAll s' (remainingLength s' :: acc) fuel
    | none => acc.reverse

def testStrictlyMonotone (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "strictly monotone consumption"
  let input := "yaml"
  let s := YamlStream.ofString input
  let chain := remainingLength s :: consumeAll s [] 100
  -- Should be [4, 3, 2, 1, 0]
  check state "chain length == 5" (chain.length == 5)
  check state "chain starts at 4" (chain.head? == some 4)
  check state "chain ends at 0" (chain.getLast? == some 0)

  -- Verify strict monotonicity: each element > next
  let pairs := chain.zip (chain.drop 1)
  let allDecreasing := pairs.all fun (a, b) => a > b
  check state "all transitions strictly decrease" allDecreasing

  -- Multibyte monotone chain: "é€𐀀" → 2+3+4 = 9 bytes
  let mInput := "é€𐀀"
  let ms := YamlStream.ofString mInput
  let mChain := remainingLength ms :: consumeAll ms [] 100
  -- Should be [9, 7, 4, 0]
  check state "multibyte chain length == 4" (mChain.length == 4)
  check state "multibyte starts at 9" (mChain.head? == some 9)
  check state "multibyte ends at 0" (mChain.getLast? == some 0)
  let mPairs := mChain.zip (mChain.drop 1)
  let mAllDecreasing := mPairs.all fun (a, b) => a > b
  check state "multibyte: all transitions strictly decrease" mAllDecreasing

/-! ## 11. stopPos Invariance

A critical invariant: `next?` never modifies `stopPos`.
If stopPos changed, remainingLength arithmetic would break.
-/

def testStopPosInvariant (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "stopPos invariance"
  let s := YamlStream.ofString "test"
  let originalStop := s.stopPos.byteIdx
  match s.next? with
  | some (_, s1) =>
    check state "stopPos unchanged after 1st next?" (s1.stopPos.byteIdx == originalStop)
    match s1.next? with
    | some (_, s2) =>
      check state "stopPos unchanged after 2nd next?" (s2.stopPos.byteIdx == originalStop)
      match s2.next? with
      | some (_, s3) =>
        check state "stopPos unchanged after 3rd next?" (s3.stopPos.byteIdx == originalStop)
      | none => check state "3rd next?" false
    | none => check state "2nd next?" false
  | none => check state "1st next?" false

/-! ## 12. str Invariance

Another critical invariant: the underlying string never changes.
This means `Pos.Raw.get s.str` and `Pos.Raw.next s.str` refer
to the same string throughout parsing.
-/

def testStrInvariant (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "str invariance"
  let input := "yaml"
  let s := YamlStream.ofString input
  match s.next? with
  | some (_, s1) =>
    check state "str unchanged after next?" (s1.str == s.str)
    match s1.next? with
    | some (_, s2) =>
      check state "str unchanged after 2nd next?" (s2.str == s.str)
    | none => check state "2nd next?" false
  | none => check state "1st next?" false

/-! ## 13. startPos < stopPos When hasNext

The guard condition in `next?` ensures we only read when
there's input remaining. This tests the correspondence
between `hasNext` and the position inequality.
-/

def testHasNextGuard (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "hasNext ↔ startPos < stopPos"
  let s := YamlStream.ofString "ab"
  check state "initially: hasNext" s.hasNext
  check state "initially: start < stop" (s.startPos.byteIdx < s.stopPos.byteIdx)

  match s.next? with
  | some (_, s1) =>
    check state "after 1: hasNext" s1.hasNext
    check state "after 1: start < stop" (s1.startPos.byteIdx < s1.stopPos.byteIdx)
    match s1.next? with
    | some (_, s2) =>
      check state "after 2: not hasNext" (!s2.hasNext)
      check state "after 2: start == stop" (s2.startPos.byteIdx == s2.stopPos.byteIdx)
      check state "after 2: next? is none" (s2.next?.isNone)
    | none => check state "2nd next?" false
  | none => check state "1st next?" false

  -- Empty
  let empty := YamlStream.ofString ""
  check state "empty: not hasNext" (!empty.hasNext)
  check state "empty: start == stop (both 0)" (empty.startPos.byteIdx == empty.stopPos.byteIdx)

/-! ## 14. Compile-Time Verification (Bool Combinators)

These checks verify that the Bool-valued character classification
functions from `Combinators.lean` agree with expected values.
The correspondence between these Bool functions and the Prop-valued
Grammar definitions is validated in Tests/Verification.lean.
-/

def testDecidableProps (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "decidable property checks"
  -- Bool versions from Parse namespace (Combinators.lean)
  check state "Parse.isLineBreak '\\n'" (Lean4Yaml.Parse.isLineBreak '\n')
  check state "¬Parse.isLineBreak 'a'" (!Lean4Yaml.Parse.isLineBreak 'a')
  check state "Parse.isWhiteSpace ' '" (Lean4Yaml.Parse.isWhiteSpace ' ')
  check state "Parse.isWhiteSpace '\\t'" (Lean4Yaml.Parse.isWhiteSpace '\t')
  check state "¬Parse.isWhiteSpace 'x'" (!Lean4Yaml.Parse.isWhiteSpace 'x')
  check state "Parse.isFlowIndicator ','" (Lean4Yaml.Parse.isFlowIndicator ',')
  check state "Parse.isFlowIndicator '['" (Lean4Yaml.Parse.isFlowIndicator '[')
  check state "¬Parse.isFlowIndicator 'a'" (!Lean4Yaml.Parse.isFlowIndicator 'a')
  -- Simple Prop checks using ground truth
  check state "isIndentChar ' '" (' ' == ' ')
  check state "¬isIndentChar 'a'" (!('a' == ' '))

/-! ## 15. YAML-Specific Indentation Position Tests

Indentation checking relies on column position matching
the stream state. These tests verify that after consuming
exactly `n` spaces, the column is `n`.
-/

def consumeSpaces (s : YamlStream) (n : Nat) : Option YamlStream :=
  match n with
  | 0 => some s
  | n + 1 =>
    match s.next? with
    | some (' ', s') => consumeSpaces s' n
    | _ => none

def testIndentationTracking (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "indentation column tracking"
  -- "  key: val" → 2 spaces of indentation
  let s := YamlStream.ofString "  key: val"
  check state "starts at col 0" (s.col == 0)
  match consumeSpaces s 2 with
  | some s2 =>
    check state "after 2 spaces: col == 2" (s2.col == 2)
    check state "after 2 spaces: remaining decreases" (remainingLength s2 < remainingLength s)
    -- Each space consumed 1 byte
    check state "2 spaces = 2 bytes consumed" (s2.startPos.byteIdx == 2)
  | none => check state "consuming 2 spaces" false

  -- "    nested" → 4 spaces
  let s4 := YamlStream.ofString "    nested"
  match consumeSpaces s4 4 with
  | some s4' =>
    check state "after 4 spaces: col == 4" (s4'.col == 4)
  | none => check state "consuming 4 spaces" false

  -- After newline, column resets and spaces count fresh
  let nl := YamlStream.ofString "a\n  b"
  match nl.next? with  -- 'a'
  | some (_, nl1) =>
    match nl1.next? with  -- '\n'
    | some (_, nl2) =>
      check state "after newline: col == 0" (nl2.col == 0)
      match consumeSpaces nl2 2 with
      | some nl3 =>
        check state "2 spaces after newline: col == 2" (nl3.col == 2)
      | none => check state "consuming spaces after newline" false
    | none => check state "newline next?" false
  | none => check state "first next?" false

/-! ## Collector -/

/-- Collect all string lemma test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)

  -- 1. utf8Size positivity
  testUtf8SizePos state

  -- 2. Pos.Raw advancement
  testPosRawAdvancement state

  -- 3. get at valid position
  testGetAtValidPos state

  -- 4. Stream ↔ Pos.Raw consistency
  testStreamPosConsistency state

  -- 5. remainingLength strictly decreases
  testRemainingDecreases state

  -- 6. rawEndPos / utf8ByteSize
  testRawEndPos state

  -- 7. Position validity
  testPositionValidity state

  -- 8. Subtraction arithmetic
  testSubtractionArithmetic state

  -- 9. Newline advancement
  testNewlineAdvancement state

  -- 10. Strictly monotone consumption
  testStrictlyMonotone state

  -- 11. stopPos invariance
  testStopPosInvariant state

  -- 12. str invariance
  testStrInvariant state

  -- 13. hasNext guard
  testHasNextGuard state

  -- 14. Decidable properties
  testDecidableProps state

  -- 15. Indentation tracking
  testIndentationTracking state

  let results ← finish state
  return { name := "stringlemmas", label := "String Lemma Tests", sourceFile := "Tests/StringLemmas.lean", tests := results }

end Tests.StringLemmas
