import Lean4Yaml.Scanner
import Lean4Yaml.Proofs.ScannerLoopInvariant

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scanner Whitespace & Navigation Proofs (P10.10a)

Machine-checked proofs that the scanner's whitespace consumption and
navigation functions preserve the `WellFormed` invariant.

## Scope

Five functions are covered:
- `consumeNewline` — non-looping, 1–2 `advance` calls + `needIndentCheck`
- `skipWhitespace` — loops over `advance` while `isWhiteSpace`
- `skipSpaces` — loops over `advance` while `' '`
- `skipToEndOfLine` — loops over `advance` until line break
- `advanceN` — loops `advance` exactly `n` times

## Strategy

Each function modifies the scanner state only via `advance` (which
preserves `indents`, `flowLevel`, `flowStack`, `simpleKeyStack`, and
`inputEnd`) and `{ s with needIndentCheck := true }` (which preserves
all `WellFormed` fields).

For `consumeNewline`, we give full universal theorems by case analysis.
For the looping functions, we provide comprehensive `#guard` validation
on concrete inputs covering all four `WellFormed` conjuncts and edge
cases.  Universal loop proofs (requiring `Nat.fold` induction over
`Id.run do for _ in [:n]`) will be developed as reusable infrastructure
in a follow-up.

## Zero Axioms

All theorems are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.ScannerWhitespace

open Lean4Yaml.Scanner
open Lean4Yaml.Proofs.ScannerLoopInvariant

/-! ## §1  consumeNewline — Field Preservation (universal)

`consumeNewline` matches on `peek?` and applies 1–2 `advance` calls
plus `{ s with needIndentCheck := true }`.  The `with` record update
only modifies `needIndentCheck`, preserving all `WellFormed` fields.

Structure:
```
match s.peek? with
| some '\n' => { s.advance with needIndentCheck := true }
| some '\r' =>
    let s' := s.advance
    match s'.peek? with
    | some '\n' => { s'.advance with needIndentCheck := true }
    | _ => { s' with needIndentCheck := true }
| _ => s
```
-/

/-- `consumeNewline` preserves `indents` (universal). -/
theorem consumeNewline_preserves_indents (s : ScannerState) :
    (consumeNewline s).indents = s.indents := by
  unfold consumeNewline
  split
  · -- some '\n' => { s.advance with needIndentCheck := true }
    exact advance_indents s
  · -- some '\r' => let s' := s.advance; match s'.peek? with ...
    dsimp only []
    split
    · -- s.advance.peek? = some '\n'
      rw [advance_indents, advance_indents]
    · -- _ => { s.advance with needIndentCheck := true }
      exact advance_indents s
  · -- _ => s
    rfl

/-- `consumeNewline` preserves `flowLevel` (universal). -/
theorem consumeNewline_preserves_flowLevel (s : ScannerState) :
    (consumeNewline s).flowLevel = s.flowLevel := by
  unfold consumeNewline
  split
  · exact advance_flowLevel s
  · dsimp only []
    split
    · rw [advance_flowLevel, advance_flowLevel]
    · exact advance_flowLevel s
  · rfl

/-- `consumeNewline` preserves `flowStack` (universal). -/
theorem consumeNewline_preserves_flowStack (s : ScannerState) :
    (consumeNewline s).flowStack = s.flowStack := by
  unfold consumeNewline
  split
  · exact advance_flowStack s
  · dsimp only []
    split
    · rw [advance_flowStack, advance_flowStack]
    · exact advance_flowStack s
  · rfl

/-- `consumeNewline` preserves `simpleKeyStack` (universal). -/
theorem consumeNewline_preserves_simpleKeyStack (s : ScannerState) :
    (consumeNewline s).simpleKeyStack = s.simpleKeyStack := by
  unfold consumeNewline
  split
  · exact advance_simpleKeyStack s
  · dsimp only []
    split
    · rw [advance_simpleKeyStack, advance_simpleKeyStack]
    · exact advance_simpleKeyStack s
  · rfl

/-- `consumeNewline` preserves `inputEnd` (universal). -/
theorem consumeNewline_preserves_inputEnd (s : ScannerState) :
    (consumeNewline s).inputEnd = s.inputEnd := by
  unfold consumeNewline
  split
  · exact advance_inputEnd s
  · dsimp only []
    split
    · rw [advance_inputEnd, advance_inputEnd]
    · exact advance_inputEnd s
  · rfl

/-- `consumeNewline` preserves `input` (universal). -/
theorem consumeNewline_preserves_input (s : ScannerState) :
    (consumeNewline s).input = s.input := by
  unfold consumeNewline
  split
  · exact advance_input s
  · dsimp only []
    split
    · rw [advance_input, advance_input]
    · exact advance_input s
  · rfl

/-! ## §2  consumeNewline — WellFormed Preservation (concrete)

Concrete `#guard` checks validate all four `WellFormed` conjuncts
on representative inputs: LF, CR, CRLF, non-newline, empty, boundary.
-/

-- LF at start
#guard (consumeNewline (ScannerState.mk' "\nabc")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\nabc")).flowLevel ==
       (consumeNewline (ScannerState.mk' "\nabc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "\nabc")).simpleKeyStack.size ==
       (consumeNewline (ScannerState.mk' "\nabc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "\nabc")).offset ≤
       (consumeNewline (ScannerState.mk' "\nabc")).inputEnd

-- CR at start
#guard (consumeNewline (ScannerState.mk' "\rabc")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\rabc")).flowLevel ==
       (consumeNewline (ScannerState.mk' "\rabc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "\rabc")).offset ≤
       (consumeNewline (ScannerState.mk' "\rabc")).inputEnd

-- CRLF at start
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).flowLevel ==
       (consumeNewline (ScannerState.mk' "\r\nabc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).offset ≤
       (consumeNewline (ScannerState.mk' "\r\nabc")).inputEnd

-- Non-newline: identity
#guard (consumeNewline (ScannerState.mk' "abc")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "abc")).flowLevel ==
       (consumeNewline (ScannerState.mk' "abc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "abc")).offset ≤
       (consumeNewline (ScannerState.mk' "abc")).inputEnd

-- Empty: identity
#guard (consumeNewline (ScannerState.mk' "")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "")).offset ≤
       (consumeNewline (ScannerState.mk' "")).inputEnd

-- LF only (no content after)
#guard (consumeNewline (ScannerState.mk' "\n")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\n")).offset ≤
       (consumeNewline (ScannerState.mk' "\n")).inputEnd

-- CR only (no content after)
#guard (consumeNewline (ScannerState.mk' "\r")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\r")).offset ≤
       (consumeNewline (ScannerState.mk' "\r")).inputEnd

/-! ## §3  skipWhitespace — WellFormed Preservation (concrete)

`skipWhitespace` loops via `for _ in [:fuel] do`, applying `advance`
while `isWhiteSpace` holds.  Each iteration only calls `advance`.
-/

-- C1: indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "  ")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "  abc")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "\t\t")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' " \t abc")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "abc")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "\t日本")).indents.size ≥ 1

-- C2: flowLevel == flowStack.size
#guard (skipWhitespace (ScannerState.mk' "")).flowLevel ==
       (skipWhitespace (ScannerState.mk' "")).flowStack.size
#guard (skipWhitespace (ScannerState.mk' "  abc")).flowLevel ==
       (skipWhitespace (ScannerState.mk' "  abc")).flowStack.size
#guard (skipWhitespace (ScannerState.mk' "\t\tabc")).flowLevel ==
       (skipWhitespace (ScannerState.mk' "\t\tabc")).flowStack.size

-- C3: simpleKeyStack.size == flowStack.size
#guard (skipWhitespace (ScannerState.mk' "")).simpleKeyStack.size ==
       (skipWhitespace (ScannerState.mk' "")).flowStack.size
#guard (skipWhitespace (ScannerState.mk' "  abc")).simpleKeyStack.size ==
       (skipWhitespace (ScannerState.mk' "  abc")).flowStack.size

-- C4: offset ≤ inputEnd
#guard (skipWhitespace (ScannerState.mk' "")).offset ≤
       (skipWhitespace (ScannerState.mk' "")).inputEnd
#guard (skipWhitespace (ScannerState.mk' "  abc")).offset ≤
       (skipWhitespace (ScannerState.mk' "  abc")).inputEnd
#guard (skipWhitespace (ScannerState.mk' "  ")).offset ≤
       (skipWhitespace (ScannerState.mk' "  ")).inputEnd
#guard (skipWhitespace (ScannerState.mk' "\t\t\tabc")).offset ≤
       (skipWhitespace (ScannerState.mk' "\t\t\tabc")).inputEnd
#guard (skipWhitespace (ScannerState.mk' "\t日本")).offset ≤
       (skipWhitespace (ScannerState.mk' "\t日本")).inputEnd

-- Stops at newline (newline is not s-white)
#guard (skipWhitespace (ScannerState.mk' "  \nabc")).offset ==
       (ScannerState.mk' "  \nabc").advance.advance.offset

/-! ## §4  skipSpaces — WellFormed Preservation (concrete) -/

-- C1: indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' "")).indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' "   ")).indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' "  abc")).indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' "abc")).indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' " \tab")).indents.size ≥ 1

-- C2: flowLevel == flowStack.size
#guard (skipSpaces (ScannerState.mk' "")).flowLevel ==
       (skipSpaces (ScannerState.mk' "")).flowStack.size
#guard (skipSpaces (ScannerState.mk' "  abc")).flowLevel ==
       (skipSpaces (ScannerState.mk' "  abc")).flowStack.size

-- C3: simpleKeyStack.size == flowStack.size
#guard (skipSpaces (ScannerState.mk' "")).simpleKeyStack.size ==
       (skipSpaces (ScannerState.mk' "")).flowStack.size
#guard (skipSpaces (ScannerState.mk' "  abc")).simpleKeyStack.size ==
       (skipSpaces (ScannerState.mk' "  abc")).flowStack.size

-- C4: offset ≤ inputEnd
#guard (skipSpaces (ScannerState.mk' "")).offset ≤
       (skipSpaces (ScannerState.mk' "")).inputEnd
#guard (skipSpaces (ScannerState.mk' "  abc")).offset ≤
       (skipSpaces (ScannerState.mk' "  abc")).inputEnd
#guard (skipSpaces (ScannerState.mk' "   ")).offset ≤
       (skipSpaces (ScannerState.mk' "   ")).inputEnd
#guard (skipSpaces (ScannerState.mk' " \tab")).offset ≤
       (skipSpaces (ScannerState.mk' " \tab")).inputEnd

-- Stops at tab
#guard (skipSpaces (ScannerState.mk' " \tabc")).offset ==
       (ScannerState.mk' " \tabc").advance.offset

/-! ## §5  skipToEndOfLine — WellFormed Preservation (concrete) -/

-- C1: indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "")).indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "abcdef")).indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "\nabc")).indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "日本\n語")).indents.size ≥ 1

-- C2: flowLevel == flowStack.size
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).flowLevel ==
       (skipToEndOfLine (ScannerState.mk' "abc\ndef")).flowStack.size
#guard (skipToEndOfLine (ScannerState.mk' "abcdef")).flowLevel ==
       (skipToEndOfLine (ScannerState.mk' "abcdef")).flowStack.size

-- C3: simpleKeyStack.size == flowStack.size
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).simpleKeyStack.size ==
       (skipToEndOfLine (ScannerState.mk' "abc\ndef")).flowStack.size

-- C4: offset ≤ inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "")).inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "abc\ndef")).inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "abcdef")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "abcdef")).inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "\nabc")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "\nabc")).inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "日本\n語")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "日本\n語")).inputEnd

-- Immediate newline: no movement
#guard (skipToEndOfLine (ScannerState.mk' "\nabc")).offset == 0

-- CR
#guard (skipToEndOfLine (ScannerState.mk' "abc\rdef")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "abc\rdef")).inputEnd

/-! ## §6  advanceN — WellFormed Preservation (concrete) -/

-- advanceN 0 is identity
#guard ((ScannerState.mk' "abc").advanceN 0).indents.size ≥ 1
#guard ((ScannerState.mk' "abc").advanceN 0).offset ≤
       ((ScannerState.mk' "abc").advanceN 0).inputEnd

-- advanceN within bounds
#guard ((ScannerState.mk' "abcdef").advanceN 3).indents.size ≥ 1
#guard ((ScannerState.mk' "abcdef").advanceN 3).flowLevel ==
       ((ScannerState.mk' "abcdef").advanceN 3).flowStack.size
#guard ((ScannerState.mk' "abcdef").advanceN 3).simpleKeyStack.size ==
       ((ScannerState.mk' "abcdef").advanceN 3).flowStack.size
#guard ((ScannerState.mk' "abcdef").advanceN 3).offset ≤
       ((ScannerState.mk' "abcdef").advanceN 3).inputEnd

-- advanceN past end: clamped
#guard ((ScannerState.mk' "ab").advanceN 10).indents.size ≥ 1
#guard ((ScannerState.mk' "ab").advanceN 10).offset ≤
       ((ScannerState.mk' "ab").advanceN 10).inputEnd

-- Multi-byte
#guard ((ScannerState.mk' "αβγ").advanceN 2).indents.size ≥ 1
#guard ((ScannerState.mk' "αβγ").advanceN 2).offset ≤
       ((ScannerState.mk' "αβγ").advanceN 2).inputEnd

-- Across newlines
#guard ((ScannerState.mk' "a\nb\nc").advanceN 4).indents.size ≥ 1
#guard ((ScannerState.mk' "a\nb\nc").advanceN 4).offset ≤
       ((ScannerState.mk' "a\nb\nc").advanceN 4).inputEnd

/-! ## §7  Behavioral Guards — Functional Correctness

Verify the *behavior* of the whitespace functions, not just WellFormed.
-/

-- skipWhitespace advances past all s-white characters
#guard (skipWhitespace (ScannerState.mk' "  abc")).col == 2
#guard (skipWhitespace (ScannerState.mk' "\t abc")).col == 2
#guard (skipWhitespace (ScannerState.mk' "abc")).col == 0

-- skipSpaces advances past spaces only (stops at tab)
#guard (skipSpaces (ScannerState.mk' "  abc")).col == 2
#guard (skipSpaces (ScannerState.mk' " \tabc")).col == 1
#guard (skipSpaces (ScannerState.mk' "\tabc")).col == 0

-- skipToEndOfLine advances to line break
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).col == 3
#guard (skipToEndOfLine (ScannerState.mk' "\nabc")).col == 0
#guard (skipToEndOfLine (ScannerState.mk' "abcdef")).col == 6

-- consumeNewline line tracking
#guard (consumeNewline (ScannerState.mk' "\nabc")).line == 1
#guard (consumeNewline (ScannerState.mk' "\nabc")).col == 0
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).line == 1
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).col == 0
#guard (consumeNewline (ScannerState.mk' "\rabc")).line == 0  -- CR alone: advance doesn't bump line
#guard (consumeNewline (ScannerState.mk' "abc")).line == 0
#guard (consumeNewline (ScannerState.mk' "abc")).col == 0

-- advanceN position tracking
#guard ((ScannerState.mk' "abcdef").advanceN 3).col == 3
#guard ((ScannerState.mk' "abcdef").advanceN 3).offset == 3
#guard ((ScannerState.mk' "ab").advanceN 10).offset == 2

end Lean4Yaml.Proofs.ScannerWhitespace
