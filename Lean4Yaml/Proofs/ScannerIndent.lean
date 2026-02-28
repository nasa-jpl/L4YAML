import Lean4Yaml.Scanner

/-!
# Scanner Indentation Proofs (Layer 2c — Tokenized Parser)

This module proves that `ScannerState.advance` correctly tracks column
and line positions, and that `skipSpaces` advances the column by the
number of spaces consumed.

Replaces `IndentConsumption.lean` (P10.5), which proved the same
properties for the old character-level parser.

## Key Results

1. **`advance_space_col`**: When `advance` consumes a space, `col`
   increases by exactly 1 and `line` stays the same.

2. **`advance_nonNewline_col`**: When `advance` consumes any non-newline
   character, `col` increases by 1.

3. **`advance_newline_col`**: When `advance` consumes a newline, `col`
   resets to 0 and `line` increments by 1.

4. **`advanceN_spaces_col`**: After advancing over `n` consecutive space
   characters, `col` increases by exactly `n`.

5. **`skipSpaces` specification guards**: Compile-time `#guard` checks
   verify that `skipSpaces` advances the column correctly.

## Strategy

The proofs operate directly on `ScannerState.advance`, which computes:
```
if c == '\n' then { s with col := 0, line := s.line + 1 }
else              { s with col := s.col + 1 }
```
This is a pure state transformation — no monad, no fuel, no backtracking.
-/

namespace Lean4Yaml.Proofs.ScannerIndent

open Lean4Yaml.Scanner

/-! ## §1: Single Character Column Advancement

`ScannerState.advance` reads the character at `offset`, updates `col`
based on whether it's a newline, and moves `offset` to the next byte position.
-/

/-- Helper: space is not newline. -/
private theorem space_ne_newline : (' ' : Char) ≠ '\n' := by decide

/--
When the current character is a space, `advance` increases `col` by 1.
Requires the offset to be within bounds (not at end of input).
-/
theorem advance_space_col (s : ScannerState)
    (hBounds : s.offset < s.inputEnd)
    (hChar : String.Pos.Raw.get s.input ⟨s.offset⟩ = ' ') :
    s.advance.col = s.col + 1 := by
  unfold ScannerState.advance
  simp [hBounds, hChar]

/--
When the current character is a space, `advance` preserves `line`.
-/
theorem advance_space_line (s : ScannerState)
    (hBounds : s.offset < s.inputEnd)
    (hChar : String.Pos.Raw.get s.input ⟨s.offset⟩ = ' ') :
    s.advance.line = s.line := by
  unfold ScannerState.advance
  simp [hBounds, hChar]

/--
When the current character is not a newline, `advance` increases `col` by 1.
-/
theorem advance_nonNewline_col (s : ScannerState)
    (hBounds : s.offset < s.inputEnd)
    (hNotNl : String.Pos.Raw.get s.input ⟨s.offset⟩ ≠ '\n') :
    s.advance.col = s.col + 1 := by
  unfold ScannerState.advance
  simp only [hBounds]
  have : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = false :=
    Bool.eq_false_iff.mpr (by simpa using hNotNl)
  simp [this]

/--
When the current character is not a newline, `advance` preserves `line`.
-/
theorem advance_nonNewline_line (s : ScannerState)
    (hBounds : s.offset < s.inputEnd)
    (hNotNl : String.Pos.Raw.get s.input ⟨s.offset⟩ ≠ '\n') :
    s.advance.line = s.line := by
  unfold ScannerState.advance
  simp only [hBounds]
  have : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = false :=
    Bool.eq_false_iff.mpr (by simpa using hNotNl)
  simp [this]

/--
When the current character is a newline, `advance` resets `col` to 0.
-/
theorem advance_newline_col (s : ScannerState)
    (hBounds : s.offset < s.inputEnd)
    (hNl : String.Pos.Raw.get s.input ⟨s.offset⟩ = '\n') :
    s.advance.col = 0 := by
  unfold ScannerState.advance
  simp [hBounds, hNl]

/--
When the current character is a newline, `advance` increments `line` by 1.
-/
theorem advance_newline_line (s : ScannerState)
    (hBounds : s.offset < s.inputEnd)
    (hNl : String.Pos.Raw.get s.input ⟨s.offset⟩ = '\n') :
    s.advance.line = s.line + 1 := by
  unfold ScannerState.advance
  simp [hBounds, hNl]

/--
When offset is at or past end, `advance` is the identity.
-/
theorem advance_at_end (s : ScannerState)
    (hEnd : ¬ (s.offset < s.inputEnd)) :
    s.advance = s := by
  unfold ScannerState.advance
  simp [hEnd]

/-! ## §2: Iterated Space Consumption

We define `AdvancedNSpaces n s s'` capturing `n` consecutive advances
over space characters, and prove it advances the column by exactly `n`.
-/

/--
`AdvancedNSpaces n s s'` means advancing `n` times from `s`, with each
position containing a space character, yields `s'`.
-/
inductive AdvancedNSpaces : Nat → ScannerState → ScannerState → Prop where
  | zero (s : ScannerState) : AdvancedNSpaces 0 s s
  | step (n : Nat) (s s' : ScannerState)
      (hBounds : s.offset < s.inputEnd)
      (hChar : String.Pos.Raw.get s.input ⟨s.offset⟩ = ' ')
      (hRest : AdvancedNSpaces n s.advance s') :
      AdvancedNSpaces (n + 1) s s'

/--
After advancing over `n` consecutive spaces, `col` increases by exactly `n`.
-/
theorem advanceN_spaces_col (n : Nat) (s s' : ScannerState)
    (h : AdvancedNSpaces n s s') : s'.col = s.col + n := by
  induction h with
  | zero => omega
  | step n s s' hBounds hChar _hRest ih =>
    have hCol := advance_space_col s hBounds hChar
    omega

/--
After advancing over `n` consecutive spaces, `line` stays the same.
-/
theorem advanceN_spaces_line (n : Nat) (s s' : ScannerState)
    (h : AdvancedNSpaces n s s') : s'.line = s.line := by
  induction h with
  | zero => rfl
  | step n s s' hBounds hChar _hRest ih =>
    have hLine := advance_space_line s hBounds hChar
    omega

/-! ## §3: `skipSpaces` Specification Guards

Compile-time `#guard` checks verify that `skipSpaces` advances `col`
by the number of leading spaces, using the scanner's actual implementation.
-/

/-- Helper: create a scanner state from a string and check col after skipSpaces -/
private def skipSpacesCol (input : String) : Nat :=
  (skipSpaces (ScannerState.mk' input)).col

-- skipSpaces on no spaces → col stays at 0
#guard skipSpacesCol "hello" == 0

-- skipSpaces on 1 space → col = 1
#guard skipSpacesCol " hello" == 1

-- skipSpaces on 2 spaces → col = 2
#guard skipSpacesCol "  hello" == 2

-- skipSpaces on 4 spaces → col = 4
#guard skipSpacesCol "    hello" == 4

-- skipSpaces on 8 spaces → col = 8
#guard skipSpacesCol "        hello" == 8

-- skipSpaces stops at tab (not a space)
#guard skipSpacesCol "\thello" == 0

-- skipSpaces on empty string → col = 0
#guard skipSpacesCol "" == 0

-- skipSpaces on all spaces → col = length
#guard skipSpacesCol "   " == 3

-- advance column tracking: non-newline increments
#guard (ScannerState.mk' "abc").advance.col == 1
#guard (ScannerState.mk' "abc").advance.advance.col == 2

-- advance column tracking: newline resets
#guard (ScannerState.mk' "a\nb").advance.advance.col == 0
#guard (ScannerState.mk' "a\nb").advance.advance.line == 1
#guard (ScannerState.mk' "a\nb").advance.advance.advance.col == 1

end Lean4Yaml.Proofs.ScannerIndent
