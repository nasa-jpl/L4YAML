import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators

/-!
# Indentation Consumption Proofs (Layer 2c)

This module proves that consuming indentation via `YamlStream.next?` advances
the column by exactly the right amount.

## Key Results

1. **`next_space_col`**: When `next?` consumes a space character, `col`
   increases by exactly 1 and `line` stays the same.

2. **`next_nonNewline_col`**: When `next?` consumes any non-newline character,
   `col` increases by 1.

3. **`next_newline_col`**: When `next?` consumes a newline, `col` resets to 0
   and `line` increments by 1.

4. **`next_n_spaces_col`**: After consuming `n` consecutive space characters,
   `col` increases by exactly `n`.

5. **`consumeIndent` specification guards**: Compile-time `#guard` checks
   verify that `consumeIndent n` advances the column by exactly `n` when
   parsing `n` spaces.

## Strategy

The stream-level theorems operate on the pure `YamlStream.next?` function,
avoiding the parser monad entirely. Since `consumeIndent n` = `drop n (token ' ')`
and `drop n` calls `next?` exactly `n` times (each time verifying the token is
`' '`), the column advancement follows from the stream-level property.

The parser-level verification uses `#guard` checks that run the full parser
and compare column values before and after.
-/

namespace Lean4Yaml.Proofs.IndentConsumption

open Lean4Yaml

/-! ## §1: Single Character Column Advancement

The `YamlStream.next?` function computes:
```
if c == '\n' then (line + 1, 0) else (line, col + 1)
```
We prove that this correctly tracks column for spaces, non-newlines,
and newlines. Each proof unfolds `next?`, extracts the character
identity from the `some` injection, and simplifies the `if` branch.
-/

/-- Helper: space is not newline. Used to resolve `if` branches. -/
private theorem space_ne_newline : (' ' : Char) ≠ '\n' := by decide

/--
When `next?` consumes a space, the column increases by 1.
-/
theorem next_space_col (s : YamlStream) (s' : YamlStream)
    (h : s.next? = some (' ', s')) : s'.col = s.col + 1 := by
  unfold YamlStream.next? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hc, hs'⟩ := h
    rw [← hs']; simp [hc]
  · contradiction

/--
When `next?` consumes a space, the line stays the same.
-/
theorem next_space_line (s : YamlStream) (s' : YamlStream)
    (h : s.next? = some (' ', s')) : s'.line = s.line := by
  unfold YamlStream.next? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hc, hs'⟩ := h
    rw [← hs']; simp [hc]
  · contradiction

/--
When `next?` consumes any non-newline character, the column increases by 1.
This generalizes `next_space_col` to all non-newline characters.
-/
theorem next_nonNewline_col (s : YamlStream) (c : Char) (s' : YamlStream)
    (h : s.next? = some (c, s')) (hNotNl : c ≠ '\n') :
    s'.col = s.col + 1 := by
  unfold YamlStream.next? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hc, hs'⟩ := h
    rw [← hs']; simp [hc, show (c == '\n') = false from by simpa using hNotNl]
  · contradiction

/--
When `next?` consumes any non-newline character, the line stays the same.
-/
theorem next_nonNewline_line (s : YamlStream) (c : Char) (s' : YamlStream)
    (h : s.next? = some (c, s')) (hNotNl : c ≠ '\n') :
    s'.line = s.line := by
  unfold YamlStream.next? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hc, hs'⟩ := h
    rw [← hs']; simp [hc, show (c == '\n') = false from by simpa using hNotNl]
  · contradiction

/--
When `next?` consumes a newline character, the column resets to 0.
-/
theorem next_newline_col (s : YamlStream) (s' : YamlStream)
    (h : s.next? = some ('\n', s')) : s'.col = 0 := by
  unfold YamlStream.next? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hc, hs'⟩ := h
    rw [← hs']; simp [hc]
  · contradiction

/--
When `next?` consumes a newline character, the line increments by 1.
-/
theorem next_newline_line (s : YamlStream) (s' : YamlStream)
    (h : s.next? = some ('\n', s')) : s'.line = s.line + 1 := by
  unfold YamlStream.next? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hc, hs'⟩ := h
    rw [← hs']; simp [hc]
  · contradiction

/-! ## §2: Iterated Space Consumption

We define a relation `NextNSpaces n s s'` capturing `n` consecutive
space characters consumed from `s` to reach `s'`, and prove it advances
the column by exactly `n`.
-/

/--
`NextNSpaces n s s'` means consuming `n` consecutive space characters
from stream `s` yields stream `s'`. Models the effect of `drop n (token ' ')`.
-/
inductive NextNSpaces : Nat → YamlStream → YamlStream → Prop where
  | zero (s : YamlStream) : NextNSpaces 0 s s
  | step (n : Nat) (s s₁ s' : YamlStream)
      (hStep : s.next? = some (' ', s₁))
      (hRest : NextNSpaces n s₁ s') :
      NextNSpaces (n + 1) s s'

/--
After consuming `n` consecutive spaces, the column increases by exactly `n`.
-/
theorem next_n_spaces_col (n : Nat) (s s' : YamlStream)
    (h : NextNSpaces n s s') : s'.col = s.col + n := by
  induction h with
  | zero => omega
  | step n s s₁ s' hStep _hRest ih =>
    have hCol := next_space_col s s₁ hStep
    omega

/--
After consuming `n` consecutive spaces, the line stays the same.
-/
theorem next_n_spaces_line (n : Nat) (s s' : YamlStream)
    (h : NextNSpaces n s s') : s'.line = s.line := by
  induction h with
  | zero => rfl
  | step n s s₁ s' hStep _hRest ih =>
    have hLine := next_space_line s s₁ hStep
    omega

/-! ## §3: Stream Invariant Preservation

Consuming spaces preserves the non-positional stream state
(anchor map, validation error, tag handles).
-/

/--
Consuming a space preserves the anchor map.
-/
theorem next_space_preserves_anchorMap (s s' : YamlStream)
    (h : s.next? = some (' ', s')) : s'.anchorMap = s.anchorMap := by
  unfold YamlStream.next? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hs'⟩ := h
    rw [← hs']
  · contradiction

/--
Consuming a space preserves the validation error.
-/
theorem next_space_preserves_validationError (s s' : YamlStream)
    (h : s.next? = some (' ', s')) : s'.validationError = s.validationError := by
  unfold YamlStream.next? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hs'⟩ := h
    rw [← hs']
  · contradiction

/-! ## §4: `consumeIndent` Specification Guards

These compile-time `#guard` checks verify that the full parser
`consumeIndent n` advances the column by exactly `n`. They exercise
the complete parser pipeline including the tab check, `drop n (token ' ')`,
and the error wrapping.
-/

open Lean4Yaml.Parse in
/-- Run a parser on a string and return (col_before, col_after) or none on failure. -/
private def runColTest (n : Nat) (input : String) : Option (Nat × Nat) :=
  let stream := YamlStream.ofString input
  match Parser.run (do
    let colBefore ← currentCol
    consumeIndent n
    let colAfter ← currentCol
    return (colBefore, colAfter)
  ) stream with
  | .ok _ pair => some pair
  | .error _ _ => none

-- consumeIndent 0 is a no-op (col stays at 0)
#guard runColTest 0 "hello" == some (0, 0)

-- consumeIndent 1 advances column by 1
#guard runColTest 1 " hello" == some (0, 1)

-- consumeIndent 2 advances column by 2
#guard runColTest 2 "  hello" == some (0, 2)

-- consumeIndent 4 advances column by 4
#guard runColTest 4 "    hello" == some (0, 4)

-- consumeIndent 8 advances column by 8
#guard runColTest 8 "        hello" == some (0, 8)

-- consumeIndent 3 fails with only 2 spaces
#guard runColTest 3 "  hello" == none

-- consumeIndent fails with tab (§6.1 tab rejection)
#guard runColTest 1 "\thello" == none

-- consumeIndent 0 succeeds even at EOF
#guard runColTest 0 "" == some (0, 0)

-- consumeIndent 1 fails at EOF
#guard runColTest 1 "" == none

end Lean4Yaml.Proofs.IndentConsumption
