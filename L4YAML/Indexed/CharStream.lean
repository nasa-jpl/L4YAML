/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Indexed.Range
import L4YAML.Indexed.TokenStream
import L4YAML.Spec.Types

/-! # `IxCursor input` — position-tracked byte cursor

A cursor that walks across `input : String` in UTF-8 byte steps,
tracking `(offset, line, col)` as a `YamlPos`. Every operation
preserves the bound `pos.offset ≤ input.utf8ByteSize`.

This is the **scanning-side analogue** of `Range input`:

- A `Range input` is a *static* byte interval (a finished span).
- An `IxCursor input` is a *moving* read head (a state during
  scanning).

The Phase 3 Step 2+ scanner is a function of type
`IxCursor input → ... → TokenStream input`, written as a recursive
descent on the cursor, with `IxToken input` values built from
`cursor-before`/`cursor-after` pairs.

## Phase 2 → Phase 3 (Step 1) scope

This file lands the *type and primitive accessors* for `IxCursor`.
Nothing here implements YAML productions or scanning logic — those
arrive in Step 2.

The bound on `advance` is discharged via `Nat.min` so the cursor
can be built without invoking deep stdlib lemmas about
`String.Pos.Raw.next`. Step 2 will refine the bound to use the
sharper stdlib lemma where it pays off.

## Indexing discipline

`input : String` is a type parameter — cursors over different
inputs are different types, so positions cannot be confused at any
stage boundary (D1 from Blueprint 08).
-/

namespace L4YAML.Indexed

open L4YAML

/-- A byte cursor at position `pos` within `input`.

    `pos.offset` is a UTF-8 byte index into `input`; the bound
    `posBound` guarantees the cursor sits at or before the end of
    the string, never past it. `(line, col)` track 0-based line and
    column for token attribution. -/
structure IxCursor (input : String) where
  /-- The cursor's position (offset, line, col). -/
  pos : YamlPos
  /-- Well-formedness: the cursor's byte offset is a valid index
      into `input` (or equal to `input.utf8ByteSize` at end-of-input). -/
  posBound : pos.offset ≤ input.utf8ByteSize
  deriving Repr

namespace IxCursor

/-- The cursor at the start of `input` (offset 0, line 0, col 0). -/
def start (input : String) : IxCursor input where
  pos := ⟨0, 0, 0⟩
  posBound := Nat.zero_le _

/-- The cursor at the end of `input` (offset = `input.utf8ByteSize`).
    Line and column for the end cursor are not generally computable
    without scanning the whole input; we leave them at zero. Code
    that needs accurate end-line/col should obtain it by advancing
    from `start`. -/
def stop (input : String) : IxCursor input where
  pos := { offset := input.utf8ByteSize, line := 0, col := 0 }
  posBound := Nat.le_refl _

/-- Whether the cursor has more input characters to read. -/
@[inline] def hasMore {input : String} (c : IxCursor input) : Bool :=
  c.pos.offset < input.utf8ByteSize

/-- Whether the cursor sits at the end of input. -/
@[inline] def atEnd {input : String} (c : IxCursor input) : Bool :=
  c.pos.offset == input.utf8ByteSize

/-- Peek at the current character without consuming it. Returns
    `none` if the cursor is at end of input. -/
def peek? {input : String} (c : IxCursor input) : Option Char :=
  if c.pos.offset < input.utf8ByteSize then
    some (String.Pos.Raw.get input ⟨c.pos.offset⟩)
  else
    none

/-- Internal: a recursive helper for `peekAt?`. Mirrors the
    pattern of `ScannerState.peekAt?Loop` in the legacy scanner. -/
def peekAt?Loop (input : String) (pos : String.Pos.Raw) (n : Nat) : Option Char :=
  match n with
  | 0 =>
    if pos.byteIdx < input.utf8ByteSize then
      some (String.Pos.Raw.get input pos)
    else
      none
  | n' + 1 =>
    if pos.byteIdx < input.utf8ByteSize then
      peekAt?Loop input (String.Pos.Raw.next input pos) n'
    else
      none

/-- Peek `n` characters ahead of the cursor without consuming.
    Returns `none` if fewer than `n+1` characters remain. -/
def peekAt? {input : String} (c : IxCursor input) (n : Nat) : Option Char :=
  peekAt?Loop input ⟨c.pos.offset⟩ n

/-- Peek at the character immediately *before* the cursor. Used for
    YAML 1.2.2 §6.7 (`#` comment) which requires preceding
    whitespace or start-of-line. Returns `none` at start of input. -/
def peekBack? {input : String} (c : IxCursor input) : Option Char :=
  if c.pos.offset > 0 then
    let prev := String.Pos.Raw.prev input ⟨c.pos.offset⟩
    some (String.Pos.Raw.get input prev)
  else
    none

/-- The next byte offset after the current cursor position, clamped
    to `input.utf8ByteSize`. The `min` makes the bound obligation
    discharge trivially; in practice the unclamped `next` already
    respects the bound when `pos.offset < utf8ByteSize`. -/
@[inline] private def nextOffsetClamped {input : String} (c : IxCursor input) : Nat :=
  Nat.min (String.Pos.Raw.next input ⟨c.pos.offset⟩).byteIdx input.utf8ByteSize

/-- Advance past the current character, updating `(offset, line, col)`.

    - Line breaks (`'\n'` or `'\r'`) reset `col` to `0` and
      increment `line` (matches YAML §5.4 [28] and the legacy
      `ScannerState.advance`).
    - At end-of-input the cursor is returned unchanged.

    The bound is preserved via `Nat.min`. -/
def advance {input : String} (c : IxCursor input) : IxCursor input :=
  if h : c.pos.offset < input.utf8ByteSize then
    let ch := String.Pos.Raw.get input ⟨c.pos.offset⟩
    let next := nextOffsetClamped c
    let (line', col') :=
      if ch == '\n' || ch == '\r' then (c.pos.line + 1, 0) else (c.pos.line, c.pos.col + 1)
    { pos := { offset := next, line := line', col := col' }
      posBound := by
        show Nat.min _ _ ≤ input.utf8ByteSize
        exact Nat.min_le_right _ _ }
  else
    c

/-- Advance `n` characters. Structurally recursive on `n`. -/
def advanceN {input : String} (c : IxCursor input) : Nat → IxCursor input
  | 0      => c
  | n' + 1 => advanceN c.advance n'

/-! ## Cursor ↔ Range bridge

The byte interval traversed between two ordered cursors forms a
`Range input`. This is the constructor the scanner uses to attach
a `range` to each emitted token / sub-graph. -/

/-- Build a `Range input` from two cursors `c₁ ≤ c₂` (by `offset`).
    Caller must supply the ordering proof. -/
def rangeBetween {input : String} (c₁ c₂ : IxCursor input)
    (hOrder : c₁.pos.offset ≤ c₂.pos.offset) : Range input where
  start := c₁.pos.offset
  stop  := c₂.pos.offset
  startLEStop := hOrder
  stopLEInput := c₂.posBound

/-- The zero-width range at the cursor's current position. -/
def pointRange {input : String} (c : IxCursor input) : Range input :=
  Range.point input c.pos.offset c.posBound

/-! ## Cursor ↔ IxToken bridge

Tokens are produced from a pair of cursors `(before, after)` and a
`YamlToken` value. The bound proof is discharged from `after`'s
`posBound`. -/

/-- Build an `IxToken input` from a *before* cursor, a token value,
    and an *after* cursor. The ordering `before.pos.offset ≤
    after.pos.offset` must be supplied (typically by construction,
    e.g. `after = before.advance ∘ … ∘ before.advance`). -/
def emitToken {input : String} (before after : IxCursor input)
    (token : YamlToken)
    (hOrder : before.pos.offset ≤ after.pos.offset) : IxToken input :=
  IxToken.mk' (input := input) before.pos token after.pos hOrder after.posBound

/-! ## Basic lemmas

These are the obvious sanity facts about `start`, `peek?`, `advance`
that the Step 2 scanner will rely on. We keep the corpus small —
non-obvious facts (e.g., monotonicity of `advance` on `offset`)
arrive alongside their use sites in Step 2. -/

@[simp] theorem pos_start (input : String) :
    (start input).pos = ⟨0, 0, 0⟩ := rfl

@[simp] theorem offset_start (input : String) :
    (start input).pos.offset = 0 := rfl

@[simp] theorem peek?_start_empty :
    peek? (start "") = none := by
  simp [peek?, start]

@[simp] theorem advanceN_zero {input : String} (c : IxCursor input) :
    advanceN c 0 = c := rfl

@[simp] theorem hasMore_iff {input : String} (c : IxCursor input) :
    c.hasMore = true ↔ c.pos.offset < input.utf8ByteSize := by
  simp [hasMore]

@[simp] theorem peek?_eq_none_iff {input : String} (c : IxCursor input) :
    c.peek? = none ↔ input.utf8ByteSize ≤ c.pos.offset := by
  unfold peek?
  split <;> rename_i h <;> simp <;> omega

/-- `advance` at end-of-input is a no-op. -/
theorem advance_atEnd {input : String} (c : IxCursor input)
    (h : ¬ c.pos.offset < input.utf8ByteSize) :
    c.advance = c := by
  unfold advance
  simp [h]

/-- `advance` strictly increases the byte offset when the cursor has
    more input. Proof uses `String.Pos.Raw.byteIdx_lt_byteIdx_next`
    (stdlib) plus the `Nat.min` clamp. -/
theorem advance_offset_lt_of_hasMore {input : String} (c : IxCursor input)
    (h : c.pos.offset < input.utf8ByteSize) :
    c.pos.offset < c.advance.pos.offset := by
  have hnext : c.pos.offset < (String.Pos.Raw.next input ⟨c.pos.offset⟩).byteIdx :=
    String.Pos.Raw.byteIdx_lt_byteIdx_next input ⟨c.pos.offset⟩
  unfold advance nextOffsetClamped
  simp only [dif_pos h, Nat.min_def]
  split <;> omega

/-- `advance` is monotonic on the byte offset (whether or not at end). -/
theorem advance_offset_monotonic {input : String} (c : IxCursor input) :
    c.pos.offset ≤ c.advance.pos.offset := by
  by_cases h : c.pos.offset < input.utf8ByteSize
  · exact Nat.le_of_lt (advance_offset_lt_of_hasMore c h)
  · rw [advance_atEnd c h]; exact Nat.le_refl _

end IxCursor

end L4YAML.Indexed
