import L4YAML.Scanner

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scanner Loop Invariant (P10.8f.1)

Machine-checked proof that `ScannerState.advance` preserves the
`WellFormed` offset bound, provided the scanner offset corresponds to a
valid UTF-8 character boundary.

## Key Result

`advance_preserves_offset_bound`: When the scanner is at a valid UTF-8
position with `offset < inputEnd`, advancing to the next character keeps
`offset ≤ inputEnd`.  This is the critical loop-invariant lemma that
underpins all scanner progress arguments.

## Architecture

The proof decomposes into four layers:

1. **`utf8ByteSize_eq_sum`** — connects `String.utf8ByteSize` (byte-array
   level) to `(s.toList.map Char.utf8Size).sum` (character-list level).

2. **`utf8GetAux_skip`** — induction lemma: scanning `utf8GetAux` past a
   prefix list of characters skips to the suffix.

3. **`utf8GetAux_head`** — base case: `utf8GetAux (c :: cs) i i = c`.

4. **`raw_next_le_utf8ByteSize`** — combines the above via
   `isValid_iff_exists_append` string decomposition to show
   `(Raw.next s p).byteIdx ≤ s.utf8ByteSize`.

## Zero Axioms

All theorems are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace L4YAML.Proofs.ScannerLoopInvariant

open L4YAML.Scanner

/-! ## §1  UTF-8 Byte Size ↔ Character Size Sum

The fundamental bridge between the byte-array representation (`utf8ByteSize`)
and the character-list representation (`toList.map Char.utf8Size`).
-/

/-- For a string constructed from a character list, `utf8ByteSize` equals
    the sum of individual character byte widths. -/
theorem utf8ByteSize_eq_sum_aux (cs : List Char) :
    (String.ofList cs).utf8ByteSize = (cs.map Char.utf8Size).sum := by
  show (cs.flatMap String.utf8EncodeChar).toByteArray.size = (cs.map Char.utf8Size).sum
  rw [List.size_toByteArray, List.length_flatMap]
  congr 1
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨String.length_utf8EncodeChar c, ih⟩

/-- For any string, `utf8ByteSize` equals the sum of `utf8Size` over its
    characters.  This connects the byte-level size to the character-level
    representation used by `utf8GetAux`. -/
theorem utf8ByteSize_eq_sum (s : String) :
    s.utf8ByteSize = (s.toList.map Char.utf8Size).sum := by
  have h := utf8ByteSize_eq_sum_aux s.toList
  rw [String.ofList_toList] at h; exact h

/-! ## §2  utf8GetAux Navigation Lemmas

These lemmas show how `utf8GetAux` navigates through a character list:
- `utf8GetAux_skip`: scanning past a prefix skips to the suffix position
- `utf8GetAux_head`: at the head position, the head character is returned
-/

/-- Scanning `utf8GetAux` past a prefix `cs₁` in `cs₁ ++ cs₂` reaches
    the same result as starting from `cs₂` at the accumulated offset.

    This is the key induction lemma: it shows that `utf8GetAux` with
    target position `base + sum(cs₁.map utf8Size)` skips exactly past
    `cs₁` and starts scanning `cs₂`.  -/
theorem utf8GetAux_skip (cs₁ cs₂ : List Char) (base : Nat) :
    String.Pos.Raw.utf8GetAux (cs₁ ++ cs₂)
      (String.Pos.Raw.mk base) (String.Pos.Raw.mk (base + (cs₁.map Char.utf8Size).sum)) =
    String.Pos.Raw.utf8GetAux cs₂
      (String.Pos.Raw.mk (base + (cs₁.map Char.utf8Size).sum))
      (String.Pos.Raw.mk (base + (cs₁.map Char.utf8Size).sum)) := by
  induction cs₁ generalizing base with
  | nil => simp
  | cons c cs₁ ih =>
    simp only [List.cons_append, List.map_cons, List.sum_cons]
    have hne : String.Pos.Raw.mk base ≠
        String.Pos.Raw.mk (base + (c.utf8Size + (cs₁.map Char.utf8Size).sum)) := by
      simp only [ne_eq, String.Pos.Raw.mk.injEq]; have := Char.utf8Size_pos c; omega
    -- Unfold brecOn to if-then-else form
    change (if String.Pos.Raw.mk base =
              String.Pos.Raw.mk (base + (c.utf8Size + (cs₁.map Char.utf8Size).sum))
            then c
            else String.Pos.Raw.utf8GetAux (cs₁ ++ cs₂) (String.Pos.Raw.mk base + c)
              (String.Pos.Raw.mk (base + (c.utf8Size + (cs₁.map Char.utf8Size).sum)))) = _
    rw [if_neg hne]
    -- Normalize the position arithmetic
    show String.Pos.Raw.utf8GetAux (cs₁ ++ cs₂) (String.Pos.Raw.mk (base + c.utf8Size))
        (String.Pos.Raw.mk (base + (c.utf8Size + (cs₁.map Char.utf8Size).sum))) = _
    rw [show base + (c.utf8Size + (cs₁.map Char.utf8Size).sum) =
        (base + c.utf8Size) + (cs₁.map Char.utf8Size).sum from by omega]
    exact ih (base + c.utf8Size)

/-- Specialized version of `utf8GetAux_skip` with `base = 0`, matching
    the form that appears after unfolding `Raw.get`. -/
theorem utf8GetAux_skip_zero (cs₁ cs₂ : List Char) :
    String.Pos.Raw.utf8GetAux (cs₁ ++ cs₂)
      (String.Pos.Raw.mk 0) (String.Pos.Raw.mk (cs₁.map Char.utf8Size).sum) =
    String.Pos.Raw.utf8GetAux cs₂
      (String.Pos.Raw.mk (cs₁.map Char.utf8Size).sum)
      (String.Pos.Raw.mk (cs₁.map Char.utf8Size).sum) := by
  have h := utf8GetAux_skip cs₁ cs₂ 0; simp at h; exact h

/-- At the head position, `utf8GetAux` returns the head character. -/
theorem utf8GetAux_head (c : Char) (cs : List Char) (i : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (c :: cs) i i = c := by
  simp [String.Pos.Raw.utf8GetAux]

/-! ## §3  Raw.next Upper Bound — The Main Theorem

Proof that advancing a valid UTF-8 position never overshoots the string end.
-/

/-- When `p` is a valid UTF-8 position in string `s` and `p < s.utf8ByteSize`,
    the next position does not overshoot the string end.

    **Proof strategy**: Use `isValid_iff_exists_append` to decompose
    `s = s₁ ++ s₂` with `p = s₁.rawEndPos`.  Since `p < s.utf8ByteSize`,
    `s₂` is non-empty with head character `c`.  The character retrieved by
    `Raw.get` at position `p` is exactly `c` (via `utf8GetAux_skip` +
    `utf8GetAux_head`), and `c.utf8Size ≤ s₂.utf8ByteSize` since `c` is
    the first character of `s₂`. -/
theorem raw_next_le_utf8ByteSize (s : String) (p : String.Pos.Raw)
    (hv : String.Pos.Raw.IsValid s p) (hlt : p.byteIdx < s.utf8ByteSize) :
    (String.Pos.Raw.next s p).byteIdx ≤ s.utf8ByteSize := by
  -- Decompose: s = s₁ ++ s₂, p = s₁.rawEndPos = ⟨s₁.utf8ByteSize⟩
  rw [String.Pos.Raw.isValid_iff_exists_append] at hv
  obtain ⟨s₁, s₂, hs, hp⟩ := hv
  subst hs; subst hp
  simp only [String.rawEndPos, String.utf8ByteSize_append] at hlt ⊢
  -- Unfold Raw.next: adds the retrieved character's utf8Size to the position
  show s₁.utf8ByteSize +
       (String.Pos.Raw.get (s₁ ++ s₂) (String.Pos.Raw.mk s₁.utf8ByteSize)).utf8Size ≤
       s₁.utf8ByteSize + s₂.utf8ByteSize
  -- Reduce to: character size ≤ remaining string size
  suffices h : (String.Pos.Raw.get (s₁ ++ s₂)
                 (String.Pos.Raw.mk s₁.utf8ByteSize)).utf8Size ≤ s₂.utf8ByteSize by omega
  -- s₂ must be non-empty (since s₁.utf8ByteSize < s₁.utf8ByteSize + s₂.utf8ByteSize)
  have hs2_ne : s₂.toList ≠ [] := by
    intro hempty
    have h0 : s₂.utf8ByteSize = 0 := by rw [utf8ByteSize_eq_sum s₂]; simp [hempty]
    omega
  obtain ⟨c, cs₂, hcs₂⟩ := List.exists_cons_of_ne_nil hs2_ne
  -- Unfold Raw.get to utf8GetAux on the character list
  show (String.Pos.Raw.utf8GetAux ((s₁ ++ s₂).toList) (String.Pos.Raw.mk 0)
        (String.Pos.Raw.mk s₁.utf8ByteSize)).utf8Size ≤ s₂.utf8ByteSize
  -- Skip past s₁.toList, then extract the head character c
  rw [String.toList_append, utf8ByteSize_eq_sum s₁, utf8GetAux_skip_zero s₁.toList s₂.toList]
  rw [hcs₂, utf8GetAux_head c cs₂]
  -- c.utf8Size ≤ c.utf8Size + rest = s₂.utf8ByteSize
  rw [utf8ByteSize_eq_sum s₂, hcs₂, List.map_cons, List.sum_cons]
  omega

/-! ## §3b  IsValid Preservation Through next

When advancing from a valid position within the string, the resulting
position is also valid (or at the string end). -/

-- Helper: utf8ByteSize of singleton character
theorem utf8ByteSize_singleton (c : Char) :
    (String.singleton c).utf8ByteSize = c.utf8Size := by
  rw [utf8ByteSize_eq_sum]; simp [String.toList_singleton]

/-- Advancing from a valid UTF-8 position within the string yields another
    valid position (possibly at the end of the string).

    Proof: decompose `s = s₁ ++ s₂` at position `p = s₁.rawEndPos`. Since
    `s₂` is non-empty, it has head `c` and tail `rest`. After `next`, the
    position is `s₁.utf8ByteSize + c.utf8Size = (s₁ ++ singleton c).utf8ByteSize`,
    which witnesses `IsValid` with `s₁' = s₁ ++ singleton c`, `s₂' = ofList rest`. -/
theorem next_isValid (s : String) (p : String.Pos.Raw)
    (hv : String.Pos.Raw.IsValid s p) (hlt : p.byteIdx < s.utf8ByteSize) :
    String.Pos.Raw.IsValid s (String.Pos.Raw.next s p) := by
  rw [String.Pos.Raw.isValid_iff_exists_append] at hv ⊢
  obtain ⟨s₁, s₂, hs, hp⟩ := hv
  subst hs; subst hp
  simp only [String.rawEndPos, String.utf8ByteSize_append] at hlt
  -- s₂ is non-empty
  have hs2_ne : s₂.toList ≠ [] := by
    intro hempty
    have h0 : s₂.utf8ByteSize = 0 := by rw [utf8ByteSize_eq_sum s₂]; simp [hempty]
    omega
  obtain ⟨c, cs₂, hcs₂⟩ := List.exists_cons_of_ne_nil hs2_ne
  -- Witnesses: s₁' = s₁ ++ singleton c, s₂' = String.ofList cs₂
  refine ⟨s₁ ++ String.singleton c, String.ofList cs₂, ?_, ?_⟩
  · -- s₁ ++ s₂ = (s₁ ++ singleton c) ++ ofList cs₂
    simp [String.ext_iff, String.toList_append, hcs₂, List.append_assoc, String.toList_ofList]
  · -- next position = (s₁ ++ singleton c).rawEndPos
    -- Both sides are String.Pos; use ext to reduce to Nat equality
    ext
    show s₁.utf8ByteSize +
      (String.Pos.Raw.get (s₁ ++ s₂) ⟨s₁.utf8ByteSize⟩).utf8Size =
      (s₁ ++ String.singleton c).utf8ByteSize
    rw [String.utf8ByteSize_append, utf8ByteSize_singleton]
    congr 1
    -- get at s₁.utf8ByteSize returns c
    show (String.Pos.Raw.utf8GetAux ((s₁ ++ s₂).toList) ⟨0⟩ ⟨s₁.utf8ByteSize⟩).utf8Size =
      c.utf8Size
    rw [String.toList_append, utf8ByteSize_eq_sum s₁,
        utf8GetAux_skip_zero s₁.toList s₂.toList, hcs₂, utf8GetAux_head]

/-- `advance` preserves `IsValid` when the scanner has more input.
    Combined with `advance_offset_le`, this enables threading the
    bound invariant through scanner loops. -/
theorem advance_preserves_isValid (s : ScannerState)
    (hv : String.Pos.Raw.IsValid s.input ⟨s.offset⟩)
    (hlt : s.offset < s.inputEnd)
    (hend : s.inputEnd = s.input.utf8ByteSize) :
    String.Pos.Raw.IsValid s.advance.input ⟨s.advance.offset⟩ := by
  unfold ScannerState.advance
  split
  case isTrue h =>
    dsimp only []
    split
    · exact next_isValid s.input ⟨s.offset⟩ hv (show s.offset < s.input.utf8ByteSize by omega)
    · split
      · exact next_isValid s.input ⟨s.offset⟩ hv (show s.offset < s.input.utf8ByteSize by omega)
      · exact next_isValid s.input ⟨s.offset⟩ hv (show s.offset < s.input.utf8ByteSize by omega)
  case isFalse h => exact absurd hlt (by omega)

/-- When `offset = inputEnd`, the position is valid (it's the end-of-string
    position, witnessed by s₁ = input, s₂ = ""). -/
theorem isValid_at_inputEnd (s : ScannerState)
    (h_eq : s.offset = s.inputEnd)
    (hend : s.inputEnd = s.input.utf8ByteSize) :
    String.Pos.Raw.IsValid s.input ⟨s.offset⟩ := by
  rw [String.Pos.Raw.isValid_iff_exists_append]
  exact ⟨s.input, "", by simp, by rw [h_eq, hend]; rfl⟩

/-- Position 0 is always valid (witnessed by s₁ = "", s₂ = s). -/
theorem isValid_at_zero (s : String) : String.Pos.Raw.IsValid s ⟨0⟩ := by
  rw [String.Pos.Raw.isValid_iff_exists_append]
  exact ⟨"", s, by simp, rfl⟩

/-- When advance is identity (offset ≥ inputEnd), IsValid is preserved. -/
theorem advance_isValid_of_ge (s : ScannerState)
    (hv : String.Pos.Raw.IsValid s.input ⟨s.offset⟩)
    (hge : s.offset ≥ s.inputEnd) :
    String.Pos.Raw.IsValid s.advance.input ⟨s.advance.offset⟩ := by
  unfold ScannerState.advance
  split
  case isTrue h => omega
  case isFalse _ => exact hv

/-- Combined: advance preserves IsValid regardless of whether it advances. -/
theorem advance_isValid (s : ScannerState)
    (hv : String.Pos.Raw.IsValid s.input ⟨s.offset⟩)
    (hend : s.inputEnd = s.input.utf8ByteSize) :
    String.Pos.Raw.IsValid s.advance.input ⟨s.advance.offset⟩ := by
  by_cases hlt : s.offset < s.inputEnd
  · exact advance_preserves_isValid s hv hlt hend
  · exact advance_isValid_of_ge s hv (by omega)

/-! ## §4  Advance Preserves WellFormed

Application of `raw_next_le_utf8ByteSize` to the scanner's `advance` function.
-/

/-- `advance` preserves the `indents` field (it only touches offset/line/col). -/
theorem advance_indents (s : ScannerState) :
    s.advance.indents = s.indents := by
  unfold ScannerState.advance
  split <;> simp_all
  split
  · rfl
  · split <;> rfl

/-- `advance` preserves the `flowLevel` field. -/
theorem advance_flowLevel (s : ScannerState) :
    s.advance.flowLevel = s.flowLevel := by
  unfold ScannerState.advance
  split <;> simp_all
  split
  · rfl
  · split <;> rfl

/-- `advance` preserves the `flowStack` field. -/
theorem advance_flowStack (s : ScannerState) :
    s.advance.flowStack = s.flowStack := by
  unfold ScannerState.advance
  split <;> simp_all
  split
  · rfl
  · split <;> rfl

/-- `advance` preserves the `simpleKeyStack` field. -/
theorem advance_simpleKeyStack (s : ScannerState) :
    s.advance.simpleKeyStack = s.simpleKeyStack := by
  unfold ScannerState.advance
  split <;> simp_all
  split
  · rfl
  · split <;> rfl

/-- `advance` preserves the `inputEnd` field. -/
theorem advance_inputEnd (s : ScannerState) :
    s.advance.inputEnd = s.inputEnd := by
  unfold ScannerState.advance
  split <;> simp_all
  split
  · rfl
  · split <;> rfl

/-- `advance` preserves the `input` field. -/
theorem advance_input (s : ScannerState) :
    s.advance.input = s.input := by
  unfold ScannerState.advance
  split <;> simp_all
  split
  · rfl
  · split <;> rfl

/-- When the scanner has more input and the offset is at a valid UTF-8
    position, `advance` keeps the offset within bounds.

    This is the main loop invariant: combined with `advance` preserving
    indents, flowLevel, and flowStack, it shows that `advance` preserves
    all four conjuncts of `WellFormed`. -/
theorem advance_offset_le (s : ScannerState)
    (hv : String.Pos.Raw.IsValid s.input ⟨s.offset⟩)
    (hwf : s.offset ≤ s.inputEnd)
    (hend : s.inputEnd = s.input.utf8ByteSize) :
    s.advance.offset ≤ s.inputEnd := by
  unfold ScannerState.advance
  split
  case isTrue hlt =>
    -- offset < inputEnd, so advance happens
    rw [hend] at hlt
    have hle := raw_next_le_utf8ByteSize s.input ⟨s.offset⟩ hv hlt
    dsimp only []
    split
    · rw [hend]; omega
    · split <;> (rw [hend]; omega)
  case isFalse _ =>
    -- offset ≥ inputEnd, advance is identity
    exact hwf

/-- `advance` preserves `WellFormed`, given that the current offset is
    at a valid UTF-8 character boundary and `inputEnd = input.utf8ByteSize`. -/
theorem advance_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed)
    (hv : String.Pos.Raw.IsValid s.input ⟨s.offset⟩)
    (hend : s.inputEnd = s.input.utf8ByteSize) :
    s.advance.WellFormed := by
  obtain ⟨hind, hflow, hsk, hoff, hmono, hsent⟩ := hwf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- indents.size ≥ 1: preserved by advance
    rw [advance_indents]; exact hind
  · -- flowLevel = flowStack.size: preserved by advance
    rw [advance_flowLevel, advance_flowStack]; exact hflow
  · -- simpleKeyStack.size = flowStack.size: preserved by advance
    rw [advance_simpleKeyStack, advance_flowStack]; exact hsk
  · -- offset ≤ inputEnd: the main result
    rw [advance_inputEnd]
    exact advance_offset_le s hv hoff hend
  · -- indent stack monotonicity: preserved (advance doesn't touch indents)
    intro i hi; simp only [advance_indents] at hi ⊢; exact hmono i hi
  · -- sentinel preserved: advance doesn't touch indents
    intro h; simp only [advance_indents] at h ⊢; exact hsent h

/-! ## §5  Emit Preserves WellFormed -/

/-- `emit` preserves all six `WellFormed` conjuncts (it only modifies `tokens`). -/
theorem emit_preserves_wellFormed (s : ScannerState) (tok : YamlToken)
    (hwf : s.WellFormed) : (s.emit tok).WellFormed := by
  obtain ⟨hind, hflow, hsk, hoff, hmono, hsent⟩ := hwf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ScannerState.emit]; exact hind
  · simp [ScannerState.emit]; exact hflow
  · simp [ScannerState.emit]; exact hsk
  · simp [ScannerState.emit]; exact hoff
  · intro i hi; simp [ScannerState.emit] at hi ⊢; exact hmono i hi
  · intro h; simp [ScannerState.emit] at h ⊢; exact hsent h

/-! ## §6  Validation Guards -/


end L4YAML.Proofs.ScannerLoopInvariant
