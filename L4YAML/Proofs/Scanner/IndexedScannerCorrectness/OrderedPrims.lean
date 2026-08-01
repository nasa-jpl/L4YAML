/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.OrderedDefs

/-! # `IndexedScannerCorrectness.OrderedPrims` — §8.3–§8.6

Primitive (`emit` / `emitAt` / `advance` / `advanceN` /
`overwriteAtCursor`) and helper (`skipToContentS` / `unwindIndentsIx` /
`pushSequenceIndentIx` / `pushMappingIndentIx` / `saveSimpleKeyIx`)
preservation lemmas for `ScanInvIx` and `AllKeysValidIx`.

Split out of `IndexedScannerCorrectness.lean` (Reflection 112). -/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.ScannerCorrectness

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.WellBehaved
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid

variable {input : String}

/-! ### §8.3  Primitive preservation: `emit`, `emitAt`, `advance`,
`overwriteAtCursor`, `setIfInBounds`.

Each primitive carries the bound from the cursor's current offset to
the new state's cursor offset (which is the same for `emit`/`emitAt`/
`overwriteAtCursor` and ≥ for `advance`). -/

/-- The key positional fact for a single `Array.push`: positions of new
    array's indices equal the push value at the new slot, and old slot's
    value below. -/
lemma push_start_offset_eq {input : String}
    (arr : Array (IxToken input)) (t : IxToken input)
    (k : Nat) (hk : k < (arr.push t).size) :
    ((arr.push t)[k]'hk).start.offset =
      if h : k < arr.size then (arr[k]'h).start.offset else t.start.offset := by
  by_cases hlt : k < arr.size
  · rw [Array.getElem_push_lt hlt]; simp [hlt]
  · have heq : k = arr.size := by
      have : k < arr.size + 1 := by rw [← Array.size_push]; exact hk
      omega
    subst heq
    rw [Array.getElem_push_eq]; simp [hlt]

/-- `emit tok` preserves `ScanInvIx`: the new token's start is
    `s.cursor.pos`, equal to all-old-bounds; cursor offset unchanged. -/
lemma emit_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (tok : YamlToken) (h : ScanInvIx s) : ScanInvIx (s.emit tok) := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInvIx ScanInv'Ix
  have h_off : (s.emit tok).cursor.pos.offset = s.cursor.pos.offset := by
    rw [emit_cursor]
  rw [h_off]
  -- We reason via the underlying push.
  have h_get : ∀ k (hk : k < (s.emit tok).tokens.tokens.size),
      ((s.emit tok).tokens.tokens[k]'hk).start.offset =
        if h : k < s.tokens.tokens.size then (s.tokens.tokens[k]'h).start.offset
                                         else s.cursor.pos.offset := by
    intro k hk
    show ((s.tokens.tokens.push _)[k]'hk).start.offset = _
    rw [push_start_offset_eq]
    split <;> rfl
  have h_sz : (s.emit tok).tokens.tokens.size = s.tokens.tokens.size + 1 := by
    show (s.tokens.tokens.push _).size = _; exact Array.size_push ..
  refine ⟨?_, ?_⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    -- Reduce Fin.val
    have hij' : i < j := hij
    show ((s.emit tok).tokens.tokens[i]'hi).start.offset ≤
         ((s.emit tok).tokens.tokens[j]'hj).start.offset
    rw [h_get i hi, h_get j hj]
    split <;> rename_i hi_lt
    · split <;> rename_i hj_lt
      · exact h_ord ⟨i, hi_lt⟩ ⟨j, hj_lt⟩ hij'
      · exact h_bnd ⟨i, hi_lt⟩
    · split <;> rename_i hj_lt
      · -- impossible: i ≥ size, j < size, i < j
        rw [h_sz] at hi
        omega
      · -- both ≥ size; from sizes, i = j = size, contradicts i < j
        rw [h_sz] at hi hj
        omega
  · intro ⟨i, hi⟩
    show ((s.emit tok).tokens.tokens[i]'hi).start.offset ≤ s.cursor.pos.offset
    rw [h_get i hi]
    split <;> rename_i hi_lt
    · exact h_bnd ⟨i, hi_lt⟩
    · exact Nat.le_refl _

/-- `emitAt startPos tok hOrder` preserves `ScanInvIx` provided that
    `startPos.offset ≥` all existing tokens' starts (the new token
    inserts at a position ≥ all current tokens). The hypothesis is
    typically discharged by `startPos = s.cursor.pos` at some earlier
    state composed with `ScanInvIx`. -/
lemma emitAt_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h : ScanInvIx s)
    (h_ge : ∀ i : Fin s.tokens.tokens.size,
      (s.tokens.tokens[i]).start.offset ≤ startPos.offset) :
    ScanInvIx (s.emitAt startPos tok hOrder) := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInvIx ScanInv'Ix
  have h_off : (s.emitAt startPos tok hOrder).cursor.pos.offset =
      s.cursor.pos.offset := by rw [emitAt_cursor]
  rw [h_off]
  have h_sz : (s.emitAt startPos tok hOrder).tokens.tokens.size =
      s.tokens.tokens.size + 1 := by
    show (s.tokens.tokens.push _).size = _; exact Array.size_push ..
  have h_get : ∀ k (hk : k < (s.emitAt startPos tok hOrder).tokens.tokens.size),
      ((s.emitAt startPos tok hOrder).tokens.tokens[k]'hk).start.offset =
        if h : k < s.tokens.tokens.size then (s.tokens.tokens[k]'h).start.offset
                                         else startPos.offset := by
    intro k hk
    show ((s.tokens.tokens.push _)[k]'hk).start.offset = _
    rw [push_start_offset_eq]
    split <;> rfl
  refine ⟨?_, ?_⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    have hij' : i < j := hij
    show ((s.emitAt startPos tok hOrder).tokens.tokens[i]'hi).start.offset ≤
         ((s.emitAt startPos tok hOrder).tokens.tokens[j]'hj).start.offset
    rw [h_get i hi, h_get j hj]
    split <;> rename_i hi_lt
    · split <;> rename_i hj_lt
      · exact h_ord ⟨i, hi_lt⟩ ⟨j, hj_lt⟩ hij'
      · exact h_ge ⟨i, hi_lt⟩
    · split <;> rename_i hj_lt
      · rw [h_sz] at hi; omega
      · rw [h_sz] at hi hj; omega
  · intro ⟨i, hi⟩
    show ((s.emitAt startPos tok hOrder).tokens.tokens[i]'hi).start.offset ≤ s.cursor.pos.offset
    rw [h_get i hi]
    split <;> rename_i hi_lt
    · exact h_bnd ⟨i, hi_lt⟩
    · exact hOrder

/-- Specialised `emitAt` preservation: when `startPos.offset =
    s.cursor.pos.offset`, the `h_ge` precondition follows from
    `ScanInvIx`'s bound. -/
lemma emitAt_preserves_ScanInvIx_eq {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h_eq : startPos.offset = s.cursor.pos.offset)
    (h : ScanInvIx s) :
    ScanInvIx (s.emitAt startPos tok hOrder) :=
  emitAt_preserves_ScanInvIx s startPos tok hOrder h
    (fun i => by rw [h_eq]; exact h.2 i)

/-- `advance` preserves `ScanInvIx`: tokens unchanged, cursor advances. -/
lemma advance_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (h : ScanInvIx s) : ScanInvIx s.advance := by
  apply ScanInvIx_of_offset_ge s s.advance h (by rfl) (advance_offset_monotonic s)

/-- `advanceN` preserves `ScanInvIx`. -/
lemma advanceN_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (n : Nat) (h : ScanInvIx s) : ScanInvIx (s.advanceN n) := by
  apply ScanInvIx_of_offset_ge s (s.advanceN n) h (by rfl) (advanceN_offset_monotonic s n)

/-- `overwriteAtCursor i sk tok` preserves `ScanInvIx` provided that
    `sk.pos.offset` matches the existing slot's `.start.offset`. -/
lemma overwriteAtCursor_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken)
    (h : ScanInvIx s)
    (h_match : ∀ (h_i : i < s.tokens.tokens.size),
      sk.pos.offset = (s.tokens.tokens[i]'h_i).start.offset) :
    ScanInvIx (s.overwriteAtCursor i sk tok) := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInvIx ScanInv'Ix
  -- cursor unchanged
  have h_off : (s.overwriteAtCursor i sk tok).cursor.pos.offset =
      s.cursor.pos.offset := by
    show (s.cursor).pos.offset = _; rfl
  rw [h_off]
  -- size unchanged
  have h_sz : (s.overwriteAtCursor i sk tok).tokens.tokens.size =
      s.tokens.tokens.size := by
    show (s.tokens.tokens.setIfInBounds i _).size = _; exact Array.size_setIfInBounds ..
  -- The overwriting token's `.start.offset = sk.pos.offset` (definitionally
  -- from `IxToken.mk'`). Reduce via `setIfInBounds` definition + `Array.set`.
  have h_get : ∀ k (hk : k < (s.overwriteAtCursor i sk tok).tokens.tokens.size),
      ((s.overwriteAtCursor i sk tok).tokens.tokens[k]'hk).start.offset =
        if i = k then sk.pos.offset
                 else (s.tokens.tokens[k]'(by rw [h_sz] at hk; exact hk)).start.offset := by
    intro k hk
    have hk' : k < s.tokens.tokens.size := by rw [h_sz] at hk; exact hk
    show ((s.tokens.tokens.setIfInBounds i
        (IxToken.mk' (input := input) sk.pos tok sk.pos (Nat.le_refl _) sk.posBound))[k]'hk
      ).start.offset = _
    unfold Array.setIfInBounds
    by_cases hi : i < s.tokens.tokens.size
    · -- in-bounds: setIfInBounds = .set i v
      simp only [hi, dite_true]
      by_cases h_ik : i = k
      · subst h_ik
        rw [Array.getElem_set_self]
        simp [IxToken.mk']
      · rw [Array.getElem_set_ne (h := h_ik), if_neg h_ik]
    · -- out-of-bounds: setIfInBounds = id; i ≠ k since k < size and i ≥ size.
      simp only [hi, dite_false]
      have h_ne : i ≠ k := fun h => by subst h; exact hi hk'
      rw [if_neg h_ne]
  refine ⟨?_, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : a < b := hab
    have ha' : a < s.tokens.tokens.size := by rw [h_sz] at ha; exact ha
    have hb' : b < s.tokens.tokens.size := by rw [h_sz] at hb; exact hb
    show ((s.overwriteAtCursor i sk tok).tokens.tokens[a]'ha).start.offset ≤
         ((s.overwriteAtCursor i sk tok).tokens.tokens[b]'hb).start.offset
    rw [h_get a ha, h_get b hb]
    split <;> rename_i h_eq_a
    · split <;> rename_i h_eq_b
      · omega
      · show sk.pos.offset ≤ _
        subst h_eq_a; rw [h_match ha']
        exact h_ord ⟨i, ha'⟩ ⟨b, hb'⟩ hab'
    · split <;> rename_i h_eq_b
      · show _ ≤ sk.pos.offset
        subst h_eq_b; rw [h_match hb']
        exact h_ord ⟨a, ha'⟩ ⟨i, hb'⟩ hab'
      · exact h_ord ⟨a, ha'⟩ ⟨b, hb'⟩ hab'
  · intro ⟨k, hk⟩
    have hk' : k < s.tokens.tokens.size := by rw [h_sz] at hk; exact hk
    show ((s.overwriteAtCursor i sk tok).tokens.tokens[k]'hk).start.offset ≤ s.cursor.pos.offset
    rw [h_get k hk]
    split <;> rename_i h_eq
    · -- i = k: show sk.pos.offset ≤ s.cursor.pos.offset
      show sk.pos.offset ≤ _
      have hi_lt : i < s.tokens.tokens.size := h_eq ▸ hk'
      rw [h_match hi_lt]
      exact h_bnd ⟨i, hi_lt⟩
    · exact h_bnd ⟨k, hk'⟩

/-! ### §8.3'  `overwriteAtCursor` start-field and other-slot lemmas.

These two lemmas isolate the `setIfInBounds` reasoning that
`scanValuePrepareIx` chains: (1) the *written* slot's new `.start`
equals `sk.pos`; (2) any *other* slot's `.start` is unchanged. Used by
`_mono_pos`-based `_preserves_AllKeysValidIx` proofs. -/

lemma overwriteAtCursor_start_at_idx {input : String} (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken)
    (h_i : i < (s.overwriteAtCursor i sk tok).tokens.tokens.size) :
    ((s.overwriteAtCursor i sk tok).tokens.tokens[i]'h_i).start = sk.pos := by
  show ((s.tokens.tokens.setIfInBounds i
      (IxToken.mk' (input := input) sk.pos tok sk.pos (Nat.le_refl _) sk.posBound))[i]'h_i).start = sk.pos
  rw [Array.getElem_setIfInBounds_self]
  rfl

lemma overwriteAtCursor_preserves_other_start {input : String}
    (s : ScannerStateIx input) (i k : Nat) (sk : IxCursor input) (tok : YamlToken)
    (h_ne : i ≠ k)
    (h_k_orig : k < s.tokens.tokens.size) :
    ((s.overwriteAtCursor i sk tok).tokens.tokens[k]'(by
        show k < (s.tokens.tokens.setIfInBounds i _).size
        rw [Array.size_setIfInBounds]; exact h_k_orig)).start =
      (s.tokens.tokens[k]'h_k_orig).start := by
  congr 1
  show (s.tokens.tokens.setIfInBounds i
      (IxToken.mk' (input := input) sk.pos tok sk.pos (Nat.le_refl _) sk.posBound))[k]'_ =
    s.tokens.tokens[k]'h_k_orig
  exact Array.getElem_setIfInBounds_ne h_k_orig h_ne

/-- If the original slot at `i` already has `.start = sk.pos`, then
    `overwriteAtCursor i sk tok` preserves the `.start` field of *every*
    slot. Used by `scanValuePrepareIx_preserves_AllKeysValidIx` to feed
    `SimpleKeyStackValidIx_mono_pos`. -/
lemma overwriteAtCursor_preserves_start_if_match {input : String}
    (s : ScannerStateIx input) (i : Nat) (sk : IxCursor input) (tok : YamlToken)
    (h_match : ∀ (h_i : i < s.tokens.tokens.size),
      (s.tokens.tokens[i]'h_i).start = sk.pos)
    (k : Nat) (h_k_orig : k < s.tokens.tokens.size) :
    ((s.overwriteAtCursor i sk tok).tokens.tokens[k]'(by
        show k < (s.tokens.tokens.setIfInBounds i _).size
        rw [Array.size_setIfInBounds]; exact h_k_orig)).start =
      (s.tokens.tokens[k]'h_k_orig).start := by
  by_cases h_eq : i = k
  · subst h_eq
    rw [overwriteAtCursor_start_at_idx s i sk tok]
    exact (h_match h_k_orig).symm
  · exact overwriteAtCursor_preserves_other_start s i k sk tok h_eq h_k_orig

/-! ### §8.4  Helper preservation: `skipToContentS`, `unwindIndentsIx`,
`saveSimpleKeyIx`, `pushSequenceIndentIx`, `pushMappingIndentIx`.

These build on the §8.3 primitives via mono / offset_ge / emit-based
composition. -/

/-- `skipToContentS` preserves `ScanInvIx`: cursor advances, tokens
    unchanged. -/
lemma skipToContentS_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx s.skipToContentS := by
  apply ScanInvIx_of_offset_ge s s.skipToContentS h
  · exact skipToContentS_tokens s
  · exact skipToContentS_offset_monotonic s

/-- `unwindIndentsLoopIx` preserves `ScanInvIx`: emits `blockEnd` at
    cursor.pos in each iteration. -/
lemma unwindIndentsLoopIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat)
    (h : ScanInvIx s) : ScanInvIx (unwindIndentsLoopIx s col fuel) := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoopIx; exact h
  | succ fuel' ih =>
    unfold unwindIndentsLoopIx
    split
    · -- emit blockEnd + pop indents + recurse
      have h_emit : ScanInvIx (s.emit YamlToken.blockEnd) := emit_preserves_ScanInvIx s _ h
      have h_pop : ScanInvIx { s.emit YamlToken.blockEnd with
          indents := (s.emit YamlToken.blockEnd).indents.pop } := by
        apply ScanInvIx_of_field_update _ _ h_emit rfl rfl
      exact ih _ h_pop
    · exact h

lemma unwindIndentsIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (col : Int)
    (h : ScanInvIx s) : ScanInvIx (unwindIndentsIx s col) := by
  unfold unwindIndentsIx
  exact unwindIndentsLoopIx_preserves_ScanInvIx s col s.indents.size h

lemma pushSequenceIndentIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (col : Int)
    (h : ScanInvIx s) : ScanInvIx (pushSequenceIndentIx s col) := by
  unfold pushSequenceIndentIx
  split
  · apply ScanInvIx_of_field_update _ _ (emit_preserves_ScanInvIx s _ h) rfl rfl
  · exact h

lemma pushMappingIndentIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (col : Int)
    (h : ScanInvIx s) : ScanInvIx (pushMappingIndentIx s col) := by
  unfold pushMappingIndentIx
  split
  · apply ScanInvIx_of_field_update _ _ (emit_preserves_ScanInvIx s _ h) rfl rfl
  · exact h

lemma saveSimpleKeyIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx (saveSimpleKeyIx s) := by
  unfold saveSimpleKeyIx
  split
  · exact h
  · split
    · -- push 2 placeholders + update simpleKey/simpleKeyStack fields
      have h1 : ScanInvIx (s.emit YamlToken.placeholder) :=
        emit_preserves_ScanInvIx s _ h
      have h2 : ScanInvIx ((s.emit YamlToken.placeholder).emit YamlToken.placeholder) :=
        emit_preserves_ScanInvIx _ _ h1
      apply ScanInvIx_of_field_update _ _ h2 rfl rfl
    · exact h

/-! ### §8.5  Helper preservation for `AllKeysValidIx`.

The simpleKey/simpleKeyStack preservation lemmas
(`unwindIndentsIx_preserves_simpleKey`, etc.) from
`IndexedScannerPlainScalarValid` give us monotonicity inputs; combined
with the `_preserves_prefix` lemmas for full-token equality, we close
`AllKeysValidIx` preservation via `AllKeysValidIx_mono`. -/

lemma skipToContentS_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h : AllKeysValidIx s) :
    AllKeysValidIx s.skipToContentS := by
  apply AllKeysValidIx_mono s s.skipToContentS h
    (skipToContentS_preserves_simpleKey s)
    (skipToContentS_preserves_simpleKeyStack s)
    (by simp [skipToContentS_tokens])
    (fun i hi => by simp [skipToContentS_tokens])

lemma unwindIndentsIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (col : Int)
    (h : AllKeysValidIx s) : AllKeysValidIx (unwindIndentsIx s col) := by
  apply AllKeysValidIx_mono s _ h
    (unwindIndentsIx_preserves_simpleKey s col)
    (unwindIndentsIx_preserves_simpleKeyStack s col)
    (unwindIndentsIx_tokens_size_le s col)
    (fun i hi => unwindIndentsIx_preserves_prefix s col i hi)

/-! ### §8.6  `saveSimpleKeyIx_preserves_AllKeysValidIx`

The remaining `AllKeysValidIx` preservation for `saveSimpleKeyIx` — the
two-emit + simpleKey-update branch fills slots `s.tokens.size` and
`s.tokens.size + 1` with `.start = s.cursor.pos`, and the new simpleKey
has `cursor := s.cursor` (so `simpleKey.pos = s.cursor.pos`). This
matches the legacy `saveSimpleKey_preserves_SimpleKeyValid`
(`ScannerCorrectness.lean:8662`) + `saveSimpleKey_preserves_SimpleKeyStackValid`
(`:8855`) pair. -/

/-- The new token's `.start` field after `emit` equals the cursor
    position. Indexed analogue of the implicit fact behind
    `Array.getElem_push_eq` + `ScannerState.currentPos`. -/
lemma emit_new_token_start {input : String} (s : ScannerStateIx input)
    (tok : YamlToken)
    (h : s.tokens.size < (s.emit tok).tokens.size) :
    ((s.emit tok).tokens[s.tokens.size]'h).start = s.cursor.pos := by
  have h_get : (s.emit tok).tokens[s.tokens.size]'h =
      IxToken.mk' s.cursor.pos tok s.cursor.pos (Nat.le_refl _) s.cursor.posBound := by
    change (s.tokens.tokens.push _)[s.tokens.tokens.size]'h = _
    exact Array.getElem_push_eq ..
  rw [h_get]; rfl

/-- The new token's `.start` field after `emitAt` equals `startPos`.
    Sister lemma to `emitAt_new_token_token` (which projects `.token`). -/
lemma emitAt_new_token_start {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h : s.tokens.size < (s.emitAt startPos tok hOrder).tokens.size) :
    ((s.emitAt startPos tok hOrder).tokens[s.tokens.size]'h).start = startPos := by
  have h_get : (s.emitAt startPos tok hOrder).tokens[s.tokens.size]'h =
      IxToken.mk' startPos tok s.cursor.pos hOrder s.cursor.posBound := by
    change (s.tokens.tokens.push _)[s.tokens.tokens.size]'h = _
    exact Array.getElem_push_eq ..
  rw [h_get]; rfl

/-- `saveSimpleKeyIx` preserves `SimpleKeyValidIx`: on the two-emit
    branch the new simpleKey has `tokenIndex = s.tokens.size`, and the
    two pushed slots carry `.start = s.cursor.pos = new simpleKey.pos`. -/
lemma saveSimpleKeyIx_preserves_SimpleKeyValidIx {input : String}
    (s : ScannerStateIx input) (h_skv : SimpleKeyValidIx s) :
    SimpleKeyValidIx (saveSimpleKeyIx s) := by
  rcases saveSimpleKeyIx_state_cases s with h_eq | h_eq
  · rw [h_eq]; exact h_skv
  · rw [h_eq]
    -- Common facts.
    have h_size1 : (s.emit YamlToken.placeholder).tokens.size = s.tokens.size + 1 :=
      emit_tokens_size s .placeholder
    have h_size2 : ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size =
        s.tokens.size + 2 := by rw [emit_tokens_size, h_size1]
    have h_lt1' : s.tokens.size < (s.emit YamlToken.placeholder).tokens.size := by
      rw [h_size1]; omega
    have h_lt1 : s.tokens.size <
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size := by
      rw [h_size2]; omega
    have h_lt2 : s.tokens.size + 1 <
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size := by
      rw [h_size2]; omega
    have h_lt2'' : (s.emit YamlToken.placeholder).tokens.size <
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size := by
      rw [emit_tokens_size]; omega
    have h_cur : (s.emit YamlToken.placeholder).cursor = s.cursor := by rw [emit_cursor]
    have h_post_cur : ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).cursor = s.cursor := by
      rw [emit_cursor, emit_cursor]
    -- The first pushed slot's start.
    have h_start1 :
        (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size]'h_lt1).start =
          s.cursor.pos := by
      rw [emit_preserves_tokens_at (s.emit YamlToken.placeholder) .placeholder s.tokens.size h_lt1']
      exact emit_new_token_start s .placeholder h_lt1'
    -- The second pushed slot's start.
    have h_start2 :
        (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size + 1]'h_lt2).start =
          s.cursor.pos := by
      have h_eq_idx :
          ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size + 1]'h_lt2 =
          ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[(s.emit YamlToken.placeholder).tokens.size]'h_lt2'' := by
        congr 1
        omega
      rw [h_eq_idx, emit_new_token_start (s.emit YamlToken.placeholder) .placeholder h_lt2'', h_cur]
    intro _h_poss
    -- Goal (after rw [h_eq]) is `SimpleKeyValidIx` applied to the field-update form.
    -- Use `change` to fold to the unwrapped form (defeq via field-update projection).
    change s.tokens.size < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size ∧
           s.tokens.size + 1 < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size ∧
           (∀ (_ : s.tokens.size < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size),
             (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size]'h_lt1).start =
               ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).cursor.pos) ∧
           (∀ (_ : s.tokens.size + 1 < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size),
             (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size + 1]'h_lt2).start =
               ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).cursor.pos)
    refine ⟨h_lt1, h_lt2, ?_, ?_⟩
    · intro _h1; rw [h_start1, h_post_cur]
    · intro _h2; rw [h_start2, h_post_cur]

/-- `saveSimpleKeyIx` preserves `SimpleKeyStackValidIx`: the simpleKeyStack
    is unchanged on both branches; on the two-emit branch the token
    prefix is preserved by `twoPlaceholderEmits_preserves_prefix`. -/
lemma saveSimpleKeyIx_preserves_SimpleKeyStackValidIx {input : String}
    (s : ScannerStateIx input) (h_ssv : SimpleKeyStackValidIx s) :
    SimpleKeyStackValidIx (saveSimpleKeyIx s) := by
  rcases saveSimpleKeyIx_state_cases s with h_eq | h_eq
  · rw [h_eq]; exact h_ssv
  · rw [h_eq]
    have h_size1 : (s.emit YamlToken.placeholder).tokens.size = s.tokens.size + 1 :=
      emit_tokens_size s .placeholder
    have h_size2 : ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size =
        s.tokens.size + 2 := by rw [emit_tokens_size, h_size1]
    have h_stack_eq :
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack = s.simpleKeyStack := by
      rw [emit_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]
    intro j hj h_poss
    -- Fold the field-update to the unwrapped form.
    change j < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack.size at hj
    change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).possible = true at h_poss
    have hj_s : j < s.simpleKeyStack.size := by rw [h_stack_eq] at hj; exact hj
    have h_get : ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj =
        s.simpleKeyStack[j]'hj_s := by simp
    rw [h_get] at h_poss
    have ⟨hb1, hb2, hp1, hp2⟩ := h_ssv j hj_s h_poss
    have h_sz_inline : s.tokens.size = s.tokens.tokens.size := rfl
    change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).tokenIndex <
              ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size ∧
           (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).tokenIndex + 1 <
              ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size ∧
           (∀ _, _) ∧ _
    rw [h_get]
    refine ⟨by rw [h_size2]; omega, by rw [h_size2]; omega, ?_, ?_⟩
    · intro _h1
      exact (congrArg IxToken.start
        (twoPlaceholderEmits_preserves_prefix s _ hb1)).trans (hp1 hb1)
    · intro _h2
      exact (congrArg IxToken.start
        (twoPlaceholderEmits_preserves_prefix s _ hb2)).trans (hp2 hb2)

lemma saveSimpleKeyIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h : AllKeysValidIx s) :
    AllKeysValidIx (saveSimpleKeyIx s) :=
  ⟨saveSimpleKeyIx_preserves_SimpleKeyValidIx s h.1,
   saveSimpleKeyIx_preserves_SimpleKeyStackValidIx s h.2⟩

/-! ### §8.6'  `emit` / `advance` preservation for `AllKeysValidIx`.

These compose `AllKeysValidIx_mono` with the existing
`emit_preserves_simpleKey` / `emit_preserves_simpleKeyStack` /
`emit_preserves_tokens_at` (and the trivial `advance_*` analogues). -/

lemma emit_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (tok : YamlToken) (h : AllKeysValidIx s) :
    AllKeysValidIx (s.emit tok) := by
  apply AllKeysValidIx_mono s _ h
    (emit_preserves_simpleKey s tok) (emit_preserves_simpleKeyStack s tok)
    (by show s.tokens.size ≤ (s.emit tok).tokens.size; rw [emit_tokens_size]; omega)
    (fun i hi => emit_preserves_tokens_at s tok i hi)

lemma advance_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h : AllKeysValidIx s) :
    AllKeysValidIx s.advance := by
  apply AllKeysValidIx_mono s _ h
    (advance_preserves_simpleKey s) (advance_preserves_simpleKeyStack s)
    (Nat.le_of_eq (congrArg Indexed.TokenStream.size (advance_tokens s).symm))
    (fun _i _hi => rfl)

/-! ### §8.6''  Generic `ScanInvIx_of_one_emit_at_pre_cursor`.

A pure-bookkeeping closer that establishes `ScanInvIx s'` from
preservation of the prefix + a single new token at-or-after
`s.tokens.size` whose `.start.offset = s.cursor.pos.offset` (or in
general, all new tokens have `.start.offset = s.cursor.pos.offset`).
Used by `scanAnchorOrAliasIx` / `scanTagIx` / `scanYamlDirectiveIx` /
`scanTagDirectiveIx` chains in OrderedDispatch, where the
`emitAt startPos token hBound` always has `startPos = s.cursor.pos`. -/
lemma ScanInvIx_of_one_emit_at_pre_cursor {input : String}
    (s s' : ScannerStateIx input) (h : ScanInvIx s)
    (h_off : s.cursor.pos.offset ≤ s'.cursor.pos.offset)
    (h_size : s.tokens.tokens.size ≤ s'.tokens.tokens.size)
    (h_pref : ∀ i (hi : i < s.tokens.tokens.size),
        (s'.tokens.tokens[i]'(Nat.lt_of_lt_of_le hi h_size)).start.offset =
          (s.tokens.tokens[i]'hi).start.offset)
    (h_new : ∀ k (_hk_lo : s.tokens.tokens.size ≤ k) (hk : k < s'.tokens.tokens.size),
        (s'.tokens.tokens[k]'hk).start.offset = s.cursor.pos.offset) :
    ScanInvIx s' := by
  refine ⟨?_, ?_⟩
  · -- Ordering.
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : a < b := hab
    show (s'.tokens.tokens[a]'ha).start.offset ≤ (s'.tokens.tokens[b]'hb).start.offset
    by_cases ha_old : a < s.tokens.tokens.size
    · by_cases hb_old : b < s.tokens.tokens.size
      · rw [h_pref a ha_old, h_pref b hb_old]
        exact h.1 ⟨a, ha_old⟩ ⟨b, hb_old⟩ hab'
      · have hb_lo : s.tokens.tokens.size ≤ b := Nat.le_of_not_lt hb_old
        rw [h_pref a ha_old, h_new b hb_lo hb]
        exact h.2 ⟨a, ha_old⟩
    · have ha_lo : s.tokens.tokens.size ≤ a := Nat.le_of_not_lt ha_old
      have hb_lo : s.tokens.tokens.size ≤ b := Nat.le_trans ha_lo (Nat.le_of_lt hab')
      rw [h_new a ha_lo ha, h_new b hb_lo hb]
      exact Nat.le_refl _
  · -- Bound.
    intro ⟨k, hk⟩
    show (s'.tokens.tokens[k]'hk).start.offset ≤ s'.cursor.pos.offset
    by_cases hk_old : k < s.tokens.tokens.size
    · rw [h_pref k hk_old]; exact Nat.le_trans (h.2 ⟨k, hk_old⟩) h_off
    · have hk_lo : s.tokens.tokens.size ≤ k := Nat.le_of_not_lt hk_old
      rw [h_new k hk_lo hk]; exact h_off

end L4YAML.Proofs.Indexed.ScannerCorrectness
