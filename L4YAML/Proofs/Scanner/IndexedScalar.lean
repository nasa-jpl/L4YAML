/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedIndent

/-! # `IndexedScalar` — Phase 3 Step 4a scalar-layer proofs (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6).

This file lands the proofs for the **single-line scalar** subset
implemented in `IndexedScanner.lean` Layer E (E1 escapes, E2
double-quoted, E3 single-quoted, E4 plain). Multi-line variants and
block scalars (literal + folded) — the Step 4b sub-cluster — defer
their proofs to the matching staging file.

## What's covered

For each scalar recogniser, the proofs land:

1. **Offset monotonicity on success**. When the recogniser returns
   `some (_, c')`, `c.pos.offset ≤ c'.pos.offset`. For the plain
   recogniser (which is total), `c.pos.offset ≤ (result_cursor).pos.offset`.

2. **Strict offset progress on success**. When a quoted recogniser
   succeeds, `c.pos.offset < c'.pos.offset` (at minimum the opening
   and closing delimiters were consumed).

## Bidirectional structure

The full bidirectional (soundness + completeness) spec proofs per
production are an explicit Step 4 deliverable; for Step 4a the
proofs above give us the **structural** half: cursor positions and
termination. The **content-correctness** half — that the resolved
content string matches the spec's substring extraction — is staged
for Step 4b alongside the multi-line work where it composes
naturally with the fold/chomp argument.

## What's *not* here

- Multi-line quoted scalar continuation proofs (Step 4b).
- Multi-line plain scalar proofs (Step 4b).
- Block scalar proofs — literal + folded (Step 4b).
- Hex-escape value correctness (Step 4b, alongside the spec map).
- Dispatch-loop integration — `scanX` precondition wiring (Step 5).
-/

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.CharPredicates L4YAML.Indexed

/-! ## Layer E1 — escape sequence offset monotonicity -/

theorem collectHexDigitsLoopIx_offset_monotonic {input : String} (c : IxCursor input)
    (hex : String) (n : Nat) :
    c.pos.offset ≤ (collectHexDigitsLoopIx c hex n).2.pos.offset := by
  induction n generalizing c hex with
  | zero => unfold collectHexDigitsLoopIx; exact Nat.le_refl _
  | succ n' ih =>
    unfold collectHexDigitsLoopIx
    split
    · split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem parseHexEscapeIx_offset_monotonic {input : String} (c : IxCursor input)
    (n : Nat) {ch : Char} {c' : IxCursor input}
    (h : parseHexEscapeIx c n = some (ch, c')) :
    c.pos.offset ≤ c'.pos.offset := by
  have hCollect : c.pos.offset ≤ (collectHexDigitsLoopIx c "" n).2.pos.offset :=
    collectHexDigitsLoopIx_offset_monotonic c "" n
  unfold parseHexEscapeIx at h
  split at h
  · contradiction
  · split at h
    · -- value in Unicode range — success
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hcEq⟩ := h
      rw [← hcEq]
      exact hCollect
    · contradiction

/-- `processEscapeIx` is monotonic on the cursor offset when successful. -/
theorem processEscapeIx_offset_monotonic {input : String} (c : IxCursor input)
    {ch : Char} {c' : IxCursor input}
    (h : processEscapeIx c = some (ch, c')) :
    c.pos.offset ≤ c'.pos.offset := by
  unfold processEscapeIx at h
  split at h
  · contradiction
  · -- some pch branch
    rename_i pch hpEq
    split at h
    · -- simpleEscapeChar pch = some decoded — result is (decoded, c.advance)
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hcEq⟩ := h
      rw [← hcEq]
      exact IxCursor.advance_offset_monotonic c
    · -- simpleEscapeChar pch = none — hex dispatch
      have hAdvMono : c.pos.offset ≤ c.advance.pos.offset :=
        IxCursor.advance_offset_monotonic c
      split at h
      · exact Nat.le_trans hAdvMono (parseHexEscapeIx_offset_monotonic c.advance _ h)
      · split at h
        · exact Nat.le_trans hAdvMono (parseHexEscapeIx_offset_monotonic c.advance _ h)
        · split at h
          · exact Nat.le_trans hAdvMono (parseHexEscapeIx_offset_monotonic c.advance _ h)
          · contradiction

/-- `processEscapeIx` strictly advances the cursor on success. The
    `\\` was already consumed by the caller — `processEscapeIx` runs
    from *after* the backslash, and at minimum consumes the escape
    indicator character itself. -/
theorem processEscapeIx_offset_lt {input : String} (c : IxCursor input)
    {ch : Char} {c' : IxCursor input}
    (h : processEscapeIx c = some (ch, c')) :
    c.pos.offset < c'.pos.offset := by
  -- For processEscapeIx to return some, we need c.peek? = some pch (else none).
  have hpe : ∃ pch, c.peek? = some pch := by
    cases hp : c.peek? with
    | none =>
      unfold processEscapeIx at h
      rw [hp] at h
      contradiction
    | some pch => exact ⟨pch, rfl⟩
  obtain ⟨pch, hpch⟩ := hpe
  have hMore : c.pos.offset < input.utf8ByteSize := by
    if h' : c.pos.offset < input.utf8ByteSize then
      exact h'
    else
      have : c.peek? = none :=
        (IxCursor.peek?_eq_none_iff c).mpr (Nat.le_of_not_lt h')
      rw [this] at hpch; contradiction
  have hAdv : c.pos.offset < c.advance.pos.offset :=
    IxCursor.advance_offset_lt_of_hasMore c hMore
  -- The escape result has c'.offset ≥ c.advance.offset (in all success cases).
  -- We get c.pos.offset < c.advance.pos.offset ≤ c'.pos.offset.
  have hMono : c.pos.offset ≤ c'.pos.offset :=
    processEscapeIx_offset_monotonic c h
  -- We need strict; combine.
  -- In all success cases of processEscapeIx, the result cursor's offset is at
  -- least c.advance.pos.offset. The strict bound follows.
  -- More precisely: we re-do the case split to pull out the c.advance.offset ≤ c'.offset link.
  have hKey : c.advance.pos.offset ≤ c'.pos.offset := by
    unfold processEscapeIx at h
    split at h
    · contradiction
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, hcEq⟩ := h
        rw [← hcEq]
        exact Nat.le_refl _
      · split at h
        · exact parseHexEscapeIx_offset_monotonic c.advance _ h
        · split at h
          · exact parseHexEscapeIx_offset_monotonic c.advance _ h
          · split at h
            · exact parseHexEscapeIx_offset_monotonic c.advance _ h
            · contradiction
  exact Nat.lt_of_lt_of_le hAdv hKey

/-! ## Layer E2 — double-quoted offset monotonicity & strict progress (working notes)

The `'"'` and closing-quote-of-single branches need to convert
`h : some (content, c.advance) = some result` into a usable form. The
trick is: after `simp only [Option.some.injEq] at h`, `h : (content,
c.advance) = result` — `Prod.mk.injEq` will *not* fire because `result`
is a variable, not a literal `Prod.mk`. Two workable patterns:

- `rw [← h]` substitutes `result` with `(content, c.advance)` in the
  goal, and `result.2` reduces definitionally to `c.advance`.
- `obtain ⟨_, _⟩ := result` destructures result upfront, then
  `Prod.mk.injEq` fires.

We use the first pattern below (less re-naming).
-/

/-! ## Layer E2 — double-quoted offset monotonicity & strict progress -/

theorem collectDoubleQuotedLoopIx_offset_monotonic {input : String} (c : IxCursor input)
    (content : String) (fuel : Nat) {result : String × IxCursor input}
    (h : collectDoubleQuotedLoopIx c content fuel = some result) :
    c.pos.offset ≤ result.2.pos.offset := by
  induction fuel generalizing c content with
  | zero => unfold collectDoubleQuotedLoopIx at h; contradiction
  | succ fuel ih =>
    unfold collectDoubleQuotedLoopIx at h
    split at h
    · contradiction
    · -- some '"' branch: h : some (content, c.advance) = some result
      simp only [Option.some.injEq] at h
      -- h : (content, c.advance) = result
      rw [← h]
      exact IxCursor.advance_offset_monotonic c
    · -- some '\\' branch
      split at h
      · rename_i pchOption decodedCh cAfterEsc hEsc
        have hAdvMono : c.pos.offset ≤ c.advance.pos.offset :=
          IxCursor.advance_offset_monotonic c
        have hEscMono : c.advance.pos.offset ≤ cAfterEsc.pos.offset :=
          processEscapeIx_offset_monotonic c.advance hEsc
        have hRec : cAfterEsc.pos.offset ≤ result.2.pos.offset := ih _ _ h
        exact Nat.le_trans hAdvMono (Nat.le_trans hEscMono hRec)
      · contradiction
    · -- some ch (other) branch
      split at h
      · contradiction
      · have hRec : c.advance.pos.offset ≤ result.2.pos.offset := ih _ _ h
        exact Nat.le_trans (IxCursor.advance_offset_monotonic c) hRec

theorem scanDoubleQuotedIx_offset_lt {input : String} (c : IxCursor input)
    {result : String × IxCursor input}
    (h : scanDoubleQuotedIx c = some result) :
    c.pos.offset < result.2.pos.offset := by
  unfold scanDoubleQuotedIx at h
  split at h
  · rename_i hp
    have hMore : c.pos.offset < input.utf8ByteSize := by
      if h' : c.pos.offset < input.utf8ByteSize then
        exact h'
      else
        have : c.peek? = none :=
          (IxCursor.peek?_eq_none_iff c).mpr (Nat.le_of_not_lt h')
        rw [this] at hp; contradiction
    have hAdv : c.pos.offset < c.advance.pos.offset :=
      IxCursor.advance_offset_lt_of_hasMore c hMore
    have hRec : c.advance.pos.offset ≤ result.2.pos.offset :=
      collectDoubleQuotedLoopIx_offset_monotonic c.advance "" _ h
    exact Nat.lt_of_lt_of_le hAdv hRec
  · contradiction

/-! ## Layer E3 — single-quoted offset monotonicity & strict progress -/

theorem collectSingleQuotedLoopIx_offset_monotonic {input : String} (c : IxCursor input)
    (content : String) (fuel : Nat) {result : String × IxCursor input}
    (h : collectSingleQuotedLoopIx c content fuel = some result) :
    c.pos.offset ≤ result.2.pos.offset := by
  induction fuel generalizing c content with
  | zero => unfold collectSingleQuotedLoopIx at h; contradiction
  | succ fuel ih =>
    unfold collectSingleQuotedLoopIx at h
    split at h
    · contradiction
    · -- some '\''
      split at h
      · -- doubled-quote escape: recurse on c.advance.advance
        have hAdv1 : c.pos.offset ≤ c.advance.pos.offset :=
          IxCursor.advance_offset_monotonic c
        have hAdv2 : c.advance.pos.offset ≤ c.advance.advance.pos.offset :=
          IxCursor.advance_offset_monotonic c.advance
        have hRec : c.advance.advance.pos.offset ≤ result.2.pos.offset := ih _ _ h
        exact Nat.le_trans hAdv1 (Nat.le_trans hAdv2 hRec)
      · -- closing quote: h : some (content, c.advance) = some result
        simp only [Option.some.injEq] at h
        rw [← h]
        exact IxCursor.advance_offset_monotonic c
    · -- some ch (other)
      split at h
      · contradiction
      · have hRec : c.advance.pos.offset ≤ result.2.pos.offset := ih _ _ h
        exact Nat.le_trans (IxCursor.advance_offset_monotonic c) hRec

theorem scanSingleQuotedIx_offset_lt {input : String} (c : IxCursor input)
    {result : String × IxCursor input}
    (h : scanSingleQuotedIx c = some result) :
    c.pos.offset < result.2.pos.offset := by
  unfold scanSingleQuotedIx at h
  split at h
  · rename_i hp
    have hMore : c.pos.offset < input.utf8ByteSize := by
      if h' : c.pos.offset < input.utf8ByteSize then
        exact h'
      else
        have : c.peek? = none :=
          (IxCursor.peek?_eq_none_iff c).mpr (Nat.le_of_not_lt h')
        rw [this] at hp; contradiction
    have hAdv : c.pos.offset < c.advance.pos.offset :=
      IxCursor.advance_offset_lt_of_hasMore c hMore
    have hRec : c.advance.pos.offset ≤ result.2.pos.offset :=
      collectSingleQuotedLoopIx_offset_monotonic c.advance "" _ h
    exact Nat.lt_of_lt_of_le hAdv hRec
  · contradiction

/-! ## Layer E4 — plain scalar offset monotonicity

The plain recogniser is total: it always returns a `String ×
IxCursor input`. Monotonicity therefore has no "success" guard. -/

theorem collectPlainScalarLoopIx_offset_monotonic {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (fuel : Nat) :
    c.pos.offset ≤ (collectPlainScalarLoopIx c content spaces inFlow fuel).2.pos.offset := by
  induction fuel generalizing c content spaces with
  | zero => unfold collectPlainScalarLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectPlainScalarLoopIx
    split
    · exact Nat.le_refl _
    · -- some ch — cascade of 7 nested ifs
      split
      · exact Nat.le_refl _                              -- '#' + spaces.length > 0
      split
      · exact Nat.le_refl _                              -- ':' terminates
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _ _)  -- ':' continues
      split
      · exact Nat.le_refl _                              -- flow indicator in flow
      split
      · exact Nat.le_refl _                              -- line break
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _ _)  -- whitespace
      split
      · exact Nat.le_refl _                              -- not plain-safe
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _ _)  -- plain-safe content

theorem scanPlainScalarIx_offset_monotonic {input : String} (c : IxCursor input)
    (inFlow : Bool) :
    c.pos.offset ≤ (scanPlainScalarIx c inFlow).2.pos.offset := by
  unfold scanPlainScalarIx
  exact collectPlainScalarLoopIx_offset_monotonic c "" "" inFlow _

end L4YAML.Scanner.Indexed
