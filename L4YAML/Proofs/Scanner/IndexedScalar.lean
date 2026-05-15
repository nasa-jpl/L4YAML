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

/-! ## Layer F1/F2 — fold helpers used by multi-line collectors

Three monotonicity facts feed the multi-line proofs:

- `skipBlankLinesLoopIx_offset_monotonic` — the blank-line counter
  only ever advances the cursor (or leaves it fixed).
- `foldQuotedNewlinesIx_offset_monotonic` — quoted-scalar fold step
  is monotonic on `.2`.
- `handleBlockLineBreakIx_offset_monotonic` — when the block-context
  handler returns `some (_, c')`, `c.pos.offset ≤ c'.pos.offset`.

Each lemma's proof unfolds the function and chains the underlying
`skipSpaces` / `skipWhitespace` / `consumeLineBreak` /
`skipBlankLinesLoopIx` monotonicity facts. We do **not** need the
strict (`<`) version for these: the strict bound on the entry-point
`scanX` recognisers comes from `consumeLineBreak_strict` /
`IxCursor.advance_offset_lt_of_hasMore` applied at the dispatch site,
combined with `≤` on the helper. -/

theorem skipBlankLinesLoopIx_offset_monotonic {input : String} (c : IxCursor input)
    (emptyCount : Nat) (fuel : Nat) :
    c.pos.offset ≤ (skipBlankLinesLoopIx c emptyCount fuel).1.pos.offset := by
  induction fuel generalizing c emptyCount with
  | zero => unfold skipBlankLinesLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold skipBlankLinesLoopIx
    split
    · -- some ch
      split
      · -- isLineBreakBool ch = true: recurse on consumeLineBreak (skipSpaces c).1
        have hSP : c.pos.offset ≤ (skipSpaces c).1.pos.offset :=
          skipSpaces_offset_monotonic c
        have hCLB : (skipSpaces c).1.pos.offset ≤
                    (consumeLineBreak (skipSpaces c).1).pos.offset :=
          consumeLineBreak_offset_monotonic _
        have hRec :
            (consumeLineBreak (skipSpaces c).1).pos.offset ≤
            (skipBlankLinesLoopIx (consumeLineBreak (skipSpaces c).1)
              (emptyCount + 1) fuel).1.pos.offset :=
          ih (consumeLineBreak (skipSpaces c).1) (emptyCount + 1)
        exact Nat.le_trans hSP (Nat.le_trans hCLB hRec)
      · -- isLineBreakBool ch = false: yields (c, _)
        exact Nat.le_refl _
    · -- peek? = none: yields (c, _)
      exact Nat.le_refl _

theorem foldQuotedNewlinesIx_offset_monotonic {input : String} (c : IxCursor input) :
    c.pos.offset ≤ (foldQuotedNewlinesIx c).2.pos.offset := by
  unfold foldQuotedNewlinesIx
  -- Both branches of the `if emptyCount > 0` use the same cursor:
  --   skipWhitespace (skipBlankLinesLoopIx (consumeLineBreak c) 0 _).1
  have hCLB : c.pos.offset ≤ (consumeLineBreak c).pos.offset :=
    consumeLineBreak_offset_monotonic c
  have hBL :
      (consumeLineBreak c).pos.offset ≤
      (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1.pos.offset :=
    skipBlankLinesLoopIx_offset_monotonic _ _ _
  have hSW :
      (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1.pos.offset ≤
      (skipWhitespace
        (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).pos.offset :=
    skipWhitespace_offset_monotonic _
  have hChain : c.pos.offset ≤
      (skipWhitespace
        (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).pos.offset :=
    Nat.le_trans hCLB (Nat.le_trans hBL hSW)
  split
  · exact hChain
  · exact hChain

theorem handleBlockLineBreakIx_offset_monotonic {input : String} (c : IxCursor input)
    (contentIndent : Nat) {folded : String} {c' : IxCursor input}
    (h : handleBlockLineBreakIx c contentIndent = some (folded, c')) :
    c.pos.offset ≤ c'.pos.offset := by
  unfold handleBlockLineBreakIx at h
  -- Build the monotonicity chain to the result cursor up front.
  have hCLB : c.pos.offset ≤ (consumeLineBreak c).pos.offset :=
    consumeLineBreak_offset_monotonic c
  have hBL :
      (consumeLineBreak c).pos.offset ≤
      (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1.pos.offset :=
    skipBlankLinesLoopIx_offset_monotonic _ _ _
  have hSP :
      (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1.pos.offset ≤
      (skipSpaces
        (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1.pos.offset :=
    skipSpaces_offset_monotonic _
  have hChain : c.pos.offset ≤
      (skipSpaces
        (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1).1.pos.offset :=
    Nat.le_trans hCLB (Nat.le_trans hBL hSP)
  split at h
  · contradiction                 -- col < contentIndent → none
  · split at h
    · contradiction               -- atDocumentBoundary → none
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, hcEq⟩ := h
        rw [← hcEq]
        exact hChain
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, hcEq⟩ := h
        rw [← hcEq]
        exact hChain

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
    · contradiction                                          -- peek? = none
    · -- some ch — cascade of nested ifs
      split at h
      · -- isDoubleQuoteBool ch: h : some (content, c.advance) = some result
        simp only [Option.some.injEq] at h
        rw [← h]
        exact IxCursor.advance_offset_monotonic c
      · split at h
        · -- isEscapeBool ch: inner match on c.advance.peek?
          split at h
          · -- some lbCh
            split at h
            · -- isLineBreakBool lbCh = true: line-continuation
              have hAdv : c.pos.offset ≤ c.advance.pos.offset :=
                IxCursor.advance_offset_monotonic c
              have hCLB : c.advance.pos.offset ≤ (consumeLineBreak c.advance).pos.offset :=
                consumeLineBreak_offset_monotonic _
              have hSW : (consumeLineBreak c.advance).pos.offset ≤
                         (skipWhitespace (consumeLineBreak c.advance)).pos.offset :=
                skipWhitespace_offset_monotonic _
              have hRec : (skipWhitespace (consumeLineBreak c.advance)).pos.offset ≤
                          result.2.pos.offset := ih _ _ h
              exact Nat.le_trans hAdv (Nat.le_trans hCLB (Nat.le_trans hSW hRec))
            · -- isLineBreakBool lbCh = false: normal escape
              split at h
              · rename_i _ _ _ decodedCh cAfterEsc hEsc
                have hAdvMono : c.pos.offset ≤ c.advance.pos.offset :=
                  IxCursor.advance_offset_monotonic c
                have hEscMono : c.advance.pos.offset ≤ cAfterEsc.pos.offset :=
                  processEscapeIx_offset_monotonic c.advance hEsc
                have hRec : cAfterEsc.pos.offset ≤ result.2.pos.offset := ih _ _ h
                exact Nat.le_trans hAdvMono (Nat.le_trans hEscMono hRec)
              · contradiction
          · contradiction
        · split at h
          · -- isLineBreakBool ch = true: fold and recurse
            have hFoldMono : c.pos.offset ≤ (foldQuotedNewlinesIx c).2.pos.offset :=
              foldQuotedNewlinesIx_offset_monotonic c
            have hRec : (foldQuotedNewlinesIx c).2.pos.offset ≤ result.2.pos.offset :=
              ih _ _ h
            exact Nat.le_trans hFoldMono hRec
          · -- regular char: advance and recurse
            have hRec : c.advance.pos.offset ≤ result.2.pos.offset := ih _ _ h
            exact Nat.le_trans (IxCursor.advance_offset_monotonic c) hRec

theorem scanDoubleQuotedIx_offset_lt {input : String} (c : IxCursor input)
    {result : String × IxCursor input}
    (h : scanDoubleQuotedIx c = some result) :
    c.pos.offset < result.2.pos.offset := by
  unfold scanDoubleQuotedIx at h
  split at h
  · -- some ch
    split at h
    · -- isDoubleQuoteBool ch
      rename_i hp _
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
    · contradiction                                          -- peek? = none
    · -- some ch — cascade of nested ifs
      split at h
      · -- isSingleQuoteBool ch: inner match on c.advance.peek?
        split at h
        · -- some next
          split at h
          · -- isSingleQuoteBool next: doubled-quote escape, recurse on c.advance.advance
            have hAdv1 : c.pos.offset ≤ c.advance.pos.offset :=
              IxCursor.advance_offset_monotonic c
            have hAdv2 : c.advance.pos.offset ≤ c.advance.advance.pos.offset :=
              IxCursor.advance_offset_monotonic c.advance
            have hRec : c.advance.advance.pos.offset ≤ result.2.pos.offset := ih _ _ h
            exact Nat.le_trans hAdv1 (Nat.le_trans hAdv2 hRec)
          · -- closing quote (single `'` followed by non-`'`): h : some (content, c.advance) = some result
            simp only [Option.some.injEq] at h
            rw [← h]
            exact IxCursor.advance_offset_monotonic c
        · -- none after single `'`: also closing quote
          simp only [Option.some.injEq] at h
          rw [← h]
          exact IxCursor.advance_offset_monotonic c
      · split at h
        · -- isLineBreakBool ch = true: fold and recurse
          have hFoldMono : c.pos.offset ≤ (foldQuotedNewlinesIx c).2.pos.offset :=
            foldQuotedNewlinesIx_offset_monotonic c
          have hRec : (foldQuotedNewlinesIx c).2.pos.offset ≤ result.2.pos.offset :=
            ih _ _ h
          exact Nat.le_trans hFoldMono hRec
        · -- regular char: advance and recurse
          have hRec : c.advance.pos.offset ≤ result.2.pos.offset := ih _ _ h
          exact Nat.le_trans (IxCursor.advance_offset_monotonic c) hRec

theorem scanSingleQuotedIx_offset_lt {input : String} (c : IxCursor input)
    {result : String × IxCursor input}
    (h : scanSingleQuotedIx c = some result) :
    c.pos.offset < result.2.pos.offset := by
  unfold scanSingleQuotedIx at h
  split at h
  · -- some ch
    split at h
    · -- isSingleQuoteBool ch
      rename_i hp _
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
  · contradiction

/-! ## Layer E4 / F2 — plain scalar offset monotonicity

The plain recogniser is total: it always returns a `String ×
IxCursor input`. Monotonicity therefore has no "success" guard.
The Step 4b additions introduce two line-break sub-branches (flow
folding via `foldQuotedNewlinesIx`; block continuation via
`handleBlockLineBreakIx`) whose chained monotonicity reduces to
the helper lemmas above. -/

theorem collectPlainScalarLoopIx_offset_monotonic {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) (fuel : Nat) :
    c.pos.offset ≤
    (collectPlainScalarLoopIx c content spaces inFlow contentIndent fuel).2.pos.offset := by
  induction fuel generalizing c content spaces with
  | zero => unfold collectPlainScalarLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectPlainScalarLoopIx
    split
    · exact Nat.le_refl _                                  -- peek? = none
    · -- some ch — cascade of nested ifs
      split
      · exact Nat.le_refl _                                -- '#' + spaces.length > 0
      split
      · exact Nat.le_refl _                                -- ':' terminates
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _ _)  -- ':' continues
      split
      · exact Nat.le_refl _                                -- flow indicator in flow
      split
      · -- line break: either flow fold or block fold
        split
        · -- inFlow: foldQuotedNewlinesIx
          exact Nat.le_trans (foldQuotedNewlinesIx_offset_monotonic c) (ih _ _ _)
        · -- block: handleBlockLineBreakIx
          split
          · exact Nat.le_refl _                            -- handleBlockLineBreakIx = none
          · rename_i _ _ _ folded cAfterFold hHandle
            have hHandleMono : c.pos.offset ≤ cAfterFold.pos.offset :=
              handleBlockLineBreakIx_offset_monotonic c contentIndent hHandle
            exact Nat.le_trans hHandleMono (ih _ _ _)
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _ _)  -- whitespace
      split
      · exact Nat.le_refl _                                -- not plain-safe
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _ _)  -- plain-safe content

theorem scanPlainScalarIx_offset_monotonic {input : String} (c : IxCursor input)
    (inFlow : Bool) (contentIndent : Nat) :
    c.pos.offset ≤ (scanPlainScalarIx c inFlow contentIndent).2.pos.offset := by
  unfold scanPlainScalarIx
  exact collectPlainScalarLoopIx_offset_monotonic c "" "" inFlow contentIndent _

/-! ## Layer F3 — block scalar offset monotonicity

The block-scalar code path threads several helpers:
`consumeExactSpacesIx`, `collectLineContentLoopIx`,
`parseBlockHeaderLoopIx`, and `collectBlockScalarLoopIx`. Each is
monotonic on the cursor offset; the entry-point `scanBlockScalarIx`
chains them together. -/

theorem consumeExactSpacesIx_offset_monotonic {input : String} (c : IxCursor input)
    (count : Nat) :
    c.pos.offset ≤ (consumeExactSpacesIx c count).2.pos.offset := by
  induction count generalizing c with
  | zero => unfold consumeExactSpacesIx; exact Nat.le_refl _
  | succ count' ih =>
    unfold consumeExactSpacesIx
    split
    · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance)
    · exact Nat.le_refl _

theorem collectLineContentLoopIx_offset_monotonic {input : String} (c : IxCursor input)
    (content : String) (fuel : Nat) :
    c.pos.offset ≤ (collectLineContentLoopIx c content fuel).2.pos.offset := by
  induction fuel generalizing c content with
  | zero => unfold collectLineContentLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectLineContentLoopIx
    split
    · split
      · exact Nat.le_refl _
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _)
    · exact Nat.le_refl _

theorem parseBlockHeaderLoopIx_offset_monotonic {input : String} (c : IxCursor input)
    (chomp : ChompStyle) (explicitOffset : Option Nat) (fuel : Nat) :
    c.pos.offset ≤
    (parseBlockHeaderLoopIx c chomp explicitOffset fuel).2.2.pos.offset := by
  induction fuel generalizing c chomp explicitOffset with
  | zero => unfold parseBlockHeaderLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold parseBlockHeaderLoopIx
    split
    · -- some ch — cascade of nested ifs
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _ _)
      · split
        · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _ _)
        · split
          · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih _ _ _)
          · exact Nat.le_refl _
    · exact Nat.le_refl _                                    -- peek? = none

theorem collectBlockScalarLoopIx_offset_monotonic {input : String} (c : IxCursor input)
    (rawContent : String) (contentIndent : Nat) (fuel : Nat) :
    c.pos.offset ≤
    (collectBlockScalarLoopIx c rawContent contentIndent fuel).2.pos.offset := by
  induction fuel generalizing c rawContent with
  | zero => unfold collectBlockScalarLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectBlockScalarLoopIx
    have hSp : c.pos.offset ≤ (consumeExactSpacesIx c contentIndent).2.pos.offset :=
      consumeExactSpacesIx_offset_monotonic c contentIndent
    split
    · exact Nat.le_refl _                                  -- document boundary
    · split
      · exact hSp                                          -- cAfterSp.peek? = none
      · split
        · -- line break: consumeLineBreak + recurse
          have hCLB :
              (consumeExactSpacesIx c contentIndent).2.pos.offset ≤
              (consumeLineBreak (consumeExactSpacesIx c contentIndent).2).pos.offset :=
            consumeLineBreak_offset_monotonic _
          exact Nat.le_trans hSp (Nat.le_trans hCLB (ih _ _))
        · split
          · exact Nat.le_refl _                            -- short line: return c
          · -- normal line: collect content + inspect cAfterLine
            have hLine :
                (consumeExactSpacesIx c contentIndent).2.pos.offset ≤
                (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                    input.utf8ByteSize).2.pos.offset :=
              collectLineContentLoopIx_offset_monotonic _ _ _
            split
            · split
              · -- line break at end of line: consume + recurse
                have hCLB :
                    (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                        input.utf8ByteSize).2.pos.offset ≤
                    (consumeLineBreak
                      (collectLineContentLoopIx (consumeExactSpacesIx c contentIndent).2 ""
                          input.utf8ByteSize).2).pos.offset :=
                  consumeLineBreak_offset_monotonic _
                exact Nat.le_trans hSp
                  (Nat.le_trans hLine (Nat.le_trans hCLB (ih _ _)))
              · -- non-LF at end of line: recurse from cAfterLine
                exact Nat.le_trans hSp (Nat.le_trans hLine (ih _ _))
            · -- peek? = none after line: return cAfterLine
              exact Nat.le_trans hSp hLine

/-- Helper: the post-header cursor is monotonic relative to `c`. -/
theorem blockHeaderToBodyIx_offset_monotonic {input : String} (c : IxCursor input) :
    c.pos.offset ≤ (blockHeaderToBodyIx c).pos.offset := by
  unfold blockHeaderToBodyIx
  have hAdv : c.pos.offset ≤ c.advance.pos.offset :=
    IxCursor.advance_offset_monotonic c
  have hHdr : c.advance.pos.offset ≤
              (parseBlockHeaderLoopIx c.advance .clip none 2).2.2.pos.offset :=
    parseBlockHeaderLoopIx_offset_monotonic _ _ _ _
  have hSW : (parseBlockHeaderLoopIx c.advance .clip none 2).2.2.pos.offset ≤
             (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).pos.offset :=
    skipWhitespace_offset_monotonic _
  have hComm :
      (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).pos.offset ≤
      (if (match (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).peek?
            with | some d => isCommentBool d | none => false) then
         skipCommentText
           (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).advance
       else
         skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).pos.offset := by
    by_cases hp :
        (match (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).peek?
              with | some d => isCommentBool d | none => false) = true
    · rw [if_pos hp]
      exact Nat.le_trans (IxCursor.advance_offset_monotonic _)
        (skipCommentText_offset_monotonic _)
    · rw [if_neg hp]
      exact Nat.le_refl _
  have hCLB :
      (if (match (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).peek?
            with | some d => isCommentBool d | none => false) then
         skipCommentText
           (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).advance
       else
         skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).pos.offset ≤
      (consumeLineBreak
        (if (match (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).peek?
              with | some d => isCommentBool d | none => false) then
           skipCommentText
             (skipWhitespace (parseBlockHeaderLoopIx c.advance .clip none 2).2.2).advance
         else
           skipWhitespace
             (parseBlockHeaderLoopIx c.advance .clip none 2).2.2)).pos.offset :=
    consumeLineBreak_offset_monotonic _
  exact Nat.le_trans hAdv (Nat.le_trans hHdr (Nat.le_trans hSW
    (Nat.le_trans hComm hCLB)))

theorem scanBlockScalarIx_offset_monotonic {input : String} (c : IxCursor input)
    (parentIndent : Nat) {result : String × ScalarStyle × IxCursor input}
    (h : scanBlockScalarIx c parentIndent = some result) :
    c.pos.offset ≤ result.2.2.pos.offset := by
  unfold scanBlockScalarIx at h
  split at h
  · -- some ch
    split at h
    · -- ch = '|' || ch = '>': success branch — result.2.2 is the body cursor.
      have hHdrToBody : c.pos.offset ≤ (blockHeaderToBodyIx c).pos.offset :=
        blockHeaderToBodyIx_offset_monotonic c
      have hBody : (blockHeaderToBodyIx c).pos.offset ≤
        (collectBlockScalarLoopIx (blockHeaderToBodyIx c) ""
          (match (parseBlockHeaderLoopIx c.advance .clip none 2).2.1 with
            | some m => parentIndent + m
            | none   =>
              autoDetectBlockScalarIndentIx (blockHeaderToBodyIx c) (parentIndent + 1))
          input.utf8ByteSize).2.pos.offset :=
        collectBlockScalarLoopIx_offset_monotonic _ _ _ _
      simp only [Option.some.injEq] at h
      rw [← h]
      exact Nat.le_trans hHdrToBody hBody
    · contradiction                                        -- not '|' or '>'
  · contradiction                                          -- EOF

/-! ## Layer E1.4 — Hex-escape value-correctness (Step 5b.4)

Carried-forward obligation from Step 4a: `hexStringValue` of a
hex-digit string equals the decoded `Nat` value (mod overflow checks).

Decomposed into four layers:

1. **Digit bound** — `hexDigitValue_lt_16`: for every hex digit `ch`
   (`isHexDigitBool ch = true`), `hexDigitValue ch < 16`.
2. **Snoc law** — `hexStringValue_push`: `hexStringValue (s.push c)
   = hexStringValue s * 16 + hexDigitValue c`. Lifts `String.foldl`
   to `List.foldl` via `String.foldl_eq_foldl_toList` and
   `String.toList_push`.
3. **Power bound** — `hexStringValue_lt_pow`: when every character
   of `s` is a hex digit, `hexStringValue s < 16 ^ s.length`. Proof:
   `String.push_induction` chaining (1) and (2).
4. **Escape spec** — `parseHexEscapeIx_decoded`: on success,
   `parseHexEscapeIx c n` returns `Char.ofNat
   (hexStringValue digits)` with the value-range guard
   `< 0x110000` already discharged. -/

theorem hexDigitValue_lt_16 {ch : Char} (h : isHexDigitBool ch = true) :
    hexDigitValue ch < 16 := by
  -- Push hypotheses *and* goal to Nat in one simp pass.
  simp only [isHexDigitBool, Bool.or_eq_true, Bool.and_eq_true,
             decide_eq_true_eq, UInt32.le_iff_toNat_le] at h
  unfold hexDigitValue
  simp only [Char.toNat, UInt32.le_iff_toNat_le]
  -- Concrete UInt32 → Nat literal equalities so `omega` sees plain numbers.
  have h30 : (0x30 : UInt32).toNat = 48 := by native_decide
  have h39 : (0x39 : UInt32).toNat = 57 := by native_decide
  have h41 : (0x41 : UInt32).toNat = 65 := by native_decide
  have h46 : (0x46 : UInt32).toNat = 70 := by native_decide
  have h61 : (0x61 : UInt32).toNat = 97 := by native_decide
  have h66 : (0x66 : UInt32).toNat = 102 := by native_decide
  -- `||` is left-associative, so `a || b || c = true` simps to `(a ∨ b) ∨ c`.
  -- Avoid `rcases` — it tries to destruct `Nat.le` and chokes.
  cases h with
  | inr hLower =>
    have hLo := hLower.1
    have hHi := hLower.2
    rw [h61] at hLo; rw [h66] at hHi
    rw [if_neg, if_pos]
    · omega
    · rw [h61]; omega
    · intro hCond; have hLe := hCond.2; rw [h39] at hLe; omega
  | inl hDU =>
    cases hDU with
    | inl hDigit =>
      have hLo := hDigit.1
      have hHi := hDigit.2
      rw [h30] at hLo; rw [h39] at hHi
      rw [if_pos]
      · omega
      · rw [h30, h39]; exact ⟨hLo, hHi⟩
    | inr hUpper =>
      have hLo := hUpper.1
      have hHi := hUpper.2
      rw [h41] at hLo; rw [h46] at hHi
      rw [if_neg, if_neg]
      · omega
      · intro hGe; rw [h61] at hGe; omega
      · intro hCond; have hLe := hCond.2; rw [h39] at hLe; omega

@[simp] theorem hexStringValue_empty : hexStringValue "" = 0 := by
  unfold hexStringValue
  rw [String.foldl_eq_foldl_toList]
  rfl

theorem hexStringValue_push (s : String) (ch : Char) :
    hexStringValue (s.push ch) = hexStringValue s * 16 + hexDigitValue ch := by
  unfold hexStringValue
  rw [String.foldl_eq_foldl_toList, String.toList_push, List.foldl_append,
      String.foldl_eq_foldl_toList]
  rfl

theorem hexStringValue_lt_pow {s : String}
    (hAll : ∀ c ∈ s.toList, isHexDigitBool c = true) :
    hexStringValue s < 16 ^ s.length := by
  induction s using String.push_induction with
  | empty =>
    rw [hexStringValue_empty]
    show 0 < 16 ^ "".length
    simp
  | push b ch ih =>
    have hCh : isHexDigitBool ch = true := by
      apply hAll
      rw [String.toList_push]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hRest : ∀ c ∈ b.toList, isHexDigitBool c = true := by
      intro c hc
      apply hAll
      rw [String.toList_push]
      exact List.mem_append_left _ hc
    have hb : hexStringValue b < 16 ^ b.length := ih hRest
    have hch : hexDigitValue ch < 16 := hexDigitValue_lt_16 hCh
    rw [hexStringValue_push, String.length_push, Nat.pow_succ]
    have hStep : (hexStringValue b + 1) * 16 ≤ 16 ^ b.length * 16 :=
      Nat.mul_le_mul_right 16 hb
    -- (hexStringValue b + 1) * 16 = hexStringValue b * 16 + 16
    -- hch < 16, so hexStringValue b * 16 + hch < hexStringValue b * 16 + 16
    -- ≤ 16 ^ b.length * 16.
    omega

theorem parseHexEscapeIx_decoded {input : String} (c : IxCursor input) (n : Nat)
    {ch : Char} {c' : IxCursor input}
    (h : parseHexEscapeIx c n = some (ch, c')) :
    hexStringValue (collectHexDigitsLoopIx c "" n).1 < 0x110000
    ∧ ch = Char.ofNat (hexStringValue (collectHexDigitsLoopIx c "" n).1)
    ∧ c' = (collectHexDigitsLoopIx c "" n).2 := by
  unfold parseHexEscapeIx at h
  split at h
  · contradiction                                        -- length ≠ n
  · split at h
    · rename_i hLt
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hcEq, hc'Eq⟩ := h
      exact ⟨hLt, hcEq.symm, hc'Eq.symm⟩
    · contradiction                                      -- value ≥ 0x110000

/-! ## Layer F.1 — Auto-detected block-scalar indent ≥ `minContentIndent` (Step 5b.5)

`autoDetectBlockScalarIndentLoopIx` probes a sequence of leading
whitespace runs to determine the content indent of a block scalar
when the header omits an explicit indicator. The loop returns a
`Nat` (the chosen indent), not a cursor — so the relevant
correctness property is a *bound*, not a monotonicity statement.

The downstream proofs (block-scalar content correctness, Step 5b.6)
need to know that the auto-detected indent is at least the
spec-mandated minimum. This is the carried-forward obligation for
Step 5b.5.

The proof is a four-way `split` per `fuel + 1` step:
1. Base (`fuel = 0`) and EOF (`none`) and end-of-fuel branches all
   return `if maxWSCol > minContentIndent then maxWSCol else minContentIndent`
   — `omega` from either disjunct.
2. Non-blank line: return `if probeAfterSp.pos.col > minContentIndent
   then probeAfterSp.pos.col else minContentIndent` — same `omega`.
3. Blank line: recurse on a new `maxWSCol'`. The IH gives
   `minContentIndent ≤ result` for any `maxWSCol`, so it discharges
   directly. -/

theorem autoDetectBlockScalarIndentLoopIx_ge_min
    {input : String} (probe : IxCursor input)
    (maxWSCol minContentIndent fuel : Nat) :
    minContentIndent ≤
      autoDetectBlockScalarIndentLoopIx probe maxWSCol minContentIndent fuel := by
  induction fuel generalizing probe maxWSCol with
  | zero =>
    unfold autoDetectBlockScalarIndentLoopIx
    split <;> omega
  | succ fuel ih =>
    unfold autoDetectBlockScalarIndentLoopIx
    -- Three nested splits: (1) the `let (probeAfterSp, _) := skipSpaces probe`
    -- prod destructure (1 case), (2) `match probeAfterSp.peek?`
    -- (some/none), (3) inside `some ch`, `if isLineBreakBool ch`.
    split  -- (1) prod destructure
    split  -- (2) peek?
    · -- some ch at probeAfterSp
      split  -- (3) isLineBreakBool
      · -- true: recurse — IH gives `minContentIndent ≤ result` for any maxWSCol'
        apply ih
      · -- false: result = max probeAfterSp.pos.col minContentIndent
        split <;> omega
    · -- none — EOF: result = max maxWSCol minContentIndent
      split <;> omega

theorem autoDetectBlockScalarIndentIx_ge_min
    {input : String} (c : IxCursor input) (minContentIndent : Nat) :
    minContentIndent ≤ autoDetectBlockScalarIndentIx c minContentIndent := by
  unfold autoDetectBlockScalarIndentIx
  exact autoDetectBlockScalarIndentLoopIx_ge_min c 0 minContentIndent _

end L4YAML.Scanner.Indexed
