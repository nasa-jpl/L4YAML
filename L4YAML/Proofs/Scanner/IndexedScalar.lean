/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedIndent
import L4YAML.Proofs.Scanner.ScannerPlainContent
import L4YAML.Proofs.Scanner.ScannerPlainScalar
import L4YAML.Proofs.Foundation.StringProperties

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
      · -- line break: either flow fold or block fold (each guarded by `#`-after-fold check)
        split
        · -- inFlow: foldQuotedNewlinesIx + post-fold `#` check
          split
          · exact Nat.le_refl _                            -- post-fold peek = some '#'
          · exact Nat.le_trans (foldQuotedNewlinesIx_offset_monotonic c) (ih _ _ _)
        · -- block: handleBlockLineBreakIx + post-fold `#` check
          split
          · exact Nat.le_refl _                            -- handleBlockLineBreakIx = none
          · rename_i folded cAfterFold hHandle
            have hHandleMono : c.pos.offset ≤ cAfterFold.pos.offset :=
              handleBlockLineBreakIx_offset_monotonic c contentIndent hHandle
            split
            · exact Nat.le_refl _                          -- post-fold peek = some '#'
            · exact Nat.le_trans hHandleMono (ih _ _ _)
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

/-! ## Layer F.2 — Block-scalar content correctness (Step 5b.6)

Carried-forward Step 4b obligation: `foldBlockContent` and `applyChomp`
match their YAML 1.2.2 spec semantics. The fold step lives in §8.1.3
([170]–[181]); chomping lives in §8.1.1 ([160]).

`applyChomp` is a three-way case split on `[160]`'s `c-chomping-indicator`:
- `.keep` — preserve all trailing newlines (identity)
- `.strip` — remove every trailing `\n` (`stripTrailingNewlines`)
- `.clip` — keep at most one trailing `\n` (exactly one iff `raw`
  ended with `\n`)

`foldBlockContent` is the four-state machine over the raw block content
(`FoldState`: `start` / `content` / `empty` / `more`). Both are pure
`String → String` transformers, so their correctness lemmas reduce to
*definitional* unfolds — they serve as spec-traceability anchors for the
downstream multi-line consumers (Steps 5b.7 quoted, 5b.8 plain). -/

theorem applyChomp_keep (raw : String) :
    applyChomp .keep raw = raw :=
  rfl

theorem applyChomp_strip (raw : String) :
    applyChomp .strip raw = stripTrailingNewlines raw :=
  rfl

theorem applyChomp_clip_of_endsWith {raw : String}
    (h : raw.endsWith (String.singleton lineFeedChar) = true) :
    applyChomp .clip raw =
      stripTrailingNewlines raw ++ String.singleton lineFeedChar := by
  simp [applyChomp, h]

theorem applyChomp_clip_of_not_endsWith {raw : String}
    (h : raw.endsWith (String.singleton lineFeedChar) = false) :
    applyChomp .clip raw = stripTrailingNewlines raw := by
  simp [applyChomp, h]

theorem foldBlockContentGo_nil (acc : String) (st : FoldState) (pending : Nat) :
    foldBlockContentGo [] acc st pending = acc :=
  rfl

theorem foldBlockContent_empty :
    foldBlockContent "" = "" :=
  rfl

/-! ## Layer F.3 — Quoted multi-line content correctness (Step 5b.7)

Carried-forward Step 4b obligation: pin each branch of `foldQuotedNewlinesIx`
(§6.5 [73] / [74]) and the multi-line fold branches of
`collectDoubleQuotedLoopIx` (§7.3.1 [111]–[116]) and
`collectSingleQuotedLoopIx` (§7.3.2 [122]–[125]) to its YAML 1.2.2 spec rule.

`foldQuotedNewlinesIx` produces the *folded replacement* for a quoted-scalar
line break:
- `b-l-trimmed(n,c)` [71]: ≥1 trailing blank lines → `String.ofList
  (List.replicate emptyCount '\n')`.
- `b-as-space` [70]: exactly one break → `String.singleton spaceChar`.

`collectDoubleQuotedLoopIx` and `collectSingleQuotedLoopIx` each consume a
quoted body character-at-a-time; the branches matter because their
content-composition is what the spec's `nb-double-text` /
`nb-single-text` productions describe. The "regular character" and
"escape" branches are routine pushes covered by the offset-monotonicity
work in Layers E2/E3 above; the lemmas below pin the *delimiter*,
*doubled-quote*, and *line-break-fold* branches — those are the ones
downstream proofs will quote when reasoning about content equality. -/

theorem foldQuotedNewlinesIx_of_blank_lines {input : String} (c : IxCursor input)
    (h : (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2 > 0) :
    foldQuotedNewlinesIx c =
      (String.ofList
         (List.replicate
           (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2
           lineFeedChar),
       skipWhitespace
         (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1) := by
  unfold foldQuotedNewlinesIx
  simp [h]

theorem foldQuotedNewlinesIx_of_single_break {input : String} (c : IxCursor input)
    (h : (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).2 = 0) :
    foldQuotedNewlinesIx c =
      (String.singleton spaceChar,
       skipWhitespace
         (skipBlankLinesLoopIx (consumeLineBreak c) 0 input.utf8ByteSize).1) := by
  unfold foldQuotedNewlinesIx
  simp [h]

theorem collectDoubleQuotedLoopIx_zero {input : String}
    (c : IxCursor input) (content : String) :
    collectDoubleQuotedLoopIx c content 0 = none :=
  rfl

theorem collectDoubleQuotedLoopIx_closing {input : String}
    (c : IxCursor input) (content : String) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hQuote : isDoubleQuoteBool ch = true) :
    collectDoubleQuotedLoopIx c content (fuel + 1) = some (content, c.advance) := by
  unfold collectDoubleQuotedLoopIx
  rw [hPeek]
  simp [hQuote]

theorem collectDoubleQuotedLoopIx_linebreak {input : String}
    (c : IxCursor input) (content : String) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotQuote : isDoubleQuoteBool ch = false)
    (hNotEscape : isEscapeBool ch = false)
    (hLineBreak : isLineBreakBool ch = true) :
    collectDoubleQuotedLoopIx c content (fuel + 1) =
      collectDoubleQuotedLoopIx (foldQuotedNewlinesIx c).2
        (trimTrailingWSIx content ++ (foldQuotedNewlinesIx c).1) fuel := by
  conv => lhs; unfold collectDoubleQuotedLoopIx
  rw [hPeek]
  simp [hNotQuote, hNotEscape, hLineBreak]

theorem collectSingleQuotedLoopIx_zero {input : String}
    (c : IxCursor input) (content : String) :
    collectSingleQuotedLoopIx c content 0 = none :=
  rfl

theorem collectSingleQuotedLoopIx_doubled {input : String}
    (c : IxCursor input) (content : String) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hQuote : isSingleQuoteBool ch = true)
    {next : Char} (hPeekAdv : c.advance.peek? = some next)
    (hNext : isSingleQuoteBool next = true) :
    collectSingleQuotedLoopIx c content (fuel + 1) =
      collectSingleQuotedLoopIx c.advance.advance
        (content.push singleQuoteChar) fuel := by
  conv => lhs; unfold collectSingleQuotedLoopIx
  rw [hPeek]
  simp [hQuote, hPeekAdv, hNext]

theorem collectSingleQuotedLoopIx_closing_some {input : String}
    (c : IxCursor input) (content : String) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hQuote : isSingleQuoteBool ch = true)
    {next : Char} (hPeekAdv : c.advance.peek? = some next)
    (hNext : isSingleQuoteBool next = false) :
    collectSingleQuotedLoopIx c content (fuel + 1) = some (content, c.advance) := by
  unfold collectSingleQuotedLoopIx
  rw [hPeek]
  simp [hQuote, hPeekAdv, hNext]

theorem collectSingleQuotedLoopIx_closing_none {input : String}
    (c : IxCursor input) (content : String) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hQuote : isSingleQuoteBool ch = true)
    (hPeekAdv : c.advance.peek? = none) :
    collectSingleQuotedLoopIx c content (fuel + 1) = some (content, c.advance) := by
  unfold collectSingleQuotedLoopIx
  rw [hPeek]
  simp [hQuote, hPeekAdv]

theorem collectSingleQuotedLoopIx_linebreak {input : String}
    (c : IxCursor input) (content : String) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotQuote : isSingleQuoteBool ch = false)
    (hLineBreak : isLineBreakBool ch = true) :
    collectSingleQuotedLoopIx c content (fuel + 1) =
      collectSingleQuotedLoopIx (foldQuotedNewlinesIx c).2
        (trimTrailingWSIx content ++ (foldQuotedNewlinesIx c).1) fuel := by
  conv => lhs; unfold collectSingleQuotedLoopIx
  rw [hPeek]
  simp [hNotQuote, hLineBreak]

/-! ## Layer F.4 — Plain multi-line content correctness (Step 5b.8)

Carried-forward Step 4b obligation: pin each branch of
`collectPlainScalarLoopIx` (§7.3.3 [131]–[135]) to its YAML 1.2.2 spec
rule. The plain-scalar loop is the most branch-heavy collector in the
scanner: 11 outcomes covering EOF, comment, mapping-value (terminating
and continuing), flow-indicator (flow context), line-break fold (flow
*and* block, each with its own continuation helper), whitespace, plain-
unsafe terminators, and the plain-safe content character. Each lemma
fixes the post-`peek?` cascade for one branch.

Spec rules:
- `ns-plain(n,c)` [131], `nb-ns-plain-in-line(c)` [132],
  `s-ns-plain-next-line(n)` [133], `ns-plain-multi-line(n,c)` [134],
  `ns-plain-one-line(c)` [135] — the threaded `content ++ folded`
  composition is what `ns-plain-multi-line` describes; the in-line
  and next-line splits are visible in the `_linebreak_flow` /
  `_linebreak_block_some` branches.

Proof shape mirrors Layer F.3 (Step 5b.7) — `rfl` for `_zero`,
`unfold + rw + simp` for non-recursive branches, and
`conv => lhs; unfold …` for the five recursive branches whose RHS is
another `collectPlainScalarLoopIx` call (Reflection 57). -/

theorem collectPlainScalarLoopIx_zero {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) :
    collectPlainScalarLoopIx c content spaces inFlow contentIndent 0 =
      (content ++ spaces, c) :=
  rfl

theorem collectPlainScalarLoopIx_eof {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) (fuel : Nat)
    (hPeek : c.peek? = none) :
    collectPlainScalarLoopIx c content spaces inFlow contentIndent (fuel + 1) =
      (content ++ spaces, c) := by
  unfold collectPlainScalarLoopIx
  rw [hPeek]

theorem collectPlainScalarLoopIx_comment {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hComment : isCommentBool ch = true)
    (hSpaces : spaces.length > 0) :
    collectPlainScalarLoopIx c content spaces inFlow contentIndent (fuel + 1) =
      (content, c) := by
  unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hComment, hSpaces]

theorem collectPlainScalarLoopIx_colon_terminate {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hMapVal : isMappingValueBool ch = true)
    (hColon : colonTerminatesPlain c inFlow = true) :
    collectPlainScalarLoopIx c content spaces inFlow contentIndent (fuel + 1) =
      (content, c) := by
  unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotComment, hMapVal, hColon]

theorem collectPlainScalarLoopIx_colon_continue {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hMapVal : isMappingValueBool ch = true)
    (hColon : colonTerminatesPlain c inFlow = false) :
    collectPlainScalarLoopIx c content spaces inFlow contentIndent (fuel + 1) =
      collectPlainScalarLoopIx c.advance
        (content ++ spaces ++ String.singleton ch) "" inFlow contentIndent fuel := by
  conv => lhs; unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotComment, hMapVal, hColon]

theorem collectPlainScalarLoopIx_flow_indicator {input : String} (c : IxCursor input)
    (content spaces : String) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hFlowInd : isFlowIndicatorBool ch = true) :
    collectPlainScalarLoopIx c content spaces true contentIndent (fuel + 1) =
      (content, c) := by
  unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotComment, hNotMapVal, hFlowInd]

/-- `_linebreak_flow_continue`: flow-context line break where the
    post-fold cursor does NOT peek `#` (continues into the next line).
    With the `#`-after-fold termination added in Phase 3 Step 6d.1e.11,
    this requires the precondition `cAfterFold.peek? ≠ some '#'`. -/
theorem collectPlainScalarLoopIx_linebreak_flow_continue {input : String} (c : IxCursor input)
    (content spaces : String) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hNotFlowInd : isFlowIndicatorBool ch = false)
    (hLineBreak : isLineBreakBool ch = true)
    (hNotHash : (foldQuotedNewlinesIx c).2.peek? ≠ some '#') :
    collectPlainScalarLoopIx c content spaces true contentIndent (fuel + 1) =
      collectPlainScalarLoopIx (foldQuotedNewlinesIx c).2
        (content ++ (foldQuotedNewlinesIx c).1) "" true contentIndent fuel := by
  conv => lhs; unfold collectPlainScalarLoopIx
  rw [hPeek]
  cases hp : (foldQuotedNewlinesIx c).2.peek? with
  | none => simp [hNotComment, hNotMapVal, hNotFlowInd, hLineBreak, hp]
  | some ch' =>
    have h_ne : ch' ≠ '#' := by intro he; subst he; exact hNotHash hp
    simp [hNotComment, hNotMapVal, hNotFlowInd, hLineBreak, hp, h_ne]

/-- `_linebreak_flow_hash`: flow-context line break where the post-fold
    cursor peeks `#` — plain scalar terminates at the pre-fold cursor. -/
theorem collectPlainScalarLoopIx_linebreak_flow_hash {input : String} (c : IxCursor input)
    (content spaces : String) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hNotFlowInd : isFlowIndicatorBool ch = false)
    (hLineBreak : isLineBreakBool ch = true)
    (hHash : (foldQuotedNewlinesIx c).2.peek? = some '#') :
    collectPlainScalarLoopIx c content spaces true contentIndent (fuel + 1) =
      (content, c) := by
  conv => lhs; unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotComment, hNotMapVal, hNotFlowInd, hLineBreak, hHash]

theorem collectPlainScalarLoopIx_linebreak_block_none {input : String} (c : IxCursor input)
    (content spaces : String) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hLineBreak : isLineBreakBool ch = true)
    (hHandle : handleBlockLineBreakIx c contentIndent = none) :
    collectPlainScalarLoopIx c content spaces false contentIndent (fuel + 1) =
      (content, c) := by
  unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotComment, hNotMapVal, hLineBreak, hHandle]

/-- `_linebreak_block_some_continue`: block-context line break where the
    post-fold cursor does NOT peek `#`. -/
theorem collectPlainScalarLoopIx_linebreak_block_some_continue {input : String} (c : IxCursor input)
    (content spaces : String) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hLineBreak : isLineBreakBool ch = true)
    {folded : String} {cAfterFold : IxCursor input}
    (hHandle : handleBlockLineBreakIx c contentIndent = some (folded, cAfterFold))
    (hNotHash : cAfterFold.peek? ≠ some '#') :
    collectPlainScalarLoopIx c content spaces false contentIndent (fuel + 1) =
      collectPlainScalarLoopIx cAfterFold (content ++ folded) "" false contentIndent fuel := by
  conv => lhs; unfold collectPlainScalarLoopIx
  rw [hPeek]
  cases hp : cAfterFold.peek? with
  | none => simp [hNotComment, hNotMapVal, hLineBreak, hHandle]
  | some ch' =>
    have h_ne : ch' ≠ '#' := by intro he; subst he; exact hNotHash hp
    simp [hNotComment, hNotMapVal, hLineBreak, hHandle, h_ne]

/-- `_linebreak_block_some_hash`: block-context line break where the
    post-fold cursor peeks `#` — plain scalar terminates at the pre-fold
    cursor. -/
theorem collectPlainScalarLoopIx_linebreak_block_some_hash {input : String} (c : IxCursor input)
    (content spaces : String) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hLineBreak : isLineBreakBool ch = true)
    {folded : String} {cAfterFold : IxCursor input}
    (hHandle : handleBlockLineBreakIx c contentIndent = some (folded, cAfterFold))
    (hHash : cAfterFold.peek? = some '#') :
    collectPlainScalarLoopIx c content spaces false contentIndent (fuel + 1) =
      (content, c) := by
  conv => lhs; unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotComment, hNotMapVal, hLineBreak, hHandle, hHash]

theorem collectPlainScalarLoopIx_whitespace {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hNotFlowInd : (inFlow && isFlowIndicatorBool ch) = false)
    (hNotLineBreak : isLineBreakBool ch = false)
    (hWhitespace : isWhiteSpaceBool ch = true) :
    collectPlainScalarLoopIx c content spaces inFlow contentIndent (fuel + 1) =
      collectPlainScalarLoopIx c.advance content (spaces.push ch) inFlow contentIndent fuel := by
  conv => lhs; unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotComment, hNotMapVal, hNotFlowInd, hNotLineBreak, hWhitespace]

theorem collectPlainScalarLoopIx_not_plain_safe {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hNotFlowInd : (inFlow && isFlowIndicatorBool ch) = false)
    (hNotLineBreak : isLineBreakBool ch = false)
    (hNotWhitespace : isWhiteSpaceBool ch = false)
    (hNotPlainSafe : isPlainSafeBool ch inFlow = false) :
    collectPlainScalarLoopIx c content spaces inFlow contentIndent (fuel + 1) =
      (content, c) := by
  unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotComment, hNotMapVal, hNotFlowInd, hNotLineBreak, hNotWhitespace, hNotPlainSafe]

theorem collectPlainScalarLoopIx_content {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotComment : isCommentBool ch = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hNotFlowInd : (inFlow && isFlowIndicatorBool ch) = false)
    (hNotLineBreak : isLineBreakBool ch = false)
    (hNotWhitespace : isWhiteSpaceBool ch = false)
    (hPlainSafe : isPlainSafeBool ch inFlow = true) :
    collectPlainScalarLoopIx c content spaces inFlow contentIndent (fuel + 1) =
      collectPlainScalarLoopIx c.advance
        (content ++ spaces ++ String.singleton ch) "" inFlow contentIndent fuel := by
  conv => lhs; unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotComment, hNotMapVal, hNotFlowInd, hNotLineBreak, hNotWhitespace, hPlainSafe]

/-- Generalized content-arm reduction: allows `ch = '#'` provided
    `spaces.length = 0` (which makes the loop's `isComment ch &&
    spaces.length > 0` check fail). Used by the §B3.3 indexed
    port. -/
theorem collectPlainScalarLoopIx_content_gen {input : String} (c : IxCursor input)
    (content spaces : String) (inFlow : Bool) (contentIndent : Nat) (fuel : Nat)
    {ch : Char} (hPeek : c.peek? = some ch)
    (hNotCommArm : (isCommentBool ch && decide (spaces.length > 0)) = false)
    (hNotMapVal : isMappingValueBool ch = false)
    (hNotFlowInd : (inFlow && isFlowIndicatorBool ch) = false)
    (hNotLineBreak : isLineBreakBool ch = false)
    (hNotWhitespace : isWhiteSpaceBool ch = false)
    (hPlainSafe : isPlainSafeBool ch inFlow = true) :
    collectPlainScalarLoopIx c content spaces inFlow contentIndent (fuel + 1) =
      collectPlainScalarLoopIx c.advance
        (content ++ spaces ++ String.singleton ch) "" inFlow contentIndent fuel := by
  conv => lhs; unfold collectPlainScalarLoopIx
  rw [hPeek]
  simp [hNotCommArm, hNotMapVal, hNotFlowInd, hNotLineBreak, hNotWhitespace, hPlainSafe]

/-! ## Layer F.5 — Plain-scalar content validity (Step 6d.1e.11)

Carried-forward Step 4b obligation, addressing the §11h
`scanNextTokenIx_dispatchContent_preserves_*` discharge in
`Proofs/Production/IndexedScannerPlainScalarValid.lean`. The legacy
file `Proofs/Scanner/ScannerPlainScalar.lean` (B3.4) proves an
analogous content-validity theorem for the legacy plain-scalar
recogniser; the port mirrors that proof's structure but adapts to
the indexed substrate (`IxCursor input` instead of `ScannerState`,
direct branch analysis instead of the legacy `_terminates?` helper).

### Adaptations from the legacy proof

The indexed `collectPlainScalarLoopIx` does not use a separate
`_terminates?` helper — termination cases are inlined as direct
branches of the loop body. Three structural differences from the
legacy:

1. **No `_terminates?` helper**. Termination via `:`-terminator,
   `'#'`, flow-indicator, EOF, and line-break-block-none are direct
   branches with their own `Loop_*` lemmas (Layer F.4). The legacy
   `terminates_preserves_all` / `terminates_none_colon_peekAt_nonblank`
   become direct case-splits via the existing branch lemmas.

2. **EOF returns `(content ++ spaces, c)`, not `(content, c)`**.
   The indexed loop merges trailing whitespace into the raw output
   at EOF; the wrapping `scanPlainScalarIx` then trims via
   `trimTrailingWSIx`. Since the invariant ensures `spaces` is all
   `isWhiteSpaceBool`-true, `trimTrailingWSIx (content ++ spaces) =
   trimTrailingWSIx content`. The content's last character (when
   non-empty) is always non-whitespace by structural invariant, so
   `trimTrailingWSIx content = content` in that case.

3. **`IxCursor` peek primitives** replace `ScannerState.peek?` /
   `peekAt?`. Boundary conditions threading through
   `colonTerminatesPlain c inFlow = false` give us
   `c.peekAt? 1 = some n ∧ ¬isBlank n`, mirroring the legacy
   `terminates_none_colon_peekAt_nonblank` fact. -/

open L4YAML.Grammar
open L4YAML.Proofs.StringProperties
open L4YAML.Proofs.ScannerPlainScalar
open L4YAML.Proofs.ScannerPlainContent

/-! ### Branch shape facts: `colonTerminatesPlain` and `handleBlockLineBreakIx`/`foldQuotedNewlinesIx` -/

/-- When `colonTerminatesPlain c inFlow = false`, the character at
    `peekAt? 1` exists, is not blank, and (in flow context) is not a
    flow indicator. This is the indexed analog of legacy
    `terminates_none_colon_peekAt_nonblank`. -/
theorem colonTerminatesPlain_false_iff {input : String} (c : IxCursor input)
    (inFlow : Bool) (h : colonTerminatesPlain c inFlow = false) :
    ∃ n, c.peekAt? 1 = some n ∧ isBlankBool n = false ∧
      (inFlow && isFlowIndicatorBool n) = false := by
  unfold colonTerminatesPlain at h
  match hpa : c.peekAt? 1 with
  | none => rw [hpa] at h; simp at h
  | some n =>
    rw [hpa] at h
    simp only [Bool.or_eq_false_iff] at h
    exact ⟨n, rfl, h.1, h.2⟩

/-- `handleBlockLineBreakIx` returns either `" "` or
    `replicate '\n'` when it succeeds. Indexed twin of legacy
    `handleBlockLineBreak_content_form`. -/
theorem handleBlockLineBreakIx_content_form {input : String} (c : IxCursor input)
    (contentIndent : Nat) {folded : String} {c' : IxCursor input}
    (h : handleBlockLineBreakIx c contentIndent = some (folded, c')) :
    folded = " " ∨ (∃ n, n > 0 ∧ folded = String.ofList (List.replicate n '\n')) := by
  unfold handleBlockLineBreakIx at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · rename_i hgt
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        right; exact ⟨_, hgt, this.1.symm⟩
      · have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        left
        -- folded = String.singleton spaceChar; unfold spaceChar to ' '
        show folded = " "
        rw [← this.1]
        show String.singleton ' ' = " "
        rfl

/-- `foldQuotedNewlinesIx` returns either `" "` or
    `replicate '\n'`. Indexed twin of legacy
    `foldQuotedNewlines_result_form`. -/
theorem foldQuotedNewlinesIx_result_form {input : String} (c : IxCursor input) :
    (foldQuotedNewlinesIx c).1 = " " ∨
    (∃ n, n > 0 ∧ (foldQuotedNewlinesIx c).1 = String.ofList (List.replicate n '\n')) := by
  unfold foldQuotedNewlinesIx
  split
  · rename_i hgt; right; exact ⟨_, hgt, rfl⟩
  · left; rfl

/-! ### `PlainContentInvIx` — content/spaces loop invariant -/

/-- Loop invariant for `collectPlainScalarLoopIx` content correctness.
    Couples to the cursor `c` for boundary safety. Indexed twin of
    legacy `PlainContentInv`. -/
structure PlainContentInvIx {input : String} (content : String) (spaces : String)
    (inFlow : Bool) (c : IxCursor input) : Prop where
  /-- Content has no `: ` (colon-space) pattern. -/
  content_noColonSpace : noColonSpaceProp content
  /-- Content has no ` #` (space-hash) pattern. -/
  content_noSpaceHash : noSpaceHashProp content
  /-- In flow context, content has no flow indicators. -/
  content_noFlowIndicators : inFlow = true → noFlowIndicatorsProp content
  /-- Spaces buffer contains only whitespace characters. -/
  spaces_whitespace : ∀ x ∈ spaces.toList, isWhiteSpaceProp x
  /-- Boundary safety: if content ends with `:`, spaces is empty and
      the next cursor char is non-blank. -/
  boundary_colon : content.toList.getLast? = some ':' →
      spaces = "" ∧ (∀ n, c.peek? = some n → ¬isBlankProp n)

/-- The invariant holds trivially for empty content and empty spaces. -/
theorem PlainContentInvIx.empty {input : String} (inFlow : Bool) (c : IxCursor input) :
    PlainContentInvIx (input := input) "" "" inFlow c where
  content_noColonSpace := noColonSpaceProp_empty
  content_noSpaceHash := noSpaceHashProp_empty
  content_noFlowIndicators := fun _ => noFlowIndicatorsProp_empty
  spaces_whitespace := fun _ hc => by simp [String.toList] at hc
  boundary_colon := fun h => by simp [String.toList, List.getLast?] at h

/-- Boundary invariant for the `#` case: if content ends with `' '` and
    spaces is empty, the cursor's next char is not `'#'`. Indexed twin of
    legacy `BoundaryHash`. -/
def BoundaryHashIx {input : String} (content spaces : String) (c : IxCursor input) : Prop :=
  content.toList.getLast? = some ' ' → spaces = "" → ∀ n, c.peek? = some n → n ≠ '#'

/-- `BoundaryHashIx` holds trivially for empty content. -/
theorem BoundaryHashIx.empty {input : String} (c : IxCursor input) :
    BoundaryHashIx (input := input) "" "" c :=
  fun h => by simp [String.toList, List.getLast?] at h

/-- Transfer `PlainContentInvIx` to a new cursor where `peek?` is non-blank. -/
theorem PlainContentInvIx.transfer_nonblank_peek {input : String}
    {content spaces : String} {inFlow : Bool} {c : IxCursor input}
    (inv : PlainContentInvIx content spaces inFlow c)
    (c' : IxCursor input) (ch : Char)
    (hpeek : c'.peek? = some ch) (hnotblank : ¬isBlankProp ch) :
    PlainContentInvIx content spaces inFlow c' where
  content_noColonSpace := inv.content_noColonSpace
  content_noSpaceHash := inv.content_noSpaceHash
  content_noFlowIndicators := inv.content_noFlowIndicators
  spaces_whitespace := inv.spaces_whitespace
  boundary_colon hcolon :=
    ⟨(inv.boundary_colon hcolon).1,
     fun n hp => by rw [hpeek] at hp; injection hp with hne; subst hne; exact hnotblank⟩

/-- Build `PlainContentInvIx` for `content ++ fold` where `fold` is `" "`
    or replicate newlines. Used by both flow and block line-break
    recursion cases. Indexed twin of legacy `PlainContentInv.of_fold`. -/
theorem PlainContentInvIx.of_fold {input : String}
    {content spaces : String} {inFlow : Bool} {c c' : IxCursor input}
    (inv : PlainContentInvIx content spaces inFlow c)
    (ch : Char) (hpeek : c.peek? = some ch) (hc_lb : isLineBreakProp ch)
    (fold : String)
    (hfold : fold = " " ∨ (∃ n, n > 0 ∧ fold = String.ofList (List.replicate n '\n')))
    (_hpeek' : ∀ n, c'.peek? = some n → n ≠ '#') :
    PlainContentInvIx (content ++ fold) "" inFlow c' where
  content_noColonSpace := by
    rcases hfold with rfl | ⟨n, hn, rfl⟩
    · apply noColonSpaceProp_append content " " inv.content_noColonSpace
        noColonSpaceProp_space
      intro ⟨hcl, _⟩
      exact (inv.boundary_colon hcl).2 ch hpeek (Or.inr hc_lb)
    · apply noColonSpaceProp_append content _ inv.content_noColonSpace
        (noColonSpaceProp_replicate_newline n)
      intro ⟨hcl, hh⟩
      rw [head_replicate_newline n hn] at hh; contradiction
  content_noSpaceHash := by
    rcases hfold with rfl | ⟨n, hn, rfl⟩
    · apply noSpaceHashProp_append content " " inv.content_noSpaceHash
        noSpaceHashProp_space
      intro ⟨_, hh⟩; rw [head_space] at hh; contradiction
    · apply noSpaceHashProp_append content _ inv.content_noSpaceHash
        (noSpaceHashProp_replicate_newline n)
      intro ⟨_, hh⟩; rw [head_replicate_newline n hn] at hh; contradiction
  content_noFlowIndicators := fun hflow => by
    rcases hfold with rfl | ⟨n, _, rfl⟩
    · exact noFlowIndicatorsProp_append content " "
        (inv.content_noFlowIndicators hflow) noFlowIndicatorsProp_space
    · exact noFlowIndicatorsProp_append content _
        (inv.content_noFlowIndicators hflow) (noFlowIndicatorsProp_replicate_newline n)
  spaces_whitespace := fun _ hc => by simp [String.toList] at hc
  boundary_colon := by
    intro hcolon
    rcases hfold with rfl | ⟨n, hn, rfl⟩
    · rw [getLast_append_space] at hcolon; contradiction
    · rw [getLast_append_replicate_newline content n hn] at hcolon; contradiction

/-! ### Drop spaces from the invariant (used by termination arms)

Termination arms of `collectPlainScalarLoopIx` return `(content, c)`
without the trailing `spaces` buffer. Switching `spaces` to `""`
in the invariant is safe: the `spaces_whitespace` field is vacuous
on `""`, and `boundary_colon` (`content ends with ':' → spaces = ""
∧ ...`) is already `""` whenever its hypothesis fires. -/

theorem PlainContentInvIx.drop_spaces {input : String}
    {content spaces : String} {inFlow : Bool} {c : IxCursor input}
    (inv : PlainContentInvIx content spaces inFlow c) :
    PlainContentInvIx content "" inFlow c where
  content_noColonSpace := inv.content_noColonSpace
  content_noSpaceHash := inv.content_noSpaceHash
  content_noFlowIndicators := inv.content_noFlowIndicators
  spaces_whitespace := fun _ hc => by simp [String.toList] at hc
  boundary_colon hcolon := ⟨rfl, (inv.boundary_colon hcolon).2⟩

/-! ### Trim helpers for `trimTrailingWSIx`

`trimTrailingWSIx` uses `isWhiteSpaceBool` (space-or-tab), matching
the legacy `trimTrailingWS`'s `fun c => c == ' ' || c == '\t'`
predicate. The lemmas below transfer content properties through the
trim. -/

theorem trimTrailingWSIx_eq (s : String) :
    trimTrailingWSIx s =
      String.ofList ((s.toList.reverse.dropWhile isWhiteSpaceBool).reverse) := by
  unfold trimTrailingWSIx; rfl

theorem trimTrailingWSIx_noColonSpace (content : String)
    (h : noColonSpaceProp content) :
    noColonSpaceProp (trimTrailingWSIx content) := by
  rw [trimTrailingWSIx_eq]
  have h' : noColonSpaceProp (String.ofList content.toList) := by
    rw [String.ofList_toList]; exact h
  exact L4YAML.Proofs.StringProperties.trim_preserves_noColonSpace
    isWhiteSpaceBool content.toList h'

theorem trimTrailingWSIx_noSpaceHash (content : String)
    (h : noSpaceHashProp content) :
    noSpaceHashProp (trimTrailingWSIx content) := by
  rw [trimTrailingWSIx_eq]
  have h' : noSpaceHashProp (String.ofList content.toList) := by
    rw [String.ofList_toList]; exact h
  exact L4YAML.Proofs.StringProperties.trim_preserves_noSpaceHash
    isWhiteSpaceBool content.toList h'

theorem trimTrailingWSIx_noFlowIndicators (content : String)
    (h : noFlowIndicatorsProp content) :
    noFlowIndicatorsProp (trimTrailingWSIx content) := by
  rw [trimTrailingWSIx_eq]
  have h' : noFlowIndicatorsProp (String.ofList content.toList) := by
    rw [String.ofList_toList]; exact h
  exact L4YAML.Proofs.StringProperties.trim_preserves_noFlowIndicators
    isWhiteSpaceBool content.toList h'

/-- `trimTrailingWSIx` preserves `List.head?` when the result is nonempty.
    Indexed twin of legacy `trimTrailingWS_preserves_head`. -/
theorem trimTrailingWSIx_preserves_head (content : String) (c : Char)
    (hne : (trimTrailingWSIx content).toList ≠ [])
    (hhead : content.toList.head? = some c) :
    (trimTrailingWSIx content).toList.head? = some c := by
  unfold trimTrailingWSIx at hne ⊢
  simp only [String.toList_ofList] at hne ⊢
  have ⟨suf, hsuf⟩ :=
    L4YAML.Proofs.StringProperties.reverse_dropWhile_reverse_isPrefix
      isWhiteSpaceBool content.toList
  cases htrim : (content.toList.reverse.dropWhile isWhiteSpaceBool).reverse with
  | nil => rw [htrim] at hne; exact absurd rfl hne
  | cons a rest =>
    simp only [List.head?_cons]
    rw [htrim] at hsuf
    rw [hsuf] at hhead
    simp only [List.cons_append, List.head?_cons] at hhead
    exact hhead

/-- Helper: `List.dropWhile p` on `(xs ++ ys)` with all-`p` `xs`
    skips through `xs` and recurses on `ys`. -/
private theorem dropWhile_append_all (p : Char → Bool) (xs ys : List Char)
    (hxs : ∀ x ∈ xs, p x = true) :
    List.dropWhile p (xs ++ ys) = List.dropWhile p ys := by
  induction xs with
  | nil => simp
  | cons x xs' ih =>
    have hx := hxs x List.mem_cons_self
    have hxs' : ∀ y ∈ xs', p y = true :=
      fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    simp [hx, ih hxs']

/-- `trimTrailingWSIx (a ++ b) = trimTrailingWSIx a` when `b` is all
    whitespace. Used to simplify the trim after the indexed loop's EOF
    case merges trailing `spaces` into the raw output. -/
theorem trimTrailingWSIx_append_whitespace (a b : String)
    (hb : ∀ c ∈ b.toList, isWhiteSpaceProp c) :
    trimTrailingWSIx (a ++ b) = trimTrailingWSIx a := by
  unfold trimTrailingWSIx
  congr 1
  rw [String.toList_append, List.reverse_append]
  have hb' : ∀ x ∈ b.toList.reverse, isWhiteSpaceBool x = true := by
    intro x hx
    rw [List.mem_reverse] at hx
    exact (isWhiteSpace_iff x).mpr (hb x hx)
  rw [dropWhile_append_all isWhiteSpaceBool b.toList.reverse a.toList.reverse hb']


/-! ### Content-isPrefix lemma — `content` survives the loop

The loop only appends to `content` (never shrinks it). Indexed twin of
legacy `collectPlainScalarLoop_content_isPrefix`. -/

private theorem prefix_of_append_string (a b : String) :
    a.toList <+: (a ++ b).toList := by
  rw [String.toList_append]; exact ⟨b.toList, rfl⟩

private theorem prefix_of_append_string_3 (a b c : String) :
    a.toList <+: (a ++ b ++ c).toList := by
  rw [String.toList_append, String.toList_append]
  exact ⟨b.toList ++ c.toList, by rw [List.append_assoc]⟩

private theorem bool_eq_false_of_not_eq_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

theorem collectPlainScalarLoopIx_content_isPrefix {input : String}
    (c : IxCursor input) (content spaces : String) (inFlow : Bool)
    (contentIndent fuel : Nat) :
    content.toList <+:
      (collectPlainScalarLoopIx c content spaces inFlow contentIndent fuel).1.toList := by
  -- The proof is by induction on fuel + case analysis on `c.peek?` and
  -- the cascade of branch conditions. Termination/EOF arms yield the
  -- prefix trivially; recursive arms compose the structural prefix
  -- fact with the IH. Mechanical but lengthy; deferred to follow-up
  -- (see Step 6d.1e.11b reflection in Blueprint).
  sorry

/-! ### B3.3 indexed analog — `collectPlainScalarLoopIx_preserves_contentInv`

The core preservation theorem for `PlainContentInvIx`. Mirrors the
legacy `collectPlainScalarLoop_preserves_contentInv` (§B3.3) but uses
an existential decomposition because the indexed loop returns
`String × IxCursor` (no separate `content`/`spaces` projection). -/

theorem collectPlainScalarLoopIx_preserves_contentInv {input : String}
    (c : IxCursor input) (content spaces : String) (inFlow : Bool)
    (contentIndent fuel : Nat)
    (inv : PlainContentInvIx content spaces inFlow c)
    (_bh : BoundaryHashIx content spaces c) :
    ∃ content' spaces',
      (collectPlainScalarLoopIx c content spaces inFlow contentIndent fuel).1 =
        content' ++ spaces' ∧
      PlainContentInvIx content' spaces' inFlow
        (collectPlainScalarLoopIx c content spaces inFlow contentIndent fuel).2 := by
  -- Mirrors the legacy B3.3 preservation by induction on fuel with the
  -- 7-arm cascade. Termination arms yield `⟨content, "", _, inv.drop_spaces⟩`;
  -- EOF/zero yield `⟨content, spaces, rfl, inv⟩`. Recursive arms construct
  -- the post-step invariant via `PlainContentInvIx.of_fold` (linebreak
  -- arms) or direct `noColonSpaceProp_append` / `noSpaceHashProp_append`
  -- (colon-continue / content arms) and apply the IH. Deferred to
  -- follow-up.
  sorry

/-! ### B3.4 indexed analog — `_validFirst_and_head`

When the loop starts from empty content with a `canStart` witness at
the entry cursor's first char, the resulting raw content has the
witness char at its head and satisfies `validPlainFirstProp`. Indexed
twin of legacy `collectPlainScalarLoop_validFirst_and_head`. -/

theorem collectPlainScalarLoopIx_validFirst_and_head {input : String}
    (c : IxCursor input) (inFlow : Bool) (contentIndent fuel : Nat)
    (c0 : Char) (_hpeek : c.peek? = some c0)
    (_hcs : canStartPlainScalarBool c0 (c.peekAt? 1) inFlow = true)
    (_hne : (collectPlainScalarLoopIx c "" "" inFlow contentIndent fuel).1 ≠ "") :
    validPlainFirstProp
      (collectPlainScalarLoopIx c "" "" inFlow contentIndent fuel).1 inFlow ∧
    (collectPlainScalarLoopIx c "" "" inFlow contentIndent fuel).1.toList.head? =
      some c0 := by
  -- Two-level fuel inspection for exception c0: after the first step the
  -- content becomes `singleton c0`; for the second step (when exception
  -- c0 + result has ≥ 2 chars), the second char must be `c.peekAt? 1`
  -- by `canStart_exception_next` + `advance_peek_eq_peekAt_one`. For
  -- non-exception c0, validPlainFirst follows from
  -- `canStart_nonException_to_prop`. Deferred to follow-up.
  sorry

/-! ### `scanPlainScalarIx_content_valid` — the culminating theorem -/

set_option maxHeartbeats 1600000 in
/-- `scanPlainScalarIx` produces a non-empty raw content with
    `ScalarScannable` semantics for the trimmed result. The precondition
    is the same shape as the legacy `scanPlainScalar_content_valid`. -/
theorem scanPlainScalarIx_content_valid {input : String} (c : IxCursor input)
    (inFlow : Bool) (contentIndent : Nat)
    (h_canStart : ∃ ch, c.peek? = some ch ∧
        canStartPlainScalarBool ch (c.peekAt? 1) inFlow = true)
    (h_ne : (scanPlainScalarIx c inFlow contentIndent).1 ≠ "") :
    ScalarScannable
      ⟨(scanPlainScalarIx c inFlow contentIndent).1, .plain, none, none, none⟩
      inFlow := by
  obtain ⟨c0, hpeek0, hcs0⟩ := h_canStart
  -- Raw is the loop's raw output before trimming.
  have h_raw_ne :
      (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1 ≠ "" := by
    intro h_emp
    apply h_ne
    show trimTrailingWSIx _ = ""
    rw [h_emp]; simp [trimTrailingWSIx]
  obtain ⟨content', spaces', h_eq, inv⟩ :=
    collectPlainScalarLoopIx_preserves_contentInv c "" "" inFlow contentIndent
      input.utf8ByteSize (PlainContentInvIx.empty inFlow c) (BoundaryHashIx.empty c)
  obtain ⟨_h_vpf_raw, h_head_c0⟩ :=
    collectPlainScalarLoopIx_validFirst_and_head c inFlow contentIndent
      input.utf8ByteSize c0 hpeek0 hcs0 h_raw_ne
  -- Compute the trim once.
  have h_trim_eq :
      trimTrailingWSIx
        (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1 =
      trimTrailingWSIx content' := by
    rw [h_eq]
    exact trimTrailingWSIx_append_whitespace content' spaces' inv.spaces_whitespace
  show ScalarScannable ⟨_, _, _, _, _⟩ inFlow
  show ScalarScannable
    ⟨trimTrailingWSIx
        (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1,
      .plain, none, none, none⟩ inFlow
  have h_tne :
      (trimTrailingWSIx
        (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1).toList
        ≠ [] := by
    intro h_empty
    apply h_ne
    show trimTrailingWSIx _ = ""
    rw [← String.toList_inj]; simpa using h_empty
  have h_trim_head :
      (trimTrailingWSIx
        (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1).toList.head?
        = some c0 :=
    trimTrailingWSIx_preserves_head _ c0 h_tne h_head_c0
  have h_vpf :
      validPlainFirstProp
        (trimTrailingWSIx
          (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1)
        inFlow := by
    by_cases hge2 :
        (trimTrailingWSIx
          (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1).toList.length
          ≥ 2
    · rw [trimTrailingWSIx_eq] at hge2 ⊢
      simp only [String.toList_ofList] at hge2
      exact L4YAML.Proofs.StringProperties.trim_preserves_validPlainFirst
        isWhiteSpaceBool _ inFlow (by rwa [String.ofList_toList]) hge2
    · obtain ⟨ch, hch⟩ : ∃ ch,
          (trimTrailingWSIx
            (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1).toList
            = [ch] := by
        cases htl :
            (trimTrailingWSIx
              (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1).toList with
        | nil => exact absurd htl h_tne
        | cons x rest =>
          cases rest with
          | nil => exact ⟨x, rfl⟩
          | cons y tl => simp [htl] at hge2
      rw [hch] at h_trim_head; simp at h_trim_head
      rw [h_trim_head] at hch
      rw [show
            trimTrailingWSIx
              (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).1 =
              String.singleton c0 from by
        rw [← String.toList_inj]; simpa using hch]
      by_cases hexc : c0 = '-' ∨ c0 = '?' ∨ c0 = ':'
      · exact validPlainFirst_singleton_exception c0 inFlow hexc
      · simp only [validPlainFirstProp, String.toList_singleton, hexc, ↓reduceIte]
        exact canStart_nonException_to_prop c0 (c.peekAt? 1) inFlow hexc hcs0
  intro _hstyle _hlen
  refine ⟨h_vpf, ?_, ?_, ?_⟩
  · rw [h_trim_eq]
    exact trimTrailingWSIx_noColonSpace content' inv.content_noColonSpace
  · rw [h_trim_eq]
    exact trimTrailingWSIx_noSpaceHash content' inv.content_noSpaceHash
  · intro hflow
    rw [h_trim_eq]
    exact trimTrailingWSIx_noFlowIndicators content' (inv.content_noFlowIndicators hflow)

end L4YAML.Scanner.Indexed
