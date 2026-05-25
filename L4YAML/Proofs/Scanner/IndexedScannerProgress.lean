/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedDispatch
import L4YAML.Proofs.Scanner.IndexedScalar

/-! # `IndexedScannerProgress` — Phase 3 Step 6f.3b3.internals.progress.leaf

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6f).

## Scope (`.progress.leaf`)

Indexed twin of `Proofs/Scanner/ScannerProgress.lean` + the per-leaf
and per-dispatcher `_offset_lt` / `_offset_gt` block at the bottom of
legacy `Proofs/Scanner/ScannerCorrectness.lean`. Provides *strict*
offset-progress (`<`) for every leaf scanner reachable from
`scanNextTokenIx`, and lifts those facts to the four sub-dispatchers
(`dispatchStructural`, `dispatchFlowIndicators`, `dispatchBlockIndicators`,
`dispatchContent`).

The capstone `scanNextTokenIx_progress` is deferred to a follow-up
`.capstone` slice that composes these per-helper facts with
`scanNextTokenIx_preprocess` strict progress.

## Layout

### §0 Helpers (cursor-level, state-level)
  - `IxCursor.advanceN_succ_offset_lt`,
  - `ScannerStateIx.advance_offset_lt_of_hasMore` and
    `ScannerStateIx.advanceN_succ_offset_lt_of_hasMore`.

### §1 Flow-bracket leaf strict progress
  - `scanFlowSequenceStartIx_offset_lt`,
    `scanFlowSequenceEndIx_offset_lt`,
    `scanFlowMappingStartIx_offset_lt`,
    `scanFlowMappingEndIx_offset_lt`.

### §2 Block / mapping leaf strict progress
  - `scanBlockEntryIx_offset_lt`, `scanKeyIx_offset_lt`,
    `scanValueIx_offset_lt`, `scanFlowEntryIx_offset_lt`.

### §3 Document / directive leaf strict progress
  - `scanDocumentStartIx_offset_lt`, `scanDocumentEndIx_offset_lt`,
    `scanDirectiveIx_offset_lt`.

### §4 Node-property / scalar leaf strict progress
  - `scanAnchorOrAliasIx_offset_lt`, `scanTagIx_offset_lt`,
    `scanBlockScalarIx_offset_lt`.
  - `scanPlainScalarIx_offset_lt_axiom` (staging axiom; discharge
    plan documented inline — port legacy `canStart_terminates_none` /
    `scanPlainScalar_offset_lt` chain).

  (`scanDoubleQuotedIx_offset_lt` / `scanSingleQuotedIx_offset_lt`
  already live in `Proofs/Scanner/IndexedScalar.lean`.)

### §5 Per-dispatcher strict progress (`_offset_gt`)
  - `scanNextTokenIx_dispatchStructural_offset_gt`,
    `scanNextTokenIx_dispatchFlowIndicators_offset_gt`,
    `scanNextTokenIx_dispatchBlockIndicators_offset_gt`,
    `scanNextTokenIx_dispatchContent_offset_gt`.

## What's deferred (`.capstone`)

  - `scanNextTokenIx_progress` (capstone — composes §5 with
    `preprocess` strict progress).
  - `ScanChainIx.bound_invariant` strict form (`offset ≥ s₀.offset + n`)
    and `ScanChainIx.fuel_bound` (`n + 1 ≤ (input.utf8ByteSize + 1) * 4`),
    both landing in `Proofs/Output/IndexedEmitterScannability/ScanChain.lean`
    §3.
  - `scanPlainScalarIx_offset_lt_axiom` discharge: requires porting
    the legacy `canStart_terminates_none` chain (~150 LOC) from
    `Proofs/Scanner/ScannerCorrectness.lean:10228–10325`. See the
    inline axiom for the precondition shape.
-/

set_option autoImplicit false

/-! ## §0  Helpers -/

namespace L4YAML.Indexed.IxCursor

/-- `advanceN (n + 1)` strictly advances offset when the cursor has more
    input. Mirrors `ScannerProgress.advanceN_succ_offset_lt`. -/
theorem advanceN_succ_offset_lt {input : String} (c : IxCursor input) (n : Nat)
    (h : c.pos.offset < input.utf8ByteSize) :
    c.pos.offset < (c.advanceN (n + 1)).pos.offset := by
  show c.pos.offset < (c.advance.advanceN n).pos.offset
  exact Nat.lt_of_lt_of_le (advance_offset_lt_of_hasMore c h)
    (advanceN_offset_monotonic c.advance n)

end L4YAML.Indexed.IxCursor

namespace L4YAML.Scanner.Indexed.ScannerStateIx

/-- State-level strict progress for `advance` under `hasMore`. -/
theorem advance_offset_lt_of_hasMore {input : String} (s : ScannerStateIx input)
    (h : s.cursor.pos.offset < input.utf8ByteSize) :
    s.cursor.pos.offset < s.advance.cursor.pos.offset :=
  L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore s.cursor h

/-- State-level strict progress for `advanceN (n + 1)` under `hasMore`. -/
theorem advanceN_succ_offset_lt_of_hasMore {input : String} (s : ScannerStateIx input)
    (n : Nat) (h : s.cursor.pos.offset < input.utf8ByteSize) :
    s.cursor.pos.offset < (s.advanceN (n + 1)).cursor.pos.offset := by
  rw [advanceN_cursor]
  exact L4YAML.Indexed.IxCursor.advanceN_succ_offset_lt s.cursor n h

end L4YAML.Scanner.Indexed.ScannerStateIx

namespace L4YAML.Proofs.Indexed.ScannerProgress

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.CharPredicates

variable {input : String}

/-! ## §1  Flow-bracket leaf strict progress

Each of the four flow-bracket scanners (`[`, `]`, `{`, `}`) is total
(returns a state, not `Except`) and ends with a single `emit` then
`advance`. Under `hasMore`, the trailing `advance` is strict;
cursor-preserving operations (`emit`, structure update) leave the
offset unchanged. -/

/-- `scanFlowSequenceStartIx` strictly advances offset. -/
theorem scanFlowSequenceStartIx_offset_lt (s : ScannerStateIx input)
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize) :
    s.cursor.pos.offset < (scanFlowSequenceStartIx s).cursor.pos.offset := by
  unfold scanFlowSequenceStartIx
  show s.cursor.pos.offset < _
  simp only [advance_cursor, emit_cursor]
  exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm

/-- `scanFlowSequenceEndIx` strictly advances offset. -/
theorem scanFlowSequenceEndIx_offset_lt (s : ScannerStateIx input)
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize) :
    s.cursor.pos.offset < (scanFlowSequenceEndIx s).cursor.pos.offset := by
  unfold scanFlowSequenceEndIx
  show s.cursor.pos.offset < _
  simp only [advance_cursor, emit_cursor]
  exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm

/-- `scanFlowMappingStartIx` strictly advances offset. -/
theorem scanFlowMappingStartIx_offset_lt (s : ScannerStateIx input)
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize) :
    s.cursor.pos.offset < (scanFlowMappingStartIx s).cursor.pos.offset := by
  unfold scanFlowMappingStartIx
  show s.cursor.pos.offset < _
  simp only [advance_cursor, emit_cursor]
  exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm

/-- `scanFlowMappingEndIx` strictly advances offset. -/
theorem scanFlowMappingEndIx_offset_lt (s : ScannerStateIx input)
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize) :
    s.cursor.pos.offset < (scanFlowMappingEndIx s).cursor.pos.offset := by
  unfold scanFlowMappingEndIx
  show s.cursor.pos.offset < _
  simp only [advance_cursor, emit_cursor]
  exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm

/-! ## §2  Block / mapping leaf strict progress

`scanBlockEntryIx` / `scanKeyIx` / `scanValueIx` / `scanFlowEntryIx`
return `Except`. Each peels its do-block via `split at h` (or
`by_cases` + `if_pos/if_neg` for outer-let `if`s, R49 pattern), then
closes the `.ok` arms via the trailing `advance` on a cursor-preserving
chain. -/

/-- `scanBlockEntryIx` strictly advances offset on `.ok`. -/
theorem scanBlockEntryIx_offset_lt {s s' : ScannerStateIx input}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanBlockEntryIx s = .ok s') :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  unfold scanBlockEntryIx at h
  by_cases hi : (!s.inFlow) = true
  · rw [if_pos hi] at h
    by_cases ht : s.hasTabInPrecedingWhitespace = true
    · rw [if_pos ht] at h
      simp [Bind.bind, Except.bind] at h
    · rw [if_neg ht] at h
      simp only [pure_bind] at h
      rw [if_pos hi] at h
      simp only [Except.ok.injEq] at h
      subst h
      show s.cursor.pos.offset < _
      simp only [advance_cursor, emit_cursor, pushSequenceIndentIx_cursor]
      exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm
  · rw [if_neg hi] at h
    simp only [pure_bind] at h
    rw [if_neg hi] at h
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset < _
    simp only [advance_cursor, emit_cursor]
    exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm

/-- `scanKeyIx` strictly advances offset on `.ok`. -/
theorem scanKeyIx_offset_lt {s s' : ScannerStateIx input}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanKeyIx s = .ok s') :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  unfold scanKeyIx at h
  by_cases hi : (!s.inFlow) = true
  · simp only [if_pos hi, advance_inFlow, emit_inFlow,
      pushMappingIndentIx_inFlow] at h
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [pure_bind, Except.ok.injEq] at h
      subst h
      show s.cursor.pos.offset < _
      simp only [advance_cursor, emit_cursor, pushMappingIndentIx_cursor]
      exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm
  · simp only [if_neg hi, advance_inFlow, emit_inFlow] at h
    simp only [pure_bind, Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset < _
    simp only [advance_cursor, emit_cursor]
    exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm

/-- `scanValueIx` strictly advances offset on `.ok`. -/
theorem scanValueIx_offset_lt {s s' : ScannerStateIx input}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanValueIx s = .ok s') :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  unfold scanValueIx at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h                                                  -- validate threw
  · split at h
    · cases h                                                -- tab-check threw
    · simp only [Except.ok.injEq] at h
      subst h
      show s.cursor.pos.offset < _
      simp only [advance_cursor, emit_cursor, scanValuePrepareIx_cursor,
                 scanValueClearKeyIx_cursor]
      exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm

/-- `scanFlowEntryIx` strictly advances offset on `.ok`. -/
theorem scanFlowEntryIx_offset_lt {s s' : ScannerStateIx input}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanFlowEntryIx s = .ok s') :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  split at h
  · split at h
    · simp at h
    · injection h with h
      subst h
      show s.cursor.pos.offset < _
      simp only [advance_cursor, emit_cursor]
      exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm
  · injection h with h
    subst h
    show s.cursor.pos.offset < _
    simp only [advance_cursor, emit_cursor]
    exact L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm

/-! ## §3  Document / directive leaf strict progress -/

/-- `scanDocumentStartIx` strictly advances offset (consumes `---`). -/
theorem scanDocumentStartIx_offset_lt (s : ScannerStateIx input)
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize) :
    s.cursor.pos.offset < (scanDocumentStartIx s).cursor.pos.offset := by
  unfold scanDocumentStartIx
  show s.cursor.pos.offset < _
  simp only [advanceN_cursor, emit_cursor, unwindIndentsIx_cursor]
  exact L4YAML.Indexed.IxCursor.advanceN_succ_offset_lt _ 2 h_hm

/-- `scanDocumentEndIx` strictly advances offset on `.ok` (consumes `...`). -/
theorem scanDocumentEndIx_offset_lt {s s' : ScannerStateIx input}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanDocumentEndIx s = .ok s') :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  unfold scanDocumentEndIx at h
  by_cases hd : (s.directivesPresent && !s.documentEverStarted) = true
  · rw [if_pos hd] at h
    simp [Bind.bind, Except.bind] at h
  · rw [if_neg hd] at h
    simp only [pure_bind] at h
    split at h
    all_goals first
      | (simp only [Except.ok.injEq] at h
         subst h
         show s.cursor.pos.offset < _
         simp only [advanceN_cursor, emit_cursor, unwindIndentsIx_cursor]
         exact L4YAML.Indexed.IxCursor.advanceN_succ_offset_lt _ 2 h_hm)
      | (split at h
         all_goals first
           | (simp only [Except.ok.injEq] at h
              subst h
              show s.cursor.pos.offset < _
              simp only [advanceN_cursor, emit_cursor, unwindIndentsIx_cursor]
              exact L4YAML.Indexed.IxCursor.advanceN_succ_offset_lt _ 2 h_hm)
           | (simp [Bind.bind, Except.bind] at h))

/-- `scanDirectiveIx` strictly advances offset on `.ok` (consumes at
    least the leading `%`). -/
theorem scanDirectiveIx_offset_lt {s s' : ScannerStateIx input}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanDirectiveIx s = .ok s') :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  have h_adv : s.cursor.pos.offset < s.advance.cursor.pos.offset :=
    L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm
  unfold scanDirectiveIx at h
  split at h
  · simp at h                                                -- !allowDirectives ⇒ .error
  · simp only at h
    split at h
    · -- YAML directive arm: result.cursor ≥ skipWhitespace ∘ collectDirectiveNameLoopIx ∘ advance
      have hChain := scanYamlDirectiveIx_offset_monotonic h
      refine Nat.lt_of_lt_of_le h_adv (Nat.le_trans ?_ hChain)
      simp only [advance_cursor]
      exact Nat.le_trans (collectDirectiveNameLoopIx_offset_monotonic _ _ _)
        (skipWhitespace_offset_monotonic _)
    · split at h
      · -- TAG directive arm
        have hChain := scanTagDirectiveIx_offset_monotonic h
        refine Nat.lt_of_lt_of_le h_adv (Nat.le_trans ?_ hChain)
        simp only [advance_cursor]
        exact Nat.le_trans (collectDirectiveNameLoopIx_offset_monotonic _ _ _)
          (skipWhitespace_offset_monotonic _)
      · -- reserved directive
        simp only [Except.ok.injEq] at h
        subst h
        show s.cursor.pos.offset < _
        simp only [advance_cursor]
        refine Nat.lt_of_lt_of_le h_adv ?_
        exact Nat.le_trans (collectDirectiveNameLoopIx_offset_monotonic _ _ _)
          (skipWhitespace_offset_monotonic _)

/-! ## §4  Node-property / scalar leaf strict progress -/

/-- `scanAnchorOrAliasIx` strictly advances offset on `.ok` (consumes
    at least the leading `&` or `*`). -/
theorem scanAnchorOrAliasIx_offset_lt {s s' : ScannerStateIx input} {isAnchor : Bool}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  unfold scanAnchorOrAliasIx at h
  by_cases hn : (collectAnchorNameLoopIx s.advance.cursor ""
      (input.utf8ByteSize - s.advance.cursor.pos.offset)).1.isEmpty = true
  · rw [if_pos hn] at h
    exact absurd h (by simp)
  · rw [if_neg hn] at h
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset < _
    simp only [emitAt_cursor, advance_cursor]
    exact Nat.lt_of_lt_of_le
      (L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm)
      (collectAnchorNameLoopIx_offset_monotonic _ _ _)

/-- `scanTagIx` strictly advances offset on `.ok` (consumes at least
    the leading `!`). -/
theorem scanTagIx_offset_lt {s s' : ScannerStateIx input}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanTagIx s = .ok s') :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  unfold scanTagIx at h
  simp only at h
  have h_adv : s.cursor.pos.offset < s.advance.cursor.pos.offset :=
    L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore _ h_hm
  split at h
  · -- some '<' — verbatim tag arm
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        show s.cursor.pos.offset < _
        simp only [emitAt_cursor, advance_cursor]
        refine Nat.lt_of_lt_of_le h_adv ?_
        exact Nat.le_trans (L4YAML.Indexed.IxCursor.advance_offset_monotonic _)
          (collectVerbatimTagLoopIx_offset_monotonic _ _ _)
  · -- some '!' — !! tag arm
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset < _
    simp only [emitAt_cursor, advance_cursor]
    refine Nat.lt_of_lt_of_le h_adv ?_
    exact Nat.le_trans (L4YAML.Indexed.IxCursor.advance_offset_monotonic _)
      (collectTagSuffixLoopIx_offset_monotonic _ _ _)
  · -- catch-all: !handle!suffix or !suffix
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset < _
    simp only [emitAt_cursor, advance_cursor]
    refine Nat.lt_of_lt_of_le h_adv ?_
    refine Nat.le_trans
      (collectTagHandleLoopIx_offset_monotonic s.cursor.advance ""
        (input.utf8ByteSize - s.cursor.advance.pos.offset)) ?_
    split
    · exact collectTagSuffixLoopIx_offset_monotonic _ _ _
    · exact Nat.le_refl _

/-! ### Block-scalar strict progress (cursor-level)

`scanBlockScalarIx` is *cursor-keyed*, not state-keyed: it returns
`Option (String × ScalarStyle × IxCursor input)`. The state-level
`scanNextTokenIx_dispatchContent` wraps it via `emitAt`. We prove
strict progress at the cursor level; the dispatcher composes through
`emitAt_cursor` and the advance chain. -/

/-- `scanBlockScalarIx` strictly advances cursor offset on `some`
    (consumes at least the leading `|`/`>`). Indexed twin of
    `ScannerCorrectness.scanBlockScalar_offset_lt`. -/
theorem scanBlockScalarIx_offset_lt {input : String} (c : IxCursor input)
    (parentIndent : Nat) {result : String × ScalarStyle × IxCursor input}
    (h_hm : c.pos.offset < input.utf8ByteSize)
    (h : scanBlockScalarIx c parentIndent = some result) :
    c.pos.offset < result.2.2.pos.offset := by
  unfold scanBlockScalarIx at h
  split at h
  · -- some ch
    split at h
    · -- ch = '|' || ch = '>': success branch — result.2.2 is the body cursor.
      have hAdv : c.pos.offset < c.advance.pos.offset :=
        L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore c h_hm
      have hHdrToBody : c.advance.pos.offset ≤ (blockHeaderToBodyIx c).pos.offset := by
        -- Replay the `blockHeaderToBodyIx_offset_monotonic` chain starting
        -- from `c.advance` (the `advance` step is the only place `hAdv` is
        -- used; everything else is monotonic).
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
            exact Nat.le_trans (L4YAML.Indexed.IxCursor.advance_offset_monotonic _)
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
            (blockHeaderToBodyIx c).pos.offset := by
          unfold blockHeaderToBodyIx
          exact consumeLineBreak_offset_monotonic _
        exact Nat.le_trans hHdr (Nat.le_trans hSW (Nat.le_trans hComm hCLB))
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
      exact Nat.lt_of_lt_of_le hAdv (Nat.le_trans hHdrToBody hBody)
    · contradiction
  · contradiction

/-! ### Plain-scalar strict progress (staging axiom)

`scanPlainScalarIx_offset_lt` requires unfolding the first iteration of
`collectPlainScalarLoopIx` and ruling out every terminating branch in
favor of the "regular char advance + recurse" branch. The
legacy proof (`Proofs/Scanner/ScannerCorrectness.lean:10304`) needs
the helper chain `flowIndicator_isIndicator'` / `canStart_not_lb` /
`canStart_not_ws` / `canStart_plainSafe` / `canStart_terminates_none`
(lines 10228–10298, ~70 LOC of supporting lemmas + ~20 LOC of the
main proof + `maxHeartbeats 3200000`). Porting them is mechanically
straightforward but voluminous; we stage it as an axiom here and
discharge in `.capstone`.

**Discharge plan**: port `canStart_*` helpers (already pure boolean
algebra over `canStartPlainScalarBool`), then port the loop's
first-iteration unfold + advance-fires conclusion. The legacy
`collectPlainScalar_terminates?` indirection collapses to direct
case splits in the indexed substrate. -/

/-- Strict progress for `scanPlainScalarIx` when the initial character
    can start a plain scalar (and no document boundary suppresses
    scanning). **Staging axiom** — discharged in `.capstone`.

    Preconditions (mirroring legacy `scanPlainScalar_offset_lt`):
    - `c.pos.offset < input.utf8ByteSize` (the cursor has more input)
    - `c.peek? = some ch` (the first character is `ch`)
    - `canStartPlainScalarBool ch (c.peekAt? 1) inFlow = true` (the
      character can begin a plain scalar)
    - `¬ (c.pos.col = 0 ∧ (atDocumentStartIx c ∨ atDocumentEndIx c))`
      (no document boundary at column 0)

    The conclusion is `c.pos.offset < (scanPlainScalarIx c inFlow
    contentIndent).2.pos.offset` — the post-scan cursor has advanced
    by at least one byte. -/
axiom scanPlainScalarIx_offset_lt_axiom {input : String} (c : IxCursor input)
    (ch : Char) (inFlow : Bool) (contentIndent : Nat)
    (h_hm : c.pos.offset < input.utf8ByteSize)
    (h_peek : c.peek? = some ch)
    (h_can : canStartPlainScalarBool ch (c.peekAt? 1) inFlow = true)
    (h_noDoc : ¬ ((c.pos.col : Nat) = 0 ∧
                  (atDocumentStartIx c = true ∨ atDocumentEndIx c = true))) :
    c.pos.offset < (scanPlainScalarIx c inFlow contentIndent).2.pos.offset

/-! ## §5  Per-dispatcher strict progress

Each of the four sub-dispatchers calls one of the leaf scanners above
on its success path. The strict-progress composes via
`Nat.lt_of_lt_of_le` against the leaf's `_offset_lt`. -/

/-- `scanNextTokenIx_dispatchStructural` strict progress on `.ok (some _)`. -/
theorem scanNextTokenIx_dispatchStructural_offset_gt {s s' : ScannerStateIx input} {c : Char}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  rcases scanNextTokenIx_dispatchStructural_ok_some_cases h with
    rfl | h_de | h_dr
  · exact scanDocumentStartIx_offset_lt s h_hm
  · exact scanDocumentEndIx_offset_lt h_hm h_de
  · exact scanDirectiveIx_offset_lt h_hm h_dr

/-- `scanNextTokenIx_dispatchFlowIndicators` strict progress on `.ok (some _)`. -/
theorem scanNextTokenIx_dispatchFlowIndicators_offset_gt {s s' : ScannerStateIx input} {c : Char}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h with
    rfl | rfl | rfl | rfl | h_fe
  · exact scanFlowSequenceStartIx_offset_lt s h_hm
  · exact scanFlowSequenceEndIx_offset_lt s h_hm
  · exact scanFlowMappingStartIx_offset_lt s h_hm
  · exact scanFlowMappingEndIx_offset_lt s h_hm
  · exact scanFlowEntryIx_offset_lt h_hm h_fe

/-- `scanNextTokenIx_dispatchBlockIndicators` strict progress on `.ok (some _)`. -/
theorem scanNextTokenIx_dispatchBlockIndicators_offset_gt {s s' : ScannerStateIx input} {c : Char}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h with
    h_be | h_k | h_v
  · exact scanBlockEntryIx_offset_lt h_hm h_be
  · exact scanKeyIx_offset_lt h_hm h_k
  · exact scanValueIx_offset_lt h_hm h_v

/-- `scanNextTokenIx_dispatchContent` strict progress on `.ok s'`. The
    plain-scalar arm uses `scanPlainScalarIx_offset_lt_axiom`; all other
    productions chain through their respective `_offset_lt` lemmas.

    Mirrors legacy `ScannerCorrectness.dispatchContent_offset_gt`
    (`Proofs/Scanner/ScannerCorrectness.lean:10435`). -/
theorem scanNextTokenIx_dispatchContent_offset_gt {s s' : ScannerStateIx input} {c : Char}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h_peek : s.peek? = some c)
    (h_noDoc : ¬ ((s.cursor.pos.col : Nat) = 0 ∧
                  (atDocumentStartIx s.cursor = true ∨
                   atDocumentEndIx s.cursor = true)))
    (h : scanNextTokenIx_dispatchContent s c = .ok s') :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  unfold scanNextTokenIx_dispatchContent at h
  by_cases hg1 : (c == '&') = true
  · rw [if_pos hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h; cases h
    | ok v =>
      rw [hA] at h
      cases h
      exact scanAnchorOrAliasIx_offset_lt h_hm hA
  · rw [if_neg hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    by_cases hg2 : (c == '*') = true
    · rw [if_pos hg2] at h
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h; cases h
      | ok v =>
        rw [hA] at h
        cases h
        exact scanAnchorOrAliasIx_offset_lt h_hm hA
    · rw [if_neg hg2] at h
      by_cases hg3 : (c == '!') = true
      · rw [if_pos hg3] at h
        cases hT : scanTagIx s with
        | error e => rw [hT] at h; cases h
        | ok v =>
          rw [hT] at h
          cases h
          exact scanTagIx_offset_lt h_hm hT
      · rw [if_neg hg3] at h
        by_cases hg4 : (c == '|' || c == '>') = true
        · rw [if_pos hg4] at h
          split at h
          · rename_i r hBS
            cases h
            show s.cursor.pos.offset < _
            simp only [emitAt_cursor]
            exact scanBlockScalarIx_offset_lt s.cursor _ h_hm hBS
          · cases h
        · rw [if_neg hg4] at h
          by_cases hg5 : (c == '"') = true
          · rw [if_pos hg5] at h
            split at h
            · rename_i r hDQ
              cases h
              show s.cursor.pos.offset < _
              simp only [emitAt_cursor]
              exact scanDoubleQuotedIx_offset_lt s.cursor hDQ
            · cases h
          · rw [if_neg hg5] at h
            by_cases hg6 : (c == '\'') = true
            · rw [if_pos hg6] at h
              split at h
              · rename_i r hSQ
                cases h
                show s.cursor.pos.offset < _
                simp only [emitAt_cursor]
                exact scanSingleQuotedIx_offset_lt s.cursor hSQ
              · cases h
            · rw [if_neg hg6] at h
              by_cases hg7 : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true
              · rw [if_pos hg7] at h
                cases h
                show s.cursor.pos.offset < _
                simp only [emitAt_cursor]
                -- Plain-scalar arm — staging axiom.
                -- The peek? value `c` is supplied by the caller and matches
                -- `s.peek? = some c` via h_peek.
                exact scanPlainScalarIx_offset_lt_axiom s.cursor c s.inFlow _
                  h_hm h_peek hg7 h_noDoc
              · rw [if_neg hg7] at h
                cases h

end L4YAML.Proofs.Indexed.ScannerProgress
