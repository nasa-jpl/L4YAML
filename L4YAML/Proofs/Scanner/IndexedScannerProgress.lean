/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedDispatch
import L4YAML.Proofs.Scanner.IndexedScalar

/-! # `IndexedScannerProgress` — Phase 3 Step 6f.3b3.internals.progress

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6f).

## Scope (`.progress.leaf` + `.progress.capstone`)

Indexed twin of `Proofs/Scanner/ScannerProgress.lean` + the per-leaf,
per-dispatcher, and capstone `_offset_lt` / `_offset_gt` block at the
bottom of legacy `Proofs/Scanner/ScannerCorrectness.lean`. Provides
*strict* offset-progress (`<`) for every leaf scanner reachable from
`scanNextTokenIx`, lifts those facts to the four sub-dispatchers
(`dispatchStructural`, `dispatchFlowIndicators`, `dispatchBlockIndicators`,
`dispatchContent`), and composes them into the top-level
`scanNextTokenIx_progress` capstone (the indexed twin of legacy
`ScannerCorrectness.scanNextToken_progress`).

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
  - **`scanPlainScalarIx_offset_lt`** — discharged from the
    `canStart_*` boolean helpers (§4 prelude) by direct
    case-split on the first iteration of `collectPlainScalarLoopIx`.

  (`scanDoubleQuotedIx_offset_lt` / `scanSingleQuotedIx_offset_lt`
  already live in `Proofs/Scanner/IndexedScalar.lean`.)

### §5 Per-dispatcher strict progress (`_offset_gt`)
  - `scanNextTokenIx_dispatchStructural_offset_gt`,
    `scanNextTokenIx_dispatchFlowIndicators_offset_gt`,
    `scanNextTokenIx_dispatchBlockIndicators_offset_gt`,
    `scanNextTokenIx_dispatchContent_offset_gt`.

### §6 Preprocess upstream lemmas (capstone prerequisites)
  - `scanNextTokenIx_preprocess_peek_eq`: the `c` returned by
    `preprocess` matches `s'.peek?`.
  - `scanNextTokenIx_preprocess_hasMore`: under
    `preprocess = .ok (some _)`, the post-state has more input.

### §7 Capstone — `scanNextTokenIx_progress`
  Composes preprocess + the four sub-dispatcher `_offset_gt` lemmas
  into the top-level strict-progress fact. Indexed twin of legacy
  `scanNextToken_progress` (`ScannerCorrectness.lean:10549`,
  `maxHeartbeats 800000`).

## Note on the unused `h_noDoc` precondition

Legacy `scanPlainScalar_offset_lt` takes `hnoDoc : (s.col == 0 &&
atDocumentBoundary s) = false` because legacy
`collectPlainScalar_terminates?` (`Scanner/Scalar.lean:427`) checks
`atDocumentBoundary s` inline as a termination guard. The indexed
`collectPlainScalarLoopIx` does NOT replicate that guard — document-
boundary handling is delegated upstream to the dispatchers
(`dispatchStructural`'s `atDocumentStartIx` / `atDocumentEndIx`
checks). So `scanPlainScalarIx_offset_lt` does not need `h_noDoc`.
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

/-! ### Plain-scalar strict progress

`scanPlainScalarIx_offset_lt` requires unfolding the first iteration of
`collectPlainScalarLoopIx` and ruling out every terminating branch in
favor of the "regular char advance + recurse" branch.

The proof uses four character-level helper facts (mirroring legacy
`canStart_*` at `ScannerCorrectness.lean:10228–10260`):
  - `canStart_not_lb` — `canStart … = true → isLineBreakBool ch = false`
  - `canStart_not_ws` — `canStart … = true → isWhiteSpaceBool ch = false`
  - `canStart_plainSafe` — `canStart … = true → isPlainSafeBool ch = true`
  - `canStart_not_flowIndicator` — `canStart … = true → isFlowIndicatorBool ch = false`

Plus a `colonTerminatesPlain_false_of_canStart` step for the `ch = ':'`
branch (deriving `colonTerminatesPlain c inFlow = false` from `canStart`'s
`peekAt? 1`-side conditions).

The indexed `collectPlainScalarLoopIx` does *not* check
`atDocumentBoundary` (the legacy `collectPlainScalar_terminates?` did),
so we don't need the `h_noDoc` precondition the legacy carried — see
the file header for details. -/

/-! #### Boolean helpers (ports of `ScannerCorrectness.lean:10228–10260`) -/

/-- Flow indicators are indicators. -/
theorem flowIndicator_isIndicator' (c : Char) (h : isFlowIndicatorBool c = true) :
    isIndicatorBool c = true := by
  simp [isFlowIndicatorBool, List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl; all_goals decide

/-- `canStart` implies not a line break. -/
theorem canStart_not_lb (c : Char) (next : Option Char) (inFlow : Bool)
    (hcan : canStartPlainScalarBool c next inFlow = true) :
    isLineBreakBool c = false := by
  unfold canStartPlainScalarBool at hcan; split at hcan
  · rename_i hc; rcases hc with rfl | rfl | rfl <;> decide
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcan; exact hcan.2

/-- `canStart` implies not whitespace. -/
theorem canStart_not_ws (c : Char) (next : Option Char) (inFlow : Bool)
    (hcan : canStartPlainScalarBool c next inFlow = true) :
    isWhiteSpaceBool c = false := by
  unfold canStartPlainScalarBool at hcan; split at hcan
  · rename_i hc; rcases hc with rfl | rfl | rfl <;> decide
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcan; exact hcan.1.2

/-- `canStart` implies plain-safe. -/
theorem canStart_plainSafe (c : Char) (next : Option Char) (inFlow : Bool)
    (hcan : canStartPlainScalarBool c next inFlow = true) :
    isPlainSafeBool c inFlow = true := by
  have hws := canStart_not_ws c next inFlow hcan
  have hlb := canStart_not_lb c next inFlow hcan
  simp only [isPlainSafeBool]; split
  · simp [hws, hlb]; cases h_fi : isFlowIndicatorBool c
    · rfl
    · unfold canStartPlainScalarBool at hcan; split at hcan
      · rename_i hc; rcases hc with rfl | rfl | rfl <;> simp [isFlowIndicatorBool] at h_fi
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcan
        exact absurd (flowIndicator_isIndicator' c h_fi) (by simp [hcan.1.1])
  · simp [hws, hlb]

/-- `canStart` implies not a flow indicator. -/
theorem canStart_not_flowIndicator (c : Char) (next : Option Char) (inFlow : Bool)
    (hcan : canStartPlainScalarBool c next inFlow = true) :
    isFlowIndicatorBool c = false := by
  cases h_fi : isFlowIndicatorBool c with
  | false => rfl
  | true =>
    exfalso
    have hind : isIndicatorBool c = true := flowIndicator_isIndicator' c h_fi
    unfold canStartPlainScalarBool at hcan; split at hcan
    · rename_i hc
      rcases hc with rfl | rfl | rfl <;> simp [isFlowIndicatorBool] at h_fi
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcan
      exact absurd hind (by simp [hcan.1.1])

/-- When `canStart` holds on `':'`, `colonTerminatesPlain c inFlow = false`. -/
theorem colonTerminatesPlain_false_of_canStart {input : String} (c : IxCursor input)
    (inFlow : Bool)
    (h_can : canStartPlainScalarBool ':' (c.peekAt? 1) inFlow = true) :
    colonTerminatesPlain c inFlow = false := by
  unfold colonTerminatesPlain
  -- Use `split` rather than `cases` because the match body contains nested `&&`s.
  split
  · -- some n: derive blank/flowIndicator facts from canStart
    rename_i n h_p1
    rw [h_p1] at h_can
    unfold canStartPlainScalarBool at h_can
    -- Manually reduce the `if`: ':' satisfies the `-`/`?`/`:` disjunction.
    rw [if_pos (Or.inr (Or.inr rfl))] at h_can
    -- After `match (some n) with | some n => P n | none => false`, body reduces to `P n`.
    dsimp only at h_can
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h_can
    obtain ⟨⟨hws, hlb⟩, hfi⟩ := h_can
    -- Goal: (isBlankBool n || (inFlow && isFlowIndicatorBool n)) = false
    simp [isBlankBool, hws, hlb, hfi]
  · -- none: canStart on ':' with no next char returns false; contradicts h_can = true
    rename_i h_p1
    rw [h_p1] at h_can
    unfold canStartPlainScalarBool at h_can
    rw [if_pos (Or.inr (Or.inr rfl))] at h_can
    -- After `match none with | some _ => _ | none => false`, body reduces to `false`.
    dsimp only at h_can
    exact absurd h_can (by decide)

/-- Strict progress for `scanPlainScalarIx` when the initial character
    can start a plain scalar. Indexed twin of legacy
    `scanPlainScalar_offset_lt` (`ScannerCorrectness.lean:10304`).

    Preconditions:
    - `c.pos.offset < input.utf8ByteSize` (the cursor has more input)
    - `c.peek? = some ch` (the first character is `ch`)
    - `canStartPlainScalarBool ch (c.peekAt? 1) inFlow = true` (the
      character can begin a plain scalar) -/
theorem scanPlainScalarIx_offset_lt {input : String} (c : IxCursor input)
    (ch : Char) (inFlow : Bool) (contentIndent : Nat)
    (h_hm : c.pos.offset < input.utf8ByteSize)
    (h_peek : c.peek? = some ch)
    (h_can : canStartPlainScalarBool ch (c.peekAt? 1) inFlow = true) :
    c.pos.offset < (scanPlainScalarIx c inFlow contentIndent).2.pos.offset := by
  unfold scanPlainScalarIx
  show c.pos.offset <
    (collectPlainScalarLoopIx c "" "" inFlow contentIndent input.utf8ByteSize).2.pos.offset
  -- Strict step: c.pos.offset < c.advance.pos.offset
  have h_adv : c.pos.offset < c.advance.pos.offset :=
    L4YAML.Indexed.IxCursor.advance_offset_lt_of_hasMore c h_hm
  -- Decompose fuel as m + 1 (since input.utf8ByteSize ≥ 1)
  obtain ⟨m, hm⟩ : ∃ m, input.utf8ByteSize = m + 1 :=
    ⟨input.utf8ByteSize - 1, by omega⟩
  rw [hm]
  refine Nat.lt_of_lt_of_le h_adv ?_
  -- canStart facts gathered up front
  have h_not_lb : isLineBreakBool ch = false := canStart_not_lb ch _ inFlow h_can
  have h_not_ws : isWhiteSpaceBool ch = false := canStart_not_ws ch _ inFlow h_can
  have h_ps : isPlainSafeBool ch inFlow = true := canStart_plainSafe ch _ inFlow h_can
  have h_not_fi : isFlowIndicatorBool ch = false :=
    canStart_not_flowIndicator ch _ inFlow h_can
  -- Open the loop body via repeated `split` (mirrors the existing
  -- `collectPlainScalarLoopIx_offset_monotonic` proof structure).
  unfold collectPlainScalarLoopIx
  split
  · -- peek? = none: contradicts h_peek
    rename_i h_pn
    rw [h_peek] at h_pn; cases h_pn
  · -- peek? = some ch'
    rename_i ch' h_ps_some
    -- Replace ch' with ch in the goal using h_peek
    have h_eq : ch' = ch := by
      rw [h_ps_some] at h_peek
      exact Option.some.inj h_peek
    rw [h_eq]
    -- Guard 1: isCommentBool ch && spaces.length > 0 (spaces = "")
    split
    · rename_i h_c; exfalso; simp at h_c
    -- Guard 2: isMappingValueBool ch && colonTerminatesPlain c inFlow
    split
    · rename_i h_ct
      exfalso
      by_cases h_isMV : isMappingValueBool ch = true
      · have h_ceq : ch = ':' := by
          unfold isMappingValueBool at h_isMV; exact eq_of_beq h_isMV
        subst h_ceq
        have h_ct_false : colonTerminatesPlain c inFlow = false :=
          colonTerminatesPlain_false_of_canStart c inFlow h_can
        simp [h_ct_false] at h_ct
      · simp [h_isMV] at h_ct
    -- Guard 3: isMappingValueBool ch (ch = ':' here — advance + recurse)
    split
    · -- collectPlainScalarLoopIx c.advance ... m
      exact collectPlainScalarLoopIx_offset_monotonic c.advance _ _ _ _ _
    -- Guard 4: inFlow && isFlowIndicatorBool ch — ruled out by canStart
    split
    · rename_i h_fi
      exfalso
      have : isFlowIndicatorBool ch = true := (Bool.and_eq_true _ _).mp h_fi |>.2
      rw [h_not_fi] at this; cases this
    -- Guard 5: isLineBreakBool ch — ruled out
    split
    · rename_i h_lb
      exfalso; rw [h_not_lb] at h_lb; cases h_lb
    -- Guard 6: isWhiteSpaceBool ch — ruled out
    split
    · rename_i h_ws
      exfalso; rw [h_not_ws] at h_ws; cases h_ws
    -- Guard 7: !isPlainSafeBool ch inFlow — ruled out
    split
    · rename_i h_nps
      exfalso
      simp only [Bool.not_eq_true'] at h_nps
      rw [h_ps] at h_nps; cases h_nps
    -- Else: recurse via c.advance
    exact collectPlainScalarLoopIx_offset_monotonic c.advance _ _ _ _ _

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

/-- `scanNextTokenIx_dispatchContent` strict progress on `.ok s'`. All
    productions (including plain scalar) chain through their respective
    `_offset_lt` lemmas. Unlike the legacy
    `ScannerCorrectness.dispatchContent_offset_gt`
    (`Proofs/Scanner/ScannerCorrectness.lean:10435`), no `h_noDoc`
    precondition is needed — the indexed `collectPlainScalarLoopIx`
    does not perform an `atDocumentBoundary` check (legacy
    `collectPlainScalar_terminates?` did at
    `Scanner/Scalar.lean:442`). -/
theorem scanNextTokenIx_dispatchContent_offset_gt {s s' : ScannerStateIx input} {c : Char}
    (h_hm : s.cursor.pos.offset < input.utf8ByteSize)
    (h_peek : s.peek? = some c)
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
                -- Plain-scalar arm — discharged via §4 proof. The indexed
                -- `collectPlainScalarLoopIx` doesn't check document boundaries,
                -- so `h_noDoc` is unused here (unlike the legacy proof).
                exact scanPlainScalarIx_offset_lt s.cursor c s.inFlow _
                  h_hm h_peek hg7
              · rw [if_neg hg7] at h
                cases h

/-! ## §6  Preprocess upstream lemmas

`scanNextTokenIx_progress` needs two facts about the `(s', c)` returned
by a successful `scanNextTokenIx_preprocess` call:

  - **`_peek_eq`**: `s'.peek? = some c` — the character `c` that
    preprocess emits is the one that `s'.peek?` will reveal. Used to
    feed `h_peek` into `dispatchContent_offset_gt`.
  - **`_hasMore`**: `s'.cursor.pos.offset < input.utf8ByteSize` — the
    post-preprocess cursor sits strictly inside the input, so all
    leaf strict-progress lemmas (which take `h_hm` as a precondition)
    are applicable. -/

/-- The `c` returned by a successful preprocess matches `s'.peek?`. -/
theorem scanNextTokenIx_preprocess_peek_eq {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_preprocess s = .ok (some (s', c))) :
    s'.peek? = some c := by
  unfold scanNextTokenIx_preprocess at h
  simp only at h
  split at h
  · simp at h                                                -- !hasMore arm
  · split at h
    all_goals
      split at h
      · simp at h                                            -- trailingContent error
      · split at h
        · simp at h                                          -- peek? = none arm
        · rename_i h_pk
          simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hs, hc⟩ := h
          subst hs; subst hc
          exact h_pk

/-- A successful preprocess leaves the cursor strictly inside the
    input (witnessed by the `some c` peek). -/
theorem scanNextTokenIx_preprocess_hasMore {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_preprocess s = .ok (some (s', c))) :
    s'.cursor.pos.offset < input.utf8ByteSize := by
  have h_peek := scanNextTokenIx_preprocess_peek_eq h
  by_cases h_lt : s'.cursor.pos.offset < input.utf8ByteSize
  · exact h_lt
  · exfalso
    have h_ge : input.utf8ByteSize ≤ s'.cursor.pos.offset := Nat.le_of_not_lt h_lt
    have h_none : s'.cursor.peek? = none :=
      (L4YAML.Indexed.IxCursor.peek?_eq_none_iff s'.cursor).mpr h_ge
    -- s'.peek? unfolds to s'.cursor.peek?, so they collide
    have h_pn : s'.peek? = none := h_none
    rw [h_pn] at h_peek
    cases h_peek

/-! ## §7  Capstone — `scanNextTokenIx_progress`

Composes preprocess monotonicity (`_offset_monotonic`) with one of the
four sub-dispatchers' strict progress (`_offset_gt`). The shape mirrors
legacy `ScannerCorrectness.scanNextToken_progress`
(`Proofs/Scanner/ScannerCorrectness.lean:10549`, ~85 LOC with
`maxHeartbeats 800000`), but the indexed substrate eliminates one
helper: legacy `dispatchStructural_none_noDoc` (10493) is unneeded
because indexed `dispatchContent_offset_gt` does not consume
`h_noDoc` — see the §5 doc-comment for the substrate explanation. -/

set_option maxHeartbeats 800000 in
/-- **Scanner progress (indexed)**: every successful
    `scanNextTokenIx s = .ok (some s')` call has
    `s.cursor.pos.offset < s'.cursor.pos.offset`. The capstone
    termination argument for `ScanChainIx.fuel_bound`. -/
theorem scanNextTokenIx_progress {input : String}
    {s s' : ScannerStateIx input}
    (h : scanNextTokenIx s = .ok (some s')) :
    s.cursor.pos.offset < s'.cursor.pos.offset := by
  unfold scanNextTokenIx at h
  simp only [Bind.bind, Except.bind] at h
  cases hPre : scanNextTokenIx_preprocess s with
  | error e => rw [hPre] at h; cases h
  | ok preRes =>
    rw [hPre] at h
    cases preRes with
    | none => cases h
    | some sc =>
      obtain ⟨sp, c⟩ := sc
      have hPpO : s.cursor.pos.offset ≤ sp.cursor.pos.offset :=
        scanNextTokenIx_preprocess_offset_monotonic hPre
      have hHm : sp.cursor.pos.offset < input.utf8ByteSize :=
        scanNextTokenIx_preprocess_hasMore hPre
      have hPk : sp.peek? = some c :=
        scanNextTokenIx_preprocess_peek_eq hPre
      simp only at h
      cases hStr : scanNextTokenIx_dispatchStructural sp c with
      | error e => rw [hStr] at h; cases h
      | ok structRes =>
        rw [hStr] at h
        cases structRes with
        | some s'' =>
          cases h
          exact Nat.lt_of_le_of_lt hPpO
            (scanNextTokenIx_dispatchStructural_offset_gt hHm hStr)
        | none =>
          -- Reduce to: sp.cursor.pos.offset < s'.cursor.pos.offset.
          suffices hChain : sp.cursor.pos.offset < s'.cursor.pos.offset by
            exact Nat.lt_of_le_of_lt hPpO hChain
          by_cases hAD : sp.allowDirectives = true
          · -- Positive case: `{ sp with allowDirectives := false,
            -- documentEverStarted := true }` has cursor = sp.cursor (defeq), so
            -- the per-dispatcher strict-progress facts about it transfer to
            -- `sp` via the defeq. We re-state `hHm` and `hPk` in the `sadj`
            -- shape so Lean can infer the dispatcher's implicit `s` from
            -- them directly.
            rw [if_pos hAD] at h
            have h_sadj_hm :
                ({ sp with allowDirectives := false, documentEverStarted := true } :
                    ScannerStateIx input).cursor.pos.offset < input.utf8ByteSize := hHm
            have h_sadj_pk :
                ({ sp with allowDirectives := false, documentEverStarted := true } :
                    ScannerStateIx input).peek? = some c := hPk
            -- Reshape the goal so the dispatcher's conclusion lands on it.
            show ({ sp with allowDirectives := false, documentEverStarted := true } :
                    ScannerStateIx input).cursor.pos.offset < s'.cursor.pos.offset
            cases hChk : scanNextTokenIx_checkBlockFlowIndent
                { sp with allowDirectives := false, documentEverStarted := true } c with
            | error e => rw [hChk] at h; cases h
            | ok _ =>
              rw [hChk] at h
              cases hFlow : scanNextTokenIx_dispatchFlowIndicators
                  { sp with allowDirectives := false, documentEverStarted := true } c with
              | error e => rw [hFlow] at h; cases h
              | ok flowRes =>
                rw [hFlow] at h
                cases flowRes with
                | some _ =>
                  cases h
                  exact scanNextTokenIx_dispatchFlowIndicators_offset_gt h_sadj_hm hFlow
                | none =>
                  cases hBlk : scanNextTokenIx_dispatchBlockIndicators
                      { sp with allowDirectives := false, documentEverStarted := true } c with
                  | error e => rw [hBlk] at h; cases h
                  | ok blkRes =>
                    rw [hBlk] at h
                    cases blkRes with
                    | some _ =>
                      cases h
                      exact scanNextTokenIx_dispatchBlockIndicators_offset_gt h_sadj_hm hBlk
                    | none =>
                      cases hCon : scanNextTokenIx_dispatchContent
                          { sp with allowDirectives := false, documentEverStarted := true } c with
                      | error e => rw [hCon] at h; cases h
                      | ok _ =>
                        rw [hCon] at h
                        cases h
                        exact scanNextTokenIx_dispatchContent_offset_gt h_sadj_hm h_sadj_pk hCon
          · -- Negative case: dispatchers receive `sp` directly.
            rw [if_neg hAD] at h
            cases hChk : scanNextTokenIx_checkBlockFlowIndent sp c with
            | error e => rw [hChk] at h; cases h
            | ok _ =>
              rw [hChk] at h
              cases hFlow : scanNextTokenIx_dispatchFlowIndicators sp c with
              | error e => rw [hFlow] at h; cases h
              | ok flowRes =>
                rw [hFlow] at h
                cases flowRes with
                | some _ =>
                  cases h
                  exact scanNextTokenIx_dispatchFlowIndicators_offset_gt hHm hFlow
                | none =>
                  cases hBlk : scanNextTokenIx_dispatchBlockIndicators sp c with
                  | error e => rw [hBlk] at h; cases h
                  | ok blkRes =>
                    rw [hBlk] at h
                    cases blkRes with
                    | some _ =>
                      cases h
                      exact scanNextTokenIx_dispatchBlockIndicators_offset_gt hHm hBlk
                    | none =>
                      cases hCon : scanNextTokenIx_dispatchContent sp c with
                      | error e => rw [hCon] at h; cases h
                      | ok _ =>
                        rw [hCon] at h
                        cases h
                        exact scanNextTokenIx_dispatchContent_offset_gt hHm hPk hCon

end L4YAML.Proofs.Indexed.ScannerProgress
