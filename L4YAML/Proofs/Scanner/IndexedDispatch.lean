/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.IndexedDispatch

/-! # `IndexedDispatch` — Phase 3 dispatcher-layer proofs (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6).

## Scope (Step 5b.1b.i–iv, partial)

State-helper cursor-preservation + offset-monotonicity infrastructure,
per-dispatcher monotonicity for the simple-shape dispatchers
(5b.1b.ii), the node-property + directive dispatchers (5b.1b.iii), and
the leaf `*_tokens_size_le` helpers (5b.1b.iv-pre) — the tokens-size
growth facts for emit/emitAt/etc. plus a `*_tokens_size_le` lemma for
every dispatcher already proven in 5b.1b.ii–iii.

The seven top-level lemmas the Blueprint targets for 5b.1b.iv (five
`scanNextTokenIx_*` + `scanNextTokenIx` + `scanLoopIx`) are *not* here.
They chain through `do`-block binds with nested `let`-zeta'd `if`/
`match` shapes that the 5b.1b.iii `simp only at h` + `split at h`
pattern doesn't cleanly handle (the inner-let `if` produces extra
`isFalse.isTrue` / `isFalse.isFalse` sub-cases that don't match the
expected 2-arm shape). They are deferred to 5b.1b.iv-cont, with R50
documenting the exact obstacle and the two candidate fixes
(case-exhaustive nested splits vs. `all_goals first`).

The dispatcher functions in `Scanner/IndexedDispatch.lean` thread the
cursor through helpers that fall into two families:

- **Cursor-preserving** (`emit`, `emitAt`, `emitAtCursor`,
  `overwriteAtCursor`, `pushSequenceIndentIx`, `pushMappingIndentIx`,
  `unwindIndentsLoopIx`, `unwindIndentsIx`, `saveSimpleKeyIx`,
  `scanValuePrepareIx`) — the output `.cursor` is definitionally
  `s.cursor`.
- **Cursor-monotonic** (`advance`, `advanceN`, `skipSpacesS`,
  `skipWhitespaceS`, `skipToContentS`) — the output cursor's
  byte offset is `≥` the input's.

The cursor-level monotonicity lemmas (`consumeLineBreak_offset_monotonic`,
`skipCommentText_offset_monotonic`, `skipToContent_offset_monotonic`,
`skipWhitespace_offset_monotonic`, `skipSpaces_offset_monotonic`)
already exist in `Proofs/Scanner/IndexedWhitespace.lean` and
`Proofs/Scanner/IndexedIndent.lean`; this file lifts them to the
`ScannerStateIx` layer and adds the cursor-preservation lemmas above.

The one new cursor-level lemma is `IxCursor.advanceN_offset_monotonic`
(the multi-step advance was not needed by the whitespace / indent
proofs).

## Layout

1. `IxCursor.advanceN_offset_monotonic`.
2. `ScannerStateIx` cursor-preservation lemmas (token emission,
   indent-stack updates, simple-key save, value-prepare).
3. `ScannerStateIx` state-level offset-monotonicity lemmas for the
   skip-helpers (`skipSpacesS`, `skipWhitespaceS`, `skipToContentS`).

## What's not here (`5b.1b.iv-cont`)

- The seven top-level Blueprint lemmas: five `scanNextTokenIx_*`
  sub-dispatcher monotonicity proofs (preprocess + structural / flow
  / block / content), `scanNextTokenIx`, and `scanLoopIx`. The leaf
  helpers below are the chain ingredients these will compose. -/

namespace L4YAML.Indexed.IxCursor

/-- `advanceN` is monotonic on the byte offset. Chained
    `advance_offset_monotonic` via induction on `n`. -/
theorem advanceN_offset_monotonic {input : String} (c : IxCursor input) (n : Nat) :
    c.pos.offset ≤ (c.advanceN n).pos.offset := by
  induction n generalizing c with
  | zero => unfold advanceN; exact Nat.le_refl _
  | succ n' ih =>
    unfold advanceN
    exact Nat.le_trans (advance_offset_monotonic c) (ih c.advance)

end L4YAML.Indexed.IxCursor

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.Indexed L4YAML.CharPredicates

/-! ## `ScannerStateIx` — cursor-preservation lemmas

Token-emission and indent-stack updates do not move the cursor. The
proofs are `rfl` (structure update preserves unspecified fields) or
one-line `split`s. -/

namespace ScannerStateIx

@[simp] theorem emit_cursor {input : String} (s : ScannerStateIx input) (tok : YamlToken) :
    (s.emit tok).cursor = s.cursor := rfl

@[simp] theorem emitAt_cursor {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (h : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok h).cursor = s.cursor := rfl

@[simp] theorem emitAtCursor_cursor {input : String} (s : ScannerStateIx input)
    (sk : IxCursor input) (tok : YamlToken) :
    (s.emitAtCursor sk tok).cursor = s.cursor := rfl

@[simp] theorem overwriteAtCursor_cursor {input : String} (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken) :
    (s.overwriteAtCursor i sk tok).cursor = s.cursor := rfl

@[simp] theorem advance_cursor {input : String} (s : ScannerStateIx input) :
    s.advance.cursor = s.cursor.advance := rfl

theorem advance_offset_monotonic {input : String} (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ s.advance.cursor.pos.offset :=
  IxCursor.advance_offset_monotonic s.cursor

@[simp] theorem advanceN_cursor {input : String} (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).cursor = s.cursor.advanceN n := rfl

theorem advanceN_offset_monotonic {input : String} (s : ScannerStateIx input) (n : Nat) :
    s.cursor.pos.offset ≤ (s.advanceN n).cursor.pos.offset := by
  rw [advanceN_cursor]
  exact IxCursor.advanceN_offset_monotonic s.cursor n

@[simp] theorem pushSequenceIndentIx_cursor {input : String} (s : ScannerStateIx input)
    (col : Int) :
    (pushSequenceIndentIx s col).cursor = s.cursor := by
  unfold pushSequenceIndentIx
  split <;> rfl

@[simp] theorem pushMappingIndentIx_cursor {input : String} (s : ScannerStateIx input)
    (col : Int) :
    (pushMappingIndentIx s col).cursor = s.cursor := by
  unfold pushMappingIndentIx
  split <;> rfl

/-! ## `flowLevel`/`inFlow` preservation lemmas (used by Step 5b.2)

`pushSequenceIndentIx` / `pushMappingIndentIx` / `emit` / `advance`
all keep the `flowLevel` field intact (they only update tokens / cursor /
indents). This lets the post-advance `if (!s.inFlow)` in `scanBlockEntryIx`
/ `scanKeyIx` (Step 5b.2 tab-check) be reasoned about with the original
state's `inFlow` after `rw [if_pos/if_neg]`. -/

@[simp] theorem emit_flowLevel {input : String} (s : ScannerStateIx input)
    (tok : YamlToken) : (s.emit tok).flowLevel = s.flowLevel := rfl

@[simp] theorem advance_flowLevel {input : String} (s : ScannerStateIx input) :
    s.advance.flowLevel = s.flowLevel := rfl

@[simp] theorem pushSequenceIndentIx_flowLevel {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (pushSequenceIndentIx s col).flowLevel = s.flowLevel := by
  unfold pushSequenceIndentIx
  split <;> rfl

@[simp] theorem pushMappingIndentIx_flowLevel {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (pushMappingIndentIx s col).flowLevel = s.flowLevel := by
  unfold pushMappingIndentIx
  split <;> rfl

@[simp] theorem emit_inFlow {input : String} (s : ScannerStateIx input)
    (tok : YamlToken) : (s.emit tok).inFlow = s.inFlow := rfl

@[simp] theorem advance_inFlow {input : String} (s : ScannerStateIx input) :
    s.advance.inFlow = s.inFlow := rfl

@[simp] theorem pushMappingIndentIx_inFlow {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (pushMappingIndentIx s col).inFlow = s.inFlow := by
  unfold pushMappingIndentIx
  split <;> rfl

@[simp] theorem unwindIndentsLoopIx_cursor {input : String} (s : ScannerStateIx input)
    (col : Int) (fuel : Nat) :
    (unwindIndentsLoopIx s col fuel).cursor = s.cursor := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoopIx; rfl
  | succ fuel ih =>
    unfold unwindIndentsLoopIx
    split
    · exact ih _
    · rfl

@[simp] theorem unwindIndentsIx_cursor {input : String} (s : ScannerStateIx input)
    (col : Int) :
    (unwindIndentsIx s col).cursor = s.cursor :=
  unwindIndentsLoopIx_cursor s col s.indents.size

@[simp] theorem saveSimpleKeyIx_cursor {input : String} (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).cursor = s.cursor := by
  unfold saveSimpleKeyIx
  split
  · rfl
  · split <;> rfl

@[simp] theorem scanValueClearKeyIx_cursor {input : String} (s : ScannerStateIx input) :
    (scanValueClearKeyIx s).cursor = s.cursor := by
  unfold scanValueClearKeyIx
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

@[simp] theorem scanValuePrepareIx_cursor {input : String} (s : ScannerStateIx input) :
    (scanValuePrepareIx s).cursor = s.cursor := by
  unfold scanValuePrepareIx
  split
  · -- s.simpleKey.possible
    split
    · -- !s.inFlow
      split <;> rfl
    · -- inFlow
      rfl
  · split
    · -- s.explicitKeyLine.isSome
      rfl
    · -- else: pushMappingIndentIx s ... or s
      split
      · exact pushMappingIndentIx_cursor s s.cursor.pos.col
      · rfl

/-! ## `ScannerStateIx` — state-level offset monotonicity for skip-helpers

`skipSpacesS`, `skipWhitespaceS`, `skipToContentS` thread the cursor
through `skipSpaces` / `skipWhitespace` / `skipToContent`. Their
state-level monotonicity follows directly. -/

@[simp] theorem skipSpacesS_cursor {input : String} (s : ScannerStateIx input) :
    s.skipSpacesS.1.cursor = (L4YAML.Scanner.Indexed.skipSpaces s.cursor).1 := rfl

theorem skipSpacesS_offset_monotonic {input : String} (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ s.skipSpacesS.1.cursor.pos.offset := by
  rw [skipSpacesS_cursor]
  exact skipSpaces_offset_monotonic s.cursor

@[simp] theorem skipWhitespaceS_cursor {input : String} (s : ScannerStateIx input) :
    s.skipWhitespaceS.cursor = L4YAML.Scanner.Indexed.skipWhitespace s.cursor := rfl

theorem skipWhitespaceS_offset_monotonic {input : String} (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ s.skipWhitespaceS.cursor.pos.offset := by
  rw [skipWhitespaceS_cursor]
  exact skipWhitespace_offset_monotonic s.cursor

@[simp] theorem skipToContentS_cursor {input : String} (s : ScannerStateIx input) :
    s.skipToContentS.cursor = L4YAML.Scanner.Indexed.skipToContent s.cursor := rfl

theorem skipToContentS_offset_monotonic {input : String} (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ s.skipToContentS.cursor.pos.offset := by
  rw [skipToContentS_cursor]
  exact skipToContent_offset_monotonic s.cursor

end ScannerStateIx

/-! ## Per-dispatcher offset monotonicity (Step 5b.1b.ii)

The ten simple-shape dispatchers compose `emit` / `advance` /
`advanceN` / `pushSequenceIndentIx` / `pushMappingIndentIx` /
`unwindIndentsIx` / `scanValuePrepareIx`. Each proof unfolds, chases
the `@[simp]` cursor-preservation lemmas from 5b.1b.i, and closes
with `IxCursor.advance_offset_monotonic` /
`advanceN_offset_monotonic`. The remaining `scanNextTokenIx_*` /
`scanLoopIx` family lands in 5b.1b.iv. -/

open ScannerStateIx

/-! ### Pattern A — always-`.ok` dispatchers -/

theorem scanBlockEntryIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} (h : scanBlockEntryIx s = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanBlockEntryIx at h
  by_cases hi : (!s.inFlow) = true
  · rw [if_pos hi] at h
    by_cases ht : s.hasTabInPrecedingWhitespace = true
    · -- §6.1 tab-throw fires; do-block reduces to `.error _` — contradicts `.ok s'`.
      rw [if_pos ht] at h
      simp [Bind.bind, Except.bind] at h
    · rw [if_neg ht] at h
      simp only [pure_bind] at h
      rw [if_pos hi] at h
      simp only [Except.ok.injEq] at h
      subst h
      show s.cursor.pos.offset ≤ _
      simp only [advance_cursor, emit_cursor, pushSequenceIndentIx_cursor]
      exact IxCursor.advance_offset_monotonic _
  · rw [if_neg hi] at h
    simp only [pure_bind] at h
    rw [if_neg hi] at h
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset ≤ _
    simp only [advance_cursor, emit_cursor]
    exact IxCursor.advance_offset_monotonic _

theorem scanKeyIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} (h : scanKeyIx s = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanKeyIx at h
  by_cases hi : (!s.inFlow) = true
  · -- Block context: rewrite the outer let-if first; that normalises
    -- the post-state to `pushMappingIndentIx s c` and lets the inFlow
    -- preservation lemmas collapse the inner if's condition to `s.inFlow`,
    -- which the second `if_pos hi` then rewrites to its `then` branch.
    simp only [if_pos hi, advance_inFlow, emit_inFlow,
      pushMappingIndentIx_inFlow] at h
    -- `if let some '\t' := … then throw` is `match s.peek? with`.
    split at h
    · -- some '\t' — throw fires; bind reduces to `.error _`, contradicts `.ok s'`.
      simp [Bind.bind, Except.bind] at h
    · -- catch-all — `pure () >>= ... = .ok {...}`.
      simp only [pure_bind, Except.ok.injEq] at h
      subst h
      show s.cursor.pos.offset ≤ _
      simp only [advance_cursor, emit_cursor, pushMappingIndentIx_cursor]
      exact IxCursor.advance_offset_monotonic _
  · -- Flow context: outer if collapses to `s`; inner if also takes else.
    simp only [if_neg hi, advance_inFlow, emit_inFlow] at h
    simp only [pure_bind, Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset ≤ _
    simp only [advance_cursor, emit_cursor]
    exact IxCursor.advance_offset_monotonic _

theorem scanValueIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} (h : scanValueIx s = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanValueIx at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h                                                  -- validate threw
  · split at h
    · cases h                                                -- tab-check threw
    · simp only [Except.ok.injEq] at h
      subst h
      show s.cursor.pos.offset ≤ _
      simp only [advance_cursor, emit_cursor, scanValuePrepareIx_cursor,
                 scanValueClearKeyIx_cursor]
      exact IxCursor.advance_offset_monotonic _

theorem scanFlowEntryIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} (h : scanFlowEntryIx s = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanFlowEntryIx at h
  simp only [Except.ok.injEq] at h
  subst h
  show s.cursor.pos.offset ≤ _
  simp only [advance_cursor, emit_cursor, scanValuePrepareIx_cursor]
  exact IxCursor.advance_offset_monotonic _

/-! ### Pattern B — state-returning dispatchers -/

theorem scanDocumentStartIx_offset_monotonic {input : String}
    (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ (scanDocumentStartIx s).cursor.pos.offset := by
  unfold scanDocumentStartIx
  show s.cursor.pos.offset ≤ _
  simp only [advanceN_cursor, emit_cursor, unwindIndentsIx_cursor]
  exact IxCursor.advanceN_offset_monotonic _ _

theorem scanFlowSequenceStartIx_offset_monotonic {input : String}
    (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ (scanFlowSequenceStartIx s).cursor.pos.offset := by
  unfold scanFlowSequenceStartIx
  show s.cursor.pos.offset ≤ _
  simp only [advance_cursor, emit_cursor]
  exact IxCursor.advance_offset_monotonic _

theorem scanFlowSequenceEndIx_offset_monotonic {input : String}
    (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ (scanFlowSequenceEndIx s).cursor.pos.offset := by
  unfold scanFlowSequenceEndIx
  show s.cursor.pos.offset ≤ _
  simp only [advance_cursor, emit_cursor]
  exact IxCursor.advance_offset_monotonic _

theorem scanFlowMappingStartIx_offset_monotonic {input : String}
    (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ (scanFlowMappingStartIx s).cursor.pos.offset := by
  unfold scanFlowMappingStartIx
  show s.cursor.pos.offset ≤ _
  simp only [advance_cursor, emit_cursor]
  exact IxCursor.advance_offset_monotonic _

theorem scanFlowMappingEndIx_offset_monotonic {input : String}
    (s : ScannerStateIx input) :
    s.cursor.pos.offset ≤ (scanFlowMappingEndIx s).cursor.pos.offset := by
  unfold scanFlowMappingEndIx
  show s.cursor.pos.offset ≤ _
  simp only [advance_cursor, emit_cursor]
  exact IxCursor.advance_offset_monotonic _

/-! ### Pattern C — `Except` with early/late throws

`scanDocumentEndIx` has an early `throw` on
`directivesPresent ∧ ¬documentEverStarted`, runs an unconditional
state-mutation chain (`unwindIndentsIx` → simpleKey reset →
`emit documentEnd` → `advanceN 3` → flag updates), then a trailing
match on `probe.peek?` that either resolves to `pure ()` or throws.

The state mutation chain preserves `cursor` (the leading `unwindIndentsIx`)
or advances it (the trailing `advanceN 3`), so on the `.ok` paths the
final `s'.cursor` differs from `s.cursor` by exactly an `advanceN 3`.
We use `Except.bind_ok` / explicit `if_pos` / `if_neg` rewriting to
peel the do-block, then close each surviving branch with
`advanceN_offset_monotonic`. -/

theorem scanDocumentEndIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} (h : scanDocumentEndIx s = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanDocumentEndIx at h
  -- Peel the early-throw guard.
  by_cases hd : (s.directivesPresent && !s.documentEverStarted) = true
  · -- Early throw fires; do-block reduces to `.error _` — contradicts `.ok s'`.
    rw [if_pos hd] at h
    simp [Bind.bind, Except.bind] at h
  · rw [if_neg hd] at h
    -- Normalize the outer `pure ()`-bind so the match is the next destructible.
    simp only [pure_bind] at h
    split at h
    all_goals first
      | (simp only [Except.ok.injEq] at h
         subst h
         show s.cursor.pos.offset ≤ _
         simp only [advanceN_cursor, emit_cursor, unwindIndentsIx_cursor]
         exact IxCursor.advanceN_offset_monotonic _ _)
      | (-- `some ch` arm: inner `if isLineBreakBool ch`
         split at h
         all_goals first
           | (simp only [Except.ok.injEq] at h
              subst h
              show s.cursor.pos.offset ≤ _
              simp only [advanceN_cursor, emit_cursor, unwindIndentsIx_cursor]
              exact IxCursor.advanceN_offset_monotonic _ _)
           | (-- inner throw branch contradicts `.ok s'`
              simp [Bind.bind, Except.bind] at h))

/-! ## Per-dispatcher offset monotonicity (Step 5b.1b.iii)

The five node-property + directive dispatchers compose the
`collect*LoopIx_offset_monotonic` helpers (5b.1a) and
`skipWhitespace_offset_monotonic` (cursor-level). The pattern is the
same as 5b.1b.ii, with two new wrinkles:

- The directive helpers `scanYamlDirectiveIx` / `scanTagDirectiveIx`
  take `cAfterWS : IxCursor input` as an explicit cursor parameter;
  their monotonicity is naturally stated relative to that parameter
  (`cAfterWS.pos.offset ≤ s'.cursor.pos.offset`). `scanDirectiveIx`
  chains through these via `skipWhitespace_offset_monotonic` and the
  pre-call `advance` (R49).
- `scanTagIx` matches `sAdv.peek?` into three arms (`some '<'`,
  `some '!'`, `_`); each arm is closed by chaining
  `IxCursor.advance_offset_monotonic` with the relevant `collect*Loop`
  lemma, and the verbatim-tag arm has two nested
  `if/.error` guards that contradict the `.ok` premise. -/

/-! ### Node properties — anchors, aliases, tags -/

theorem scanAnchorOrAliasIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} {isAnchor : Bool}
    (h : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanAnchorOrAliasIx at h
  -- The body is `let* ; if name.isEmpty then .error else .ok ...`. The
  -- term-level `let`s in `h` block `split` from finding the `if` (R49); peel
  -- the conditional with `by_cases` + `rw [if_pos/if_neg]` instead.
  by_cases hn : (collectAnchorNameLoopIx s.advance.cursor ""
      (input.utf8ByteSize - s.advance.cursor.pos.offset)).1.isEmpty = true
  · rw [if_pos hn] at h
    exact absurd h (by simp)
  · rw [if_neg hn] at h
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset ≤ _
    simp only [emitAt_cursor, advance_cursor]
    exact Nat.le_trans (IxCursor.advance_offset_monotonic _)
      (collectAnchorNameLoopIx_offset_monotonic _ _ _)

theorem scanTagIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input}
    (h : scanTagIx s = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanTagIx at h
  -- Zeta-reduce the outer `let startPos := ...; let sAdv := ...` so the
  -- `match sAdv.peek?` rises to the top and `split at h` can dispatch (R49).
  simp only at h
  split at h
  · -- some '<' — verbatim tag arm
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        show s.cursor.pos.offset ≤ _
        simp only [emitAt_cursor, advance_cursor]
        exact Nat.le_trans (IxCursor.advance_offset_monotonic _)
          (Nat.le_trans (IxCursor.advance_offset_monotonic _)
            (collectVerbatimTagLoopIx_offset_monotonic _ _ _))
  · -- some '!' — !! tag arm
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset ≤ _
    simp only [emitAt_cursor, advance_cursor]
    exact Nat.le_trans (IxCursor.advance_offset_monotonic _)
      (Nat.le_trans (IxCursor.advance_offset_monotonic _)
        (collectTagSuffixLoopIx_offset_monotonic _ _ _))
  · -- catch-all: `!handle!suffix` or `!suffix`
    simp only [Except.ok.injEq] at h
    subst h
    show s.cursor.pos.offset ≤ _
    simp only [emitAt_cursor, advance_cursor]
    refine Nat.le_trans (IxCursor.advance_offset_monotonic _) ?_
    refine Nat.le_trans
      (collectTagHandleLoopIx_offset_monotonic s.cursor.advance ""
        (input.utf8ByteSize - s.cursor.advance.pos.offset)) ?_
    split
    · exact collectTagSuffixLoopIx_offset_monotonic _ _ _
    · exact Nat.le_refl _

/-! ### Directives -/

theorem scanYamlDirectiveIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} {cAfterWS : IxCursor input} {startPos : YamlPos}
    {hStart : startPos.offset ≤ cAfterWS.pos.offset}
    (h : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s') :
    cAfterWS.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanYamlDirectiveIx at h
  -- Peel the duplicate-directive throw guard.
  by_cases hd : s.seenYamlDirective = true
  · rw [if_pos hd] at h
    simp [Bind.bind, Except.bind] at h
  · rw [if_neg hd] at h
    simp only [pure_bind] at h
    -- Remaining: `if !major.isEmpty && !minor.isEmpty then .ok ... else throw`.
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      show cAfterWS.pos.offset ≤ _
      simp only [emitAt_cursor]
      exact Nat.le_trans (collectVersionMajorLoopIx_offset_monotonic _ _ _)
        (Nat.le_trans (collectVersionMinorLoopIx_offset_monotonic _ _ _)
          (skipWhitespace_offset_monotonic _))
    · simp at h

theorem scanTagDirectiveIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} {cAfterWS : IxCursor input} {startPos : YamlPos}
    {hStart : startPos.offset ≤ cAfterWS.pos.offset}
    (h : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s') :
    cAfterWS.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanTagDirectiveIx at h
  simp only [Except.ok.injEq] at h
  subst h
  show cAfterWS.pos.offset ≤ _
  simp only [emitAt_cursor]
  exact Nat.le_trans (collectTagHandleLoopIx_offset_monotonic _ _ _)
    (Nat.le_trans (skipWhitespace_offset_monotonic _)
      (Nat.le_trans (collectTagSuffixLoopIx_offset_monotonic _ _ _)
        (skipWhitespace_offset_monotonic _)))

theorem scanDirectiveIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input}
    (h : scanDirectiveIx s = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanDirectiveIx at h
  split at h
  · -- !s.allowDirectives: .error
    simp at h
  · -- else branch: zeta-reduce lets before nested `split` (R49).
    simp only at h
    split at h
    · -- name == "YAML": delegate to scanYamlDirectiveIx_offset_monotonic
      have hChain := scanYamlDirectiveIx_offset_monotonic h
      refine Nat.le_trans ?_ hChain
      simp only [advance_cursor]
      exact Nat.le_trans (IxCursor.advance_offset_monotonic _)
        (Nat.le_trans (collectDirectiveNameLoopIx_offset_monotonic _ _ _)
          (skipWhitespace_offset_monotonic _))
    · split at h
      · -- name == "TAG": delegate to scanTagDirectiveIx_offset_monotonic
        have hChain := scanTagDirectiveIx_offset_monotonic h
        refine Nat.le_trans ?_ hChain
        simp only [advance_cursor]
        exact Nat.le_trans (IxCursor.advance_offset_monotonic _)
          (Nat.le_trans (collectDirectiveNameLoopIx_offset_monotonic _ _ _)
            (skipWhitespace_offset_monotonic _))
      · -- reserved directive: .ok { sAdv with cursor := cAfterWS }
        simp only [Except.ok.injEq] at h
        subst h
        show s.cursor.pos.offset ≤ _
        simp only [advance_cursor]
        exact Nat.le_trans (IxCursor.advance_offset_monotonic _)
          (Nat.le_trans (collectDirectiveNameLoopIx_offset_monotonic _ _ _)
            (skipWhitespace_offset_monotonic _))

/-! ## Top-level dispatcher offset monotonicity (Step 5b.1b.iv)

The five `scanNextTokenIx_*` sub-dispatchers, the per-iteration
`scanNextTokenIx`, and the fueled `scanLoopIx`. All six sub /
per-iteration lemmas state cursor monotonicity on the `.ok (some s')`
branch (preprocess additionally carries the lookahead character); the
proofs chain the 5b.1b.ii / 5b.1b.iii per-helper lemmas.

`scanLoopIx_offset_monotonic` is the only non-chain. Since `scanLoopIx`
returns a `TokenStream` rather than state, the claim is stated as
`s.tokens.size ≤ ts.tokens.size` and proven by induction on fuel,
chaining `scanNextTokenIx_tokens_size_le` (an auxiliary derived from
the per-helper structure: every emit grows tokens by 1, every
`overwriteAtCursor` preserves size). The full *"every newly-emitted
token has `start.offset ≥` initial cursor's offset"* claim — the
indexed-scanner analogue of the legacy `scanLoop_emits_in_order`
invariant — is deferred to Step 5b.2: it requires that each of the
5b.1b.ii / 5b.1b.iii leaf lemmas additionally claim a `start.offset`
bound for tokens emitted by the helper, which is a strict
strengthening of their current cursor-only statement (R50). -/

/-! ### Tokens-size and tokens-preservation helpers

The `_tokens` simp lemmas establish that the state's `tokens` field is
*preserved* through cursor-only updates (`advance`, `advanceN`, the
whitespace skips), and the `_tokens_size` lemmas count emits. -/

@[simp] theorem skipToContentS_tokens {input : String} (s : ScannerStateIx input) :
    s.skipToContentS.tokens = s.tokens := rfl

@[simp] theorem skipSpacesS_tokens {input : String} (s : ScannerStateIx input) :
    s.skipSpacesS.1.tokens = s.tokens := rfl

@[simp] theorem skipWhitespaceS_tokens {input : String} (s : ScannerStateIx input) :
    s.skipWhitespaceS.tokens = s.tokens := rfl

@[simp] theorem advance_tokens {input : String} (s : ScannerStateIx input) :
    s.advance.tokens = s.tokens := rfl

@[simp] theorem advanceN_tokens {input : String} (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).tokens = s.tokens := rfl

@[simp] theorem emit_tokens_size {input : String} (s : ScannerStateIx input)
    (tok : YamlToken) :
    (s.emit tok).tokens.size = s.tokens.size + 1 := by
  show (s.tokens.tokens.push _).size = s.tokens.tokens.size + 1
  exact Array.size_push ..

@[simp] theorem emitAt_tokens_size {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken) (h : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok h).tokens.size = s.tokens.size + 1 := by
  show (s.tokens.tokens.push _).size = s.tokens.tokens.size + 1
  exact Array.size_push ..

@[simp] theorem emitAtCursor_tokens_size {input : String} (s : ScannerStateIx input)
    (sk : IxCursor input) (tok : YamlToken) :
    (s.emitAtCursor sk tok).tokens.size = s.tokens.size + 1 := by
  show (s.tokens.tokens.push _).size = s.tokens.tokens.size + 1
  exact Array.size_push ..

@[simp] theorem overwriteAtCursor_tokens_size {input : String} (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken) :
    (s.overwriteAtCursor i sk tok).tokens.size = s.tokens.size := by
  show (s.tokens.tokens.setIfInBounds i _).size = s.tokens.tokens.size
  exact Array.size_setIfInBounds ..

theorem unwindIndentsLoopIx_tokens_size_le {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat) :
    s.tokens.size ≤ (unwindIndentsLoopIx s col fuel).tokens.size := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold unwindIndentsLoopIx
    split
    · refine Nat.le_trans ?_ (ih _)
      simp
    · exact Nat.le_refl _

theorem unwindIndentsIx_tokens_size_le {input : String}
    (s : ScannerStateIx input) (col : Int) :
    s.tokens.size ≤ (unwindIndentsIx s col).tokens.size :=
  unwindIndentsLoopIx_tokens_size_le s col s.indents.size

theorem pushSequenceIndentIx_tokens_size_le {input : String}
    (s : ScannerStateIx input) (col : Int) :
    s.tokens.size ≤ (pushSequenceIndentIx s col).tokens.size := by
  unfold pushSequenceIndentIx
  split
  · simp
  · exact Nat.le_refl _

theorem pushMappingIndentIx_tokens_size_le {input : String}
    (s : ScannerStateIx input) (col : Int) :
    s.tokens.size ≤ (pushMappingIndentIx s col).tokens.size := by
  unfold pushMappingIndentIx
  split
  · simp
  · exact Nat.le_refl _

theorem saveSimpleKeyIx_tokens_size_le {input : String} (s : ScannerStateIx input) :
    s.tokens.size ≤ (saveSimpleKeyIx s).tokens.size := by
  unfold saveSimpleKeyIx
  split
  · exact Nat.le_refl _
  · split
    · simp; omega
    · exact Nat.le_refl _

theorem scanValueClearKeyIx_tokens_size_le {input : String} (s : ScannerStateIx input) :
    s.tokens.size ≤ (scanValueClearKeyIx s).tokens.size := by
  unfold scanValueClearKeyIx
  split
  · split
    · exact Nat.le_refl _
    · split <;> exact Nat.le_refl _
  · exact Nat.le_refl _

theorem scanValuePrepareIx_tokens_size_le {input : String} (s : ScannerStateIx input) :
    s.tokens.size ≤ (scanValuePrepareIx s).tokens.size := by
  unfold scanValuePrepareIx
  split
  · split
    · split
      · simp
      · simp
    · simp
  · split
    · exact Nat.le_refl _
    · split
      · exact pushMappingIndentIx_tokens_size_le s s.cursor.pos.col
      · exact Nat.le_refl _

/-! ### Tokens-grow for the 5b.1b.ii / 5b.1b.iii dispatcher helpers

Each proof unfolds the dispatcher, destructures `h` (or substitutes
the `.ok` result), and closes by `simp` over the `emit_tokens_size`
/ `emitAt_tokens_size` / `_tokens` simp lemmas, plus `Nat.le_succ` /
`Nat.le_refl`. The `omega` tactic discharges arithmetic conclusions
when emit counts vary by branch. -/

theorem scanBlockEntryIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} (h : scanBlockEntryIx s = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanBlockEntryIx at h
  by_cases hi : (!s.inFlow) = true
  · rw [if_pos hi] at h
    by_cases ht : s.hasTabInPrecedingWhitespace = true
    · -- §6.1 tab-throw fires; contradicts `.ok s'`.
      rw [if_pos ht] at h
      simp [Bind.bind, Except.bind] at h
    · rw [if_neg ht] at h
      simp only [pure_bind] at h
      rw [if_pos hi] at h
      simp only [Except.ok.injEq] at h
      subst h
      show s.tokens.size ≤ _
      refine Nat.le_trans (pushSequenceIndentIx_tokens_size_le s s.cursor.pos.col) ?_
      simp
  · rw [if_neg hi] at h
    simp only [pure_bind] at h
    rw [if_neg hi] at h
    simp only [Except.ok.injEq] at h
    subst h
    show s.tokens.size ≤ _
    simp

theorem scanKeyIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} (h : scanKeyIx s = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanKeyIx at h
  by_cases hi : (!s.inFlow) = true
  · -- Block context: outer if rewrites; inFlow chains normalise the inner
    -- if's condition to `s.inFlow`; second if_pos hi rewrites the inner if.
    simp only [if_pos hi, advance_inFlow, emit_inFlow,
      pushMappingIndentIx_inFlow] at h
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [pure_bind, Except.ok.injEq] at h
      subst h
      show s.tokens.size ≤ _
      refine Nat.le_trans (pushMappingIndentIx_tokens_size_le s s.cursor.pos.col) ?_
      simp
  · -- Flow context: outer if collapses to `s`; inner if takes else.
    simp only [if_neg hi, advance_inFlow, emit_inFlow] at h
    simp only [pure_bind, Except.ok.injEq] at h
    subst h
    show s.tokens.size ≤ _
    simp

theorem scanValueIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} (h : scanValueIx s = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanValueIx at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h                                                  -- validate threw
  · split at h
    · cases h                                                -- tab-check threw
    · simp only [Except.ok.injEq] at h
      subst h
      refine Nat.le_trans (scanValueClearKeyIx_tokens_size_le s) ?_
      refine Nat.le_trans
        (scanValuePrepareIx_tokens_size_le (scanValueClearKeyIx s)) ?_
      show _ ≤ _
      simp

theorem scanFlowEntryIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} (h : scanFlowEntryIx s = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanFlowEntryIx at h
  simp only [Except.ok.injEq] at h
  subst h
  refine Nat.le_trans (scanValuePrepareIx_tokens_size_le s) ?_
  show _ ≤ _
  simp

theorem scanFlowSequenceStartIx_tokens_size_le {input : String}
    (s : ScannerStateIx input) :
    s.tokens.size ≤ (scanFlowSequenceStartIx s).tokens.size := by
  unfold scanFlowSequenceStartIx
  show s.tokens.size ≤ _
  simp

theorem scanFlowSequenceEndIx_tokens_size_le {input : String}
    (s : ScannerStateIx input) :
    s.tokens.size ≤ (scanFlowSequenceEndIx s).tokens.size := by
  unfold scanFlowSequenceEndIx
  show s.tokens.size ≤ _
  simp

theorem scanFlowMappingStartIx_tokens_size_le {input : String}
    (s : ScannerStateIx input) :
    s.tokens.size ≤ (scanFlowMappingStartIx s).tokens.size := by
  unfold scanFlowMappingStartIx
  show s.tokens.size ≤ _
  simp

theorem scanFlowMappingEndIx_tokens_size_le {input : String}
    (s : ScannerStateIx input) :
    s.tokens.size ≤ (scanFlowMappingEndIx s).tokens.size := by
  unfold scanFlowMappingEndIx
  show s.tokens.size ≤ _
  simp

theorem scanDocumentStartIx_tokens_size_le {input : String}
    (s : ScannerStateIx input) :
    s.tokens.size ≤ (scanDocumentStartIx s).tokens.size := by
  unfold scanDocumentStartIx
  show s.tokens.size ≤ _
  refine Nat.le_trans (unwindIndentsIx_tokens_size_le s (-1)) ?_
  simp

theorem scanDocumentEndIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} (h : scanDocumentEndIx s = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
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
         refine Nat.le_trans (unwindIndentsIx_tokens_size_le s (-1)) ?_
         simp)
      | (split at h
         all_goals first
           | (simp only [Except.ok.injEq] at h
              subst h
              refine Nat.le_trans (unwindIndentsIx_tokens_size_le s (-1)) ?_
              simp)
           | (simp [Bind.bind, Except.bind] at h))

theorem scanAnchorOrAliasIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} {isAnchor : Bool}
    (h : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanAnchorOrAliasIx at h
  by_cases hn : (collectAnchorNameLoopIx s.advance.cursor ""
      (input.utf8ByteSize - s.advance.cursor.pos.offset)).1.isEmpty = true
  · rw [if_pos hn] at h
    exact absurd h (by simp)
  · rw [if_neg hn] at h
    simp only [Except.ok.injEq] at h
    subst h
    show s.tokens.size ≤ _
    simp

theorem scanTagIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input}
    (h : scanTagIx s = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanTagIx at h
  simp only at h
  split at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        show s.tokens.size ≤ _
        simp
  · simp only [Except.ok.injEq] at h
    subst h
    show s.tokens.size ≤ _
    simp
  · simp only [Except.ok.injEq] at h
    subst h
    show s.tokens.size ≤ _
    simp

theorem scanYamlDirectiveIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} {cAfterWS : IxCursor input} {startPos : YamlPos}
    {hStart : startPos.offset ≤ cAfterWS.pos.offset}
    (h : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanYamlDirectiveIx at h
  by_cases hd : s.seenYamlDirective = true
  · rw [if_pos hd] at h
    simp [Bind.bind, Except.bind] at h
  · rw [if_neg hd] at h
    simp only [pure_bind] at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      show s.tokens.size ≤ _
      simp
    · simp at h

theorem scanTagDirectiveIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} {cAfterWS : IxCursor input} {startPos : YamlPos}
    {hStart : startPos.offset ≤ cAfterWS.pos.offset}
    (h : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanTagDirectiveIx at h
  simp only [Except.ok.injEq] at h
  subst h
  show s.tokens.size ≤ _
  simp

theorem scanDirectiveIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input}
    (h : scanDirectiveIx s = .ok s') :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanDirectiveIx at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · -- YAML: delegate. `sAdv := s.advance` and `advance` preserves `tokens` (rfl).
      have hChain := scanYamlDirectiveIx_tokens_size_le h
      show s.tokens.size ≤ _
      exact hChain
    · split at h
      · have hChain := scanTagDirectiveIx_tokens_size_le h
        show s.tokens.size ≤ _
        exact hChain
      · simp only [Except.ok.injEq] at h
        subst h
        show s.tokens.size ≤ _
        exact Nat.le_refl _

/-! ## Top-level dispatcher monotonicity (Step 5b.1b.iv-cont)

The seven Blueprint-targeted top-level lemmas: five `scanNextTokenIx_*`
sub-dispatchers (`preprocess`, `dispatchStructural`,
`dispatchFlowIndicators`, `dispatchBlockIndicators`, `dispatchContent`),
the per-iteration `scanNextTokenIx`, and the fueled `scanLoopIx`.

The proofs use R50's two-pronged technique: outer `unfold + simp only at h`
flattens the let-zeta'd body, then we use `split at h` with
`all_goals first | <success-arm> | <recurse>` patterns to handle the
let-zeta'd extra sub-cases without writing each path by hand. The
sub-dispatchers with do-block early-return (`return some _`) are peeled
guard-by-guard with `by_cases hg + rw [if_pos/if_neg] at h`, then
`simp only [Bind.bind, Except.bind, pure_bind]` reduces the surviving
`(throw _) >>= _` / `pure _ >>= _` shape.

`scanLoopIx_offset_monotonic` is stated as `s.tokens.size ≤ ts.tokens.size`
(not a cursor-comparison, since `scanLoopIx` returns a `TokenStream` and
not a state). It is proven by induction on fuel, chaining
`scanNextTokenIx_tokens_size_le` on each step. The stronger
*"every newly-emitted token's `start.offset ≥` initial cursor's offset"*
claim is deferred to Step 5b.2 (it requires per-helper bound proofs that
each leaf lemma's current `_offset_monotonic` statement does not carry). -/

/-! ### Preprocess

`scanNextTokenIx_preprocess` is `let-if-if-match` without a do-block, so
the R50 nested-`split` pattern applies directly. After `simp only at h`
zeta-reduces the four `let` shadowings (`s.skipToContentS`, `savedIndentSize`,
`{ unwindIndentsIx s.skipToContentS ... with needIndentCheck := false } | s`,
`saveSimpleKeyIx _`), the four conditional layers are:
(1) outer `if !hasMore` (true ⇒ `.ok none`, contradiction);
(2) inner-let `if !inFlow && needIndentCheck` (both arms continue);
(3) middle `if errCond` (true ⇒ `.error`, contradiction);
(4) `match peek?` (`none` ⇒ `.ok none` contradiction, `some c` ⇒ success).
The two surviving success paths share the same chain: the final cursor
is the post-`skipToContentS` cursor (unaffected by `unwindIndentsIx` /
`saveSimpleKeyIx`, both cursor-preserving), so `_offset_monotonic` chains
through `skipToContentS_offset_monotonic`. -/

theorem scanNextTokenIx_preprocess_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_preprocess s = .ok (some (s', c))) :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  unfold scanNextTokenIx_preprocess at h
  simp only at h
  split at h
  · simp at h
  · split at h
    all_goals
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hs, _⟩ := h
          subst hs
          show s.cursor.pos.offset ≤ _
          simp only [saveSimpleKeyIx_cursor, unwindIndentsIx_cursor]
          exact skipToContentS_offset_monotonic s

theorem scanNextTokenIx_preprocess_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_preprocess s = .ok (some (s', c))) :
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanNextTokenIx_preprocess at h
  simp only at h
  split at h
  · simp at h
  · split at h
    all_goals
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hs, _⟩ := h
          subst hs
          show s.tokens.size ≤ _
          rw [show s.tokens.size = s.skipToContentS.tokens.size from rfl]
          refine Nat.le_trans ?_ (saveSimpleKeyIx_tokens_size_le _)
          first
            | exact Nat.le_refl _
            | exact unwindIndentsIx_tokens_size_le _ _

/-! ### Structural dispatch

`scanNextTokenIx_dispatchStructural` is a `do`-block with two early-throw
guards and three early-return production branches. The early-return form
`if c then return v` desugars to a conditional that short-circuits the
remaining `do`-block. Each guard / production is peeled with
`by_cases hg + rw [if_pos/if_neg] at h`; the throw branches reduce to
`.error _` (contradicting `.ok _`) via `simp [Bind.bind, Except.bind]`,
the early-return branches reduce to `.ok (some _)` and chain through
the per-helper monotonicity. The default `return none` (no production
fired) contradicts `.ok (some s')` directly. -/

/-- Auxiliary: characterise the `.ok (some s')` output of
    `scanNextTokenIx_dispatchStructural`. Exactly one of three productions
    fires (DocumentStart, DocumentEnd, Directive).

    The proof is verbose because the do-block elaborates with `__do_jp`
    join points whose `simp` reduction is incomplete; we peel each guard
    explicitly with `by_cases + rw [if_pos / if_neg]` and use `cases hSDE :
    scanDocumentEndIx s` to step through the bind. -/
theorem scanNextTokenIx_dispatchStructural_ok_some_cases {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    s' = scanDocumentStartIx s ∨
    scanDocumentEndIx s = .ok s' ∨
    scanDirectiveIx s = .ok s' := by
  unfold scanNextTokenIx_dispatchStructural at h
  -- Peel guard 1 outer + inner (under-indent throw).
  by_cases hg1 :
      (s.inFlow && decide (s.currentIndent ≥ 0) &&
       decide ((s.cursor.pos.col : Int) ≤ s.currentIndent)) = true
  · rw [if_pos hg1] at h
    by_cases hg1' : (c != ']' && c != '}') = true
    · rw [if_pos hg1'] at h
      simp [Bind.bind, Except.bind] at h
    · rw [if_neg hg1'] at h
      -- Continue with productions
      by_cases hg2 : (s.cursor.pos.col == 0 && s.inFlow &&
                      (atDocumentStartIx s.cursor || atDocumentEndIx s.cursor)) = true
      · rw [if_pos hg2] at h
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      · rw [if_neg hg2] at h
        by_cases hg3 : (s.cursor.pos.col == 0 && atDocumentStartIx s.cursor) = true
        · rw [if_pos hg3] at h
          left
          show s' = _
          have := (Except.ok.injEq _ _).mp h
          exact ((Option.some.injEq _ _).mp this).symm
        · rw [if_neg hg3] at h
          by_cases hg4 : (s.cursor.pos.col == 0 && atDocumentEndIx s.cursor) = true
          · rw [if_pos hg4] at h
            right; left
            cases hSDE : scanDocumentEndIx s with
            | error e =>
              rw [hSDE] at h
              simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            | ok v =>
              rw [hSDE] at h
              simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
              exact congrArg Except.ok h
          · rw [if_neg hg4] at h
            by_cases hg5 : (c == '%' && s.cursor.pos.col == 0) = true
            · rw [if_pos hg5] at h
              right; right
              cases hSD : scanDirectiveIx s with
              | error e =>
                rw [hSD] at h
                simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
              | ok v =>
                rw [hSD] at h
                simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
                exact congrArg Except.ok h
            · rw [if_neg hg5] at h
              simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  · rw [if_neg hg1] at h
    by_cases hg2 : (s.cursor.pos.col == 0 && s.inFlow &&
                    (atDocumentStartIx s.cursor || atDocumentEndIx s.cursor)) = true
    · rw [if_pos hg2] at h
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    · rw [if_neg hg2] at h
      by_cases hg3 : (s.cursor.pos.col == 0 && atDocumentStartIx s.cursor) = true
      · rw [if_pos hg3] at h
        left
        show s' = _
        have := (Except.ok.injEq _ _).mp h
        exact ((Option.some.injEq _ _).mp this).symm
      · rw [if_neg hg3] at h
        by_cases hg4 : (s.cursor.pos.col == 0 && atDocumentEndIx s.cursor) = true
        · rw [if_pos hg4] at h
          right; left
          cases hSDE : scanDocumentEndIx s with
          | error e =>
            rw [hSDE] at h
            simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          | ok v =>
            rw [hSDE] at h
            simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            exact congrArg Except.ok h
        · rw [if_neg hg4] at h
          by_cases hg5 : (c == '%' && s.cursor.pos.col == 0) = true
          · rw [if_pos hg5] at h
            right; right
            cases hSD : scanDirectiveIx s with
            | error e =>
              rw [hSD] at h
              simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            | ok v =>
              rw [hSD] at h
              simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
              exact congrArg Except.ok h
          · rw [if_neg hg5] at h
            simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

theorem scanNextTokenIx_dispatchStructural_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  rcases scanNextTokenIx_dispatchStructural_ok_some_cases h with heq | hOk | hOk
  · subst heq
    exact scanDocumentStartIx_offset_monotonic s
  · exact scanDocumentEndIx_offset_monotonic hOk
  · exact scanDirectiveIx_offset_monotonic hOk

theorem scanNextTokenIx_dispatchStructural_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    s.tokens.size ≤ s'.tokens.size := by
  rcases scanNextTokenIx_dispatchStructural_ok_some_cases h with heq | hOk | hOk
  · subst heq
    exact scanDocumentStartIx_tokens_size_le s
  · exact scanDocumentEndIx_tokens_size_le hOk
  · exact scanDirectiveIx_tokens_size_le hOk

/-! ### Flow indicators dispatch

5 productions (`[`, `]`, `{`, `}`, `,`), each guarded by a character
match. The end-indicators (`]`, `}`, `,`) additionally throw when
`s.flowLevel == 0`. Same by_cases pattern as structural. -/

theorem scanNextTokenIx_dispatchFlowIndicators_ok_some_cases {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) :
    s' = scanFlowSequenceStartIx s ∨
    s' = scanFlowSequenceEndIx s ∨
    s' = scanFlowMappingStartIx s ∨
    s' = scanFlowMappingEndIx s ∨
    scanFlowEntryIx s = .ok s' := by
  unfold scanNextTokenIx_dispatchFlowIndicators at h
  by_cases hg1 : (c == '[') = true
  · rw [if_pos hg1] at h
    left
    show s' = _
    have hi := (Except.ok.injEq _ _).mp h
    exact ((Option.some.injEq _ _).mp hi).symm
  · rw [if_neg hg1] at h
    by_cases hg2 : (c == ']') = true
    · rw [if_pos hg2] at h
      by_cases hg2' : (s.flowLevel == 0) = true
      · rw [if_pos hg2'] at h
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      · rw [if_neg hg2'] at h
        right; left
        show s' = _
        have hi := (Except.ok.injEq _ _).mp h
        exact ((Option.some.injEq _ _).mp hi).symm
    · rw [if_neg hg2] at h
      by_cases hg3 : (c == '{') = true
      · rw [if_pos hg3] at h
        right; right; left
        show s' = _
        have hi := (Except.ok.injEq _ _).mp h
        exact ((Option.some.injEq _ _).mp hi).symm
      · rw [if_neg hg3] at h
        by_cases hg4 : (c == '}') = true
        · rw [if_pos hg4] at h
          by_cases hg4' : (s.flowLevel == 0) = true
          · rw [if_pos hg4'] at h
            simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          · rw [if_neg hg4'] at h
            right; right; right; left
            show s' = _
            have hi := (Except.ok.injEq _ _).mp h
            exact ((Option.some.injEq _ _).mp hi).symm
        · rw [if_neg hg4] at h
          by_cases hg5 : (c == ',') = true
          · rw [if_pos hg5] at h
            by_cases hg5' : (s.flowLevel == 0) = true
            · rw [if_pos hg5'] at h
              simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            · rw [if_neg hg5'] at h
              right; right; right; right
              cases hSFE : scanFlowEntryIx s with
              | error e =>
                rw [hSFE] at h
                simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
              | ok v =>
                rw [hSFE] at h
                simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
                exact congrArg Except.ok h
          · rw [if_neg hg5] at h
            simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

theorem scanNextTokenIx_dispatchFlowIndicators_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h with
    heq | heq | heq | heq | hOk
  · subst heq; exact scanFlowSequenceStartIx_offset_monotonic s
  · subst heq; exact scanFlowSequenceEndIx_offset_monotonic s
  · subst heq; exact scanFlowMappingStartIx_offset_monotonic s
  · subst heq; exact scanFlowMappingEndIx_offset_monotonic s
  · exact scanFlowEntryIx_offset_monotonic hOk

theorem scanNextTokenIx_dispatchFlowIndicators_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) :
    s.tokens.size ≤ s'.tokens.size := by
  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h with
    heq | heq | heq | heq | hOk
  · subst heq; exact scanFlowSequenceStartIx_tokens_size_le s
  · subst heq; exact scanFlowSequenceEndIx_tokens_size_le s
  · subst heq; exact scanFlowMappingStartIx_tokens_size_le s
  · subst heq; exact scanFlowMappingEndIx_tokens_size_le s
  · exact scanFlowEntryIx_tokens_size_le hOk

/-! ### Block indicators dispatch

3 productions (`-`, `?`, `:`) each guarded by a character-and-context
match; each binds through its `Except`-returning scanner. -/

theorem scanNextTokenIx_dispatchBlockIndicators_ok_some_cases {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    scanBlockEntryIx s = .ok s' ∨
    scanKeyIx s = .ok s' ∨
    scanValueIx s = .ok s' := by
  unfold scanNextTokenIx_dispatchBlockIndicators at h
  by_cases hg1 : (c == '-' && !s.inFlow && isBlockEntryCandidateIx s) = true
  · rw [if_pos hg1] at h
    left
    cases hBE : scanBlockEntryIx s with
    | error e =>
      rw [hBE] at h
      simp [Bind.bind, Except.bind] at h
    | ok v =>
      rw [hBE] at h
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      exact congrArg Except.ok h
  · rw [if_neg hg1] at h
    by_cases hg2 : (c == '?' && isKeyCandidateIx s) = true
    · rw [if_pos hg2] at h
      right; left
      cases hK : scanKeyIx s with
      | error e =>
        rw [hK] at h
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      | ok v =>
        rw [hK] at h
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        exact congrArg Except.ok h
    · rw [if_neg hg2] at h
      by_cases hg3 : (c == ':' && isValueCandidateIx s) = true
      · rw [if_pos hg3] at h
        right; right
        cases hV : scanValueIx s with
        | error e =>
          rw [hV] at h
          simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        | ok v =>
          rw [hV] at h
          simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          exact congrArg Except.ok h
      · rw [if_neg hg3] at h
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure] at h

theorem scanNextTokenIx_dispatchBlockIndicators_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h with hOk | hOk | hOk
  · exact scanBlockEntryIx_offset_monotonic hOk
  · exact scanKeyIx_offset_monotonic hOk
  · exact scanValueIx_offset_monotonic hOk

theorem scanNextTokenIx_dispatchBlockIndicators_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    s.tokens.size ≤ s'.tokens.size := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h with hOk | hOk | hOk
  · exact scanBlockEntryIx_tokens_size_le hOk
  · exact scanKeyIx_tokens_size_le hOk
  · exact scanValueIx_tokens_size_le hOk

/-! ### Content dispatch (scalars + node properties)

7 productions: `&`/`*` (anchor/alias via `scanAnchorOrAliasIx`), `!` (tag),
`|`/`>` (block scalar match), `"` / `'` (quoted scalar matches), and plain
scalar; with a final `unexpectedChar` throw fallback.

The block / quoted scalar productions are state-constructive on the
`some r` arm and throw on `none`; on the constructive arm the result is
`{ sAfter.emitAt startPos ... with simpleKeyAllowed := false }`. We
package the per-case monotonicity (cursor + tokens-size) as a conjunctive
helper, then derive each main theorem by `.1` / `.2`. -/

theorem scanNextTokenIx_dispatchContent_ok_monotonic {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchContent s c = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset ∧
    s.tokens.size ≤ s'.tokens.size := by
  unfold scanNextTokenIx_dispatchContent at h
  by_cases hg1 : (c == '&') = true
  · rw [if_pos hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h; cases h
    | ok v =>
      rw [hA] at h
      cases h
      exact ⟨scanAnchorOrAliasIx_offset_monotonic hA, scanAnchorOrAliasIx_tokens_size_le hA⟩
  · rw [if_neg hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    by_cases hg2 : (c == '*') = true
    · rw [if_pos hg2] at h
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h; cases h
      | ok v =>
        rw [hA] at h
        cases h
        exact ⟨scanAnchorOrAliasIx_offset_monotonic hA, scanAnchorOrAliasIx_tokens_size_le hA⟩
    · rw [if_neg hg2] at h
      by_cases hg3 : (c == '!') = true
      · rw [if_pos hg3] at h
        cases hT : scanTagIx s with
        | error e => rw [hT] at h; cases h
        | ok v =>
          rw [hT] at h
          cases h
          exact ⟨scanTagIx_offset_monotonic hT, scanTagIx_tokens_size_le hT⟩
      · rw [if_neg hg3] at h
        by_cases hg4 : (c == '|' || c == '>') = true
        · rw [if_pos hg4] at h
          -- Use split at h to handle the dependent match's hBS witness.
          split at h
          · rename_i r hBS
            cases h
            refine ⟨?_, ?_⟩
            · show s.cursor.pos.offset ≤ _
              simp only [emitAt_cursor]
              exact scanBlockScalarIx_offset_monotonic s.cursor _ hBS
            · show s.tokens.size ≤ _
              simp only [emitAt_tokens_size]
              exact Nat.le_succ _
          · cases h
        · rw [if_neg hg4] at h
          by_cases hg5 : (c == '"') = true
          · rw [if_pos hg5] at h
            split at h
            · rename_i r hDQ
              cases h
              refine ⟨?_, ?_⟩
              · show s.cursor.pos.offset ≤ _
                simp only [emitAt_cursor]
                exact Nat.le_of_lt (scanDoubleQuotedIx_offset_lt s.cursor hDQ)
              · show s.tokens.size ≤ _
                simp only [emitAt_tokens_size]
                exact Nat.le_succ _
            · cases h
          · rw [if_neg hg5] at h
            by_cases hg6 : (c == '\'') = true
            · rw [if_pos hg6] at h
              split at h
              · rename_i r hSQ
                cases h
                refine ⟨?_, ?_⟩
                · show s.cursor.pos.offset ≤ _
                  simp only [emitAt_cursor]
                  exact Nat.le_of_lt (scanSingleQuotedIx_offset_lt s.cursor hSQ)
                · show s.tokens.size ≤ _
                  simp only [emitAt_tokens_size]
                  exact Nat.le_succ _
              · cases h
            · rw [if_neg hg6] at h
              by_cases hg7 : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true
              · rw [if_pos hg7] at h
                cases h
                refine ⟨?_, ?_⟩
                · show s.cursor.pos.offset ≤ _
                  simp only [emitAt_cursor]
                  exact scanPlainScalarIx_offset_monotonic s.cursor s.inFlow _
                · show s.tokens.size ≤ _
                  simp only [emitAt_tokens_size]
                  exact Nat.le_succ _
              · rw [if_neg hg7] at h
                cases h

theorem scanNextTokenIx_dispatchContent_offset_monotonic {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchContent s c = .ok s') :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset :=
  (scanNextTokenIx_dispatchContent_ok_monotonic h).1

theorem scanNextTokenIx_dispatchContent_tokens_size_le {input : String}
    {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchContent s c = .ok s') :
    s.tokens.size ≤ s'.tokens.size :=
  (scanNextTokenIx_dispatchContent_ok_monotonic h).2

/-! ### Per-iteration `scanNextTokenIx`

Chains `preprocess` (advances cursor / grows tokens) → optional dispatcher
(structural/flow/block/content). The structure update
`{ s with allowDirectives := false, documentEverStarted := true }` and
`scanNextTokenIx_checkBlockFlowIndent` (returns `Except Unit`) preserve
both cursor and tokens; the dispatcher chains close via the per-helper
lemmas above. -/

theorem scanNextTokenIx_ok_some_monotonic {input : String}
    {s s' : ScannerStateIx input}
    (h : scanNextTokenIx s = .ok (some s')) :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset ∧
    s.tokens.size ≤ s'.tokens.size := by
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
      have hPpO := scanNextTokenIx_preprocess_offset_monotonic hPre
      have hPpT := scanNextTokenIx_preprocess_tokens_size_le hPre
      simp only at h
      cases hStr : scanNextTokenIx_dispatchStructural sp c with
      | error e => rw [hStr] at h; cases h
      | ok structRes =>
        rw [hStr] at h
        cases structRes with
        | some s'' =>
          cases h
          have hStrO := scanNextTokenIx_dispatchStructural_offset_monotonic hStr
          have hStrT := scanNextTokenIx_dispatchStructural_tokens_size_le hStr
          exact ⟨Nat.le_trans hPpO hStrO, Nat.le_trans hPpT hStrT⟩
        | none =>
          -- Branch on sp.allowDirectives. In both branches, the adjusted state
          -- `sadj` has cursor = sp.cursor and tokens = sp.tokens, so each
          -- dispatcher's monotonicity gives the chain via Nat.le_trans.
          suffices hChain : sp.cursor.pos.offset ≤ s'.cursor.pos.offset ∧
                            sp.tokens.size ≤ s'.tokens.size by
            exact ⟨Nat.le_trans hPpO hChain.1, Nat.le_trans hPpT hChain.2⟩
          by_cases hAD : sp.allowDirectives = true
          all_goals first
            | (rw [if_pos hAD] at h
               -- sadj := { sp with allowDirectives := false, documentEverStarted := true }
               -- cursor and tokens unchanged: prove via cases on each dispatcher
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
                     have hFO := scanNextTokenIx_dispatchFlowIndicators_offset_monotonic hFlow
                     have hFT := scanNextTokenIx_dispatchFlowIndicators_tokens_size_le hFlow
                     exact ⟨hFO, hFT⟩
                   | none =>
                     cases hBlk : scanNextTokenIx_dispatchBlockIndicators
                         { sp with allowDirectives := false, documentEverStarted := true } c with
                     | error e => rw [hBlk] at h; cases h
                     | ok blkRes =>
                       rw [hBlk] at h
                       cases blkRes with
                       | some _ =>
                         cases h
                         have hBO := scanNextTokenIx_dispatchBlockIndicators_offset_monotonic hBlk
                         have hBT := scanNextTokenIx_dispatchBlockIndicators_tokens_size_le hBlk
                         exact ⟨hBO, hBT⟩
                       | none =>
                         cases hCon : scanNextTokenIx_dispatchContent
                             { sp with allowDirectives := false, documentEverStarted := true } c with
                         | error e => rw [hCon] at h; cases h
                         | ok _ =>
                           rw [hCon] at h
                           cases h
                           have hCO := scanNextTokenIx_dispatchContent_offset_monotonic hCon
                           have hCT := scanNextTokenIx_dispatchContent_tokens_size_le hCon
                           exact ⟨hCO, hCT⟩)
            | (rw [if_neg hAD] at h
               -- sadj := sp; cursor and tokens are sp's
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
                     have hFO := scanNextTokenIx_dispatchFlowIndicators_offset_monotonic hFlow
                     have hFT := scanNextTokenIx_dispatchFlowIndicators_tokens_size_le hFlow
                     exact ⟨hFO, hFT⟩
                   | none =>
                     cases hBlk : scanNextTokenIx_dispatchBlockIndicators sp c with
                     | error e => rw [hBlk] at h; cases h
                     | ok blkRes =>
                       rw [hBlk] at h
                       cases blkRes with
                       | some _ =>
                         cases h
                         have hBO := scanNextTokenIx_dispatchBlockIndicators_offset_monotonic hBlk
                         have hBT := scanNextTokenIx_dispatchBlockIndicators_tokens_size_le hBlk
                         exact ⟨hBO, hBT⟩
                       | none =>
                         cases hCon : scanNextTokenIx_dispatchContent sp c with
                         | error e => rw [hCon] at h; cases h
                         | ok _ =>
                           rw [hCon] at h
                           cases h
                           have hCO := scanNextTokenIx_dispatchContent_offset_monotonic hCon
                           have hCT := scanNextTokenIx_dispatchContent_tokens_size_le hCon
                           exact ⟨hCO, hCT⟩)

theorem scanNextTokenIx_offset_monotonic {input : String}
    {s s' : ScannerStateIx input}
    (h : scanNextTokenIx s = .ok (some s')) :
    s.cursor.pos.offset ≤ s'.cursor.pos.offset :=
  (scanNextTokenIx_ok_some_monotonic h).1

theorem scanNextTokenIx_tokens_size_le {input : String}
    {s s' : ScannerStateIx input}
    (h : scanNextTokenIx s = .ok (some s')) :
    s.tokens.size ≤ s'.tokens.size :=
  (scanNextTokenIx_ok_some_monotonic h).2

/-! ### Fueled `scanLoopIx` token-stream growth

`scanLoopIx` returns a `TokenStream` (not a state), so the natural
claim is `s.tokens.size ≤ ts.size`: each loop iteration either
terminates with `unwindIndents + emit streamEnd` (grows tokens) or
recurses on a state whose tokens have grown via `scanNextTokenIx`. -/

theorem scanLoopIx_tokens_size_le {input : String}
    {s : ScannerStateIx input} {fuel : Nat} {ts : Indexed.TokenStream input}
    (h : scanLoopIx s fuel = .ok ts) :
    s.tokens.size ≤ ts.size := by
  induction fuel generalizing s with
  | zero => unfold scanLoopIx at h; cases h
  | succ fuel' ih =>
    unfold scanLoopIx at h
    cases hSc : scanNextTokenIx s with
    | error e => rw [hSc] at h; cases h
    | ok scRes =>
      rw [hSc] at h
      cases scRes with
      | none =>
        -- Terminal arm: nested ifs then `unwindIndentsIx + emit streamEnd`.
        by_cases hFL : s.flowLevel > 0
        · rw [if_pos hFL] at h; cases h
        · rw [if_neg hFL] at h
          by_cases hDS : (s.directivesPresent && !s.documentEverStarted) = true
          · rw [if_pos hDS] at h; cases h
          · rw [if_neg hDS] at h
            -- h : .ok ((unwindIndentsIx s (-1)).emit streamEnd).tokens = .ok ts
            cases h
            -- Goal: s.tokens.size ≤ ((unwindIndentsIx s (-1)).emit streamEnd).tokens.size
            show s.tokens.size ≤ _
            refine Nat.le_trans (unwindIndentsIx_tokens_size_le s (-1)) ?_
            simp
      | some s'' =>
        -- Recursive arm: chain via scanNextTokenIx_tokens_size_le + IH.
        have hStep := scanNextTokenIx_tokens_size_le hSc
        exact Nat.le_trans hStep (ih h)

end L4YAML.Scanner.Indexed
