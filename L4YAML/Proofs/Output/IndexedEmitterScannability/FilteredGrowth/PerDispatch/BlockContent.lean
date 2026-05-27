/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.Infra
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.StreamStart

/-! # `FilteredGrowth.PerDispatch.BlockContent` — Phase 3 Step
`6f.3b3.filteredgrowth.perdispatch.blockcontent`

**Sub-session 2 of `.perdispatch`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 6364–6757, ~395 LOC).

Per-dispatch-layer filtered growth lemmas for the **block-indicator**
(`-`/`?`/`:`) and **content** (`&`/`*`/`!`/`|`/`>`/`"`/`'`/plain)
dispatchers. The companion sub-session `.structflow` ships the
structural + flow-indicator dispatcher lemmas (legacy 6071–6362).

Ships:

  * **§1 `scanBlockEntry_filtered_growsIx`** — `≥ +1` for `-`
    (legacy 6368). Push-sequence-indent (monotone) then emit
    `.blockEntry` (the new token at the first new slot).
  * **§2 `scanKey_filtered_growsIx`** — `≥ +1` for `?` (legacy
    6389). Same skeleton with `pushMappingIndentIx` + emit `.key`.
  * **§3 `scanValue_filtered_growsIx`** — `≥ +1` for `:` (legacy
    6432). The only `_filtered_growsIx` consumer of
    `Array_setIfInBounds_filter_monoIx` (`.infra` §2): the
    `scanValuePrepareIx` placeholder-to-real overwrite path is
    filter-monotone (`≥ +0`), then the `.value` emit adds `+1`.
  * **§4 `dispatchBlockIndicators_filtered_growsIx`** — `≥ +1` for
    the block dispatcher (legacy 6515); `rcases` on the
    `_ok_some_cases` enumerator delegates to §1/§2/§3.
  * **§5 `dispatchContent_new_not_placeholderIx`** — the newly-added
    token at index `s.tokens.size` is non-`.placeholder` (legacy
    6539, the heavy one). Pattern-matches `dispatchContent`'s arms:
    `.anchor`/`.alias`/`.tag` emit inside the cursor-level scanner,
    `.scalar` (block/double/single/plain) emit at dispatch level
    via `emitAt`.
  * **§6 `dispatchContent_filtered_growsIx`** — `≥ +1` for the
    content dispatcher (legacy 6725); composes the exact `+1` raw
    growth, dispatch prefix preservation, and §5.

## Indexed simplification

The indexed `scanValuePrepareIx` overwrites placeholder slots via
`overwriteAtCursor` (a `TokenStream.setIfInBounds`), whose
`.tokens.tokens` field is the underlying `Array.setIfInBounds` by
`rfl` (`overwriteAtCursor_tokens_tokens` §0). The block / quoted /
plain scalars are *cursor-level* in the indexed substrate, so the
`.scalar` `emitAt` lives in `scanNextTokenIx_dispatchContent` itself
(mirroring the technique used in `FirstFiltered §3`): the new-token
claim reads the push shape off `emitAt` directly, with no per-scanner
`_adds_token` lemma. The anchor / alias / tag scanners emit
internally, so §5 delegates to the small private
`_new_not_placeholderIx` helpers (twins of the upstream
`_new_token_not_plain` / `_not_flow` lemmas).

The `TokenStream` ↔ `Array (IxToken)` defeq (Reflection 133) keeps
the bridge invisible; `omega` doesn't reduce by defeq, so the proofs
`change`/`show` between `.tokens.size` and `.tokens.tokens.size` at
the boundary.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth

open L4YAML
open L4YAML.Indexed
open L4YAML.CharPredicates
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.ScannerCorrectness
-- Selective open of the per-scanner lemma family living in
-- `L4YAML.Proofs.Indexed.ScannerPlainScalarValid` (a full `open` would
-- shadow `Scanner.Indexed.ScannerStateIx.emitAt_tokens_size` with an
-- ambiguous copy — see StructFlow).
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid (
  scanBlockEntryIx_preserves_prefix
  scanKeyIx_preserves_prefix
  scanValueClearKeyIx_tokens
  emit_preserves_tokens_at
  scanAnchorOrAliasIx_adds_one_token
  scanTagIx_adds_one_token)

variable {input : String}

/-! ## §0  Shape helpers -/

/-- `overwriteAtCursor`'s underlying token array is `Array.setIfInBounds`
    of a zero-width token at the saved cursor. By `rfl` through the
    `TokenStream.setIfInBounds` definition. -/
theorem overwriteAtCursor_tokens_tokens (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken) :
    (s.overwriteAtCursor i sk tok).tokens.tokens =
      s.tokens.tokens.setIfInBounds i
        (IxToken.mk' (input := input) sk.pos tok sk.pos (Nat.le_refl _) sk.posBound) := rfl

/-- `scanBlockEntryIx`'s `tokens` field equals
    `((if !inFlow then pushSequenceIndentIx else id).emit .blockEntry)`'s
    tokens on the successful (non-tab-throw) branch. -/
theorem scanBlockEntryIx_tokens_eq {s s' : ScannerStateIx input}
    (h : scanBlockEntryIx s = .ok s') :
    s'.tokens =
      ((if !s.inFlow then pushSequenceIndentIx s s.cursor.pos.col else s).emit
        YamlToken.blockEntry).tokens := by
  unfold scanBlockEntryIx at h
  by_cases hi : (!s.inFlow) = true
  · rw [if_pos hi] at h
    by_cases ht : s.hasTabInPrecedingWhitespace = true
    · rw [if_pos ht] at h; simp [Bind.bind, Except.bind] at h
    · rw [if_neg ht] at h
      simp only [pure_bind] at h
      rw [if_pos hi] at h
      simp only [Except.ok.injEq] at h
      subst h
      simp only [if_pos hi, advance_tokens]
  · rw [if_neg hi] at h
    simp only [pure_bind] at h
    rw [if_neg hi] at h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [if_neg hi, advance_tokens]

/-- `scanKeyIx`'s `tokens` field equals
    `((if !inFlow then pushMappingIndentIx else id).emit .key)`'s tokens
    on every successful branch (the trailing tab-after-`?` probe is a
    guard that does not touch tokens). -/
theorem scanKeyIx_tokens_eq {s s' : ScannerStateIx input}
    (h : scanKeyIx s = .ok s') :
    s'.tokens =
      ((if !s.inFlow then pushMappingIndentIx s s.cursor.pos.col else s).emit
        YamlToken.key).tokens := by
  unfold scanKeyIx at h
  by_cases hi : (!s.inFlow) = true
  · simp only [if_pos hi, advance_inFlow, emit_inFlow, pushMappingIndentIx_inFlow] at h
    split at h
    · simp [Bind.bind, Except.bind] at h
    · simp only [pure_bind, Except.ok.injEq] at h
      subst h
      simp only [if_pos hi, advance_tokens]
  · simp only [if_neg hi, advance_inFlow, emit_inFlow] at h
    simp only [pure_bind, Except.ok.injEq] at h
    subst h
    simp only [if_neg hi, advance_tokens]

/-- `scanValuePrepareIx` is filter-monotone: every branch either leaves
    the token array unchanged, overwrites placeholder slots with
    non-`.placeholder` tokens (`overwriteAtCursor` ↦
    `Array_setIfInBounds_filter_monoIx`), or emits a
    `.blockMappingStart` (the deferred-mapping-start case). -/
theorem scanValuePrepareIx_filtered_monoIx (s : ScannerStateIx input) :
    ((scanValuePrepareIx s).tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
      (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
  unfold scanValuePrepareIx
  split
  · -- simpleKey.possible
    split
    · -- !inFlow
      split
      · -- col > currentIndent: two overwriteAtCursor (.blockMappingStart, .key)
        dsimp only []
        rw [overwriteAtCursor_tokens_tokens, overwriteAtCursor_tokens_tokens]
        have h1 := Array_setIfInBounds_filter_monoIx s.tokens.tokens
          s.simpleKey.tokenIndex
          (IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.blockMappingStart
            s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound)
          (fun t : IxToken input => t.token != .placeholder) (by simp [IxToken.mk'])
        have h2 := Array_setIfInBounds_filter_monoIx
          (s.tokens.tokens.setIfInBounds s.simpleKey.tokenIndex
            (IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.blockMappingStart
              s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound))
          (s.simpleKey.tokenIndex + 1)
          (IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.key
            s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound)
          (fun t : IxToken input => t.token != .placeholder) (by simp [IxToken.mk'])
        omega
      · -- col ≤ currentIndent: one overwriteAtCursor (.key)
        dsimp only []
        rw [overwriteAtCursor_tokens_tokens]
        have := Array_setIfInBounds_filter_monoIx s.tokens.tokens
          (s.simpleKey.tokenIndex + 1)
          (IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.key
            s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound)
          (fun t : IxToken input => t.token != .placeholder) (by simp [IxToken.mk'])
        omega
    · -- inFlow: one overwriteAtCursor (.key)
      dsimp only []
      rw [overwriteAtCursor_tokens_tokens]
      have := Array_setIfInBounds_filter_monoIx s.tokens.tokens
        (s.simpleKey.tokenIndex + 1)
        (IxToken.mk' (input := input) s.simpleKey.cursor.pos YamlToken.key
          s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound)
        (fun t : IxToken input => t.token != .placeholder) (by simp [IxToken.mk'])
      omega
  · split
    · -- explicitKeyLine.isSome: record update only, tokens unchanged
      dsimp only []; omega
    · split
      · -- !inFlow: pushMappingIndentIx (emits .blockMappingStart, monotone)
        unfold pushMappingIndentIx
        split
        · -- col > currentIndent: emit .blockMappingStart
          dsimp only []
          have h_grow := filtered_grows_of_extended_prefixIx s.tokens.tokens
            (s.emit YamlToken.blockMappingStart).tokens.tokens
            (fun t => t.token != .placeholder)
            (by rw [emit_tokens_pushIx, Array.size_push]; omega)
            (fun i hi => emit_preserves_tokens_at s YamlToken.blockMappingStart i hi)
            (by simp [emit_tokens_pushIx, IxToken.mk'])
          omega
        · -- col ≤ currentIndent: identity
          omega
      · -- inFlow: identity
        omega

/-! ## §1  `scanBlockEntry_filtered_growsIx` (legacy 6368) -/

theorem scanBlockEntry_filtered_growsIx {s s' : ScannerStateIx input}
    (h : scanBlockEntryIx s = .ok s') :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
      (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  have h_base_sz : s.tokens.tokens.size ≤
      (if !s.inFlow then pushSequenceIndentIx s s.cursor.pos.col else s).tokens.tokens.size := by
    split
    · exact pushSequenceIndentIx_tokens_size_le s s.cursor.pos.col
    · exact Nat.le_refl _
  have h_arr := congrArg Indexed.TokenStream.tokens (scanBlockEntryIx_tokens_eq h)
  rw [emit_tokens_pushIx] at h_arr
  refine filtered_grows_of_any_newIx s.tokens.tokens s'.tokens.tokens
    (fun t => t.token != .placeholder) ?_ ?_
    (if !s.inFlow then pushSequenceIndentIx s s.cursor.pos.col else s).tokens.tokens.size
    ?_ ?_ ?_
  · rw [h_arr, Array.size_push]; omega
  · intro i hi; exact scanBlockEntryIx_preserves_prefix s s' h i hi
  · exact h_base_sz
  · rw [h_arr, Array.size_push]; omega
  · simp only [h_arr, Array.getElem_push_eq, IxToken.mk']; rfl

/-! ## §2  `scanKey_filtered_growsIx` (legacy 6389) -/

theorem scanKey_filtered_growsIx {s s' : ScannerStateIx input}
    (h : scanKeyIx s = .ok s') :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
      (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  have h_base_sz : s.tokens.tokens.size ≤
      (if !s.inFlow then pushMappingIndentIx s s.cursor.pos.col else s).tokens.tokens.size := by
    split
    · exact pushMappingIndentIx_tokens_size_le s s.cursor.pos.col
    · exact Nat.le_refl _
  have h_arr := congrArg Indexed.TokenStream.tokens (scanKeyIx_tokens_eq h)
  rw [emit_tokens_pushIx] at h_arr
  refine filtered_grows_of_any_newIx s.tokens.tokens s'.tokens.tokens
    (fun t => t.token != .placeholder) ?_ ?_
    (if !s.inFlow then pushMappingIndentIx s s.cursor.pos.col else s).tokens.tokens.size
    ?_ ?_ ?_
  · rw [h_arr, Array.size_push]; omega
  · intro i hi; exact scanKeyIx_preserves_prefix s s' h i hi
  · exact h_base_sz
  · rw [h_arr, Array.size_push]; omega
  · simp only [h_arr, Array.getElem_push_eq, IxToken.mk']; rfl

/-! ## §3  `scanValue_filtered_growsIx` (legacy 6432) -/

set_option maxHeartbeats 400000 in
theorem scanValue_filtered_growsIx {s s' : ScannerStateIx input}
    (h : scanValueIx s = .ok s') :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
      (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  unfold scanValueIx at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h                                                    -- validate threw
  · split at h
    · cases h                                                  -- tab-check threw
    · simp only [Except.ok.injEq] at h
      subst h
      -- advance + record-update preserve tokens; reduce to the emit form.
      show (((scanValuePrepareIx (scanValueClearKeyIx s)).emit YamlToken.value).tokens.tokens.filter
              (fun t => t.token != .placeholder)).size ≥
            (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1
      -- Step 1: the `.value` emit adds one non-`.placeholder`.
      have h_emit :=
        filtered_grows_of_extended_prefixIx
          (scanValuePrepareIx (scanValueClearKeyIx s)).tokens.tokens
          ((scanValuePrepareIx (scanValueClearKeyIx s)).emit YamlToken.value).tokens.tokens
          (fun t => t.token != .placeholder)
          (by rw [emit_tokens_pushIx, Array.size_push]; omega)
          (fun i hi =>
            emit_preserves_tokens_at (scanValuePrepareIx (scanValueClearKeyIx s))
              YamlToken.value i hi)
          (by simp [emit_tokens_pushIx, IxToken.mk'])
      -- Step 2: `scanValuePrepareIx` is filter-monotone; `scanValueClearKeyIx`
      -- leaves tokens untouched.
      have h_ck : (scanValueClearKeyIx s).tokens.tokens = s.tokens.tokens :=
        congrArg Indexed.TokenStream.tokens (scanValueClearKeyIx_tokens s)
      have h_prep := scanValuePrepareIx_filtered_monoIx (scanValueClearKeyIx s)
      rw [h_ck] at h_prep
      omega

/-! ## §4  `dispatchBlockIndicators_filtered_growsIx` (legacy 6515) -/

theorem dispatchBlockIndicators_filtered_growsIx {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
      (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h with hOk | hOk | hOk
  · exact scanBlockEntry_filtered_growsIx hOk
  · exact scanKey_filtered_growsIx hOk
  · exact scanValue_filtered_growsIx hOk

/-! ## §5  `dispatchContent_new_not_placeholderIx` (legacy 6539)

The new token added by each content scanner is non-`.placeholder`.
For `.anchor`/`.alias`/`.tag` the emit lives inside the scanner
(small private helpers); for the four scalar styles the `emitAt`
lives in `scanNextTokenIx_dispatchContent` itself, so the proof reads
the `.scalar` push shape off the reduced dispatch branch. -/

/-- The anchor/alias scanner's new token at `s.tokens.size` is
    `.anchor`/`.alias` — never `.placeholder`. Twin of the upstream
    `scanAnchorOrAliasIx_new_token_not_plain`. -/
theorem scanAnchorOrAliasIx_new_not_placeholderIx (s : ScannerStateIx input)
    (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (hj : s.tokens.tokens.size < s'.tokens.tokens.size) :
    (s'.tokens.tokens[s.tokens.tokens.size]'hj).token ≠ YamlToken.placeholder := by
  unfold scanAnchorOrAliasIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · simp at h_ok
  · simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show (((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
            rw [Array.size_push]; omega)) : IxToken input).token ≠ _
    simp only [Array.getElem_push_eq, IxToken.mk']
    split <;> (intro hpl; cases hpl)

/-- The tag scanner's new token at `s.tokens.size` is `.tag _ _` —
    never `.placeholder`. Twin of `scanTagIx_new_token_not_plain`. -/
theorem scanTagIx_new_not_placeholderIx (s : ScannerStateIx input)
    (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s')
    (hj : s.tokens.tokens.size < s'.tokens.tokens.size) :
    (s'.tokens.tokens[s.tokens.tokens.size]'hj).token ≠ YamlToken.placeholder := by
  unfold scanTagIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · -- some '<' (verbatim)
    split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        show (((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
                rw [Array.size_push]; omega)) : IxToken input).token ≠ _
        simp only [Array.getElem_push_eq, IxToken.mk']
        intro hpl; cases hpl
  · -- some '!' (secondary)
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    show (((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
            rw [Array.size_push]; omega)) : IxToken input).token ≠ _
    simp only [Array.getElem_push_eq, IxToken.mk']
    intro hpl; cases hpl
  · -- default (named/primary)
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    show (((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
            rw [Array.size_push]; omega)) : IxToken input).token ≠ _
    simp only [Array.getElem_push_eq, IxToken.mk']
    intro hpl; cases hpl

set_option maxHeartbeats 1600000 in
theorem dispatchContent_new_not_placeholderIx {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchContent s c = .ok s')
    (h_strict : s'.tokens.tokens.size ≥ s.tokens.tokens.size + 1) :
    (s'.tokens.tokens[s.tokens.tokens.size]'(by omega)).token ≠ YamlToken.placeholder := by
  unfold scanNextTokenIx_dispatchContent at h
  by_cases hg1 : (c == '&') = true
  · rw [if_pos hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h; cases h
    | ok v =>
      rw [hA] at h; simp only [Except.ok.injEq] at h; subst h
      exact scanAnchorOrAliasIx_new_not_placeholderIx s true v hA (by omega)
  · rw [if_neg hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    by_cases hg2 : (c == '*') = true
    · rw [if_pos hg2] at h
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h; cases h
      | ok v =>
        rw [hA] at h; simp only [Except.ok.injEq] at h; subst h
        exact scanAnchorOrAliasIx_new_not_placeholderIx s false v hA (by omega)
    · rw [if_neg hg2] at h
      by_cases hg3 : (c == '!') = true
      · rw [if_pos hg3] at h
        cases hT : scanTagIx s with
        | error e => rw [hT] at h; cases h
        | ok v =>
          rw [hT] at h; simp only [Except.ok.injEq] at h; subst h
          exact scanTagIx_new_not_placeholderIx s v hT (by omega)
      · rw [if_neg hg3] at h
        by_cases hg4 : (c == '|' || c == '>') = true
        · rw [if_pos hg4] at h
          split at h
          · rename_i r hBS
            cases h
            intro hpl
            simp only [ScannerStateIx.emitAt, IxToken.mk', Indexed.TokenStream.push,
                       Array.getElem_push_eq] at hpl
            contradiction
          · cases h
        · rw [if_neg hg4] at h
          by_cases hg5 : (c == '"') = true
          · rw [if_pos hg5] at h
            split at h
            · rename_i r hDQ
              cases h
              intro hpl
              simp only [ScannerStateIx.emitAt, IxToken.mk', Indexed.TokenStream.push,
                         Array.getElem_push_eq] at hpl
              contradiction
            · cases h
          · rw [if_neg hg5] at h
            by_cases hg6 : (c == '\'') = true
            · rw [if_pos hg6] at h
              split at h
              · rename_i r hSQ
                cases h
                intro hpl
                simp only [ScannerStateIx.emitAt, IxToken.mk', Indexed.TokenStream.push,
                           Array.getElem_push_eq] at hpl
                contradiction
              · cases h
            · rw [if_neg hg6] at h
              by_cases hg7 : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true
              · rw [if_pos hg7] at h
                cases h
                intro hpl
                simp only [ScannerStateIx.emitAt, IxToken.mk', Indexed.TokenStream.push,
                           Array.getElem_push_eq] at hpl
                contradiction
              · rw [if_neg hg7] at h
                cases h

/-! ## §6  `dispatchContent_filtered_growsIx` (legacy 6725)

The content dispatcher always adds exactly one token, the dispatch
prefix is preserved, and the new token is non-`.placeholder` (§5). -/

set_option maxHeartbeats 1600000 in
/-- `scanNextTokenIx_dispatchContent` adds exactly one token across all
    seven productions. -/
theorem dispatchContent_adds_one_tokenIx {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchContent s c = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanNextTokenIx_dispatchContent at h
  by_cases hg1 : (c == '&') = true
  · rw [if_pos hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h; cases h
    | ok v =>
      rw [hA] at h; simp only [Except.ok.injEq] at h; subst h
      exact scanAnchorOrAliasIx_adds_one_token s true v hA
  · rw [if_neg hg1] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    by_cases hg2 : (c == '*') = true
    · rw [if_pos hg2] at h
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h; cases h
      | ok v =>
        rw [hA] at h; simp only [Except.ok.injEq] at h; subst h
        exact scanAnchorOrAliasIx_adds_one_token s false v hA
    · rw [if_neg hg2] at h
      by_cases hg3 : (c == '!') = true
      · rw [if_pos hg3] at h
        cases hT : scanTagIx s with
        | error e => rw [hT] at h; cases h
        | ok v =>
          rw [hT] at h; simp only [Except.ok.injEq] at h; subst h
          exact scanTagIx_adds_one_token s v hT
      · rw [if_neg hg3] at h
        by_cases hg4 : (c == '|' || c == '>') = true
        · rw [if_pos hg4] at h
          split at h
          · rename_i r hBS; cases h; simp only [emitAt_tokens_size]
          · cases h
        · rw [if_neg hg4] at h
          by_cases hg5 : (c == '"') = true
          · rw [if_pos hg5] at h
            split at h
            · rename_i r hDQ; cases h; simp only [emitAt_tokens_size]
            · cases h
          · rw [if_neg hg5] at h
            by_cases hg6 : (c == '\'') = true
            · rw [if_pos hg6] at h
              split at h
              · rename_i r hSQ; cases h; simp only [emitAt_tokens_size]
              · cases h
            · rw [if_neg hg6] at h
              by_cases hg7 : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true
              · rw [if_pos hg7] at h; cases h; simp only [emitAt_tokens_size]
              · rw [if_neg hg7] at h; cases h

theorem dispatchContent_filtered_growsIx {s s' : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_dispatchContent s c = .ok s') :
    (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
      (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size + 1 := by
  have h_strict : s'.tokens.tokens.size ≥ s.tokens.tokens.size + 1 := by
    have h_one := dispatchContent_adds_one_tokenIx h
    show s'.tokens.size ≥ s.tokens.size + 1
    omega
  refine filtered_grows_of_any_newIx s.tokens.tokens s'.tokens.tokens
    (fun t => t.token != .placeholder) h_strict ?_ s.tokens.tokens.size
    (Nat.le_refl _) (by omega) ?_
  · intro i hi
    exact scanNextTokenIx_dispatchContent_preserves_prefix s s' c h i hi
  · simp only [bne_iff_ne]
    exact dispatchContent_new_not_placeholderIx h h_strict

end L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth
