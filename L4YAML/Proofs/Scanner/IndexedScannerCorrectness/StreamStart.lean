/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.Basic

/-! # `IndexedScannerCorrectness.StreamStart` — §7

`SimpleKeyAboveIx` mono-chain + `scanIx_first_is_streamStart` —
discharges the `scanIx_first_is_streamStart_axiom` staging axiom
exposed in `Basic.lean`. Includes the §7.10 composite
`scanIx_valid_token_stream` (which still references
`scanIx_positions_ordered_axiom` for now — discharged in
`OrderedLoop.lean`).

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

/-! ## §7  `SimpleKeyAboveIx` and `scanIx_first_is_streamStart`

Discharges the §6.4 staging axiom `scanIx_first_is_streamStart_axiom`
by porting the legacy `SimpleKeyAbove` invariant and the chain
`scanLoop_preserves_tokens` from
`Proofs/Scanner/ScannerCorrectness.lean:6175–6401`.

### Strategy

`overwriteAtCursor i sk tok` is the *only* operation in the indexed
scanner that mutates an existing slot in `tokens.tokens` (everything
else only `push`es). It is invoked from `scanValuePrepareIx` at
positions `s.simpleKey.tokenIndex` and `s.simpleKey.tokenIndex + 1`.
Therefore, if every simple key (current or stacked) has
`tokenIndex ≥ n`, then no `overwriteAtCursor` writes below index `n`,
so the prefix below `n` is preserved through `scanLoopIx`. With
`n = 1`, that prefix is exactly `[streamStart]`.

The composition mirrors the §12l `AllKeysPlaceholderInvIx`
dispatcher chain in `IndexedScannerPlainScalarValid.lean`: the
per-helper `_preserves_simpleKey` / `_preserves_simpleKeyStack` /
`_clears_simpleKey` / `_simpleKey_restored` / `_stack_pushed` /
`_stack_popped` facts compose with `_preserves_prefix` to maintain
`SimpleKeyAboveIx`. Most helpers preserve the *entire* prefix
unconditionally (`emit`-only); only `scanValueIx` requires the
`tokenIndex ≥ n` bound (it calls `scanValuePrepareIx`). -/

/-! ### §7.1  Definition -/

/-- Simple-key invariant: every simple key (current or stacked) with
    `possible = true` has `tokenIndex ≥ n`. Indexed twin of legacy
    `SimpleKeyAbove` (`Proofs/Scanner/ScannerCorrectness.lean:81`).

    `SimpleKeyAboveIx` does not depend on `s.tokens` directly, only on
    `s.simpleKey` and `s.simpleKeyStack` — so mono / cleared / restored
    transfers are by destructured projection (no `tokens` precondition
    required). The `n ≤ s.tokens.size` precondition is threaded
    separately at the call sites that need it (`saveSimpleKeyIx` is
    the only operation that bumps `tokenIndex` from `tokens.size`). -/
def SimpleKeyAboveIx {input : String} (s : ScannerStateIx input) (n : Nat) : Prop :=
  (s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n) ∧
  (∀ j (hj : j < s.simpleKeyStack.size),
    (s.simpleKeyStack[j]'hj).possible = true → (s.simpleKeyStack[j]'hj).tokenIndex ≥ n)

/-! ### §7.2  Mono helpers

`SimpleKeyAboveIx_mono` covers any state transition where `simpleKey`
and `simpleKeyStack` are both unchanged (only `tokens`, `cursor`, or
flag fields differ). `_of_cleared_mono` covers transitions where
`simpleKey.possible` becomes `false` and the stack is unchanged.
`_flowStart` / `_flowEnd` cover the flow-collection bracket
transitions that push/pop the stack. -/

theorem SimpleKeyAboveIx_mono {input : String} (s s' : ScannerStateIx input) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack) :
    SimpleKeyAboveIx s' n := by
  refine ⟨fun h_poss => ?_, fun j hj h_poss_j => ?_⟩
  · rw [h_sk] at h_poss ⊢; exact h_inv.1 h_poss
  · have hj' : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
    have h_get : (s'.simpleKeyStack[j]'hj) = (s.simpleKeyStack[j]'hj') := by simp [h_stack]
    rw [h_get] at h_poss_j ⊢
    exact h_inv.2 j hj' h_poss_j

theorem SimpleKeyAboveIx_of_cleared_mono {input : String} (s s' : ScannerStateIx input) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_cleared : s'.simpleKey.possible = false)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack) :
    SimpleKeyAboveIx s' n := by
  refine ⟨fun h_poss => absurd h_poss (by simp [h_cleared]), fun j hj h_poss_j => ?_⟩
  have hj' : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
  have h_get : (s'.simpleKeyStack[j]'hj) = (s.simpleKeyStack[j]'hj') := by simp [h_stack]
  rw [h_get] at h_poss_j ⊢
  exact h_inv.2 j hj' h_poss_j

/-- Flow start (`[`, `{`) clears current key and pushes old key onto
    the stack — both invariants transfer. -/
theorem SimpleKeyAboveIx_flowStart {input : String} (s s' : ScannerStateIx input) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_cleared : s'.simpleKey.possible = false)
    (h_pushed : s'.simpleKeyStack = s.simpleKeyStack.push s.simpleKey) :
    SimpleKeyAboveIx s' n := by
  refine ⟨fun h_poss => absurd h_poss (by simp [h_cleared]), fun j hj h_poss_j => ?_⟩
  have hj_sz : j < s.simpleKeyStack.size + 1 := by
    rw [h_pushed, Array.size_push] at hj; exact hj
  have hg_j : s'.simpleKeyStack[j]'hj =
      (s.simpleKeyStack.push s.simpleKey)[j]'(by rw [Array.size_push]; exact hj_sz) := by
    simp [h_pushed]
  rw [hg_j] at h_poss_j ⊢
  by_cases hlt : j < s.simpleKeyStack.size
  · rw [Array.getElem_push_lt hlt] at h_poss_j ⊢
    exact h_inv.2 j hlt h_poss_j
  · have hj_eq : j = s.simpleKeyStack.size := by omega
    subst hj_eq
    rw [Array.getElem_push_eq] at h_poss_j ⊢
    exact h_inv.1 h_poss_j

/-- Flow end (`]`, `}`) restores current key from stack top and pops.
    The restored key was on the stack, so its invariant was already
    established; the popped stack is a prefix of the old stack. -/
theorem SimpleKeyAboveIx_flowEnd {input : String} (s s' : ScannerStateIx input) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_restored : s'.simpleKey =
      s.simpleKeyStack.back?.getD { cursor := IxCursor.start input })
    (h_popped : s'.simpleKeyStack = s.simpleKeyStack.pop) :
    SimpleKeyAboveIx s' n := by
  refine ⟨fun h_poss => ?_, fun j hj h_poss_j => ?_⟩
  · rw [h_restored] at h_poss ⊢
    by_cases h_size : s.simpleKeyStack.size > 0
    · have h_bound : s.simpleKeyStack.size - 1 < s.simpleKeyStack.size := by omega
      have h_get_back :
          (s.simpleKeyStack.back?.getD { cursor := IxCursor.start input }) =
          s.simpleKeyStack[s.simpleKeyStack.size - 1]'h_bound := by
        simp [Array.back?, h_bound]
      rw [h_get_back] at h_poss ⊢
      exact h_inv.2 (s.simpleKeyStack.size - 1) h_bound h_poss
    · have h_empty : s.simpleKeyStack.size = 0 := by omega
      simp [Array.back?, h_empty] at h_poss
  · have hj' : j < s.simpleKeyStack.size := by
      simp [h_popped, Array.size_pop] at hj; omega
    have hg_j : s'.simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj' := by
      simp [h_popped, Array.getElem_pop]
    rw [hg_j] at h_poss_j ⊢
    exact h_inv.2 j hj' h_poss_j

/-! ### §7.3  `saveSimpleKeyIx` maintains `SimpleKeyAboveIx`

`saveSimpleKeyIx` either returns `s` unchanged (case 1 of
`saveSimpleKeyIx_state_cases`) or pushes two placeholder tokens and
sets the new simple key to `{ possible := true, tokenIndex :=
s.tokens.size, ... }` (case 2). In the latter case,
`tokens.size ≥ n` (precondition) guarantees the new key's
`tokenIndex ≥ n`, and the stack is unchanged (`emit`-only). -/

theorem saveSimpleKeyIx_maintains_SimpleKeyAboveIx {input : String}
    (s : ScannerStateIx input) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n) :
    SimpleKeyAboveIx (saveSimpleKeyIx s) n := by
  rcases saveSimpleKeyIx_state_cases s with h_eq | h_eq
  · rw [h_eq]; exact h_inv
  · rw [h_eq]
    refine ⟨fun _h_poss => ?_, fun j hj h_poss_j => ?_⟩
    · -- new simpleKey.tokenIndex = s.tokens.size ≥ n
      exact h_n
    · -- stack unchanged: two emits, both `emit_preserves_simpleKeyStack`
      have h_stack_eq :
          ({ (s.emit YamlToken.placeholder).emit YamlToken.placeholder with
              simpleKey := { possible := true, tokenIndex := s.tokens.size,
                             cursor := ((s.emit YamlToken.placeholder).emit
                               YamlToken.placeholder).cursor,
                             endLine := ((s.emit YamlToken.placeholder).emit
                               YamlToken.placeholder).cursor.pos.line } }
                : ScannerStateIx input).simpleKeyStack = s.simpleKeyStack := by
        show ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack =
          s.simpleKeyStack
        rw [emit_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]
      have hj_s : j < s.simpleKeyStack.size := by rw [← h_stack_eq]; exact hj
      have h_get :
          ({ (s.emit YamlToken.placeholder).emit YamlToken.placeholder with
              simpleKey := { possible := true, tokenIndex := s.tokens.size,
                             cursor := ((s.emit YamlToken.placeholder).emit
                               YamlToken.placeholder).cursor,
                             endLine := ((s.emit YamlToken.placeholder).emit
                               YamlToken.placeholder).cursor.pos.line } }
                : ScannerStateIx input).simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj_s := by
        simp
      rw [h_get] at h_poss_j ⊢
      exact h_inv.2 j hj_s h_poss_j

/-! ### §7.4  Preprocess maintains `SimpleKeyAboveIx`

`scanNextTokenIx_preprocess` does: `skipToContentS` → optional
`unwindIndentsIx` (under `needIndentCheck`) → `saveSimpleKeyIx`.
None of `skipToContentS` / `unwindIndentsIx` touch `simpleKey` or
`simpleKeyStack` (mono case); `saveSimpleKeyIx` requires the
`n ≤ tokens.size` bound, which is monotone through the preceding
steps. -/

theorem scanNextTokenIx_preprocess_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_pre : scanNextTokenIx_preprocess s = .ok (some (s', c)))
    (h_inv : SimpleKeyAboveIx s n) :
    SimpleKeyAboveIx s' n := by
  have h_inv_skip : SimpleKeyAboveIx s.skipToContentS n :=
    SimpleKeyAboveIx_mono s s.skipToContentS n h_inv
      (skipToContentS_preserves_simpleKey s) (skipToContentS_preserves_simpleKeyStack s)
  have h_n_skip : n ≤ s.skipToContentS.tokens.size := by
    rw [show s.skipToContentS.tokens.size = s.tokens.size from by simp [skipToContentS_tokens]]
    exact h_n
  unfold scanNextTokenIx_preprocess at h_pre
  simp only at h_pre
  split at h_pre
  · simp at h_pre
  · split at h_pre
    · -- with indent check
      have h_unwind_sk :
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).simpleKey =
          s.skipToContentS.simpleKey := unwindIndentsIx_preserves_simpleKey _ _
      have h_unwind_stack :
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).simpleKeyStack =
          s.skipToContentS.simpleKeyStack := unwindIndentsIx_preserves_simpleKeyStack _ _
      have h_unwind_mono :
          s.skipToContentS.tokens.size ≤
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).tokens.size :=
        unwindIndentsIx_tokens_size_le _ _
      have h_inv_unwind : SimpleKeyAboveIx
          { unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
              needIndentCheck := false } n :=
        SimpleKeyAboveIx_mono s.skipToContentS _ n h_inv_skip h_unwind_sk h_unwind_stack
      have h_n_unwind : n ≤
          ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
              needIndentCheck := false } : ScannerStateIx input).tokens.size := by
        show n ≤ (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).tokens.size
        omega
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          exact saveSimpleKeyIx_maintains_SimpleKeyAboveIx _ n h_n_unwind h_inv_unwind
    · -- without indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          exact saveSimpleKeyIx_maintains_SimpleKeyAboveIx _ n h_n_skip h_inv_skip

/-! ### §7.5  Sub-dispatcher maintains lemmas

Each of the four `scanNextTokenIx_dispatch*` sub-dispatchers preserves
`SimpleKeyAboveIx` via the case-enumeration theorems in
`Proofs/Scanner/IndexedDispatch.lean` and the per-helper
`_preserves_simpleKey` / `_clears_simpleKey` / `_simpleKey_restored` /
`_stack_pushed` / `_stack_popped` facts in `IndexedScannerPlainScalarValid`. -/

theorem scanNextTokenIx_dispatchStructural_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    SimpleKeyAboveIx s' n := by
  rcases scanNextTokenIx_dispatchStructural_ok_some_cases h_ok with heq | hOk | hOk
  · subst heq
    exact SimpleKeyAboveIx_of_cleared_mono s _ n h_inv
      (scanDocumentStartIx_clears_simpleKey s)
      (scanDocumentStartIx_preserves_simpleKeyStack s)
  · exact SimpleKeyAboveIx_of_cleared_mono s _ n h_inv
      (scanDocumentEndIx_clears_simpleKey s s' hOk)
      (scanDocumentEndIx_preserves_simpleKeyStack s s' hOk)
  · exact SimpleKeyAboveIx_mono s _ n h_inv
      (scanDirectiveIx_preserves_simpleKey s s' hOk)
      (scanDirectiveIx_preserves_simpleKeyStack s s' hOk)

theorem scanNextTokenIx_dispatchFlowIndicators_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) :
    SimpleKeyAboveIx s' n := by
  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h_ok with
    heq | heq | heq | heq | hOk
  · subst heq
    exact SimpleKeyAboveIx_flowStart s _ n h_inv
      (scanFlowSequenceStartIx_simpleKey_cleared s)
      (scanFlowSequenceStartIx_stack_pushed s)
  · subst heq
    exact SimpleKeyAboveIx_flowEnd s _ n h_inv
      (scanFlowSequenceEndIx_simpleKey_restored s)
      (scanFlowSequenceEndIx_stack_popped s)
  · subst heq
    exact SimpleKeyAboveIx_flowStart s _ n h_inv
      (scanFlowMappingStartIx_simpleKey_cleared s)
      (scanFlowMappingStartIx_stack_pushed s)
  · subst heq
    exact SimpleKeyAboveIx_flowEnd s _ n h_inv
      (scanFlowMappingEndIx_simpleKey_restored s)
      (scanFlowMappingEndIx_stack_popped s)
  · -- scanFlowEntryIx preserves simpleKey + simpleKeyStack (Step 6f.0)
    exact SimpleKeyAboveIx_mono s _ n h_inv
      (scanFlowEntryIx_preserves_simpleKey s s' hOk)
      (scanFlowEntryIx_preserves_simpleKeyStack s s' hOk)

theorem scanNextTokenIx_dispatchBlockIndicators_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    SimpleKeyAboveIx s' n := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h_ok with hOk | hOk | hOk
  · -- scanBlockEntryIx: preserves
    exact SimpleKeyAboveIx_mono s _ n h_inv
      (scanBlockEntryIx_preserves_simpleKey s s' hOk)
      (scanBlockEntryIx_preserves_simpleKeyStack s s' hOk)
  · -- scanKeyIx: clears + preserves stack
    exact SimpleKeyAboveIx_of_cleared_mono s _ n h_inv
      (scanKeyIx_clears_simpleKey s s' hOk)
      (scanKeyIx_preserves_simpleKeyStack s s' hOk)
  · -- scanValueIx: clears + preserves stack
    exact SimpleKeyAboveIx_of_cleared_mono s _ n h_inv
      (scanValueIx_clears_simpleKey s s' hOk)
      (scanValueIx_preserves_simpleKeyStack s s' hOk)

theorem scanNextTokenIx_dispatchContent_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s') :
    SimpleKeyAboveIx s' n := by
  unfold scanNextTokenIx_dispatchContent at h_ok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_ok
  split at h_ok
  · -- c == '&': anchor
    generalize h_anch : scanAnchorOrAliasIx s true = anch_result at h_ok
    cases anch_result with
    | error e => simp at h_ok
    | ok s_anch =>
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact SimpleKeyAboveIx_mono s s_anch n h_inv
        (scanAnchorOrAliasIx_preserves_simpleKey s true s_anch h_anch)
        (scanAnchorOrAliasIx_preserves_simpleKeyStack s true s_anch h_anch)
  · split at h_ok
    · -- c == '*': alias
      generalize h_anch : scanAnchorOrAliasIx s false = anch_result at h_ok
      cases anch_result with
      | error e => simp at h_ok
      | ok s_anch =>
        dsimp only [] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        exact SimpleKeyAboveIx_mono s s_anch n h_inv
          (scanAnchorOrAliasIx_preserves_simpleKey s false s_anch h_anch)
          (scanAnchorOrAliasIx_preserves_simpleKeyStack s false s_anch h_anch)
    · split at h_ok
      · -- c == '!': tag
        generalize h_tag : scanTagIx s = tag_result at h_ok
        cases tag_result with
        | error e => simp at h_ok
        | ok s_tag =>
          dsimp only [] at h_ok
          simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact SimpleKeyAboveIx_mono s s_tag n h_inv
            (scanTagIx_preserves_simpleKey s s_tag h_tag)
            (scanTagIx_preserves_simpleKeyStack s s_tag h_tag)
      · split at h_ok
        · -- c == '|' || c == '>': block scalar (inline)
          split at h_ok
          · simp only [Except.ok.injEq] at h_ok
            subst h_ok
            exact SimpleKeyAboveIx_mono s _ n h_inv (by simp) (by simp)
          · simp at h_ok
        · split at h_ok
          · -- c == '"': double quoted
            split at h_ok
            · simp only [Except.ok.injEq] at h_ok
              subst h_ok
              exact SimpleKeyAboveIx_mono s _ n h_inv (by simp) (by simp)
            · simp at h_ok
          · split at h_ok
            · -- c == '\'': single quoted
              split at h_ok
              · simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact SimpleKeyAboveIx_mono s _ n h_inv (by simp) (by simp)
              · simp at h_ok
            · split at h_ok
              · -- plain scalar
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact SimpleKeyAboveIx_mono s _ n h_inv (by simp) (by simp)
              · simp at h_ok

/-! ### §7.6  `scanNextTokenIx` maintains `SimpleKeyAboveIx`

Composes preprocess (§7.4) with the four sub-dispatcher maintains
lemmas (§7.5) and the `allowDirectives` record update (which
preserves both `simpleKey` and `simpleKeyStack` by mono). -/

theorem scanNextTokenIx_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx s = .ok (some s')) :
    SimpleKeyAboveIx s' n := by
  unfold scanNextTokenIx at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  generalize h_pp : scanNextTokenIx_preprocess s = pp_res at h_ok
  cases pp_res with
  | error e => simp at h_ok
  | ok pp_inner =>
    cases pp_inner with
    | none => simp at h_ok
    | some pair =>
      cases pair with
      | mk s_pp c =>
        have h_inv_pp : SimpleKeyAboveIx s_pp n :=
          scanNextTokenIx_preprocess_maintains_SimpleKeyAboveIx s s_pp c n h_n h_pp h_inv
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            exact scanNextTokenIx_dispatchStructural_maintains_SimpleKeyAboveIx
              s_pp s_str c n h_inv_pp h_ds
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_inv_dir : SimpleKeyAboveIx s_dir n := by
              rw [← h_dir_def]
              split
              · exact SimpleKeyAboveIx_mono s_pp _ n h_inv_pp rfl rfl
              · exact h_inv_pp
            generalize h_ck : scanNextTokenIx_checkBlockFlowIndent s_dir c = ck_res at h_ok
            cases ck_res with
            | error e => simp at h_ok
            | ok _ =>
              dsimp only [] at h_ok
              generalize h_df : scanNextTokenIx_dispatchFlowIndicators s_dir c = df_res at h_ok
              cases df_res with
              | error e => simp at h_ok
              | ok df_inner =>
                cases df_inner with
                | some s_flow =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                  subst h_ok
                  exact scanNextTokenIx_dispatchFlowIndicators_maintains_SimpleKeyAboveIx
                    s_dir s_flow c n h_inv_dir h_df
                | none =>
                  dsimp only [] at h_ok
                  generalize h_db : scanNextTokenIx_dispatchBlockIndicators s_dir c = db_res at h_ok
                  cases db_res with
                  | error e => simp at h_ok
                  | ok db_inner =>
                    cases db_inner with
                    | some s_blk =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                      subst h_ok
                      exact scanNextTokenIx_dispatchBlockIndicators_maintains_SimpleKeyAboveIx
                        s_dir s_blk c n h_inv_dir h_db
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        exact scanNextTokenIx_dispatchContent_maintains_SimpleKeyAboveIx
                          s_dir s_ct c n h_inv_dir h_dc

/-! ### §7.7  Per-helper preserves-prefix-below-n

The existing `_preserves_prefix` lemmas in
`IndexedScannerPlainScalarValid.lean` are bound-by-`s.tokens.size`
(preserve the entire prefix unconditionally, or — for `scanValueIx` —
preserve below `n` given the simple-key bound). They use
`Indexed.TokenStream`'s `GetElem` instance (`s.tokens[i]`), which is
the form we adopt throughout §7.7–§7.9.

`scanNextTokenIx_dispatchContent` does not have a packaged
`_preserves_prefix` lemma in `IndexedScannerPlainScalarValid.lean`,
so we build it here by case-splitting through each `c` branch of the
dispatcher. Each content branch only `emit`-pushes a token (scalars,
anchors, tags) and so preserves the entire prefix. -/

theorem _inline_scalar_preserves_prefix {input : String}
    (s : ScannerStateIx input) (cAfter : IxCursor input)
    (startPos : YamlPos) (tok : YamlToken)
    (hBound : startPos.offset ≤ cAfter.pos.offset)
    (i : Nat) (h_bound : i < s.tokens.size) :
    ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos tok hBound with
        simpleKeyAllowed := false } : ScannerStateIx input).tokens[i]'(by
          show i <
            (({ s with cursor := cAfter } : ScannerStateIx input).emitAt
              startPos tok hBound).tokens.size
          rw [ScannerPlainScalarValid.emitAt_tokens_size]
          have h_eq : ({ s with cursor := cAfter : ScannerStateIx input}).tokens.size =
            s.tokens.size := rfl
          omega) = s.tokens[i]'h_bound := by
  -- record-update on simpleKeyAllowed is rfl on .tokens; emitAt preserves prefix.
  show (({ s with cursor := cAfter } : ScannerStateIx input).emitAt
    startPos tok hBound).tokens[i]'_ = s.tokens[i]'h_bound
  show (({ s with cursor := cAfter } : ScannerStateIx input).tokens.tokens.push
    (IxToken.mk' startPos tok cAfter.pos hBound cAfter.posBound))[i]'_ =
      s.tokens.tokens[i]'h_bound
  exact Array.getElem_push_lt h_bound

theorem scanNextTokenIx_dispatchContent_preserves_prefix {input : String}
    (s s' : ScannerStateIx input) (c : Char)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by
      have := scanNextTokenIx_dispatchContent_tokens_size_le h_ok; omega) =
    s.tokens[i]'h_bound := by
  unfold scanNextTokenIx_dispatchContent at h_ok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_ok
  split at h_ok
  · -- c == '&'
    generalize h_anch : scanAnchorOrAliasIx s true = anch_result at h_ok
    cases anch_result with
    | error e => simp at h_ok
    | ok s_anch =>
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact scanAnchorOrAliasIx_preserves_prefix s true s_anch h_anch i h_bound
  · split at h_ok
    · -- c == '*'
      generalize h_anch : scanAnchorOrAliasIx s false = anch_result at h_ok
      cases anch_result with
      | error e => simp at h_ok
      | ok s_anch =>
        dsimp only [] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        exact scanAnchorOrAliasIx_preserves_prefix s false s_anch h_anch i h_bound
    · split at h_ok
      · -- c == '!'
        generalize h_tag : scanTagIx s = tag_result at h_ok
        cases tag_result with
        | error e => simp at h_ok
        | ok s_tag =>
          dsimp only [] at h_ok
          simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact scanTagIx_preserves_prefix s s_tag h_tag i h_bound
      · split at h_ok
        · -- block scalar
          split at h_ok
          · simp only [Except.ok.injEq] at h_ok
            subst h_ok
            exact _inline_scalar_preserves_prefix s _ _ _ _ i h_bound
          · simp at h_ok
        · split at h_ok
          · -- double quoted
            split at h_ok
            · simp only [Except.ok.injEq] at h_ok
              subst h_ok
              exact _inline_scalar_preserves_prefix s _ _ _ _ i h_bound
            · simp at h_ok
          · split at h_ok
            · -- single quoted
              split at h_ok
              · simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact _inline_scalar_preserves_prefix s _ _ _ _ i h_bound
              · simp at h_ok
            · split at h_ok
              · -- plain scalar
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact _inline_scalar_preserves_prefix s _ _ _ _ i h_bound
              · simp at h_ok

/-! ### §7.7'  `scanNextTokenIx_preserves_prefix` (composed)

Combines preprocess prefix-preservation with the four sub-dispatcher
preserves-prefix lemmas. Most sub-dispatchers preserve the *entire*
prefix (their helpers only `emit`); only `scanValueIx` requires the
`SimpleKeyAboveIx` bound.

Spec uses `Indexed.TokenStream`'s `GetElem` instance, with the
original bound provided explicitly via `Nat.lt_of_lt_of_le` (omega
does not see through the `.size = .tokens.size` defeq). -/

theorem _preprocess_preserves_prefix {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_pre : scanNextTokenIx_preprocess s = .ok (some (s', c)))
    (i : Nat) (h_i : i < n) :
    ∃ (h_size : i < s'.tokens.size),
      s'.tokens[i]'h_size = s.tokens[i]'(Nat.lt_of_lt_of_le h_i h_n) := by
  have h_orig : i < s.tokens.size := Nat.lt_of_lt_of_le h_i h_n
  -- skipToContentS preserves tokens (cursor-only update).
  have h_skip_tok : s.skipToContentS.tokens = s.tokens := skipToContentS_tokens s
  have h_i_skip : i < s.skipToContentS.tokens.size := by rw [h_skip_tok]; exact h_orig
  have h_skip_eq :
      s.skipToContentS.tokens[i]'h_i_skip = s.tokens[i]'h_orig := by
    have : ∀ (h : i < s.tokens.size),
        s.skipToContentS.tokens[i]'(h_skip_tok ▸ h) = s.tokens[i]'h := by
      intro h; congr 1
    exact this h_orig
  unfold scanNextTokenIx_preprocess at h_pre
  simp only at h_pre
  split at h_pre
  · simp at h_pre
  · split at h_pre
    · -- branch 1: with indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          -- s_mid := { unwindIndentsIx ... with needIndentCheck := false }
          have h_mid_tok :
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                  needIndentCheck := false } : ScannerStateIx input).tokens =
              (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).tokens := rfl
          have h_unwind_sz := unwindIndentsIx_tokens_size_le s.skipToContentS
            s.skipToContentS.cursor.pos.col
          have h_skip_sz_eq : s.skipToContentS.tokens.size = s.tokens.size := by
            rw [h_skip_tok]
          have h_i_mid : i <
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                  needIndentCheck := false } : ScannerStateIx input).tokens.size := by
            rw [h_mid_tok]; omega
          have h_mid_eq :
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                  needIndentCheck := false } : ScannerStateIx input).tokens[i]'h_i_mid =
              s.tokens[i]'h_orig := by
            rw [show
                ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                    needIndentCheck := false } : ScannerStateIx input).tokens[i]'h_i_mid =
                  (unwindIndentsIx s.skipToContentS
                    s.skipToContentS.cursor.pos.col).tokens[i]'(h_mid_tok ▸ h_i_mid) from
                by congr 1]
            rw [unwindIndentsIx_preserves_prefix s.skipToContentS
                  s.skipToContentS.cursor.pos.col i h_i_skip]
            exact h_skip_eq
          have h_save_sz := saveSimpleKeyIx_tokens_size_le
            ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                needIndentCheck := false } : ScannerStateIx input)
          have h_i_save : i < (saveSimpleKeyIx
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                  needIndentCheck := false } : ScannerStateIx input)).tokens.size := by omega
          refine ⟨h_i_save, ?_⟩
          rw [saveSimpleKeyIx_preserves_prefix
            ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                needIndentCheck := false } : ScannerStateIx input) i h_i_mid]
          exact h_mid_eq
    · -- branch 2: without indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          have h_save_sz := saveSimpleKeyIx_tokens_size_le s.skipToContentS
          have h_i_save : i < (saveSimpleKeyIx s.skipToContentS).tokens.size := by omega
          refine ⟨h_i_save, ?_⟩
          rw [saveSimpleKeyIx_preserves_prefix s.skipToContentS i h_i_skip]
          exact h_skip_eq

theorem _dir_update_tokens {input : String} (s_pp : ScannerStateIx input) :
    (if s_pp.allowDirectives = true then
        { s_pp with allowDirectives := false, documentEverStarted := true }
      else s_pp).tokens = s_pp.tokens := by
  split <;> rfl

theorem scanNextTokenIx_preserves_prefix {input : String}
    (s s' : ScannerStateIx input) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx s = .ok (some s'))
    (i : Nat) (h_i : i < n) :
    ∃ (h_size : i < s'.tokens.size),
      s'.tokens[i]'h_size = s.tokens[i]'(Nat.lt_of_lt_of_le h_i h_n) := by
  have h_orig : i < s.tokens.size := Nat.lt_of_lt_of_le h_i h_n
  unfold scanNextTokenIx at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  generalize h_pp : scanNextTokenIx_preprocess s = pp_res at h_ok
  cases pp_res with
  | error e => simp at h_ok
  | ok pp_inner =>
    cases pp_inner with
    | none => simp at h_ok
    | some pair =>
      cases pair with
      | mk s_pp c =>
        have h_inv_pp : SimpleKeyAboveIx s_pp n :=
          scanNextTokenIx_preprocess_maintains_SimpleKeyAboveIx s s_pp c n h_n h_pp h_inv
        obtain ⟨h_i_pp, h_pre_eq⟩ := _preprocess_preserves_prefix s s_pp c n h_n h_pp i h_i
        have h_n_pp : n ≤ s_pp.tokens.size :=
          Nat.le_trans h_n (scanNextTokenIx_preprocess_tokens_size_le h_pp)
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            rcases scanNextTokenIx_dispatchStructural_ok_some_cases h_ds with heq | hOk | hOk
            · subst heq
              have h_pref := scanDocumentStartIx_preserves_prefix s_pp i h_i_pp
              have h_sz : i < (scanDocumentStartIx s_pp).tokens.size := by
                have := scanDocumentStartIx_tokens_size_le s_pp; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
            · have h_pref := scanDocumentEndIx_preserves_prefix s_pp _ hOk i h_i_pp
              have h_sz : i < s_str.tokens.size := by
                have := scanDocumentEndIx_tokens_size_le hOk; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
            · have h_pref := scanDirectiveIx_preserves_prefix s_pp _ hOk i h_i_pp
              have h_sz : i < s_str.tokens.size := by
                have := scanDirectiveIx_tokens_size_le hOk; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_dir_tok : s_dir.tokens = s_pp.tokens := by
              rw [← h_dir_def]; exact _dir_update_tokens s_pp
            have h_i_dir : i < s_dir.tokens.size := by rw [h_dir_tok]; exact h_i_pp
            have h_dir_eq : s_dir.tokens[i]'h_i_dir = s_pp.tokens[i]'h_i_pp := by
              have : ∀ (h : i < s_pp.tokens.size),
                  s_dir.tokens[i]'(h_dir_tok ▸ h) = s_pp.tokens[i]'h := by
                intro h; congr 1
              exact this h_i_pp
            have h_inv_dir : SimpleKeyAboveIx s_dir n := by
              rw [← h_dir_def]
              split
              · exact SimpleKeyAboveIx_mono s_pp _ n h_inv_pp rfl rfl
              · exact h_inv_pp
            generalize h_ck : scanNextTokenIx_checkBlockFlowIndent s_dir c = ck_res at h_ok
            cases ck_res with
            | error e => simp at h_ok
            | ok _ =>
              dsimp only [] at h_ok
              generalize h_df : scanNextTokenIx_dispatchFlowIndicators s_dir c = df_res at h_ok
              cases df_res with
              | error e => simp at h_ok
              | ok df_inner =>
                cases df_inner with
                | some s_flow =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                  subst h_ok
                  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h_df with
                    heq | heq | heq | heq | hOk
                  · subst heq
                    have h_pref := scanFlowSequenceStartIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowSequenceStartIx s_dir).tokens.size := by
                      have := scanFlowSequenceStartIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowSequenceEndIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowSequenceEndIx s_dir).tokens.size := by
                      have := scanFlowSequenceEndIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowMappingStartIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowMappingStartIx s_dir).tokens.size := by
                      have := scanFlowMappingStartIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowMappingEndIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowMappingEndIx s_dir).tokens.size := by
                      have := scanFlowMappingEndIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · have h_pref := scanFlowEntryIx_preserves_prefix s_dir s_flow hOk i h_i_dir
                    have h_sz : i < s_flow.tokens.size := by
                      have := scanFlowEntryIx_tokens_size_le hOk; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                | none =>
                  dsimp only [] at h_ok
                  generalize h_db : scanNextTokenIx_dispatchBlockIndicators s_dir c = db_res at h_ok
                  cases db_res with
                  | error e => simp at h_ok
                  | ok db_inner =>
                    cases db_inner with
                    | some s_blk =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                      subst h_ok
                      have h_n_dir : n ≤ s_dir.tokens.size := by rw [h_dir_tok]; exact h_n_pp
                      rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h_db with
                        hOk | hOk | hOk
                      · have h_pref := scanBlockEntryIx_preserves_prefix s_dir s_blk hOk i h_i_dir
                        have h_sz : i < s_blk.tokens.size := by
                          have := scanBlockEntryIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                      · have h_pref := scanKeyIx_preserves_prefix s_dir s_blk hOk i h_i_dir
                        have h_sz : i < s_blk.tokens.size := by
                          have := scanKeyIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                      · -- scanValueIx: bounded form requires SimpleKeyAboveIx
                        have h_pref := scanValueIx_preserves_prefix s_dir s_blk hOk n h_n_dir
                          h_inv_dir.1 i h_i
                        have h_sz : i < s_blk.tokens.size := by
                          have := scanValueIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        have h_pref :=
                          scanNextTokenIx_dispatchContent_preserves_prefix s_dir s_ct c h_dc i h_i_dir
                        have h_sz : i < s_ct.tokens.size := by
                          have := scanNextTokenIx_dispatchContent_tokens_size_le h_dc; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩

/-! ### §7.8  `scanLoopIx_preserves_tokens` (fuel induction)

Indexed twin of legacy `scanLoop_preserves_tokens` (`Proofs/Scanner/
ScannerCorrectness.lean:6197`). Proven by induction on fuel:

  - Base (`fuel = 0`): `scanLoopIx` returns `.error`, contradicting `.ok`.
  - Recursive step (`fuel = fuel'+1`): split on `scanNextTokenIx`.
    - Terminal (`.ok none` branch into final `unwindIndentsIx + emit
      streamEnd`): use `unwindIndentsIx_preserves_prefix` + emit.
    - Recursive (`.ok (some s')`): combine
      `scanNextTokenIx_preserves_prefix` +
      `scanNextTokenIx_maintains_SimpleKeyAboveIx` + IH. -/

theorem scanLoopIx_preserves_tokens {input : String}
    (s : ScannerStateIx input) (fuel : Nat) (ts : Indexed.TokenStream input)
    (n : Nat) (h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAboveIx s n)
    (h : scanLoopIx s fuel = .ok ts) (i : Nat) (h_i : i < n) :
    ∃ (h_size : i < ts.size),
      ts[i]'h_size = s.tokens[i]'(Nat.lt_of_lt_of_le h_i h_n) := by
  have h_orig : i < s.tokens.size := Nat.lt_of_lt_of_le h_i h_n
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
        by_cases hFL : s.flowLevel > 0
        · rw [if_pos hFL] at h; cases h
        · rw [if_neg hFL] at h
          by_cases hDS : (s.directivesPresent && !s.documentEverStarted) = true
          · rw [if_pos hDS] at h; cases h
          · rw [if_neg hDS] at h
            cases h
            -- ts = ((unwindIndentsIx s (-1)).emit streamEnd).tokens
            have h_unwind_sz := unwindIndentsIx_tokens_size_le s (-1)
            have h_i_unwind : i < (unwindIndentsIx s (-1)).tokens.size := by omega
            have h_emit_sz :
                ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).tokens.size =
                (unwindIndentsIx s (-1)).tokens.size + 1 :=
              emit_tokens_size (unwindIndentsIx s (-1)) .streamEnd
            have h_i_emit : i <
                ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).tokens.size := by
              rw [h_emit_sz]; omega
            refine ⟨h_i_emit, ?_⟩
            calc ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).tokens[i]'h_i_emit
                = (unwindIndentsIx s (-1)).tokens[i]'h_i_unwind :=
                    emit_preserves_tokens_at (unwindIndentsIx s (-1)) .streamEnd i h_i_unwind
              _ = s.tokens[i]'h_orig :=
                    unwindIndentsIx_preserves_prefix s (-1) i h_orig
      | some s'' =>
        have h_step := scanNextTokenIx_tokens_size_le hSc
        have h_inv_step := scanNextTokenIx_maintains_SimpleKeyAboveIx s s'' n h_n h_inv hSc
        have h_n_step : n ≤ s''.tokens.size := by omega
        obtain ⟨h_i_step, h_pre_eq⟩ :=
          scanNextTokenIx_preserves_prefix s s'' n h_n h_inv hSc i h_i
        -- IH binds `i < s''.tokens.size` as an extra parameter after generalization
        -- (the existential's RHS bound depends on `h_n` which was generalized).
        have h_orig_step : i < s''.tokens.size := Nat.lt_of_lt_of_le h_i h_n_step
        obtain ⟨h_i_ts, h_ts_eq⟩ := ih s'' h_n_step h_inv_step h h_orig_step
        exact ⟨h_i_ts, h_ts_eq.trans h_pre_eq⟩

/-! ### §7.9  `scanIx_first_is_streamStart` — discharge of §6.4 axiom

After `(mk' input).emit streamStart`, `tokens.size = 1` and
`tokens[0].token = streamStart`. The optional BOM advance preserves
both. Both states satisfy `SimpleKeyAboveIx _ 1` vacuously
(`simpleKey.possible = false`, `simpleKeyStack` empty). Applying
`scanLoopIx_preserves_tokens` with `n = 1` and `i = 0` gives that
`tokens[0]` is preserved through the loop. -/

theorem scanIx_first_is_streamStart {input : String}
    (tokens : Indexed.TokenStream input)
    (h : scanIx input = .ok tokens)
    (h_size : 0 < tokens.tokens.size) :
    (tokens.tokens[0]'h_size).token = YamlToken.streamStart := by
  -- Naming: s0 := (mk' input).emit streamStart; sB := BOM-handled s0.
  -- s0.tokens.size = 1, s0.tokens[0].token = streamStart.
  -- sB.tokens = s0.tokens, SimpleKeyAboveIx sB 1 holds vacuously.
  -- scanLoopIx_preserves_tokens with n=1, i=0 gives tokens[0] = sB.tokens[0] = s0.tokens[0].
  unfold scanIx at h
  have h_mk_sz : (ScannerStateIx.mk' input).tokens.tokens.size = 0 := rfl
  have h_s0_sz :
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size = 1 := by
    rw [emit_tokens_size]
    show (ScannerStateIx.mk' input).tokens.tokens.size + 1 = 1
    omega
  have h_s0_pos : 0 < ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size := by
    rw [h_s0_sz]; omega
  have h_s0_tok :
      (((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h_s0_pos).token =
      YamlToken.streamStart := by
    show (((ScannerStateIx.mk' input).tokens.tokens.push
      (IxToken.mk' (ScannerStateIx.mk' input).cursor.pos YamlToken.streamStart
        (ScannerStateIx.mk' input).cursor.pos (Nat.le_refl _)
        (ScannerStateIx.mk' input).cursor.posBound))[0]'h_s0_pos).token =
        YamlToken.streamStart
    rw [Array.getElem_push]
    simp [h_mk_sz]
    rfl
  -- BOM step preserves tokens.
  have h_sB_tok : ∀ (s : ScannerStateIx input),
      (match s.peek? with | some '﻿' => s.advance | _ => s).tokens = s.tokens := by
    intro s; split <;> rfl
  have h_bom_eq : (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
      | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
      | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens =
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens := h_sB_tok _
  have h_sB_sz :
      (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
        | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
        | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size = 1 := by
    rw [h_bom_eq]; exact h_s0_sz
  have h_n_sB : 1 ≤ (match
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
      | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
      | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size := by
    rw [h_sB_sz]; omega
  -- Vacuous SimpleKeyAboveIx for the post-streamStart state.
  have h_inv_s0 :
      SimpleKeyAboveIx ((ScannerStateIx.mk' input).emit YamlToken.streamStart) 1 := by
    refine ⟨?_, ?_⟩
    · intro h_poss
      exfalso; revert h_poss
      show ¬ ((ScannerStateIx.mk' input).emit YamlToken.streamStart).simpleKey.possible = true
      rw [emit_preserves_simpleKey]
      simp [ScannerStateIx.mk']
    · intro j hj
      exfalso; revert hj
      show ¬ j < ((ScannerStateIx.mk' input).emit YamlToken.streamStart).simpleKeyStack.size
      rw [emit_preserves_simpleKeyStack]
      simp [ScannerStateIx.mk']
  -- Vacuous SimpleKeyAboveIx for the BOM-handled state.
  have h_inv_sB : SimpleKeyAboveIx (match
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
      | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
      | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart) 1 := by
    split
    · exact SimpleKeyAboveIx_mono _ _ 1 h_inv_s0
        (by simp [advance_preserves_simpleKey]) (by simp [advance_preserves_simpleKeyStack])
    · exact h_inv_s0
  -- Apply scanLoopIx_preserves_tokens with n = 1, i = 0.
  obtain ⟨h_pos_ts, h_eq⟩ :=
    scanLoopIx_preserves_tokens _ ((input.utf8ByteSize + 1) * 4) tokens 1
      h_n_sB h_inv_sB h 0 (by omega)
  -- h_eq : tokens[0]'_ = bom.tokens[0]'_.
  have h_pos_bom : 0 <
      (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
        | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
        | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size := by
    rw [h_sB_sz]; omega
  have h_bom_tok0 :
      (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
        | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
        | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h_pos_bom =
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h_s0_pos := by
    have : ∀ (h : 0 < ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size),
        (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
          | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
          | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'(h_bom_eq ▸ h) =
        ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h := by
      intro h; congr 1
    exact this h_s0_pos
  -- Bridge: tokens.tokens[0] = tokens[0] (TokenStream GetElem rfl).
  have h_link :
      tokens[0]'h_pos_ts =
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h_s0_pos :=
    h_eq.trans h_bom_tok0
  -- The two access forms are definitionally equal (GetElem instance is rfl).
  have h_link' :
      tokens.tokens[0]'h_size =
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.tokens[0]'h_s0_pos :=
    h_link
  rw [h_link']
  exact h_s0_tok

/-! ### §7.10  Final composite `scanIx_valid_token_stream` (theorem)

Replaces the old composite using the discharged `scanIx_first_is_streamStart`. -/

theorem scanIx_valid_token_stream
    {input : String} (tokens : Indexed.TokenStream input)
    (h : scanIx input = .ok tokens) :
    ValidTokenStreamPropIx tokens := by
  have h_size : tokens.tokens.size ≥ 2 := scanIx_produces_at_least_two tokens h
  have h_pos : 0 < tokens.tokens.size := by omega
  refine ⟨h_size, ?_, ?_, ?_⟩
  · intro _; exact scanIx_first_is_streamStart tokens h h_pos
  · intro _; exact scanIx_last_is_streamEnd tokens h h_pos
  · exact scanIx_positions_ordered_axiom tokens h

end L4YAML.Proofs.Indexed.ScannerCorrectness
