/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Grammar
import Lean4Yaml.Proofs.ScannerPlainScalar
import Lean4Yaml.Proofs.ScannerCorrectness

/-!
# Plain Scalar Validity for the Full Scan Chain (B3.5)

Proves `scan_plain_scalar_valid`: every plain scalar token emitted by the
scanner satisfies `ScalarScannable _ false`.

## Strategy

Thread `scanPlainScalar_content_valid` (B3.4) through the
`scanFiltered → scan → scanLoop → scanNextToken → dispatchContent → scanPlainScalar`
chain using `PlainScalarsValid`, a monotone token-array invariant.

Key insight: `ScalarScannable _ true → ScalarScannable _ false` (monotonicity),
so we can use `inFlow = false` uniformly. The only scan function that emits
`.scalar _ .plain` tokens is `scanPlainScalar`; all other functions emit
non-plain-scalar tokens.

## Sorry inventory

Sorries in this file fall into two categories:

1. **Non-plain token characterization** (dispatch-level): Each non-plain dispatch
   branch emits a specific token type (.blockEnd, .flowEntry, .anchor, .tag, etc.)
   that is manifestly not `.scalar _ .plain`. Discharging these formally requires
   unfolding each sub-function to expose its `emit`/`emitAt` call and showing the
   pushed token's `.val` is a different constructor. Structurally straightforward
   but tedious (~20 lines each × ~12 branches = ~240 lines of boilerplate).

2. **Scan chain setup** (`scan_all_plain_scalars_valid`): Threading `PlainScalarsValid`
   from the initial state through `scan`'s let-bindings into `scanLoop`.
-/

namespace Lean4Yaml.Proofs.ScannerPlainScalarValid

open Lean4Yaml
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates
open Lean4Yaml.Grammar
open Lean4Yaml.Proofs.ScannerPlainScalar
open Lean4Yaml.Proofs.ScannerCorrectness
open Lean4Yaml.Proofs.ScannerCorrectness.ScanHelpers
open Lean4Yaml.Proofs.ScannerProofs

/-! ## Definition -/

/-- Every plain scalar token in a token array satisfies `ScalarScannable _ false`. -/
def PlainScalarsValid (tokens : Array (Positioned YamlToken)) : Prop :=
  ∀ i (hi : i < tokens.size),
    match (tokens[i]'hi).val with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True

/-! ## Monotonicity: ScalarScannable true → false -/

theorem canStartPlainScalarProp_true_implies_false (c : Char) (next : Option Char) :
    canStartPlainScalarProp c next true → canStartPlainScalarProp c next false := by
  unfold canStartPlainScalarProp
  split
  · cases next with
    | none => exact id
    | some n => intro ⟨h1, h2, _⟩; exact ⟨h1, h2, fun h => absurd h (by decide)⟩
  · exact id

theorem validPlainFirstProp_true_implies_false (content : String) :
    validPlainFirstProp content true → validPlainFirstProp content false := by
  unfold validPlainFirstProp
  cases content.toList with
  | nil => exact id
  | cons c rest =>
    cases rest with
    | nil => exact canStartPlainScalarProp_true_implies_false c none
    | cons n _ => exact canStartPlainScalarProp_true_implies_false c (some n)

theorem ScalarScannable_true_implies_false (s : Scalar) :
    ScalarScannable s true → ScalarScannable s false := by
  intro h hplain hlen
  have ⟨h1, h2, h3, _⟩ := h hplain hlen
  exact ⟨validPlainFirstProp_true_implies_false s.content h1, h2, h3,
         fun h => absurd h (by decide)⟩

/-- `ScalarScannable _ b` implies `ScalarScannable _ false` for any `b`. -/
theorem ScalarScannable_any_implies_false (s : Scalar) (b : Bool) :
    ScalarScannable s b → ScalarScannable s false := by
  cases b with
  | false => exact id
  | true => exact ScalarScannable_true_implies_false s

/-! ## Generic lemmas -/

theorem PlainScalarsValid_empty : PlainScalarsValid #[] :=
  fun _ hi => absurd hi (by simp [Array.size])

/-- Prefix preservation + new tokens valid ⟹ PlainScalarsValid for extended array. -/
theorem PlainScalarsValid_of_prefix_and_new
    (old_tokens new_tokens : Array (Positioned YamlToken))
    (h_old : PlainScalarsValid old_tokens)
    (h_mono : old_tokens.size ≤ new_tokens.size)
    (h_prefix : ∀ (i : Nat) (hi : i < old_tokens.size),
      new_tokens[i]'(by omega) = old_tokens[i])
    (h_new : ∀ j (hj : j < new_tokens.size), j ≥ old_tokens.size →
      match (new_tokens[j]'hj).val with
      | .scalar content .plain =>
          ScalarScannable ⟨content, .plain, none, none, none⟩ false
      | _ => True) :
    PlainScalarsValid new_tokens := by
  intro i hi
  by_cases h : i < old_tokens.size
  · rw [h_prefix i h]; exact h_old i h
  · exact h_new i hi (by omega)

/-! ## scanPlainScalar preserves PlainScalarsValid -/

/-- The per-token property used in PlainScalarsValid. -/
def psv_match (tok : Positioned YamlToken) : Prop :=
  match tok.val with
  | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
  | _ => True

/-- When a token is provably not `.scalar _ .plain`, the PSV match is `True`. -/
theorem psv_match_of_ne_plain
    (tokens : Array (Positioned YamlToken)) (j : Nat) (hj : j < tokens.size)
    (h_ne : ∀ c, (tokens[j]'hj).val ≠ YamlToken.scalar c .plain) :
    match (tokens[j]'hj).val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  generalize h_eq : (tokens[j]'hj).val = tok
  cases tok with
  | scalar content style => cases style with | plain => exact absurd h_eq (h_ne content) | _ => trivial
  | _ => trivial

/-! ## Non-plain token building blocks

Helper lemmas proving that `unwindIndentsLoop`, `unwindIndents`, and `saveSimpleKey`
only emit non-plain-scalar tokens at new positions. Used to close the
"new token characterization" sorry obligations in the dispatch theorems. -/

/-- If a token's `.val` is not `.scalar _ .plain`, the PSV match gives `True`. -/
theorem psv_of_not_plain (tok : Positioned YamlToken)
    (h : match tok.val with | .scalar _ .plain => False | _ => True) :
    match tok.val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  cases tok with | mk pos val =>
  cases val <;> simp_all
  rename_i content style; cases style <;> simp_all

set_option maxHeartbeats 800000 in
/-- `unwindIndentsLoop` only emits `.blockEnd` tokens at new positions. -/
theorem unwindIndentsLoop_new_tokens_not_plain (s : ScannerState) (col : Int) (fuel : Nat) :
    ∀ (j : Nat) (hj : j < (unwindIndentsLoop s col fuel).tokens.size), j ≥ s.tokens.size →
    match ((unwindIndentsLoop s col fuel).tokens[j]'hj).val with
    | .scalar _ .plain => False
    | _ => True := by
  induction fuel generalizing s with
  | zero =>
    unfold unwindIndentsLoop
    intro j hj hge; omega
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · intro j hj hge
      have h_emit_size : (s.emit .blockEnd).tokens.size = s.tokens.size + 1 := emit_tokens_size s .blockEnd
      by_cases hlt : j < s.tokens.size + 1
      · have hj_eq : j = s.tokens.size := by omega
        subst hj_eq
        have h_pop_sz : s.tokens.size < ({ s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop } : ScannerState).tokens.size := by
          show s.tokens.size < (s.emit .blockEnd).tokens.size
          rw [h_emit_size]; omega
        rw [unwindIndentsLoop_preserves_prefix _ col fuel' s.tokens.size h_pop_sz]
        show match (({ s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop } : ScannerState).tokens[s.tokens.size]'h_pop_sz).val with
          | .scalar _ .plain => False | _ => True
        show match ((s.emit .blockEnd).tokens[s.tokens.size]'(by rw [h_emit_size]; omega)).val with
          | .scalar _ .plain => False | _ => True
        unfold ScannerState.emit
        simp only [Array.getElem_push_eq]
      · have hge' : j ≥ ({ s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop } : ScannerState).tokens.size := by
          show j ≥ (s.emit .blockEnd).tokens.size
          rw [h_emit_size]; omega
        exact ih _ j hj hge'
    · intro j hj hge; omega

/-- `unwindIndents` only emits `.blockEnd` tokens at new positions. -/
theorem unwindIndents_new_tokens_not_plain (s : ScannerState) (col : Int)
    (j : Nat) (hj : j < (unwindIndents s col).tokens.size) (hge : j ≥ s.tokens.size) :
    match ((unwindIndents s col).tokens[j]'hj).val with
    | .scalar _ .plain => False
    | _ => True := by
  unfold unwindIndents
  exact unwindIndentsLoop_new_tokens_not_plain s col s.indents.size j hj hge

set_option maxHeartbeats 400000 in
/-- `saveSimpleKey` only inserts `.placeholder` tokens at new positions. -/
theorem saveSimpleKey_new_tokens_not_plain (s : ScannerState)
    (j : Nat) (hj : j < (saveSimpleKey s).tokens.size) (hge : j ≥ s.tokens.size) :
    match ((saveSimpleKey s).tokens[j]'hj).val with
    | .scalar _ .plain => False
    | _ => True := by
  have h_cases : (saveSimpleKey s).tokens = s.tokens ∨
                 (saveSimpleKey s).tokens = (s.tokens.push ⟨s.currentPos, .placeholder⟩).push ⟨s.currentPos, .placeholder⟩ := by
    unfold saveSimpleKey
    split
    · left; rfl
    · split
      · right; rfl
      · left; rfl
  rcases h_cases with h_eq | h_eq
  · rw [h_eq] at hj; omega
  · simp only [h_eq] at hj ⊢
    by_cases h : j < s.tokens.size + 1
    · have hj_eq : j = s.tokens.size := by omega
      subst hj_eq
      simp [Array.getElem_push]
    · have hj_eq : j = s.tokens.size + 1 := by
        simp [Array.size_push] at hj; omega
      subst hj_eq
      simp [Array.getElem_push]

theorem scanPlainScalar_preserves_PlainScalarsValid
    (s s' : ScannerState) (h_old : PlainScalarsValid s.tokens)
    (h_ok : scanPlainScalar s = .ok s') :
    PlainScalarsValid s'.tokens := by
  have h_adds := scanPlainScalar_adds_one_token s s' h_ok
  apply PlainScalarsValid_of_prefix_and_new s.tokens s'.tokens h_old (by omega)
  · intro i hi; exact scanPlainScalar_preserves_prefix s s' h_ok i hi
  · intro j hj hge
    have h_jeq : j = s.tokens.size := by omega
    subst h_jeq
    -- Case split on the token type to reduce the goal's match
    generalize h_tok : (s'.tokens[s.tokens.size]'hj).val = tok
    cases tok with
    | scalar content style =>
      cases style with
      | plain =>
        have h_cv := scanPlainScalar_content_valid s s' h_ok hj
        rw [h_tok] at h_cv
        exact ScalarScannable_any_implies_false _ s.inFlow h_cv
      | _ => trivial
    | _ => trivial

/-! ## scanTag token is never plain scalar -/

set_option maxHeartbeats 800000 in
/-- The token added by `scanTag` is always `.tag _ _`, never `.scalar _ .plain`. -/
theorem scanTag_psv_match (s : ScannerState)
    (hj : s.tokens.size < (scanTag s).tokens.size) :
    match ((scanTag s).tokens[s.tokens.size]'hj).val with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  have h_tok_eq : (scanTag s).tokens = (match s.advance.peek? with
      | some '<' => scanVerbatimTag s.advance s.currentPos
      | some '!' => scanSecondaryTag s.advance s.currentPos
      | _        => scanNamedTag s.advance s.currentPos s.inputEnd).tokens := by
    unfold scanTag; rfl
  generalize h_gen : ((scanTag s).tokens[s.tokens.size]'hj).val = tok
  cases tok with
  | scalar content style =>
    cases style with
    | plain =>
      exfalso
      rcases h_peek : s.advance.peek? with _ | ⟨c⟩
      · have h_eq : (scanTag s).tokens = (scanNamedTag s.advance s.currentPos s.inputEnd).tokens := by
          rw [h_tok_eq]; simp [h_peek]
        simp only [h_eq] at h_gen
        unfold scanNamedTag at h_gen; simp only [] at h_gen
        unfold ScannerState.emitAt at h_gen
        simp only [Array.getElem_push] at h_gen
        split at h_gen
        · split at h_gen
          · rename_i h_inner
            simp only [collectTagSuffixLoop_preserves_tokens,
              collectTagHandleLoop_preserves_tokens, advance_preserves_tokens] at h_inner
            exact absurd h_inner (Nat.lt_irrefl _)
          · exact absurd h_gen (by intro h; exact YamlToken.noConfusion h)
        · split at h_gen
          · rename_i h_inner
            simp only [collectTagHandleLoop_preserves_tokens,
              advance_preserves_tokens] at h_inner
            exact absurd h_inner (Nat.lt_irrefl _)
          · exact absurd h_gen (by intro h; exact YamlToken.noConfusion h)
      · by_cases hlt : c = '<'
        · subst hlt
          have h_eq : (scanTag s).tokens = (scanVerbatimTag s.advance s.currentPos).tokens := by
            rw [h_tok_eq]; simp [h_peek]
          simp only [h_eq] at h_gen
          unfold scanVerbatimTag ScannerState.emitAt at h_gen
          simp only [Array.getElem_push] at h_gen
          split at h_gen
          · rename_i h_inner
            simp only [collectVerbatimTagLoop_preserves_tokens,
              advance_preserves_tokens] at h_inner
            exact absurd h_inner (Nat.lt_irrefl _)
          · exact absurd h_gen (by intro h; exact YamlToken.noConfusion h)
        · by_cases hbang : c = '!'
          · subst hbang
            have h_eq : (scanTag s).tokens = (scanSecondaryTag s.advance s.currentPos).tokens := by
              rw [h_tok_eq]; simp [h_peek]
            simp only [h_eq] at h_gen
            unfold scanSecondaryTag ScannerState.emitAt at h_gen
            simp only [Array.getElem_push] at h_gen
            split at h_gen
            · rename_i h_inner
              simp only [collectTagSuffixLoop_preserves_tokens,
                advance_preserves_tokens] at h_inner
              exact absurd h_inner (Nat.lt_irrefl _)
            · exact absurd h_gen (by intro h; exact YamlToken.noConfusion h)
          · have h_eq : (scanTag s).tokens = (scanNamedTag s.advance s.currentPos s.inputEnd).tokens := by
              rw [h_tok_eq]; simp [h_peek, hlt, hbang]
            simp only [h_eq] at h_gen
            unfold scanNamedTag at h_gen; simp only [] at h_gen
            unfold ScannerState.emitAt at h_gen
            simp only [Array.getElem_push] at h_gen
            split at h_gen
            · split at h_gen
              · rename_i h_inner
                simp only [collectTagSuffixLoop_preserves_tokens,
                  collectTagHandleLoop_preserves_tokens, advance_preserves_tokens] at h_inner
                exact absurd h_inner (Nat.lt_irrefl _)
              · exact absurd h_gen (by intro h; exact YamlToken.noConfusion h)
            · split at h_gen
              · rename_i h_inner
                simp only [collectTagHandleLoop_preserves_tokens,
                  advance_preserves_tokens] at h_inner
                exact absurd h_inner (Nat.lt_irrefl _)
              · exact absurd h_gen (by intro h; exact YamlToken.noConfusion h)
    | _ => trivial
  | _ => trivial

set_option maxHeartbeats 1600000 in
theorem scanBlockScalar_psv_match (s s_bs : ScannerState)
    (h_bs : scanBlockScalar s = .ok s_bs)
    (hj : s.tokens.size < s_bs.tokens.size) :
    match (s_bs.tokens[s.tokens.size]'hj).val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  have h_size := scanBlockScalar_adds_one_token s s_bs h_bs
  unfold scanBlockScalar at h_bs
  simp only [] at h_bs
  split at h_bs
  · contradiction
  · rename_i s_nl h_nl
    have h_tok : s_nl.tokens = s.tokens := by
      rw [scanBlockScalarConsumeNewline_preserves_tokens _ _ (by assumption),
          scanBlockScalarSkipComment_preserves_tokens,
          skipWhitespace_preserves_tokens,
          parseBlockHeaderLoop_preserves_tokens,
          advance_preserves_tokens]
    unfold scanBlockScalarBody at h_bs
    simp only [] at h_bs
    repeat (any_goals (split at h_bs))
    all_goals (try contradiction)
    all_goals (
      simp only [Except.ok.injEq] at h_bs
      generalize h_gen : (s_bs.tokens[s.tokens.size]'hj).val = tok
      subst h_bs
      dsimp only [] at h_gen
      unfold ScannerState.emitAt at h_gen
      dsimp only [] at h_gen
      simp only [Array.getElem_push] at h_gen
      rw [collectBlockScalarLoop_preserves_tokens, h_tok] at h_gen
      simp only [Nat.lt_irrefl] at h_gen
      split at h_gen
      · subst h_gen; trivial
      · subst h_gen; trivial
    )

set_option maxHeartbeats 1600000 in
theorem scanDoubleQuoted_psv_match (s s_dq : ScannerState)
    (h_dq : scanDoubleQuoted s = .ok s_dq)
    (hj : s.tokens.size < s_dq.tokens.size) :
    match (s_dq.tokens[s.tokens.size]'hj).val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  have h_size := scanDoubleQuoted_adds_one_token s s_dq h_dq
  generalize h_gen : (s_dq.tokens[s.tokens.size]'hj).val = tok
  unfold scanDoubleQuoted at h_dq
  simp only [bind, Except.bind] at h_dq
  split at h_dq <;> try contradiction
  rename_i heq
  have h_collect := collectDoubleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h_dq
  · split at h_dq <;> try contradiction
    injection h_dq with h_eq; subst h_eq
    unfold ScannerState.emitAt at h_gen; dsimp only [] at h_gen
    simp only [Array.getElem_push] at h_gen
    rw [h_collect, h_adv] at h_gen
    simp only [Nat.lt_irrefl] at h_gen
    subst h_gen; trivial
  · injection h_dq with h_eq; subst h_eq
    unfold ScannerState.emitAt at h_gen; dsimp only [] at h_gen
    simp only [Array.getElem_push] at h_gen
    rw [h_collect, h_adv] at h_gen
    simp only [Nat.lt_irrefl] at h_gen
    subst h_gen; trivial

set_option maxHeartbeats 1600000 in
theorem scanSingleQuoted_psv_match (s s_sq : ScannerState)
    (h_sq : scanSingleQuoted s = .ok s_sq)
    (hj : s.tokens.size < s_sq.tokens.size) :
    match (s_sq.tokens[s.tokens.size]'hj).val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  have h_size := scanSingleQuoted_adds_one_token s s_sq h_sq
  generalize h_gen : (s_sq.tokens[s.tokens.size]'hj).val = tok
  unfold scanSingleQuoted at h_sq
  simp only [bind, Except.bind] at h_sq
  split at h_sq <;> try contradiction
  rename_i heq
  have h_collect := collectSingleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h_sq
  · split at h_sq <;> try contradiction
    injection h_sq with h_eq; subst h_eq
    unfold ScannerState.emitAt at h_gen; dsimp only [] at h_gen
    simp only [Array.getElem_push] at h_gen
    rw [h_collect, h_adv] at h_gen
    simp only [Nat.lt_irrefl] at h_gen
    subst h_gen; trivial
  · injection h_sq with h_eq; subst h_eq
    unfold ScannerState.emitAt at h_gen; dsimp only [] at h_gen
    simp only [Array.getElem_push] at h_gen
    rw [h_collect, h_adv] at h_gen
    simp only [Nat.lt_irrefl] at h_gen
    subst h_gen; trivial

/-! ## dispatchContent preserves PlainScalarsValid -/

set_option maxHeartbeats 800000 in
theorem dispatchContent_preserves_PlainScalarsValid
    (s : ScannerState) (c : Char) (h_old : PlainScalarsValid s.tokens)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchContent s c = .ok s') :
    PlainScalarsValid s'.tokens := by
  apply PlainScalarsValid_of_prefix_and_new s.tokens s'.tokens h_old
    (dispatchContent_tokens_mono s c s' h_ok)
  · intro i hi; exact dispatchContent_preserves_prefix s c s' h_ok i hi
  · -- New tokens: determine which sub-function was called
    unfold scanNextToken_dispatchContent at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · -- c == '&': .anchor — not plain scalar
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      intro j hj hge
      have : j = s.tokens.size := by
        have := scanAnchorOrAlias_adds_one_token s true; omega
      subst this
      exact psv_match_of_ne_plain _ _ hj (fun c => by
        unfold scanAnchorOrAlias ScannerState.emitAt
        simp only [collectAnchorNameLoop_preserves_tokens, advance_preserves_tokens, Array.getElem_push]
        split
        · omega
        · simp)
    · split at h_ok
      · -- c == '*': .alias — not plain scalar
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        intro j hj hge
        have : j = s.tokens.size := by
          have := scanAnchorOrAlias_adds_one_token s false; omega
        subst this
        exact psv_match_of_ne_plain _ _ hj (fun c => by
          unfold scanAnchorOrAlias ScannerState.emitAt
          simp only [collectAnchorNameLoop_preserves_tokens, advance_preserves_tokens, Array.getElem_push]
          split
          · omega
          · simp)
      · split at h_ok
        · -- c == '!': .tag — not plain scalar
          simp only [Except.ok.injEq] at h_ok
          intro j hj hge
          have hj_eq : j = s.tokens.size := by
            rw [← h_ok] at hj; have := scanTag_adds_one_token s; omega
          subst hj_eq
          simp only [← h_ok]
          exact scanTag_psv_match s (by have := scanTag_adds_one_token s; omega)
        · split at h_ok
          · -- c == '|' || '>': .scalar _ .literal/.folded — not .plain
            split at h_ok <;> try contradiction
            simp only [Except.ok.injEq] at h_ok; subst h_ok
            rename_i s_bs h_bs
            intro j hj hge
            have : j = s.tokens.size := by
              have := scanBlockScalar_adds_one_token s s_bs h_bs; omega
            subst this
            exact scanBlockScalar_psv_match s s_bs h_bs hj
          · split at h_ok
            · -- c == '"': .scalar _ .doubleQuoted — not .plain
              split at h_ok <;> try contradiction
              rename_i s_dq h_dq
              split at h_ok <;> (
                simp only [Except.ok.injEq] at h_ok; subst h_ok
                intro j hj hge
                try dsimp only [] at hj ⊢
                have hj_eq : j = s.tokens.size := by
                  have := scanDoubleQuoted_adds_one_token s s_dq h_dq; omega
                subst hj_eq
                exact scanDoubleQuoted_psv_match s s_dq h_dq hj
                )
            · split at h_ok
              · -- c == '\'': .scalar _ .singleQuoted — not .plain
                split at h_ok <;> try contradiction
                rename_i s_sq h_sq
                split at h_ok <;> (
                  simp only [Except.ok.injEq] at h_ok; subst h_ok
                  intro j hj hge
                  try dsimp only [] at hj ⊢
                  have hj_eq : j = s.tokens.size := by
                    have := scanSingleQuoted_adds_one_token s s_sq h_sq; omega
                  subst hj_eq
                  exact scanSingleQuoted_psv_match s s_sq h_sq hj
                  )
              · split at h_ok
                · -- canStartPlainScalar: THE .scalar _ .plain case
                  split at h_ok <;> try contradiction
                  simp only [Except.ok.injEq] at h_ok; subst h_ok
                  rename_i s_ps h_ps
                  intro j hj hge
                  have : j = s.tokens.size := by
                    have := scanPlainScalar_adds_one_token s s_ps h_ps; omega
                  subst this
                  -- B3.4 + monotonicity
                  generalize h_tok : (s_ps.tokens[s.tokens.size]'hj).val = tok
                  cases tok with
                  | scalar content style =>
                    cases style with
                    | plain =>
                      have h_cv := scanPlainScalar_content_valid s s_ps h_ps hj
                      rw [h_tok] at h_cv
                      exact ScalarScannable_any_implies_false _ s.inFlow h_cv
                    | _ => trivial
                  | _ => trivial
                · -- error: unexpectedChar
                  simp at h_ok

/-! ## Other dispatches preserve PlainScalarsValid

These functions only emit structural/flow/block tokens, never `.scalar _ .plain`.
Preservation follows from prefix preservation + the fact that no new plain scalar
tokens are introduced. The sorry's are for characterizing new token values. -/

theorem preprocess_preserves_PlainScalarsValid
    (s s1 : ScannerState) (c : Char)
    (h_old : PlainScalarsValid s.tokens)
    (h_ok : scanNextToken_preprocess s = .ok (some (s1, c))) :
    PlainScalarsValid s1.tokens := by
  apply PlainScalarsValid_of_prefix_and_new s.tokens s1.tokens h_old
    (preprocess_tokens_mono s s1 c h_ok)
  · intro i hi; exact preprocess_preserves_prefix s s1 c h_ok i hi
  · -- New tokens: .blockEnd and .placeholder only
    intro j hj hge
    unfold scanNextToken_preprocess at h_ok
    simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h_ok
    simp only [Except.bind] at h_ok
    split at h_ok
    · contradiction
    · rename_i v heq_skip
      have h_skip := skipToContent_preserves_tokens s v heq_skip
      have h_sizes : v.tokens.size = s.tokens.size := congrArg Array.size h_skip
      split at h_ok
      · simp at h_ok
      · split at h_ok
        · split at h_ok
          · contradiction
          · split at h_ok
            · simp at h_ok
            · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_ok
              obtain ⟨rfl, _⟩ := h_ok
              by_cases h_lt : j < (unwindIndents v v.col).tokens.size
              · -- Token added by unwindIndents
                rw [saveSimpleKey_preserves_prefix _ j
                  (by show j < ({ unwindIndents v v.col with needIndentCheck := false } : ScannerState).tokens.size; exact h_lt)]
                apply psv_of_not_plain
                exact unwindIndents_new_tokens_not_plain v v.col j h_lt (by omega)
              · -- Token added by saveSimpleKey
                have h_ni_tok : ({ unwindIndents v v.col with needIndentCheck := false } : ScannerState).tokens.size = (unwindIndents v v.col).tokens.size := rfl
                apply psv_of_not_plain
                have : j ≥ ({ unwindIndents v v.col with needIndentCheck := false } : ScannerState).tokens.size := by
                  rw [h_ni_tok]; omega
                exact saveSimpleKey_new_tokens_not_plain _ j hj this
        · split at h_ok
          · contradiction
          · split at h_ok
            · simp at h_ok
            · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_ok
              obtain ⟨rfl, _⟩ := h_ok
              apply psv_of_not_plain
              exact saveSimpleKey_new_tokens_not_plain v j hj (by omega)

theorem scanDocumentStart_new_not_plain (s : ScannerState) (j : Nat)
    (hj : j < (scanDocumentStart s).tokens.size) (hge : j ≥ s.tokens.size) :
    match ((scanDocumentStart s).tokens[j]'hj).val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  unfold scanDocumentStart at hj ⊢
  simp only [advanceN_preserves_tokens] at hj ⊢
  have h_sk_tok : ({ unwindIndents s (-1) with simpleKey := { possible := false } } : ScannerState).tokens = (unwindIndents s (-1)).tokens := rfl
  by_cases h_lt : j < (unwindIndents s (-1)).tokens.size
  · simp only [emit_preserves_tokens_at
        { unwindIndents s (-1) with simpleKey := { possible := false } }
        .documentStart j (by rw [h_sk_tok]; exact h_lt)]
    exact psv_of_not_plain _ (unwindIndents_new_tokens_not_plain s (-1) j h_lt hge)
  · have h_j : j = (unwindIndents s (-1)).tokens.size := by rw [emit_tokens_size, h_sk_tok] at hj; omega
    subst h_j; unfold ScannerState.emit; simp only [Array.getElem_push_eq]

-- All OK branches of scanDocumentEnd return the same `result`, whose tokens are
-- exactly the emit .documentEnd of the unwindIndents state.
set_option maxHeartbeats 800000 in
theorem scanDocumentEnd_tokens_eq (s : ScannerState) (s' : ScannerState)
    (h_de : scanDocumentEnd s = .ok s') :
    s'.tokens = ({ unwindIndents s (-1) with simpleKey := { possible := false } }.emit .documentEnd).tokens := by
  unfold scanDocumentEnd at h_de
  dsimp only [] at h_de
  simp only [bind, Except.bind] at h_de
  split at h_de
  · contradiction
  · split at h_de
    · contradiction
    · split at h_de
      · split at h_de
        · contradiction
        · injection h_de with h_eq; subst h_eq
          simp only [advanceN_preserves_tokens]
      · split at h_de
        · contradiction
        · injection h_de with h_eq; subst h_eq
          simp only [advanceN_preserves_tokens]
      · split at h_de
        · split at h_de
          · contradiction
          · injection h_de with h_eq; subst h_eq
            simp only [advanceN_preserves_tokens]
        · contradiction

theorem scanDocumentEnd_new_not_plain (s : ScannerState) (s' : ScannerState)
    (h_de : scanDocumentEnd s = .ok s') (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    match (s'.tokens[j]'hj).val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  have h_tok := scanDocumentEnd_tokens_eq s s' h_de
  simp only [h_tok] at hj ⊢
  have h_sk_tok : ({ unwindIndents s (-1) with simpleKey := { possible := false } } : ScannerState).tokens = (unwindIndents s (-1)).tokens := rfl
  by_cases h_lt : j < (unwindIndents s (-1)).tokens.size
  · simp only [emit_preserves_tokens_at
        { unwindIndents s (-1) with simpleKey := { possible := false } }
        .documentEnd j (by rw [h_sk_tok]; exact h_lt)]
    exact psv_of_not_plain _ (unwindIndents_new_tokens_not_plain s (-1) j h_lt hge)
  · have h_j : j = (unwindIndents s (-1)).tokens.size := by rw [emit_tokens_size, h_sk_tok] at hj; omega
    subst h_j; unfold ScannerState.emit; simp only [Array.getElem_push_eq]

set_option maxHeartbeats 800000 in
theorem scanYamlDirective_new_not_plain (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (h : scanYamlDirective s s_after_ws startPos = .ok s')
    (h_ws : s_after_ws.tokens = s.tokens) (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    match (s'.tokens[j]'hj).val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  unfold scanYamlDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · split at h
    · -- some '#'
      split at h
      · contradiction
      · injection h with h_eq; subst h_eq; dsimp only []
        have h_j : j = s.tokens.size := by
          simp only [emitAt_tokens_size, skipWhitespace_preserves_tokens,
            collectVersionMinorLoop_preserves_tokens,
            collectVersionMajorLoop_preserves_tokens, h_ws] at hj; omega
        subst h_j
        simp only [ScannerState.emitAt, skipWhitespace_preserves_tokens,
          collectVersionMinorLoop_preserves_tokens,
          collectVersionMajorLoop_preserves_tokens, h_ws, Array.getElem_push_eq]
    · -- some c, not '#'
      split at h
      · contradiction
      · injection h with h_eq; subst h_eq; dsimp only []
        have h_j : j = s.tokens.size := by
          simp only [emitAt_tokens_size, skipWhitespace_preserves_tokens,
            collectVersionMinorLoop_preserves_tokens,
            collectVersionMajorLoop_preserves_tokens, h_ws] at hj; omega
        subst h_j
        simp only [ScannerState.emitAt, skipWhitespace_preserves_tokens,
          collectVersionMinorLoop_preserves_tokens,
          collectVersionMajorLoop_preserves_tokens, h_ws, Array.getElem_push_eq]
    · -- none
      injection h with h_eq; subst h_eq; dsimp only []
      have h_j : j = s.tokens.size := by
        simp only [emitAt_tokens_size, skipWhitespace_preserves_tokens,
          collectVersionMinorLoop_preserves_tokens,
          collectVersionMajorLoop_preserves_tokens, h_ws] at hj; omega
      subst h_j
      simp only [ScannerState.emitAt, skipWhitespace_preserves_tokens,
        collectVersionMinorLoop_preserves_tokens,
        collectVersionMajorLoop_preserves_tokens, h_ws, Array.getElem_push_eq]

theorem scanTagDirective_new_not_plain (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (h : scanTagDirective s s_after_ws startPos = .ok s')
    (h_ws : s_after_ws.tokens = s.tokens) (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    match (s'.tokens[j]'hj).val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  unfold scanTagDirective at h
  dsimp only [] at h
  injection h with h_eq; subst h_eq; dsimp only []
  have h_j : j = s.tokens.size := by
    simp only [emitAt_tokens_size, collectTagPrefixLoop_preserves_tokens,
      skipWhitespace_preserves_tokens, collectTagHandleDirectiveLoop_preserves_tokens,
      h_ws] at hj; omega
  subst h_j
  simp only [ScannerState.emitAt, collectTagPrefixLoop_preserves_tokens,
    skipWhitespace_preserves_tokens, collectTagHandleDirectiveLoop_preserves_tokens,
    h_ws, Array.getElem_push_eq]

theorem scanDirective_new_not_plain (s : ScannerState) (s' : ScannerState)
    (h_dir : scanDirective s = .ok s') (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    match (s'.tokens[j]'hj).val with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  unfold scanDirective at h_dir
  dsimp only [] at h_dir
  split at h_dir
  any_goals contradiction
  have h_ws_tok : (skipWhitespace (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2).tokens = s.tokens := by
    rw [skipWhitespace_preserves_tokens, collectDirectiveNameLoop_preserves_tokens, advance_preserves_tokens]
  split at h_dir
  · -- YAML directive
    exact scanYamlDirective_new_not_plain s _ _ s' h_dir h_ws_tok j hj hge
  · split at h_dir
    · -- TAG directive
      exact scanTagDirective_new_not_plain s _ _ s' h_dir h_ws_tok j hj hge
    · -- unknown directive: tokens preserved
      injection h_dir with h_eq; subst h_eq; exfalso
      rw [skipToEndOfLine_preserves_tokens, h_ws_tok] at hj; omega

set_option maxHeartbeats 800000 in
theorem dispatchStructural_preserves_PlainScalarsValid
    (s : ScannerState) (c : Char) (h_old : PlainScalarsValid s.tokens)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchStructural s c = .ok (some s')) :
    PlainScalarsValid s'.tokens := by
  apply PlainScalarsValid_of_prefix_and_new s.tokens s'.tokens h_old
    (dispatchStructural_tokens_mono s c s' h_ok)
  · intro i hi; exact dispatchStructural_preserves_prefix s c s' h_ok i (by omega)
  · intro j hj hge
    unfold scanNextToken_dispatchStructural at h_ok
    simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h_ok
    simp only [Except.bind] at h_ok
    repeat (any_goals (split at h_ok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    -- scanDocumentStart goals: substed directly
    all_goals (try exact scanDocumentStart_new_not_plain s j hj hge)
    -- scanDocumentEnd goals: have heq✝ : scanDocumentEnd s = .ok v✝
    all_goals (try (rename_i v h_de; exact scanDocumentEnd_new_not_plain s v h_de j hj hge))
    -- scanDirective goals: have heq✝ : scanDirective s = .ok v✝
    all_goals (rename_i v h_dir; exact scanDirective_new_not_plain s v h_dir j hj hge)

theorem dispatchFlowIndicators_preserves_PlainScalarsValid
    (s : ScannerState) (c : Char) (h_old : PlainScalarsValid s.tokens)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    PlainScalarsValid s'.tokens := by
  apply PlainScalarsValid_of_prefix_and_new s.tokens s'.tokens h_old
    (dispatchFlowIndicators_tokens_mono s c s' h_ok)
  · intro i hi; exact dispatchFlowIndicators_preserves_prefix s c s' h_ok i (by omega)
  · intro j hj hge
    unfold scanNextToken_dispatchFlowIndicators at h_ok
    simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h_ok
    simp only [Except.bind] at h_ok
    repeat (any_goals (split at h_ok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    -- scanFlowSequenceStart: one new token = .flowSequenceStart
    · have h_j : j = s.tokens.size := by
        have := scanFlowSequenceStart_adds_one_token s; omega
      subst h_j
      unfold scanFlowSequenceStart ScannerState.emit
      simp only [advance_preserves_tokens, Array.getElem_push_eq]
    -- scanFlowSequenceEnd
    · have h_j : j = s.tokens.size := by
        have := scanFlowSequenceEnd_adds_one_token s; omega
      subst h_j
      unfold scanFlowSequenceEnd ScannerState.emit
      simp only [advance_preserves_tokens, Array.getElem_push_eq]
    -- scanFlowMappingStart
    · have h_j : j = s.tokens.size := by
        have := scanFlowMappingStart_adds_one_token s; omega
      subst h_j
      unfold scanFlowMappingStart ScannerState.emit
      simp only [advance_preserves_tokens, Array.getElem_push_eq]
    -- scanFlowMappingEnd
    · have h_j : j = s.tokens.size := by
        have := scanFlowMappingEnd_adds_one_token s; omega
      subst h_j
      unfold scanFlowMappingEnd ScannerState.emit
      simp only [advance_preserves_tokens, Array.getElem_push_eq]
    -- scanFlowEntry
    · rename_i s_fe h_fe
      have h_tok : s_fe.tokens = (s.emit .flowEntry).advance.tokens := by
        unfold scanFlowEntry at h_fe
        simp only [bind, Except.bind] at h_fe
        split at h_fe
        · split at h_fe
          · contradiction
          · injection h_fe with h_eq; subst h_eq; rfl
        · injection h_fe with h_eq; subst h_eq; rfl
      simp only [h_tok, advance_preserves_tokens]
      have h_j : j = s.tokens.size := by
        rw [h_tok, advance_preserves_tokens, emit_tokens_size] at hj; omega
      subst h_j
      unfold ScannerState.emit
      simp [Array.getElem_push_eq]

/-! ### Block indicators: helper lemmas for dispatchBlockIndicators -/

theorem PlainScalarsValid_setIfInBounds_non_plain
    (tokens : Array (Positioned YamlToken))
    (h_old : PlainScalarsValid tokens)
    (idx : Nat) (val : Positioned YamlToken)
    (h_np : match val.val with | .scalar _ .plain => False | _ => True) :
    PlainScalarsValid (tokens.setIfInBounds idx val) := by
  intro i hi
  have h_i_lt : i < tokens.size := by
    rw [Array.size_setIfInBounds] at hi; exact hi
  rw [Array.getElem_setIfInBounds h_i_lt]
  by_cases h_eq : idx = i
  · subst h_eq; simp only [↓reduceIte]
    generalize h_v : val.val = v at h_np ⊢
    cases v with
    | scalar content style =>
      cases style with
      | plain => exact absurd h_np (by simp)
      | _ => trivial
    | _ => trivial
  · simp only [h_eq, ↓reduceIte]; exact h_old i h_i_lt

theorem PlainScalarsValid_push_non_plain
    (tokens : Array (Positioned YamlToken))
    (h_old : PlainScalarsValid tokens)
    (val : Positioned YamlToken)
    (h_np : match val.val with | .scalar _ .plain => False | _ => True) :
    PlainScalarsValid (tokens.push val) := by
  intro i hi
  by_cases h_lt : i < tokens.size
  · rw [show (tokens.push val)[i] = tokens[i] from Array.getElem_push_lt ..]
    exact h_old i h_lt
  · have h_eq : i = tokens.size := by simp [Array.size_push] at hi; omega
    subst h_eq; simp only [Array.getElem_push_eq]
    generalize h_v : val.val = v at h_np ⊢
    cases v with
    | scalar content style =>
      cases style with
      | plain => exact absurd h_np (by simp)
      | _ => trivial
    | _ => trivial

theorem pushSequenceIndent_preserves_PlainScalarsValid
    (s : ScannerState) (col : Int) (h_old : PlainScalarsValid s.tokens) :
    PlainScalarsValid (pushSequenceIndent s col).tokens := by
  unfold pushSequenceIndent
  split
  · show PlainScalarsValid ({ s.emit .blockSequenceStart with indents := _ }.tokens)
    exact PlainScalarsValid_push_non_plain s.tokens h_old
      ⟨s.currentPos, .blockSequenceStart⟩ (by trivial)
  · exact h_old

theorem pushMappingIndent_preserves_PlainScalarsValid
    (s : ScannerState) (col : Int) (h_old : PlainScalarsValid s.tokens) :
    PlainScalarsValid (pushMappingIndent s col).tokens := by
  unfold pushMappingIndent
  split
  · show PlainScalarsValid ({ s.emit .blockMappingStart with indents := _ }.tokens)
    exact PlainScalarsValid_push_non_plain s.tokens h_old
      ⟨s.currentPos, .blockMappingStart⟩ (by trivial)
  · exact h_old

set_option maxHeartbeats 400000 in
theorem scanBlockEntry_preserves_PlainScalarsValid
    (s : ScannerState) (s' : ScannerState)
    (h_old : PlainScalarsValid s.tokens)
    (h_ok : scanBlockEntry s = .ok s') :
    PlainScalarsValid s'.tokens := by
  unfold scanBlockEntry at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · contradiction
    · injection h_ok with h_ok; subst h_ok
      simp only [advance_preserves_tokens]
      apply PlainScalarsValid_push_non_plain _ _ _ (by trivial)
      exact pushSequenceIndent_preserves_PlainScalarsValid s s.col h_old
  · injection h_ok with h_ok; subst h_ok
    simp only [advance_preserves_tokens]
    apply PlainScalarsValid_push_non_plain _ _ _ (by trivial)
    exact h_old

set_option maxHeartbeats 800000 in
theorem scanKey_preserves_PlainScalarsValid
    (s : ScannerState) (s' : ScannerState)
    (h_old : PlainScalarsValid s.tokens)
    (h_ok : scanKey s = .ok s') :
    PlainScalarsValid s'.tokens := by
  unfold scanKey at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · split at h_ok
      · contradiction
      · injection h_ok with h_ok; subst h_ok
        simp only [advance_preserves_tokens]
        apply PlainScalarsValid_push_non_plain _ _ _ (by trivial)
        exact pushMappingIndent_preserves_PlainScalarsValid s s.col h_old
    · injection h_ok with h_ok; subst h_ok
      simp only [advance_preserves_tokens]
      apply PlainScalarsValid_push_non_plain _ _ _ (by trivial)
      exact pushMappingIndent_preserves_PlainScalarsValid s s.col h_old
  · split at h_ok
    · split at h_ok
      · contradiction
      · injection h_ok with h_ok; subst h_ok
        simp only [advance_preserves_tokens]
        apply PlainScalarsValid_push_non_plain _ _ _ (by trivial); exact h_old
    · injection h_ok with h_ok; subst h_ok
      simp only [advance_preserves_tokens]
      apply PlainScalarsValid_push_non_plain _ _ _ (by trivial); exact h_old

theorem scanValuePrepare_preserves_PlainScalarsValid
    (s : ScannerState) (h_old : PlainScalarsValid s.tokens) :
    PlainScalarsValid (scanValuePrepare s).tokens := by
  unfold scanValuePrepare
  split
  · split
    · split
      · apply PlainScalarsValid_setIfInBounds_non_plain _ _ _ _ (by trivial)
        apply PlainScalarsValid_setIfInBounds_non_plain _ _ _ _ (by trivial)
        exact h_old
      · apply PlainScalarsValid_setIfInBounds_non_plain _ _ _ _ (by trivial)
        exact h_old
    · apply PlainScalarsValid_setIfInBounds_non_plain _ _ _ _ (by trivial)
      exact h_old
  · split
    · exact h_old
    · split
      · exact pushMappingIndent_preserves_PlainScalarsValid s s.col h_old
      · exact h_old

set_option maxHeartbeats 800000 in
theorem scanValue_preserves_PlainScalarsValid
    (s : ScannerState) (s' : ScannerState)
    (h_old : PlainScalarsValid s.tokens)
    (h_ok : scanValue s = .ok s') :
    PlainScalarsValid s'.tokens := by
  unfold scanValue scanValueTabCheck at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · contradiction
  · split at h_ok
    · contradiction
    · injection h_ok with h_ok; subst h_ok
      simp only [advance_preserves_tokens]
      apply PlainScalarsValid_push_non_plain _ _ _ (by trivial)
      have h_ck := scanValueClearKey_preserves_tokens s
      have h_ck_psv : PlainScalarsValid (scanValueClearKey s).tokens := by rw [h_ck]; exact h_old
      exact scanValuePrepare_preserves_PlainScalarsValid (scanValueClearKey s) h_ck_psv

set_option maxHeartbeats 400000 in
/-- Block indicators: uses `setIfInBounds` which may overwrite tokens, but only
    with `.key`/`.blockMappingStart` (never `.scalar _ .plain`).
    Separate treatment needed because prefix preservation has SimpleKeyAbove condition. -/
theorem dispatchBlockIndicators_preserves_PlainScalarsValid
    (s : ScannerState) (c : Char) (h_old : PlainScalarsValid s.tokens)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    PlainScalarsValid s'.tokens := by
  unfold scanNextToken_dispatchBlockIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · contradiction
    · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact scanBlockEntry_preserves_PlainScalarsValid s _ h_old (by assumption)
  · split at h_ok
    · split at h_ok
      · contradiction
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanKey_preserves_PlainScalarsValid s _ h_old (by assumption)
    · split at h_ok
      · split at h_ok
        · contradiction
        · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
          exact scanValue_preserves_PlainScalarsValid s _ h_old (by assumption)
      · simp at h_ok

/-! ## scanNextToken preserves PlainScalarsValid -/

theorem allowDir_ite_preserves_PlainScalarsValid (s : ScannerState)
    (h : PlainScalarsValid s.tokens) :
    PlainScalarsValid (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true }
    else s).tokens := by
  split <;> exact h

set_option maxHeartbeats 400000 in
theorem scanNextToken_preserves_PlainScalarsValid :
    ∀ (s s' : ScannerState),
      PlainScalarsValid s.tokens →
      scanNextToken s = .ok (some s') →
      PlainScalarsValid s'.tokens := by
  intro s s' h_old h_ok
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> (try (simp at h_ok; done))
  split at h_ok <;> (try (simp at h_ok; done))
  rename_i s2 c h_pre
  have h_old2 := preprocess_preserves_PlainScalarsValid s s2 c h_old h_pre
  split at h_ok <;> (try (simp at h_ok; done))
  split at h_ok
  · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact dispatchStructural_preserves_PlainScalarsValid s2 c h_old2 _ (by assumption)
  · have h_old3 := allowDir_ite_preserves_PlainScalarsValid s2 h_old2
    split at h_ok <;> (try (simp at h_ok; done))
    split at h_ok
    · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact dispatchFlowIndicators_preserves_PlainScalarsValid _ c h_old3 _ (by assumption)
    · split at h_ok <;> (try (simp at h_ok; done))
      split at h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchBlockIndicators_preserves_PlainScalarsValid _ c h_old3 _ (by assumption)
      · split at h_ok <;> (try (simp at h_ok; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchContent_preserves_PlainScalarsValid _ c h_old3 _ (by assumption)

/-! ## scanLoop preserves PlainScalarsValid -/

theorem finalEmit_preserves_PlainScalarsValid (s : ScannerState)
    (h : PlainScalarsValid s.tokens) :
    PlainScalarsValid ((unwindIndents s (-1)).emit .streamEnd).tokens := by
  apply PlainScalarsValid_of_prefix_and_new s.tokens _ h (by
    have h_uw := unwindIndents_adds_tokens s (-1); rw [emit_tokens_size]; omega)
  · -- prefix preservation
    intro i hi
    rw [emit_preserves_tokens_at _ .streamEnd i (by
      have h_uw := unwindIndents_adds_tokens s (-1); omega)]
    exact unwindIndents_preserves_prefix s (-1) i hi
  · -- new tokens are not plain
    intro j hj hge
    by_cases h_lt : j < (unwindIndents s (-1)).tokens.size
    · rw [emit_preserves_tokens_at _ .streamEnd j h_lt]
      exact psv_of_not_plain _ (unwindIndents_new_tokens_not_plain s (-1) j h_lt hge)
    · have h_j : j = (unwindIndents s (-1)).tokens.size := by
        rw [emit_tokens_size] at hj; omega
      subst h_j; unfold ScannerState.emit; simp only [Array.getElem_push_eq]

theorem scanLoop_preserves_PlainScalarsValid
    (s : ScannerState) (fuel : Nat)
    (tokens : Array (Positioned YamlToken))
    (h_old : PlainScalarsValid s.tokens)
    (h_ok : scanLoop s fuel = .ok tokens) :
    PlainScalarsValid tokens := by
  induction fuel generalizing s with
  | zero => simp [scanLoop] at h_ok
  | succ fuel' ih =>
    simp only [scanLoop] at h_ok
    split at h_ok
    · simp at h_ok
    · split at h_ok <;> try (simp at h_ok; done)
      split at h_ok <;> try (simp at h_ok; done)
      injection h_ok with h_eq; rw [← h_eq]
      exact finalEmit_preserves_PlainScalarsValid s h_old
    · rename_i s' h_snt
      exact ih s'
        (scanNextToken_preserves_PlainScalarsValid s s' h_old h_snt)
        h_ok

/-! ## scan and scanFiltered -/

theorem scan_all_plain_scalars_valid (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    PlainScalarsValid tokens := by
  unfold scan at h
  simp only [] at h
  have h_init : PlainScalarsValid (match (ScannerState.mk' input |>.emit .streamStart).peek? with
      | some '\uFEFF' => (ScannerState.mk' input |>.emit .streamStart).advance
      | _ => ScannerState.mk' input |>.emit .streamStart).tokens := by
    have h_tok_eq : (match (ScannerState.mk' input |>.emit .streamStart).peek? with
        | some '\uFEFF' => (ScannerState.mk' input |>.emit .streamStart).advance
        | _ => ScannerState.mk' input |>.emit .streamStart).tokens =
        (ScannerState.mk' input |>.emit .streamStart).tokens := by
      split
      · exact advance_preserves_tokens _
      · rfl
    rw [h_tok_eq]
    intro i hi
    have h_size : (ScannerState.mk' input |>.emit .streamStart).tokens.size = 1 := by
      rw [emit_tokens_size]; simp [ScannerState.mk']
    rw [h_size] at hi
    have h_i0 : i = 0 := by omega
    subst h_i0
    -- The only token is .streamStart, which is not .scalar _ .plain
    have h_emit_val : ((ScannerState.mk' input |>.emit .streamStart).tokens[0]'(by
        rw [h_size]; omega)).val = .streamStart := by
      simp [ScannerState.emit, ScannerState.mk']
    simp only [h_emit_val]
  exact scanLoop_preserves_PlainScalarsValid _ _ _ h_init h

/-! ## Main theorem (B3.5) -/

/-- Every plain scalar token emitted by the scanner satisfies `ScalarScannable _ false`.

    This is the global scanner contract for plain scalars. Combined with
    `ScalarScannable_true_implies_false`, it also implies `ScalarScannable _ true`
    for tokens emitted in flow context (a fact used by Phase C).

    **Status**: The chain architecture is complete. Remaining sorries are for
    non-plain token characterization (structurally obvious) and scan setup. -/
theorem scan_plain_scalar_valid (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens)
    (i : Nat) (hi : i < tokens.size) :
    match (tokens[i]'hi).val with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  unfold Scanner.scanFiltered at h
  split at h
  · rename_i all_tokens h_scan
    have h_all := scan_all_plain_scalars_valid input all_tokens h_scan
    injection h with h_eq; subst h_eq
    -- Each filtered token is an element of all_tokens; PlainScalarsValid transfers.
    have h_in : (all_tokens.filter fun t => t.val != YamlToken.placeholder)[i] ∈ all_tokens := by
      exact (Array.mem_filter.mp (Array.getElem_mem hi)).1
    obtain ⟨j, hj_lt, hj_eq⟩ := Array.mem_iff_getElem.mp h_in
    rw [← hj_eq]
    exact h_all j hj_lt
  · simp at h

end Lean4Yaml.Proofs.ScannerPlainScalarValid
