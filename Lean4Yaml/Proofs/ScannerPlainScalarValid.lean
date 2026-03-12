/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Grammar
import Lean4Yaml.Proofs.ScannerPlainScalar
import Lean4Yaml.Proofs.ScannerCorrectness
import Lean4Yaml.Proofs.ScannerFlowCollection

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
    | nil =>
      intro h
      by_cases hexc : c = '-' ∨ c = '?' ∨ c = ':'
      · simp [hexc]
      · simp [hexc] at h ⊢
        exact canStartPlainScalarProp_true_implies_false c none h
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
    (h_ok : scanPlainScalar s = .ok s')
    (h_canStart : ∃ c, s.peek? = some c ∧
        canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true) :
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
        have h_cv := scanPlainScalar_content_valid s s' h_ok h_canStart hj
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
    (s : ScannerState) (c : Char) (h_peek : s.peek? = some c)
    (h_old : PlainScalarsValid s.tokens)
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
                  have h_cs : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true := by assumption
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
                      have h_cv := scanPlainScalar_content_valid s s_ps h_ps
                        ⟨c, h_peek, h_cs⟩ hj
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

theorem preprocess_peek (s s' : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s', c))) :
    s'.peek? = some c := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            assumption
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            assumption

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

theorem scanDocumentStart_new_tok_not_plain (s : ScannerState) (j : Nat)
    (hj : j < (scanDocumentStart s).tokens.size) (hge : j ≥ s.tokens.size) :
    match ((scanDocumentStart s).tokens[j]'hj).val with
    | .scalar _ .plain => False
    | _ => True := by
  unfold scanDocumentStart at hj ⊢
  simp only [advanceN_preserves_tokens] at hj ⊢
  have h_sk_tok : ({ unwindIndents s (-1) with simpleKey := { possible := false } } : ScannerState).tokens = (unwindIndents s (-1)).tokens := rfl
  by_cases h_lt : j < (unwindIndents s (-1)).tokens.size
  · simp only [emit_preserves_tokens_at
        { unwindIndents s (-1) with simpleKey := { possible := false } }
        .documentStart j (by rw [h_sk_tok]; exact h_lt)]
    exact unwindIndents_new_tokens_not_plain s (-1) j h_lt hge
  · have h_j : j = (unwindIndents s (-1)).tokens.size := by rw [emit_tokens_size, h_sk_tok] at hj; omega
    subst h_j; unfold ScannerState.emit; simp only [Array.getElem_push_eq]

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

theorem scanDocumentEnd_new_tok_not_plain (s : ScannerState) (s' : ScannerState)
    (h_de : scanDocumentEnd s = .ok s') (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    match (s'.tokens[j]'hj).val with
    | .scalar _ .plain => False
    | _ => True := by
  have h_tok := scanDocumentEnd_tokens_eq s s' h_de
  simp only [h_tok] at hj ⊢
  have h_sk_tok : ({ unwindIndents s (-1) with simpleKey := { possible := false } } : ScannerState).tokens = (unwindIndents s (-1)).tokens := rfl
  by_cases h_lt : j < (unwindIndents s (-1)).tokens.size
  · simp only [emit_preserves_tokens_at
        { unwindIndents s (-1) with simpleKey := { possible := false } }
        .documentEnd j (by rw [h_sk_tok]; exact h_lt)]
    exact unwindIndents_new_tokens_not_plain s (-1) j h_lt hge
  · have h_j : j = (unwindIndents s (-1)).tokens.size := by rw [emit_tokens_size, h_sk_tok] at hj; omega
    subst h_j; unfold ScannerState.emit; simp only [Array.getElem_push_eq]

theorem scanYamlDirective_new_tok_not_plain (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (h : scanYamlDirective s s_after_ws startPos = .ok s')
    (h_ws : s_after_ws.tokens = s.tokens) (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    match (s'.tokens[j]'hj).val with
    | .scalar _ .plain => False
    | _ => True := by
  have h_toks : s'.tokens = s.tokens.push ⟨startPos, .versionDirective
    (collectVersionMajorLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).fst.toNat!
    (collectVersionMinorLoop (collectVersionMajorLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).snd ""
      (s.inputEnd - (collectVersionMajorLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).snd.offset)).fst.toNat!⟩ := by
    unfold scanYamlDirective at h
    dsimp only [] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · contradiction
    · split at h
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq
          simp only [ScannerState.emitAt, skipWhitespace_preserves_tokens,
            collectVersionMinorLoop_preserves_tokens,
            collectVersionMajorLoop_preserves_tokens, h_ws]
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq
          simp only [ScannerState.emitAt, skipWhitespace_preserves_tokens,
            collectVersionMinorLoop_preserves_tokens,
            collectVersionMajorLoop_preserves_tokens, h_ws]
      · injection h with h_eq; subst h_eq
        simp only [ScannerState.emitAt, skipWhitespace_preserves_tokens,
          collectVersionMinorLoop_preserves_tokens,
          collectVersionMajorLoop_preserves_tokens, h_ws]
  simp only [h_toks, Array.size_push] at hj
  have h_j : j = s.tokens.size := by omega
  simp only [h_toks, h_j, Array.getElem_push_eq]

theorem scanTagDirective_new_tok_not_plain (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (h : scanTagDirective s s_after_ws startPos = .ok s')
    (h_ws : s_after_ws.tokens = s.tokens) (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    match (s'.tokens[j]'hj).val with
    | .scalar _ .plain => False
    | _ => True := by
  unfold scanTagDirective at h
  dsimp only [] at h
  injection h with h_eq
  have h_toks : s'.tokens = s.tokens.push ⟨startPos, .tagDirective
    (collectTagHandleDirectiveLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).fst
    (collectTagPrefixLoop (skipWhitespace (collectTagHandleDirectiveLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).snd) ""
      (s.inputEnd - (skipWhitespace (collectTagHandleDirectiveLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).snd).offset)).fst⟩ := by
    subst h_eq
    simp only [ScannerState.emitAt, collectTagPrefixLoop_preserves_tokens,
      skipWhitespace_preserves_tokens, collectTagHandleDirectiveLoop_preserves_tokens, h_ws]
  simp only [h_toks, Array.size_push] at hj
  have h_j : j = s.tokens.size := by omega
  simp only [h_toks, h_j, Array.getElem_push_eq]

theorem scanDirective_new_tok_not_plain (s : ScannerState) (s' : ScannerState)
    (h_dir : scanDirective s = .ok s') (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    match (s'.tokens[j]'hj).val with
    | .scalar _ .plain => False
    | _ => True := by
  unfold scanDirective at h_dir
  dsimp only [] at h_dir
  split at h_dir
  any_goals contradiction
  have h_ws_tok : (skipWhitespace (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2).tokens = s.tokens := by
    rw [skipWhitespace_preserves_tokens, collectDirectiveNameLoop_preserves_tokens, advance_preserves_tokens]
  split at h_dir
  · exact scanYamlDirective_new_tok_not_plain s _ _ s' h_dir h_ws_tok j hj hge
  · split at h_dir
    · exact scanTagDirective_new_tok_not_plain s _ _ s' h_dir h_ws_tok j hj hge
    · injection h_dir with h_eq; subst h_eq; exfalso
      rw [skipToEndOfLine_preserves_tokens, h_ws_tok] at hj; omega

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
  have h_peek2 := preprocess_peek s s2 c h_pre
  split at h_ok <;> (try (simp at h_ok; done))
  split at h_ok
  · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact dispatchStructural_preserves_PlainScalarsValid s2 c h_old2 _ (by assumption)
  · have h_old3 := allowDir_ite_preserves_PlainScalarsValid s2 h_old2
    have h_peek3 : (if s2.allowDirectives then
        { s2 with allowDirectives := false, documentEverStarted := true }
      else s2).peek? = some c := by split <;> exact h_peek2
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
        exact dispatchContent_preserves_PlainScalarsValid _ c h_peek3 h_old3 _ (by assumption)

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

/-! ## Flow-Aware Plain Scalar Validity (B3.5+)

Extends B3.5's `PlainScalarsValid` to additionally track flow-context
scalar validity through the scan chain. Proves `scan_flow_aware_psv`:
the scanner output satisfies `FlowAwarePSV`.

### Architecture

`FlowAwarePSV tokens ≡ PlainScalarsValid tokens ∧ FlowContextPSV tokens`

- `PlainScalarsValid` (B3.5): `ScalarScannable _ false` for every plain scalar
- `FlowContextPSV` (new): `ScalarScannable _ true` for plain scalars at `flowNesting > 0`

Two additional invariants are threaded through the scan chain:

1. `FlowContextPSV s.tokens` — flow-context scalars satisfy `ScalarScannable _ true`
2. `FlowNestingInv s` — `flowNesting s.tokens s.tokens.size = s.flowLevel`

The `FlowNestingInv` connects the token-array flow depth to the scanner
state's `flowLevel`, enabling B3.4's `ScalarScannable _ s.inFlow` to
discharge `FlowContextPSV` for new plain scalar tokens at `scanPlainScalar`.
-/

/-- Flow nesting depth at position `i` in the token array.
    Counts unmatched flow-start tokens (`flowSequenceStart`, `flowMappingStart`)
    before position `i`, subtracting flow-end tokens. Uses natural number
    subtraction (saturating at 0) for well-formed token streams. -/
def flowNesting (tokens : Array (Positioned YamlToken)) (i : Nat) : Nat :=
  go tokens 0 i 0
where
  go (tokens : Array (Positioned YamlToken)) (pos target depth : Nat) : Nat :=
    if pos ≥ target then depth
    else if h : pos < tokens.size then
      let depth' := match (tokens[pos]'h).val with
        | .flowSequenceStart | .flowMappingStart => depth + 1
        | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
        | _ => depth
      go tokens (pos + 1) target depth'
    else depth
  termination_by target - pos

/-- Plain scalars at flow-nesting positions satisfy `ScalarScannable _ true`. -/
def FlowContextPSV (tokens : Array (Positioned YamlToken)) : Prop :=
  ∀ i (hi : i < tokens.size),
    flowNesting tokens i > 0 →
    match (tokens[i]'hi).val with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ true
    | _ => True

/-- Flow-aware extension of `PlainScalarsValid`.
    At positions where `flowNesting > 0`, plain scalar tokens additionally
    satisfy `ScalarScannable _ true`. -/
def FlowAwarePSV (tokens : Array (Positioned YamlToken)) : Prop :=
  PlainScalarsValid tokens ∧ FlowContextPSV tokens

/-- `flowNesting` tracks scanner `flowLevel` in the token array. -/
def FlowNestingInv (s : ScannerState) : Prop :=
  flowNesting s.tokens s.tokens.size = s.flowLevel

/-! ### flowNesting stability -/

theorem FlowContextPSV_empty : FlowContextPSV #[] :=
  fun _ hi => absurd hi (by simp [Array.size])

/-- `flowNesting.go` is stable under prefix-preserving array extension.
    When iterating up to `target ≤ old.size`, extending the array
    doesn't change the result because only prefix elements are examined.

    **Proof sketch**: Induction on `target - pos`. At each step, both
    `go new pos target depth` and `go old pos target depth` inspect
    `tokens[pos].val` (identical by `h_prefix_val` since `pos < old.size`),
    compute the same `depth'`, and recurse with `pos + 1`. -/
theorem flowNesting_go_prefix_stable
    (old new : Array (Positioned YamlToken))
    (h_mono : old.size ≤ new.size)
    (h_prefix_val : ∀ j (hj : j < old.size),
      (new[j]'(by omega)).val = (old[j]).val)
    (pos target depth : Nat) (h_target : target ≤ old.size) :
    flowNesting.go new pos target depth = flowNesting.go old pos target depth := by
  generalize hn : target - pos = n
  induction n generalizing pos depth with
  | zero =>
    have hge : pos ≥ target := by omega
    simp only [flowNesting.go, hge, ↓reduceIte]
  | succ n ih =>
    by_cases hge : pos ≥ target
    · simp only [flowNesting.go, hge, ↓reduceIte]
    · have h_pos_old : pos < old.size := by omega
      have h_pos_new : pos < new.size := by omega
      have h_val_eq : (new[pos]'h_pos_new).val = (old[pos]'h_pos_old).val :=
        h_prefix_val pos h_pos_old
      unfold flowNesting.go
      simp only [eq_false (show ¬(pos ≥ target) by omega), ite_false,
        eq_true h_pos_new, eq_true h_pos_old, dite_true, h_val_eq]
      exact ih (pos + 1) _ (by omega)

/-- `flowNesting` at positions `≤ old.size` is unchanged by array extension. -/
theorem flowNesting_prefix_stable
    (old new : Array (Positioned YamlToken))
    (h_mono : old.size ≤ new.size)
    (h_prefix_val : ∀ j (hj : j < old.size),
      (new[j]'(by omega)).val = (old[j]).val)
    (i : Nat) (hi : i ≤ old.size) :
    flowNesting new i = flowNesting old i := by
  unfold flowNesting
  exact flowNesting_go_prefix_stable old new h_mono h_prefix_val 0 i 0 hi

/-! ### FlowContextPSV extension lemma -/

/-- `FlowContextPSV` transfers through prefix-preserving array extension. -/
theorem FlowContextPSV_of_prefix_and_new
    (old_tokens new_tokens : Array (Positioned YamlToken))
    (h_old : FlowContextPSV old_tokens)
    (h_mono : old_tokens.size ≤ new_tokens.size)
    (h_prefix : ∀ (i : Nat) (hi : i < old_tokens.size),
      new_tokens[i]'(by omega) = old_tokens[i])
    (h_new : ∀ j (hj : j < new_tokens.size), j ≥ old_tokens.size →
      flowNesting new_tokens j > 0 →
      match (new_tokens[j]'hj).val with
      | .scalar content .plain =>
          ScalarScannable ⟨content, .plain, none, none, none⟩ true
      | _ => True) :
    FlowContextPSV new_tokens := by
  intro i hi h_flow
  by_cases h : i < old_tokens.size
  · have h_prefix_val : ∀ j (hj : j < old_tokens.size),
        (new_tokens[j]'(by omega)).val = (old_tokens[j]).val := by
      intro j hj; rw [h_prefix j hj]
    have h_fn := flowNesting_prefix_stable old_tokens new_tokens h_mono h_prefix_val i (by omega)
    rw [h_prefix i h]
    rw [h_fn] at h_flow
    exact h_old i h h_flow
  · exact h_new i hi (by omega) h_flow

/-! ### flowNesting extension lemmas -/

/-- `flowNesting.go` on an out-of-bounds range just returns `depth`. -/
theorem flowNesting_go_oob (tokens : Array (Positioned YamlToken))
    (pos target depth : Nat) (h : pos ≥ tokens.size) :
    flowNesting.go tokens pos target depth = depth := by
  generalize hk : target - pos = k
  induction k generalizing pos with
  | zero =>
    unfold flowNesting.go; simp [show pos ≥ target by omega]
  | succ k _ =>
    unfold flowNesting.go
    simp only [show ¬(pos ≥ target) by omega, ite_false,
      show ¬(pos < tokens.size) by omega, dite_false]

/-- One-step unfolding of `flowNesting.go` when `pos < tokens.size` and `pos < target`. -/
theorem flowNesting_go_step
    (tokens : Array (Positioned YamlToken))
    (pos target depth : Nat) (h_pos : pos < tokens.size) (h_tgt : pos < target) :
    flowNesting.go tokens pos target depth =
    flowNesting.go tokens (pos + 1) target
      (match (tokens[pos]'h_pos).val with
       | .flowSequenceStart | .flowMappingStart => depth + 1
       | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
       | _ => depth) := by
  conv => lhs; unfold flowNesting.go
          simp only [eq_false (show ¬(pos ≥ target) by omega), ite_false,
            eq_true h_pos, dite_true]

/-- Splitting `flowNesting.go`: processing positions `[pos, target)` can be split
    at any midpoint `mid` s.t. `pos ≤ mid ≤ target`.

    Uses `flowNesting_go_step` to unfold one step at a time, avoiding the
    cascading-unfold problem where `unfold` on the full goal unfolds ALL
    `flowNesting.go` occurrences simultaneously. -/
theorem flowNesting_go_split
    (tokens : Array (Positioned YamlToken))
    (pos mid target depth : Nat) (h1 : pos ≤ mid) (h2 : mid ≤ target) :
    flowNesting.go tokens pos target depth =
    flowNesting.go tokens mid target (flowNesting.go tokens pos mid depth) := by
  generalize hn : mid - pos = n
  induction n generalizing pos depth with
  | zero =>
    have : pos = mid := by omega
    subst this
    have h_inner : flowNesting.go tokens pos pos depth = depth := by
      unfold flowNesting.go; simp [show pos ≥ pos from Nat.le_refl pos]
    rw [h_inner]
  | succ n ih =>
    have h_lt_mid : pos < mid := by omega
    by_cases h_pos : pos < tokens.size
    · -- In-bounds: step both LHS and inner RHS by one position
      rw [flowNesting_go_step tokens pos target depth h_pos (by omega)]
      rw [flowNesting_go_step tokens pos mid depth h_pos (by omega)]
      exact ih (pos + 1) _ (by omega) (by omega)
    · -- Out-of-bounds: all three go calls collapse to depth
      simp only [flowNesting_go_oob tokens pos target depth (by omega),
                  flowNesting_go_oob tokens pos mid depth (by omega),
                  flowNesting_go_oob tokens mid target depth (by omega)]

/-- Processing a single pushed token at the end of the array. -/
theorem flowNesting_go_single_push
    (tokens : Array (Positioned YamlToken)) (t : Positioned YamlToken)
    (depth : Nat) :
    flowNesting.go (tokens.push t) tokens.size (tokens.size + 1) depth =
    match t.val with
    | .flowSequenceStart | .flowMappingStart => depth + 1
    | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
    | _ => depth := by
  unfold flowNesting.go
  simp only [show ¬(tokens.size ≥ tokens.size + 1) by omega, ite_false,
    show tokens.size < (tokens.push t).size by simp [Array.size_push], dite_true,
    show (tokens.push t)[tokens.size] = t from Array.getElem_push_eq]
  unfold flowNesting.go
  simp only [show tokens.size + 1 ≥ tokens.size + 1 from Nat.le_refl _, ite_true]

/-- How `flowNesting` changes when a single token is appended to the array. -/
theorem flowNesting_push (tokens : Array (Positioned YamlToken)) (t : Positioned YamlToken) :
    flowNesting (tokens.push t) (tokens.size + 1) =
    match t.val with
    | .flowSequenceStart | .flowMappingStart => flowNesting tokens tokens.size + 1
    | .flowSequenceEnd | .flowMappingEnd =>
        if flowNesting tokens tokens.size > 0
        then flowNesting tokens tokens.size - 1 else 0
    | _ => flowNesting tokens tokens.size := by
  unfold flowNesting
  rw [flowNesting_go_split (tokens.push t) 0 tokens.size (tokens.size + 1) 0
      (by omega) (by omega)]
  rw [flowNesting_go_prefix_stable tokens (tokens.push t)
      (by simp [Array.size_push])
      (fun j hj => by simp [Array.getElem_push, hj])
      0 tokens.size 0 (by omega)]
  exact flowNesting_go_single_push tokens t _

/-- Appending a non-flow token preserves `flowNesting` at the old size. -/
theorem flowNesting_push_non_flow (tokens : Array (Positioned YamlToken))
    (t : Positioned YamlToken)
    (h1 : t.val ≠ .flowSequenceStart) (h2 : t.val ≠ .flowMappingStart)
    (h3 : t.val ≠ .flowSequenceEnd) (h4 : t.val ≠ .flowMappingEnd) :
    flowNesting (tokens.push t) (tokens.size + 1) = flowNesting tokens tokens.size := by
  rw [flowNesting_push]
  cases h : t.val <;> simp_all

/-- `FlowNestingInv` is preserved when a non-flow token is emitted
    and `flowLevel` is unchanged. -/
theorem FlowNestingInv_emit_non_flow (s : ScannerState) (tok : YamlToken)
    (h_fni : FlowNestingInv s)
    (h1 : tok ≠ .flowSequenceStart) (h2 : tok ≠ .flowMappingStart)
    (h3 : tok ≠ .flowSequenceEnd) (h4 : tok ≠ .flowMappingEnd) :
    FlowNestingInv (s.emit tok) := by
  unfold FlowNestingInv at *
  simp only [emit_preserves_flowLevel, emit_tokens_size]
  rw [show (s.emit tok).tokens = s.tokens.push ⟨s.currentPos, tok⟩ from rfl]
  rw [flowNesting_push_non_flow s.tokens ⟨s.currentPos, tok⟩ h1 h2 h3 h4]
  exact h_fni

/-! ### FlowInv helper lemmas -/

/-- When a token is provably not `.scalar _ .plain`, the FlowContextPSV match is `True`. -/
theorem fpsv_of_not_plain (tok : Positioned YamlToken)
    (h : match tok.val with | .scalar _ .plain => False | _ => True) :
    match tok.val with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ true
    | _ => True := by
  cases tok with | mk pos val =>
  cases val <;> simp_all
  rename_i content style; cases style <;> simp_all

/-- `flowNesting.go` on non-flow tokens returns depth unchanged. -/
theorem flowNesting_go_non_flow
    (tokens : Array (Positioned YamlToken)) (pos target depth : Nat)
    (h_nf : ∀ j, pos ≤ j → j < target → (hj : j < tokens.size) →
      (tokens[j]'hj).val ≠ .flowSequenceStart ∧
      (tokens[j]'hj).val ≠ .flowMappingStart ∧
      (tokens[j]'hj).val ≠ .flowSequenceEnd ∧
      (tokens[j]'hj).val ≠ .flowMappingEnd) :
    flowNesting.go tokens pos target depth = depth := by
  generalize hn : target - pos = n
  induction n generalizing pos depth with
  | zero => simp [flowNesting.go, show pos ≥ target by omega]
  | succ n ih =>
    have h_lt : pos < target := by omega
    by_cases h_pos : pos < tokens.size
    · rw [flowNesting_go_step tokens pos target depth h_pos h_lt]
      have ⟨h1, h2, h3, h4⟩ := h_nf pos (Nat.le_refl _) h_lt h_pos
      have : (match (tokens[pos]'h_pos).val with
        | .flowSequenceStart | .flowMappingStart => depth + 1
        | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
        | _ => depth) = depth := by
        generalize h_tok : (tokens[pos]'h_pos).val = tok
        cases tok <;> simp_all
      rw [this]
      exact ih (pos + 1) depth (fun j hge hlt hj => h_nf j (by omega) hlt hj) (by omega)
    · exact flowNesting_go_oob tokens pos target depth (by omega)

/-- `FlowNestingInv` is preserved through any extension that adds only non-flow tokens
    and preserves flowLevel. -/
theorem FlowNestingInv_of_non_flow_extension
    (s s' : ScannerState)
    (h_fni : FlowNestingInv s)
    (h_mono : s.tokens.size ≤ s'.tokens.size)
    (h_prefix_val : ∀ j (hj : j < s.tokens.size),
      (s'.tokens[j]'(by omega)).val = (s.tokens[j]).val)
    (h_fl : s'.flowLevel = s.flowLevel)
    (h_non_flow : ∀ j (hj : j < s'.tokens.size), j ≥ s.tokens.size →
      (s'.tokens[j]'hj).val ≠ .flowSequenceStart ∧
      (s'.tokens[j]'hj).val ≠ .flowMappingStart ∧
      (s'.tokens[j]'hj).val ≠ .flowSequenceEnd ∧
      (s'.tokens[j]'hj).val ≠ .flowMappingEnd) :
    FlowNestingInv s' := by
  unfold FlowNestingInv at *
  rw [h_fl]; unfold flowNesting
  rw [flowNesting_go_split s'.tokens 0 s.tokens.size s'.tokens.size 0 (by omega) h_mono]
  rw [flowNesting_go_prefix_stable s.tokens s'.tokens h_mono h_prefix_val 0 s.tokens.size 0
      (by omega)]
  rw [flowNesting_go_non_flow s'.tokens s.tokens.size s'.tokens.size _
      (fun j hge hlt hj => h_non_flow j hj (by omega))]
  exact h_fni

/-- `unwindIndentsLoop` preserves `FlowNestingInv`. -/
theorem unwindIndentsLoop_preserves_FlowNestingInv (s : ScannerState) (col : Int) (fuel : Nat)
    (h_fni : FlowNestingInv s) :
    FlowNestingInv (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; exact h_fni
  | succ fuel' ih =>
    unfold unwindIndentsLoop; split
    · apply ih
      exact FlowNestingInv_emit_non_flow s .blockEnd h_fni
        (by decide) (by decide) (by decide) (by decide)
    · exact h_fni

/-- `unwindIndents` preserves `FlowNestingInv`. -/
theorem unwindIndents_preserves_FlowNestingInv (s : ScannerState) (col : Int)
    (h_fni : FlowNestingInv s) :
    FlowNestingInv (unwindIndents s col) := by
  unfold unwindIndents
  exact unwindIndentsLoop_preserves_FlowNestingInv s col s.indents.size h_fni

/-- `saveSimpleKey` preserves `FlowNestingInv`. -/
theorem saveSimpleKey_preserves_FlowNestingInv (s : ScannerState)
    (h_fni : FlowNestingInv s) :
    FlowNestingInv (saveSimpleKey s) := by
  unfold FlowNestingInv at *
  rw [saveSimpleKey_preserves_flowLevel]
  have h_cases : (saveSimpleKey s).tokens = s.tokens ∨
      ∃ ph : Positioned YamlToken, ph.val = .placeholder ∧
        (saveSimpleKey s).tokens = (s.tokens.push ph).push ph := by
    unfold saveSimpleKey; split
    · left; rfl
    · split
      · right; exact ⟨⟨s.currentPos, .placeholder⟩, rfl, rfl⟩
      · left; rfl
  rcases h_cases with h_eq | ⟨ph, h_ph, h_eq⟩
  · rw [h_eq]; exact h_fni
  · rw [h_eq, Array.size_push]
    rw [flowNesting_push_non_flow (s.tokens.push ph) ph
      (by rw [h_ph]; decide) (by rw [h_ph]; decide)
      (by rw [h_ph]; decide) (by rw [h_ph]; decide)]
    rw [Array.size_push]
    rw [flowNesting_push_non_flow s.tokens ph
      (by rw [h_ph]; decide) (by rw [h_ph]; decide)
      (by rw [h_ph]; decide) (by rw [h_ph]; decide)]
    exact h_fni

/-- Preprocessing preserves `FlowNestingInv`. -/
theorem preprocess_preserves_FlowNestingInv
    (s s1 : ScannerState) (c : Char)
    (h_fni : FlowNestingInv s)
    (h_ok : scanNextToken_preprocess s = .ok (some (s1, c))) :
    FlowNestingInv s1 := by
  unfold scanNextToken_preprocess at h_ok
  simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h_ok
  simp only [Except.bind] at h_ok
  split at h_ok
  · contradiction
  · rename_i v heq_skip
    have h_fni_v : FlowNestingInv v := by
      unfold FlowNestingInv at *
      rw [skipToContent_preserves_tokens s v heq_skip,
          skipToContent_preserves_flowLevel s v heq_skip]
      exact h_fni
    split at h_ok
    · simp at h_ok
    · split at h_ok
      · split at h_ok
        · contradiction
        · split at h_ok
          · simp at h_ok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_ok
            obtain ⟨rfl, _⟩ := h_ok
            exact saveSimpleKey_preserves_FlowNestingInv _
              (unwindIndents_preserves_FlowNestingInv v v.col h_fni_v)
      · split at h_ok
        · contradiction
        · split at h_ok
          · simp at h_ok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_ok
            obtain ⟨rfl, _⟩ := h_ok
            exact saveSimpleKey_preserves_FlowNestingInv v h_fni_v

/-- Preprocessing preserves `FlowContextPSV`. -/
theorem preprocess_preserves_FlowContextPSV
    (s s1 : ScannerState) (c : Char)
    (h_old : FlowContextPSV s.tokens)
    (h_ok : scanNextToken_preprocess s = .ok (some (s1, c))) :
    FlowContextPSV s1.tokens := by
  apply FlowContextPSV_of_prefix_and_new s.tokens s1.tokens h_old
    (preprocess_tokens_mono s s1 c h_ok)
  · intro i hi; exact preprocess_preserves_prefix s s1 c h_ok i hi
  · intro j hj hge h_flow
    -- Same token analysis as preprocess_preserves_PlainScalarsValid:
    -- new tokens are .blockEnd or .placeholder, not .scalar _ .plain
    unfold scanNextToken_preprocess at h_ok
    simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h_ok
    simp only [Except.bind] at h_ok
    split at h_ok
    · contradiction
    · rename_i v heq_skip
      have h_sizes : v.tokens.size = s.tokens.size :=
        congrArg Array.size (skipToContent_preserves_tokens s v heq_skip)
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
              · rw [saveSimpleKey_preserves_prefix _ j
                  (by show j < ({ unwindIndents v v.col with needIndentCheck := false } : ScannerState).tokens.size; exact h_lt)]
                exact fpsv_of_not_plain _
                  (unwindIndents_new_tokens_not_plain v v.col j h_lt (by omega))
              · exact fpsv_of_not_plain _
                  (saveSimpleKey_new_tokens_not_plain _ j hj (by
                    have : ({ unwindIndents v v.col with needIndentCheck := false } : ScannerState).tokens.size = (unwindIndents v v.col).tokens.size := rfl
                    show j ≥ ({ unwindIndents v v.col with needIndentCheck := false } : ScannerState).tokens.size
                    rw [this]; omega))
        · split at h_ok
          · contradiction
          · split at h_ok
            · simp at h_ok
            · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_ok
              obtain ⟨rfl, _⟩ := h_ok
              exact fpsv_of_not_plain _
                (saveSimpleKey_new_tokens_not_plain v j hj (by omega))

/-- `allowDirectives` conditional preserves `FlowNestingInv` (tokens and flowLevel unchanged). -/
theorem allowDir_ite_preserves_FlowNestingInv (s : ScannerState)
    (h : FlowNestingInv s) :
    FlowNestingInv (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true }
    else s) := by
  split <;> exact h

/-- `allowDirectives` conditional preserves `FlowContextPSV` (tokens unchanged). -/
theorem allowDir_ite_preserves_FlowContextPSV (s : ScannerState)
    (h : FlowContextPSV s.tokens) :
    FlowContextPSV (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true }
    else s).tokens := by
  split <;> exact h

/-! ### Non-flow dispatch helpers for FlowNestingInv

For structural, block, and content dispatches: all new tokens are non-flow
indicators, and `flowLevel` is unchanged. `FlowNestingInv_of_non_flow_extension`
handles all three. -/

/-- Unwinding new tokens from `unwindIndents` are non-flow. -/
theorem unwindIndentsLoop_new_tokens_not_flow (s : ScannerState) (col : Int) (fuel : Nat) :
    ∀ (j : Nat) (hj : j < (unwindIndentsLoop s col fuel).tokens.size), j ≥ s.tokens.size →
    ((unwindIndentsLoop s col fuel).tokens[j]'hj).val ≠ .flowSequenceStart ∧
    ((unwindIndentsLoop s col fuel).tokens[j]'hj).val ≠ .flowMappingStart ∧
    ((unwindIndentsLoop s col fuel).tokens[j]'hj).val ≠ .flowSequenceEnd ∧
    ((unwindIndentsLoop s col fuel).tokens[j]'hj).val ≠ .flowMappingEnd := by
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
        have h_val : (({ s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop } : ScannerState).tokens[s.tokens.size]'h_pop_sz).val = .blockEnd := by
          show ((s.emit .blockEnd).tokens[s.tokens.size]'(by rw [h_emit_size]; omega)).val = .blockEnd
          unfold ScannerState.emit; simp [Array.getElem_push_eq]
        simp [h_val]
      · have hge' : j ≥ ({ s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop } : ScannerState).tokens.size := by
          show j ≥ (s.emit .blockEnd).tokens.size
          rw [h_emit_size]; omega
        exact ih _ j hj hge'
    · intro j hj hge; omega

/-- `unwindIndents` new tokens are non-flow. -/
theorem unwindIndents_new_tokens_not_flow (s : ScannerState) (col : Int)
    (j : Nat) (hj : j < (unwindIndents s col).tokens.size) (hge : j ≥ s.tokens.size) :
    ((unwindIndents s col).tokens[j]'hj).val ≠ .flowSequenceStart ∧
    ((unwindIndents s col).tokens[j]'hj).val ≠ .flowMappingStart ∧
    ((unwindIndents s col).tokens[j]'hj).val ≠ .flowSequenceEnd ∧
    ((unwindIndents s col).tokens[j]'hj).val ≠ .flowMappingEnd := by
  unfold unwindIndents
  exact unwindIndentsLoop_new_tokens_not_flow s col s.indents.size j hj hge

/-- `saveSimpleKey` new tokens are non-flow (.placeholder only). -/
theorem saveSimpleKey_new_tokens_not_flow (s : ScannerState)
    (j : Nat) (hj : j < (saveSimpleKey s).tokens.size) (hge : j ≥ s.tokens.size) :
    ((saveSimpleKey s).tokens[j]'hj).val ≠ .flowSequenceStart ∧
    ((saveSimpleKey s).tokens[j]'hj).val ≠ .flowMappingStart ∧
    ((saveSimpleKey s).tokens[j]'hj).val ≠ .flowSequenceEnd ∧
    ((saveSimpleKey s).tokens[j]'hj).val ≠ .flowMappingEnd := by
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

/-! ### Dispatch-level FlowInv preservation

For structural, block, and content dispatches: all new tokens are non-flow
indicators, and `flowLevel` is unchanged. The flow indicators dispatch changes
both and requires specific analysis. -/

/-- `advanceN` preserves `FlowNestingInv` (preserves both tokens and flowLevel). -/
theorem advanceN_preserves_FlowNestingInv (s : ScannerState) (n : Nat)
    (h : FlowNestingInv s) : FlowNestingInv (s.advanceN n) := by
  unfold FlowNestingInv at *
  rw [advanceN_preserves_tokens, advanceN_preserves_flowLevel]; exact h

/-- `scanDocumentStart` preserves `FlowNestingInv`. -/
theorem scanDocumentStart_preserves_FlowNestingInv (s : ScannerState)
    (h : FlowNestingInv s) : FlowNestingInv (scanDocumentStart s) := by
  unfold scanDocumentStart
  apply advanceN_preserves_FlowNestingInv
  exact FlowNestingInv_emit_non_flow
    { unwindIndents s (-1) with simpleKey := { possible := false } }
    .documentStart
    (unwindIndents_preserves_FlowNestingInv s (-1) h)
    (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 800000 in
/-- `scanDocumentEnd` preserves `FlowNestingInv` on success.
    The function chains: unwindIndents → simpleKey update → emit .documentEnd → advanceN 3 →
    field update. Validation (skipDocEndWhitespace + peek) may throw but doesn't change result. -/
theorem scanDocumentEnd_preserves_FlowNestingInv (s s' : ScannerState)
    (h_fni : FlowNestingInv s) (h_ok : scanDocumentEnd s = .ok s') :
    FlowNestingInv s' := by
  unfold scanDocumentEnd at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · -- All ok paths produce the same `result` computed before validation
    have h_base : FlowNestingInv
        (({ unwindIndents s (-1) with simpleKey := { possible := false } }.emit .documentEnd).advanceN 3) :=
      advanceN_preserves_FlowNestingInv _ _
        (FlowNestingInv_emit_non_flow
          { unwindIndents s (-1) with simpleKey := { possible := false } }
          .documentEnd
          (unwindIndents_preserves_FlowNestingInv s (-1) h_fni)
          (by decide) (by decide) (by decide) (by decide))
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_base
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_base
    · split at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_base
      · simp at h_ok

set_option maxHeartbeats 800000 in
/-- `scanDirective` preserves `flowLevel` on success. -/
theorem scanDirective_preserves_flowLevel (s s' : ScannerState)
    (h : scanDirective s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanDirective at h
  split at h
  · contradiction
  · -- allowDirectives = true. After advance + collectDirectiveNameLoop + skipWhitespace,
    -- dispatches to scanYamlDirective, scanTagDirective, or skipToEndOfLine.
    dsimp only [] at h
    -- The intermediate state preserves flowLevel:
    have h_ws_fl :
        (skipWhitespace (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2).flowLevel
        = s.flowLevel := by
      rw [skipWhitespace_preserves_flowLevel,
          collectDirectiveNameLoop_preserves_flowLevel,
          advance_preserves_flowLevel]
    split at h
    · -- name == "YAML": scanYamlDirective
      unfold scanYamlDirective at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · contradiction  -- seenYamlDirective error
      · -- Past validation, all branches produce { s_with_token | seenYamlDirective, directivesPresent }
        -- where s_with_token = s_validated.emitAt startPos tok
        -- emitAt preserves flowLevel, struct update preserves flowLevel
        split at h
        · -- some '#'
          split at h
          · contradiction
          · simp only [Except.ok.injEq] at h; subst h; simp only []
            rw [emitAt_preserves_flowLevel, skipWhitespace_preserves_flowLevel,
                collectVersionMinorLoop_preserves_flowLevel,
                collectVersionMajorLoop_preserves_flowLevel, h_ws_fl]
        · -- some c (not '#')
          split at h
          · contradiction
          · simp only [Except.ok.injEq] at h; subst h; simp only []
            rw [emitAt_preserves_flowLevel, skipWhitespace_preserves_flowLevel,
                collectVersionMinorLoop_preserves_flowLevel,
                collectVersionMajorLoop_preserves_flowLevel, h_ws_fl]
        · -- none
          simp only [Except.ok.injEq] at h; subst h; simp only []
          rw [emitAt_preserves_flowLevel, skipWhitespace_preserves_flowLevel,
              collectVersionMinorLoop_preserves_flowLevel,
              collectVersionMajorLoop_preserves_flowLevel, h_ws_fl]
    · split at h
      · -- name == "TAG": scanTagDirective
        unfold scanTagDirective at h
        simp only [Except.ok.injEq] at h; subst h
        simp only []
        rw [emitAt_preserves_flowLevel, collectTagPrefixLoop_preserves_flowLevel,
            skipWhitespace_preserves_flowLevel,
            collectTagHandleDirectiveLoop_preserves_flowLevel, h_ws_fl]
      · -- unknown directive: skipToEndOfLine
        simp only [Except.ok.injEq] at h; subst h
        rw [skipToEndOfLine_preserves_flowLevel, h_ws_fl]

theorem scanYamlDirective_new_tokens_not_flow (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (h : scanYamlDirective s s_after_ws startPos = .ok s')
    (h_ws : s_after_ws.tokens = s.tokens) (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    (s'.tokens[j]'hj).val ≠ .flowSequenceStart ∧
    (s'.tokens[j]'hj).val ≠ .flowMappingStart ∧
    (s'.tokens[j]'hj).val ≠ .flowSequenceEnd ∧
    (s'.tokens[j]'hj).val ≠ .flowMappingEnd := by
  unfold scanYamlDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · -- All three YAML sub-branches produce the same token structure
    -- Prove token equality: s'.tokens = s.tokens.push ⟨startPos, .versionDirective ...⟩
    have h_toks : s'.tokens = s.tokens.push ⟨startPos, .versionDirective
      (collectVersionMajorLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).fst.toNat!
      (collectVersionMinorLoop (collectVersionMajorLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).snd ""
        (s.inputEnd - (collectVersionMajorLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).snd.offset)).fst.toNat!⟩ := by
      split at h
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq
          simp only [ScannerState.emitAt, skipWhitespace_preserves_tokens,
            collectVersionMinorLoop_preserves_tokens,
            collectVersionMajorLoop_preserves_tokens, h_ws]
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq
          simp only [ScannerState.emitAt, skipWhitespace_preserves_tokens,
            collectVersionMinorLoop_preserves_tokens,
            collectVersionMajorLoop_preserves_tokens, h_ws]
      · injection h with h_eq; subst h_eq
        simp only [ScannerState.emitAt, skipWhitespace_preserves_tokens,
          collectVersionMinorLoop_preserves_tokens,
          collectVersionMajorLoop_preserves_tokens, h_ws]
    simp only [h_toks, Array.size_push] at hj
    have h_j : j = s.tokens.size := by omega
    simp only [h_toks, h_j, Array.getElem_push_eq]
    exact ⟨by nofun, by nofun, by nofun, by nofun⟩

theorem scanTagDirective_new_tokens_not_flow (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (h : scanTagDirective s s_after_ws startPos = .ok s')
    (h_ws : s_after_ws.tokens = s.tokens) (j : Nat)
    (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    (s'.tokens[j]'hj).val ≠ .flowSequenceStart ∧
    (s'.tokens[j]'hj).val ≠ .flowMappingStart ∧
    (s'.tokens[j]'hj).val ≠ .flowSequenceEnd ∧
    (s'.tokens[j]'hj).val ≠ .flowMappingEnd := by
  unfold scanTagDirective at h
  dsimp only [] at h
  injection h with h_eq
  have h_toks : s'.tokens = s.tokens.push ⟨startPos, .tagDirective
    (collectTagHandleDirectiveLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).fst
    (collectTagPrefixLoop (skipWhitespace (collectTagHandleDirectiveLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).snd) ""
      (s.inputEnd - (skipWhitespace (collectTagHandleDirectiveLoop s_after_ws "" (s.inputEnd - s_after_ws.offset)).snd).offset)).fst⟩ := by
    subst h_eq
    simp only [ScannerState.emitAt, collectTagPrefixLoop_preserves_tokens,
      skipWhitespace_preserves_tokens, collectTagHandleDirectiveLoop_preserves_tokens, h_ws]
  simp only [h_toks, Array.size_push] at hj
  have h_j : j = s.tokens.size := by omega
  simp only [h_toks, h_j, Array.getElem_push_eq]
  exact ⟨by nofun, by nofun, by nofun, by nofun⟩

set_option maxHeartbeats 800000 in
/-- `scanDirective` emits non-flow tokens.
    Proved by the same structural decomposition as `scanDirective_new_not_plain`:
    each branch emits `.versionDirective`, `.tagDirective`, or no new tokens. -/
theorem scanDirective_new_tokens_not_flow (s s' : ScannerState)
    (h : scanDirective s = .ok s')
    (j : Nat) (hj : j < s'.tokens.size) (hge : j ≥ s.tokens.size) :
    (s'.tokens[j]'hj).val ≠ .flowSequenceStart ∧
    (s'.tokens[j]'hj).val ≠ .flowMappingStart ∧
    (s'.tokens[j]'hj).val ≠ .flowSequenceEnd ∧
    (s'.tokens[j]'hj).val ≠ .flowMappingEnd := by
  unfold scanDirective at h
  dsimp only [] at h
  split at h
  any_goals contradiction
  have h_ws_tok : (skipWhitespace (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2).tokens = s.tokens := by
    rw [skipWhitespace_preserves_tokens, collectDirectiveNameLoop_preserves_tokens, advance_preserves_tokens]
  split at h
  · -- YAML directive
    exact scanYamlDirective_new_tokens_not_flow s _ _ s' h h_ws_tok j hj hge
  · split at h
    · -- TAG directive
      exact scanTagDirective_new_tokens_not_flow s _ _ s' h h_ws_tok j hj hge
    · -- unknown directive: skipToEndOfLine adds no tokens
      injection h with h_eq; subst h_eq; exfalso
      rw [skipToEndOfLine_preserves_tokens, h_ws_tok] at hj; omega

set_option maxHeartbeats 800000 in
/-- Structural dispatch preserves `FlowInv`. -/
theorem dispatchStructural_preserves_FlowInv
    (s : ScannerState) (c : Char)
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchStructural s c = .ok (some s')) :
    FlowContextPSV s'.tokens ∧ FlowNestingInv s' := by
  constructor
  · -- FlowContextPSV: new tokens from structural dispatch are .documentStart,
    -- .documentEnd, .blockEnd, .directive — never .scalar _ .plain
    apply FlowContextPSV_of_prefix_and_new s.tokens s'.tokens h_fpsv
      (dispatchStructural_tokens_mono s c s' h_ok)
    · intro i hi; exact dispatchStructural_preserves_prefix s c s' h_ok i (by omega)
    · intro j hj hge _
      -- All new structural tokens satisfy fpsv_of_not_plain
      unfold scanNextToken_dispatchStructural at h_ok
      simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h_ok
      simp only [Except.bind] at h_ok
      repeat (any_goals (split at h_ok))
      any_goals contradiction
      all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
      any_goals contradiction
      all_goals (try subst_vars)
      -- scanDocumentStart: tokens are .blockEnd (from unwindIndents) or .documentStart
      all_goals (try (
        apply fpsv_of_not_plain
        exact scanDocumentStart_new_tok_not_plain s j hj hge))
      -- scanDocumentEnd
      all_goals (try (
        rename_i _ _ v h_de _
        apply fpsv_of_not_plain
        exact scanDocumentEnd_new_tok_not_plain s v h_de j hj hge))
      -- scanDirective
      all_goals (try (
        rename_i _ _ v h_dir _
        apply fpsv_of_not_plain
        exact scanDirective_new_tok_not_plain s v h_dir j hj hge))
  · -- FlowNestingInv: structural dispatch preserves flowLevel and emits non-flow tokens
    unfold scanNextToken_dispatchStructural at h_ok
    simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h_ok
    simp only [Except.bind] at h_ok
    repeat (any_goals (split at h_ok))
    any_goals contradiction
    all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
    any_goals contradiction
    all_goals (try subst_vars)
    -- scanDocumentStart branches
    all_goals (try exact scanDocumentStart_preserves_FlowNestingInv s h_fni)
    -- scanDocumentEnd branches
    all_goals (try (rename_i s_de h_de
                    exact scanDocumentEnd_preserves_FlowNestingInv s s_de h_fni h_de))
    -- scanDirective branches
    all_goals (rename_i v h_dir
               exact FlowNestingInv_of_non_flow_extension s v h_fni
                 (scanDirective_monotonic s v h_dir)
                 (fun j hj => congrArg Positioned.val (scanDirective_preserves_prefix s v h_dir j (by omega)))
                 (scanDirective_preserves_flowLevel s v h_dir)
                 (fun j hj hge => scanDirective_new_tokens_not_flow s v h_dir j hj hge))

/-- Flow indicators dispatch preserves `FlowInv`. -/
theorem dispatchFlowIndicators_preserves_FlowInv
    (s : ScannerState) (c : Char)
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    FlowContextPSV s'.tokens ∧ FlowNestingInv s' := by
  -- Flow indicators: `[`, `]`, `{`, `}`, `,`
  -- These change flowLevel and emit flow tokens
  unfold scanNextToken_dispatchFlowIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  -- Split on each character check
  split at h_ok
  · -- c == '['
    injection h_ok with h_ok2; injection h_ok2 with h_eq; subst h_eq
    -- s' = scanFlowSequenceStart s
    constructor
    · -- FlowContextPSV: new token is flowSequenceStart (not plain scalar)
      refine FlowContextPSV_of_prefix_and_new s.tokens (scanFlowSequenceStart s).tokens h_fpsv ?_ ?_ ?_
      · have : (scanFlowSequenceStart s).tokens.size ≥ s.tokens.size + 1 := by
          simp [scanFlowSequenceStart_adds_one_token]
        omega
      · intro i hi
        exact scanFlowSequenceStart_preserves_prefix s i hi
      · intro j hj hge _
        apply fpsv_of_not_plain
        -- j = s.tokens.size, token is flowSequenceStart
        have : j = s.tokens.size := by
          have : (scanFlowSequenceStart s).tokens.size = s.tokens.size + 1 := scanFlowSequenceStart_adds_one_token s
          omega
        subst this
        unfold scanFlowSequenceStart
        simp [ScannerState.emit, advance_preserves_tokens, Array.getElem_push_eq]
    · -- FlowNestingInv: flowLevel increases by 1, flowNesting increases by 1
      unfold FlowNestingInv at *
      unfold scanFlowSequenceStart
      simp [ScannerState.emit, advance_preserves_tokens, advance_preserves_flowLevel, Array.size_push]
      rw [flowNesting_push, h_fni]
  · split at h_ok
    · split at h_ok
      · contradiction  -- flowLevel == 0 error
      · split at h_ok
        · contradiction  -- validateFlowClose error
        · -- c == ']', s' = scanFlowSequenceEnd s
          injection h_ok with h_ok2; injection h_ok2 with h_eq; subst h_eq
          constructor
          · -- FlowContextPSV: new token is flowSequenceEnd (not plain scalar)
            refine FlowContextPSV_of_prefix_and_new s.tokens (scanFlowSequenceEnd s).tokens h_fpsv ?_ ?_ ?_
            · have : (scanFlowSequenceEnd s).tokens.size ≥ s.tokens.size + 1 := by
                simp [scanFlowSequenceEnd_adds_one_token]
              omega
            · intro i hi
              exact scanFlowSequenceEnd_preserves_prefix s i hi
            · intro j hj hge _
              apply fpsv_of_not_plain
              have : j = s.tokens.size := by
                have : (scanFlowSequenceEnd s).tokens.size = s.tokens.size + 1 := scanFlowSequenceEnd_adds_one_token s
                omega
              subst this
              unfold scanFlowSequenceEnd
              simp [ScannerState.emit, advance_preserves_tokens, Array.getElem_push_eq]
          · -- FlowNestingInv: flowLevel decreases by 1, flowNesting decreases by 1
            unfold FlowNestingInv at *
            unfold scanFlowSequenceEnd
            simp [ScannerState.emit, advance_preserves_tokens, advance_preserves_flowLevel, Array.size_push]
            rw [flowNesting_push, h_fni]
    · split at h_ok
      · -- c == '{'
        injection h_ok with h_ok2; injection h_ok2 with h_eq; subst h_eq
        constructor
        · -- FlowContextPSV
          refine FlowContextPSV_of_prefix_and_new s.tokens (scanFlowMappingStart s).tokens h_fpsv ?_ ?_ ?_
          · have : (scanFlowMappingStart s).tokens.size ≥ s.tokens.size + 1 := by
              simp [scanFlowMappingStart_adds_one_token]
            omega
          · intro i hi
            exact scanFlowMappingStart_preserves_prefix s i hi
          · intro j hj hge _
            apply fpsv_of_not_plain
            have : j = s.tokens.size := by
              have : (scanFlowMappingStart s).tokens.size = s.tokens.size + 1 := scanFlowMappingStart_adds_one_token s
              omega
            subst this
            unfold scanFlowMappingStart
            simp [ScannerState.emit, advance_preserves_tokens, Array.getElem_push_eq]
        · -- FlowNestingInv
          unfold FlowNestingInv at *
          unfold scanFlowMappingStart
          simp [ScannerState.emit, advance_preserves_tokens, advance_preserves_flowLevel, Array.size_push]
          rw [flowNesting_push, h_fni]
      · split at h_ok
        · split at h_ok
          · contradiction  -- flowLevel == 0 error
          · split at h_ok
            · contradiction  -- validateFlowClose error
            · -- c == '}'
              injection h_ok with h_ok2; injection h_ok2 with h_eq; subst h_eq
              constructor
              · -- FlowContextPSV
                refine FlowContextPSV_of_prefix_and_new s.tokens (scanFlowMappingEnd s).tokens h_fpsv ?_ ?_ ?_
                · have : (scanFlowMappingEnd s).tokens.size ≥ s.tokens.size + 1 := by
                    simp [scanFlowMappingEnd_adds_one_token]
                  omega
                · intro i hi
                  exact scanFlowMappingEnd_preserves_prefix s i hi
                · intro j hj hge _
                  apply fpsv_of_not_plain
                  have : j = s.tokens.size := by
                    have : (scanFlowMappingEnd s).tokens.size = s.tokens.size + 1 := scanFlowMappingEnd_adds_one_token s
                    omega
                  subst this
                  unfold scanFlowMappingEnd
                  simp [ScannerState.emit, advance_preserves_tokens, Array.getElem_push_eq]
              · -- FlowNestingInv
                unfold FlowNestingInv at *
                unfold scanFlowMappingEnd
                simp [ScannerState.emit, advance_preserves_tokens, advance_preserves_flowLevel, Array.size_push]
                rw [flowNesting_push, h_fni]
        · split at h_ok
          · -- c == ','
            split at h_ok
            · contradiction  -- flowLevel == 0 error
            · -- flowLevel > 0, split on scanFlowEntry result
              split at h_ok
              · contradiction  -- scanFlowEntry error
              · rename_i _ s_flow h_flow
                injection h_ok with h_ok2; injection h_ok2 with h_eq; subst h_eq
                -- s' = s_flow = result of scanFlowEntry s
                -- scanFlowEntry emits .flowEntry (not plain scalar) and preserves flowLevel
                constructor
                · -- FlowContextPSV
                  refine FlowContextPSV_of_prefix_and_new s.tokens s_flow.tokens h_fpsv ?_ ?_ ?_
                  · have : s_flow.tokens.size ≥ s.tokens.size + 1 := by
                      exact scanFlowEntry_adds_one_token s s_flow h_flow
                    omega
                  · intro i hi
                    exact scanFlowEntry_preserves_prefix s s_flow h_flow i hi
                  · intro j hj hge _
                    apply fpsv_of_not_plain
                    have hsize : s_flow.tokens.size = s.tokens.size + 1 := by
                      have := scanFlowEntry_adds_one_token s s_flow h_flow
                      unfold scanFlowEntry at h_flow
                      simp only [bind, Except.bind, pure, Except.pure] at h_flow
                      split at h_flow
                      · split at h_flow
                        · simp at h_flow
                        · injection h_flow with h_eq; subst h_eq
                          simp [ScannerState.emit, advance_preserves_tokens, Array.size_push]
                      · injection h_flow with h_eq; subst h_eq
                        simp [ScannerState.emit, advance_preserves_tokens, Array.size_push]
                    have : j = s.tokens.size := by omega
                    subst this
                    unfold scanFlowEntry at h_flow
                    simp only [bind, Except.bind, pure, Except.pure] at h_flow
                    split at h_flow
                    · split at h_flow
                      · simp at h_flow
                      · injection h_flow with h_eq; subst h_eq
                        simp [ScannerState.emit, advance_preserves_tokens, Array.getElem_push_eq]
                    · injection h_flow with h_eq; subst h_eq
                      simp [ScannerState.emit, advance_preserves_tokens, Array.getElem_push_eq]
                · -- FlowNestingInv
                  unfold FlowNestingInv at *
                  have h_fl := scanFlowEntry_preserves_flowLevel s s_flow h_flow
                  rw [h_fl]
                  unfold scanFlowEntry at h_flow
                  simp only [bind, Except.bind, pure, Except.pure] at h_flow
                  split at h_flow
                  · split at h_flow
                    · simp at h_flow
                    · injection h_flow with h_eq; subst h_eq
                      simp [ScannerState.emit, advance_preserves_tokens, Array.size_push]
                      rw [flowNesting_push, h_fni]
                  · injection h_flow with h_eq; subst h_eq
                    simp [ScannerState.emit, advance_preserves_tokens, Array.size_push]
                    rw [flowNesting_push, h_fni]
          · -- c is not any flow indicator, returns none
            simp at h_ok

-- Helper lemmas for content tokens

theorem collectAnchorNameLoop_preserves_flowLevel (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s acc with
  | zero => unfold collectAnchorNameLoop; rfl
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · split
      · rw [ih, advance_preserves_flowLevel]
      · rfl
    · rfl

theorem collectVerbatimTagLoop_preserves_flowLevel (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · -- some '>'
      exact advance_preserves_flowLevel s
    · -- some c (not '>')
      rw [ih, advance_preserves_flowLevel]
    · -- none
      rfl

theorem collectTagSuffixLoop_preserves_flowLevel (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih, advance_preserves_flowLevel]
      · rfl
    · rfl

theorem collectTagHandleLoop_preserves_flowLevel (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · exact advance_preserves_flowLevel s
    · split
      · rw [ih, advance_preserves_flowLevel]
      · rfl
    · rfl

theorem scanAnchorOrAlias_preserves_flowLevel (s : ScannerState) (isAnchor : Bool) :
    (scanAnchorOrAlias s isAnchor).flowLevel = s.flowLevel := by
  unfold scanAnchorOrAlias
  simp [ScannerState.emitAt, collectAnchorNameLoop_preserves_flowLevel, advance_preserves_flowLevel]

theorem scanAnchorOrAlias_new_token_not_plain (s : ScannerState) (isAnchor : Bool) :
    let tok := (scanAnchorOrAlias s isAnchor).tokens[s.tokens.size]'(by
      have := scanAnchorOrAlias_adds_one_token s isAnchor; omega)
    match tok.val with
    | .scalar _ .plain => False
    | _ => True := by
  unfold scanAnchorOrAlias
  simp [ScannerState.emitAt, collectAnchorNameLoop_preserves_tokens,
        advance_preserves_tokens, Array.getElem_push_eq]
  cases isAnchor <;> trivial

-- Individual helper lemmas for content scan functions

theorem scanAnchorOrAlias_preserves_FlowInv (s : ScannerState) (isAnchor : Bool)
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s) :
    FlowContextPSV (scanAnchorOrAlias s isAnchor).tokens ∧
    FlowNestingInv (scanAnchorOrAlias s isAnchor) := by
  constructor
  · -- FlowContextPSV: anchor/alias is not plain scalar
    refine FlowContextPSV_of_prefix_and_new s.tokens (scanAnchorOrAlias s isAnchor).tokens h_fpsv ?_ ?_ ?_
    · have : (scanAnchorOrAlias s isAnchor).tokens.size = s.tokens.size + 1 :=
        scanAnchorOrAlias_adds_one_token s isAnchor
      omega
    · intro i hi
      exact scanAnchorOrAlias_preserves_prefix s isAnchor i hi
    · intro j hj hge _
      have : j = s.tokens.size := by
        have : (scanAnchorOrAlias s isAnchor).tokens.size = s.tokens.size + 1 :=
          scanAnchorOrAlias_adds_one_token s isAnchor
        omega
      subst this
      apply fpsv_of_not_plain
      exact scanAnchorOrAlias_new_token_not_plain s isAnchor
  · -- FlowNestingInv: flowLevel unchanged, non-flow token
    unfold FlowNestingInv at *
    have h_size : (scanAnchorOrAlias s isAnchor).tokens.size = s.tokens.size + 1 :=
      scanAnchorOrAlias_adds_one_token s isAnchor
    rw [h_size, scanAnchorOrAlias_preserves_flowLevel]
    unfold scanAnchorOrAlias
    generalize h_name : (collectAnchorNameLoop s.advance "" (s.inputEnd - s.advance.offset)).fst = name
    have h_coll := collectAnchorNameLoop_preserves_tokens s.advance "" (s.inputEnd - s.advance.offset)
    have h_adv := advance_preserves_tokens s
    simp only [ScannerState.emitAt, h_coll, h_adv, h_name]
    split <;> (rw [flowNesting_push_non_flow s.tokens ⟨s.currentPos, _⟩
           (by nofun) (by nofun) (by nofun) (by nofun)]; exact h_fni)

theorem scanVerbatimTag_preserves_flowLevel (s : ScannerState) (startPos : YamlPos) :
    (scanVerbatimTag s startPos).flowLevel = s.flowLevel := by
  unfold scanVerbatimTag
  simp [ScannerState.emitAt,
        collectVerbatimTagLoop_preserves_flowLevel, advance_preserves_flowLevel]

theorem scanSecondaryTag_preserves_flowLevel (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).flowLevel = s.flowLevel := by
  unfold scanSecondaryTag
  simp [ScannerState.emitAt, collectTagSuffixLoop_preserves_flowLevel, advance_preserves_flowLevel]

theorem scanNamedTag_preserves_flowLevel (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).flowLevel = s.flowLevel := by
  unfold scanNamedTag
  generalize h_handle : (collectTagHandleLoop s "" (inputEnd - s.offset)) = handle_result
  have h_fl : handle_result.2.2.flowLevel = s.flowLevel := by
    rw [← h_handle]
    exact collectTagHandleLoop_preserves_flowLevel s "" (inputEnd - s.offset)
  simp only [h_handle]
  split
  · simp [ScannerState.emitAt,
          collectTagSuffixLoop_preserves_flowLevel, h_fl]
  · simp [ScannerState.emitAt, h_fl]

theorem scanTag_preserves_flowLevel (s : ScannerState) :
    (scanTag s).flowLevel = s.flowLevel := by
  unfold scanTag
  simp only []
  split
  · simp only [scanVerbatimTag_preserves_flowLevel, advance_preserves_flowLevel]
  · simp only [scanSecondaryTag_preserves_flowLevel, advance_preserves_flowLevel]
  · simp only [scanNamedTag_preserves_flowLevel, advance_preserves_flowLevel]

theorem scanVerbatimTag_new_token_is_tag (s : ScannerState) (startPos : YamlPos)
    (h : s.tokens.size < (scanVerbatimTag s startPos).tokens.size) :
    ∃ handle suffix, ((scanVerbatimTag s startPos).tokens[s.tokens.size]'h).val = .tag handle suffix := by
  unfold scanVerbatimTag
  simp [ScannerState.emitAt, collectVerbatimTagLoop_preserves_tokens,
        advance_preserves_tokens, Array.getElem_push_eq]

theorem scanSecondaryTag_new_token_is_tag (s : ScannerState) (startPos : YamlPos)
    (h : s.tokens.size < (scanSecondaryTag s startPos).tokens.size) :
    ∃ handle suffix, ((scanSecondaryTag s startPos).tokens[s.tokens.size]'h).val = .tag handle suffix := by
  unfold scanSecondaryTag
  simp [ScannerState.emitAt, collectTagSuffixLoop_preserves_tokens,
        advance_preserves_tokens, Array.getElem_push_eq]

theorem scanNamedTag_new_token_is_tag (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat)
    (h : s.tokens.size < (scanNamedTag s startPos inputEnd).tokens.size) :
    ∃ handle suffix, ((scanNamedTag s startPos inputEnd).tokens[s.tokens.size]'h).val = .tag handle suffix := by
  unfold scanNamedTag
  generalize h_handle : (collectTagHandleLoop s "" (inputEnd - s.offset)) = handle_result
  have h_toks : handle_result.2.2.tokens = s.tokens := by
    rw [← h_handle]
    exact collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
  simp only [h_handle]
  split
  · -- foundBang = true
    simp [ScannerState.emitAt, collectTagSuffixLoop_preserves_tokens,
          h_toks, Array.getElem_push_eq]
  · -- foundBang = false
    simp [ScannerState.emitAt, h_toks, Array.getElem_push_eq]

theorem scanTag_new_token_is_tag (s : ScannerState)
    (h : s.tokens.size < (scanTag s).tokens.size) :
    ∃ handle suffix, ((scanTag s).tokens[s.tokens.size]'h).val = .tag handle suffix := by
  -- Unfold scanTag at both h and ⊢ so that `split` can generalize
  -- the peek? discriminant without breaking the dependent bound proof.
  -- simp only [] reduces the let bindings and struct update.
  -- Crucially, revert h before split so the dependent bound is part of the
  -- goal (universally quantified), allowing split to generalize the discriminant.
  unfold scanTag at h ⊢
  simp only [] at h ⊢
  revert h; split
  · -- some '<' → scanVerbatimTag
    intro h
    simp only [← advance_preserves_tokens s] at h ⊢
    exact scanVerbatimTag_new_token_is_tag s.advance s.currentPos h
  · -- some '!' → scanSecondaryTag
    intro h
    simp only [← advance_preserves_tokens s] at h ⊢
    exact scanSecondaryTag_new_token_is_tag s.advance s.currentPos h
  · -- catch-all → scanNamedTag
    intro h
    simp only [← advance_preserves_tokens s] at h ⊢
    exact scanNamedTag_new_token_is_tag s.advance s.currentPos s.inputEnd h

theorem scanTag_new_token_not_plain (s : ScannerState) :
    let tok := (scanTag s).tokens[s.tokens.size]'(by
      have := scanTag_adds_one_token s; omega)
    match tok.val with
    | .scalar _ .plain => False
    | _ => True := by
  have h_sz : s.tokens.size < (scanTag s).tokens.size := by
    have := scanTag_adds_one_token s; omega
  obtain ⟨handle, suffix, h_tag⟩ := scanTag_new_token_is_tag s h_sz
  simp only [h_tag]

theorem scanTag_preserves_FlowInv (s : ScannerState)
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s) :
    FlowContextPSV (scanTag s).tokens ∧ FlowNestingInv (scanTag s) := by
  constructor
  · -- FlowContextPSV: tag is not plain scalar
    refine FlowContextPSV_of_prefix_and_new s.tokens (scanTag s).tokens h_fpsv ?_ ?_ ?_
    · have : (scanTag s).tokens.size = s.tokens.size + 1 := scanTag_adds_one_token s
      omega
    · intro i hi
      exact scanTag_preserves_prefix s i hi
    · intro j hj hge _
      have : j = s.tokens.size := by
        have : (scanTag s).tokens.size = s.tokens.size + 1 := scanTag_adds_one_token s
        omega
      subst this
      apply fpsv_of_not_plain
      exact scanTag_new_token_not_plain s
  · -- FlowNestingInv: flowLevel unchanged, tag is non-flow token
    unfold FlowNestingInv at *
    have h_size : (scanTag s).tokens.size = s.tokens.size + 1 := scanTag_adds_one_token s
    rw [h_size, scanTag_preserves_flowLevel]
    -- scanTag emits one non-flow token
    unfold scanTag
    simp only []
    split
    · -- Case: verbatim tag
      unfold scanVerbatimTag
      simp only [ScannerState.emitAt, collectVerbatimTagLoop_preserves_tokens,
                 advance_preserves_tokens]
      rw [flowNesting_push_non_flow s.tokens ⟨s.currentPos, .tag _ _⟩
           (by nofun) (by nofun) (by nofun) (by nofun)]
      exact h_fni
    · -- Case: secondary tag
      unfold scanSecondaryTag
      simp only [ScannerState.emitAt, collectTagSuffixLoop_preserves_tokens,
                 advance_preserves_tokens]
      rw [flowNesting_push_non_flow s.tokens ⟨s.currentPos, .tag _ _⟩
           (by nofun) (by nofun) (by nofun) (by nofun)]
      exact h_fni
    · -- Case: named tag
      unfold scanNamedTag
      simp only [ScannerState.emitAt]
      -- After unfolding, we have nested lets with collectTagHandleLoop
      -- The key insight: the final state tokens depend on foundBang
      -- Let's name the result of collectTagHandleLoop
      generalize h_collect : collectTagHandleLoop s.advance "" (s.inputEnd - s.advance.offset) = result
      -- result is a triple (chars, foundBang, s_after_handle)
      obtain ⟨chars, foundBang, s_after_handle⟩ := result
      -- Now split on foundBang
      cases foundBang
      · -- Case: foundBang = false, so suffix_or_chars = chars, s_after_suffix = s_after_handle
        simp only []
        -- Need to show s_after_handle.tokens = s.tokens
        have h_tok : s_after_handle.tokens = s.advance.tokens := by
          have := collectTagHandleLoop_preserves_tokens s.advance "" (s.inputEnd - s.advance.offset)
          rw [h_collect] at this
          simp at this
          exact this
        -- Simplify the if-then-else expressions (foundBang = false here)
        simp
        rw [h_tok, advance_preserves_tokens]
        rw [flowNesting_push_non_flow s.tokens ⟨s.currentPos, .tag _ _⟩
             (by nofun) (by nofun) (by nofun) (by nofun)]
        exact h_fni
      · -- Case: foundBang = true, so we call collectTagSuffixLoop
        simp only []
        -- Need to show (collectTagSuffixLoop s_after_handle ...).snd.tokens = s.tokens
        have h_tok1 : s_after_handle.tokens = s.advance.tokens := by
          have := collectTagHandleLoop_preserves_tokens s.advance "" (s.inputEnd - s.advance.offset)
          rw [h_collect] at this
          simp at this
          exact this
        -- Simplify the if-then-else expressions (foundBang = true here)
        simp
        rw [collectTagSuffixLoop_preserves_tokens, h_tok1, advance_preserves_tokens]
        rw [flowNesting_push_non_flow s.tokens ⟨s.currentPos, .tag _ _⟩
             (by nofun) (by nofun) (by nofun) (by nofun)]
        exact h_fni

-- Helper: scalar scan functions preserve flowLevel

theorem consumeExactSpaces_preserves_flowLevel (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.flowLevel = s.flowLevel := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces
    split
    · simp [ih, advance_preserves_flowLevel]
    · rfl

theorem consumeNewline_preserves_flowLevel (s : ScannerState) :
    (consumeNewline s).flowLevel = s.flowLevel := by
  unfold consumeNewline
  split
  · simp [advance_preserves_flowLevel]
  · simp only []
    split
    · simp [advance_preserves_flowLevel]
    · simp [advance_preserves_flowLevel]
  · rfl

theorem collectLineContentLoop_preserves_flowLevel (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih, advance_preserves_flowLevel]
    · rfl

theorem collectBlockScalarLoop_preserves_flowLevel (s : ScannerState) (rawContent : String)
    (fuel contentIndent inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · cases h_eq : consumeExactSpaces s contentIndent with
      | mk spacesConsumed s_after_spaces =>
        have h_fl_spaces : s_after_spaces.flowLevel = s.flowLevel := by
          have := consumeExactSpaces_preserves_flowLevel s contentIndent
          rw [h_eq] at this; exact this
        simp only []
        split
        · exact h_fl_spaces
        · split
          · rw [ih, consumeNewline_preserves_flowLevel, h_fl_spaces]
          · split
            · rfl
            · have h_fl_line := collectLineContentLoop_preserves_flowLevel
                  s_after_spaces ""
                  (inputEnd - s_after_spaces.offset + 1)
              split
              · split
                · rw [ih, consumeNewline_preserves_flowLevel, h_fl_line, h_fl_spaces]
                · rw [ih, h_fl_line, h_fl_spaces]
              · rw [h_fl_line, h_fl_spaces]

theorem collectCommentTextLoop_preserves_flowLevel (s : ScannerState) (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' ih =>
    unfold collectCommentTextLoop
    split
    · split
      · rfl
      · rw [ih, advance_preserves_flowLevel]
    · rfl

theorem scanBlockScalarSkipComment_preserves_flowLevel (s : ScannerState) :
    (scanBlockScalarSkipComment s).flowLevel = s.flowLevel := by
  unfold scanBlockScalarSkipComment
  split
  · split
    · simp only []
      split
      · simp only [collectCommentTextLoop_preserves_flowLevel, advance_preserves_flowLevel]
      · rfl
    · rfl
  · rfl

theorem parseBlockHeaderLoop_preserves_flowLevel (s : ScannerState) (chomp : ChompStyle)
    (explicitOffset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp explicitOffset fuel).snd.snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s chomp explicitOffset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop
    split
    · rw [ih, advance_preserves_flowLevel]
    · rw [ih, advance_preserves_flowLevel]
    · split
      · rw [ih, advance_preserves_flowLevel]
      · rfl
    · rfl

theorem scanBlockScalarConsumeNewline_preserves_flowLevel (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq
      exact consumeNewline_preserves_flowLevel s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

theorem scanBlockScalar_preserves_flowLevel (s s' : ScannerState)
    (h_ok : scanBlockScalar s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanBlockScalar at h_ok
  simp only at h_ok
  split at h_ok
  · contradiction
  · rename_i s_after_newline heq
    have h_fl : s_after_newline.flowLevel = s.flowLevel := by
      rw [scanBlockScalarConsumeNewline_preserves_flowLevel _ _ heq,
          scanBlockScalarSkipComment_preserves_flowLevel,
          skipWhitespace_preserves_flowLevel,
          parseBlockHeaderLoop_preserves_flowLevel,
          advance_preserves_flowLevel]
    unfold scanBlockScalarBody at h_ok
    simp only at h_ok
    -- Split on autoDetectErr? match
    split at h_ok
    · -- Case: autoDetectErr? = some err (error case)
      contradiction
    · -- Case: autoDetectErr? = none (success case)
      simp only [ScannerState.emitAt] at h_ok
      injection h_ok with h_eq; subst h_eq
      simp [collectBlockScalarLoop_preserves_flowLevel, h_fl]

theorem collectHexDigitsLoop_preserves_flowLevel (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.flowLevel = s.flowLevel := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    split
    · split
      · rw [ih, advance_preserves_flowLevel]
      · rfl
    · rfl

theorem parseHexEscape_preserves_flowLevel (s : ScannerState) (digits : Nat)
    (result : Char × ScannerState) (h : parseHexEscape s digits = .ok result) :
    result.snd.flowLevel = s.flowLevel := by
  unfold parseHexEscape at h
  simp only [] at h
  split at h
  · -- Case: hex.length != digits (error case)
    contradiction
  · -- Case: hex.length = digits
    split at h
    · -- Case: val < 0x110000 (success)
      injection h with h_eq; subst h_eq
      exact collectHexDigitsLoop_preserves_flowLevel s "" digits
    · -- Case: val >= 0x110000 (error)
      contradiction

theorem processEscape_preserves_flowLevel (s : ScannerState) (result : Char × ScannerState)
    (h : processEscape s = .ok result) :
    result.snd.flowLevel = s.flowLevel := by
  unfold processEscape at h
  split at h <;> try contradiction
  split at h
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · injection h with h_eq; subst h_eq; exact advance_preserves_flowLevel s
  · simp only [] at h; exact parseHexEscape_preserves_flowLevel _ _ _ h |>.trans (advance_preserves_flowLevel s)
  · simp only [] at h; exact parseHexEscape_preserves_flowLevel _ _ _ h |>.trans (advance_preserves_flowLevel s)
  · simp only [] at h; exact parseHexEscape_preserves_flowLevel _ _ _ h |>.trans (advance_preserves_flowLevel s)
  · contradiction

theorem foldQuotedNewlinesLoop_preserves_flowLevel (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.flowLevel = s.flowLevel := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    simp only []
    split
    · split
      · rw [ih, consumeNewline_preserves_flowLevel, skipSpaces_preserves_flowLevel]
      · rfl
    · rfl

theorem foldQuotedNewlines_preserves_flowLevel (s : ScannerState) (result : String × ScannerState)
    (h : foldQuotedNewlines s = .ok result) :
    result.snd.flowLevel = s.flowLevel := by
  unfold foldQuotedNewlines at h
  simp only [] at h
  split at h
  · split at h <;> try contradiction
    split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_flowLevel, skipSpaces_preserves_flowLevel,
            foldQuotedNewlinesLoop_preserves_flowLevel, consumeNewline_preserves_flowLevel]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_flowLevel, skipSpaces_preserves_flowLevel,
            foldQuotedNewlinesLoop_preserves_flowLevel, consumeNewline_preserves_flowLevel]
  · split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_flowLevel, skipSpaces_preserves_flowLevel,
            foldQuotedNewlinesLoop_preserves_flowLevel, consumeNewline_preserves_flowLevel]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_flowLevel, skipSpaces_preserves_flowLevel,
            foldQuotedNewlinesLoop_preserves_flowLevel, consumeNewline_preserves_flowLevel]

theorem collectDoubleQuotedLoop_preserves_flowLevel (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (result : String × ScannerState)
    (h : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result) :
    result.snd.flowLevel = s.flowLevel := by
  sorry

theorem scanDoubleQuoted_preserves_flowLevel (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_fl_collect := collectDoubleQuotedLoop_preserves_flowLevel _ _ _ _ _ _ _ _ heq
  split at h_ok
  · -- Case: !s.inFlow = true, need to validate trailing content
    split at h_ok <;> try contradiction
    injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_flowLevel, h_fl_collect, advance_preserves_flowLevel]
  · -- Case: !s.inFlow = false, no validation needed
    injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_flowLevel, h_fl_collect, advance_preserves_flowLevel]

theorem collectSingleQuotedLoop_preserves_flowLevel (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (result : String × ScannerState)
    (h : collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result) :
    result.snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s content with
  | zero => unfold collectSingleQuotedLoop at h; contradiction
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at h
    split at h <;> try contradiction
    · -- Case: peek? = some '\''
      rename_i heq_quote
      simp only [] at h
      split at h
      · -- Case: peek? after advance = some '\'' (escaped quote)
        exact ih _ _ h |>.trans (advance_preserves_flowLevel _) |>.trans (advance_preserves_flowLevel s)
      · -- Case: closing quote (other character or none)
        injection h with h_eq; subst h_eq
        exact advance_preserves_flowLevel s
    · -- Case: peek? = some c (other character)
      split at h <;> try contradiction
      · -- Line break: fold newlines
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i folded_result heq_fold
        have h_fl_fold := foldQuotedNewlines_preserves_flowLevel _ _ heq_fold
        split at h <;> try contradiction
        split at h <;> try contradiction
        split at h <;> try contradiction
        exact ih _ _ h |>.trans h_fl_fold
      · -- Regular character
        exact ih _ _ h |>.trans (advance_preserves_flowLevel s)

theorem scanSingleQuoted_preserves_flowLevel (s s' : ScannerState)
    (h_ok : scanSingleQuoted s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanSingleQuoted at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_fl_collect := collectSingleQuotedLoop_preserves_flowLevel _ _ _ _ _ _ _ _ heq
  split at h_ok
  · -- Case: !s.inFlow = true, need to validate trailing content
    split at h_ok <;> try contradiction
    injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_flowLevel, h_fl_collect, advance_preserves_flowLevel]
  · -- Case: !s.inFlow = false, no validation needed
    injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_flowLevel, h_fl_collect, advance_preserves_flowLevel]

theorem collectPlainScalarLoop_preserves_flowLevel (s : ScannerState) (content spaces : String) (fuel : Nat)
    (inFlow : Bool) (contentIndent inputEnd : Nat) (result : PlainScalarResult)
    (h : collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd = .ok result) :
    result.state.flowLevel = s.flowLevel := by
  sorry

theorem scanPlainScalar_preserves_flowLevel (s s' : ScannerState)
    (h_ok : scanPlainScalar s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanPlainScalar at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_fl_collect := collectPlainScalarLoop_preserves_flowLevel _ _ _ _ _ _ _ _ heq
  injection h_ok with h_eq; subst h_eq
  simp [emitAt_preserves_flowLevel, h_fl_collect]

theorem scanPlainScalar_new_token_is_plain (s s' : ScannerState)
    (h_ok : scanPlainScalar s = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    ∃ content, (s'.tokens[s.tokens.size]'hj).val = .scalar content .plain := by
  unfold scanPlainScalar at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok; contradiction
  rename_i result heq
  injection h_ok with h_eq; subst h_eq
  have h_tok : result.state.tokens = s.tokens :=
    collectPlainScalarLoop_preserves_tokens s "" "" _ _ _ _ _ heq
  unfold ScannerState.emitAt
  simp only [h_tok, Array.getElem_push_eq]
  exact ⟨_, rfl⟩

theorem scanBlockScalar_preserves_FlowInv (s s' : ScannerState)
    (h_ok : scanBlockScalar s = .ok s')
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s) :
    FlowContextPSV s'.tokens ∧ FlowNestingInv s' := by
  constructor
  · -- FlowContextPSV: block scalar is not plain
    refine FlowContextPSV_of_prefix_and_new s.tokens s'.tokens h_fpsv ?_ ?_ ?_
    · have : s'.tokens.size = s.tokens.size + 1 := by
        have := scanBlockScalar_adds_one_token s s' h_ok
        omega
      omega
    · intro i hi
      exact scanBlockScalar_preserves_prefix s s' h_ok i hi
    · intro j hj hge _
      have : j = s.tokens.size := by
        have : s'.tokens.size = s.tokens.size + 1 := by
          have := scanBlockScalar_adds_one_token s s' h_ok
          omega
        omega
      subst this
      apply fpsv_of_not_plain
      -- Token is block scalar, not plain
      unfold scanBlockScalar at h_ok
      simp only [] at h_ok
      split at h_ok; contradiction
      unfold scanBlockScalarBody at h_ok
      simp only [] at h_ok
      split at h_ok
      · contradiction
      · simp only [ScannerState.emitAt] at h_ok
        injection h_ok with h_eq; subst h_eq
        simp only [Array.getElem_push_eq]
        -- The token is .scalar _ (if peek? == '|' then literal else folded)
        -- which cannot be .scalar _ plain
        sorry
  · -- FlowNestingInv: flowLevel unchanged, scalar is non-flow token
    unfold FlowNestingInv at *
    have h_size : s'.tokens.size = s.tokens.size + 1 := by
      have := scanBlockScalar_adds_one_token s s' h_ok
      omega
    rw [h_size, scanBlockScalar_preserves_flowLevel s s' h_ok]
    unfold scanBlockScalar at h_ok
    simp only [] at h_ok
    split at h_ok; contradiction
    rename_i s_after_newline heq
    unfold scanBlockScalarBody at h_ok
    simp only [] at h_ok
    split at h_ok
    · -- autoDetectErr? = some err
      contradiction
    · -- autoDetectErr? = none
      simp only [ScannerState.emitAt] at h_ok
      injection h_ok with h_eq; subst h_eq
      sorry

theorem scanDoubleQuoted_preserves_FlowInv (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s')
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s) :
    FlowContextPSV s'.tokens ∧ FlowNestingInv s' := by
  constructor
  · -- FlowContextPSV: double quoted scalar is not plain
    refine FlowContextPSV_of_prefix_and_new s.tokens s'.tokens h_fpsv ?_ ?_ ?_
    · have : s'.tokens.size = s.tokens.size + 1 := by
        have := scanDoubleQuoted_adds_one_token s s' h_ok
        omega
      omega
    · intro i hi
      exact scanDoubleQuoted_preserves_prefix s s' h_ok i hi
    · intro j hj hge _
      have : j = s.tokens.size := by
        have : s'.tokens.size = s.tokens.size + 1 := by
          have := scanDoubleQuoted_adds_one_token s s' h_ok
          omega
        omega
      subst this
      apply fpsv_of_not_plain
      unfold scanDoubleQuoted at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok
      split at h_ok <;> try contradiction
      sorry
  · -- FlowNestingInv: flowLevel unchanged
    unfold FlowNestingInv at *
    have h_size : s'.tokens.size = s.tokens.size + 1 := by
      have := scanDoubleQuoted_adds_one_token s s' h_ok
      omega
    rw [h_size, scanDoubleQuoted_preserves_flowLevel s s' h_ok]
    unfold scanDoubleQuoted at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok <;> try contradiction
    sorry

theorem scanSingleQuoted_preserves_FlowInv (s s' : ScannerState)
    (h_ok : scanSingleQuoted s = .ok s')
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s) :
    FlowContextPSV s'.tokens ∧ FlowNestingInv s' := by
  constructor
  · -- FlowContextPSV: single quoted scalar is not plain
    refine FlowContextPSV_of_prefix_and_new s.tokens s'.tokens h_fpsv ?_ ?_ ?_
    · have : s'.tokens.size = s.tokens.size + 1 := by
        have := scanSingleQuoted_adds_one_token s s' h_ok
        omega
      omega
    · intro i hi
      exact scanSingleQuoted_preserves_prefix s s' h_ok i hi
    · intro j hj hge _
      have : j = s.tokens.size := by
        have : s'.tokens.size = s.tokens.size + 1 := by
          have := scanSingleQuoted_adds_one_token s s' h_ok
          omega
        omega
      subst this
      apply fpsv_of_not_plain
      unfold scanSingleQuoted at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok
      split at h_ok <;> try contradiction
      sorry
  · -- FlowNestingInv: flowLevel unchanged
    unfold FlowNestingInv at *
    have h_size : s'.tokens.size = s.tokens.size + 1 := by
      have := scanSingleQuoted_adds_one_token s s' h_ok
      omega
    rw [h_size, scanSingleQuoted_preserves_flowLevel s s' h_ok]
    unfold scanSingleQuoted at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok <;> try contradiction
    sorry

theorem scanPlainScalar_preserves_FlowInv (s s' : ScannerState)
    (h_ok : scanPlainScalar s = .ok s')
    (h_canStart : ∃ c, s.peek? = some c ∧
        canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true)
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s) :
    FlowContextPSV s'.tokens ∧ FlowNestingInv s' := by
  constructor
  · -- FlowContextPSV: plain scalar is scannable in flow context
    refine FlowContextPSV_of_prefix_and_new s.tokens s'.tokens h_fpsv ?_ ?_ ?_
    · have : s'.tokens.size = s.tokens.size + 1 := by
        have := scanPlainScalar_adds_one_token s s' h_ok
        omega
      omega
    · intro i hi
      exact scanPlainScalar_preserves_prefix s s' h_ok i hi
    · intro j hj hge h_flowNest
      have : j = s.tokens.size := by
        have : s'.tokens.size = s.tokens.size + 1 := by
          have := scanPlainScalar_adds_one_token s s' h_ok
          omega
        omega
      subst this
      -- At j = s.tokens.size, the token is a plain scalar
      obtain ⟨content, h_tok⟩ := scanPlainScalar_new_token_is_plain s s' h_ok hj
      rw [h_tok]
      -- Need to show: ScalarScannable ⟨content, .plain, none, none, none⟩ true
      -- Since flowNesting > 0, by FlowNestingInv we have s.flowLevel > 0
      have h_flowLevel : s.flowLevel > 0 := by
        unfold FlowNestingInv at h_fni
        rw [← h_fni]
        sorry
      -- Since s.flowLevel > 0, we have s.inFlow = true
      have h_inFlow : s.inFlow = true := by
        unfold ScannerState.inFlow
        simp [h_flowLevel]
      -- scanPlainScalar_content_valid gives us ScalarScannable _ s.inFlow
      have h_cv := scanPlainScalar_content_valid s s' h_ok h_canStart hj
      rw [h_tok] at h_cv
      -- Since s.inFlow = true, we have ScalarScannable _ true
      rw [h_inFlow] at h_cv
      exact h_cv
  · -- FlowNestingInv: flowLevel unchanged
    unfold FlowNestingInv at *
    have h_size : s'.tokens.size = s.tokens.size + 1 := by
      have := scanPlainScalar_adds_one_token s s' h_ok
      omega
    rw [h_size, scanPlainScalar_preserves_flowLevel s s' h_ok]
    unfold scanPlainScalar at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok <;> try contradiction
    sorry

/-- Content dispatch preserves `FlowInv` by delegating to individual scan function lemmas. -/
theorem dispatchContent_preserves_FlowInv
    (s : ScannerState) (c : Char)
    (h_peek : s.peek? = some c)
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchContent s c = .ok s') :
    FlowContextPSV s'.tokens ∧ FlowNestingInv s' := by
  unfold scanNextToken_dispatchContent at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · -- c == '&'
    injection h_ok with h_eq; subst h_eq
    exact scanAnchorOrAlias_preserves_FlowInv s true h_fpsv h_fni
  · split at h_ok
    · -- c == '*'
      injection h_ok with h_eq; subst h_eq
      exact scanAnchorOrAlias_preserves_FlowInv s false h_fpsv h_fni
    · split at h_ok
      · -- c == '!'
        injection h_ok with h_eq; subst h_eq
        exact scanTag_preserves_FlowInv s h_fpsv h_fni
      · split at h_ok
        · -- c == '|' or c == '>'
          split at h_ok
          · contradiction
          · rename_i s_bs h_bs
            injection h_ok with h_eq; subst h_eq
            exact scanBlockScalar_preserves_FlowInv s s_bs h_bs h_fpsv h_fni
        · split at h_ok
          · -- c == '"'
            split at h_ok
            · contradiction
            · rename_i s_dq h_dq
              split at h_ok
              · injection h_ok with h_eq; subst h_eq
                exact scanDoubleQuoted_preserves_FlowInv s s_dq h_dq h_fpsv h_fni
              · injection h_ok with h_eq; subst h_eq
                exact scanDoubleQuoted_preserves_FlowInv s s_dq h_dq h_fpsv h_fni
          · split at h_ok
            · -- c == '\''
              split at h_ok
              · contradiction
              · rename_i s_sq h_sq
                split at h_ok
                · injection h_ok with h_eq; subst h_eq
                  exact scanSingleQuoted_preserves_FlowInv s s_sq h_sq h_fpsv h_fni
                · injection h_ok with h_eq; subst h_eq
                  exact scanSingleQuoted_preserves_FlowInv s s_sq h_sq h_fpsv h_fni
            · split at h_ok
              · -- Plain scalar
                rename_i h_canStart
                split at h_ok
                · contradiction
                · rename_i s_ps h_ps
                  injection h_ok with h_eq; subst h_eq
                  have h_cs : ∃ c', s.peek? = some c' ∧
                      canStartPlainScalarBool c' (s.peekAt? 1) s.inFlow = true := by
                    exact ⟨c, h_peek, h_canStart⟩
                  exact scanPlainScalar_preserves_FlowInv s s_ps h_ps h_cs h_fpsv h_fni
              · simp at h_ok

/-! ### pushSequenceIndent / pushMappingIndent token type lemmas -/

theorem pushSequenceIndent_new_token_is_blockSequenceStart (s : ScannerState) (col : Int)
    (h : col > s.currentIndent) :
    (pushSequenceIndent s col).tokens[s.tokens.size]'(by
      unfold pushSequenceIndent
      simp [h, ScannerState.emit, Array.size_push]) =
      { pos := s.currentPos, val := YamlToken.blockSequenceStart } := by
  unfold pushSequenceIndent
  simp [h, ScannerState.emit, Array.getElem_push_eq]

theorem pushMappingIndent_new_token_is_blockMappingStart (s : ScannerState) (col : Int)
    (h : col > s.currentIndent) :
    (pushMappingIndent s col).tokens[s.tokens.size]'(by
      unfold pushMappingIndent
      simp [h, ScannerState.emit, Array.size_push]) =
      { pos := s.currentPos, val := YamlToken.blockMappingStart } := by
  unfold pushMappingIndent
  simp [h, ScannerState.emit, Array.getElem_push_eq]

/-! ### Block indicator helper lemmas -/

theorem scanBlockEntry_preserves_FlowContextPSV
    (s s' : ScannerState) (h_fpsv : FlowContextPSV s.tokens)
    (h_ok : scanBlockEntry s = .ok s') :
    FlowContextPSV s'.tokens := by
  -- scanBlockEntry emits blockEntry (and possibly blockSequenceStart)
  -- Neither is a plain scalar
  refine FlowContextPSV_of_prefix_and_new s.tokens s'.tokens h_fpsv ?_ ?_ ?_
  · -- h_mono
    have : s'.tokens.size ≥ s.tokens.size + 1 := scanBlockEntry_adds_tokens s s' h_ok
    omega
  · -- h_prefix
    intro i hi
    exact scanBlockEntry_preserves_prefix s s' h_ok i hi
  · -- h_new: show new tokens are not plain scalars
    intro j hj hge _
    apply fpsv_of_not_plain
    -- Need to prove: match s'.tokens[j].val with | .scalar _ .plain => False | _ => True
    -- scanBlockEntry emits blockEntry and possibly blockSequenceStart
    -- Both are non-plain tokens
    sorry  -- TODO: Complete proof showing emitted tokens are blockEntry/blockSequenceStart

theorem scanBlockEntry_preserves_FlowNestingInv
    (s s' : ScannerState) (h_fni : FlowNestingInv s)
    (h_ok : scanBlockEntry s = .ok s') :
    FlowNestingInv s' := by
  -- scanBlockEntry: emits non-flow tokens, preserves flowLevel
  unfold scanBlockEntry at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · contradiction
    · injection h_ok with h_eq; subst h_eq
      -- Case: !inFlow, no tab error
      -- s' = (pushSequenceIndent s s.col).emit(blockEntry).advance
      unfold pushSequenceIndent
      split
      · rename_i h_indent
        -- pushSequenceIndent emitted blockSequenceStart, then emit blockEntry
        -- Use FlowNestingInv_emit_non_flow twice
        have h_after_start : FlowNestingInv (s.emit .blockSequenceStart) := by
          apply FlowNestingInv_emit_non_flow s .blockSequenceStart h_fni <;> nofun
        -- After emitting blockSequenceStart, the state is modified (indents updated)
        -- but FlowNestingInv is preserved. Now emit blockEntry from modified state.
        let s_with_indent := { s.emit .blockSequenceStart with
              indents := (s.emit .blockSequenceStart).indents.push { column := ↑s.col, isSequence := true } }
        have h_indents : FlowNestingInv s_with_indent := by
          unfold FlowNestingInv at *
          -- s_with_indent only differs in indents field, tokens and flowLevel are the same
          show flowNesting s_with_indent.tokens s_with_indent.tokens.size = s_with_indent.flowLevel
          -- s_with_indent.tokens = (s.emit .blockSequenceStart).tokens (same reference)
          -- s_with_indent.flowLevel = (s.emit .blockSequenceStart).flowLevel (same reference)
          -- s_with_indent.tokens.size = (s.emit .blockSequenceStart).tokens.size (same reference)
          -- So the goal is exactly h_after_start
          exact h_after_start
        have h_after_entry : FlowNestingInv (s_with_indent.emit .blockEntry) := by
          apply FlowNestingInv_emit_non_flow s_with_indent .blockEntry h_indents <;> nofun
        -- Finally, advance preserves FlowNestingInv
        unfold FlowNestingInv at *
        simp only [advance_preserves_flowLevel, advance_preserves_tokens] at h_after_entry ⊢
        exact h_after_entry
      · rename_i h_indent
        -- pushSequenceIndent returned s unchanged, just emit blockEntry
        have h_after_entry : FlowNestingInv (s.emit .blockEntry) := by
          apply FlowNestingInv_emit_non_flow s .blockEntry h_fni <;> nofun
        unfold FlowNestingInv at *
        simp only [advance_preserves_flowLevel, advance_preserves_tokens] at h_after_entry ⊢
        exact h_after_entry
  · injection h_ok with h_eq; subst h_eq
    -- Case: inFlow, no pushSequenceIndent, just emit blockEntry
    have h_after_entry : FlowNestingInv (s.emit .blockEntry) := by
      apply FlowNestingInv_emit_non_flow s .blockEntry h_fni <;> nofun
    unfold FlowNestingInv at *
    simp only [advance_preserves_flowLevel, advance_preserves_tokens] at h_after_entry ⊢
    exact h_after_entry

theorem scanKey_preserves_FlowContextPSV
    (s s' : ScannerState) (h_fpsv : FlowContextPSV s.tokens)
    (h_ok : scanKey s = .ok s') :
    FlowContextPSV s'.tokens := by
  -- scanKey emits .key (and possibly .blockMappingStart), never plain scalars
  -- Use same pattern as scanBlockEntry
  refine FlowContextPSV_of_prefix_and_new s.tokens s'.tokens h_fpsv ?_ ?_ ?_
  · -- h_mono
    have : s'.tokens.size ≥ s.tokens.size + 1 := scanKey_adds_one_token s s' h_ok
    omega
  · -- h_prefix
    intro i hi
    exact scanKey_preserves_prefix s s' h_ok i hi
  · -- h_new
    intro j hj hge _
    apply fpsv_of_not_plain
    -- scanKey emits .key and possibly .blockMappingStart
    sorry

theorem scanKey_preserves_FlowNestingInv
    (s s' : ScannerState) (h_fni : FlowNestingInv s)
    (h_ok : scanKey s = .ok s') :
    FlowNestingInv s' := by
  -- scanKey: emits non-flow tokens (.key, optionally .blockMappingStart), preserves flowLevel
  unfold scanKey at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · split at h_ok
      · contradiction
      · injection h_ok with h_eq; subst h_eq
        unfold FlowNestingInv at *
        simp only [advance_preserves_flowLevel, advance_preserves_tokens]
        -- pushMappingIndent may emit blockMappingStart, then emit .key
        unfold pushMappingIndent
        split
        · rename_i h_indent
          -- pushMappingIndent emitted blockMappingStart, then emit .key
          -- Use FlowNestingInv_emit_non_flow twice
          have h_after_start : FlowNestingInv (s.emit .blockMappingStart) := by
            apply FlowNestingInv_emit_non_flow s .blockMappingStart h_fni <;> nofun
          -- After emitting blockMappingStart, the state is modified (indents updated)
          let s_with_indent := { s.emit .blockMappingStart with
                indents := (s.emit .blockMappingStart).indents.push { column := ↑s.col, isSequence := false } }
          have h_indents : FlowNestingInv s_with_indent := by
            unfold FlowNestingInv at *
            exact h_after_start
          have h_after_key : FlowNestingInv (s_with_indent.emit .key) := by
            apply FlowNestingInv_emit_non_flow s_with_indent .key h_indents <;> nofun
          -- Finally, advance preserves FlowNestingInv
          unfold FlowNestingInv at *
          simp at h_after_key ⊢
          exact h_after_key
        · -- No blockMappingStart, just .key
          unfold ScannerState.emit
          simp [Array.size_push]
          have : flowNesting (s.tokens.push ⟨s.currentPos, .key⟩) (s.tokens.size + 1) =
                 flowNesting s.tokens s.tokens.size := by
            apply flowNesting_push_non_flow <;> nofun
          rw [this]
          exact h_fni
    · injection h_ok with h_eq; subst h_eq
      unfold FlowNestingInv at *
      simp only [advance_preserves_flowLevel, advance_preserves_tokens]
      unfold pushMappingIndent
      split
      · rename_i h_indent
        -- pushMappingIndent emitted blockMappingStart, then emit .key
        have h_after_start : FlowNestingInv (s.emit .blockMappingStart) := by
          apply FlowNestingInv_emit_non_flow s .blockMappingStart h_fni <;> nofun
        let s_with_indent := { s.emit .blockMappingStart with
              indents := (s.emit .blockMappingStart).indents.push { column := ↑s.col, isSequence := false } }
        have h_indents : FlowNestingInv s_with_indent := by
          unfold FlowNestingInv at *
          exact h_after_start
        have h_after_key : FlowNestingInv (s_with_indent.emit .key) := by
          apply FlowNestingInv_emit_non_flow s_with_indent .key h_indents <;> nofun
        unfold FlowNestingInv at *
        simp at h_after_key ⊢
        exact h_after_key
      · -- No blockMappingStart, just .key
        unfold ScannerState.emit
        simp [Array.size_push]
        have : flowNesting (s.tokens.push ⟨s.currentPos, .key⟩) (s.tokens.size + 1) =
               flowNesting s.tokens s.tokens.size := by
          apply flowNesting_push_non_flow <;> nofun
        rw [this]
        exact h_fni
  · split at h_ok
    · split at h_ok
      · contradiction
      · injection h_ok with h_eq; subst h_eq
        unfold FlowNestingInv at *
        simp only [advance_preserves_flowLevel, advance_preserves_tokens]
        unfold ScannerState.emit
        simp [Array.size_push]
        have : flowNesting (s.tokens.push ⟨s.currentPos, .key⟩) (s.tokens.size + 1) =
               flowNesting s.tokens s.tokens.size := by
          apply flowNesting_push_non_flow <;> nofun
        rw [this]
        exact h_fni
    · injection h_ok with h_eq; subst h_eq
      unfold FlowNestingInv at *
      simp only [advance_preserves_flowLevel, advance_preserves_tokens]
      unfold ScannerState.emit
      simp [Array.size_push]
      have : flowNesting (s.tokens.push ⟨s.currentPos, .key⟩) (s.tokens.size + 1) =
             flowNesting s.tokens s.tokens.size := by
        apply flowNesting_push_non_flow <;> nofun
      rw [this]
      exact h_fni

theorem scanValue_preserves_FlowContextPSV
    (s s' : ScannerState) (h_fpsv : FlowContextPSV s.tokens)
    (h_ok : scanValue s = .ok s') :
    FlowContextPSV s'.tokens := by
  -- scanValue emits .value (and possibly .key, .blockMappingStart via scanValuePrepare)
  -- None are plain scalars
  refine FlowContextPSV_of_prefix_and_new s.tokens s'.tokens h_fpsv ?_ ?_ ?_
  · -- h_mono
    have : s'.tokens.size ≥ s.tokens.size + 1 := scanValue_adds_tokens s s' h_ok
    omega
  · -- h_prefix
    intro i hi
    -- scanValue_preserves_prefix has complex requirements about simpleKey
    sorry
  · -- h_new
    intro j hj hge _
    apply fpsv_of_not_plain
    -- scanValue emits .value and possibly .key, .blockMappingStart
    sorry

theorem scanValue_preserves_FlowNestingInv
    (s s' : ScannerState) (h_fni : FlowNestingInv s)
    (h_ok : scanValue s = .ok s') :
    FlowNestingInv s' := by
  -- scanValue: complex due to scanValuePrepare, but all emitted tokens are non-flow
  -- and flowLevel is preserved throughout
  -- scanValuePrepare may modify tokens (setIfInBounds, pushMappingIndent)
  -- but doesn't change flowLevel. Then emit .value (non-flow token).
  unfold scanValue at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  split at h_ok <;> try contradiction
  injection h_ok with h_eq; subst h_eq
  -- After scanValueClearKey, scanValueValidate, scanValuePrepare, we emit .value, advance, then scanValueTabCheck
  -- The result is: { advance(emit(scanValuePrepare(...)).value) with simpleKeyAllowed := true, explicitKeyLine := none }

  -- Key observations:
  -- 1. scanValueClearKey preserves FlowNestingInv (only modifies simpleKey field)
  -- 2. scanValuePrepare preserves FlowNestingInv (complex - needs helper lemma)
  -- 3. emit .value preserves FlowNestingInv (non-flow token)
  -- 4. advance preserves FlowNestingInv
  -- 5. Setting simpleKeyAllowed and explicitKeyLine preserves FlowNestingInv

  -- For now, this is complex enough to warrant a sorry
  sorry

/-- Block indicators dispatch preserves `FlowInv`. -/
theorem dispatchBlockIndicators_preserves_FlowInv
    (s : ScannerState) (c : Char)
    (h_fpsv : FlowContextPSV s.tokens) (h_fni : FlowNestingInv s)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    FlowContextPSV s'.tokens ∧ FlowNestingInv s' := by
  -- Block indicators: `-` (blockEntry), `?` (key), `:` (value)
  unfold scanNextToken_dispatchBlockIndicators at h_ok
  simp only [bind, bind_ok_simp, pure, Pure.pure, Except.pure] at h_ok
  simp only [Except.bind] at h_ok
  repeat (any_goals (split at h_ok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  -- After splitting, we have 3 cases: scanBlockEntry, scanKey, scanValue
  -- scanBlockEntry case
  all_goals (try (
    rename_i s_be h_be
    constructor
    · exact scanBlockEntry_preserves_FlowContextPSV s s_be h_fpsv h_be
    · exact scanBlockEntry_preserves_FlowNestingInv s s_be h_fni h_be))
  -- scanKey case
  all_goals (try (
    rename_i s_k h_k
    constructor
    · exact scanKey_preserves_FlowContextPSV s s_k h_fpsv h_k
    · exact scanKey_preserves_FlowNestingInv s s_k h_fni h_k))
  -- scanValue case
  all_goals (
    rename_i s_v h_v
    constructor
    · exact scanValue_preserves_FlowContextPSV s s_v h_fpsv h_v
    · exact scanValue_preserves_FlowNestingInv s s_v h_fni h_v)

/-! ### Scan chain threading -/

set_option maxHeartbeats 800000 in
/-- `scanNextToken` preserves `FlowContextPSV ∧ FlowNestingInv`.
    Proof follows B3.5's `scanNextToken_preserves_PlainScalarsValid`
    dispatch structure. For each branch:

    - Non-plain token branches: `FlowContextPSV_of_prefix_and_new` with trivial `h_new`
    - Plain scalar branch: use `scanPlainScalar_content_valid` (B3.4) + `FlowNestingInv`
    - `FlowNestingInv`: `preserves_flowLevel` for most branches,
      flow nesting increment/decrement for flow indicator branches -/
theorem scanNextToken_preserves_FlowInv
    (s s' : ScannerState)
    (h_fpsv : FlowContextPSV s.tokens)
    (h_fni : FlowNestingInv s)
    (h_ok : scanNextToken s = .ok (some s')) :
    FlowContextPSV s'.tokens ∧ FlowNestingInv s' := by
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> (try (simp at h_ok; done))
  split at h_ok <;> (try (simp at h_ok; done))
  rename_i s2 c h_pre
  have h_fpsv2 := preprocess_preserves_FlowContextPSV s s2 c h_fpsv h_pre
  have h_fni2 := preprocess_preserves_FlowNestingInv s s2 c h_fni h_pre
  have h_peek2 := preprocess_peek s s2 c h_pre
  split at h_ok <;> (try (simp at h_ok; done))
  split at h_ok
  · -- dispatchStructural
    simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact dispatchStructural_preserves_FlowInv s2 c h_fpsv2 h_fni2 _ (by assumption)
  · have h_fpsv3 := allowDir_ite_preserves_FlowContextPSV s2 h_fpsv2
    have h_fni3 := allowDir_ite_preserves_FlowNestingInv s2 h_fni2
    have h_peek3 : (if s2.allowDirectives then
        { s2 with allowDirectives := false, documentEverStarted := true }
      else s2).peek? = some c := by split <;> exact h_peek2
    split at h_ok <;> (try (simp at h_ok; done))
    split at h_ok
    · -- dispatchFlowIndicators
      simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact dispatchFlowIndicators_preserves_FlowInv _ c h_fpsv3 h_fni3 _ (by assumption)
    · split at h_ok <;> (try (simp at h_ok; done))
      split at h_ok
      · -- dispatchBlockIndicators
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchBlockIndicators_preserves_FlowInv _ c h_fpsv3 h_fni3 _ (by assumption)
      · -- dispatchContent
        split at h_ok <;> (try (simp at h_ok; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchContent_preserves_FlowInv _ c h_peek3 h_fpsv3 h_fni3 _ (by assumption)

theorem finalEmit_preserves_FlowContextPSV (s : ScannerState)
    (h : FlowContextPSV s.tokens) :
    FlowContextPSV ((unwindIndents s (-1)).emit .streamEnd).tokens := by
  apply FlowContextPSV_of_prefix_and_new s.tokens _ h
    (by have h_uw := unwindIndents_adds_tokens s (-1); rw [emit_tokens_size]; omega)
  · intro i hi
    rw [emit_preserves_tokens_at _ .streamEnd i (by
      have h_uw := unwindIndents_adds_tokens s (-1); omega)]
    exact unwindIndents_preserves_prefix s (-1) i hi
  · intro j hj hge h_flow
    by_cases h_lt : j < (unwindIndents s (-1)).tokens.size
    · -- Token from unwindIndents: .blockEnd, not .scalar _ .plain
      rw [emit_preserves_tokens_at _ .streamEnd j h_lt]
      have h_not_plain := unwindIndents_new_tokens_not_plain s (-1) j h_lt hge
      generalize h_tok : ((unwindIndents s (-1)).tokens[j]'h_lt).val = tok
      rw [h_tok] at h_not_plain
      cases tok with
      | scalar content style =>
        cases style with
        | plain => exact absurd h_not_plain (by simp)
        | _ => trivial
      | _ => trivial
    · -- Token is .streamEnd
      have h_j : j = (unwindIndents s (-1)).tokens.size := by
        rw [emit_tokens_size] at hj; omega
      subst h_j; unfold ScannerState.emit; simp only [Array.getElem_push_eq]

theorem scanLoop_preserves_FlowInv
    (s : ScannerState) (fuel : Nat)
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowContextPSV s.tokens)
    (h_fni : FlowNestingInv s)
    (h_ok : scanLoop s fuel = .ok tokens) :
    FlowContextPSV tokens := by
  induction fuel generalizing s with
  | zero => simp [scanLoop] at h_ok
  | succ fuel' ih =>
    simp only [scanLoop] at h_ok
    split at h_ok
    · simp at h_ok
    · split at h_ok <;> try (simp at h_ok; done)
      split at h_ok <;> try (simp at h_ok; done)
      injection h_ok with h_eq; rw [← h_eq]
      exact finalEmit_preserves_FlowContextPSV s h_fpsv
    · rename_i s' h_snt
      have ⟨h1, h2⟩ := scanNextToken_preserves_FlowInv s s' h_fpsv h_fni h_snt
      exact ih s' h1 h2 h_ok

theorem flowNesting_go_streamStart (p : YamlPos) :
    flowNesting.go #[⟨p, .streamStart⟩] 0 1 0 = 0 := by
  unfold flowNesting.go
  split
  · rfl
  · split
    · simp only [eq_false (by omega : ¬((0 : Nat) < 0))]
      unfold flowNesting.go
      split
      · rfl
      · omega
    · rfl

/-- `scan` output satisfies `FlowContextPSV`. -/
theorem scan_all_flow_context_psv (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    FlowContextPSV tokens := by
  unfold scan at h; simp only [] at h
  exact scanLoop_preserves_FlowInv _ _ _
    (by -- FlowContextPSV for initial state (1 token: .streamStart, not plain)
        have h_tok_eq : (match (ScannerState.mk' input |>.emit .streamStart).peek? with
            | some '\uFEFF' => (ScannerState.mk' input |>.emit .streamStart).advance
            | _ => ScannerState.mk' input |>.emit .streamStart).tokens =
            (ScannerState.mk' input |>.emit .streamStart).tokens := by
          split
          · exact advance_preserves_tokens _
          · rfl
        suffices h_suf : FlowContextPSV (ScannerState.mk' input |>.emit .streamStart).tokens by
          exact Eq.mpr (congrArg FlowContextPSV h_tok_eq) h_suf
        intro i hi h_flow
        have h_size : (ScannerState.mk' input |>.emit .streamStart).tokens.size = 1 := by
          rw [emit_tokens_size]; simp [ScannerState.mk']
        have h_i0 : i = 0 := by omega
        subst h_i0
        simp [ScannerState.emit, ScannerState.mk'])
    (by -- FlowNestingInv for initial state (flowLevel = 0, single non-flow token)
        unfold FlowNestingInv
        split <;> (
          try simp only [advance_preserves_tokens, advance_preserves_flowLevel]
          simp only [ScannerState.emit, ScannerState.mk', ScannerState.currentPos]
          unfold flowNesting
          exact flowNesting_go_streamStart _))
    h

/-! ### Filter preservation -/

/-- A placeholder token at position k doesn't change the flow depth. -/
theorem flowNesting_go_placeholder_neutral
    (tokens : Array (Positioned YamlToken))
    (k target depth : Nat) (hk : k < tokens.size) (h_tgt : k < target)
    (h_placeholder : (tokens[k]).val = .placeholder) :
    flowNesting.go tokens k target depth =
    flowNesting.go tokens (k + 1) target depth := by
  rw [flowNesting_go_step _ _ _ _ hk h_tgt]
  simp [h_placeholder]

/-- `flowNesting.go` returns `depth` when `pos ≥ target`. -/
theorem flowNesting_go_ge_target (tokens : Array (Positioned YamlToken))
    (pos target depth : Nat) (h : pos ≥ target) :
    flowNesting.go tokens pos target depth = depth := by
  unfold flowNesting.go; simp [h]

/-- Core List-level reverse direction: for every position `i` in a filtered list,
    there exists a canonical position `j` in the original list such that the
    filtered element equals the original, it satisfies the predicate, and `i`
    equals the count of satisfying elements before `j`. -/
theorem list_filter_origIdx
    {α : Type _} (l : List α) (p : α → Bool) (i : Nat)
    (hi : i < (l.filter p).length) :
    ∃ j, ∃ hj : j < l.length,
      (l.filter p)[i] = l[j] ∧
      p l[j] = true ∧
      i = ((l.take j).filter p).length := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    by_cases hpx : p x = true
    · simp only [List.filter_cons_of_pos hpx] at hi
      cases i with
      | zero =>
        exact ⟨0, by simp,
          by simp [List.filter_cons_of_pos hpx],
          by simpa using hpx,
          by simp⟩
      | succ i' =>
        simp only [List.length_cons] at hi
        have hi' : i' < (xs.filter p).length := by omega
        obtain ⟨j', hj', val_eq, p_eq, count_eq⟩ := ih i' hi'
        refine ⟨j' + 1, by simp; omega, ?_, ?_, ?_⟩
        · simp only [List.filter_cons_of_pos hpx, List.getElem_cons_succ]; exact val_eq
        · simp only [List.getElem_cons_succ]; exact p_eq
        · simp only [List.take_succ_cons, List.filter_cons_of_pos hpx, List.length_cons]; omega
    · simp only [List.filter_cons_of_neg hpx] at hi
      obtain ⟨j', hj', val_eq, p_eq, count_eq⟩ := ih i hi
      refine ⟨j' + 1, by simp; omega, ?_, ?_, ?_⟩
      · simp only [List.filter_cons_of_neg hpx, List.getElem_cons_succ]; exact val_eq
      · simp only [List.getElem_cons_succ]; exact p_eq
      · simp only [List.take_succ_cons, List.filter_cons_of_neg hpx]; exact count_eq

/-- Core List-level forward direction: position `j` in a list with `p l[j] = true`
    maps to position `i = (l.take j |>.filter p).length` in the filtered list. -/
theorem list_filter_getElem_by_count
    {α : Type _} (l : List α) (p : α → Bool) (j : Nat) (hj : j < l.length)
    (h_sat : p l[j] = true) :
    ((l.take j).filter p).length < (l.filter p).length ∧
    ∀ (h : ((l.take j).filter p).length < (l.filter p).length),
      (l.filter p)[((l.take j).filter p).length] = l[j] := by
  induction l generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.take, List.filter, List.getElem_cons_zero] at *
      exact ⟨by simp [h_sat], fun _ => by simp [h_sat]⟩
    | succ j' =>
      have hj' : j' < xs.length := by simp at hj; omega
      simp only [List.getElem_cons_succ] at h_sat
      have ih_result := ih j' hj' h_sat
      simp only [List.take_succ_cons]
      by_cases hpx : p x = true
      · simp only [List.filter_cons_of_pos hpx, List.length_cons, List.getElem_cons_succ]
        exact ⟨by omega, fun _ => ih_result.2 ih_result.1⟩
      · simp only [List.filter_cons_of_neg hpx]
        exact ih_result

/-- Array wrapper: the i-th element of a filtered array corresponds to the j-th element
    of the original array, where i counts elements satisfying the predicate before j. -/
theorem array_filter_getElem_correspondence
    {α : Type _} (arr : Array α) (p : α → Bool) (j : Nat) (hj : j < arr.size)
    (h_sat : p arr[j] = true) :
    let filtered := arr.filter p
    let i := (arr.toList.take j).filter p |>.length
    ∃ (h : i < filtered.size), filtered[i] = arr[j] := by
  intro filtered i
  have hj_list : j < arr.toList.length := by simpa using hj
  have h_sat_list : p arr.toList[j] = true := by simpa [Array.getElem_toList] using h_sat
  have h_list := list_filter_getElem_by_count arr.toList p j hj_list h_sat_list
  have h_bound : i < filtered.size := by
    show ((arr.toList.take j).filter p).length < (arr.filter p).size
    rw [show (arr.filter p).size = (arr.filter p).toList.length from rfl,
        Array.toList_filter]
    exact h_list.1
  refine ⟨h_bound, ?_⟩
  have h_val := h_list.2 h_list.1
  -- Goal: filtered[i] = arr[j]
  show (arr.filter p).toList[i] = arr.toList[j]
  simp only [Array.toList_filter]
  exact h_val

/-- `flowNesting.go` on the original array equals `flowNesting.go` on the filtered
    array, where the target in the filtered array is the count of non-placeholder
    tokens before position `j`. -/
theorem flowNesting_go_filter_equiv
    (all_tokens : Array (Positioned YamlToken))
    (j : Nat) (hj : j ≤ all_tokens.size)
    (depth : Nat) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    let filtered := all_tokens.filter p
    let i := (all_tokens.toList.take j).filter p |>.length
    flowNesting.go all_tokens 0 j depth =
    flowNesting.go filtered 0 i depth := by
  intro p filtered
  show flowNesting.go all_tokens 0 j depth =
    flowNesting.go filtered 0 ((all_tokens.toList.take j).filter p |>.length) depth
  induction j generalizing depth with
  | zero =>
    simp only [List.take_zero, List.filter_nil, List.length_nil]
    rw [flowNesting_go_ge_target _ _ _ _ (by omega : 0 ≥ 0),
        flowNesting_go_ge_target _ _ _ _ (by omega : 0 ≥ 0)]
  | succ j' ih =>
    -- Split LHS at position j'
    rw [flowNesting_go_split all_tokens 0 j' (j' + 1) depth (by omega) (by omega)]
    -- Apply IH to rewrite inner go
    rw [ih (by omega : j' ≤ all_tokens.size)]
    -- Goal: go all_tokens j' (j'+1) (go filtered 0 len_j' depth) = go filtered 0 len_succ depth
    by_cases hj'_bound : j' < all_tokens.size
    · -- j' in bounds
      have hj'_list : j' < all_tokens.toList.length := by simpa using hj'_bound
      have h_take_split : all_tokens.toList.take (j' + 1) =
          all_tokens.toList.take j' ++ [all_tokens.toList[j']] :=
        List.take_succ_eq_append_getElem hj'_list
      by_cases h_ph : (all_tokens[j']).val = .placeholder
      · -- Placeholder: flowNesting step is neutral, filter count doesn't increase
        rw [flowNesting_go_step all_tokens j' (j' + 1) _ hj'_bound (by omega)]
        simp [h_ph]
        rw [flowNesting_go_ge_target all_tokens (j' + 1) (j' + 1) _ (by omega)]
        -- Show filter counts are equal (placeholder doesn't pass filter)
        congr 1
        show (List.filter p (List.take j' all_tokens.toList)).length =
             (List.filter p (List.take (j' + 1) all_tokens.toList)).length
        symm
        rw [h_take_split, List.filter_append, List.length_append]
        simp only [List.filter]
        have : p all_tokens.toList[j'] = false := by
          simp only [p, bne]
          rw [Array.getElem_toList hj'_bound, h_ph]
          decide
        rw [this]; simp
      · -- Not placeholder: process token, filter count increases by 1
        have h_p_true : p all_tokens[j'] = true := by
          simp only [p, bne, Bool.not_eq_true']
          exact decide_eq_false h_ph
        have h_p_list : p all_tokens.toList[j'] = true := by
          rwa [Array.getElem_toList hj'_bound]
        have h_len_succ : (List.filter p (List.take (j' + 1) all_tokens.toList)).length =
            (List.filter p (List.take j' all_tokens.toList)).length + 1 := by
          rw [h_take_split, List.filter_append, List.length_append]
          simp only [List.filter, h_p_list, List.length_cons, List.length_nil]
        obtain ⟨h_i_bound, h_filt_eq⟩ :=
          array_filter_getElem_correspondence all_tokens p j' hj'_bound h_p_true
        -- Split RHS at len_j'
        rw [h_len_succ]
        rw [flowNesting_go_split filtered 0
          ((List.filter p (List.take j' all_tokens.toList)).length)
          ((List.filter p (List.take j' all_tokens.toList)).length + 1)
          _ (by omega) (by omega)]
        -- Apply one-step unfolding on both sides
        rw [flowNesting_go_step all_tokens j' (j' + 1) _ hj'_bound (by omega)]
        rw [flowNesting_go_step filtered
          ((List.filter p (List.take j' all_tokens.toList)).length)
          ((List.filter p (List.take j' all_tokens.toList)).length + 1)
          _ h_i_bound (by omega)]
        -- Reduce trailing go to identity
        simp only [flowNesting_go_ge_target _ _ _ _ (by omega : j' + 1 ≥ j' + 1),
                    flowNesting_go_ge_target _ _ _ _
                      (by omega : (List.filter p (List.take j' all_tokens.toList)).length + 1 ≥
                        (List.filter p (List.take j' all_tokens.toList)).length + 1)]
        -- Now both sides are match on token value applied to the same inner depth
        have h_val_eq : (filtered[(List.filter p (List.take j' all_tokens.toList)).length]'h_i_bound).val =
               (all_tokens[j']'hj'_bound).val := by
          rw [h_filt_eq]
        rw [h_val_eq]
    · -- j' out of bounds
      rw [flowNesting_go_oob all_tokens j' (j' + 1) _ (by omega)]
      congr 1
      show (List.filter p (List.take j' all_tokens.toList)).length =
           (List.filter p (List.take (j' + 1) all_tokens.toList)).length
      symm; congr 1
      have : all_tokens.toList.length ≤ j' := by simpa using hj'_bound
      rw [List.take_of_length_le this, List.take_of_length_le (by omega)]

/-- Filtering out `.placeholder` tokens preserves `FlowContextPSV`.
    `.placeholder` tokens are neither flow start/end nor plain scalars,
    so removing them preserves flow nesting at all retained positions. -/
theorem filter_preserves_FlowContextPSV
    (all_tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowContextPSV all_tokens) :
    FlowContextPSV (all_tokens.filter fun t => t.val != YamlToken.placeholder) := by
  unfold FlowContextPSV
  intro i hi h_flow
  let p := fun (t : Positioned YamlToken) => t.val != YamlToken.placeholder
  let filtered := all_tokens.filter p
  -- Find canonical original position using list_filter_origIdx
  have hi_list : i < (all_tokens.toList.filter p).length := by
    rwa [← Array.toList_filter, show (all_tokens.filter p).toList.length =
      (all_tokens.filter p).size from rfl]
  obtain ⟨j, hj_lt, val_eq, p_j, count_eq⟩ :=
    list_filter_origIdx all_tokens.toList p i hi_list
  have hj_arr : j < all_tokens.size := by simpa using hj_lt
  -- Lift value equality to array level
  have val_eq_arr : filtered[i] = all_tokens[j] := by
    have hi_list2 : i < (all_tokens.filter p).toList.length := by
      rwa [show (all_tokens.filter p).toList.length = (all_tokens.filter p).size from rfl]
    have hj_list2 : j < all_tokens.toList.length := by simpa using hj_arr
    show (all_tokens.filter p).toList[i]'hi_list2 = all_tokens.toList[j]'hj_list2
    simp only [Array.toList_filter]; exact val_eq
  -- Flow nesting correspondence via flowNesting_go_filter_equiv
  have h_nest_eq : flowNesting filtered i = flowNesting all_tokens j := by
    unfold flowNesting
    rw [count_eq]
    exact (flowNesting_go_filter_equiv all_tokens j (by omega) 0).symm
  -- Apply h_fpsv
  rw [h_nest_eq] at h_flow
  have h_j := h_fpsv j hj_arr h_flow
  exact val_eq_arr ▸ h_j

/-! ### Main theorems -/

/-- **B3.5+**: Flow-context plain scalar tokens satisfy `ScalarScannable _ true`. -/
theorem scan_flow_context_psv (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    FlowContextPSV tokens := by
  unfold Scanner.scanFiltered at h
  split at h
  · rename_i all_tokens h_scan
    injection h with h_eq; subst h_eq
    exact filter_preserves_FlowContextPSV all_tokens
      (scan_all_flow_context_psv input all_tokens h_scan)
  · simp at h

/-- **B3.5+ main**: Scanner output satisfies `FlowAwarePSV`.
    Combines B3.5's `PlainScalarsValid` with `FlowContextPSV`. -/
theorem scan_flow_aware_psv (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    FlowAwarePSV tokens :=
  ⟨fun i hi => scan_plain_scalar_valid input tokens h i hi,
   scan_flow_context_psv input tokens h⟩

end Lean4Yaml.Proofs.ScannerPlainScalarValid
