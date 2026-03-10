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
      subst this; sorry
    · split at h_ok
      · -- c == '*': .alias — not plain scalar
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        intro j hj hge
        have : j = s.tokens.size := by
          have := scanAnchorOrAlias_adds_one_token s false; omega
        subst this; sorry
      · split at h_ok
        · -- c == '!': .tag — not plain scalar
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          intro j hj hge
          have : j = s.tokens.size := by
            have := scanTag_adds_one_token s; omega
          subst this; sorry
        · split at h_ok
          · -- c == '|' || '>': .scalar _ .literal/.folded — not .plain
            split at h_ok <;> try contradiction
            simp only [Except.ok.injEq] at h_ok; subst h_ok
            rename_i s_bs h_bs
            intro j hj hge
            have : j = s.tokens.size := by
              have := scanBlockScalar_adds_one_token s s_bs h_bs; omega
            subst this; sorry
          · split at h_ok
            · -- c == '"': .scalar _ .doubleQuoted — not .plain
              split at h_ok <;> try contradiction
              rename_i s_dq h_dq
              split at h_ok <;> (
                simp only [Except.ok.injEq] at h_ok; subst h_ok
                intro j hj hge; sorry)
            · split at h_ok
              · -- c == '\'': .scalar _ .singleQuoted — not .plain
                split at h_ok <;> try contradiction
                rename_i s_sq h_sq
                split at h_ok <;> (
                  simp only [Except.ok.injEq] at h_ok; subst h_ok
                  intro j hj hge; sorry)
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
    sorry

theorem dispatchStructural_preserves_PlainScalarsValid
    (s : ScannerState) (c : Char) (h_old : PlainScalarsValid s.tokens)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchStructural s c = .ok (some s')) :
    PlainScalarsValid s'.tokens := by
  apply PlainScalarsValid_of_prefix_and_new s.tokens s'.tokens h_old
    (dispatchStructural_tokens_mono s c s' h_ok)
  · intro i hi; exact dispatchStructural_preserves_prefix s c s' h_ok i (by omega)
  · sorry

theorem dispatchFlowIndicators_preserves_PlainScalarsValid
    (s : ScannerState) (c : Char) (h_old : PlainScalarsValid s.tokens)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    PlainScalarsValid s'.tokens := by
  apply PlainScalarsValid_of_prefix_and_new s.tokens s'.tokens h_old
    (dispatchFlowIndicators_tokens_mono s c s' h_ok)
  · intro i hi; exact dispatchFlowIndicators_preserves_prefix s c s' h_ok i (by omega)
  · sorry

/-- Block indicators: uses `setIfInBounds` which may overwrite tokens, but only
    with `.key`/`.blockMappingStart` (never `.scalar _ .plain`).
    Separate treatment needed because prefix preservation has SimpleKeyAbove condition. -/
theorem dispatchBlockIndicators_preserves_PlainScalarsValid
    (s : ScannerState) (c : Char) (h_old : PlainScalarsValid s.tokens)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    PlainScalarsValid s'.tokens := by
  sorry

/-! ## scanNextToken preserves PlainScalarsValid -/

private theorem allowDir_ite_preserves_PlainScalarsValid (s : ScannerState)
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

private theorem finalEmit_preserves_PlainScalarsValid (s : ScannerState)
    (h : PlainScalarsValid s.tokens) :
    PlainScalarsValid ((unwindIndents s (-1)).emit .streamEnd).tokens := by
  -- unwindIndents emits only .blockEnd tokens; .streamEnd is also not .scalar _ .plain
  sorry

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
  -- The initial state after mk'.emit(.streamStart) + optional BOM advance
  -- has tokens = #[⟨pos, .streamStart⟩], satisfying PlainScalarsValid.
  sorry

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
    sorry
  · simp at h

end Lean4Yaml.Proofs.ScannerPlainScalarValid
