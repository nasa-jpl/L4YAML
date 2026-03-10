/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Grammar
import Lean4Yaml.Proofs.ScannerPlainContent
import Lean4Yaml.Proofs.ScannerCorrectness
import Lean4Yaml.Proofs.StringProperties

/-!
# Plain Scalar Content Validity (B3.4)

Per-function theorem: `scanPlainScalar` emits a token whose content
satisfies `ScalarScannable`.

## Proof structure

1. Unfold `scanPlainScalar` to expose the `collectPlainScalarLoop` call.
2. Apply `collectPlainScalarLoop_preserves_contentInv` (B3.3) with the
   empty base case to obtain `PlainContentInv` for the raw content.
3. Apply `trim_preserves_*` lemmas from `StringProperties` to transfer
   `noColonSpaceProp`, `noSpaceHashProp`, `noFlowIndicatorsProp` through
   `trimTrailingWS`.
4. For `validPlainFirstProp`: see `validPlainFirst_sorry` note below.
5. Package as `ScalarScannable`.

## Known gap: `validPlainFirstProp` for single-exception-char content

When the scanner's first character is an exception char (`-`, `?`, `:`)
and the second input character triggers immediate termination in
`collectPlainScalar_terminates?` (e.g., input `?:` at EOF), the loop
produces single-character content like `"?"`. Then
`validPlainFirstProp "?" inFlow = canStartPlainScalarProp '?' none inFlow = False`,
making `ScalarScannable` unprovable for this edge case.

This is a semantic gap between the scanner (which checks
`canStartPlainScalarBool` against the INPUT lookahead) and the grammar
(which checks `validPlainFirstProp` against the CONTENT lookahead).
The YAML spec's [123] ns-plain-first requires exception chars to be
followed by ns-plain-safe IN THE CONTENT, not in the input stream.

Resolution options (future work):
- Strengthen the scanner to avoid producing single-exception-char content
- Track `validPlainFirstProp` through the loop invariant with case analysis
- Accept the gap as a known limitation for rare edge cases
-/

namespace Lean4Yaml.Proofs.ScannerPlainScalar

open Lean4Yaml
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates
open Lean4Yaml.Grammar
open Lean4Yaml.Proofs.ScannerPlainContent
open Lean4Yaml.Proofs.ScannerCorrectness
open Lean4Yaml.Proofs.ScannerCorrectness.ScanHelpers
open Lean4Yaml.Proofs.StringProperties

/-! ## Helper: trimTrailingWS rewriting -/

/-- `trimTrailingWS` is `String.ofList (s.toList.reverse.dropWhile p).reverse`
    where `p = fun c => c == ' ' || c == '\t'`. -/
theorem trimTrailingWS_eq (s : String) :
    trimTrailingWS s = String.ofList
      (s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse := by
  unfold trimTrailingWS; rfl

/-! ## Content properties after trimming -/

private def wsTab : Char → Bool := fun c => c == ' ' || c == '\t'

theorem trimTrailingWS_noColonSpace (content : String)
    (h : noColonSpaceProp content) :
    noColonSpaceProp (trimTrailingWS content) := by
  rw [trimTrailingWS_eq]
  have h' : noColonSpaceProp (String.ofList content.toList) := by
    rw [String.ofList_toList]; exact h
  exact trim_preserves_noColonSpace wsTab content.toList h'

theorem trimTrailingWS_noSpaceHash (content : String)
    (h : noSpaceHashProp content) :
    noSpaceHashProp (trimTrailingWS content) := by
  rw [trimTrailingWS_eq]
  have h' : noSpaceHashProp (String.ofList content.toList) := by
    rw [String.ofList_toList]; exact h
  exact trim_preserves_noSpaceHash wsTab content.toList h'

theorem trimTrailingWS_noFlowIndicators (content : String)
    (h : noFlowIndicatorsProp content) :
    noFlowIndicatorsProp (trimTrailingWS content) := by
  rw [trimTrailingWS_eq]
  have h' : noFlowIndicatorsProp (String.ofList content.toList) := by
    rw [String.ofList_toList]; exact h
  exact trim_preserves_noFlowIndicators wsTab content.toList h'

/-! ## Main theorem (B3.4) -/

/-- `validPlainFirstProp` for the trimmed content.

    **Status: sorry** — See module docstring for the known gap with
    single-exception-char content. The three content-structure properties
    (`noColonSpace`, `noSpaceHash`, `noFlowIndicators`) are fully proven. -/
theorem validPlainFirst_sorry (content : String) (inFlow : Bool) :
    (trimTrailingWS content).length > 0 → validPlainFirstProp (trimTrailingWS content) inFlow := by
  sorry

/-- `scanPlainScalar` produces a token whose plain scalar content
    satisfies `ScalarScannable`.

    Combines B3.3 (`collectPlainScalarLoop_preserves_contentInv`) with
    trim-preservation lemmas to establish the content properties
    required by `ScalarScannable`.

    **Proof status**: 1 sorry (for `validPlainFirstProp`; see module docstring). -/
theorem scanPlainScalar_content_valid (s : ScannerState)
    (s' : ScannerState) (h : scanPlainScalar s = .ok s') :
    let idx := s.tokens.size
    ∀ (h_bound : idx < s'.tokens.size),
      match (s'.tokens[idx]'h_bound).val with
      | .scalar content .plain =>
          ScalarScannable ⟨content, .plain, none, none, none⟩ s.inFlow
      | _ => True := by
  intro idx h_bound
  -- Step 1: Unfold scanPlainScalar to expose collectPlainScalarLoop
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  -- Split on the result of collectPlainScalarLoop
  split at h
  · -- collectPlainScalarLoop returned .error — contradicts h
    contradiction
  · -- collectPlainScalarLoop returned .ok result
    rename_i result heq
    injection h with h_eq; subst h_eq; dsimp only []
    -- Step 2: Identify the emitted token
    -- The result state's tokens = s.tokens (loop preserves tokens)
    have h_tok : result.state.tokens = s.tokens :=
      collectPlainScalarLoop_preserves_tokens s "" "" _ _ _ _ _ heq
    -- After emitAt, the new token is at s.tokens.size
    unfold ScannerState.emitAt
    simp only [h_tok]
    -- The pushed token is at index s.tokens.size; match reduces to .scalar
    -- Step 3: Reduce Array.push indexing at s.tokens.size
    simp only [Array.getElem_push]
    have h_not_lt : ¬(idx < s.tokens.size) := Nat.lt_irrefl _
    simp only [h_not_lt, dite_false]
    -- Goal: ScalarScannable { content := trimTrailingWS result.content, style := .plain } s.inFlow
    -- Step 4: Unfold ScalarScannable, introduce premises
    intro _ hlen
    -- Step 5: Apply B3.3 with empty base case
    have inv := collectPlainScalarLoop_preserves_contentInv
      s "" "" _ s.inFlow _ s.inputEnd
      (PlainContentInv.empty s.inFlow s)
      (BoundaryHash.empty s.inFlow s)
      result heq
    -- Step 6: Package the four conjuncts
    exact ⟨validPlainFirst_sorry result.content s.inFlow hlen,
           trimTrailingWS_noColonSpace result.content inv.content_noColonSpace,
           trimTrailingWS_noSpaceHash result.content inv.content_noSpaceHash,
           fun hflow => trimTrailingWS_noFlowIndicators result.content (inv.content_noFlowIndicators hflow)⟩

end Lean4Yaml.Proofs.ScannerPlainScalar
