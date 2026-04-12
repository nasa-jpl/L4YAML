/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Grammar
import L4YAML.Proofs.ScannerPlainContent
import L4YAML.Proofs.ScannerCorrectness
import L4YAML.Proofs.StringProperties
import L4YAML.Proofs.CharClass

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
4. For `validPlainFirstProp`: proved using scanner pre-condition
   `canStartPlainScalarBool` plus the grammar definition that accepts
   single exception chars (`-`, `?`, `:`) unconditionally.
5. Package as `ScalarScannable`.

## Resolution of the validPlainFirstProp gap

The YAML 1.2.2 §7.3.3 [123] `ns-plain-first` exception chars (`-`, `?`, `:`)
require a following `ns-plain-safe` character. The scanner checks this against
the INPUT lookahead (`canStartPlainScalarBool`), while the grammar checks
against CONTENT lookahead (`validPlainFirstProp`). When the second input char
triggers termination (e.g., input `?:` followed by blank), content may be a
single exception char.

This is resolved by modifying `validPlainFirstProp` to accept single exception
chars unconditionally, since the scanner already validated the input context.
For non-exception chars, the scanner's `canStartPlainScalarBool` check provides
the necessary `¬isIndicator ∧ ¬isWhitespace ∧ ¬isLineBreak` properties.
-/

namespace L4YAML.Proofs.ScannerPlainScalar

open L4YAML
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Grammar
open L4YAML.Proofs.ScannerPlainContent
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.ScannerCorrectness.ScanHelpers
open L4YAML.Proofs.StringProperties
open L4YAML.Proofs.CharClass

/-! ## Helper: trimTrailingWS rewriting -/

/-- `trimTrailingWS` is `String.ofList (s.toList.reverse.dropWhile p).reverse`
    where `p = fun c => c == ' ' || c == '\t'`. -/
theorem trimTrailingWS_eq (s : String) :
    trimTrailingWS s = String.ofList
      (s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse := by
  unfold trimTrailingWS; rfl

/-! ## Content properties after trimming -/

def wsTab : Char → Bool := fun c => c == ' ' || c == '\t'

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

/-! ### Loop prefix preservation -/

/-- Content produced by `collectPlainScalarLoop` always has the input content
    as a prefix: the loop only appends to the end of content. -/
theorem collectPlainScalarLoop_content_isPrefix
    (s : ScannerState) (content spaces : String) (fuel : Nat)
    (inFlow : Bool) (contentIndent inputEnd : Nat) (result : PlainScalarResult)
    (h : collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd = .ok result) :
    content.toList <+: result.content.toList := by
  induction fuel generalizing s content spaces with
  | zero => unfold collectPlainScalarLoop at h; injection h with h_eq; cases h_eq; exact List.prefix_rfl
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at h; split at h
    · injection h with h_eq; cases h_eq; exact List.prefix_rfl
    · rename_i c hpeek; split at h
      · rename_i hterm; injection h with h_eq; cases h_eq
        exact (terminates_preserves_all _ _ _ _ _ _ hterm).1 ▸ List.prefix_rfl
      · rename_i hterm; split at h
        · split at h
          · simp only [bind, Except.bind] at h; split at h <;> try contradiction
            rename_i fold_result heq; cases fold_result with
            | mk folded s_fold =>
              split at h
              · injection h with h_eq; cases h_eq; exact List.prefix_rfl
              · generalize h_loop : collectPlainScalarLoop s_fold (content ++ folded) "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; exact List.prefix_rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    exact List.IsPrefix.trans ⟨folded.toList, String.toList_append.symm⟩
                      (ih s_fold (content ++ folded) "" h_loop)
                | error e => simp at h
          · split at h
            · injection h with h_eq; cases h_eq; exact List.prefix_rfl
            · rename_i content' s' hblk; split at h
              · injection h with h_eq; cases h_eq; exact List.prefix_rfl
              · generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; exact List.prefix_rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    have hform := handleBlockLineBreak_content_form s content contentIndent inputEnd content' s' hblk
                    rcases hform with rfl | ⟨n, _, rfl⟩
                    all_goals exact List.IsPrefix.trans ⟨_, String.toList_append.symm⟩ (ih _ _ "" h_loop)
                | error e => simp at h
        · split at h
          · exact ih s.advance content (spaces.push c) h
          · split at h
            · injection h with h_eq; cases h_eq; exact List.prefix_rfl
            · exact List.IsPrefix.trans
                ⟨(spaces ++ String.singleton c).toList, by
                  rw [String.toList_append, String.toList_append, String.toList_singleton]
                  rw [String.toList_append]
                  rw [← List.append_assoc]⟩
                (ih s.advance (content ++ spaces ++ String.singleton c) "" h)

/-! ### canStartPlainScalar helpers -/

open L4YAML.Proofs.ScannerProofs in
/-- `canStartPlainScalarBool c _ inFlow = true` implies `isPlainSafeBool c inFlow = true`. -/
theorem canStart_isPlainSafe (c : Char) (next : Option Char) (inFlow : Bool)
    (h : canStartPlainScalarBool c next inFlow = true) :
    isPlainSafeBool c inFlow = true := by
  rw [isPlainSafe_iff]
  have hprop := (canStartPlainScalar_iff c next inFlow).mp h
  unfold canStartPlainScalarProp at hprop; unfold isPlainSafeProp
  split at hprop
  · rename_i hexc; rcases hexc with rfl | rfl | rfl
    all_goals (split <;> simp_all [isWhiteSpaceProp, isLineBreakProp, isFlowIndicatorProp])
  · obtain ⟨h_ni, h_nws, h_nlb⟩ := hprop; split
    · exact ⟨h_nws, h_nlb, fun hfi =>
        h_ni ((isIndicator_iff c).mp (isFlowIndicator_implies_isIndicator c
          ((isFlowIndicator_iff c).mpr hfi)))⟩
    · exact ⟨h_nws, h_nlb⟩

/-- `canStartPlainScalarBool c _ inFlow = true` implies `c` is not whitespace. -/
theorem canStart_not_whitespace (c : Char) (next : Option Char) (inFlow : Bool)
    (h : canStartPlainScalarBool c next inFlow = true) :
    isWhiteSpaceBool c = false := by
  unfold canStartPlainScalarBool at h
  split at h
  · rename_i hexc; rcases hexc with rfl | rfl | rfl <;> native_decide
  · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨_, h2⟩, _⟩ := h; exact h2

/-- `canStartPlainScalarBool c _ inFlow = true` implies `c` is not a linebreak. -/
theorem canStart_not_linebreak (c : Char) (next : Option Char) (inFlow : Bool)
    (h : canStartPlainScalarBool c next inFlow = true) :
    isLineBreakBool c = false := by
  unfold canStartPlainScalarBool at h
  split at h
  · rename_i hexc; rcases hexc with rfl | rfl | rfl <;> native_decide
  · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨_, _⟩, h3⟩ := h; exact h3

/-- For non-exception chars, `canStartPlainScalarProp` does not depend on `next`. -/
theorem canStart_nonException_next_irrel (c : Char) (n1 n2 : Option Char) (inFlow : Bool)
    (h : ¬(c = '-' ∨ c = '?' ∨ c = ':')) :
    canStartPlainScalarProp c n1 inFlow = canStartPlainScalarProp c n2 inFlow := by
  unfold canStartPlainScalarProp; simp [h]

/-- For non-exception first char, `canStartPlainScalarBool` implies `validPlainFirstProp`
    regardless of what follows in the content. -/
theorem validPlainFirst_of_nonException
    (c0 : Char) (content : List Char) (inFlow : Bool)
    (h_nexc : ¬(c0 = '-' ∨ c0 = '?' ∨ c0 = ':'))
    (h_cs : canStartPlainScalarProp c0 none inFlow) :
    validPlainFirstProp (String.ofList (c0 :: content)) inFlow := by
  simp only [validPlainFirstProp, String.toList_ofList]
  cases content with
  | nil => simp [h_nexc]; exact h_cs
  | cons n rest =>
    simp; rwa [← canStart_nonException_next_irrel c0 none (some n) inFlow h_nexc]

/-- `canStartPlainScalarBool` for non-exception chars implies `canStartPlainScalarProp _ none`. -/
theorem canStart_nonException_to_prop (c : Char) (next : Option Char) (inFlow : Bool)
    (h_nexc : ¬(c = '-' ∨ c = '?' ∨ c = ':'))
    (h : canStartPlainScalarBool c next inFlow = true) :
    canStartPlainScalarProp c none inFlow := by
  have := (canStartPlainScalar_iff c next inFlow).mp h
  rwa [← canStart_nonException_next_irrel c next none inFlow h_nexc]

/-- `canStartPlainScalarBool` for exception chars requires `peekAt? 1 = some n`
    with `n` that is plain-safe, not whitespace, and not a linebreak. -/
theorem canStart_exception_next (c : Char) (next : Option Char) (inFlow : Bool)
    (h_exc : c = '-' ∨ c = '?' ∨ c = ':')
    (h : canStartPlainScalarBool c next inFlow = true) :
    ∃ n, next = some n ∧ isPlainSafeBool n inFlow = true
      ∧ isWhiteSpaceBool n = false ∧ isLineBreakBool n = false := by
  unfold canStartPlainScalarBool at h; simp only [h_exc, ↓reduceIte] at h
  match next with
  | none => simp at h
  | some n =>
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨h_nws, h_nlb⟩, h_nfi⟩ := h
    refine ⟨n, rfl, ?_, h_nws, h_nlb⟩
    unfold isPlainSafeBool; split
    · rename_i hflow; rw [hflow] at h_nfi
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact ⟨⟨h_nws, h_nlb⟩, h_nfi⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact ⟨h_nws, h_nlb⟩

/-- For exception chars, `validPlainFirstProp` for singletons is trivially `True`. -/
theorem validPlainFirst_singleton_exception
    (c0 : Char) (inFlow : Bool) (h_exc : c0 = '-' ∨ c0 = '?' ∨ c0 = ':') :
    validPlainFirstProp (String.singleton c0) inFlow := by
  simp only [validPlainFirstProp, String.toList_singleton, h_exc, ↓reduceIte]

/-! ### Core lemma: canStartPlainScalar → validPlainFirstProp for loop output -/

/-- The loop starting from empty content, where the first char satisfies
    `canStartPlainScalarBool`, produces content satisfying `validPlainFirstProp`
    and starting with the first input char. -/
theorem collectPlainScalarLoop_validFirst_and_head
    (s : ScannerState) (fuel : Nat)
    (inFlow : Bool) (contentIndent inputEnd : Nat) (result : PlainScalarResult)
    (c0 : Char) (hpeek : s.peek? = some c0)
    (hcs : canStartPlainScalarBool c0 (s.peekAt? 1) inFlow = true)
    (h : collectPlainScalarLoop s "" "" fuel inFlow contentIndent inputEnd = .ok result)
    (hne : result.content ≠ "") :
    validPlainFirstProp result.content inFlow ∧ result.content.toList.head? = some c0 := by
  have h_nws := canStart_not_whitespace c0 (s.peekAt? 1) inFlow hcs
  have h_nlb := canStart_not_linebreak c0 (s.peekAt? 1) inFlow hcs
  have h_ps := canStart_isPlainSafe c0 (s.peekAt? 1) inFlow hcs
  match fuel, h with
  | 0, h =>
    unfold collectPlainScalarLoop at h; injection h with h; rw [← h] at hne; exact absurd rfl hne
  | fuel' + 1, h =>
    unfold collectPlainScalarLoop at h; rw [hpeek] at h
    split at h
    · contradiction
    · rename_i c heq; injection heq with heq; subst heq
      split at h
      · rename_i r ht
        injection h with h_eq
        have := (terminates_preserves_all _ _ _ _ _ _ ht).1
        rw [← h_eq, ← this] at hne; exact absurd rfl hne
      · rw [show isLineBreakBool c0 = false from h_nlb] at h
        simp at h
        rw [show isWhiteSpaceBool c0 = false from h_nws] at h
        simp at h
        split at h
        · rename_i hbad; rw [h_ps] at hbad; contradiction
        · change collectPlainScalarLoop s.advance (String.singleton c0) "" fuel' inFlow contentIndent inputEnd = Except.ok result at h
          have hpfx := collectPlainScalarLoop_content_isPrefix
            s.advance (String.singleton c0) "" fuel' inFlow contentIndent inputEnd result h
          obtain ⟨sfx, hsfx⟩ := hpfx
          simp [String.toList_singleton] at hsfx
          have h_head : result.content.toList.head? = some c0 := by rw [← hsfx]; simp
          refine ⟨?_, h_head⟩
          by_cases hexc : c0 = '-' ∨ c0 = '?' ∨ c0 = ':'
          · /- EXCEPTION c0 -/
            obtain ⟨n, hnext, hps_n, h_nws_n, h_nlb_n⟩ :=
              canStart_exception_next c0 (s.peekAt? 1) inFlow hexc hcs
            cases sfx with
            | nil =>
              have : result.content = String.singleton c0 := by
                rw [← String.toList_inj, String.toList_singleton, ← hsfx]
              rw [this]; exact validPlainFirst_singleton_exception c0 inFlow hexc
            | cons c1 rest =>
              match fuel', h with
              | 0, h =>
                unfold collectPlainScalarLoop at h; injection h with h_eq
                have : result.content.toList = [c0] := by
                  simp [← h_eq, String.toList_singleton]
                rw [this] at hsfx; simp at hsfx
              | fuel'' + 1, h =>
                unfold collectPlainScalarLoop at h
                have h_adv_peek := advance_peek_eq_peekAt_one s c0 hpeek
                rw [hnext] at h_adv_peek; rw [h_adv_peek] at h
                split at h
                · contradiction
                · rename_i c heq; injection heq with heq; subst heq
                  split at h
                  · rename_i r ht
                    injection h with h_eq
                    have hpres := (terminates_preserves_all _ _ _ _ _ _ ht).1
                    have : result.content.toList = [c0] := by
                      rw [← h_eq, hpres]; simp [String.toList_singleton]
                    rw [this] at hsfx; simp at hsfx
                  · rw [show isLineBreakBool n = false from h_nlb_n] at h
                    simp at h
                    rw [show isWhiteSpaceBool n = false from h_nws_n] at h
                    simp at h
                    split at h
                    · rename_i hbad2; rw [hps_n] at hbad2; contradiction
                    · have : (String.singleton c0).push n =
                          String.singleton c0 ++ String.singleton n := by rfl
                      rw [this] at h
                      have hpfx2 := collectPlainScalarLoop_content_isPrefix
                        s.advance.advance (String.singleton c0 ++ String.singleton n)
                        "" fuel'' inFlow contentIndent inputEnd result h
                      have h_tl : (String.singleton c0 ++ String.singleton n).toList = [c0, n] := by
                        simp [String.toList_singleton]
                      obtain ⟨sfx2, hsfx2⟩ := hpfx2
                      rw [h_tl] at hsfx2
                      rw [← hsfx] at hsfx2; simp at hsfx2
                      obtain ⟨hc1_eq, _⟩ := hsfx2
                      subst hc1_eq
                      have : result.content = String.ofList (c0 :: n :: rest) := by
                        rw [← String.toList_inj, String.toList_ofList, hsfx]
                      rw [this]
                      simp only [validPlainFirstProp, String.toList_ofList]
                      rw [hnext] at hcs
                      exact (canStartPlainScalar_iff c0 (some n) inFlow).mp hcs
          · /- NON-EXCEPTION c0 -/
            have h_nexc : ¬(c0 = '-' ∨ c0 = '?' ∨ c0 = ':') := hexc
            have h_csp := canStart_nonException_to_prop c0 (s.peekAt? 1) inFlow h_nexc hcs
            have : result.content = String.ofList (c0 :: sfx) := by
              rw [← String.toList_inj, String.toList_ofList, hsfx]
            rw [this]
            exact validPlainFirst_of_nonException c0 sfx inFlow h_nexc h_csp

/-! ### Transfer through trimTrailingWS -/

/-- `trimTrailingWS` preserves `List.head?` when the result is nonempty. -/
theorem trimTrailingWS_preserves_head (content : String) (c : Char)
    (hne : (trimTrailingWS content).toList ≠ [])
    (hhead : content.toList.head? = some c) :
    (trimTrailingWS content).toList.head? = some c := by
  unfold trimTrailingWS at hne ⊢
  simp only [String.toList_ofList] at hne ⊢
  change (content.toList.reverse.dropWhile wsTab).reverse.head? = some c
  change (content.toList.reverse.dropWhile wsTab).reverse ≠ [] at hne
  have ⟨suf, hsuf⟩ := reverse_dropWhile_reverse_isPrefix wsTab content.toList
  cases htrim : (content.toList.reverse.dropWhile wsTab).reverse with
  | nil => rw [htrim] at hne; exact absurd rfl hne
  | cons a rest =>
    simp only [List.head?_cons]
    rw [htrim] at hsuf
    rw [hsuf] at hhead
    simp only [List.cons_append, List.head?_cons] at hhead
    exact hhead

/-! ### Main theorem -/

/-- `scanPlainScalar` produces a token whose plain scalar content
    satisfies `ScalarScannable`.

    Combines B3.3 (`collectPlainScalarLoop_preserves_contentInv`) with
    trim-preservation lemmas and `collectPlainScalarLoop_validFirst_and_head`
    to establish all content properties required by `ScalarScannable`.

    **Pre-condition**: The scanner state's first character satisfies
    `canStartPlainScalarBool`, as guaranteed by `scanNextToken_dispatchContent`
    before calling `scanPlainScalar`. -/
theorem scanPlainScalar_content_valid (s : ScannerState)
    (s' : ScannerState) (h : scanPlainScalar s = .ok s')
    (h_canStart : ∃ c, s.peek? = some c ∧
        canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true) :
    let idx := s.tokens.size
    ∀ (h_bound : idx < s'.tokens.size),
      match (s'.tokens[idx]'h_bound).val with
      | .scalar content .plain =>
          ScalarScannable ⟨content, .plain, none, none, none⟩ s.inFlow
      | _ => True := by
  intro idx h_bound
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i result heq
    injection h with h_eq; subst h_eq; dsimp only []
    have h_tok : result.state.tokens = s.tokens :=
      collectPlainScalarLoop_preserves_tokens s "" "" _ _ _ _ _ heq
    unfold ScannerState.emitAt
    simp only [h_tok]
    simp only [Array.getElem_push]
    have h_not_lt : ¬(idx < s.tokens.size) := Nat.lt_irrefl _
    simp only [h_not_lt, dite_false]
    intro _ hlen
    have inv := collectPlainScalarLoop_preserves_contentInv
      s "" "" _ s.inFlow _ s.inputEnd
      (PlainContentInv.empty s.inFlow s)
      (BoundaryHash.empty s.inFlow s)
      result heq
    obtain ⟨c0, hpeek0, hcs0⟩ := h_canStart
    have hne_raw : result.content ≠ "" := by
      intro he; rw [he] at hlen; simp [trimTrailingWS] at hlen
    -- Apply key lemma
    have ⟨h_vpf_raw, h_head_c0⟩ := collectPlainScalarLoop_validFirst_and_head
      s _ s.inFlow _ s.inputEnd result c0 hpeek0 hcs0 heq hne_raw
    -- Transfer validPlainFirstProp through trim
    have h_tne : (trimTrailingWS result.content).toList ≠ [] := by
      intro h_empty
      have : (trimTrailingWS result.content).toList.length = 0 := by rw [h_empty]; simp
      rw [show (trimTrailingWS result.content) = "" from by
        rw [← String.toList_inj]; simpa using h_empty] at hlen; simp at hlen
    have h_vpf : validPlainFirstProp (trimTrailingWS result.content) s.inFlow := by
      by_cases hge2 : (trimTrailingWS result.content).toList.length ≥ 2
      · rw [trimTrailingWS_eq] at hge2 ⊢
        simp only [String.toList_ofList] at hge2
        exact trim_preserves_validPlainFirst wsTab result.content.toList s.inFlow
          (by rwa [String.ofList_toList]) hge2
      · -- Trimmed has exactly 1 char (can't be 0 by h_tne)
        obtain ⟨c, hc⟩ : ∃ c, (trimTrailingWS result.content).toList = [c] := by
          cases htl : (trimTrailingWS result.content).toList with
          | nil => exact absurd htl h_tne
          | cons x rest =>
            cases rest with
            | nil => exact ⟨x, rfl⟩
            | cons y tl => simp [htl] at hge2
        -- c = c0 (trim preserves head)
        have h_trim_head := trimTrailingWS_preserves_head result.content c0 h_tne h_head_c0
        rw [hc] at h_trim_head; simp at h_trim_head
        rw [h_trim_head] at hc
        rw [show (trimTrailingWS result.content) = String.singleton c0 from by
          rw [← String.toList_inj]; simpa using hc]
        by_cases hexc : c0 = '-' ∨ c0 = '?' ∨ c0 = ':'
        · exact validPlainFirst_singleton_exception c0 s.inFlow hexc
        · simp only [validPlainFirstProp, String.toList_singleton, hexc, ↓reduceIte]
          exact canStart_nonException_to_prop c0 (s.peekAt? 1) s.inFlow hexc hcs0
    exact ⟨h_vpf,
           trimTrailingWS_noColonSpace result.content inv.content_noColonSpace,
           trimTrailingWS_noSpaceHash result.content inv.content_noSpaceHash,
           fun hflow => trimTrailingWS_noFlowIndicators result.content (inv.content_noFlowIndicators hflow)⟩

end L4YAML.Proofs.ScannerPlainScalar
