/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.Scanner
import L4YAML.Spec.CharPredicates

/-!
# Plain Scalar Content Invariant (B3.2)

Defines `PlainContentInv`, the loop invariant for
`collectPlainScalarLoop` content correctness. This invariant tracks
that the accumulated `content` string satisfies the content predicates
required by `ScalarScannable`, and that `spaces` contains only
whitespace characters.

The boundary condition `boundary_colon` couples to the scanner state:
if content ends with `:`, then spaces is empty AND the next character
to scan is non-blank. This prevents `: ` from appearing at the
content–fold boundary during line folding, and is maintained because
`_terminates?` only returns `none` for `:` when the next char is
non-blank.
-/

namespace L4YAML.Proofs.ScannerPlainContent

open L4YAML.CharPredicates
open L4YAML.Scanner

/-- Loop invariant for `collectPlainScalarLoop` content correctness.
    Couples to scanner state `s` for boundary safety. -/
structure PlainContentInv (content : String) (spaces : String)
    (inFlow : Bool) (s : ScannerState) : Prop where
  /-- Content has no `: ` (colon-space) pattern. -/
  content_noColonSpace : noColonSpaceProp content
  /-- Content has no ` #` (space-hash) pattern. -/
  content_noSpaceHash : noSpaceHashProp content
  /-- In flow context, content has no flow indicators. -/
  content_noFlowIndicators : inFlow = true → noFlowIndicatorsProp content
  /-- Spaces buffer contains only whitespace characters. -/
  spaces_whitespace : ∀ c ∈ spaces.toList, isWhiteSpaceProp c
  /-- Boundary safety: if content ends with ':', spaces is empty and
      the next char to scan is non-blank. This prevents `: ` at the
      content–fold boundary during line folding. -/
  boundary_colon : content.toList.getLast? = some ':' →
      spaces = "" ∧ (∀ n, s.peek? = some n → ¬isBlankProp n)

/-- The invariant holds trivially for empty content and empty spaces
    (regardless of scanner state). -/
theorem PlainContentInv.empty (inFlow : Bool) (s : ScannerState) :
    PlainContentInv "" "" inFlow s where
  content_noColonSpace := noColonSpaceProp_empty
  content_noSpaceHash := noSpaceHashProp_empty
  content_noFlowIndicators := fun _ => noFlowIndicatorsProp_empty
  spaces_whitespace := fun _ hc => by simp [String.toList] at hc
  boundary_colon := fun h => by simp [String.toList, List.getLast?] at h

/-- Boundary invariant for the `#` case: if content ends with `' '` and
    spaces is empty, the scanner's next char is not `'#'`. This prevents
    the ` #` (space-hash) pattern at the content–fold boundary. -/
def BoundaryHash (content spaces : String) (s : ScannerState) : Prop :=
  content.toList.getLast? = some ' ' → spaces = "" → ∀ n, s.peek? = some n → n ≠ '#'

/-- BoundaryHash holds trivially for empty content. -/
theorem BoundaryHash.empty (_inFlow : Bool) (s : ScannerState) :
    BoundaryHash "" "" s :=
  fun h => by simp [String.toList, List.getLast?] at h

/-! ## Scanner State Lemmas -/

/-- `s.advance.peek?` equals `s.peekAt? 1` when the scanner has a current char. -/
theorem advance_peek_eq_peekAt_one (s : ScannerState) (c : Char)
    (h : s.peek? = some c) :
    s.advance.peek? = s.peekAt? 1 := by
  unfold ScannerState.peek? at h ⊢
  unfold ScannerState.advance
  unfold ScannerState.peekAt? ScannerState.peekAt?Loop
  split at h
  · rename_i hlt
    simp only [hlt, ↓reduceIte]
    split
    · unfold ScannerState.peekAt?Loop; simp_all
    · split <;> (unfold ScannerState.peekAt?Loop; simp_all)
  · contradiction

/-- When `_terminates?` returns `none` and `c = ':'`, the next char (`peekAt? 1`)
    is non-blank. This is the key fact for maintaining `boundary_colon`. -/
theorem terminates_none_colon_peekAt_nonblank (s : ScannerState) (c : Char)
    (content spaces : String) (inFlow : Bool)
    (hterm : collectPlainScalar_terminates? c s content spaces inFlow = none)
    (hcolon : c = ':') :
    ∃ n, s.peekAt? 1 = some n ∧ ¬isBlankProp n := by
  subst hcolon
  unfold collectPlainScalar_terminates? at hterm
  simp only [beq_self_eq_true, show (':' == '#') = false from rfl,
             Bool.false_and, ↓reduceIte, Bool.false_eq_true] at hterm
  match hpa : s.peekAt? 1 with
  | none => simp [hpa] at hterm
  | some n =>
    simp [hpa] at hterm
    exact ⟨n, rfl, fun hb => absurd ((isBlank_iff n).mpr hb) (by simp [hterm.1])⟩

/-! ## Content String Property Lemmas -/

/-- `noColonSpaceProp` for a single space string. -/
theorem noColonSpaceProp_space : noColonSpaceProp " " := by
  intro ⟨i, h1, _⟩
  have : " ".toList = [' '] := by native_decide
  rw [this] at h1
  cases i <;> simp at h1

/-- `noSpaceHashProp` for a single space string. -/
theorem noSpaceHashProp_space : noSpaceHashProp " " := by
  intro ⟨i, _, h2⟩
  have : " ".toList = [' '] := by native_decide
  rw [this] at h2
  cases i <;> simp at h2

/-- `noFlowIndicatorsProp` for a single space string. -/
theorem noFlowIndicatorsProp_space : noFlowIndicatorsProp " " := by
  intro c hc
  have : " ".toList = [' '] := by native_decide
  rw [this] at hc; simp at hc; subst hc
  intro h; simp [isFlowIndicatorProp] at h

/-- Helper: elements of `List.replicate` are all the replicated element. -/
theorem replicate_getElem?_char {a b : Char} {n i : Nat}
    (h : (List.replicate n a)[i]? = some b) : b = a := by
  rw [List.getElem?_replicate] at h
  split at h
  · exact Option.some.inj h.symm
  · simp at h

/-- `noColonSpaceProp` for strings of newlines only. -/
theorem noColonSpaceProp_replicate_newline (n : Nat) :
    noColonSpaceProp (String.ofList (List.replicate n '\n')) := by
  intro ⟨i, h1, _⟩
  simp only [String.toList_ofList] at h1
  exact absurd (replicate_getElem?_char h1) (by decide)

/-- `noSpaceHashProp` for strings of newlines only. -/
theorem noSpaceHashProp_replicate_newline (n : Nat) :
    noSpaceHashProp (String.ofList (List.replicate n '\n')) := by
  intro ⟨i, h1, _⟩
  simp only [String.toList_ofList] at h1
  exact absurd (replicate_getElem?_char h1) (by decide)

/-- `noFlowIndicatorsProp` for strings of newlines only. -/
theorem noFlowIndicatorsProp_replicate_newline (n : Nat) :
    noFlowIndicatorsProp (String.ofList (List.replicate n '\n')) := by
  intro c hc
  simp only [String.toList_ofList] at hc
  have := List.eq_of_mem_replicate hc
  subst this
  intro h; simp [isFlowIndicatorProp] at h

/-- Last character of `content ++ " "` is `' '`. -/
theorem getLast_append_space (content : String) :
    (content ++ " ").toList.getLast? = some ' ' := by
  have htl : " ".toList = [' '] := by native_decide
  rw [String.toList_append, htl]
  simp [List.getLast?_append]

/-- Last character of `content ++ replicate n '\n'` is `'\n'` when `n > 0`. -/
theorem getLast_append_replicate_newline (content : String) (n : Nat) (hn : n > 0) :
    (content ++ String.ofList (List.replicate n '\n')).toList.getLast? = some '\n' := by
  rw [String.toList_append, String.toList_ofList]
  have hne : List.replicate n '\n' ≠ [] := by
    intro h; simp [List.replicate_eq_nil_iff] at h; omega
  simp [List.getLast?_append, hne]
  rw [List.getLast?_eq_some_getLast hne]
  congr 1; exact List.getLast_replicate hne

/-- First character of `" "` is `' '`. -/
theorem head_space : " ".toList.head? = some ' ' := by native_decide

/-- First character of `replicate n '\n'` is `'\n'` when `n > 0`. -/
theorem head_replicate_newline (n : Nat) (hn : n > 0) :
    (String.ofList (List.replicate n '\n')).toList.head? = some '\n' := by
  simp only [String.toList_ofList]
  cases n with
  | zero => omega
  | succ n' => simp [List.replicate]

/-! ## Main Preservation Theorem (B3.3) -/

/-- Helper: `'#'` is not blank. -/
theorem hash_not_blank : ¬isBlankProp '#' := by
  simp [isBlankProp, isWhiteSpaceProp, isLineBreakProp]

/-- When `_terminates?` returns `some result`, content, spaces, and state are unchanged. -/
theorem terminates_preserves_all
    (c : Char) (s : ScannerState) (content spaces : String) (inFlow : Bool) (r : PlainScalarResult)
    (h : collectPlainScalar_terminates? c s content spaces inFlow = some r) :
    r.content = content ∧ r.spaces = spaces ∧ r.state = s := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · injection h with h; rw [← h]; exact ⟨rfl, rfl, rfl⟩
  · split at h
    · -- c == ':'
      simp only at h
      split at h <;> (split at h <;> first | (injection h with h; rw [← h]; exact ⟨rfl, rfl, rfl⟩) | contradiction)
    · split at h
      · injection h with h; rw [← h]; exact ⟨rfl, rfl, rfl⟩
      · split at h
        · injection h with h; rw [← h]; exact ⟨rfl, rfl, rfl⟩
        · contradiction

/-- Transfer `PlainContentInv` to a new state where `peek?` is known non-blank. -/
theorem PlainContentInv.transfer_nonblank_peek
    {content spaces : String} {inFlow : Bool} {s : ScannerState}
    (inv : PlainContentInv content spaces inFlow s)
    (s' : ScannerState) (c : Char)
    (hpeek : s'.peek? = some c) (hnotblank : ¬isBlankProp c) :
    PlainContentInv content spaces inFlow s' where
  content_noColonSpace := inv.content_noColonSpace
  content_noSpaceHash := inv.content_noSpaceHash
  content_noFlowIndicators := inv.content_noFlowIndicators
  spaces_whitespace := inv.spaces_whitespace
  boundary_colon hcolon :=
    ⟨(inv.boundary_colon hcolon).1,
     fun n hp => by rw [hpeek] at hp; injection hp; subst_vars; exact hnotblank⟩

/-- When `_handleBlockLineBreak` returns `some (content', s')`, content' is
    `content ++ " "` or `content ++ replicate '\n'`. -/
theorem handleBlockLineBreak_content_form
    (s : ScannerState) (content : String) (contentIndent inputEnd : Nat)
    (content' : String) (s' : ScannerState)
    (h : collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd = some (content', s')) :
    (content' = content ++ " ") ∨
    (∃ n, n > 0 ∧ content' = content ++ String.ofList (List.replicate n '\n')) := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · rename_i hempty
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        right; exact ⟨_, hempty, this.1.symm⟩
      · have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        left; exact this.1.symm

/-- When `foldQuotedNewlines` succeeds, the folded string is `" "` or replicate newlines. -/
theorem foldQuotedNewlines_result_form
    (s : ScannerState) (folded : String) (s' : ScannerState)
    (h : foldQuotedNewlines s = .ok (folded, s')) :
    (folded = " ") ∨
    (∃ n, n > 0 ∧ folded = String.ofList (List.replicate n '\n')) := by
  unfold foldQuotedNewlines at h
  dsimp only at h
  split at h
  · split at h
    · simp only [pure, Except.pure] at h
      split at h <;> contradiction
    · split at h
      · rename_i hempty
        have := Except.ok.inj h
        simp only [Prod.mk.injEq] at this
        right; exact ⟨_, hempty, this.1.symm⟩
      · have := Except.ok.inj h
        simp only [Prod.mk.injEq] at this
        left; exact this.1.symm
  · split at h
    · rename_i hempty
      have := Except.ok.inj h
      simp only [Prod.mk.injEq] at this
      right; exact ⟨_, hempty, this.1.symm⟩
    · have := Except.ok.inj h
      simp only [Prod.mk.injEq] at this
      left; exact this.1.symm

/-- Build `PlainContentInv` for `content ++ fold` where `fold` is `" "` or replicate newlines.
    Used by both block and flow linebreak recursion cases. -/
theorem PlainContentInv.of_fold
    {content spaces : String} {inFlow : Bool} {s s' : ScannerState}
    (inv : PlainContentInv content spaces inFlow s)
    (c : Char) (hpeek : s.peek? = some c) (hc_lb : isLineBreakProp c)
    (fold : String)
    (hfold : (fold = " ") ∨ (∃ n, n > 0 ∧ fold = String.ofList (List.replicate n '\n')))
    (_hpeek' : ∀ n, s'.peek? = some n → n ≠ '#') :
    PlainContentInv (content ++ fold) "" inFlow s' where
  content_noColonSpace := by
    rcases hfold with rfl | ⟨n, hn, rfl⟩
    · apply noColonSpaceProp_append content " " inv.content_noColonSpace noColonSpaceProp_space
      intro ⟨hcl, _⟩
      exact (inv.boundary_colon hcl).2 c hpeek (Or.inr hc_lb)
    · apply noColonSpaceProp_append content _ inv.content_noColonSpace
          (noColonSpaceProp_replicate_newline n)
      intro ⟨hcl, hh⟩
      rw [head_replicate_newline n hn] at hh; contradiction
  content_noSpaceHash := by
    rcases hfold with rfl | ⟨n, hn, rfl⟩
    · apply noSpaceHashProp_append content " " inv.content_noSpaceHash noSpaceHashProp_space
      intro ⟨_, hh⟩; rw [head_space] at hh; contradiction
    · apply noSpaceHashProp_append content _ inv.content_noSpaceHash
          (noSpaceHashProp_replicate_newline n)
      intro ⟨_, hh⟩; rw [head_replicate_newline n hn] at hh; contradiction
  content_noFlowIndicators := fun hflow => by
    rcases hfold with rfl | ⟨n, _, rfl⟩
    · exact noFlowIndicatorsProp_append content " "
          (inv.content_noFlowIndicators hflow) noFlowIndicatorsProp_space
    · exact noFlowIndicatorsProp_append content _
          (inv.content_noFlowIndicators hflow) (noFlowIndicatorsProp_replicate_newline n)
  spaces_whitespace := fun _ hc => by simp [String.toList] at hc
  boundary_colon := by
    intro hcolon
    rcases hfold with rfl | ⟨n, hn, rfl⟩
    · rw [getLast_append_space] at hcolon; contradiction
    · rw [getLast_append_replicate_newline content n hn] at hcolon; contradiction

/-- `collectPlainScalarLoop` preserves `PlainContentInv`.
    If the invariant holds for the input `content`, `spaces`, `inFlow`, and `s`,
    then it holds for the result's `content`, `spaces`, `inFlow`, and `state`. -/
theorem collectPlainScalarLoop_preserves_contentInv
    (s : ScannerState) (content spaces : String) (fuel : Nat)
    (inFlow : Bool) (contentIndent : Nat) (inputEnd : Nat)
    (inv : PlainContentInv content spaces inFlow s)
    (bh : BoundaryHash content spaces s) :
    ∀ result,
      collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd = .ok result →
      PlainContentInv result.content result.spaces inFlow result.state := by
  intro result h
  induction fuel generalizing s content spaces with
  | zero =>
    unfold collectPlainScalarLoop at h
    injection h with h_eq; cases h_eq; exact inv
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · -- peek? = none
      injection h with h_eq; cases h_eq; exact inv
    · -- peek? = some c
      rename_i c hpeek
      split at h
      · -- _terminates? = some → terminate
        rename_i hterm
        injection h with h_eq; cases h_eq
        have ⟨hc, hs, hst⟩ := terminates_preserves_all _ _ _ _ _ _ hterm
        rw [hc, hs, hst]
        exact inv
      · -- _terminates? = none → continue
        rename_i hterm
        split at h
        · -- isLineBreak c
          split at h
          · -- inFlow: flow line break via foldQuotedNewlines
            simp only [bind, Except.bind] at h
            split at h <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk folded s_fold =>
              split at h
              · -- s_fold.peek? = some '#' → terminate with state = s
                injection h with h_eq; cases h_eq; exact inv
              · -- recurse with content-length check
                rename_i hfoldpeek
                dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s_fold _ "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · -- ≤ prevLen → state = s, content unchanged
                    injection h with h_eq; cases h_eq; exact inv
                  · -- > prevLen → use ih
                    have h_eq := Except.ok.inj h; subst h_eq
                    have hc_lb : isLineBreakProp c := by
                      have : isLineBreakBool c = true := by assumption
                      exact (isLineBreak_iff c).mp this
                    have hfold := foldQuotedNewlines_result_form s folded s_fold heq
                    have hpeek_ne : ∀ n, s_fold.peek? = some n → n ≠ '#' := by
                      intro n hn heq'; rw [heq'] at hn; exact hfoldpeek hn
                    rcases hfold with rfl | ⟨n, hn, rfl⟩
                    · apply ih s_fold (content ++ " ") ""
                      · exact PlainContentInv.of_fold inv c hpeek hc_lb " " (.inl rfl) hpeek_ne
                      · intro _ _; exact hpeek_ne
                      · exact h_loop
                    · apply ih s_fold (content ++ String.ofList (List.replicate n '\n')) ""
                      · exact PlainContentInv.of_fold inv c hpeek hc_lb _ (.inr ⟨n, hn, rfl⟩) hpeek_ne
                      · intro hlast _
                        rw [getLast_append_replicate_newline content n hn] at hlast
                        exact absurd hlast (by decide)
                      · exact h_loop
                | error e => simp at h
          · -- !inFlow: block line break
            split at h
            · -- _handleBlockLineBreak = none → terminate
              injection h with h_eq; cases h_eq; exact inv
            · -- _handleBlockLineBreak = some (content', s')
              rename_i content' s' hblk
              split at h
              · -- s'.peek? = some '#' → terminate with state = s
                injection h with h_eq; cases h_eq; exact inv
              · -- recurse with content-length check
                rename_i hblkpeek
                dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · -- ≤ prevLen → state = s, content unchanged
                    injection h with h_eq; cases h_eq; exact inv
                  · -- > prevLen → use ih
                    have h_eq := Except.ok.inj h; subst h_eq
                    have hc_lb : isLineBreakProp c := by
                      have : isLineBreakBool c = true := by assumption
                      exact (isLineBreak_iff c).mp this
                    have hfold := handleBlockLineBreak_content_form s content contentIndent inputEnd content' s' hblk
                    have hpeek_ne : ∀ n, s'.peek? = some n → n ≠ '#' := by
                      intro n hn heq; rw [heq] at hn; exact hblkpeek hn
                    rcases hfold with rfl | ⟨n, hn, rfl⟩
                    · apply ih s' (content ++ " ") ""
                      · exact PlainContentInv.of_fold inv c hpeek hc_lb " " (.inl rfl) hpeek_ne
                      · intro _ _; exact hpeek_ne
                      · exact h_loop
                    · apply ih s' (content ++ String.ofList (List.replicate n '\n')) ""
                      · exact PlainContentInv.of_fold inv c hpeek hc_lb _ (.inr ⟨n, hn, rfl⟩) hpeek_ne
                      · intro hlast _
                        rw [getLast_append_replicate_newline content n hn] at hlast
                        exact absurd hlast (by decide)
                      · exact h_loop
                | error e => simp at h
        · split at h
          · -- isWhiteSpace c → spaces grows, content unchanged
            rename_i hws
            have hIsWS : isWhiteSpaceProp c := (isWhiteSpace_iff c).mp hws
            apply ih s.advance content (spaces.push c)
            · exact {
                content_noColonSpace := inv.content_noColonSpace
                content_noSpaceHash := inv.content_noSpaceHash
                content_noFlowIndicators := inv.content_noFlowIndicators
                spaces_whitespace := fun x hx => by
                  rw [String.toList_push] at hx
                  rcases List.mem_append.mp hx with hx' | hx'
                  · exact inv.spaces_whitespace x hx'
                  · simp at hx'; rw [hx']; exact hIsWS
                boundary_colon := fun hcolon => by
                  exfalso
                  exact (inv.boundary_colon hcolon).2 c hpeek (Or.inl hIsWS)
              }
            · -- BoundaryHash: content.getLast? = ' ' → spaces.push c = "" → ...
              -- spaces.push c is never "", so the second hypothesis is vacuously false
              intro _ habs
              exact absurd habs (by intro h'; have := String.toList_push (s := spaces) (c := c); rw [h'] at this; simp at this)
            · exact h
          · -- not whitespace, not linebreak
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; exact inv
            · -- plainSafe → content' = content ++ spaces ++ singleton c, recurse
              rename_i hps
              simp only [] at h
              have hPlainSafe : isPlainSafeProp c inFlow := by
                simp at hps
                exact (isPlainSafe_iff c inFlow).mp hps
              have hNotSpace : c ≠ ' ' := not_space_of_plainSafe c inFlow hPlainSafe
              apply ih s.advance (content ++ spaces ++ String.singleton c) ""
              · -- PlainContentInv
                exact {
                  content_noColonSpace := by
                    apply noColonSpaceProp_append
                    · apply noColonSpaceProp_append content spaces
                          inv.content_noColonSpace
                          (noColonSpaceProp_of_whitespace spaces inv.spaces_whitespace)
                      intro ⟨hcl, hsh⟩
                      have := (inv.boundary_colon hcl).1
                      rw [this] at hsh; simp [String.toList] at hsh
                    · intro ⟨_, h2⟩; simp [String.toList_singleton] at h2
                    · intro ⟨_, hh⟩
                      simp [String.toList_singleton] at hh
                      exact absurd hh hNotSpace
                  content_noSpaceHash := by
                    apply noSpaceHashProp_append
                    · apply noSpaceHashProp_append content spaces
                          inv.content_noSpaceHash
                          (noSpaceHashProp_of_whitespace spaces inv.spaces_whitespace)
                      intro ⟨_, hh⟩
                      cases hl : spaces.toList with
                      | nil => simp [hl] at hh
                      | cons x xs =>
                        simp [hl] at hh; rw [hh] at hl
                        exact absurd (inv.spaces_whitespace '#' (hl ▸ List.Mem.head _))
                          (by simp [isWhiteSpaceProp])
                    · intro ⟨_, h2⟩; simp [String.toList_singleton] at h2
                    · intro ⟨hgl, hch⟩
                      simp [String.toList_singleton] at hch
                      rw [hch] at hpeek hterm
                      cases hl : spaces.toList with
                      | nil =>
                        simp [String.toList_append, hl] at hgl
                        have hse : spaces = "" := String.ext_iff.mpr (by rw [hl]; rfl)
                        exact absurd rfl (bh hgl hse '#' hpeek)
                      | cons _ _ =>
                        have hlen : spaces.length > 0 := by
                          rw [← String.length_toList]; simp [hl]
                        have : collectPlainScalar_terminates? '#' s content spaces inFlow ≠ none := by
                          unfold collectPlainScalar_terminates?; simp [hlen]
                        contradiction
                  content_noFlowIndicators := fun hflow => by
                    have hNotFI : ¬isFlowIndicatorProp c := by
                      have hp := hPlainSafe; rw [hflow] at hp
                      simp [isPlainSafeProp] at hp; exact hp.2.2
                    apply noFlowIndicatorsProp_append
                    · apply noFlowIndicatorsProp_append _ _
                          (inv.content_noFlowIndicators hflow)
                          (noFlowIndicatorsProp_of_whitespace spaces inv.spaces_whitespace)
                    · intro x hx; simp [String.toList_singleton] at hx; subst hx; exact hNotFI
                  spaces_whitespace := fun _ hc => by simp [String.toList] at hc
                  boundary_colon := by
                    intro hcolon
                    simp [String.toList_append, List.getLast?_append] at hcolon
                    subst hcolon -- c = ':'
                    exact ⟨rfl, fun n hn => by
                      have ⟨m, hm, hnb⟩ := terminates_none_colon_peekAt_nonblank s ':' content spaces inFlow hterm rfl
                      rw [advance_peek_eq_peekAt_one s ':' hpeek, hm] at hn
                      exact Option.some.inj hn ▸ hnb⟩
                }
              · -- BoundaryHash: getLast? = some c, c ≠ ' ' (plainSafe)
                intro hlast _
                simp [String.toList_append, List.getLast?_append] at hlast
                exact absurd hlast hNotSpace
              · exact h

end L4YAML.Proofs.ScannerPlainContent
