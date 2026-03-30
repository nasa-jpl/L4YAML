/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Surface.Document
import Lean4Yaml.Scanner

/-!
# Scanner ↔ Surface Syntax Bridge

Defines the formal correspondence between `ScannerState` (byte-level
scanner over `String`) and `SurfPos` (character-level surface syntax
over `List Char`), and proves coupling between scanner operations
and surface syntax predicates.

## Architecture

The bridge works through `CharsFromOffset`, an inductive relation
that connects byte offsets to character lists using the same raw
`String.Pos.Raw.get`/`next` operations as the scanner.

## Sections

1. **CharsFromOffset**: byte offset → character list relation
2. **ScannerSurfCorr**: scanner state ↔ surface position correspondence
3. **Peek/EOF**: correspondence for scanner queries
4. **Advance**: advance preserves correspondence
5. **Production coupling**: scanner ops → surface predicates
6. **Composition helpers**: building higher-level productions
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.CouplingBridge

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates

/-! ## §1 Character-at-Offset Relation -/

/-- `CharsFromOffset input offset cs` asserts that `cs` is the character
    list obtained by iterating `String.Pos.Raw.get`/`next` from `offset`
    to end-of-string. This mirrors the scanner's iteration pattern. -/
inductive CharsFromOffset (input : String) : Nat → List Char → Prop where
  | at_end (p : Nat) (h : p ≥ input.utf8ByteSize) :
      CharsFromOffset input p []
  | cons (p : Nat) (h : p < input.utf8ByteSize)
      (c : Char) (rest : List Char)
      (hc : String.Pos.Raw.get input ⟨p⟩ = c)
      (hrest : CharsFromOffset input (String.Pos.Raw.next input ⟨p⟩).byteIdx rest) :
      CharsFromOffset input p (c :: rest)

/-! ### Byte-size helpers for CharsFromOffset ↔ toList bridge -/

/-- Sum of UTF-8 byte sizes of characters in a list. -/
def listByteSize : List Char → Nat
  | [] => 0
  | c :: rest => c.utf8Size + listByteSize rest

theorem listByteSize_append (l₁ l₂ : List Char) :
    listByteSize (l₁ ++ l₂) = listByteSize l₁ + listByteSize l₂ := by
  induction l₁ with
  | nil => simp [listByteSize]
  | cons c cs ih => simp [listByteSize, ih]; omega

/-- `utf8GetAux` returns the character at the byte boundary of a prefix. -/
theorem utf8GetAux_at_boundary (pre : List Char) (c : Char) (suf : List Char)
    (base : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (pre ++ c :: suf) base
      ⟨base.byteIdx + listByteSize pre⟩ = c := by
  induction pre generalizing base with
  | nil =>
    simp [listByteSize]
    rw [String.Pos.Raw.utf8GetAux.eq_2]
    simp
  | cons p ps ih =>
    simp only [List.cons_append, listByteSize]
    rw [String.Pos.Raw.utf8GetAux.eq_2]
    have hne : base ≠ ⟨base.byteIdx + (p.utf8Size + listByteSize ps)⟩ := by
      intro heq
      have := congrArg String.Pos.Raw.byteIdx heq
      simp at this
      have := Char.utf8Size_pos p
      omega
    simp [hne]
    rw [show (⟨base.byteIdx + (p.utf8Size + listByteSize ps)⟩ : String.Pos.Raw) =
            ⟨(base + p).byteIdx + listByteSize ps⟩ from by ext; simp; omega]
    exact ih (base + p)

theorem toByteArray_eq_utf8Encode (input : String) :
    input.toByteArray = input.toList.utf8Encode := by
  have h := String.ofList_toList (s := input)
  have h2 : (String.ofList input.toList).toByteArray = input.toList.utf8Encode := by
    unfold String.ofList; rfl
  rw [h] at h2; exact h2

/-- String byte size equals the sum of character byte sizes. -/
theorem utf8ByteSize_eq_listByteSize (input : String) :
    input.utf8ByteSize = listByteSize input.toList := by
  show input.toByteArray.size = listByteSize input.toList
  rw [toByteArray_eq_utf8Encode]
  unfold List.utf8Encode
  rw [List.size_toByteArray, List.length_flatMap]
  simp only [String.length_utf8EncodeChar]
  generalize input.toList = l
  induction l with
  | nil => simp [listByteSize]
  | cons c cs ih => simp [listByteSize, ih]

theorem get_eq_utf8GetAux (input : String) (p : Nat) :
    String.Pos.Raw.get input ⟨p⟩ = String.Pos.Raw.utf8GetAux input.toList 0 ⟨p⟩ := rfl

theorem next_byteIdx (input : String) (p : Nat) :
    (String.Pos.Raw.next input ⟨p⟩).byteIdx =
    p + (String.Pos.Raw.get input ⟨p⟩).utf8Size := rfl

/-- Starting at byte offset 0, iterating get/next yields `input.toList`. -/
theorem chars_from_zero_toList (input : String) :
    CharsFromOffset input 0 input.toList := by
  suffices h : ∀ (pre suf : List Char), input.toList = pre ++ suf →
      CharsFromOffset input (listByteSize pre) suf from
    h [] input.toList (by simp)
  intro pre suf hsplit
  induction suf generalizing pre with
  | nil =>
    apply CharsFromOffset.at_end
    rw [utf8ByteSize_eq_listByteSize, hsplit, listByteSize_append]
    simp [listByteSize]
  | cons c cs ih =>
    apply CharsFromOffset.cons
    · rw [utf8ByteSize_eq_listByteSize, hsplit, listByteSize_append]
      simp [listByteSize]; have := Char.utf8Size_pos c; omega
    · rw [get_eq_utf8GetAux, hsplit]
      have h := utf8GetAux_at_boundary pre c cs (0 : String.Pos.Raw)
      simp at h; exact h
    · have hget : String.Pos.Raw.get input ⟨listByteSize pre⟩ = c := by
        rw [get_eq_utf8GetAux, hsplit]
        have h := utf8GetAux_at_boundary pre c cs (0 : String.Pos.Raw)
        simp at h; exact h
      rw [next_byteIdx, hget]
      rw [show listByteSize pre + c.utf8Size = listByteSize (pre ++ [c]) from by
            rw [listByteSize_append]; simp [listByteSize]]
      exact ih (pre ++ [c]) (by rw [hsplit, List.append_assoc]; rfl)

/-! ## §2 State Correspondence -/

/-- Scanner state and surface position correspond when the remaining
    characters match and columns agree. -/
structure ScannerSurfCorr (sc : ScannerState) (sp : SurfPos) : Prop where
  chars_from : CharsFromOffset sc.input sc.offset sp.chars
  col_eq : sp.col = sc.col
  end_eq : sc.inputEnd = sc.input.utf8ByteSize

/-- CharsFromOffset is a function: given `input` and `offset`, the
    character list is uniquely determined. -/
theorem CharsFromOffset_unique {input : String} {p : Nat}
    {cs₁ cs₂ : List Char}
    (h₁ : CharsFromOffset input p cs₁)
    (h₂ : CharsFromOffset input p cs₂) : cs₁ = cs₂ := by
  induction h₁ generalizing cs₂ with
  | at_end _ hp₁ =>
    cases h₂ with
    | at_end => rfl
    | cons _ hp₂ => omega
  | cons _ hp₁ c₁ _ hc₁ _ ih =>
    cases h₂ with
    | at_end _ hp₂ => omega
    | cons _ _ c₂ _ hc₂ hrest₂ =>
      have : c₁ = c₂ := by rw [← hc₁, ← hc₂]
      subst this
      congr 1
      exact ih hrest₂

/-- Surface position correspondence is unique: given a scanner state,
    at most one surface position corresponds to it. -/
theorem ScannerSurfCorr_unique {sc : ScannerState} {sp₁ sp₂ : SurfPos}
    (h₁ : ScannerSurfCorr sc sp₁) (h₂ : ScannerSurfCorr sc sp₂) :
    sp₁ = sp₂ := by
  have hchars := CharsFromOffset_unique h₁.chars_from h₂.chars_from
  have hcol : sp₁.col = sp₂.col := by rw [h₁.col_eq, h₂.col_eq]
  cases sp₁; cases sp₂; simp only [SurfPos.mk.injEq] at hchars hcol ⊢
  exact ⟨hchars, hcol⟩

/-- Initial state correspondence. -/
theorem initial_corr (input : String) (cs : List Char)
    (hcs : CharsFromOffset input 0 cs) :
    ScannerSurfCorr (ScannerState.mk' input) ⟨cs, 0⟩ :=
  ⟨hcs, rfl, rfl⟩

/-! ## §3 Peek/EOF Correspondence -/

/-- If the scanner has more input, the surface position is non-empty
    and its head matches `peek?`. -/
theorem peek_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hmore : sc.offset < sc.inputEnd) :
    ∃ c rest, sp.chars = c :: rest ∧ sc.peek? = some c := by
  have hlt := hcorr.end_eq ▸ hmore
  have hcf := hcorr.chars_from
  match hsp : sp.chars, hcf with
  | [], CharsFromOffset.at_end _ hp => omega
  | c :: rest, CharsFromOffset.cons _ _ _ _ hc _ =>
    exact ⟨c, rest, rfl, by simp [ScannerState.peek?, hcorr.end_eq, hlt, hc]⟩

/-- At end of input, the surface position has no remaining characters. -/
theorem eof_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (heof : ¬ sc.offset < sc.inputEnd) :
    sp.chars = [] := by
  rw [hcorr.end_eq] at heof
  have hge : sc.offset ≥ sc.input.utf8ByteSize := by omega
  have hcf := hcorr.chars_from
  match hsp : sp.chars, hcf with
  | [], _ => rfl
  | _ :: _, CharsFromOffset.cons _ hp _ _ _ _ => exact absurd hp (by omega)

/-! ## §4 Advance Correspondence

Helper lemmas extracting field projections from `ScannerState.advance`,
then the main correspondence theorems. -/

theorem advance_input (s : ScannerState) : s.advance.input = s.input := by
  unfold ScannerState.advance; split
  · dsimp only []; split
    · rfl
    · split <;> rfl
  · rfl

theorem advance_inputEnd (s : ScannerState) : s.advance.inputEnd = s.inputEnd := by
  unfold ScannerState.advance; split
  · dsimp only []; split
    · rfl
    · split <;> rfl
  · rfl

theorem advance_offset_eq (s : ScannerState) (h : s.offset < s.inputEnd) :
    s.advance.offset = (String.Pos.Raw.next s.input ⟨s.offset⟩).byteIdx := by
  unfold ScannerState.advance; split
  · dsimp only []; split
    · rfl
    · split <;> rfl
  · omega

theorem advance_col_non_newline (s : ScannerState) (h : s.offset < s.inputEnd)
    (hnl : ¬ (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = true)
    (hcr : ¬ (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\r') = true) :
    s.advance.col = s.col + 1 := by
  unfold ScannerState.advance; split
  · dsimp only []; simp [hnl, hcr]
  · omega

theorem advance_col_newline (s : ScannerState) (h : s.offset < s.inputEnd)
    (hyes : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = true) :
    s.advance.col = 0 := by
  unfold ScannerState.advance; split
  · dsimp only []; simp [hyes]
  · omega

theorem advance_col_cr (s : ScannerState) (h : s.offset < s.inputEnd)
    (hcr : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\r') = true) :
    s.advance.col = 0 := by
  have hnl : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = false := by
    have : String.Pos.Raw.get s.input ⟨s.offset⟩ = '\r' := beq_iff_eq.mp hcr
    rw [this]; decide
  unfold ScannerState.advance; split
  · dsimp only []; simp [hnl, hcr]
  · omega

/-- Advance past non-newline, non-CR preserves correspondence. -/
theorem advance_non_newline_corr (sc : ScannerState) (c : Char) (rest : List Char)
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, sc.col⟩)
    (hmore : sc.offset < sc.inputEnd)
    (hnl : c ≠ '\n')
    (hcr : c ≠ '\r') :
    ScannerSurfCorr sc.advance ⟨rest, sc.col + 1⟩ := by
  have hcf := hcorr.chars_from
  match hcf with
  | .cons _ hlt _ _ hc hrest =>
    have hnl_bool : ¬ (String.Pos.Raw.get sc.input ⟨sc.offset⟩ == '\n') = true := by
      rw [hc]; simp [hnl]
    have hcr_bool : ¬ (String.Pos.Raw.get sc.input ⟨sc.offset⟩ == '\r') = true := by
      rw [hc]; simp [hcr]
    constructor
    · rw [advance_input, advance_offset_eq sc hmore]; exact hrest
    · exact (advance_col_non_newline sc hmore hnl_bool hcr_bool).symm
    · rw [advance_inputEnd, advance_input]; exact hcorr.end_eq

/-- Advance past `\n` preserves correspondence with column reset. -/
theorem advance_newline_corr (sc : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr sc ⟨'\n' :: rest, sc.col⟩)
    (hmore : sc.offset < sc.inputEnd) :
    ScannerSurfCorr sc.advance ⟨rest, 0⟩ := by
  have hcf := hcorr.chars_from
  match hcf with
  | .cons _ hlt _ _ hc hrest =>
    have hyes : (String.Pos.Raw.get sc.input ⟨sc.offset⟩ == '\n') = true := by
      rw [hc]; decide
    constructor
    · rw [advance_input, advance_offset_eq sc hmore]; exact hrest
    · exact (advance_col_newline sc hmore hyes).symm
    · rw [advance_inputEnd, advance_input]; exact hcorr.end_eq

/-- Advance past `\r` preserves correspondence with column reset. -/
theorem advance_cr_corr (sc : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr sc ⟨'\r' :: rest, sc.col⟩)
    (hmore : sc.offset < sc.inputEnd) :
    ScannerSurfCorr sc.advance ⟨rest, 0⟩ := by
  have hcf := hcorr.chars_from
  match hcf with
  | .cons _ hlt _ _ hc hrest =>
    have hcr : (String.Pos.Raw.get sc.input ⟨sc.offset⟩ == '\r') = true := by
      rw [hc]; decide
    constructor
    · rw [advance_input, advance_offset_eq sc hmore]; exact hrest
    · exact (advance_col_cr sc hmore hcr).symm
    · rw [advance_inputEnd, advance_input]; exact hcorr.end_eq

/-- Skip one character by raw offset increment, preserving correspondence.
    Used for the `\n` byte in CRLF sequences where line counting was already
    handled by the preceding `\r` advance. -/
theorem skip_byte_corr (sc : ScannerState) (c : Char) (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩)
    (_hmore : sc.offset < sc.inputEnd) :
    ScannerSurfCorr
      { sc with offset := (String.Pos.Raw.next sc.input ⟨sc.offset⟩).byteIdx }
      ⟨rest, col⟩ := by
  have hcf := hcorr.chars_from
  match hcf with
  | .cons _ _ _ _ _ hrest =>
    constructor
    · exact hrest
    · exact hcorr.col_eq
    · exact hcorr.end_eq

/-! ## §5 Production Coupling (Scanner → Surface) -/

/-- `n` consecutive spaces give `SIndent n`. -/
theorem skipSpaces_gives_SIndent (n : Nat) (sp : SurfPos)
    (hpre : sp.chars.take n = List.replicate n ' ')
    (hlen : sp.chars.length ≥ n) :
    SIndent n sp ⟨sp.chars.drop n, sp.col + n⟩ :=
  Surface.indent_coupling n sp.chars sp.col hpre hlen

/-- `\n` gives `SBBreak`. -/
theorem lf_gives_SBBreak (sp : SurfPos) (rest : List Char)
    (hchars : sp.chars = '\n' :: rest) :
    SBBreak sp ⟨rest, 0⟩ := by
  cases sp; simp at hchars; subst hchars; exact SBBreak.lf rest _

/-- `\r\n` gives `SBBreak`. -/
theorem crlf_gives_SBBreak (sp : SurfPos) (rest : List Char)
    (hchars : sp.chars = '\r' :: '\n' :: rest) :
    SBBreak sp ⟨rest, 0⟩ := by
  cases sp; simp at hchars; subst hchars; exact SBBreak.crLf rest _

/-- `\r` gives `SBBreak`. -/
theorem cr_gives_SBBreak (sp : SurfPos) (rest : List Char)
    (hchars : sp.chars = '\r' :: rest) :
    SBBreak sp ⟨rest, 0⟩ := by
  cases sp; simp at hchars; subst hchars; exact SBBreak.cr rest _

/-! ## §6 Composition Helpers -/

/-- Start-of-line gives `SSeparateInLine`. -/
theorem start_of_line_gives_SSeparateInLine (rest : List Char) :
    SSeparateInLine ⟨rest, 0⟩ ⟨rest, 0⟩ :=
  SSeparateInLine.startOfLine rest

/-- Space gives `SSeparateInLine`. -/
theorem space_gives_SSeparateInLine (rest : List Char) (col : Nat) :
    SSeparateInLine ⟨' ' :: rest, col⟩ ⟨rest, col + 1⟩ :=
  SSeparateInLine.whites _ _
    (GPlus.mk _ _ _ (SSWhite.space rest col) (GStar.nil _))

/-- Start-of-line gives `SSLComments`. -/
theorem start_of_line_gives_SSLComments (rest : List Char) :
    SSLComments ⟨rest, 0⟩ ⟨rest, 0⟩ :=
  SSLComments.startOfLine rest ⟨rest, 0⟩ (GStar.nil _)

/-- Break gives `SSBComment`. -/
theorem break_gives_SSBComment (sp sp' : SurfPos) (hbreak : SBBreak sp sp') :
    SSBComment sp sp' :=
  SSBComment.noSep sp sp' (SBComment.break sp sp' hbreak)

/-- EOF gives `SBComment`. -/
theorem eof_gives_SBComment (col : Nat) :
    SBComment ⟨[], col⟩ ⟨[], col⟩ :=
  SBComment.eof col

/-- Empty node matches anywhere. -/
theorem empty_node (s : SurfPos) : SENode s s :=
  GEps.mk s

/-! ## §7 Bool↔Prop Character Bridging -/

/-- If `isWhiteSpaceBool c = true`, then `SSWhite` holds. -/
theorem isWhiteSpace_gives_SSWhite (c : Char) (rest : List Char) (col : Nat)
    (h : isWhiteSpaceBool c = true) :
    SSWhite ⟨c :: rest, col⟩ ⟨rest, col + 1⟩ := by
  simp [isWhiteSpaceBool, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl
  · exact SSWhite.space rest col
  · exact SSWhite.tab rest col

/-- A whitespace character (space or tab) is not `\n`. -/
theorem isWhiteSpace_not_newline (c : Char) (h : isWhiteSpaceBool c = true) : c ≠ '\n' := by
  simp [isWhiteSpaceBool, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

/-- A whitespace character (space or tab) is not `\r`. -/
theorem isWhiteSpace_not_cr (c : Char) (h : isWhiteSpaceBool c = true) : c ≠ '\r' := by
  simp [isWhiteSpaceBool, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

/-- A non-line-break character is not `\n`. -/
theorem not_isLineBreak_not_newline (c : Char) (h : ¬isLineBreakBool c = true) : c ≠ '\n' := by
  intro heq; subst heq; simp [isLineBreakBool] at h

/-- A non-line-break character is not `\r`. -/
theorem not_isLineBreak_not_cr (c : Char) (h : ¬isLineBreakBool c = true) : c ≠ '\r' := by
  intro heq; subst heq; simp [isLineBreakBool] at h

/-- A non-line-break character satisfies `isNbChar`. -/
theorem not_isLineBreak_isNbChar (c : Char) (h : ¬isLineBreakBool c = true) :
    isNbChar c := by
  intro hlb
  exact h ((isLineBreak_iff c).mpr hlb)

/-- A non-line-break character gives `SNbChar` (= `GChar isNbChar`). -/
theorem not_isLineBreak_gives_SNbChar (c : Char) (rest : List Char) (col : Nat)
    (h : ¬isLineBreakBool c = true) :
    GChar isNbChar ⟨c :: rest, col⟩ ⟨rest, col + 1⟩ :=
  GChar.mk c rest col (not_isLineBreak_isNbChar c h)

/-! ## §8 GStar Composition -/

/-- Transitivity for `GStar`: append two star sequences. -/
theorem GStar_trans {P : SurfPos → SurfPos → Prop} {s₁ s₂ s₃ : SurfPos}
    (h₁ : GStar P s₁ s₂) (h₂ : GStar P s₂ s₃) : GStar P s₁ s₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons _ _ _ hp _ ih => exact GStar.cons _ _ _ hp (ih h₂)

/-- `SIndent n` can be viewed as `GStar SSWhite` (each space is whitespace). -/
theorem SIndent_gives_GStar_SSWhite {n : Nat} {s s' : SurfPos}
    (h : SIndent n s s') : GStar SSWhite s s' := by
  induction h with
  | zero => exact GStar.nil _
  | succ k rest col _ _ ih =>
    exact GStar.cons _ _ _ (SSWhite.space rest col) ih

/-! ## §9 Field Update Correspondence -/

/-- Updating `comments` preserves correspondence. -/
theorem corr_of_comments_update {sc : ScannerState} {sp : SurfPos}
    (cs : Array (Lean4Yaml.YamlPos × String)) (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr { sc with comments := cs } sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq⟩

/-- Updating `needIndentCheck` preserves correspondence. -/
theorem corr_of_needIndentCheck_update {sc : ScannerState} {sp : SurfPos}
    (b : Bool) (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr { sc with needIndentCheck := b } sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq⟩

/-- Updating `simpleKeyAllowed` preserves correspondence. -/
theorem corr_of_simpleKeyAllowed_update {sc : ScannerState} {sp : SurfPos}
    (b : Bool) (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr { sc with simpleKeyAllowed := b } sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq⟩

end Lean4Yaml.Proofs.CouplingBridge
