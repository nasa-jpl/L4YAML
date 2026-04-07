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

/-- `utf8PrevAux` returns the start position of the character at a given boundary.
    Dual of `utf8GetAux_at_boundary`: prev at the end of character `c` returns its start. -/
theorem utf8PrevAux_at_boundary (pre : List Char) (c : Char) (suf : List Char)
    (base_n : Nat) :
    String.Pos.Raw.utf8PrevAux (pre ++ c :: suf) ⟨base_n⟩
      ⟨base_n + listByteSize pre + c.utf8Size⟩ =
    ⟨base_n + listByteSize pre⟩ := by
  induction pre generalizing base_n with
  | nil =>
    simp only [List.nil_append, listByteSize, Nat.add_zero]
    rw [String.Pos.Raw.utf8PrevAux.eq_2]
    split
    · rfl
    · rename_i h; exfalso; exact h (Nat.le_refl _)
  | cons p ps ih =>
    simp only [List.cons_append, listByteSize]
    rw [String.Pos.Raw.utf8PrevAux.eq_2]
    split
    · exfalso; rename_i h
      have h_nat : base_n + (p.utf8Size + listByteSize ps) + c.utf8Size ≤
                   base_n + p.utf8Size := h
      have := Char.utf8Size_pos c; omega
    · rename_i _h
      rw [show (⟨base_n⟩ : String.Pos.Raw) + p = ⟨base_n + p.utf8Size⟩ from rfl]
      have h1 : (⟨base_n + (p.utf8Size + listByteSize ps) + c.utf8Size⟩ : String.Pos.Raw) =
                 ⟨base_n + p.utf8Size + listByteSize ps + c.utf8Size⟩ := by
        show String.Pos.Raw.mk _ = String.Pos.Raw.mk _; congr 1; omega
      have h2 : (⟨base_n + (p.utf8Size + listByteSize ps)⟩ : String.Pos.Raw) =
                 ⟨base_n + p.utf8Size + listByteSize ps⟩ := by
        show String.Pos.Raw.mk _ = String.Pos.Raw.mk _; congr 1; omega
      rw [h1, h2]
      exact ih (base_n + p.utf8Size)

/-- prev(next(p)) = p when the character list prefix is known.
    Uses `utf8PrevAux_at_boundary` with the concrete prefix. -/
theorem prev_next_with_prefix (input : String) (pre : List Char)
    (c : Char) (rest : List Char)
    (hsplit : input.toList = pre ++ c :: rest) :
    String.Pos.Raw.prev input (String.Pos.Raw.next input ⟨listByteSize pre⟩) =
      ⟨listByteSize pre⟩ := by
  show String.Pos.Raw.utf8PrevAux input.toList 0
    (String.Pos.Raw.next input ⟨listByteSize pre⟩) = ⟨listByteSize pre⟩
  have hget : String.Pos.Raw.get input ⟨listByteSize pre⟩ = c := by
    show String.Pos.Raw.utf8GetAux input.toList 0 ⟨listByteSize pre⟩ = c
    rw [hsplit]
    have := utf8GetAux_at_boundary pre c rest (0 : String.Pos.Raw)
    simp at this; exact this
  rw [show String.Pos.Raw.next input ⟨listByteSize pre⟩ =
          ⟨listByteSize pre + c.utf8Size⟩ from by
            ext; show (String.Pos.Raw.next input ⟨listByteSize pre⟩).byteIdx =
              listByteSize pre + c.utf8Size
            unfold String.Pos.Raw.next; simp [hget]]
  rw [hsplit]
  have h := utf8PrevAux_at_boundary pre c rest 0
  simp at h
  exact h

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
    characters match and columns agree.

    The `input_prefix` field witnesses that `sc.offset` is at a valid UTF-8
    character boundary and that `sp.chars` is the suffix of `input.toList`
    starting there.  This is needed for `peekBack?` reasoning
    (see `prev_next_with_prefix`). -/
structure ScannerSurfCorr (sc : ScannerState) (sp : SurfPos) : Prop where
  chars_from : CharsFromOffset sc.input sc.offset sp.chars
  col_eq : sp.col = sc.col
  end_eq : sc.inputEnd = sc.input.utf8ByteSize
  input_prefix : ∃ pre, sc.input.toList = pre ++ sp.chars ∧ listByteSize pre = sc.offset
  indent_cols_nonneg : ∀ (i : Nat) (hi : i < sc.indents.size), i > 0 → sc.indents[i].column ≥ 0

-- Derive `currentIndent ≥ 0` from `ScannerSurfCorr` when indent stack has non-sentinel entries.
theorem ScannerSurfCorr.currentIndent_nonneg {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hne : sc.indents.size > 1) :
    sc.currentIndent ≥ 0 := by
  simp only [ScannerState.currentIndent]
  have hback : sc.indents.back? = some sc.indents[sc.indents.size - 1] := by
    rw [Array.back?_eq_getElem?]
    simp [Array.getElem?_eq_getElem (by omega : sc.indents.size - 1 < sc.indents.size)]
  rw [hback]
  exact hcorr.indent_cols_nonneg _ (by omega) (by omega)

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
  have heq : cs = input.toList := CharsFromOffset_unique hcs (chars_from_zero_toList input)
  ⟨hcs, rfl, rfl, ⟨[], by subst heq; exact ⟨rfl, rfl⟩⟩,
   fun i hi h0 => by simp [ScannerState.mk'] at hi; omega⟩

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

/-! ### peekAt? ↔ CharsFromOffset bridge -/

theorem peekAtLoop_cons {input : String} {inputEnd p : Nat}
    {c : Char} {rest : List Char}
    (hlt : p < inputEnd)
    (hcf : CharsFromOffset input p (c :: rest)) :
    ScannerState.peekAt?Loop input inputEnd ⟨p⟩ 0 = some c := by
  cases hcf with
  | cons _ hp _ _ hc hrest =>
    simp [ScannerState.peekAt?Loop, show p < inputEnd from hlt, hc]

theorem peekAtLoop_step {input : String} {inputEnd p : Nat} {n : Nat}
    (hlt : p < inputEnd) :
    ScannerState.peekAt?Loop input inputEnd ⟨p⟩ (n + 1) =
    ScannerState.peekAt?Loop input inputEnd
      (String.Pos.Raw.next input ⟨p⟩) n := by
  simp [ScannerState.peekAt?Loop, show p < inputEnd from hlt]

/-- When the surface chars begin with `c :: rest`, `peekAt? 0 = some c`. -/
theorem peekAt_zero_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (c : Char) (rest : List Char) (hchars : sp.chars = c :: rest) :
    sc.peekAt? 0 = some c := by
  unfold ScannerState.peekAt?
  have hlt : sc.offset < sc.inputEnd := by
    rw [hcorr.end_eq]
    have hcf := hcorr.chars_from; rw [hchars] at hcf
    exact match hcf with | .cons _ h _ _ _ _ => h
  exact peekAtLoop_cons hlt (hchars ▸ hcorr.chars_from)

/-- Extract `CharsFromOffset` for the tail after a cons. -/
theorem chars_from_cons_tail {input : String} {p : Nat}
    {c : Char} {rest : List Char}
    (hcf : CharsFromOffset input p (c :: rest)) :
    CharsFromOffset input (String.Pos.Raw.next input ⟨p⟩).byteIdx rest := by
  cases hcf with | cons _ _ _ _ _ hrest => exact hrest

/-- `atDocumentStart` + `ScannerSurfCorr` implies chars begin with `---`.
    Extracts the char pattern needed by `scanDocumentStart_prod`. -/
theorem option_beq_some_eq {c d : Char} (h : (some c == some d) = true) : c = d := by
  simp [beq_iff_eq] at h; exact h

theorem option_beq_none_absurd {d : Char} (h : (none == some d) = true) : False := by
  simp [] at h

/-- Extract hypotheses from `atDocumentStart sc = true`. -/
theorem atDocumentStart_decompose {sc : ScannerState}
    (h : atDocumentStart sc = true) :
    sc.col = 0 ∧ sc.peekAt? 0 = some '-' ∧
    sc.peekAt? 1 = some '-' ∧ sc.peekAt? 2 = some '-' := by
  unfold atDocumentStart at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hcol, hp0⟩, hp1⟩, hp2⟩, _⟩ := h
  refine ⟨by exact beq_iff_eq.mp hcol, ?_, ?_, ?_⟩
  · generalize hv : sc.peekAt? 0 = v at hp0
    cases v with
    | none => exact absurd hp0 (by decide)
    | some c => rw [show c = '-' from option_beq_some_eq hp0]
  · generalize hv : sc.peekAt? 1 = v at hp1
    cases v with
    | none => exact absurd hp1 (by decide)
    | some c => rw [show c = '-' from option_beq_some_eq hp1]
  · generalize hv : sc.peekAt? 2 = v at hp2
    cases v with
    | none => exact absurd hp2 (by decide)
    | some c => rw [show c = '-' from option_beq_some_eq hp2]

/-- Extract hypotheses from `atDocumentEnd sc = true`. -/
theorem atDocumentEnd_decompose {sc : ScannerState}
    (h : atDocumentEnd sc = true) :
    sc.col = 0 ∧ sc.peekAt? 0 = some '.' ∧
    sc.peekAt? 1 = some '.' ∧ sc.peekAt? 2 = some '.' := by
  unfold atDocumentEnd at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hcol, hp0⟩, hp1⟩, hp2⟩, _⟩ := h
  refine ⟨by exact beq_iff_eq.mp hcol, ?_, ?_, ?_⟩
  · generalize hv : sc.peekAt? 0 = v at hp0
    cases v with
    | none => exact absurd hp0 (by decide)
    | some c => rw [show c = '.' from option_beq_some_eq hp0]
  · generalize hv : sc.peekAt? 1 = v at hp1
    cases v with
    | none => exact absurd hp1 (by decide)
    | some c => rw [show c = '.' from option_beq_some_eq hp1]
  · generalize hv : sc.peekAt? 2 = v at hp2
    cases v with
    | none => exact absurd hp2 (by decide)
    | some c => rw [show c = '.' from option_beq_some_eq hp2]

/-- When `peekAt? n` returns `some c`, the character at offset+n positions
    in the chars list equals `c`. Helper lemma for extracting chars from
    `peekAt?`. -/
theorem peekAtLoop_some_chars {input : String} {inputEnd p : Nat}
    {n : Nat} {c : Char}
    (hend : inputEnd = input.utf8ByteSize)
    (hok : ScannerState.peekAt?Loop input inputEnd ⟨p⟩ n = some c)
    (cs : List Char) (hcf : CharsFromOffset input p cs) :
    ∃ pre rest, cs = pre ++ c :: rest ∧ pre.length = n := by
  induction n generalizing p cs with
  | zero =>
    unfold ScannerState.peekAt?Loop at hok
    split at hok
    · -- p < inputEnd branch
      cases hcf with
      | at_end _ hp => exact absurd (show p < input.utf8ByteSize from hend ▸ ‹_›) (by omega)
      | cons _ _ c' rest hc' hrest =>
        have hinj := Option.some.inj hok
        have : c' = c := by rw [← hc']; exact hinj
        exact ⟨[], rest, by subst this; rfl, rfl⟩
    · exact absurd hok nofun
  | succ n ih =>
    unfold ScannerState.peekAt?Loop at hok
    split at hok
    · -- p < inputEnd branch
      cases hcf with
      | at_end _ hp => exact absurd (show p < input.utf8ByteSize from hend ▸ ‹_›) (by omega)
      | cons _ _ c' rest hc' hrest =>
        -- hok : peekAtLoop ... (next input ⟨p⟩) n = some c
        obtain ⟨pre', rest', heq, hlen⟩ := ih hok rest hrest
        exact ⟨c' :: pre', rest', by simp [heq], by simp; exact hlen⟩
    · exact absurd hok nofun

/-- When we have `peekAt? 0/1/2` all returning `some`, extract the first three
    chars from `sp.chars`.  Used by `atDocumentStart_chars` and `atDocumentEnd_chars`. -/
theorem three_peekAt_to_chars {sc : ScannerState} {sp : SurfPos} {c0 c1 c2 : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hp0 : sc.peekAt? 0 = some c0)
    (hp1 : sc.peekAt? 1 = some c1)
    (hp2 : sc.peekAt? 2 = some c2) :
    ∃ rest, sp.chars = c0 :: c1 :: c2 :: rest := by
  unfold ScannerState.peekAt? at hp0 hp1 hp2
  obtain ⟨pre0, rest0, hcs0, hlen0⟩ :=
    peekAtLoop_some_chars hcorr.end_eq hp0 sp.chars hcorr.chars_from
  obtain ⟨pre1, rest1, hcs1, hlen1⟩ :=
    peekAtLoop_some_chars hcorr.end_eq hp1 sp.chars hcorr.chars_from
  obtain ⟨pre2, rest2, hcs2, hlen2⟩ :=
    peekAtLoop_some_chars hcorr.end_eq hp2 sp.chars hcorr.chars_from
  -- pre0 = [] (length 0)
  have h0 : pre0 = [] := by
    cases pre0 with
    | nil => rfl
    | cons _ _ => simp at hlen0
  subst h0; simp only [List.nil_append] at hcs0
  rw [hcs0] at hcs1 hcs2
  -- pre1 has 1 element
  have h1 : ∃ a, pre1 = [a] := by
    cases pre1 with
    | nil => simp at hlen1
    | cons a as =>
      cases as with
      | nil => exact ⟨a, rfl⟩
      | cons _ _ => simp at hlen1
  obtain ⟨a, rfl⟩ := h1
  simp at hcs1; obtain ⟨rfl, rfl⟩ := hcs1
  -- pre2 has 2 elements
  have h2 : ∃ b d, pre2 = [b, d] := by
    cases pre2 with
    | nil => simp at hlen2
    | cons b bs =>
      cases bs with
      | nil => simp at hlen2
      | cons d ds =>
        cases ds with
        | nil => exact ⟨b, d, rfl⟩
        | cons _ _ => simp at hlen2
  obtain ⟨b, d, rfl⟩ := h2
  simp at hcs2; obtain ⟨rfl, rfl, rfl⟩ := hcs2
  exact ⟨rest2, hcs0⟩

theorem atDocumentStart_chars (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (h_at : atDocumentStart sc = true) :
    ∃ rest, sp.chars = '-' :: '-' :: '-' :: rest ∧ sp.col = 0 := by
  obtain ⟨hcol, hp0, hp1, hp2⟩ := atDocumentStart_decompose h_at
  have hcol_sp : sp.col = 0 := by rw [hcorr.col_eq]; exact_mod_cast hcol
  obtain ⟨rest, hchars⟩ := three_peekAt_to_chars hcorr hp0 hp1 hp2
  exact ⟨rest, hchars, hcol_sp⟩

/-- `atDocumentEnd` + `ScannerSurfCorr` implies chars begin with `...`.
    Extracts the char pattern needed by `scanDocumentEnd_prod`. -/
theorem atDocumentEnd_chars (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (h_at : atDocumentEnd sc = true) :
    ∃ rest, sp.chars = '.' :: '.' :: '.' :: rest ∧ sp.col = 0 := by
  obtain ⟨hcol, hp0, hp1, hp2⟩ := atDocumentEnd_decompose h_at
  have hcol_sp : sp.col = 0 := by rw [hcorr.col_eq]; exact_mod_cast hcol
  obtain ⟨rest, hchars⟩ := three_peekAt_to_chars hcorr hp0 hp1 hp2
  exact ⟨rest, hchars, hcol_sp⟩

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

theorem advance_offset_of_eq (s1 s2 : ScannerState)
    (h_input : s1.input = s2.input) (h_offset : s1.offset = s2.offset)
    (h_inputEnd : s1.inputEnd = s2.inputEnd) :
    s1.advance.offset = s2.advance.offset := by
  have h1 := advance_offset_eq s1
  have h2 := advance_offset_eq s2
  by_cases h : s1.offset < s1.inputEnd
  · rw [h1 h, h2 (by rw [← h_offset, ← h_inputEnd]; exact h), h_input, h_offset]
  · have h1' : s1.advance.offset = s1.offset := by
      unfold ScannerState.advance; simp [show ¬(s1.offset < s1.inputEnd) from h]
    have h2' : s2.advance.offset = s2.offset := by
      unfold ScannerState.advance; simp [show ¬(s2.offset < s2.inputEnd) from by rw [← h_offset, ← h_inputEnd]; exact h]
    rw [h1', h2', h_offset]

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

theorem advance_indents (s : ScannerState) : s.advance.indents = s.indents := by
  unfold ScannerState.advance; split
  · dsimp only []; split
    · rfl
    · split <;> rfl
  · rfl

theorem advance_inFlow (s : ScannerState) : s.advance.inFlow = s.inFlow := by
  unfold ScannerState.advance; split
  · dsimp only []; split
    · rfl
    · split <;> rfl
  · rfl

theorem advance_flowLevel (s : ScannerState) : s.advance.flowLevel = s.flowLevel := by
  unfold ScannerState.advance; split
  · dsimp only []; split
    · rfl
    · split <;> rfl
  · rfl

theorem advance_dp (s : ScannerState) : s.advance.directivesPresent = s.directivesPresent := by
  unfold ScannerState.advance; split
  · dsimp only []; split
    · rfl
    · split <;> rfl
  · rfl

theorem advance_explicitKeyLine (s : ScannerState) :
    s.advance.explicitKeyLine = s.explicitKeyLine := by
  unfold ScannerState.advance; split
  · dsimp only []; split
    · rfl
    · split <;> rfl
  · rfl

/-- Advance past a non-newline, non-CR character preserves line number. -/
theorem advance_line_non_newline (s : ScannerState) (h : s.offset < s.inputEnd)
    (hnl : ¬ (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = true)
    (hcr : ¬ (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\r') = true) :
    s.advance.line = s.line := by
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
    exact {
      chars_from := by rw [advance_input, advance_offset_eq sc hmore]; exact hrest
      col_eq := (advance_col_non_newline sc hmore hnl_bool hcr_bool).symm
      end_eq := by rw [advance_inputEnd, advance_input]; exact hcorr.end_eq
      input_prefix := by
        obtain ⟨pre, hsplit, hoff⟩ := hcorr.input_prefix
        exact ⟨pre ++ [c], by rw [advance_input, hsplit, List.append_assoc]; rfl,
               by rw [advance_offset_eq sc hmore, next_byteIdx, hc,
                      listByteSize_append]; simp [listByteSize]; omega⟩
      indent_cols_nonneg := fun i hi h0 => by
        simp only [advance_indents] at hi ⊢; exact hcorr.indent_cols_nonneg i hi h0
    }

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
    exact {
      chars_from := by rw [advance_input, advance_offset_eq sc hmore]; exact hrest
      col_eq := (advance_col_newline sc hmore hyes).symm
      end_eq := by rw [advance_inputEnd, advance_input]; exact hcorr.end_eq
      input_prefix := by
        obtain ⟨pre, hsplit, hoff⟩ := hcorr.input_prefix
        exact ⟨pre ++ ['\n'], by rw [advance_input, hsplit, List.append_assoc]; rfl,
               by rw [advance_offset_eq sc hmore, next_byteIdx, hc,
                      listByteSize_append]; simp [listByteSize]; omega⟩
      indent_cols_nonneg := fun i hi h0 => by
        simp only [advance_indents] at hi ⊢; exact hcorr.indent_cols_nonneg i hi h0
    }

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
    exact {
      chars_from := by rw [advance_input, advance_offset_eq sc hmore]; exact hrest
      col_eq := (advance_col_cr sc hmore hcr).symm
      end_eq := by rw [advance_inputEnd, advance_input]; exact hcorr.end_eq
      input_prefix := by
        obtain ⟨pre, hsplit, hoff⟩ := hcorr.input_prefix
        exact ⟨pre ++ ['\r'], by rw [advance_input, hsplit, List.append_assoc]; rfl,
               by rw [advance_offset_eq sc hmore, next_byteIdx, hc,
                      listByteSize_append]; simp [listByteSize]; omega⟩
      indent_cols_nonneg := fun i hi h0 => by
        simp only [advance_indents] at hi ⊢; exact hcorr.indent_cols_nonneg i hi h0
    }

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
  | .cons _ _ _ _ hc hrest =>
    exact {
      chars_from := hrest
      col_eq := hcorr.col_eq
      end_eq := hcorr.end_eq
      input_prefix := by
        obtain ⟨pre, hsplit, hoff⟩ := hcorr.input_prefix
        exact ⟨pre ++ [c], by rw [hsplit, List.append_assoc]; rfl,
               by rw [next_byteIdx, hc,
                      listByteSize_append]; simp [listByteSize]; omega⟩
      indent_cols_nonneg := hcorr.indent_cols_nonneg
    }

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

/-- Start-of-line gives `SSeparateInLine` (zero-width, any column). -/
theorem start_of_line_gives_SSeparateInLine (rest : List Char) :
    SSeparateInLine ⟨rest, 0⟩ ⟨rest, 0⟩ :=
  SSeparateInLine.startOfLine ⟨rest, 0⟩

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

/-- Non-emptiness evidence `s ≠ s'` lifts `GStar` to `GPlus`. -/
theorem GStar_to_GPlus {P : SurfPos → SurfPos → Prop} {s s' : SurfPos}
    (h : GStar P s s') (hne : s ≠ s') : GPlus P s s' := by
  match h with
  | .nil _ => exact absurd rfl hne
  | .cons _ sp_mid _ h_head h_tail => exact GPlus.mk _ sp_mid _ h_head h_tail

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
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩

/-- Updating `needIndentCheck` preserves correspondence. -/
theorem corr_of_needIndentCheck_update {sc : ScannerState} {sp : SurfPos}
    (b : Bool) (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr { sc with needIndentCheck := b } sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩

/-- Updating `simpleKeyAllowed` preserves correspondence. -/
theorem corr_of_simpleKeyAllowed_update {sc : ScannerState} {sp : SurfPos}
    (b : Bool) (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr { sc with simpleKeyAllowed := b } sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩

/-! ## §10 PeekBack Reasoning -/

theorem listByteSize_pos_of_ne_nil {l : List Char} (h : l ≠ []) :
    listByteSize l > 0 := by
  match l with
  | [] => exact absurd rfl h
  | c :: cs => simp [listByteSize]; have := Char.utf8Size_pos c; omega

theorem listByteSize_dropLast_add_getLast (l : List Char) (h : l ≠ []) :
    listByteSize l.dropLast + (l.getLast h).utf8Size = listByteSize l := by
  induction l with
  | nil => exact absurd rfl h
  | cons c cs ih =>
    cases cs with
    | nil => simp [List.dropLast, List.getLast, listByteSize]
    | cons d ds =>
      have hne : d :: ds ≠ [] := List.cons_ne_nil d ds
      have h_ih := ih hne
      have h_getLast : (c :: d :: ds).getLast h = (d :: ds).getLast hne := by
        rfl
      have h_dropLast : (c :: d :: ds).dropLast = c :: (d :: ds).dropLast := by
        rfl
      rw [h_getLast, h_dropLast]
      simp only [listByteSize]
      have h2 : listByteSize (d :: ds) = d.utf8Size + listByteSize ds := rfl
      rw [h2] at h_ih
      omega

/-- `peekBack?` returns the last character of the input prefix.
    When the scanner offset is positive, `prev` lands at the start of the
    last character before the current position, and `get` recovers it. -/
theorem peekBack_eq_last_prefix {sc : ScannerState} {sp : SurfPos}
    {pre : List Char}
    (hsplit : sc.input.toList = pre ++ sp.chars)
    (hoff : listByteSize pre = sc.offset)
    (hne : pre ≠ []) :
    sc.peekBack? = some (pre.getLast hne) := by
  have hpos : sc.offset > 0 := by
    rw [← hoff]; exact listByteSize_pos_of_ne_nil hne
  have hdrop : pre = pre.dropLast ++ [pre.getLast hne] :=
    (List.dropLast_concat_getLast hne).symm
  have h_split2 : sc.input.toList = pre.dropLast ++ (pre.getLast hne :: sp.chars) := by
    rw [hsplit, show pre.getLast hne :: sp.chars = [pre.getLast hne] ++ sp.chars from rfl,
        ← List.append_assoc, List.dropLast_concat_getLast hne]
  have h_prev : String.Pos.Raw.prev sc.input ⟨sc.offset⟩ =
      ⟨listByteSize pre.dropLast⟩ := by
    rw [← hoff]
    have h_bs : listByteSize pre = listByteSize pre.dropLast + (pre.getLast hne).utf8Size := by
      have := listByteSize_dropLast_add_getLast pre hne; omega
    show String.Pos.Raw.utf8PrevAux sc.input.toList 0 ⟨listByteSize pre⟩ =
      ⟨listByteSize pre.dropLast⟩
    rw [h_split2, h_bs]
    have h := utf8PrevAux_at_boundary pre.dropLast (pre.getLast hne) sp.chars 0
    simp at h; exact h
  have h_get : String.Pos.Raw.get sc.input ⟨listByteSize pre.dropLast⟩ = pre.getLast hne := by
    show String.Pos.Raw.utf8GetAux sc.input.toList 0 ⟨listByteSize pre.dropLast⟩ = _
    rw [h_split2]
    have := utf8GetAux_at_boundary pre.dropLast (pre.getLast hne) sp.chars (0 : String.Pos.Raw)
    simp at this; exact this
  unfold ScannerState.peekBack?
  simp only [hpos, ↓reduceIte, h_prev, h_get]

/-! ## §11 PeekBack After Advance -/

/-- Predicate: character is not whitespace, not line-break, not BOM. -/
def notWsLbBom (c : Char) : Prop :=
  isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ (c == '\uFEFF') = false

/-- After `advance` past a non-newline character `c`, `peekBack?` returns `c`. -/
theorem advance_peekBack_eq_peek {sc : ScannerState} {c : Char} {rest : List Char}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, sc.col⟩)
    (hmore : sc.offset < sc.inputEnd)
    (hnl : c ≠ '\n') (hcr : c ≠ '\r') :
    sc.advance.peekBack? = some c := by
  have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
  obtain ⟨pre_adv, hsplit_adv, hoff_adv⟩ := hcorr_adv.input_prefix
  obtain ⟨pre, hsplit, hoff⟩ := hcorr.input_prefix
  have h_pre_adv : pre_adv = pre ++ [c] := by
    have h_rhs : sc.advance.input.toList = (pre ++ [c]) ++ rest := by
      rw [advance_input, hsplit, List.append_assoc]; rfl
    exact List.append_cancel_right (hsplit_adv.symm.trans h_rhs)
  subst h_pre_adv
  have h_ne : pre ++ [c] ≠ [] := by simp
  have h := peekBack_eq_last_prefix hsplit_adv hoff_adv h_ne
  suffices (pre ++ [c]).getLast h_ne = c by rw [this] at h; exact h
  simp

/-! ## §12 SkipWhitespace Input Preservation -/

theorem skipWhitespaceLoop_input (sc : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop sc fuel).input = sc.input := by
  induction fuel generalizing sc with
  | zero => simp [skipWhitespaceLoop]
  | succ n ih =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [ih, advance_input]
      · rfl
    · rfl

theorem skipWhitespace_input (sc : ScannerState) :
    (skipWhitespace sc).input = sc.input := by
  unfold skipWhitespace; exact skipWhitespaceLoop_input sc _

/-! ## §13 Offset Uniqueness from SurfPos -/

theorem ScannerSurfCorr_same_offset {sc1 sc2 : ScannerState} {sp : SurfPos}
    (h1 : ScannerSurfCorr sc1 sp) (h2 : ScannerSurfCorr sc2 sp)
    (h_input : sc1.input = sc2.input) :
    sc1.offset = sc2.offset := by
  obtain ⟨pre1, hsplit1, hoff1⟩ := h1.input_prefix
  obtain ⟨pre2, hsplit2, hoff2⟩ := h2.input_prefix
  rw [← hoff1, ← hoff2,
    show pre1 = pre2 from List.append_cancel_right
      ((show sc2.input.toList = pre1 ++ sp.chars from by rw [← h_input]; exact hsplit1).symm.trans hsplit2)]

/-! ## §14 GStar Column Monotonicity -/

theorem gstar_gchar_col_le {p : Char → Prop} {s1 s2 : SurfPos}
    (h : GStar (GChar p) s1 s2) : s2.col ≥ s1.col := by
  induction h with
  | nil => omega
  | cons _ _ _ hfirst _ ih =>
    cases hfirst with | mk c rest col _ => exact Nat.le_trans (Nat.le_succ col) ih

end Lean4Yaml.Proofs.CouplingBridge
