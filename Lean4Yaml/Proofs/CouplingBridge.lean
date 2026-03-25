/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Surface
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

/-! ## §2 State Correspondence -/

/-- Scanner state and surface position correspond when the remaining
    characters match and columns agree. -/
structure ScannerSurfCorr (sc : ScannerState) (sp : SurfPos) : Prop where
  chars_from : CharsFromOffset sc.input sc.offset sp.chars
  col_eq : sp.col = sc.col
  end_eq : sc.inputEnd = sc.input.utf8ByteSize

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
  · dsimp only []; split <;> rfl
  · rfl

theorem advance_inputEnd (s : ScannerState) : s.advance.inputEnd = s.inputEnd := by
  unfold ScannerState.advance; split
  · dsimp only []; split <;> rfl
  · rfl

theorem advance_offset_eq (s : ScannerState) (h : s.offset < s.inputEnd) :
    s.advance.offset = (String.Pos.Raw.next s.input ⟨s.offset⟩).byteIdx := by
  unfold ScannerState.advance; split
  · dsimp only []; split <;> rfl
  · omega

theorem advance_col_non_newline (s : ScannerState) (h : s.offset < s.inputEnd)
    (hnl : ¬ (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = true) :
    s.advance.col = s.col + 1 := by
  unfold ScannerState.advance; split
  · dsimp only []; simp [hnl]
  · omega

theorem advance_col_newline (s : ScannerState) (h : s.offset < s.inputEnd)
    (hyes : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = true) :
    s.advance.col = 0 := by
  unfold ScannerState.advance; split
  · dsimp only []; simp [hyes]
  · omega

/-- Advance past non-newline preserves correspondence. -/
theorem advance_non_newline_corr (sc : ScannerState) (c : Char) (rest : List Char)
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, sc.col⟩)
    (hmore : sc.offset < sc.inputEnd)
    (hnl : c ≠ '\n') :
    ScannerSurfCorr sc.advance ⟨rest, sc.col + 1⟩ := by
  have hcf := hcorr.chars_from
  match hcf with
  | .cons _ hlt _ _ hc hrest =>
    have hnl_bool : ¬ (String.Pos.Raw.get sc.input ⟨sc.offset⟩ == '\n') = true := by
      rw [hc]; simp [hnl]
    constructor
    · rw [advance_input, advance_offset_eq sc hmore]; exact hrest
    · exact (advance_col_non_newline sc hmore hnl_bool).symm
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

/-! ## §5 Production Coupling (Scanner → Surface) -/

/-- `n` consecutive spaces give `SIndent n`. -/
theorem skipSpaces_gives_SIndent (n : Nat) (sp : SurfPos)
    (hpre : sp.chars.take n = List.replicate n ' ')
    (hlen : sp.chars.length ≥ n) :
    SIndent n sp ⟨sp.chars.drop n, sp.col + n⟩ :=
  indent_coupling n sp.chars sp.col hpre hlen

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

end Lean4Yaml.Proofs.CouplingBridge
