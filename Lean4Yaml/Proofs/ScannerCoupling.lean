/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Proofs.CouplingBridge
import Lean4Yaml.Proofs.SurfaceCoupling

/-!
# Scanner Loop Coupling

Coupling theorems for scanner loops, connecting fuel-based recursion
(`skipSpaces`, `consumeNewline`) to surface syntax predicates
(`SIndent`, `SBBreak`).

## Strategy

Each loop coupling theorem shows:
1. The loop preserves `ScannerSurfCorr`
2. The consumed characters form the appropriate surface syntax production
3. The fuel parameter ensures termination but does not affect correctness

## Sections

1. **Helpers**: peek-to-chars, fuel budget, advance correspondence shortcuts
2. **skipSpacesLoop**: spaces consumed → `SIndent n`
3. **consumeNewline**: line break consumed → `SBBreak`
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.ScannerCoupling

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.SurfaceCoupling

/-! ## §1 Helpers -/

/-- If `peek?` returns `some c`, then `offset < inputEnd`. -/
theorem peek_some_hasMore (sc : ScannerState) (c : Char)
    (h : sc.peek? = some c) : sc.offset < sc.inputEnd := by
  unfold ScannerState.peek? at h; split at h
  · assumption
  · contradiction

/-- If `peek?` returns `some c` and correspondence holds,
    the surface chars start with `c`. -/
theorem peek_some_chars (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some c) :
    ∃ rest, sp.chars = c :: rest := by
  have hmore := peek_some_hasMore sc c hpeek
  obtain ⟨c', rest, hchars, hpeek'⟩ := peek_corr sc sp hcorr hmore
  have hceq : c = c' := Option.some.inj (hpeek ▸ hpeek')
  subst hceq; exact ⟨rest, hchars⟩

/-- `Raw.next` strictly increases the byte offset. -/
theorem raw_next_gt (s : String) (p : Nat) :
    (String.Pos.Raw.next s ⟨p⟩).byteIdx > p :=
  String.Pos.Raw.byteIdx_lt_byteIdx_next s ⟨p⟩

/-- After advance, the fuel budget decreases: if `fuel + 1 ≥ inputEnd - offset`,
    then `fuel ≥ inputEnd - advance.offset`. -/
theorem advance_fuel_budget (sc : ScannerState) (fuel : Nat)
    (hmore : sc.offset < sc.inputEnd)
    (hfuel : fuel + 1 ≥ sc.inputEnd - sc.offset) :
    fuel ≥ sc.advance.inputEnd - sc.advance.offset := by
  rw [advance_inputEnd]
  have hgt := raw_next_gt sc.input sc.offset
  have hoff := advance_offset_eq sc hmore
  omega

/-! ## §2 skipSpacesLoop Coupling -/

/-- `skipSpacesLoop` consumes leading spaces and preserves correspondence.
    Returns the number of spaces consumed `n`, a surface proof `SIndent n`,
    and updated correspondence for the post-skip state. -/
theorem skipSpacesLoop_corr (sc : ScannerState) (sp : SurfPos) (fuel : Nat)
    (hcorr : ScannerSurfCorr sc sp)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset) :
    ∃ (n : Nat) (sp' : SurfPos),
      SIndent n sp sp' ∧ ScannerSurfCorr (skipSpacesLoop sc fuel) sp' := by
  induction fuel generalizing sc sp with
  | zero =>
    simp [skipSpacesLoop]
    exact ⟨0, sp, SIndent.zero sp, hcorr⟩
  | succ fuel' ih =>
    unfold skipSpacesLoop
    split
    · -- sc.peek? matches some ' '
      rename_i hpeek
      have hmore := peek_some_hasMore sc ' ' hpeek
      obtain ⟨rest, hchars⟩ := peek_some_chars sc sp ' ' hcorr hpeek
      -- Establish sp = ⟨' ' :: rest, sc.col⟩
      have hcol := hcorr.col_eq
      have hsp_eq : sp = ⟨' ' :: rest, sc.col⟩ := by
        cases sp with | mk cs cl =>
        simp only [] at hchars hcol
        subst hchars; subst hcol; rfl
      subst hsp_eq
      have hadv := advance_non_newline_corr sc ' ' rest hcorr hmore (by decide) (by decide)
      have hfuel' := advance_fuel_budget sc fuel' hmore hfuel
      obtain ⟨n, sp', hindent, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ hadv hfuel'
      exact ⟨n + 1, sp', SIndent.succ n rest sc.col sp' hindent, hcorr'⟩
    · -- peek ≠ some ' ' (other char or none)
      exact ⟨0, sp, SIndent.zero sp, hcorr⟩

/-- Top-level coupling for `skipSpaces`: wraps the loop version. -/
theorem skipSpaces_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ (n : Nat) (sp' : SurfPos),
      SIndent n sp sp' ∧ ScannerSurfCorr (skipSpaces sc) sp' := by
  unfold skipSpaces
  exact skipSpacesLoop_corr sc sp _ hcorr (Nat.le_refl _)

/-! ## §3 consumeNewline Coupling -/

/-- `consumeNewline` when peeking `\n` consumes it and produces `SBBreak`. -/
theorem consumeNewline_lf_corr (sc : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr sc ⟨'\n' :: rest, sc.col⟩)
    (hpeek : sc.peek? = some '\n') :
    SBBreak ⟨'\n' :: rest, sc.col⟩ ⟨rest, 0⟩ ∧
    ∃ sc', sc' = { (sc.advance : ScannerState) with needIndentCheck := true } ∧
    ScannerSurfCorr sc' ⟨rest, 0⟩ := by
  have hmore := peek_some_hasMore sc '\n' hpeek
  have hadv := advance_newline_corr sc rest hcorr hmore
  constructor
  · exact SBBreak.lf rest sc.col
  · -- The advance correspondence gives us ScannerSurfCorr sc.advance ⟨rest, 0⟩
    -- Setting needIndentCheck doesn't affect chars/col/offset/input/inputEnd
    refine ⟨_, rfl, ?_⟩
    constructor
    · exact hadv.chars_from
    · exact hadv.col_eq
    · exact hadv.end_eq
    · exact hadv.input_prefix

/-- `consumeNewline` when peeking `\r` followed by `\n` (CRLF). -/
theorem consumeNewline_crlf_corr (sc : ScannerState) (rest : List Char)
    (_hcorr : ScannerSurfCorr sc ⟨'\r' :: '\n' :: rest, sc.col⟩)
    (_hpeek_cr : sc.peek? = some '\r')
    (_hpeek_lf : sc.advance.peek? = some '\n') :
    SBBreak ⟨'\r' :: '\n' :: rest, sc.col⟩ ⟨rest, 0⟩ := by
  exact SBBreak.crLf rest sc.col

/-- `consumeNewline` when peeking lone `\r` (no following `\n`). -/
theorem consumeNewline_cr_corr (sc : ScannerState) (rest : List Char)
    (_hcorr : ScannerSurfCorr sc ⟨'\r' :: rest, sc.col⟩)
    (_hpeek : sc.peek? = some '\r') :
    SBBreak ⟨'\r' :: rest, sc.col⟩ ⟨rest, 0⟩ := by
  exact SBBreak.cr rest sc.col

/-- Unified `consumeNewline` correspondence: if a line break character is
    peeked, `consumeNewline` advances to a state with some valid surface
    correspondence.  Dispatches on `'\n'`, CRLF, and lone `'\r'`. -/
theorem consumeNewline_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true) :
    ∃ sp', ScannerSurfCorr (consumeNewline sc) sp' := by
  have hmore := peek_some_hasMore sc c hpeek
  obtain ⟨rest, hchars⟩ := peek_some_chars sc sp c hcorr hpeek
  have hcol := hcorr.col_eq
  have hsp_eq : sp = ⟨c :: rest, sc.col⟩ := by
    cases sp with | mk cs cl => simp only [] at hchars hcol; subst hchars; subst hcol; rfl
  subst hsp_eq
  simp [isLineBreakBool, Bool.or_eq_true, beq_iff_eq] at hlb
  unfold consumeNewline
  rcases hlb with rfl | rfl
  · -- c = '\n': returns { sc.advance with needIndentCheck := true }
    simp only [hpeek]
    exact ⟨⟨rest, 0⟩, corr_of_needIndentCheck_update true
      (advance_newline_corr sc rest hcorr hmore)⟩
  · -- c = '\r': dispatch on next character
    simp only [hpeek]
    have hadv := advance_cr_corr sc rest hcorr hmore
    split
    · -- sc.advance.peek? = some '\n' (CRLF): raw offset skip
      rename_i hpeek2
      have hmore2 := peek_some_hasMore sc.advance '\n' hpeek2
      obtain ⟨rest2, hchars2⟩ := peek_some_chars sc.advance ⟨rest, 0⟩ '\n' hadv hpeek2
      subst hchars2
      have hskip := skip_byte_corr sc.advance '\n' rest2 0 hadv hmore2
      exact ⟨⟨rest2, 0⟩, corr_of_needIndentCheck_update true hskip⟩
    · -- lone '\r' (or end of input): returns { sc.advance with needIndentCheck := true }
      exact ⟨⟨rest, 0⟩, corr_of_needIndentCheck_update true hadv⟩

/-! ## §4 skipWhitespaceLoop Coupling -/

/-- `skipWhitespaceLoop` consumes leading whitespace (spaces + tabs) and
    preserves correspondence.  Returns a surface proof `GStar SSWhite`
    and updated correspondence for the post-skip state. -/
theorem skipWhitespaceLoop_corr (sc : ScannerState) (sp : SurfPos) (fuel : Nat)
    (hcorr : ScannerSurfCorr sc sp)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset) :
    ∃ sp', GStar SSWhite sp sp' ∧ ScannerSurfCorr (skipWhitespaceLoop sc fuel) sp' := by
  induction fuel generalizing sc sp with
  | zero =>
    simp [skipWhitespaceLoop]
    exact ⟨sp, GStar.nil sp, hcorr⟩
  | succ fuel' ih =>
    unfold skipWhitespaceLoop
    split
    · -- peek? = some c
      rename_i c hpeek
      split
      · -- isWhiteSpaceBool c = true
        rename_i hws
        have hmore := peek_some_hasMore sc c hpeek
        obtain ⟨rest, hchars⟩ := peek_some_chars sc sp c hcorr hpeek
        have hcol := hcorr.col_eq
        have hsp_eq : sp = ⟨c :: rest, sc.col⟩ := by
          cases sp with | mk cs cl =>
          simp only [] at hchars hcol
          subst hchars; subst hcol; rfl
        subst hsp_eq
        have hnl := isWhiteSpace_not_newline c hws
        have hcr := isWhiteSpace_not_cr c hws
        have hadv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
        have hfuel' := advance_fuel_budget sc fuel' hmore hfuel
        obtain ⟨sp', hstar, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ hadv hfuel'
        exact ⟨sp', GStar.cons _ _ _ (isWhiteSpace_gives_SSWhite c rest sc.col hws) hstar, hcorr'⟩
      · -- isWhiteSpaceBool c ≠ true
        exact ⟨sp, GStar.nil sp, hcorr⟩
    · -- peek? = none
      exact ⟨sp, GStar.nil sp, hcorr⟩

/-- Top-level coupling for `skipWhitespace`: wraps the loop version. -/
theorem skipWhitespace_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', GStar SSWhite sp sp' ∧ ScannerSurfCorr (skipWhitespace sc) sp' := by
  unfold skipWhitespace
  exact skipWhitespaceLoop_corr sc sp _ hcorr (Nat.le_refl _)

/-! ## §5 skipToEndOfLineLoop Coupling -/

/-- `skipToEndOfLineLoop` consumes non-break characters and preserves
    correspondence.  Returns `GStar SNbChar` (= `GStar (GChar isNbChar)`). -/
theorem skipToEndOfLineLoop_corr (sc : ScannerState) (sp : SurfPos) (fuel : Nat)
    (hcorr : ScannerSurfCorr sc sp)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset) :
    ∃ sp', GStar SNbChar sp sp' ∧ ScannerSurfCorr (skipToEndOfLineLoop sc fuel) sp' := by
  induction fuel generalizing sc sp with
  | zero =>
    simp [skipToEndOfLineLoop]
    exact ⟨sp, GStar.nil sp, hcorr⟩
  | succ fuel' ih =>
    unfold skipToEndOfLineLoop
    split
    · -- peek? = some c
      rename_i c hpeek
      split
      · -- isLineBreakBool c = true (stop)
        exact ⟨sp, GStar.nil sp, hcorr⟩
      · -- ¬isLineBreakBool c (advance and recurse)
        rename_i hnlb
        have hmore := peek_some_hasMore sc c hpeek
        obtain ⟨rest, hchars⟩ := peek_some_chars sc sp c hcorr hpeek
        have hcol := hcorr.col_eq
        have hsp_eq : sp = ⟨c :: rest, sc.col⟩ := by
          cases sp with | mk cs cl =>
          simp only [] at hchars hcol
          subst hchars; subst hcol; rfl
        subst hsp_eq
        have hnl := not_isLineBreak_not_newline c hnlb
        have hcr := not_isLineBreak_not_cr c hnlb
        have hadv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
        have hfuel' := advance_fuel_budget sc fuel' hmore hfuel
        obtain ⟨sp', hstar, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ hadv hfuel'
        exact ⟨sp', GStar.cons _ _ _ (not_isLineBreak_gives_SNbChar c rest sc.col hnlb) hstar, hcorr'⟩
    · -- peek? = none
      exact ⟨sp, GStar.nil sp, hcorr⟩

/-- Top-level coupling for `skipToEndOfLine`. -/
theorem skipToEndOfLine_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', GStar SNbChar sp sp' ∧ ScannerSurfCorr (skipToEndOfLine sc) sp' := by
  unfold skipToEndOfLine
  exact skipToEndOfLineLoop_corr sc sp _ hcorr (Nat.le_refl _)

/-! ## §6 collectCommentTextLoop Coupling -/

/-- `collectCommentTextLoop` consumes non-break characters (the comment
    body after `#`) and preserves correspondence.  The accumulated text
    string is irrelevant for surface syntax coupling. -/
theorem collectCommentTextLoop_corr (sc : ScannerState) (sp : SurfPos)
    (text : String) (fuel : Nat)
    (hcorr : ScannerSurfCorr sc sp)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset) :
    ∃ sp', GStar SNbChar sp sp' ∧
           ScannerSurfCorr (collectCommentTextLoop sc text fuel).2 sp' := by
  induction fuel generalizing sc sp text with
  | zero =>
    simp [collectCommentTextLoop]
    exact ⟨sp, GStar.nil sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectCommentTextLoop
    split
    · -- peek? = some c
      rename_i c hpeek
      split
      · -- isLineBreakBool c = true (stop)
        exact ⟨sp, GStar.nil sp, hcorr⟩
      · -- ¬isLineBreakBool c (advance and recurse)
        rename_i hnlb
        have hmore := peek_some_hasMore sc c hpeek
        obtain ⟨rest, hchars⟩ := peek_some_chars sc sp c hcorr hpeek
        have hcol := hcorr.col_eq
        have hsp_eq : sp = ⟨c :: rest, sc.col⟩ := by
          cases sp with | mk cs cl =>
          simp only [] at hchars hcol
          subst hchars; subst hcol; rfl
        subst hsp_eq
        have hnl := not_isLineBreak_not_newline c hnlb
        have hcr := not_isLineBreak_not_cr c hnlb
        have hadv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
        have hfuel' := advance_fuel_budget sc fuel' hmore hfuel
        obtain ⟨sp', hstar, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ (text.push c) hadv hfuel'
        exact ⟨sp', GStar.cons _ _ _ (not_isLineBreak_gives_SNbChar c rest sc.col hnlb) hstar, hcorr'⟩
    · -- peek? = none
      exact ⟨sp, GStar.nil sp, hcorr⟩

/-! ## §7 skipToContentComment Coupling -/

/-- `skipToContentComment` optionally consumes a `#`-comment and preserves
    correspondence.  When `#` is matched and the comment is valid, produces
    `SCNbCommentText`; otherwise identity (`GOpt.none`).

    The `comments` field update does not affect correspondence since it
    does not change `input`/`offset`/`col`/`inputEnd`. -/
theorem skipToContentComment_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', GOpt SCNbCommentText sp sp' ∧
           ScannerSurfCorr (skipToContentComment sc) sp' := by
  unfold skipToContentComment
  -- Inline let bindings so split targets matches/ifs cleanly
  dsimp only []
  -- First split: match sc.peek? with | some '#' => ... | _ => sc
  split
  · -- peek? = some '#'
    rename_i hpeek
    -- split targets match sc.peekBack? inside the commentOk condition
    split
    · -- peekBack? = some c
      rename_i c
      -- split targets if commentOk
      split
      · -- commentOk = true: process comment
        have hmore := peek_some_hasMore sc '#' hpeek
        obtain ⟨rest, hchars⟩ := peek_some_chars sc sp '#' hcorr hpeek
        have hcol := hcorr.col_eq
        have hsp_eq : sp = ⟨'#' :: rest, sc.col⟩ := by
          cases sp with | mk cs cl =>
          simp only [] at hchars hcol
          subst hchars; subst hcol; rfl
        subst hsp_eq
        have hadv := advance_non_newline_corr sc '#' rest hcorr hmore (by decide) (by decide)
        have hfuel : sc.advance.inputEnd - sc.advance.offset ≥
                     sc.advance.inputEnd - sc.advance.offset := Nat.le_refl _
        obtain ⟨sp', hstar, hcorr'⟩ :=
          collectCommentTextLoop_corr sc.advance ⟨rest, sc.col + 1⟩ "" _ hadv hfuel
        exact ⟨sp', GOpt.some _ _ (SCNbCommentText.mk rest sc.col sp' hstar),
               corr_of_comments_update _ hcorr'⟩
      · -- commentOk = false: identity
        exact ⟨sp, GOpt.none sp, hcorr⟩
    · -- peekBack? = none
      -- commentOk = sc.col == 0 || true, so split on if
      split
      · -- commentOk = true: process comment (same as above)
        have hmore := peek_some_hasMore sc '#' hpeek
        obtain ⟨rest, hchars⟩ := peek_some_chars sc sp '#' hcorr hpeek
        have hcol := hcorr.col_eq
        have hsp_eq : sp = ⟨'#' :: rest, sc.col⟩ := by
          cases sp with | mk cs cl =>
          simp only [] at hchars hcol
          subst hchars; subst hcol; rfl
        subst hsp_eq
        have hadv := advance_non_newline_corr sc '#' rest hcorr hmore (by decide) (by decide)
        have hfuel : sc.advance.inputEnd - sc.advance.offset ≥
                     sc.advance.inputEnd - sc.advance.offset := Nat.le_refl _
        obtain ⟨sp', hstar, hcorr'⟩ :=
          collectCommentTextLoop_corr sc.advance ⟨rest, sc.col + 1⟩ "" _ hadv hfuel
        exact ⟨sp', GOpt.some _ _ (SCNbCommentText.mk rest sc.col sp' hstar),
               corr_of_comments_update _ hcorr'⟩
      · -- commentOk = false: impossible (condition is _ || true)
        rename_i h; exfalso; simp [Bool.or_true] at h
  · -- peek? ≠ some '#'
    exact ⟨sp, GOpt.none sp, hcorr⟩

/-! ## §8 skipToContentWs Coupling

The whitespace phase (`skipToContentWs`) handles indentation checking and
tab-as-indentation validation.  When it returns `.ok`, the scanner state
preserves correspondence and the consumed characters form valid whitespace
(indentation spaces + optional separation whitespace). -/

/-- `skipToContentWs` preserves correspondence on `.ok` paths.

    On every `.ok s'` return, the scanner state `s'` has a corresponding
    surface position `sp'` that is reachable from `sp` via indentation
    spaces (`SIndent`) and/or whitespace (`GStar SSWhite`). -/
theorem skipToContentWs_ok_corr (sc : ScannerState) (sp : SurfPos) (s' : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : skipToContentWs sc = .ok s') :
    ∃ sp', GStar SSWhite sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold skipToContentWs at hok
  -- Zeta-reduce all let bindings (s1, probe, etc.) so split can see the if/match
  dsimp only [] at hok
  split at hok
  · -- needIndentCheck = true
    obtain ⟨n, sp_spaces, hindent, hcorr_spaces⟩ := skipSpaces_corr sc sp hcorr
    have hstar_indent := SIndent_gives_GStar_SSWhite hindent
    split at hok
    · -- in indentation zone
      split at hok
      · -- peek? of skipSpaces sc = some '\t'
        obtain ⟨sp_ws, hstar_ws, hcorr_ws⟩ := skipWhitespace_corr _ sp_spaces hcorr_spaces
        split at hok
        · -- probe.peek? = some '#'
          have hinj := Except.ok.inj hok; subst hinj
          exact ⟨sp_ws, GStar_trans hstar_indent hstar_ws, hcorr_ws⟩
        · -- probe.peek? = some c (not '#')
          split at hok
          · -- isLineBreakBool c = true
            have hinj := Except.ok.inj hok; subst hinj
            exact ⟨sp_ws, GStar_trans hstar_indent hstar_ws, hcorr_ws⟩
          · -- not line break
            split at hok
            · -- flow indicator exception
              have hinj := Except.ok.inj hok; subst hinj
              exact ⟨sp_ws, GStar_trans hstar_indent hstar_ws, hcorr_ws⟩
            · -- error: tab in indentation
              exact absurd hok (by simp)
        · -- probe.peek? = none
          have hinj := Except.ok.inj hok; subst hinj
          exact ⟨sp_ws, GStar_trans hstar_indent hstar_ws, hcorr_ws⟩
      · -- peek? of skipSpaces sc ≠ some '\t'
        have hinj := Except.ok.inj hok; subst hinj
        exact ⟨sp_spaces, hstar_indent, hcorr_spaces⟩
    · -- past indentation boundary: skip whitespace
      have hinj := Except.ok.inj hok; subst hinj
      obtain ⟨sp_ws, hstar_ws, hcorr_ws⟩ := skipWhitespace_corr _ sp_spaces hcorr_spaces
      exact ⟨sp_ws, GStar_trans hstar_indent hstar_ws, hcorr_ws⟩
  · -- needIndentCheck = false
    have hinj := Except.ok.inj hok; subst hinj
    exact skipWhitespace_corr sc sp hcorr

/-! ## §9 skipToContentLoop Coupling

The main content-skipping loop composes whitespace, comments, and line
breaks.  When it returns `.ok`, the scanner state has a corresponding
surface position. -/

/-- Monotonicity: `skipSpacesLoop` does not decrease the offset. -/
theorem skipSpacesLoop_offset_mono (sc : ScannerState) (fuel : Nat) :
    (skipSpacesLoop sc fuel).offset ≥ sc.offset ∧
    (skipSpacesLoop sc fuel).inputEnd = sc.inputEnd := by
  induction fuel generalizing sc with
  | zero => simp [skipSpacesLoop]
  | succ fuel' ih =>
    unfold skipSpacesLoop
    split
    · -- peek? = some ' '
      rename_i hpeek
      have hmore := peek_some_hasMore sc ' ' hpeek
      have ⟨ih_off, ih_end⟩ := ih sc.advance
      have hadv_gt : sc.advance.offset > sc.offset := by
        rw [advance_offset_eq sc hmore]; exact raw_next_gt _ _
      exact ⟨by omega, by rw [ih_end, advance_inputEnd]⟩
    · -- not space
      exact ⟨Nat.le_refl _, rfl⟩

/-- Monotonicity: `skipWhitespaceLoop` does not decrease the offset. -/
theorem skipWhitespaceLoop_offset_mono (sc : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop sc fuel).offset ≥ sc.offset ∧
    (skipWhitespaceLoop sc fuel).inputEnd = sc.inputEnd := by
  induction fuel generalizing sc with
  | zero => simp [skipWhitespaceLoop]
  | succ fuel' ih =>
    unfold skipWhitespaceLoop
    split
    · -- peek? = some c
      rename_i c hpeek
      split
      · -- isWhiteSpaceBool c = true (recursive)
        have hmore := peek_some_hasMore sc c hpeek
        have ⟨ih_off, ih_end⟩ := ih sc.advance
        have hadv_gt : sc.advance.offset > sc.offset := by
          rw [advance_offset_eq sc hmore]; exact raw_next_gt _ _
        exact ⟨by omega, by rw [ih_end, advance_inputEnd]⟩
      · -- not whitespace
        exact ⟨Nat.le_refl _, rfl⟩
    · -- none
      exact ⟨Nat.le_refl _, rfl⟩

/-- If `skipWhitespaceLoop` doesn't change the offset, it returns the input state.
    Proof: if any whitespace was consumed, `advance` would strictly increase the
    offset, and the recursive call can only increase further (by monotonicity).
    So offset equality implies no WS was consumed → state unchanged. -/
theorem skipWhitespaceLoop_eq_of_same_offset (sc : ScannerState) (fuel : Nat)
    (heq : (skipWhitespaceLoop sc fuel).offset = sc.offset) :
    skipWhitespaceLoop sc fuel = sc := by
  induction fuel generalizing sc with
  | zero => simp [skipWhitespaceLoop]
  | succ n ih =>
    unfold skipWhitespaceLoop
    split
    · -- peek? = some c
      rename_i c hpeek
      split
      · -- isWhiteSpaceBool c = true: advance + recurse
        exfalso
        have hmore := peek_some_hasMore sc c hpeek
        have hadv_gt : sc.advance.offset > sc.offset := by
          rw [advance_offset_eq sc hmore]; exact raw_next_gt _ _
        have ⟨hmono, _⟩ := skipWhitespaceLoop_offset_mono sc.advance n
        -- heq says the result offset = sc.offset, but it's ≥ advance.offset > sc.offset
        simp only [skipWhitespaceLoop] at heq
        simp only [hpeek, ite_true, ‹isWhiteSpaceBool c = true›] at heq
        omega
      · -- not whitespace: returns sc
        rfl
    · -- peek? = none: returns sc
      rfl

/-- If the current char is not whitespace (or at EOF), `skipWhitespaceLoop` is a no-op. -/
theorem skipWhitespaceLoop_noop_of_not_ws (sc : ScannerState) (fuel : Nat)
    (h : match sc.peek? with | some c => isWhiteSpaceBool c = false | none => True) :
    skipWhitespaceLoop sc fuel = sc := by
  cases fuel with
  | zero => simp [skipWhitespaceLoop]
  | succ n =>
    unfold skipWhitespaceLoop
    split
    · rename_i c hpeek
      simp [hpeek] at h
      split
      · rename_i hws; simp [h] at hws
      · rfl
    · rfl

/-- `skipWhitespace` returns the input state when the first char is not whitespace. -/
theorem skipWhitespace_noop (sc : ScannerState)
    (h : match sc.peek? with | some c => isWhiteSpaceBool c = false | none => True) :
    skipWhitespace sc = sc := by
  unfold skipWhitespace
  exact skipWhitespaceLoop_noop_of_not_ws sc _ h

/-- Monotonicity: `collectCommentTextLoop` does not decrease the offset. -/
theorem collectCommentTextLoop_offset_mono (sc : ScannerState) (text : String) (fuel : Nat) :
    (collectCommentTextLoop sc text fuel).2.offset ≥ sc.offset ∧
    (collectCommentTextLoop sc text fuel).2.inputEnd = sc.inputEnd := by
  induction fuel generalizing sc text with
  | zero => simp [collectCommentTextLoop]
  | succ fuel' ih =>
    unfold collectCommentTextLoop
    split
    · -- peek? = some c
      rename_i c hpeek
      split
      · -- line break
        exact ⟨Nat.le_refl _, rfl⟩
      · -- not line break
        have hmore := peek_some_hasMore sc c hpeek
        have ⟨ih_off, ih_end⟩ := ih sc.advance (text.push c)
        have hadv_gt : sc.advance.offset > sc.offset := by
          rw [advance_offset_eq sc hmore]; exact raw_next_gt _ _
        exact ⟨by omega, by rw [ih_end, advance_inputEnd]⟩
    · -- none
      exact ⟨Nat.le_refl _, rfl⟩

/-- Monotonicity: `skipToContentComment` does not decrease the offset.

    This follows from the function's structure: on every path it either
    returns `sc` unchanged or returns `{ s' with comments := ... }` where
    `s' = (collectCommentTextLoop sc.advance "" fuel).2`.  In both cases
    `offset` is non-decreasing and `inputEnd` is preserved.

    The proof handles the nested `match`/`if`/`let`/struct-update through
    direct case analysis on the `commentOk` boolean. -/
theorem skipToContentComment_offset_mono (sc : ScannerState) :
    (skipToContentComment sc).offset ≥ sc.offset ∧
    (skipToContentComment sc).inputEnd = sc.inputEnd := by
  unfold skipToContentComment
  -- After unfold, `some '#'` arm has let/if/match nesting that blocks `split`.
  -- Use dsimp to inline lets, then case-split on match/if manually.
  dsimp only []
  -- First split: match sc.peek? with | some '#' => ... | _ => sc
  split
  · -- peek? = some '#'
    rename_i hpeek
    -- Now: if (sc.col == 0 || match sc.peekBack? with ...) then { struct } else sc
    -- split targets the match inside the condition first
    split
    · -- peekBack? = some c
      rename_i c
      split
      · -- commentOk = true → result is struct update
        dsimp only []
        have hmore := peek_some_hasMore sc '#' hpeek
        have ⟨h_off, h_end⟩ := collectCommentTextLoop_offset_mono sc.advance ""
                                  (sc.advance.inputEnd - sc.advance.offset)
        have hadv_gt : sc.advance.offset > sc.offset := by
          rw [advance_offset_eq sc hmore]; exact raw_next_gt _ _
        exact ⟨by omega, by rw [h_end, advance_inputEnd]⟩
      · -- commentOk = false → result is sc
        exact ⟨Nat.le_refl _, rfl⟩
    · -- peekBack? = none → commentOk = _ || true = true
      split
      · -- commentOk = true
        dsimp only []
        have hmore := peek_some_hasMore sc '#' hpeek
        have ⟨h_off, h_end⟩ := collectCommentTextLoop_offset_mono sc.advance ""
                                  (sc.advance.inputEnd - sc.advance.offset)
        have hadv_gt : sc.advance.offset > sc.offset := by
          rw [advance_offset_eq sc hmore]; exact raw_next_gt _ _
        exact ⟨by omega, by rw [h_end, advance_inputEnd]⟩
      · -- commentOk = false → impossible (condition is _ || true)
        rename_i h
        exfalso; simp [Bool.or_true] at h
  · -- not '#'
    exact ⟨Nat.le_refl _, rfl⟩

/-- `consumeNewline` advances the offset by at least 1 when a line break is peeked. -/
theorem consumeNewline_offset_advance (sc : ScannerState) (c : Char)
    (hpeek : sc.peek? = some c) (hlb : isLineBreakBool c = true) :
    (consumeNewline sc).offset > sc.offset ∧
    (consumeNewline sc).inputEnd = sc.inputEnd := by
  have hmore := peek_some_hasMore sc c hpeek
  simp [isLineBreakBool, Bool.or_eq_true, beq_iff_eq] at hlb
  unfold consumeNewline
  rcases hlb with rfl | rfl
  · -- c = '\n'
    simp [hpeek]
    constructor
    · rw [advance_offset_eq sc hmore]; exact raw_next_gt _ _
    · exact advance_inputEnd sc
  · -- c = '\r'
    simp [hpeek]
    constructor
    · have h1 : sc.advance.offset > sc.offset := by
        rw [advance_offset_eq sc hmore]; exact raw_next_gt _ _
      split
      · -- CRLF: advance + raw offset skip
        exact Nat.lt_trans h1 (raw_next_gt sc.advance.input sc.advance.offset)
      · -- lone CR: advance once
        exact h1
    · split
      · simp [advance_inputEnd]
      · exact advance_inputEnd sc

/-- Monotonicity: `skipToContentWs` does not decrease the offset on `.ok` paths. -/
theorem skipToContentWs_offset_mono (sc : ScannerState) (s' : ScannerState)
    (hok : skipToContentWs sc = .ok s') :
    s'.offset ≥ sc.offset ∧ s'.inputEnd = sc.inputEnd := by
  unfold skipToContentWs at hok
  dsimp only [] at hok
  split at hok
  · -- needIndentCheck
    have ⟨h_sp_off, h_sp_end⟩ := skipSpacesLoop_offset_mono sc (sc.inputEnd - sc.offset)
    have hskipSpaces_unfold : skipSpaces sc = skipSpacesLoop sc (sc.inputEnd - sc.offset) := by
      unfold skipSpaces; rfl
    rw [← hskipSpaces_unfold] at h_sp_off h_sp_end
    split at hok
    · -- in indentation zone
      split at hok
      · -- peek '\t'
        have ⟨h_ws_off, h_ws_end⟩ := skipWhitespaceLoop_offset_mono
              (skipSpaces sc) ((skipSpaces sc).inputEnd - (skipSpaces sc).offset)
        have hskipWs_unfold : skipWhitespace (skipSpaces sc) =
          skipWhitespaceLoop (skipSpaces sc)
            ((skipSpaces sc).inputEnd - (skipSpaces sc).offset) := by
          unfold skipWhitespace; rfl
        rw [← hskipWs_unfold] at h_ws_off h_ws_end
        split at hok <;> (try split at hok) <;> (try split at hok) <;>
          (try (have hinj := Except.ok.inj hok; subst hinj;
                exact ⟨by omega, by rw [h_ws_end, h_sp_end]⟩)) <;>
          (try exact absurd hok (by simp))
      · -- not '\t'
        have hinj := Except.ok.inj hok; subst hinj
        exact ⟨h_sp_off, h_sp_end⟩
    · -- past indentation
      have hinj := Except.ok.inj hok; subst hinj
      have ⟨h_ws_off, h_ws_end⟩ := skipWhitespaceLoop_offset_mono
            (skipSpaces sc) ((skipSpaces sc).inputEnd - (skipSpaces sc).offset)
      have hskipWs_unfold : skipWhitespace (skipSpaces sc) =
        skipWhitespaceLoop (skipSpaces sc)
          ((skipSpaces sc).inputEnd - (skipSpaces sc).offset) := by
        unfold skipWhitespace; rfl
      rw [← hskipWs_unfold] at h_ws_off h_ws_end
      exact ⟨by omega, by rw [h_ws_end, h_sp_end]⟩
  · -- no indent check
    have hinj := Except.ok.inj hok; subst hinj
    have ⟨h_ws_off, h_ws_end⟩ := skipWhitespaceLoop_offset_mono
          sc (sc.inputEnd - sc.offset)
    have hsk : skipWhitespace sc = skipWhitespaceLoop sc (sc.inputEnd - sc.offset) := by
      unfold skipWhitespace; rfl
    rw [← hsk] at h_ws_off h_ws_end
    exact ⟨h_ws_off, h_ws_end⟩

/-- `skipToContentLoop` preserves correspondence on `.ok` paths. -/
theorem skipToContentLoop_ok_corr (sc : ScannerState) (sp : SurfPos) (fuel : Nat)
    (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result) :
    ∃ sp', ScannerSurfCorr s_result sp' := by
  induction fuel generalizing sc sp s_result with
  | zero =>
    simp [skipToContentLoop] at hok
    subst hok; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold skipToContentLoop at hok
    dsimp only [] at hok
    -- Split on skipToContentWs result
    split at hok
    · -- skipToContentWs = .error
      simp at hok
    · -- skipToContentWs = .ok s1
      rename_i s1 hok_ws
      obtain ⟨sp1, _, hcorr1⟩ := skipToContentWs_ok_corr sc sp s1 hcorr hok_ws
      obtain ⟨sp2, _, hcorr2⟩ := skipToContentComment_corr s1 sp1 hcorr1
      -- Split on peek of (skipToContentComment s1)
      split at hok
      · -- peek? = some c
        rename_i c hpeek2
        split at hok
        · -- isLineBreakBool c = true: consume newline and recurse
          rename_i hlb
          -- Establish consumeNewline correspondence and fuel budget
          obtain ⟨sp3, hcorr3⟩ := consumeNewline_corr (skipToContentComment s1) sp2 c hcorr2 hpeek2 hlb
          have ⟨h_ws_off, h_ws_end⟩ := skipToContentWs_offset_mono sc s1 hok_ws
          have ⟨h_sc_off, h_sc_end⟩ := skipToContentComment_offset_mono s1
          have ⟨h_cn_off, h_cn_end⟩ := consumeNewline_offset_advance (skipToContentComment s1) c hpeek2 hlb
          have h_cn_inputEnd : (consumeNewline (skipToContentComment s1)).inputEnd = sc.inputEnd := by
            rw [h_cn_end, h_sc_end, h_ws_end]
          have hscc_more := peek_some_hasMore (skipToContentComment s1) c hpeek2
          have hscc_end_eq : (skipToContentComment s1).inputEnd = sc.inputEnd := by
            rw [h_sc_end, h_ws_end]
          rw [hscc_end_eq] at hscc_more
          have hfuel' : fuel' ≥ (consumeNewline (skipToContentComment s1)).inputEnd -
                                 (consumeNewline (skipToContentComment s1)).offset + 1 := by
            rw [h_cn_inputEnd]; omega
          split at hok
          · -- not in flow sequence: { consumeNewline s2 with simpleKeyAllowed := true }
            exact ih _ sp3 s_result
              (corr_of_simpleKeyAllowed_update true hcorr3) hfuel' hok
          · -- in flow sequence: consumeNewline s2
            exact ih _ sp3 s_result hcorr3 hfuel' hok
        · -- not line break: done
          have hinj := Except.ok.inj hok; subst hinj
          exact ⟨sp2, hcorr2⟩
      · -- peek? = none: done
        have hinj := Except.ok.inj hok; subst hinj
        exact ⟨sp2, hcorr2⟩

end Lean4Yaml.Proofs.ScannerCoupling
