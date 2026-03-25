/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Proofs.CouplingBridge

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
      have hadv := advance_non_newline_corr sc ' ' rest hcorr hmore (by decide)
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

end Lean4Yaml.Proofs.ScannerCoupling
