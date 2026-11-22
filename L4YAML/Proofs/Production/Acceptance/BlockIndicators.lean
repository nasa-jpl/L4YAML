/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.StructureProduction
public import L4YAML.Proofs.Production.Acceptance.Quoted

@[expose] public section Blanket

/-! # Acceptance (scanner converse) for block indicators

    The inverse of `scanBlockEntry_prod` / `scanKey_prod` / `scanValue_prod`: a `GLit`
    derivation of `-` / `?` / `:` at the scanner's position makes the scanner land at
    the derivation's end with the indicator token emitted — under the STATE-side
    checks the forward lemmas go through (`scanBlockEntryValidate`, `scanKeyValidate`,
    `scanValueValidate`, `scanValueIndentTabCheck`, the §6.1 tab checks), which are
    not surface facts and are taken as hypotheses.  Refuters of the bare `GLit`
    converse: `\t- a` (`tabInIndentation`), `- a` at a mapping's own column with the
    entry complete (`invalidBareDocument`), `?` at a sequence's own indent
    (`trailingContent`), a `:` whose implicit key sits on an earlier line
    (`invalidImplicitKey`), `?\tb` / `:\tb` at or below the indent (`tabInIndentation`). -/

namespace L4YAML.Proofs.Acceptance

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.StructureCoupling
open L4YAML.Proofs.StructureProduction
open L4YAML.Grammar

lemma emit_corr (sc : ScannerState) {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp)
    (tok : YamlToken) : ScannerSurfCorr (sc.emit tok) sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩

lemma tokens_advance (sc : ScannerState) : sc.advance.tokens = sc.tokens := (keeps_advance sc).1

lemma pushSequenceIndent_currentPos (sc : ScannerState) (col : Int) :
    (pushSequenceIndent sc col).currentPos = sc.currentPos := by
  unfold pushSequenceIndent; split <;> rfl

lemma pushMappingIndent_currentPos (sc : ScannerState) (col : Int) :
    (pushMappingIndent sc col).currentPos = sc.currentPos := by
  unfold pushMappingIndent; split <;> rfl

/-- Converse of `scanBlockEntry_prod`.  In block context the §6.1 tab check, the item-48
    same-line check and `scanBlockEntryValidate` are state-side hypotheses. -/
lemma scanBlockEntry_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : GLit '-' sp sp')
    (hblk : sc.inFlow = false →
      sc.hasTabInPrecedingWhitespace = false ∧
      (sc.implicitValueLine == some sc.line || lastTokenIsNodePropertyOnLine sc.tokens sc.line ||
        sc.markerOnLine) = false ∧
      scanBlockEntryValidate sc = .ok ()) :
    ∃ s', scanBlockEntry sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = (if !sc.inFlow then pushSequenceIndent sc sc.col else sc).tokens.push
        { pos := sc.currentPos, val := .blockEntry } := by
  cases hder with
  | mk rest col =>
    unfold scanBlockEntry
    simp only [bind, Except.bind]
    split
    · rename_i hf
      obtain ⟨htab, hsame, hval⟩ := hblk (by simpa using hf)
      have hind : ScannerSurfCorr (pushSequenceIndent sc sc.col) ⟨'-' :: rest, col⟩ :=
        pushSequenceIndent_corr sc _ hcorr _ (Int.natCast_nonneg _)
      have h := advance_corr (emit_corr _ hind .blockEntry) (by decide) (by decide)
      simp only [htab, Bool.false_eq_true, ite_false, hsame, hval]
      exact ⟨_, rfl, ⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩,
        by simp [tokens_advance, ScannerState.emit, pushSequenceIndent_currentPos]⟩
    · rename_i hf
      have hf' : sc.inFlow = true := by simpa using hf
      have h := advance_corr (emit_corr _ hcorr .blockEntry) (by decide) (by decide)
      exact ⟨_, rfl, ⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩,
        by simp [tokens_advance, ScannerState.emit]⟩

lemma pushMappingIndent_inFlow (sc : ScannerState) (col : Int) :
    (pushMappingIndent sc col).inFlow = sc.inFlow := by
  unfold pushMappingIndent; split <;> rfl

lemma advance_inFlow (sc : ScannerState) : sc.advance.inFlow = sc.inFlow := by
  unfold ScannerState.inFlow; rw [L4YAML.Proofs.ScannerContracts.advance_preserves_flowLevel]

/-- Converse of `scanKey_prod`.  `scanKeyValidate` and the post-`?` tab check (§6.1) are
    hypotheses in block context. -/
lemma scanKey_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : GLit '?' sp sp')
    (hblk : sc.inFlow = false → scanKeyValidate sc = .ok () ∧ sp'.chars.head? ≠ some '\t') :
    ∃ s', scanKey sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = (if !sc.inFlow then pushMappingIndent sc sc.col else sc).tokens.push
        { pos := sc.currentPos, val := .key } := by
  cases hder with
  | mk rest col =>
    unfold scanKey
    simp only [bind, Except.bind]
    split
    · rename_i hf
      obtain ⟨hval, htab⟩ := hblk (by simpa using hf)
      have hind : ScannerSurfCorr (pushMappingIndent sc sc.col) ⟨'?' :: rest, col⟩ :=
        pushMappingIndent_corr sc _ hcorr _ (Int.natCast_nonneg _)
      have h := advance_corr (emit_corr _ hind .key) (by decide) (by decide)
      have hfl : ((pushMappingIndent sc sc.col).emit .key).advance.inFlow = false := by
        rw [advance_inFlow]; show (pushMappingIndent sc sc.col).inFlow = false
        rw [pushMappingIndent_inFlow]; simpa using hf
      simp only [hval, ite_true, hfl, Bool.not_false]
      have hpk : ((pushMappingIndent sc sc.col).emit .key).advance.peek? ≠ some '\t' := by
        cases rest with
        | nil => rw [peek_none_of_corr h]; simp
        | cons d tl => rw [(peek_of_corr h).1]; intro e; exact htab (by simpa using e)
      split
      · rename_i e; exact absurd e hpk
      · exact ⟨_, rfl, ⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩,
          by simp [tokens_advance, ScannerState.emit, pushMappingIndent_currentPos]⟩
    · rename_i hf
      have hf' : sc.inFlow = true := by simpa using hf
      have h := advance_corr (emit_corr _ hcorr .key) (by decide) (by decide)
      have hfl : (sc.emit .key).advance.inFlow = true := by
        rw [advance_inFlow]; exact hf'
      simp only [hfl, Bool.not_true, Bool.false_eq_true, ite_false]
      exact ⟨_, rfl, ⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩,
        by simp [tokens_advance, ScannerState.emit]⟩

/-! ## `:` -/

lemma scanValueClearKey_currentPos (sc : ScannerState) :
    (scanValueClearKey sc).currentPos = sc.currentPos := by
  unfold scanValueClearKey; split <;> (try split) <;> (try split) <;> rfl

lemma scanValueClearKey_flowLevel (sc : ScannerState) :
    (scanValueClearKey sc).flowLevel = sc.flowLevel := by
  unfold scanValueClearKey; split <;> (try split) <;> (try split) <;> rfl

lemma scanValuePrepare_currentPos (sc : ScannerState) :
    (scanValuePrepare sc).currentPos = sc.currentPos := by
  unfold scanValuePrepare pushMappingIndent
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl

lemma scanValuePrepare_flowLevel (sc : ScannerState) :
    (scanValuePrepare sc).flowLevel = sc.flowLevel := by
  unfold scanValuePrepare pushMappingIndent
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl

/-- Converse of `scanValue_prod`.  `scanValueValidate` / `scanValueIndentTabCheck` (on the
    key-cleared state) and the §6.1 tab check after a `:` at or below the indent are
    state-side hypotheses. -/
lemma scanValue_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : GLit ':' sp sp')
    (hval : scanValueValidate (scanValueClearKey sc) = .ok ())
    (hitc : scanValueIndentTabCheck (scanValueClearKey sc) = .ok ())
    (htab : (sc.col : Int) ≤ sc.currentIndent → sc.inFlow = false →
      sp'.chars.head? ≠ some '\t') :
    ∃ s', scanValue sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = (scanValuePrepare (scanValueClearKey sc)).tokens.push
        { pos := sc.currentPos, val := .value } := by
  cases hder with
  | mk rest col =>
    have h1 := scanValueClearKey_corr sc _ hcorr
    have h2 := scanValuePrepare_corr _ _ h1
    have h := advance_corr (emit_corr _ h2 .value) (by decide) (by decide)
    have hfl : ((scanValuePrepare (scanValueClearKey sc)).emit .value).advance.inFlow = sc.inFlow := by
      rw [advance_inFlow]
      show decide (((scanValuePrepare (scanValueClearKey sc)).emit .value).flowLevel > 0) = _
      simp only [ScannerState.emit, scanValuePrepare_flowLevel, scanValueClearKey_flowLevel]
      rfl
    have htc : scanValueTabCheck (sc.col : Int) sc.currentIndent
        ((scanValuePrepare (scanValueClearKey sc)).emit .value).advance = .ok () := by
      unfold scanValueTabCheck
      split
      · rename_i hc
        rw [hfl] at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
        have hne := htab hc.1 hc.2
        split
        · rename_i e
          exfalso
          cases rest with
          | nil => rw [peek_none_of_corr h] at e; simp at e
          | cons d tl => rw [(peek_of_corr h).1] at e; exact hne (by simpa using e)
        · rfl
      · rfl
    unfold scanValue
    simp only [bind, Except.bind, hval, hitc, htc]
    exact ⟨_, rfl, ⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩,
      by simp [tokens_advance, ScannerState.emit, scanValuePrepare_currentPos,
        scanValueClearKey_currentPos]⟩

end L4YAML.Proofs.Acceptance
