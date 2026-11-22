/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.StructureProduction
public import L4YAML.Proofs.Production.Acceptance.Quoted

@[expose] public section Blanket

/-! # Acceptance (scanner converse) for flow indicators

    The inverse of `scanFlowSequenceStart_prod` … `scanFlowEntry_glit`: a
    `GLit` derivation of the indicator at the scanner's position makes the
    scanner land at the derivation's end with the indicator token emitted.

    The four bracket scanners are total.  `scanFlowEntry` is not: `[7]`'s
    `GLit ','` is wider than the scanner, which refuses a leading or doubled
    comma (`[,` / `{,` / `[a,,b]` → `invalidFlowEntry`, §7.4); hence
    `FlowEntryOk`. -/

namespace L4YAML.Proofs.Acceptance

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.StructureProduction
open L4YAML.Grammar

/-- The token-side precondition of `scanFlowEntry`: no leading or doubled comma. -/
def FlowEntryOk (tokens : Array (Positioned YamlToken)) : Prop :=
  ∀ t, lastRealTokenVal? tokens = some t →
    t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry

/-- `ScannerSurfCorr` ignores the token array and the simple-key register. -/
lemma corr_of_emit_key (sc : ScannerState) {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp)
    (tok : YamlToken) (sk : SimpleKeyState) :
    ScannerSurfCorr ({ sc with simpleKey := sk }.emit tok) sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩

lemma advance_tokens (sc : ScannerState) : sc.advance.tokens = sc.tokens := (keeps_advance sc).1

lemma corr_of_emit (sc : ScannerState) {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp)
    (tok : YamlToken) : ScannerSurfCorr (sc.emit tok) sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩

/-- Converse of `scanFlowSequenceStart_prod`. -/
lemma scanFlowSequenceStart_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : GLit '[' sp sp') :
    ScannerSurfCorr (scanFlowSequenceStart sc) sp' ∧
      (scanFlowSequenceStart sc).tokens =
        sc.tokens.push { pos := sc.currentPos, val := .flowSequenceStart } := by
  cases hder with
  | mk rest col =>
    have h := advance_corr (corr_of_emit_key sc hcorr .flowSequenceStart { possible := false })
      (by decide) (by decide)
    exact ⟨⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩, by simp [scanFlowSequenceStart, advance_tokens, ScannerState.emit, ScannerState.currentPos]⟩

/-- Converse of `scanFlowSequenceEnd_prod`. -/
lemma scanFlowSequenceEnd_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : GLit ']' sp sp') :
    ScannerSurfCorr (scanFlowSequenceEnd sc) sp' ∧
      (scanFlowSequenceEnd sc).tokens =
        sc.tokens.push { pos := sc.currentPos, val := .flowSequenceEnd } := by
  cases hder with
  | mk rest col =>
    have h := advance_corr (corr_of_emit sc hcorr .flowSequenceEnd) (by decide) (by decide)
    exact ⟨⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩, by simp [scanFlowSequenceEnd, advance_tokens, ScannerState.emit]⟩

/-- Converse of `scanFlowMappingStart_prod`. -/
lemma scanFlowMappingStart_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : GLit '{' sp sp') :
    ScannerSurfCorr (scanFlowMappingStart sc) sp' ∧
      (scanFlowMappingStart sc).tokens =
        sc.tokens.push { pos := sc.currentPos, val := .flowMappingStart } := by
  cases hder with
  | mk rest col =>
    have h := advance_corr (corr_of_emit_key sc hcorr .flowMappingStart { possible := false })
      (by decide) (by decide)
    exact ⟨⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩, by simp [scanFlowMappingStart, advance_tokens, ScannerState.emit, ScannerState.currentPos]⟩

/-- Converse of `scanFlowMappingEnd_prod`. -/
lemma scanFlowMappingEnd_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : GLit '}' sp sp') :
    ScannerSurfCorr (scanFlowMappingEnd sc) sp' ∧
      (scanFlowMappingEnd sc).tokens =
        sc.tokens.push { pos := sc.currentPos, val := .flowMappingEnd } := by
  cases hder with
  | mk rest col =>
    have h := advance_corr (corr_of_emit sc hcorr .flowMappingEnd) (by decide) (by decide)
    exact ⟨⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩, by simp [scanFlowMappingEnd, advance_tokens, ScannerState.emit]⟩

/-- Converse of `scanFlowEntry_glit`: `[7] c-collect-entry` is accepted unless it is a
    leading or doubled comma (`[,` / `[a,,b]` refute the converse without `FlowEntryOk`). -/
lemma scanFlowEntry_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : GLit ',' sp sp') (hok : FlowEntryOk sc.tokens) :
    ∃ s', scanFlowEntry sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .flowEntry } := by
  cases hder with
  | mk rest col =>
    have h := advance_corr (corr_of_emit sc hcorr .flowEntry) (by decide) (by decide)
    unfold scanFlowEntry
    simp only [bind, Except.bind]
    split
    · rename_i t ht
      obtain ⟨h1, h2, h3⟩ := hok t ht
      have hc : (t == YamlToken.flowSequenceStart || t == YamlToken.flowMappingStart ||
          t == YamlToken.flowEntry) = false := by simp [h1, h2, h3]
      simp only [hc, Bool.false_eq_true, ite_false]
      exact ⟨_, rfl, ⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩,
        by simp [advance_tokens, ScannerState.emit]⟩
    · exact ⟨_, rfl, ⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩,
        by simp [advance_tokens, ScannerState.emit]⟩

end L4YAML.Proofs.Acceptance
