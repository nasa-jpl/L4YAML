/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Coupling.StructureCoupling
public import L4YAML.Proofs.Foundation.CharClass

@[expose] public section Blanket

/-! # Structure Production Coupling (Phase C of v0.4.4)

    Strengthen the `_corr` theorems from `StructureCoupling.lean` to
    additionally produce surface-syntax derivation trees for flow indicators,
    block indicators, node properties, and document markers.

    **Strategy**: Each scanner operation that consumes known characters
    produces the corresponding surface syntax derivation as a witness.
    Flow indicators produce `GLit`, block indicators produce `GLit`.
    Anchor/alias scanning produces `GLit marker ∧ GStar (GChar isNsAnchorChar)`.
    Tag and document marker scanners delegate to `_corr` (deferred).
-/

set_option autoImplicit false

namespace L4YAML.Proofs.StructureProduction

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.StructureCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Proofs.CharClass

/-! ## §1 Flow Indicator Productions

Each flow indicator scanner advances past a single known character.
The production is `GLit c sp sp'` where `c` is the indicator character.

After unfolding the scanner function, the advance is on the emit'd state
(which preserves input/offset/col/inputEnd), so `advance_non_newline_corr`
applies. The final struct updates (flowLevel, simpleKeyAllowed, etc.) are
non-tracked, so correspondence transfers via field projection. -/

-- `scanFlowSequenceStart` produces `GLit '['`.
lemma scanFlowSequenceStart_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '[') :
    ∃ sp', GLit '[' sp sp' ∧ ScannerSurfCorr (scanFlowSequenceStart sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanFlowSequenceStart
  have hcorr_emit : ScannerSurfCorr
      ({ sc with simpleKey := { possible := false } }.emit .flowSequenceStart)
      ⟨'[' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr
    ({ sc with simpleKey := { possible := false } }.emit .flowSequenceStart)
    '[' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

-- `scanFlowSequenceEnd` produces `GLit ']'`.
lemma scanFlowSequenceEnd_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some ']') :
    ∃ sp', GLit ']' sp sp' ∧ ScannerSurfCorr (scanFlowSequenceEnd sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanFlowSequenceEnd
  have hcorr_emit : ScannerSurfCorr
      (sc.emit .flowSequenceEnd)
      ⟨']' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr
    (sc.emit .flowSequenceEnd)
    ']' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

-- `scanFlowMappingStart` produces `GLit '{'`.
lemma scanFlowMappingStart_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '{') :
    ∃ sp', GLit '{' sp sp' ∧ ScannerSurfCorr (scanFlowMappingStart sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanFlowMappingStart
  have hcorr_emit : ScannerSurfCorr
      ({ sc with simpleKey := { possible := false } }.emit .flowMappingStart)
      ⟨'{' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr
    ({ sc with simpleKey := { possible := false } }.emit .flowMappingStart)
    '{' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

-- `scanFlowMappingEnd` produces `GLit '}'`.
lemma scanFlowMappingEnd_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '}') :
    ∃ sp', GLit '}' sp sp' ∧ ScannerSurfCorr (scanFlowMappingEnd sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanFlowMappingEnd
  have hcorr_emit : ScannerSurfCorr
      (sc.emit .flowMappingEnd)
      ⟨'}' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr
    (sc.emit .flowMappingEnd)
    '}' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

-- `scanFlowEntry` preserves correspondence on success.
lemma scanFlowEntry_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (s' : ScannerState) (hok : scanFlowEntry sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' :=
  scanFlowEntry_corr sc sp hcorr s' hok

-- `scanFlowEntry` produces `GLit ','` when the head character is `,`.
-- Strengthens `scanFlowEntry_prod`: the entry separator carries the
-- `GLit ','` surface witness needed for `SFlowSeqEntries`/`SFlowMapEntries`
-- accumulation (Fix A, Piece 2). Both the guard-throw and the clean paths
-- are handled; on `.ok` the state is `(sc.emit .flowEntry).advance` (with the
-- untracked `simpleKeyAllowed` field flipped), so the tracked correspondence
-- fields transfer from `advance_non_newline_corr`.
lemma scanFlowEntry_glit (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some ',')
    (s' : ScannerState) (hok : scanFlowEntry sc = .ok s') :
    ∃ sp', GLit ',' sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanFlowEntry at hok
  simp only [bind, Except.bind] at hok
  have hcorr_emit : ScannerSurfCorr (sc.emit .flowEntry) ⟨',' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr (sc.emit .flowEntry) ',' rest hcorr_emit hmore
    (by decide) (by decide)
  split at hok
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix,
             hcorr_adv.indent_cols_nonneg⟩
  · have h := Except.ok.inj hok; subst h
    exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix,
           hcorr_adv.indent_cols_nonneg⟩

/-! ## §2 Block Indicator Productions

Block indicators (`-`, `?`, `:`) each advance past a single character.
On success they produce `GLit` for the indicator character.

The main complication vs flow indicators is that block scanners go through
`Except` (for tab-in-indentation checks) and `pushSequenceIndent`/
`pushMappingIndent` (which have an internal `if` that prevents definitional
col equality). The fix: repack `ScannerSurfCorr` with `⟨chars_from, rfl, end_eq⟩`
to use the intermediate state's col, then derive `hmore` from the nonempty
char list. -/

-- Derive `offset < inputEnd` from ScannerSurfCorr with nonempty chars.
-- Used when `peek_some_has_more` doesn't apply (intermediate state's peek?
-- isn't known, but the SurfPos chars are known nonempty after `peek_some_sp`).
lemma corr_nonempty_has_more {sc : ScannerState}
    {c : Char} {rest : List Char} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩) :
    sc.offset < sc.inputEnd := by
  match hcorr.chars_from with
  | .cons _ hlt _ _ _ _ => have := hcorr.end_eq; omega

-- `scanBlockEntry` produces `GLit '-'`.
lemma scanBlockEntry_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '-')
    (s' : ScannerState) (hok : scanBlockEntry sc = .ok s') :
    ∃ sp', GLit '-' sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · -- !inFlow: pushSequenceIndent
    split at hok
    · simp at hok
    · split at hok  -- item 48 same-line check
      · simp at hok
      split at hok  -- `scanBlockEntryValidate` (item 134)
      · simp at hok
      have h := Except.ok.inj hok; subst h
      have hcorr_ind := pushSequenceIndent_corr sc
        ⟨'-' :: rest, sc.col⟩ hcorr (sc.col : Int) (Int.natCast_nonneg _)
      have hcorr_emit : ScannerSurfCorr
          ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry)
          ⟨'-' :: rest, sc.col⟩ :=
        ⟨hcorr_ind.chars_from, hcorr_ind.col_eq, hcorr_ind.end_eq, hcorr_ind.input_prefix, hcorr_ind.indent_cols_nonneg⟩
      -- Repack with sc_mid.col to satisfy advance_non_newline_corr
      have hcorr_at : ScannerSurfCorr
          ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry)
          ⟨'-' :: rest,
           ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry).col⟩ :=
        ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
      have hmore := corr_nonempty_has_more hcorr_at
      have hcorr_adv := advance_non_newline_corr
        ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry)
        '-' rest hcorr_at hmore (by decide) (by decide)
      exact ⟨hcorr_adv.chars_from,
             by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                dsimp only [] at *; omega,
             hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
  · -- inFlow: no pushSequenceIndent
    have h := Except.ok.inj hok; subst h
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr
        (sc.emit .blockEntry) ⟨'-' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    have hcorr_adv := advance_non_newline_corr
      (sc.emit .blockEntry) '-' rest hcorr_emit hmore (by decide) (by decide)
    exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

-- Bridge: isBlankBool c → ¬isNsChar c (converse of not_blank_to_nsChar in ScalarProduction).
lemma blank_to_not_nsChar {c : Char}
    (h : isBlankBool c = true) : ¬isNsChar c := by
  intro hns
  obtain ⟨hlb, hws, -, -⟩ := hns
  simp [isBlankBool, isWhiteSpaceBool, isSpaceBool, isTabBool,
    isLineBreakBool, isLineFeedBool, isCarriageReturnBool, beq_iff_eq] at h
  simp [isWhiteSpaceProp, isSpaceProp, isTabProp] at hws
  simp [isLineBreakProp, isLineFeedProp, isCarriageReturnProp] at hlb
  rcases h with (rfl | rfl) | rfl | rfl <;> simp_all

-- GNot SNsChar at position after block entry indicator, given isBlockEntryCandidate.
-- The scanner checks `peekAt? 1` = blank/EOF. After advancing past `-`, the head
-- of the remaining chars is the character that was at `peekAt? 1`.
lemma blockEntryCandidate_gnot (sc : ScannerState) (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨'-' :: rest, col⟩)
    (h_candidate : isBlockEntryCandidate sc = true) :
    GNot SNsChar ⟨rest, col + 1⟩ := by
  intro s' h_ns
  cases rest with
  | nil => cases h_ns
  | cons c rest' =>
    cases h_ns with
    | mk c' rest'' col' h_pred =>
      have h_peekAt : sc.peekAt? 1 = some c := by
        unfold ScannerState.peekAt?
        have hlt : sc.offset < sc.inputEnd := by
          rw [hcorr.end_eq]
          exact match hcorr.chars_from with | .cons _ h _ _ _ _ => h
        rw [peekAtLoop_step hlt]
        have hcf_tail := chars_from_cons_tail hcorr.chars_from
        have hlt_next : (String.Pos.Raw.next sc.input ⟨sc.offset⟩).byteIdx < sc.inputEnd := by
          rw [hcorr.end_eq]
          exact match hcf_tail with | .cons _ h _ _ _ _ => h
        exact peekAtLoop_cons hlt_next hcf_tail
      unfold isBlockEntryCandidate at h_candidate
      rw [h_peekAt] at h_candidate
      exact blank_to_not_nsChar h_candidate h_pred

-- `scanKey` produces `GLit '?'`.
lemma scanKey_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '?')
    (s' : ScannerState) (hok : scanKey sc = .ok s') :
    ∃ sp', GLit '?' sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · -- !inFlow: `scanKeyValidate` (item 131), then pushMappingIndent
    split at hok
    · simp at hok
    have hcorr_ind := pushMappingIndent_corr sc
      ⟨'?' :: rest, sc.col⟩ hcorr (sc.col : Int) (Int.natCast_nonneg _)
    have hcorr_emit : ScannerSurfCorr
        ((pushMappingIndent sc (sc.col : Int)).emit .key)
        ⟨'?' :: rest, sc.col⟩ :=
      ⟨hcorr_ind.chars_from, hcorr_ind.col_eq, hcorr_ind.end_eq, hcorr_ind.input_prefix, hcorr_ind.indent_cols_nonneg⟩
    have hcorr_at : ScannerSurfCorr
        ((pushMappingIndent sc (sc.col : Int)).emit .key)
        ⟨'?' :: rest,
         ((pushMappingIndent sc (sc.col : Int)).emit .key).col⟩ :=
      ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
    have hmore := corr_nonempty_has_more hcorr_at
    have hcorr_adv := advance_non_newline_corr
      ((pushMappingIndent sc (sc.col : Int)).emit .key)
      '?' rest hcorr_at hmore (by decide) (by decide)
    -- Tab check after advance, then .ok
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨hcorr_adv.chars_from,
               by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                  dsimp only [] at *; omega,
               hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨hcorr_adv.chars_from,
             by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                dsimp only [] at *; omega,
             hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
  · -- inFlow
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr
        (sc.emit .key) ⟨'?' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    have hcorr_adv := advance_non_newline_corr
      (sc.emit .key) '?' rest hcorr_emit hmore (by decide) (by decide)
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

-- `scanValue` produces `GLit ':'`.
lemma scanValue_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some ':')
    (s' : ScannerState) (hok : scanValue sc = .ok s') :
    ∃ sp', GLit ':' sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  -- scanValueValidate (Except)
  split at hok
  · simp at hok
  · -- scanValueIndentTabCheck (item 31), then scanValueTabCheck
    split at hok
    · simp at hok
    split at hok
    · simp at hok
    · have h := Except.ok.inj hok; subst h
      have hcorr_ck := scanValueClearKey_corr sc ⟨':' :: rest, sc.col⟩ hcorr
      have hcorr_prep := scanValuePrepare_corr
        (scanValueClearKey sc) ⟨':' :: rest, sc.col⟩ hcorr_ck
      have hcorr_emit : ScannerSurfCorr
          ((scanValuePrepare (scanValueClearKey sc)).emit .value)
          ⟨':' :: rest, sc.col⟩ :=
        ⟨hcorr_prep.chars_from, hcorr_prep.col_eq, hcorr_prep.end_eq, hcorr_prep.input_prefix, hcorr_prep.indent_cols_nonneg⟩
      have hcorr_at : ScannerSurfCorr
          ((scanValuePrepare (scanValueClearKey sc)).emit .value)
          ⟨':' :: rest,
           ((scanValuePrepare (scanValueClearKey sc)).emit .value).col⟩ :=
        ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
      have hmore := corr_nonempty_has_more hcorr_at
      have hcorr_adv := advance_non_newline_corr
        ((scanValuePrepare (scanValueClearKey sc)).emit .value)
        ':' rest hcorr_at hmore (by decide) (by decide)
      exact ⟨hcorr_adv.chars_from,
             by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                dsimp only [] at *; omega,
             hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

/-! ## §3 Node Property Productions

Anchor, alias, and tag scanners produce surface syntax derivation trees.
The anchor name loop produces `GStar (GChar isNsAnchorChar)`.
The overall `scanAnchorOrAlias` produces `GLit marker ∧ GStar (GChar isNsAnchorChar)`.
Tag scanning delegates to `_corr` (4-variant analysis deferred). -/

-- Bridge: scanner's Bool conjunction → surface Prop `isNsAnchorChar`.
lemma not_of_bool_false {P : Prop} {b : Bool}
    (h_iff : P ↔ b = true) (hf : b = false) : ¬P :=
  fun hp => by rw [hf] at h_iff; exact absurd (h_iff.mp hp) Bool.false_ne_true

lemma bool_not_true_imp_false {b : Bool} (h : (!b) = true) :
    b = false := by cases b <;> simp_all

lemma isNsAnchorChar_of_scanner_cond {c : Char}
    (h : (!isFlowIndicatorBool c && !isWhiteSpaceBool c &&
          !isLineBreakBool c && isPrintableBool c && (c != '﻿')) = true) :
    isNsAnchorChar c := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨hnfi, hnws⟩, hnlb⟩, hpr⟩, hbom⟩ := h
  have hfi := bool_not_true_imp_false hnfi
  have hws := bool_not_true_imp_false hnws
  have hlb := bool_not_true_imp_false hnlb
  exact ⟨⟨not_of_bool_false (isLineBreak_correspondence c) hlb,
          not_of_bool_false (isWhiteSpace_correspondence c) hws,
          (isPrintable_iff c).mp hpr, hbom⟩,
         not_of_bool_false (isFlowIndicator_correspondence c) hfi⟩

lemma scanner_cond_of_isNsAnchorChar {c : Char} (h : isNsAnchorChar c) :
    (!isFlowIndicatorBool c && !isWhiteSpaceBool c &&
      !isLineBreakBool c && isPrintableBool c && (c != '\ufeff')) = true := by
  obtain ⟨⟨hnlb, hnws, hpr, hbom⟩, hnfi⟩ := h
  simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, (isPrintable_iff c).mpr hpr⟩, hbom⟩
  · exact Bool.eq_false_iff.mpr (fun ht => hnfi ((isFlowIndicator_correspondence c).mpr ht))
  · exact Bool.eq_false_iff.mpr (fun ht => hnws ((isWhiteSpace_correspondence c).mpr ht))
  · exact Bool.eq_false_iff.mpr (fun ht => hnlb ((isLineBreak_correspondence c).mpr ht))

lemma gnot_gchar_nil {P : Char → Prop} (col : Nat) : GNot (GChar P) ⟨[], col⟩ := by
  intro s' h; cases h

lemma gnot_gchar_head {P : Char → Prop} {c : Char} {rest : List Char} {col : Nat}
    (h : ¬ P c) : GNot (GChar P) ⟨c :: rest, col⟩ := by
  intro s' hg; cases hg with | mk _ _ _ hp => exact h hp

-- `GNot (GChar P)` at a position whose scanner twin has `peek? = none`.
lemma gnot_gchar_of_peek_none {P : Char → Prop} {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = none) : GNot (GChar P) sp := by
  have hnil := peek_none_chars_nil hcorr hpeek
  obtain ⟨chars, col⟩ := sp
  simp only at hnil; subst hnil; exact gnot_gchar_nil col

lemma peek_none_of_fuel_zero {sc : ScannerState} (h : sc.inputEnd - sc.offset ≤ 0) :
    sc.peek? = none := by
  unfold ScannerState.peek?
  simp only [show ¬ sc.offset < sc.inputEnd by omega, ↓reduceIte]

-- `collectAnchorNameLoop` produces the MAXIMAL `GStar (GChar isNsAnchorChar)`:
-- with fuel covering the remaining input, the loop stops only at end of input or
-- at a non-anchor char, which is the `GNot` lookahead [101]/[104] demand.
-- When starting from empty name and the result name grew, positions differ (sp ≠ sp').
lemma collectAnchorNameLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (name : String) (fuel : Nat)
    (hfuel : sc.inputEnd - sc.offset ≤ fuel) :
    ∃ sp', GStar (GChar isNsAnchorChar) sp sp' ∧
           ScannerSurfCorr (collectAnchorNameLoop sc name fuel).snd sp' ∧
           (sp = sp' → (collectAnchorNameLoop sc name fuel).fst = name) ∧
           GNot (GChar isNsAnchorChar) sp' := by
  induction fuel generalizing sc sp name with
  | zero =>
    exact ⟨sp, GStar.nil sp, hcorr, fun _ => rfl,
           gnot_gchar_of_peek_none hcorr (peek_none_of_fuel_zero hfuel)⟩
  | succ fuel' ih =>
    unfold collectAnchorNameLoop; split
    · rename_i c hpeek; split
      · -- anchor char: advance and recurse
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        -- Extract isLineBreakBool c = false from conjunction
        have hlb : isLineBreakBool c = false :=
          bool_not_true_imp_false
            (Bool.and_eq_true_iff.mp
              (Bool.and_eq_true_iff.mp
                (Bool.and_eq_true_iff.mp hcond).1).1).2
        -- c ≠ newlines: rw substitutes the literal, native_decide finishes
        have hne_nl : c ≠ '\n' := by
          intro heq; rw [heq] at hlb; exact absurd hlb (by native_decide)
        have hne_cr : c ≠ '\r' := by
          intro heq; rw [heq] at hlb; exact absurd hlb (by native_decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          hmore hne_nl hne_cr
        have hfuel' : sc.advance.inputEnd - sc.advance.offset ≤ fuel' := by
          have h1 := ScannerProgress.advance_offset_lt sc hmore
          have h2 : sc.advance.inputEnd = sc.inputEnd := advance_inputEnd sc
          omega
        obtain ⟨sp', h_tail, hcorr', _, hnot⟩ := ih sc.advance ⟨rest, sc.col + 1⟩
          hcorr_adv (name.push c) hfuel'
        refine ⟨sp',
               GStar.cons _ _ _
                 (GChar.mk c rest sc.col (isNsAnchorChar_of_scanner_cond hcond))
                 h_tail,
               hcorr', ?_, hnot⟩
        intro h_eq; exfalso
        have h_col_ge : sp'.col ≥ sc.col + 1 := gstar_gchar_col_le h_tail
        have : sp'.col = sc.col := by rw [← h_eq]
        omega
      · -- not anchor char: stop; the lookahead is exactly the failed condition
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        refine ⟨_, GStar.nil _, hcorr, fun _ => rfl, gnot_gchar_head ?_⟩
        intro h; exact hcond (scanner_cond_of_isNsAnchorChar h)
    · -- none: stop
      rename_i hpeek
      exact ⟨sp, GStar.nil sp, hcorr, fun _ => rfl, gnot_gchar_of_peek_none hcorr hpeek⟩

-- `scanAnchorOrAlias` produces `GLit marker ∧ GStar (GChar isNsAnchorChar)` with `sp_mid ≠ sp'`.
-- The marker character is `&` for anchors and `*` for aliases.
-- Since `.ok` requires a non-empty name (A10 Except conversion), the GStar is always non-empty.
lemma scanAnchorOrAlias_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (isAnchor : Bool)
    (marker : Char) (hpeek : sc.peek? = some marker)
    (hne_nl : marker ≠ '\n') (hne_cr : marker ≠ '\r')
    (s' : ScannerState) (hok : scanAnchorOrAlias sc isAnchor = .ok s') :
    ∃ sp_mid sp', GLit marker sp sp_mid ∧
                  GStar (GChar isNsAnchorChar) sp_mid sp' ∧
                  sp_mid ≠ sp' ∧
                  GNot (GChar isNsAnchorChar) sp' ∧
                  ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  have hcorr_adv := advance_non_newline_corr sc marker rest hcorr
    hmore hne_nl hne_cr
  obtain ⟨sp', h_gstar, hcorr', h_sp_name, h_not⟩ :=
    collectAnchorNameLoop_prod sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv ""
      (sc.inputEnd - sc.advance.offset) (by simp [advance_inputEnd sc])
  refine ⟨⟨rest, sc.col + 1⟩, sp', GLit.mk rest sc.col, h_gstar, ?_, h_not, ?_⟩
  · -- sp_mid ≠ sp': .ok requires non-empty name, which requires sp advance
    intro h_eq
    have h_name_empty := h_sp_name h_eq
    unfold scanAnchorOrAlias at hok; dsimp only [] at hok
    rw [h_name_empty] at hok; simp at hok
  · unfold scanAnchorOrAlias at hok; dsimp only [] at hok
    split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      exact ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩

/-! ### Tag char predicate bridges -/

-- Word chars are tag chars: ns-word-char ⊂ ns-tag-char.
lemma isWordCharProp_to_isTagCharProp {c : Char} (hw : isWordCharProp c) :
    isTagCharProp c := by
  refine ⟨Or.inl hw, ?_, ?_⟩ <;> intro h
  · subst h; simp [isWordCharProp, isAsciiLetterProp] at hw
  · simp only [isFlowIndicatorProp, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;>
      simp [isWordCharProp, isAsciiLetterProp] at hw

-- Lift `GStar (GChar P)` through predicate implication.
lemma GStar_gchar_lift {P Q : Char → Prop} (h : ∀ c, P c → Q c)
    {sp sp' : SurfPos} (hg : GStar (GChar P) sp sp') :
    GStar (GChar Q) sp sp' := by
  induction hg with
  | nil => exact GStar.nil _
  | cons _ _ _ hchar hrest ih =>
    cases hchar with
    | mk c rest col hpc =>
      exact GStar.cons _ _ _ (GChar.mk c rest col (h c hpc)) ih

/-! ### Tag suffix loop production -/

-- `collectTagSuffixLoop` produces `GStar (GChar isTagCharProp)`.
private lemma gstar_append_local {P : SurfPos → SurfPos → Prop} {a b c : SurfPos}
    (h₁ : GStar P a b) : GStar P b c → GStar P a c := by
  induction h₁ with
  | nil _ => exact id
  | cons s₁ s₂ _ hx _ ih => exact fun h => GStar.cons s₁ s₂ c hx (ih h)

lemma collectTagSuffixLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (suffix : String) (fuel : Nat)
    (hfuel : sc.inputEnd - sc.offset ≤ fuel) :
    ∃ sp', GStar (GChar isTagCharProp) sp sp' ∧
           ScannerSurfCorr (collectTagSuffixLoop sc suffix fuel).snd sp' ∧
           GNot (GChar isTagCharProp) sp' := by
  induction fuel generalizing sc sp suffix with
  | zero =>
    exact ⟨sp, GStar.nil sp, hcorr, gnot_gchar_of_peek_none hcorr (peek_none_of_fuel_zero hfuel)⟩
  | succ fuel' ih =>
    unfold collectTagSuffixLoop; split
    · rename_i c hpeek; split
      · -- tag char: advance and recurse
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have htag : isTagCharProp c := (isTagChar_iff c).mp hcond
        have hne_nl : c ≠ '\n' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hne_cr : c ≠ '\r' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          hmore hne_nl hne_cr
        have hfuel' : sc.advance.inputEnd - sc.advance.offset ≤ fuel' := by
          have h1 := ScannerProgress.advance_offset_lt sc hmore
          have h2 : sc.advance.inputEnd = sc.inputEnd := advance_inputEnd sc
          omega
        obtain ⟨sp', h_tail, hcorr', hnot⟩ := ih sc.advance ⟨rest, sc.col + 1⟩
          hcorr_adv (suffix.push c) hfuel'
        exact ⟨sp',
               GStar.cons _ _ _
                 (GChar.mk c rest sc.col htag)
                 h_tail,
               hcorr', hnot⟩
      · -- not tag char: stop — the lookahead
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        exact ⟨_, GStar.nil _, hcorr,
               gnot_gchar_head (fun h => hcond ((isTagChar_iff c).mpr h))⟩
    · -- none: stop — end of input
      rename_i hpeek
      exact ⟨sp, GStar.nil sp, hcorr, gnot_gchar_of_peek_none hcorr hpeek⟩

/-! ### Verbatim tag URI loop production -/

-- `collectVerbatimTagLoop` produces `GStar (GChar isUriCharProp)` for URI chars.
-- When the loop terminates at `>`, also produces `GLit '>'`.
-- Links grammar positions to scanner-level `foundClose` and `uri` values.
lemma collectVerbatimTagLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (uri : String) (fuel : Nat) :
    ∃ sp_mid sp', GStar (GChar isUriCharProp) sp sp_mid ∧
                  ScannerSurfCorr (collectVerbatimTagLoop sc uri fuel).snd.snd sp' ∧
                  (sp_mid = sp' ∨ GLit '>' sp_mid sp') ∧
                  (sp_mid = sp' → (collectVerbatimTagLoop sc uri fuel).snd.fst = false) ∧
                  (sp = sp_mid → (collectVerbatimTagLoop sc uri fuel).fst = uri) := by
  induction fuel generalizing sc sp uri with
  | zero => exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl rfl, fun _ => rfl, fun _ => rfl⟩
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop; split
    · -- peek? = some '>': advance past > and produce GLit
      rename_i hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      have hcorr_adv := advance_non_newline_corr sc '>' rest hcorr
        hmore (by decide) (by decide)
      exact ⟨⟨'>' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
             GStar.nil _,
             hcorr_adv,
             Or.inr (GLit.mk rest sc.col),
             fun h => by simp only [SurfPos.mk.injEq] at h; omega,
             fun _ => rfl⟩
    · -- peek? = some c (c ≠ '>'): check isUriCharBool
      rename_i c _ hpeek; split
      · -- isUriCharBool c = true: advance and recurse
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have huri : isUriCharProp c := (isUriChar_iff c).mp hcond
        have hne_nl : c ≠ '\n' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hne_cr : c ≠ '\r' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          hmore hne_nl hne_cr
        obtain ⟨sp_mid, sp', h_tail, hcorr', h_gt, h_close_link, _⟩ :=
          ih sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv (uri.push c)
        refine ⟨sp_mid, sp',
               GStar.cons _ _ sp_mid
                 (GChar.mk c rest sc.col huri)
                 h_tail,
               hcorr', h_gt, h_close_link, ?_⟩
        intro h_eq; exfalso
        have h_col_ge : sp_mid.col ≥ sc.col + 1 := gstar_gchar_col_le h_tail
        have : sp_mid.col = sc.col := by rw [← h_eq]
        omega
      · -- isUriCharBool c = false: stop
        exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl rfl, fun _ => rfl, fun _ => rfl⟩
    · -- peek? = none: stop
      exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl rfl, fun _ => rfl, fun _ => rfl⟩

/-! ### Tag handle loop production -/

-- `collectTagHandleLoop` produces `GStar (GChar isWordCharProp)` for word chars.
-- When the loop terminates at `!`, also produces `GLit '!'` and `foundBang = true`.
-- When stopping without `!`, produces `foundBang = false` and `sp_mid = sp'`.
lemma collectTagHandleLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (chars : String) (fuel : Nat) :
    ∃ sp_mid sp', GStar (GChar isWordCharProp) sp sp_mid ∧
                  ScannerSurfCorr (collectTagHandleLoop sc chars fuel).snd.snd sp' ∧
                  ((sp_mid = sp' ∧ (collectTagHandleLoop sc chars fuel).snd.fst = false) ∨
                   (GLit '!' sp_mid sp' ∧ (collectTagHandleLoop sc chars fuel).snd.fst = true)) := by
  induction fuel generalizing sc sp chars with
  | zero => exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl ⟨rfl, rfl⟩⟩
  | succ fuel' ih =>
    unfold collectTagHandleLoop; split
    · -- peek? = some '!': advance past ! and produce GLit
      rename_i hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      have hcorr_adv := advance_non_newline_corr sc '!' rest hcorr
        hmore (by decide) (by decide)
      exact ⟨⟨'!' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
             GStar.nil _,
             hcorr_adv,
             Or.inr ⟨GLit.mk rest sc.col, rfl⟩⟩
    · -- peek? = some c (c ≠ '!'): check isWordCharBool
      rename_i c _ hpeek; split
      · -- isWordCharBool c = true: advance and recurse
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have hword : isWordCharProp c := (isWordChar_iff c).mp hcond
        have hne_nl : c ≠ '\n' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hne_cr : c ≠ '\r' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          hmore hne_nl hne_cr
        obtain ⟨sp_mid, sp', h_tail, hcorr', h_bang⟩ :=
          ih sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv (chars.push c)
        exact ⟨sp_mid, sp',
               GStar.cons _ _ sp_mid
                 (GChar.mk c rest sc.col hword)
                 h_tail,
               hcorr', h_bang⟩
      · -- isWordCharBool c = false: stop
        exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl ⟨rfl, rfl⟩⟩
    · -- peek? = none: stop
      exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl ⟨rfl, rfl⟩⟩

-- `scanTag` on the secondary branch (`!!suffix`) produces `SCNsTagProperty.secondary`.
-- Preconditions: first char `!`, second char `!`.
lemma scanTag_secondary_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '!') (hpeek2 : sc.advance.peek? = some '!')
    (s' : ScannerState) (hok : scanTag sc = .ok s') :
    ∃ sp', SCNsTagProperty sp sp' ∧ ScannerSurfCorr s' sp' := by
  -- Decompose first `!`
  obtain ⟨rest1, hsp_eq1⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq1
  have hmore1 := peek_some_has_more hpeek
  have hcorr_bang := advance_non_newline_corr sc '!' rest1 hcorr
    hmore1 (by decide) (by decide)
  -- Decompose second `!`
  obtain ⟨srest, hrest1_eq⟩ := peek_some_sp hcorr_bang hpeek2
  have hchars_eq := congrArg SurfPos.chars hrest1_eq
  dsimp only [] at hchars_eq; subst hchars_eq
  -- Now sp = ⟨'!' :: '!' :: srest, sc.col⟩
  -- Repack hcorr_bang with rfl col for advance_non_newline_corr
  have hcorr_bang' : ScannerSurfCorr sc.advance ⟨'!' :: srest, sc.advance.col⟩ :=
    ⟨hcorr_bang.chars_from, rfl, hcorr_bang.end_eq, hcorr_bang.input_prefix, hcorr_bang.indent_cols_nonneg⟩
  have hmore2 := peek_some_has_more hpeek2
  have hcorr_bang2 := advance_non_newline_corr sc.advance '!' srest hcorr_bang'
    hmore2 (by decide) (by decide)
  -- Repack for suffix loop with rfl col
  have hcorr_bang2' : ScannerSurfCorr sc.advance.advance
      ⟨srest, sc.advance.advance.col⟩ :=
    ⟨hcorr_bang2.chars_from, rfl, hcorr_bang2.end_eq, hcorr_bang2.input_prefix, hcorr_bang2.indent_cols_nonneg⟩
  -- Unfold scanTag and resolve match to secondary branch
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · -- some '<': contradicts hpeek2
    rename_i h_lt
    exact absurd (h_lt ▸ hpeek2) (by decide)
  · -- some '!': secondary tag
    have h_inj := Except.ok.inj hok; subst h_inj
    unfold scanSecondaryTag; dsimp only []
    obtain ⟨sp', h_gstar, hcorr_sfx, h_gnot⟩ :=
      collectTagSuffixLoop_prod sc.advance.advance ⟨srest, sc.advance.advance.col⟩
        hcorr_bang2' "" (sc.currentPos.offset + sc.advance.inputEnd - sc.advance.advance.offset)
        (by simp only [advance_inputEnd]; omega)
    -- Bridge col: sc.advance.advance.col = sc.col + 2
    have hcol_bridge : sc.advance.advance.col = sc.col + 2 := by
      have := hcorr_bang.col_eq; have := hcorr_bang2.col_eq
      dsimp only [] at *; omega
    rw [hcol_bridge] at h_gstar
    refine ⟨sp', SCNsTagProperty.secondary srest sc.col sp' h_gstar h_gnot, ?_⟩
    exact ⟨hcorr_sfx.chars_from, hcorr_sfx.col_eq, hcorr_sfx.end_eq, hcorr_sfx.input_prefix, hcorr_sfx.indent_cols_nonneg⟩
  · -- fallthrough: contradicts hpeek2
    rename_i _ h_not_bang
    exact absurd hpeek2 h_not_bang

-- Named/non-specific tag grammar + correspondence.
-- Pre: scanner after first `!`, at ⟨rest, col+1⟩, peek ≠ `!`.
private lemma collectTagHandleLoop_inputEnd (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.inputEnd = s.inputEnd := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_inputEnd s
    · split
      · rw [ih]; exact advance_inputEnd s
      · simp only []
    · simp only []

-- `hend`: the suffix loop's fuel `inputEnd - offset` must cover the remaining input for the
-- `[97]` lookahead (`scanTag` passes `sc.inputEnd`).
lemma scanNamedTag_prod (sc : ScannerState) (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨rest, col + 1⟩)
    (hpeek_not_bang : ¬(sc.peek? = some '!'))
    (startPos : YamlPos) (inputEnd : Nat) (hend : sc.inputEnd ≤ inputEnd) :
    ∃ sp', SCNsTagProperty ⟨'!' :: rest, col⟩ sp' ∧
           ScannerSurfCorr (scanNamedTag sc startPos inputEnd) sp' := by
  unfold scanNamedTag; dsimp only []
  obtain ⟨sp_mid, sp_hdl, h_gstar_word, hcorr_hdl, h_bang_cases⟩ :=
    collectTagHandleLoop_prod sc ⟨rest, col + 1⟩ hcorr "" _
  split
  · -- foundBang = true → named tag (handle + suffix)
    rename_i h_fb_true
    -- Resolve h_bang_cases to inr (foundBang = true)
    rcases h_bang_cases with ⟨_, h_fb⟩ | ⟨h_glit, _⟩
    · exact absurd (h_fb.symm.trans h_fb_true) (by decide)
    · -- h_glit : GLit '!' sp_mid sp_hdl
      -- sp ≠ sp_mid: if sp = sp_mid then rest starts with '!',
      -- contradicting hpeek_not_bang
      have h_ne : ⟨rest, col + 1⟩ ≠ sp_mid := by
        intro h_eq
        -- GLit says sp_mid.chars starts with '!'
        have h_sp_chars : ∃ rest', sp_mid.chars = '!' :: rest' := by
          cases h_glit with | mk r c => exact ⟨r, rfl⟩
        obtain ⟨rest', h_chars_eq⟩ := h_sp_chars
        rw [← h_eq] at h_chars_eq
        -- rest = '!' :: rest'
        dsimp only [] at h_chars_eq
        have hmore : sc.offset < sc.inputEnd := by
          rw [hcorr.end_eq]; rw [h_chars_eq] at hcorr
          exact match hcorr.chars_from with | .cons _ h _ _ _ _ => h
        obtain ⟨c, _, h_cs, h_peek⟩ := peek_corr sc ⟨rest, col + 1⟩ hcorr hmore
        rw [h_chars_eq] at h_cs
        have : c = '!' := by injection h_cs with h; exact h.symm
        rw [this] at h_peek
        exact hpeek_not_bang h_peek
      have h_gplus := GStar_to_GPlus h_gstar_word h_ne
      -- Suffix production
      obtain ⟨sp', h_gstar_tag, hcorr_sfx, h_gnot⟩ :=
        collectTagSuffixLoop_prod _ sp_hdl hcorr_hdl "" (inputEnd - (collectTagHandleLoop sc "" (inputEnd - sc.offset)).snd.snd.offset) (by rw [collectTagHandleLoop_inputEnd]; omega)
      exact ⟨sp', SCNsTagProperty.named rest col sp_mid sp_hdl sp' h_gplus h_glit h_gstar_tag h_gnot,
             corr_of_emitAt _ _ hcorr_sfx⟩
  · -- foundBang = false → primary/non-specific tag
    rename_i h_fb_false
    -- Resolve h_bang_cases to inl (foundBang = false)
    have h_eq : sp_mid = sp_hdl := by
      rcases h_bang_cases with ⟨h, _⟩ | ⟨_, h_fb⟩
      · exact h
      · exact absurd h_fb h_fb_false
    subst h_eq
    -- Lift GStar wordChar → GStar tagChar, then the suffix loop extends it to
    -- the full `ns-tag-char*` run (N1b: `!t.x` is one primary tag)
    have h_gstar_tag := GStar_gchar_lift (fun c => isWordCharProp_to_isTagCharProp) h_gstar_word
    obtain ⟨sp', h_sfx, hcorr_sfx, h_gnot⟩ :=
      collectTagSuffixLoop_prod _ sp_mid hcorr_hdl
        ("!", (collectTagHandleLoop sc "" (inputEnd - sc.offset)).fst).snd
        (inputEnd - (collectTagHandleLoop sc "" (inputEnd - sc.offset)).snd.snd.offset) (by rw [collectTagHandleLoop_inputEnd]; omega)
    have h_full := gstar_append_local h_gstar_tag h_sfx
    by_cases h_ne : (⟨rest, col + 1⟩ : SurfPos) = sp'
    · -- empty suffix: the bare `!` is the non-specific tag [100]
      subst h_ne
      exact ⟨_, SCNsTagProperty.nonSpecific rest col h_gnot, corr_of_emitAt _ _ hcorr_sfx⟩
    · exact ⟨sp', SCNsTagProperty.primary rest col sp' (GStar_to_GPlus h_full h_ne) h_gnot,
             corr_of_emitAt _ _ hcorr_sfx⟩

-- `scanTag` on non-secondary branches produces `SCNsTagProperty`.
-- Handles verbatim `!<uri>`, named `!handle!suffix`, and non-specific `!`.
-- Verbatim well-formed case fully proven. S8/S9 closed via A10 Except + linking lemmas.
-- S10 closed via A16 scanNamedTag_prod decomposition.
lemma scanTag_nonSecondary_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '!') (hpeek2 : ¬(sc.advance.peek? = some '!'))
    (s' : ScannerState) (hok : scanTag sc = .ok s') :
    ∃ sp', SCNsTagProperty sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  have hcorr_bang := advance_non_newline_corr sc '!' rest hcorr
    hmore (by decide) (by decide)
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · -- sc.advance.peek? = some '<': verbatim tag
    rename_i hpeek_lt
    obtain ⟨rest2, hrest_eq⟩ := peek_some_sp hcorr_bang hpeek_lt
    have hchars_eq := congrArg SurfPos.chars hrest_eq
    dsimp only [] at hchars_eq; subst hchars_eq
    have hmore2 := peek_some_has_more hpeek_lt
    have hcorr_lt := advance_non_newline_corr sc.advance '<' rest2
      ⟨hcorr_bang.chars_from, rfl, hcorr_bang.end_eq, hcorr_bang.input_prefix, hcorr_bang.indent_cols_nonneg⟩
      hmore2 (by decide) (by decide)
    have hcorr_loop : ScannerSurfCorr sc.advance.advance ⟨rest2, sc.advance.advance.col⟩ :=
      ⟨hcorr_lt.chars_from, rfl, hcorr_lt.end_eq, hcorr_lt.input_prefix, hcorr_lt.indent_cols_nonneg⟩
    -- Separate the monadic bind from scanTag's do block
    simp only [bind, Except.bind] at hok
    generalize h_verb : scanVerbatimTag sc.advance sc.currentPos = verb_result at hok
    cases verb_result with
    | error e => simp at hok
    | ok s_verb =>
      -- hok has Pure.pure wrapped; normalize to Except.ok for injection
      change Except.ok { s_verb with simpleKeyAllowed := false } = Except.ok s' at hok
      have hok_eq := Except.ok.inj hok; subst hok_eq
      -- Unfold scanVerbatimTag at the clean h_verb (no Bind.bind wrapper)
      unfold scanVerbatimTag at h_verb; dsimp only [] at h_verb
      split at h_verb
      · exact absurd h_verb (by simp)  -- unterminatedVerbatimTag error
      · rename_i h_fc_true  -- ¬(!foundClose = true), i.e., foundClose = true
        split at h_verb
        · exact absurd h_verb (by simp)  -- emptyVerbatimTagURI error
        · rename_i h_uri_ne  -- ¬(uri.isEmpty = true), i.e., uri ≠ ""
          have h_sv := Except.ok.inj h_verb
          obtain ⟨sp_mid, sp', h_gstar, hcorr_uri, h_gt_or_eq, h_close_link, h_uri_link⟩ :=
            collectVerbatimTagLoop_prod sc.advance.advance ⟨rest2, sc.advance.advance.col⟩
              hcorr_loop "" _
          have hcol2 : sc.advance.advance.col = sc.col + 2 := by
            have := hcorr_bang.col_eq; have := hcorr_lt.col_eq; dsimp only [] at *; omega
          rw [hcol2] at h_gstar h_uri_link
          -- Build ScannerSurfCorr for { s_verb with simpleKeyAllowed := false }
          have hcorr_sv : ScannerSurfCorr s_verb sp' := by
            rw [← h_sv]; exact corr_of_emitAt _ _ hcorr_uri
          cases h_gt_or_eq with
          | inl h_eq =>
            -- S8: No '>' found — impossible since scanVerbatimTag returned .ok
            -- h_close_link gives foundClose = false, contradicting the split
            exfalso; simp [h_close_link h_eq] at h_fc_true
          | inr h_glit =>
            by_cases hne : ⟨rest2, sc.col + 2⟩ = sp_mid
            · -- S9: Empty URI !<> — impossible since scanVerbatimTag returned .ok
              -- h_uri_link gives uri = "", contradicting the split
              exfalso; simp [h_uri_link hne] at h_uri_ne
            · -- Well-formed !<uri>: construct verbatim evidence
              exact ⟨sp',
                     SCNsTagProperty.verbatim ('<' :: rest2) sc.col
                       ⟨rest2, sc.col + 2⟩ sp_mid sp'
                       (GLit.mk rest2 (sc.col + 1)) (GStar_to_GPlus h_gstar hne) h_glit,
                     corr_of_simpleKeyAllowed_update false hcorr_sv⟩
  · -- sc.advance.peek? = some '!': contradiction
    rename_i h_bang
    exact absurd h_bang hpeek2
  · -- catch-all: named/non-specific via scanNamedTag
    rename_i h_not_lt h_not_bang
    have h_inj := Except.ok.inj hok; subst h_inj
    have hcorr_adv : ScannerSurfCorr sc.advance ⟨rest, sc.col + 1⟩ :=
      ⟨hcorr_bang.chars_from, hcorr_bang.col_eq,
       hcorr_bang.end_eq, hcorr_bang.input_prefix, hcorr_bang.indent_cols_nonneg⟩
    obtain ⟨sp', h_tag, hcorr'⟩ := scanNamedTag_prod sc.advance rest sc.col
      hcorr_adv hpeek2 sc.currentPos sc.inputEnd (Nat.le_of_eq (advance_inputEnd sc))
    exact ⟨sp', h_tag, corr_of_simpleKeyAllowed_update false hcorr'⟩

-- `scanTag` preserves correspondence on all branches.
lemma scanTag_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanTag sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' :=
  scanTag_corr sc sp hcorr s' hok

/-! ## §4 Document Marker Productions

`scanDocumentStart` and `scanDocumentEnd` advance 3 characters past
`---` and `...` respectively. When the start position has `col = 0`
and the chars are the expected marker sequence, these produce
`SCDirectivesEnd` / `SCDocumentEnd` witnesses.

Helper: `unwindIndents_corr_exact` shows `unwindIndents` preserves the
exact surface position (not just existential). -/

-- `unwindIndentsLoop` preserves the exact surface position.
lemma unwindIndentsLoop_corr_exact (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) (fuel : Nat) :
    ScannerSurfCorr (unwindIndentsLoop sc col fuel) sp := by
  induction fuel generalizing sc with
  | zero => simp [unwindIndentsLoop]; exact hcorr
  | succ fuel' ih =>
    unfold unwindIndentsLoop; split
    · exact ih { (sc.emit .blockEnd) with indents := _, pendingKeys := _ }
        ⟨(corr_of_emit .blockEnd hcorr).chars_from,
         (corr_of_emit .blockEnd hcorr).col_eq,
         (corr_of_emit .blockEnd hcorr).end_eq, (corr_of_emit .blockEnd hcorr).input_prefix,
         fun i hi h0 => by
           simp only [ScannerState.emit] at hi ⊢
           rw [Array.getElem_pop]
           exact hcorr.indent_cols_nonneg i (by simp [Array.size_pop] at hi; omega) h0⟩
    · exact hcorr

-- `unwindIndents` preserves the exact surface position.
lemma unwindIndents_corr_exact (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) :
    ScannerSurfCorr (unwindIndents sc col) sp := by
  unfold unwindIndents
  exact unwindIndentsLoop_corr_exact sc sp hcorr col _

-- `scanDocumentStart` produces `SCDirectivesEnd` when chars = `---rest` at col 0.
lemma scanDocumentStart_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (rest : List Char) (hchars : sp.chars = '-' :: '-' :: '-' :: rest)
    (hcol : sp.col = 0) :
    ∃ sp', SCDirectivesEnd sp sp' ∧ ScannerSurfCorr (scanDocumentStart sc) sp' := by
  cases sp with | mk chars col =>
  dsimp only [] at hchars hcol ⊢
  subst hchars; subst hcol
  refine ⟨⟨rest, 3⟩, SCDirectivesEnd.mk rest, ?_⟩
  unfold scanDocumentStart
  simp only [ScannerState.advanceN, ScannerState.advanceNLoop]
  -- Thread through unwindIndents (preserves exact position)
  have hcorr_uw := unwindIndents_corr_exact sc ⟨'-' :: '-' :: '-' :: rest, 0⟩ hcorr (-1)
  have hcorr_key : ScannerSurfCorr
      { (unwindIndents sc (-1)) with simpleKey := { possible := false } }
      ⟨'-' :: '-' :: '-' :: rest, 0⟩ :=
    ⟨hcorr_uw.chars_from, hcorr_uw.col_eq, hcorr_uw.end_eq, hcorr_uw.input_prefix, hcorr_uw.indent_cols_nonneg⟩
  have hcorr_emit := corr_of_emit .documentStart hcorr_key
  -- Advance past first '-'
  have hcorr_at1 : ScannerSurfCorr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart)
      ⟨'-' :: '-' :: '-' :: rest,
       ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).col⟩ :=
    ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
  have hmore1 := corr_nonempty_has_more hcorr_at1
  have hcorr_adv1 := advance_non_newline_corr
    ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart)
    '-' ('-' :: '-' :: rest) hcorr_at1 hmore1 (by decide) (by decide)
  -- Advance past second '-'
  have hcorr_at2 : ScannerSurfCorr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance
      ⟨'-' :: '-' :: rest,
       ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance.col⟩ :=
    ⟨hcorr_adv1.chars_from, rfl, hcorr_adv1.end_eq, hcorr_adv1.input_prefix, hcorr_adv1.indent_cols_nonneg⟩
  have hmore2 := corr_nonempty_has_more hcorr_at2
  have hcorr_adv2 := advance_non_newline_corr
    ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance
    '-' ('-' :: rest) hcorr_at2 hmore2 (by decide) (by decide)
  -- Advance past third '-'
  have hcorr_at3 : ScannerSurfCorr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance.advance
      ⟨'-' :: rest,
       ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance.advance.col⟩ :=
    ⟨hcorr_adv2.chars_from, rfl, hcorr_adv2.end_eq, hcorr_adv2.input_prefix, hcorr_adv2.indent_cols_nonneg⟩
  have hmore3 := corr_nonempty_has_more hcorr_at3
  have hcorr_adv3 := advance_non_newline_corr
    ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance.advance
    '-' rest hcorr_at3 hmore3 (by decide) (by decide)
  -- Final: ScannerSurfCorr (scanDocumentStart sc) ⟨rest, 3⟩
  exact ⟨hcorr_adv3.chars_from,
         by have h0 := hcorr_emit.col_eq
            have h1 := hcorr_adv1.col_eq
            have h2 := hcorr_adv2.col_eq
            have h3 := hcorr_adv3.col_eq
            dsimp only [] at *; omega,
         hcorr_adv3.end_eq, hcorr_adv3.input_prefix, hcorr_adv3.indent_cols_nonneg⟩

-- `scanDocumentEnd` produces `SCDocumentEnd` when chars = `...rest` at col 0.
lemma scanDocumentEnd_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (rest : List Char) (hchars : sp.chars = '.' :: '.' :: '.' :: rest)
    (hcol : sp.col = 0)
    (s' : ScannerState) (hok : scanDocumentEnd sc = .ok s') :
    ∃ sp', SCDocumentEnd sp sp' ∧ ScannerSurfCorr s' sp' := by
  cases sp with | mk chars col =>
  dsimp only [] at hchars hcol ⊢
  subst hchars; subst hcol
  refine ⟨⟨rest, 3⟩, SCDocumentEnd.mk rest, ?_⟩
  -- Unfold and handle Except
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · exact absurd hok (by simp)
  · -- Build correspondence through unwindIndents + emit + advanceN 3
    have hcorr_uw := unwindIndents_corr_exact sc
      ⟨'.' :: '.' :: '.' :: rest, 0⟩ hcorr (-1)
    have hcorr_key : ScannerSurfCorr
        { (unwindIndents sc (-1)) with simpleKey := { possible := false } }
        ⟨'.' :: '.' :: '.' :: rest, 0⟩ :=
      ⟨hcorr_uw.chars_from, hcorr_uw.col_eq, hcorr_uw.end_eq, hcorr_uw.input_prefix, hcorr_uw.indent_cols_nonneg⟩
    have hcorr_emit := corr_of_emit .documentEnd hcorr_key
    -- Advance past first '.'
    have hcorr_at1 : ScannerSurfCorr
        ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd)
        ⟨'.' :: '.' :: '.' :: rest,
         ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).col⟩ :=
      ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
    have hmore1 := corr_nonempty_has_more hcorr_at1
    have hcorr_adv1 := advance_non_newline_corr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd)
      '.' ('.' :: '.' :: rest) hcorr_at1 hmore1 (by decide) (by decide)
    -- Advance past second '.'
    have hcorr_at2 : ScannerSurfCorr
        ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance
        ⟨'.' :: '.' :: rest,
         ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.col⟩ :=
      ⟨hcorr_adv1.chars_from, rfl, hcorr_adv1.end_eq, hcorr_adv1.input_prefix, hcorr_adv1.indent_cols_nonneg⟩
    have hmore2 := corr_nonempty_has_more hcorr_at2
    have hcorr_adv2 := advance_non_newline_corr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance
      '.' ('.' :: rest) hcorr_at2 hmore2 (by decide) (by decide)
    -- Advance past third '.'
    have hcorr_at3 : ScannerSurfCorr
        ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.advance
        ⟨'.' :: rest,
         ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.advance.col⟩ :=
      ⟨hcorr_adv2.chars_from, rfl, hcorr_adv2.end_eq, hcorr_adv2.input_prefix, hcorr_adv2.indent_cols_nonneg⟩
    have hmore3 := corr_nonempty_has_more hcorr_at3
    have hcorr_adv3 := advance_non_newline_corr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.advance
      '.' rest hcorr_at3 hmore3 (by decide) (by decide)
    -- Handle the validation match (all OK paths yield s' = result)
    -- Each OK branch gives s' = result; derive correspondence
    have mk_corr : ScannerSurfCorr
        { ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.advance.advance with
          simpleKeyAllowed := true, allowDirectives := true,
          directivesPresent := false, definedAnchors := #[],
          -- Item 317: the marker ends the explicit-key register (`scanDocumentEnd`).
          explicitKeyLine := none, explicitKeyCol := -1 }
        ⟨rest, 3⟩ := by
      exact ⟨hcorr_adv3.chars_from,
             by have h0 := hcorr_emit.col_eq
                have h1 := hcorr_adv1.col_eq
                have h2 := hcorr_adv2.col_eq
                have h3 := hcorr_adv3.col_eq
                dsimp only [] at *; omega,
             hcorr_adv3.end_eq, hcorr_adv3.input_prefix, hcorr_adv3.indent_cols_nonneg⟩
    split at hok
    · have h := Except.ok.inj hok; subst h; exact mk_corr
    · have h := Except.ok.inj hok; subst h; exact mk_corr
    · split at hok
      · have h := Except.ok.inj hok; subst h; exact mk_corr
      · exact absurd hok (by simp)

/-! ## §12 Directive scanning — grammar evidence

    Upgrade `scanDirective_prod` to return `GStar SCommentChar` evidence:
    all characters consumed after `%` are non-break.

    Each collect*Loop_prod is a fuel-induction mirror of the _corr version in
    StructureCoupling.lean, using `advance_non_newline_corr` (exact position)
    instead of `advance_corr` (existential position), and collecting
    `GStar SCommentChar` evidence at each step.

    The whitespace-to-nbchar bridge converts `GStar SSWhite → GStar SCommentChar`
    (whitespace chars are non-break). -/

-- After `skipToEndOfLine`, the scanner is at a line break or EOF.
-- Converts peek-level information to surface-position chars evidence.
-- Used by `scanDirective_prod` to give the break/EOF postcondition.
lemma skipToEndOfLineLoop_at_break_or_eof (sc : ScannerState) (fuel : Nat)
    (h_fuel : sc.offset + fuel ≥ sc.inputEnd) :
    let s' := skipToEndOfLineLoop sc fuel
    s'.peek? = none ∨ ∃ c, s'.peek? = some c ∧ isLineBreakBool c = true := by
  induction fuel generalizing sc with
  | zero =>
    simp [skipToEndOfLineLoop]
    left
    unfold ScannerState.peek?
    split
    · omega
    · rfl
  | succ fuel' ih =>
    simp only [skipToEndOfLineLoop]
    split
    · -- peek? = some c
      rename_i c hpeek
      split
      · -- isLineBreakBool c → return sc
        rename_i hlb
        exact Or.inr ⟨c, hpeek, hlb⟩
      · -- ¬isLineBreakBool c → recurse with advance
        exact ih sc.advance (by
          have h_lt := peek_some_has_more hpeek
          have h_ie := advance_inputEnd sc
          have h_adv := ScannerProgress.advance_offset_lt sc h_lt
          omega)
    · -- peek? = none → return sc
      exact Or.inl ‹_›

lemma skipToEndOfLine_at_break_or_eof (sc : ScannerState) :
    let s' := skipToEndOfLine sc
    s'.peek? = none ∨ ∃ c, s'.peek? = some c ∧ isLineBreakBool c = true := by
  unfold skipToEndOfLine
  exact skipToEndOfLineLoop_at_break_or_eof sc _ (by omega)

-- Surface-position version: after `skipToEndOfLine`, the surface position
-- has empty chars (EOF) or starts with a break character.
lemma skipToEndOfLine_at_break_or_eof_chars (sc : ScannerState)
    (sp' : SurfPos)
    (hcorr' : ScannerSurfCorr (skipToEndOfLine sc) sp') :
    sp'.chars = [] ∨ ∃ ch rest, sp'.chars = ch :: rest ∧ isLineBreakBool ch = true := by
  have h_peek := skipToEndOfLine_at_break_or_eof sc
  cases h_peek with
  | inl h_none =>
    -- peek? = none → chars = []
    have h_cf := hcorr'.chars_from
    cases sp' with | mk chars col =>
    dsimp only [] at h_cf h_none ⊢
    cases chars with
    | nil => exact Or.inl rfl
    | cons c rest =>
      -- CharsFromOffset gives offset < utf8ByteSize, but peek? = none → offset ≥ inputEnd
      cases h_cf with
      | cons _ h_lt _ _ _ _ =>
        have h_bound : (skipToEndOfLine sc).offset < (skipToEndOfLine sc).inputEnd := by
          rw [hcorr'.end_eq]; exact h_lt
        unfold ScannerState.peek? at h_none
        simp [h_bound] at h_none
  | inr h_break =>
    obtain ⟨c, hpeek, hlb⟩ := h_break
    obtain ⟨rest', rfl⟩ := peek_some_sp hcorr' hpeek
    exact Or.inr ⟨c, rest', rfl, hlb⟩

lemma GStar_SSWhite_to_GStar_SCommentChar {sp sp' : SurfPos}
    (h : GStar SSWhite sp sp') : GStar SCommentChar sp sp' := by
  induction h with
  | nil => exact GStar.nil _
  | cons _ _ _ hw _ ih =>
    cases hw with
    | space rest col =>
      exact GStar.cons _ _ _ (not_isLineBreak_gives_SCommentChar ' ' rest col (by decide)) ih
    | tab rest col =>
      exact GStar.cons _ _ _ (not_isLineBreak_gives_SCommentChar '\t' rest col (by decide)) ih

/-! ### `[82]` l-directive as the scanner cuts it (item 367)

    `scanDirective` reads `%`, a maximal ns-char name (`collectDirectiveNameLoop`),
    whites, and then one of three bodies — `YAML` (`digit+ . digit+`), `TAG`
    (handle, whites, prefix) or a reserved name (rest of line unvalidated) — each
    closed by `skipToEndOfLine`.  The loop lemmas below return the character
    class each loop accepts and, where the body needs it, maximality
    (`GNot (GChar _)` at the stop) off the fuel budget: every loop is called with
    `fuel = inputEnd - offset`, so fuel never runs out before EOF. -/

lemma isNsChar_iff_bool (c : Char) :
    isNsChar c ↔
      (!isWhiteSpaceBool c && !isLineBreakBool c && isPrintableBool c && c != '﻿') = true := by
  simp only [isNsChar, ← isWhiteSpace_iff, ← isLineBreak_iff, ← isPrintable_iff]
  cases h1 : isWhiteSpaceBool c <;> cases h2 : isLineBreakBool c <;>
    cases h3 : isPrintableBool c <;> simp [h1, h2, h3, bne_iff_ne]

lemma isNsDecDigit_of_isDigit {c : Char} (h : c.isDigit = true) : isNsDecDigit c := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

lemma not_isNsDecDigit_of_not_isDigit {c : Char} (h : ¬ c.isDigit = true) :
    ¬ isNsDecDigit c := by
  intro hd; simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, not_and] at h
  exact h hd.1 hd.2

lemma isTagHandleChar_iff_bool (c : Char) :
    (isWordCharBool c || c == '!') = true ↔ (isWordCharProp c ∨ c = '!') := by
  simp [isWordChar_iff]

lemma collectDirectiveNameLoop_inputEnd (sc : ScannerState) (name : String) (fuel : Nat) :
    (collectDirectiveNameLoop sc name fuel).snd.inputEnd = sc.inputEnd := by
  induction fuel generalizing sc name with
  | zero => simp [collectDirectiveNameLoop]
  | succ fuel' ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · exact (ih _ _).trans (advance_inputEnd sc)
      · rfl
    · rfl

lemma collectVersionMajorLoop_inputEnd (sc : ScannerState) (major : String) (fuel : Nat) :
    (collectVersionMajorLoop sc major fuel).snd.inputEnd = sc.inputEnd := by
  induction fuel generalizing sc major with
  | zero => simp [collectVersionMajorLoop]
  | succ fuel' ih =>
    unfold collectVersionMajorLoop; split
    · exact advance_inputEnd sc
    · split
      · exact (ih _ _).trans (advance_inputEnd sc)
      · rfl
    · rfl

/-- The directive name: a maximal run of ns-chars after the `%`, returned as the
    characters the scanner pushed (so `name == "YAML"` can be read off it) with
    the stop position's maximality. -/
lemma collectDirectiveNameLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (name : String) (fuel : Nat)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset) :
    ∃ (nm : List Char) (sp' : SurfPos),
      sp.chars = nm ++ sp'.chars ∧ sp'.col = sp.col + nm.length ∧
      (∀ c ∈ nm, isNsChar c) ∧
      (collectDirectiveNameLoop sc name fuel).fst.toList = name.toList ++ nm ∧
      GNot (GChar isNsChar) sp' ∧
      ScannerSurfCorr (collectDirectiveNameLoop sc name fuel).snd sp' := by
  induction fuel generalizing sc sp name with
  | zero =>
    simp only [collectDirectiveNameLoop]
    exact ⟨[], sp, by simp, by simp, by simp, by simp,
      gnot_gchar_of_peek_none hcorr (peek_none_of_fuel_zero hfuel), hcorr⟩
  | succ fuel' ih =>
    unfold collectDirectiveNameLoop; split
    · rename_i c hpeek; split
      · rename_i h_pred
        have h_ns : isNsChar c := (isNsChar_iff_bool c).mpr h_pred
        have h_nlb : ¬isLineBreakBool c = true := by
          intro h; simp [h] at h_pred
        obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
        have hmore := corr_nonempty_has_more hcorr
        have hadv := advance_non_newline_corr sc c rest hcorr hmore
          (not_isLineBreak_not_newline c h_nlb) (not_isLineBreak_not_cr c h_nlb)
        obtain ⟨nm, sp', hchars, hcol, hall, hname, hnot, hcorr'⟩ :=
          ih sc.advance ⟨rest, sc.col + 1⟩ hadv (name.push c)
            (advance_fuel_budget sc fuel' hmore hfuel)
        refine ⟨c :: nm, sp', ?_, ?_, ?_, ?_, hnot, hcorr'⟩
        · simp only [List.cons_append]; exact congrArg (c :: ·) hchars
        · dsimp only at hcol; simp only [List.length_cons]; omega
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact h_ns
          · exact hall d hd
        · rw [hname]; simp
      · rename_i h_pred
        obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
        exact ⟨[], _, by simp, by simp, by simp, by simp,
          gnot_gchar_head (fun h => h_pred ((isNsChar_iff_bool c).mp h)), hcorr⟩
    · rename_i hpeek
      exact ⟨[], sp, by simp, by simp, by simp, by simp,
        gnot_gchar_of_peek_none hcorr hpeek, hcorr⟩

-- Printable-ASCII bridges for the nb-char [27] conjuncts: every character
-- class the directive/tag loops accept sits inside `[#x20-#x7E]`, hence is
-- `c-printable` and not the BOM.
lemma isPrintableBool_of_ascii {c : Char}
    (h1 : 0x20 ≤ c.val) (h2 : c.val ≤ 0x7E) : isPrintableBool c = true := by
  simp only [isPrintableBool, decide_eq_true_eq]
  unfold isPrintableProp
  exact Or.inr (Or.inl ⟨h1, h2⟩)

lemma not_bom_of_ascii {c : Char} (h2 : c.val ≤ 0x7E) : (c == '﻿') = false := by
  cases hb : (c == '﻿') with
  | false => rfl
  | true => exact absurd (eq_of_beq hb ▸ h2) (by decide)

lemma isDigit_not_isLineBreak (c : Char) (h : c.isDigit = true) :
    ¬isLineBreakBool c = true := by
  intro hlb; simp [isLineBreakBool, isLineFeedBool, isCarriageReturnBool] at hlb
  cases hlb with
  | inl h1 => subst h1; simp [Char.isDigit] at h
  | inr h1 => subst h1; simp [Char.isDigit] at h

lemma isDigit_ascii (c : Char) (h : c.isDigit = true) :
    0x20 ≤ c.val ∧ c.val ≤ 0x7E := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨UInt32.le_trans (by decide) h1, UInt32.le_trans h2 (by decide)⟩

lemma isWordCharOrBang_ascii (c : Char)
    (h : (isWordCharBool c || c == '!') = true) :
    0x20 ≤ c.val ∧ c.val ≤ 0x7E := by
  simp only [Bool.or_eq_true, isWordCharBool, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | rfl
  · unfold isWordCharProp isAsciiLetterProp at h
    rcases h with ⟨h1, h2⟩ | (⟨h1, h2⟩ | ⟨h1, h2⟩) | rfl
    · exact ⟨UInt32.le_trans (by decide) h1, UInt32.le_trans h2 (by decide)⟩
    · exact ⟨UInt32.le_trans (by decide) h1, UInt32.le_trans h2 (by decide)⟩
    · exact ⟨UInt32.le_trans (by decide) h1, UInt32.le_trans h2 (by decide)⟩
    · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

lemma isUriChar_ascii (c : Char) (h : isUriCharBool c = true) :
    0x20 ≤ c.val ∧ c.val ≤ 0x7E := by
  simp only [isUriCharBool, decide_eq_true_eq] at h
  unfold isUriCharProp at h
  rcases h with h | h
  · exact isWordCharOrBang_ascii c (by simp [isWordCharBool, h])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide⟩

/-- The run a digit loop pushed, as a grammar fact: empty and stationary, or a
    `[35] ns-dec-digit+` to the stop. -/
def DigitRun (ds : List Char) (sp sp₁ : SurfPos) : Prop :=
  (ds = [] ∧ sp₁ = sp) ∨ (ds ≠ [] ∧ GPlus (GChar isNsDecDigit) sp sp₁)

lemma DigitRun.cons {c : Char} {rest : List Char} {col : Nat} {ds : List Char} {sp₁ : SurfPos}
    (hd : isNsDecDigit c) (h : DigitRun ds ⟨rest, col + 1⟩ sp₁) :
    DigitRun (c :: ds) ⟨c :: rest, col⟩ sp₁ := by
  refine Or.inr ⟨List.cons_ne_nil _ _, GPlus.mk _ ⟨rest, col + 1⟩ _ (GChar.mk c rest col hd) ?_⟩
  rcases h with ⟨_, rfl⟩ | ⟨_, hp⟩
  · exact GStar.nil _
  · exact GPlus_to_GStar hp

lemma DigitRun.plus_of_ne {ds : List Char} {sp sp₁ : SurfPos} (h : DigitRun ds sp sp₁)
    (hne : ds ≠ []) : GPlus (GChar isNsDecDigit) sp sp₁ := by
  rcases h with ⟨h, _⟩ | ⟨_, hp⟩
  · exact absurd h hne
  · exact hp

lemma DigitRun.nil_of_gnot {ds : List Char} {sp sp₁ : SurfPos} (h : DigitRun ds sp sp₁)
    (hnot : GNot (GChar isNsDecDigit) sp) : ds = [] := by
  rcases h with ⟨h, _⟩ | ⟨_, hp⟩
  · exact h
  · cases hp with
    | mk _ _ hfirst _ => exact absurd hfirst (hnot _)

/-- `[86]`'s major part: the digits pushed and, at the stop, either the `.`
    consumed or a non-digit left in place (maximality). -/
lemma collectVersionMajorLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (major : String) (fuel : Nat)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset) :
    ∃ (ds : List Char) (sp₁ : SurfPos),
      (collectVersionMajorLoop sc major fuel).fst.toList = major.toList ++ ds ∧
      DigitRun ds sp sp₁ ∧
      ((∃ sp₂, GLit '.' sp₁ sp₂ ∧
          ScannerSurfCorr (collectVersionMajorLoop sc major fuel).snd sp₂) ∨
        (GNot (GChar isNsDecDigit) sp₁ ∧
          ScannerSurfCorr (collectVersionMajorLoop sc major fuel).snd sp₁)) := by
  induction fuel generalizing sc sp major with
  | zero =>
    simp only [collectVersionMajorLoop]
    exact ⟨[], sp, by simp, Or.inl ⟨rfl, rfl⟩,
      Or.inr ⟨gnot_gchar_of_peek_none hcorr (peek_none_of_fuel_zero hfuel), hcorr⟩⟩
  | succ fuel' ih =>
    unfold collectVersionMajorLoop; split
    · -- peek? = some '.'
      rename_i hpeek
      obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
      have hmore := corr_nonempty_has_more hcorr
      have hadv := advance_non_newline_corr sc '.' rest hcorr hmore (by decide) (by decide)
      exact ⟨[], _, by simp, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, hadv⟩⟩
    · -- peek? = some c (c ≠ '.')
      rename_i c _ hpeek; split
      · rename_i h_dig
        have h_nlb := isDigit_not_isLineBreak c h_dig
        obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
        have hmore := corr_nonempty_has_more hcorr
        have hadv := advance_non_newline_corr sc c rest hcorr hmore
          (not_isLineBreak_not_newline c h_nlb) (not_isLineBreak_not_cr c h_nlb)
        obtain ⟨ds, sp₁, hname, hrun, htail⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ hadv _
          (advance_fuel_budget sc fuel' hmore hfuel)
        exact ⟨c :: ds, sp₁, by rw [hname]; simp, hrun.cons (isNsDecDigit_of_isDigit h_dig), htail⟩
      · rename_i h_dig
        obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
        exact ⟨[], _, by simp, Or.inl ⟨rfl, rfl⟩,
          Or.inr ⟨gnot_gchar_head (not_isNsDecDigit_of_not_isDigit h_dig), hcorr⟩⟩
    · rename_i hpeek
      exact ⟨[], sp, by simp, Or.inl ⟨rfl, rfl⟩,
        Or.inr ⟨gnot_gchar_of_peek_none hcorr hpeek, hcorr⟩⟩

/-- `[86]`'s minor part: the digits pushed, maximal at the stop. -/
lemma collectVersionMinorLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (minor : String) (fuel : Nat)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset) :
    ∃ (ds : List Char) (sp₁ : SurfPos),
      (collectVersionMinorLoop sc minor fuel).fst.toList = minor.toList ++ ds ∧
      DigitRun ds sp sp₁ ∧
      GNot (GChar isNsDecDigit) sp₁ ∧
      ScannerSurfCorr (collectVersionMinorLoop sc minor fuel).snd sp₁ := by
  induction fuel generalizing sc sp minor with
  | zero =>
    simp only [collectVersionMinorLoop]
    exact ⟨[], sp, by simp, Or.inl ⟨rfl, rfl⟩,
      gnot_gchar_of_peek_none hcorr (peek_none_of_fuel_zero hfuel), hcorr⟩
  | succ fuel' ih =>
    unfold collectVersionMinorLoop; split
    · rename_i c hpeek; split
      · rename_i h_dig
        have h_nlb := isDigit_not_isLineBreak c h_dig
        obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
        have hmore := corr_nonempty_has_more hcorr
        have hadv := advance_non_newline_corr sc c rest hcorr hmore
          (not_isLineBreak_not_newline c h_nlb) (not_isLineBreak_not_cr c h_nlb)
        obtain ⟨ds, sp₁, hname, hrun, hnot, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ hadv
          (minor.push c) (advance_fuel_budget sc fuel' hmore hfuel)
        exact ⟨c :: ds, sp₁, by rw [hname]; simp,
          hrun.cons (isNsDecDigit_of_isDigit h_dig), hnot, hcorr'⟩
      · rename_i h_dig
        obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
        exact ⟨[], _, by simp, Or.inl ⟨rfl, rfl⟩,
          gnot_gchar_head (not_isNsDecDigit_of_not_isDigit h_dig), hcorr⟩
    · rename_i hpeek
      exact ⟨[], sp, by simp, Or.inl ⟨rfl, rfl⟩, gnot_gchar_of_peek_none hcorr hpeek, hcorr⟩

lemma isWordCharOrBang_not_isLineBreak (c : Char)
    (h : (isWordCharBool c || c == '!') = true) :
    ¬isLineBreakBool c = true := by
  intro hlb; simp [isLineBreakBool, isLineFeedBool, isCarriageReturnBool] at hlb
  simp [isWordCharBool, isWordCharProp, isAsciiLetterProp] at h
  rcases hlb with rfl | rfl <;> simp_all

/-- `[89]` c-tag-handle characters: `[38] ns-word-char` or `!`, a maximal run (the stop off
    the fuel budget, as for the name). -/
lemma collectTagHandleDirectiveLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (handle : String) (fuel : Nat)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset) :
    ∃ sp', GStar (GChar (fun c => isWordCharProp c ∨ c = '!')) sp sp' ∧
      GNot (GChar (fun c => isWordCharProp c ∨ c = '!')) sp' ∧
      ScannerSurfCorr (collectTagHandleDirectiveLoop sc handle fuel).snd sp' := by
  induction fuel generalizing sc sp handle with
  | zero =>
    simp only [collectTagHandleDirectiveLoop]
    exact ⟨sp, GStar.nil _, gnot_gchar_of_peek_none hcorr (peek_none_of_fuel_zero hfuel), hcorr⟩
  | succ fuel' ih =>
    unfold collectTagHandleDirectiveLoop; split
    · rename_i c hpeek; split
      · rename_i h_pred
        have h_nlb := isWordCharOrBang_not_isLineBreak c h_pred
        obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
        have hmore := corr_nonempty_has_more hcorr
        have hadv := advance_non_newline_corr sc c rest hcorr hmore
          (not_isLineBreak_not_newline c h_nlb) (not_isLineBreak_not_cr c h_nlb)
        obtain ⟨sp', hstar, hnot, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ hadv (handle.push c)
          (advance_fuel_budget sc fuel' hmore hfuel)
        exact ⟨sp', GStar.cons _ _ _
          (GChar.mk c rest sc.col ((isTagHandleChar_iff_bool c).mp h_pred)) hstar, hnot, hcorr'⟩
      · rename_i h_pred
        obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
        exact ⟨_, GStar.nil _, gnot_gchar_head (fun h => h_pred ((isTagHandleChar_iff_bool c).mpr h)), hcorr⟩
    · rename_i hpeek
      exact ⟨sp, GStar.nil _, gnot_gchar_of_peek_none hcorr hpeek, hcorr⟩

lemma isUriChar_not_isLineBreak (c : Char)
    (h : isUriCharBool c = true) :
    ¬isLineBreakBool c = true := by
  intro hlb; simp [isLineBreakBool, isLineFeedBool, isCarriageReturnBool] at hlb
  simp [isUriCharBool, isUriCharProp, isWordCharProp, isAsciiLetterProp] at h
  rcases hlb with rfl | rfl <;> simp_all

/-- `[93]` ns-tag-prefix characters: `[39] ns-uri-char`. -/
lemma collectTagPrefixLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (pfx : String) (fuel : Nat) :
    ∃ sp', GStar (GChar isUriCharProp) sp sp' ∧
      ScannerSurfCorr (collectTagPrefixLoop sc pfx fuel).snd sp' := by
  induction fuel generalizing sc sp pfx with
  | zero => simp [collectTagPrefixLoop]; exact ⟨sp, GStar.nil _, hcorr⟩
  | succ fuel' ih =>
    unfold collectTagPrefixLoop; split
    · rename_i c hpeek; split
      · rename_i h_pred
        have h_nlb := isUriChar_not_isLineBreak c h_pred
        obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
        have hmore := corr_nonempty_has_more hcorr
        have hadv := advance_non_newline_corr sc c rest hcorr hmore
          (not_isLineBreak_not_newline c h_nlb) (not_isLineBreak_not_cr c h_nlb)
        obtain ⟨sp', hstar, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ hadv (pfx.push c)
        exact ⟨sp', GStar.cons _ _ _
          (GChar.mk c rest sc.col ((isUriChar_iff c).mp h_pred)) hstar, hcorr'⟩
      · exact ⟨sp, GStar.nil _, hcorr⟩
    · exact ⟨sp, GStar.nil _, hcorr⟩

/-- Where a `%YAML`/`%TAG` line may stop after its last parameter, as the
    scanner's `directiveTrailingContent` check reads it: EOF, a break, or a `#`
    that at least one white separated from the parameter. -/
def DirectiveStop (a b : SurfPos) : Prop :=
  b.chars = [] ∨ (∃ ch r, b.chars = ch :: r ∧ isLineBreakBool ch = true) ∨
    (∃ r, b.chars = '#' :: r ∧ b.col ≠ a.col)

/-- What the scanner leaves between a directive's last parameter and the line
    stop: the whites it skipped, a `DirectiveStop`, and the comment text
    `skipToEndOfLine` swallowed up to the break. -/
def DirectiveTail (a c : SurfPos) : Prop :=
  ∃ b, GStar SSWhite a b ∧ DirectiveStop a b ∧ GStar SCommentChar b c

/-- A run whose characters all satisfy `P`, as the `GStar (GChar P)` from its start to its end. -/
lemma gstar_gchar_of_all {P : Char → Prop} (nm tail : List Char) (col : Nat)
    (h : ∀ c ∈ nm, P c) : GStar (GChar P) ⟨nm ++ tail, col⟩ ⟨tail, col + nm.length⟩ := by
  induction nm generalizing col with
  | nil => simp only [List.nil_append, List.length_nil, Nat.add_zero]; exact GStar.nil _
  | cons c nm ih =>
    have hc := h c (List.mem_cons.mpr (Or.inl rfl))
    have hrest := ih (col + 1) (fun d hd => h d (List.mem_cons.mpr (Or.inr hd)))
    simp only [List.cons_append, List.length_cons]
    rw [show col + (nm.length + 1) = col + 1 + nm.length by omega]
    exact GStar.cons _ ⟨nm ++ tail, col + 1⟩ _ (GChar.mk c (nm ++ tail) col hc) hrest

/-- `[82]` as `scanDirective` cuts a line: the three bodies of `SLDirective`
    with the tail still in scanner form.  `ScannedDirective.toSLDirective`
    (StreamAccum) attaches the `s-l-comments` the next step supplies. -/
inductive ScannedDirective : SurfPos → SurfPos → Prop where
  | yaml (rest : List Char) (col : Nat) (s₁ s₂ s₃ s₄ s' : SurfPos) :
      GNot (GChar isNsChar) ⟨rest, col + 5⟩ →
      GStar SSWhite ⟨rest, col + 5⟩ s₁ →
      GPlus (GChar isNsDecDigit) s₁ s₂ →
      GLit '.' s₂ s₃ →
      GPlus (GChar isNsDecDigit) s₃ s₄ →
      DirectiveTail s₄ s' →
      ScannedDirective ⟨'%' :: 'Y' :: 'A' :: 'M' :: 'L' :: rest, col⟩ s'
  | tag (rest : List Char) (col : Nat) (s₁ s₂ s₃ s₄ s' : SurfPos) :
      GNot (GChar isNsChar) ⟨rest, col + 4⟩ →
      GStar SSWhite ⟨rest, col + 4⟩ s₁ →
      GStar (GChar (fun c => isWordCharProp c ∨ c = '!')) s₁ s₂ →
      GNot (GChar (fun c => isWordCharProp c ∨ c = '!')) s₂ →
      GStar SSWhite s₂ s₃ →
      GStar (GChar isUriCharProp) s₃ s₄ →
      DirectiveTail s₄ s' →
      ScannedDirective ⟨'%' :: 'T' :: 'A' :: 'G' :: rest, col⟩ s'
  | reserved (rest : List Char) (col : Nat) (s₀ s' : SurfPos) :
      GStar (GChar isNsChar) ⟨rest, col + 1⟩ s₀ →
      GNot (GChar isNsChar) s₀ →
      rest ≠ 'Y' :: 'A' :: 'M' :: 'L' :: s₀.chars →
      rest ≠ 'T' :: 'A' :: 'G' :: s₀.chars →
      GStar SCommentChar s₀ s' →
      ScannedDirective ⟨'%' :: rest, col⟩ s'

/-- The trailing-content check of `scanYamlDirective`/`scanTagDirective`, read
    on the surface: after the whites, the cursor is at a `DirectiveStop`. -/
lemma directiveStop_of_validated {s_before s_v : ScannerState} {sp_before sp_v : SurfPos}
    (hcorr_before : ScannerSurfCorr s_before sp_before)
    (hcorr_v : ScannerSurfCorr s_v sp_v)
    (h : s_v.peek? = none ∨ (∃ c, s_v.peek? = some c ∧ isLineBreakBool c = true) ∨
      (s_v.peek? = some '#' ∧ ¬ (s_v.col == s_before.col) = true)) :
    DirectiveStop sp_before sp_v := by
  rcases h with h | ⟨c, hpeek, hlb⟩ | ⟨hpeek, hcol⟩
  · exact Or.inl (peek_none_chars_nil hcorr_v h)
  · obtain ⟨rest, rfl⟩ := peek_some_sp hcorr_v hpeek
    exact Or.inr (Or.inl ⟨c, rest, rfl, hlb⟩)
  · obtain ⟨rest, rfl⟩ := peek_some_sp hcorr_v hpeek
    refine Or.inr (Or.inr ⟨rest, rfl, ?_⟩)
    show s_v.col ≠ sp_before.col
    rw [hcorr_before.col_eq]
    exact fun heq => hcol (beq_iff_eq.mpr heq)

lemma scanYamlDirective_prod (sc : ScannerState)
    (s_after_ws : ScannerState) (sp_ws : SurfPos)
    (hcorr_ws : ScannerSurfCorr s_after_ws sp_ws)
    (hend : s_after_ws.inputEnd = sc.inputEnd)
    (startPos : YamlPos) (s' : ScannerState)
    (hok : scanYamlDirective sc s_after_ws startPos = .ok s') :
    ∃ s₂ s₃ s₄ sp_v, GPlus (GChar isNsDecDigit) sp_ws s₂ ∧ GLit '.' s₂ s₃ ∧
      GPlus (GChar isNsDecDigit) s₃ s₄ ∧
      GStar SSWhite s₄ sp_v ∧ DirectiveStop s₄ sp_v ∧
      ScannerSurfCorr s' sp_v := by
  unfold scanYamlDirective at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · exact absurd hok (by simp)
  · obtain ⟨ds, sp₁, h_maj, h_run_maj, h_tail_maj⟩ :=
      collectVersionMajorLoop_prod s_after_ws sp_ws hcorr_ws "" (sc.inputEnd - s_after_ws.offset)
        (Nat.le_of_eq (by rw [hend]))
    have hend_dot : (collectVersionMajorLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).snd.inputEnd
        = sc.inputEnd := by rw [collectVersionMajorLoop_inputEnd, hend]
    -- The stop shape and the two non-empty checks are the same in every `.ok` arm.
    suffices finish : ∀ (s_v : ScannerState),
        (s_v = skipWhitespace (collectVersionMinorLoop
          (collectVersionMajorLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).snd ""
          (sc.inputEnd - (collectVersionMajorLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).snd.offset)).snd) →
        (s_v.peek? = none ∨ (∃ c, s_v.peek? = some c ∧ isLineBreakBool c = true) ∨
          (s_v.peek? = some '#' ∧ ¬ (s_v.col == (collectVersionMinorLoop
            (collectVersionMajorLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).snd ""
            (sc.inputEnd - (collectVersionMajorLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).snd.offset)).snd.col) = true)) →
        ¬ ((collectVersionMajorLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).fst.isEmpty ||
           (collectVersionMinorLoop
            (collectVersionMajorLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).snd ""
            (sc.inputEnd - (collectVersionMajorLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).snd.offset)).fst.isEmpty) = true →
        (∀ sp_v, ScannerSurfCorr s_v sp_v → ScannerSurfCorr s' sp_v) →
        ∃ s₂ s₃ s₄ sp_v, GPlus (GChar isNsDecDigit) sp_ws s₂ ∧ GLit '.' s₂ s₃ ∧
          GPlus (GChar isNsDecDigit) s₃ s₄ ∧
          GStar SSWhite s₄ sp_v ∧ DirectiveStop s₄ sp_v ∧ ScannerSurfCorr s' sp_v by
      split at hok
      · -- `#`
        rename_i hpeek
        split at hok
        · exact absurd hok (by simp)
        · rename_i hcol
          split at hok
          · exact absurd hok (by simp)
          · rename_i hne
            have h := Except.ok.inj hok; subst h
            exact finish _ rfl (Or.inr (Or.inr ⟨hpeek, hcol⟩)) hne
              (fun sp_v hc => ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩)
      · -- some c
        rename_i c _ hpeek
        split at hok
        · exact absurd hok (by simp)
        · rename_i hlb
          split at hok
          · exact absurd hok (by simp)
          · rename_i hne
            have h := Except.ok.inj hok; subst h
            exact finish _ rfl (Or.inr (Or.inl ⟨c, hpeek, by simpa using hlb⟩)) hne
              (fun sp_v hc => ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩)
      · -- none
        rename_i hpeek
        split at hok
        · exact absurd hok (by simp)
        · rename_i hne
          have h := Except.ok.inj hok; subst h
          exact finish _ rfl (Or.inl hpeek) hne
            (fun sp_v hc => ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩)
    intro s_v hs_v hstop hne hcorr_lift
    subst hs_v
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hne
    have h_maj_ne : ds ≠ [] := by
      intro hds; rw [hds, List.append_nil] at h_maj
      have h1 : (collectVersionMajorLoop s_after_ws "" (sc.inputEnd - s_after_ws.offset)).fst.toList ≠ [] := by
        simpa using hne.1
      exact h1 (by rw [h_maj]; simp)
    have h_plus_maj := h_run_maj.plus_of_ne h_maj_ne
    -- The minor loop runs from wherever the major loop stopped.
    rcases h_tail_maj with ⟨sp₂, hdot, hcorr_dot⟩ | ⟨hnot₁, hcorr₁⟩
    · obtain ⟨ds', sp₃, h_min, h_run_min, _, hcorr_min⟩ :=
        collectVersionMinorLoop_prod _ sp₂ hcorr_dot "" _ (Nat.le_of_eq (by rw [hend_dot]))
      have h_min_ne : ds' ≠ [] := by
        intro hds; rw [hds, List.append_nil] at h_min
        have hX : _ = ("" : String) := String.ext h_min
        rw [hX] at hne; exact absurd hne.2 (by decide)
      obtain ⟨sp_v, h_ws, hcorr_v⟩ := skipWhitespace_corr _ sp₃ hcorr_min
      exact ⟨sp₁, sp₂, sp₃, sp_v, h_plus_maj, hdot, h_run_min.plus_of_ne h_min_ne, h_ws,
        directiveStop_of_validated hcorr_min hcorr_v hstop, hcorr_lift sp_v hcorr_v⟩
    · -- No `.`: the minor run is empty, refused by the `isEmpty` check.
      obtain ⟨ds', sp₃, h_min, h_run_min, _, _⟩ :=
        collectVersionMinorLoop_prod _ sp₁ hcorr₁ "" _ (Nat.le_of_eq (by rw [hend_dot]))
      have hds' : ds' = [] := h_run_min.nil_of_gnot hnot₁
      rw [hds', List.append_nil] at h_min
      have hX : _ = ("" : String) := String.ext h_min
      rw [hX] at hne; exact absurd hne.2 (by decide)

lemma scanTagDirective_prod
    (s_after_ws : ScannerState) (sp_ws : SurfPos)
    (hcorr_ws : ScannerSurfCorr s_after_ws sp_ws)
    (sc : ScannerState) (hend : s_after_ws.inputEnd = sc.inputEnd)
    (startPos : YamlPos) (s' : ScannerState)
    (hok : scanTagDirective sc s_after_ws startPos = .ok s') :
    ∃ s₂ s₃ s₄ sp_v, GStar (GChar (fun c => isWordCharProp c ∨ c = '!')) sp_ws s₂ ∧
      GNot (GChar (fun c => isWordCharProp c ∨ c = '!')) s₂ ∧
      GStar SSWhite s₂ s₃ ∧ GStar (GChar isUriCharProp) s₃ s₄ ∧
      GStar SSWhite s₄ sp_v ∧ DirectiveStop s₄ sp_v ∧
      ScannerSurfCorr s' sp_v := by
  unfold scanTagDirective at hok
  simp only [bind, Except.bind] at hok
  obtain ⟨sp_hdl, h_hdl, h_hnot, hcorr_hdl⟩ :=
    collectTagHandleDirectiveLoop_prod s_after_ws sp_ws hcorr_ws "" (sc.inputEnd - s_after_ws.offset)
      (Nat.le_of_eq (by rw [hend]))
  obtain ⟨sp_ws2, h_ws, hcorr_ws2⟩ := skipWhitespace_corr _ sp_hdl hcorr_hdl
  obtain ⟨sp_pfx, h_pfx, hcorr_pfx⟩ := collectTagPrefixLoop_prod _ sp_ws2 hcorr_ws2 "" _
  obtain ⟨sp_val, h_ws_val, hcorr_val⟩ := skipWhitespace_corr _ sp_pfx hcorr_pfx
  have lift : ∀ (s_v : ScannerState) (sp_v : SurfPos), ScannerSurfCorr s_v sp_v →
      ∀ (startPos : YamlPos) (h t : String),
      ScannerSurfCorr { s_v.emitAt startPos (.tagDirective h t) with directivesPresent := true } sp_v :=
    fun _ _ hc _ _ _ => ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩
  split at hok
  · contradiction  -- [89]: a malformed `%TAG` handle is refused
  split at hok
  · rename_i hpeek
    split at hok
    · exact absurd hok (by simp)
    · rename_i hcol
      have h := Except.ok.inj hok; subst h
      exact ⟨sp_hdl, sp_ws2, sp_pfx, sp_val, h_hdl, h_hnot, h_ws, h_pfx, h_ws_val,
        directiveStop_of_validated hcorr_pfx hcorr_val (Or.inr (Or.inr ⟨hpeek, hcol⟩)),
        lift _ _ hcorr_val _ _ _⟩
  · rename_i c _ hpeek
    split at hok
    · exact absurd hok (by simp)
    · rename_i hlb
      have h := Except.ok.inj hok; subst h
      exact ⟨sp_hdl, sp_ws2, sp_pfx, sp_val, h_hdl, h_hnot, h_ws, h_pfx, h_ws_val,
        directiveStop_of_validated hcorr_pfx hcorr_val (Or.inr (Or.inl ⟨c, hpeek, by simpa using hlb⟩)),
        lift _ _ hcorr_val _ _ _⟩
  · rename_i hpeek
    have h := Except.ok.inj hok; subst h
    exact ⟨sp_hdl, sp_ws2, sp_pfx, sp_val, h_hdl, h_hnot, h_ws, h_pfx, h_ws_val,
      directiveStop_of_validated hcorr_pfx hcorr_val (Or.inl hpeek),
      lift _ _ hcorr_val _ _ _⟩

/-- `scanDirective` produces `[82]` as the scanner cuts it (`ScannedDirective`),
    ending at a break or EOF (every branch closes with `skipToEndOfLine`).
    Requires `hpeek` (the caller dispatches on `sc.peek? = some '%'`). -/
lemma scanDirective_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '%')
    (s' : ScannerState) (hok : scanDirective sc = .ok s') :
    ∃ sp', ScannedDirective sp sp' ∧ ScannerSurfCorr s' sp' ∧
      (sp'.chars = [] ∨ ∃ ch rest', sp'.chars = ch :: rest' ∧ isLineBreakBool ch = true) := by
  obtain ⟨rest, rfl⟩ := peek_some_sp hcorr hpeek
  unfold scanDirective at hok
  split at hok
  · exact absurd hok (by simp)
  · dsimp only [] at hok
    have hmore := corr_nonempty_has_more hcorr
    have hcorr_pct := advance_non_newline_corr sc '%' rest
      ⟨hcorr.chars_from, rfl, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
      hmore (by decide) (by decide)
    obtain ⟨nm, sp_name, hchars, hcol, hall, hname, hnot, hcorr_name⟩ :=
      collectDirectiveNameLoop_prod sc.advance ⟨rest, sc.col + 1⟩ hcorr_pct ""
        (sc.inputEnd - sc.advance.offset) (Nat.le_of_eq (by rw [advance_inputEnd]))
    simp only [String.toList_empty, List.nil_append] at hname
    obtain ⟨sp_ws, h_ws, hcorr_ws⟩ := skipWhitespace_corr _ sp_name hcorr_name
    have hend_ws : (skipWhitespace (collectDirectiveNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).snd).inputEnd
        = sc.inputEnd := by
      rw [skipWhitespace_inputEnd', collectDirectiveNameLoop_inputEnd, advance_inputEnd]
    obtain ⟨tail, tcol⟩ := sp_name
    simp only at hchars hcol
    subst hchars
    split at hok
    · -- `%YAML`
      rename_i h_y
      have hnm : nm = ['Y', 'A', 'M', 'L'] := by
        have := congrArg String.toList (eq_of_beq h_y); rw [hname] at this; simpa using this
      subst hnm
      have hcol5 : tcol = sc.col + 5 := by simp at hcol; omega
      subst hcol5
      split at hok
      · rename_i s_yaml h_yaml_ok
        have h_eol := Except.ok.inj hok; subst h_eol
        obtain ⟨s₂, s₃, s₄, sp_v, hd1, hdot, hd2, h_wsv, hstop, hcorr_v⟩ :=
          scanYamlDirective_prod sc _ sp_ws hcorr_ws hend_ws _ s_yaml h_yaml_ok
        obtain ⟨sp', h_skip, hcorr'⟩ := skipToEndOfLine_corr _ sp_v hcorr_v
        exact ⟨sp', .yaml tail sc.col sp_ws s₂ s₃ s₄ sp' hnot h_ws hd1 hdot hd2 ⟨sp_v, h_wsv, hstop, h_skip⟩,
          hcorr', skipToEndOfLine_at_break_or_eof_chars _ sp' hcorr'⟩
      · simp at hok
    · rename_i h_y
      split at hok
      · -- `%TAG`
        rename_i h_t
        have hnm : nm = ['T', 'A', 'G'] := by
          have := congrArg String.toList (eq_of_beq h_t); rw [hname] at this; simpa using this
        subst hnm
        have hcol4 : tcol = sc.col + 4 := by simp at hcol; omega
        subst hcol4
        split at hok
        · rename_i s_tag h_tag_ok
          have h_eol := Except.ok.inj hok; subst h_eol
          obtain ⟨s₂, s₃, s₄, sp_v, h_hdl, h_hnot, h_ws2, h_pfx, h_wsv, hstop, hcorr_v⟩ :=
            scanTagDirective_prod _ sp_ws hcorr_ws sc hend_ws _ s_tag h_tag_ok
          obtain ⟨sp', h_skip, hcorr'⟩ := skipToEndOfLine_corr _ sp_v hcorr_v
          exact ⟨sp', .tag tail sc.col sp_ws s₂ s₃ s₄ sp' hnot h_ws h_hdl h_hnot h_ws2 h_pfx ⟨sp_v, h_wsv, hstop, h_skip⟩,
            hcorr', skipToEndOfLine_at_break_or_eof_chars _ sp' hcorr'⟩
        · simp at hok
      · -- reserved: `skipToEndOfLine` + `directivesPresent` flag (Fix B)
        rename_i h_t
        have h := Except.ok.inj hok; subst h
        obtain ⟨sp', h_skip, hcorr'⟩ := skipToEndOfLine_corr _ sp_ws hcorr_ws
        have hcol' : tcol = sc.col + 1 + nm.length := hcol
        subst hcol'
        refine ⟨sp', .reserved (nm ++ tail) sc.col ⟨tail, sc.col + 1 + nm.length⟩ sp'
          (gstar_gchar_of_all nm tail (sc.col + 1) hall) hnot ?_ ?_
          (GStar_trans (GStar_SSWhite_to_GStar_SCommentChar h_ws) h_skip),
          ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩,
          skipToEndOfLine_at_break_or_eof_chars _ sp' hcorr'⟩
        · intro heq; apply h_y
          have hnm : nm = ['Y', 'A', 'M', 'L'] :=
            List.append_cancel_right (show nm ++ tail = ['Y', 'A', 'M', 'L'] ++ tail from heq)
          have : (collectDirectiveNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).fst = "YAML" :=
            String.ext (by rw [hname, hnm]; rfl)
          simp [this]
        · intro heq; apply h_t
          have hnm : nm = ['T', 'A', 'G'] :=
            List.append_cancel_right (show nm ++ tail = ['T', 'A', 'G'] ++ tail from heq)
          have : (collectDirectiveNameLoop sc.advance "" (sc.inputEnd - sc.advance.offset)).fst = "TAG" :=
            String.ext (by rw [hname, hnm]; rfl)
          simp [this]

end L4YAML.Proofs.StructureProduction

end Blanket
