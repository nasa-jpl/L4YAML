/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Proofs.StructureCoupling

/-!
# Scan-Strict Coupling: Full-Consumption Infrastructure

Phase A of v0.4.4. Composes the 80+ leaf coupling theorems from
CouplingBridge, ScannerCoupling, ScalarCoupling, and StructureCoupling
into top-level theorems showing that `scan` consumes all input characters.

## Main Results

- `scanNextToken_corr`: each scanNextToken step preserves ScannerSurfCorr
- `scanNextToken_none_consumed`: when scanNextToken returns none, input is consumed
- `scanLoop_full_consumption`: after scanLoop succeeds, all characters consumed
- `scan_full_consumption`: scan success implies full character consumption

## Architecture

```
chars_from_zero_toList          -- String ↔ CharsFromOffset bridge
    ↓
scanNextToken_preprocess_corr   -- skipToContent + unwind + saveKey
    ↓
scanNextToken_dispatch*_corr    -- 4 dispatch couplings composing leaf theorems
    ↓
scanNextToken_corr              -- full token step
    ↓
scanLoop_full_consumption       -- fuel induction
    ↓
scan_full_consumption           -- initial state + BOM + loop
```
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.ScanStrictCoupling

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScannerCoupling
open Lean4Yaml.Proofs.ScalarCoupling
open Lean4Yaml.Proofs.StructureCoupling

/-! ## §1 CharsFromOffset–toList Bridge -/

-- The initial character list matches input.toList.
-- CharsFromOffset iterates byte positions using get/next, while
-- String.toList iterates using String.Internal.toArray.
-- Both traverse valid UTF-8 and produce identical character sequences.
theorem chars_from_zero_toList (input : String) :
    CharsFromOffset input 0 input.toList :=
  CouplingBridge.chars_from_zero_toList input

/-! ## §1.5 Preservation Lemmas

Field-preservation lemmas for unwindIndentsLoop and saveSimpleKey:
offset, inputEnd, and input are unchanged by these bookkeeping operations. -/

theorem unwindIndentsLoop_offset (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).offset = s.offset := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ n ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

theorem unwindIndentsLoop_inputEnd (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).inputEnd = s.inputEnd := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ n ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

theorem unwindIndentsLoop_input (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).input = s.input := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ n ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

theorem saveSimpleKey_offset (s : ScannerState) :
    (saveSimpleKey s).offset = s.offset := by
  unfold saveSimpleKey
  split <;> (try split) <;> (try split) <;> rfl

theorem saveSimpleKey_inputEnd (s : ScannerState) :
    (saveSimpleKey s).inputEnd = s.inputEnd := by
  unfold saveSimpleKey
  split <;> (try split) <;> (try split) <;> rfl

theorem saveSimpleKey_input (s : ScannerState) :
    (saveSimpleKey s).input = s.input := by
  unfold saveSimpleKey
  split <;> (try split) <;> (try split) <;> rfl

theorem saveSimpleKey_peek (s : ScannerState) :
    (saveSimpleKey s).peek? = s.peek? := by
  unfold ScannerState.peek?
  simp only [saveSimpleKey_offset, saveSimpleKey_inputEnd, saveSimpleKey_input]

/-! ## §2 Dispatch Couplings

Each dispatch function processes one category of YAML tokens.
These theorems compose the leaf _corr theorems from StructureCoupling
and ScalarCoupling. -/

-- Structural dispatch: document markers and directives.
theorem scanNextToken_dispatchStructural_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken_dispatchStructural sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · split at hok
        · have h := Except.ok.inj hok; injection h with h; subst h
          exact scanDocumentStart_corr sc sp hcorr
        · split at hok
          · split at hok
            · simp at hok
            · have h := Except.ok.inj hok; injection h with h; subst h
              exact scanDocumentEnd_corr sc sp hcorr _ ‹_›
          · split at hok
            · split at hok
              · simp at hok
              · have h := Except.ok.inj hok; injection h with h; subst h
                exact scanDirective_corr sc sp hcorr _ ‹_›
            · simp at hok
  · split at hok
    · simp at hok
    · split at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanDocumentStart_corr sc sp hcorr
      · split at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h; subst h
            exact scanDocumentEnd_corr sc sp hcorr _ ‹_›
        · split at hok
          · split at hok
            · simp at hok
            · have h := Except.ok.inj hok; injection h with h; subst h
              exact scanDirective_corr sc sp hcorr _ ‹_›
          · simp at hok

-- Flow indicator dispatch: [ ] { } ,
theorem scanNextToken_dispatchFlowIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken_dispatchFlowIndicators sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · have h := Except.ok.inj hok; injection h with h; subst h
    exact scanFlowSequenceStart_corr sc sp hcorr
  · split at hok
    · split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · have h := Except.ok.inj hok; injection h with h; subst h
          exact scanFlowSequenceEnd_corr sc sp hcorr
    · split at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanFlowMappingStart_corr sc sp hcorr
      · split at hok
        · split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · have h := Except.ok.inj hok; injection h with h; subst h
              exact scanFlowMappingEnd_corr sc sp hcorr
        · split at hok
          · split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · have h := Except.ok.inj hok; injection h with h; subst h
                exact scanFlowEntry_corr sc sp hcorr _ ‹_›
          · simp at hok

-- Block indicator dispatch: - ? :
theorem scanNextToken_dispatchBlockIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken_dispatchBlockIndicators sc c = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · split at hok
    · simp at hok
    · have h := Except.ok.inj hok; injection h with h; subst h
      exact scanBlockEntry_corr sc sp hcorr _ ‹_›
  · split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; injection h with h; subst h
        exact scanKey_corr sc sp hcorr _ ‹_›
    · split at hok
      · split at hok
        · simp at hok
        · have h := Except.ok.inj hok; injection h with h; subst h
          exact scanValue_corr sc sp hcorr _ ‹_›
      · simp at hok

-- Content dispatch: & * ! | > " ' plain scalars.
theorem scanNextToken_dispatchContent_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · have h := Except.ok.inj hok; subst h
    obtain ⟨sp', hcorr'⟩ := scanAnchorOrAlias_corr sc sp hcorr true
    exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  · split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact scanAnchorOrAlias_corr sc sp hcorr false
    · split at hok
      · have h := Except.ok.inj hok; subst h
        exact scanTag_corr sc sp hcorr
      · split at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; subst h
            exact scanBlockScalar_corr sc sp hcorr ‹_›
        · split at hok
          · split at hok
            · simp at hok
            · have h := Except.ok.inj hok; subst h
              obtain ⟨sp', hcorr'⟩ := scanDoubleQuoted_corr sc sp hcorr ‹_›
              split
              · exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
              · exact ⟨sp', hcorr'⟩
          · split at hok
            · split at hok
              · simp at hok
              · have h := Except.ok.inj hok; subst h
                obtain ⟨sp', hcorr'⟩ := scanSingleQuoted_corr sc sp hcorr ‹_›
                split
                · exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
                · exact ⟨sp', hcorr'⟩
            · split at hok
              · split at hok
                · simp at hok
                · have h := Except.ok.inj hok; subst h
                  exact scanPlainScalar_corr sc sp hcorr ‹_›
              · simp at hok

/-! ## §3 Preprocess Coupling -/

-- scanNextToken_preprocess preserves ScannerSurfCorr on the .ok (some _) path.
theorem scanNextToken_preprocess_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState) (c : Char)
    (hok : scanNextToken_preprocess sc = .ok (some (s', c))) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    obtain ⟨sp1, hcorr1⟩ := skipToContentLoop_ok_corr sc sp _ s_content hcorr
        (Nat.le_refl _) h_skip
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            obtain ⟨sp2, hcorr2⟩ := unwindIndents_corr s_content sp1 hcorr1 (↑s_content.col)
            have hcorr3 : ScannerSurfCorr
                { (unwindIndents s_content ↑s_content.col) with
                  needIndentCheck := false } sp2 :=
              ⟨hcorr2.chars_from, hcorr2.col_eq, hcorr2.end_eq, hcorr2.input_prefix, hcorr2.indent_cols_nonneg⟩
            exact ⟨sp2, saveSimpleKey_corr _ sp2 hcorr3⟩
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            exact ⟨sp1, saveSimpleKey_corr _ sp1 hcorr1⟩

-- When scanNextToken_preprocess returns .ok none, all input is consumed.
theorem scanNextToken_preprocess_none_consumed (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok none) :
    ∃ sp_final : SurfPos, sp_final.chars = [] := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · cases hok
  · rename_i s_content h_skip
    split at hok
    · rename_i h_hasMore
      obtain ⟨sp_c, hcorr_c⟩ := skipToContentLoop_ok_corr sc sp _ s_content hcorr
        (Nat.le_refl _) h_skip
      have h_not_lt : ¬ s_content.offset < s_content.inputEnd := by
        simp [ScannerState.hasMore] at h_hasMore; omega
      exact ⟨sp_c, eof_corr s_content sp_c hcorr_c h_not_lt⟩
    · rename_i h_hasMore
      split at hok
      · split at hok
        · cases hok
        · split at hok
          · rename_i h_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none; dsimp only [] at h_peek_none
            unfold unwindIndents at h_peek_none
            simp only [unwindIndentsLoop_offset, unwindIndentsLoop_inputEnd,
              unwindIndentsLoop_input] at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt; simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok
      · split at hok
        · cases hok
        · split at hok
          · rename_i h_no_indent h_no_trailing h_peek_none
            exfalso; rw [saveSimpleKey_peek] at h_peek_none
            unfold ScannerState.peek? at h_peek_none
            split at h_peek_none
            · cases h_peek_none
            · rename_i h_not_lt; simp [ScannerState.hasMore] at h_hasMore
              exact h_not_lt h_hasMore
          · cases hok

/-! ## §4 scanNextToken Coupling -/

-- When scanNextToken returns .ok (some s'), ScannerSurfCorr is preserved.
theorem scanNextToken_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken sc = .ok (some s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · split at hok
    · exact absurd (Except.ok.inj hok) nofun
    · rename_i s_pre c_pre h_pre
      obtain ⟨sp_pre, hcorr_pre⟩ := scanNextToken_preprocess_corr sc sp hcorr s_pre c_pre h_pre
      split at hok
      · simp at hok
      · split at hok
        · rename_i s_str h_str
          have h := Except.ok.inj hok; injection h with h; subst h
          exact scanNextToken_dispatchStructural_corr s_pre sp_pre c_pre hcorr_pre s_str h_str
        · split at hok
          · simp at hok
          · have hcorr_ad : ScannerSurfCorr
                (if s_pre.allowDirectives then
                  { s_pre with allowDirectives := false, documentEverStarted := true }
                else s_pre) sp_pre := by
              split
              · exact ⟨hcorr_pre.chars_from, hcorr_pre.col_eq, hcorr_pre.end_eq, hcorr_pre.input_prefix, hcorr_pre.indent_cols_nonneg⟩
              · exact hcorr_pre
            split at hok
            · simp at hok
            · split at hok
              · rename_i s_flow h_flow
                have h := Except.ok.inj hok; injection h with h; subst h
                exact scanNextToken_dispatchFlowIndicators_corr _ sp_pre c_pre hcorr_ad s_flow h_flow
              · split at hok
                · simp at hok
                · split at hok
                  · rename_i s_blk h_blk
                    have h := Except.ok.inj hok; injection h with h; subst h
                    exact scanNextToken_dispatchBlockIndicators_corr _ sp_pre c_pre hcorr_ad s_blk h_blk
                  · split at hok
                    · simp at hok
                    · rename_i s_cnt h_cnt
                      have h := Except.ok.inj hok; injection h with h; subst h
                      exact scanNextToken_dispatchContent_corr _ sp_pre c_pre hcorr_ad s_cnt h_cnt

-- When scanNextToken returns .ok none, all input characters are consumed.
theorem scanNextToken_none_consumed (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken sc = .ok none) :
    ∃ sp_final : SurfPos, sp_final.chars = [] := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · split at hok
    · rename_i h_pre
      exact scanNextToken_preprocess_none_consumed sc sp hcorr h_pre
    · split at hok
      · simp at hok
      · split at hok
        · exact absurd (Except.ok.inj hok) nofun
        · split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · split at hok
              · exact absurd (Except.ok.inj hok) nofun
              · split at hok
                · simp at hok
                · split at hok
                  · exact absurd (Except.ok.inj hok) nofun
                  · split at hok
                    · simp at hok
                    · exact absurd (Except.ok.inj hok) nofun

/-! ## §5 scanLoop Full Consumption -/

-- After scanLoop succeeds, all input characters have been consumed.
-- Proof by induction on fuel, threading ScannerSurfCorr through each
-- scanNextToken step via scanNextToken_corr, and using
-- scanNextToken_none_consumed when the loop terminates.
theorem scanLoop_full_consumption (sc : ScannerState) (sp : SurfPos) (fuel : Nat)
    (tokens : Array (Positioned YamlToken))
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanLoop sc fuel = .ok tokens) :
    ∃ sp_final : SurfPos, sp_final.chars = [] := by
  induction fuel generalizing sc sp tokens with
  | zero => simp [scanLoop] at hok
  | succ fuel' ih =>
    simp only [scanLoop] at hok
    split at hok
    · -- scanNextToken = .error → contradicts .ok
      simp at hok
    · -- scanNextToken = .ok none → EOF
      rename_i h_none
      -- Final validation: flowLevel, directives checks
      split at hok <;> try (simp at hok; done)
      split at hok <;> try (simp at hok; done)
      -- Past validation, scanner reached EOF
      exact scanNextToken_none_consumed sc sp hcorr h_none
    · -- scanNextToken = .ok (some s') → recurse
      rename_i s_next h_next
      obtain ⟨sp', hcorr'⟩ := scanNextToken_corr sc sp hcorr s_next h_next
      exact ih s_next sp' tokens hcorr' hok

/-! ## §6 scan Full Consumption -/

-- Full consumption: when `scan` succeeds, all input characters are consumed.
-- Proof: establish ScannerSurfCorr for the initial state (mk' + emit + BOM),
-- then apply scanLoop_full_consumption.
theorem scan_full_consumption (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    ∃ sp_final : SurfPos, sp_final.chars = [] := by
  unfold scan at h
  simp only [] at h
  -- Establish ScannerSurfCorr for initial state
  have h_chars := chars_from_zero_toList input
  have h_init := initial_corr input input.toList h_chars
  have h_emit : ScannerSurfCorr ((ScannerState.mk' input).emit .streamStart)
      ⟨input.toList, 0⟩ :=
    ⟨h_init.chars_from, h_init.col_eq, h_init.end_eq, h_init.input_prefix, h_init.indent_cols_nonneg⟩
  -- BOM handling preserves ScannerSurfCorr
  have h_bom : ∃ sp, ScannerSurfCorr
      (match (ScannerState.mk' input |>.emit .streamStart).peek? with
       | some '\uFEFF' => (ScannerState.mk' input |>.emit .streamStart).advance
       | _ => ScannerState.mk' input |>.emit .streamStart) sp := by
    split
    · exact advance_corr _ _ h_emit
    · exact ⟨_, h_emit⟩
  obtain ⟨sp_bom, h_bom⟩ := h_bom
  exact scanLoop_full_consumption _ sp_bom _ tokens h_bom h

end Lean4Yaml.Proofs.ScanStrictCoupling
