/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Coupling.StructureCoupling

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

namespace L4YAML.Proofs.ScanStrictCoupling

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.StructureCoupling

/-! ## §1 CharsFromOffset–toList Bridge -/

-- The initial character list matches input.toList.
-- CharsFromOffset iterates byte positions using get/next, while
-- String.toList iterates using String.Internal.toArray.
-- Both traverse valid UTF-8 and produce identical character sequences.
lemma chars_from_zero_toList (input : String) :
    CharsFromOffset input 0 input.toList :=
  CouplingBridge.chars_from_zero_toList input

/-! ## §1.5 Preservation Lemmas

Field-preservation lemmas for unwindIndentsLoop and saveSimpleKey:
offset, inputEnd, and input are unchanged by these bookkeeping operations. -/

lemma unwindIndentsLoop_offset (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).offset = s.offset := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ n ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

lemma unwindIndentsLoop_inputEnd (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).inputEnd = s.inputEnd := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ n ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

lemma unwindIndentsLoop_input (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).input = s.input := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ n ih =>
    unfold unwindIndentsLoop; split
    · exact ih _
    · rfl

lemma saveSimpleKey_offset (s : ScannerState) :
    (saveSimpleKey s).offset = s.offset := by
  unfold saveSimpleKey
  split <;> (try split) <;> (try split) <;> rfl

lemma saveSimpleKey_inputEnd (s : ScannerState) :
    (saveSimpleKey s).inputEnd = s.inputEnd := by
  unfold saveSimpleKey
  split <;> (try split) <;> (try split) <;> rfl

lemma saveSimpleKey_input (s : ScannerState) :
    (saveSimpleKey s).input = s.input := by
  unfold saveSimpleKey
  split <;> (try split) <;> (try split) <;> rfl

lemma saveSimpleKey_peek (s : ScannerState) :
    (saveSimpleKey s).peek? = s.peek? := by
  unfold ScannerState.peek?
  simp only [saveSimpleKey_offset, saveSimpleKey_inputEnd, saveSimpleKey_input]

/-! ## §2 Dispatch Couplings

Each dispatch function processes one category of YAML tokens.
These theorems compose the leaf _corr theorems from StructureCoupling
and ScalarCoupling. -/

-- Structural dispatch: document markers and directives.
lemma scanNextToken_dispatchStructural_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
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
lemma scanNextToken_dispatchFlowIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
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
lemma scanNextToken_dispatchBlockIndicators_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
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
lemma scanNextToken_dispatchContent_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanNextToken_dispatchContent sc c = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · -- '&': scanAnchorOrAlias bind
    generalize h_anch : scanAnchorOrAlias sc true = result at hok
    cases result with
    | error e => simp at hok
    | ok s_a =>
      have h := Except.ok.inj hok; subst h
      obtain ⟨sp', hcorr'⟩ := scanAnchorOrAlias_corr sc sp hcorr true s_a h_anch
      exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  · split at hok
    · split at hok
      · simp at hok
      · -- '*': scanAnchorOrAlias bind
        generalize h_anch : scanAnchorOrAlias sc false = result at hok
        cases result with
        | error e => simp at hok
        | ok s_a =>
          have h := Except.ok.inj hok; subst h
          exact scanAnchorOrAlias_corr sc sp hcorr false s_a h_anch
    · split at hok
      · -- '!': scanTag bind
        generalize h_tag : scanTag sc = result at hok
        cases result with
        | error e => simp at hok
        | ok s_t =>
          have h := Except.ok.inj hok; subst h
          exact scanTag_corr sc sp hcorr s_t h_tag
      · split at hok
        · -- '|' or '>': scanBlockScalar returns directly
          exact scanBlockScalar_corr sc sp hcorr hok
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
              · -- canStartPlainScalar: scanPlainScalar returns directly
                exact scanPlainScalar_corr sc sp hcorr hok
              · simp at hok

/-! ## §3 Preprocess Coupling -/

-- scanNextToken_preprocess preserves ScannerSurfCorr on the .ok (some _) path.
lemma scanNextToken_preprocess_corr (sc : ScannerState) (sp : SurfPos)
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
lemma scanNextToken_preprocess_none_consumed (sc : ScannerState) (sp : SurfPos)
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
lemma scanNextToken_corr (sc : ScannerState) (sp : SurfPos)
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
          · -- pending-directives check (Fix B)
            split at hok
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
lemma scanNextToken_none_consumed (sc : ScannerState) (sp : SurfPos)
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
        · -- pending-directives check (Fix B)
          split at hok
          · simp at hok
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
lemma scanLoop_full_consumption (sc : ScannerState) (sp : SurfPos) (fuel : Nat)
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
@[capstone]
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

/-! ## §6 Fix-B helpers: `directivesPresent` tracking (grammar-completeness Phase 1)

The pendingDirective↔scanner coupling in `StreamAccum` needs to know how
`directivesPresent` flows through the scan pipeline:
- preprocessing preserves it (`preprocess_some_directivesPresent`);
- `scanDirective` always sets it (`scanDirective_directivesPresent`);
- a successful `scanDocumentEnd` implies it was clear
  (`scanDocumentEnd_ok_directivesPresent`) and clears it in the result;
- `scanDocumentStart` clears it.

Mirrors the `_preserves_flowLevel` family in `ScannerCorrectness`. -/

lemma emit_dp (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).directivesPresent = s.directivesPresent := by
  unfold ScannerState.emit; rfl

lemma consumeNewline_dp (s : ScannerState) :
    (consumeNewline s).directivesPresent = s.directivesPresent := by
  unfold consumeNewline
  split
  · exact advance_dp s
  · dsimp only []
    split
    · exact advance_dp s
    · exact advance_dp s
  · rfl

lemma skipSpaces_dp (s : ScannerState) :
    (skipSpaces s).directivesPresent = s.directivesPresent := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop; split
    · rw [IH, advance_dp]
    · rfl

lemma skipWhitespace_dp (s : ScannerState) :
    (skipWhitespace s).directivesPresent = s.directivesPresent := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [IH, advance_dp]
      · rfl
    · rfl

lemma collectCommentTextLoop_dp (s : ScannerState) (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_dp]
    · rfl

lemma skipToEndOfLineLoop_dp (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ fuel' IH =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · rw [IH, advance_dp]
    · rfl

lemma skipToEndOfLine_dp (s : ScannerState) :
    (skipToEndOfLine s).directivesPresent = s.directivesPresent := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_dp s _

lemma unwindIndentsLoop_dp (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · rw [ih]; exact emit_dp s .blockEnd
    · rfl

lemma unwindIndents_dp (s : ScannerState) (col : Int) :
    (unwindIndents s col).directivesPresent = s.directivesPresent := by
  unfold unwindIndents
  exact unwindIndentsLoop_dp s col s.indents.size

lemma saveSimpleKey_dp (s : ScannerState) :
    (saveSimpleKey s).directivesPresent = s.directivesPresent := by
  unfold saveSimpleKey
  split <;> (try rfl)
  split <;> rfl

lemma skipToContentWs_dp (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
        · split at h
          · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
          · split at h
            · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
      · simp at h; rw [← h, skipSpaces_dp]
    · simp at h; rw [← h, skipWhitespace_dp, skipSpaces_dp]
  · simp at h; rw [← h, skipWhitespace_dp]

lemma skipToContentComment_dp (s : ScannerState) :
    (skipToContentComment s).directivesPresent = s.directivesPresent := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_dp, advance_dp]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_dp, advance_dp]
      · rfl
  · rfl

lemma skipToContentLoop_dp (s : ScannerState) (s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [← h]
  | succ fuel' IH =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · rename_i c hpeek
        split at h
        · split at h
          · have ih := IH _ h
            rw [ih, consumeNewline_dp, skipToContentComment_dp]
            exact skipToContentWs_dp s s1 hws
          · have ih := IH _ h
            rw [ih, consumeNewline_dp, skipToContentComment_dp]
            exact skipToContentWs_dp s s1 hws
        · simp at h; rw [← h, skipToContentComment_dp]
          exact skipToContentWs_dp s s1 hws
      · simp at h; rw [← h, skipToContentComment_dp]
        exact skipToContentWs_dp s s1 hws

lemma skipToContent_dp (s : ScannerState) (s' : ScannerState)
    (h : skipToContent s = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold skipToContent at h
  exact skipToContentLoop_dp s s' _ h

/-- Preprocessing preserves `directivesPresent`. -/
lemma preprocess_some_directivesPresent {sc s_prep : ScannerState} {c : Char}
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.directivesPresent = sc.directivesPresent := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i s1 hskip
    split at h
    · simp at h
    · split at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, _⟩ := h
            rw [← h1, saveSimpleKey_dp, unwindIndents_dp]
            exact skipToContent_dp sc s1 hskip
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, _⟩ := h
            rw [← h1, saveSimpleKey_dp]
            exact skipToContent_dp sc s1 hskip

/-- `scanYamlDirective` always sets `directivesPresent`. -/
lemma scanYamlDirective_directivesPresent {s s_ws s' : ScannerState} {sp : YamlPos}
    (h : scanYamlDirective s s_ws sp = .ok s') : s'.directivesPresent = true := by
  unfold scanYamlDirective at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; rfl)
    | simp at h

/-- `scanTagDirective` always sets `directivesPresent`. -/
lemma scanTagDirective_directivesPresent {s s_ws s' : ScannerState} {sp : YamlPos}
    (h : scanTagDirective s s_ws sp = .ok s') : s'.directivesPresent = true := by
  unfold scanTagDirective at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; rfl)
    | simp at h

/-- `scanDirective` always sets `directivesPresent` (Fix B: including the
    reserved-directive branch). -/
lemma scanDirective_directivesPresent {s s' : ScannerState}
    (h : scanDirective s = .ok s') : s'.directivesPresent = true := by
  unfold scanDirective at h
  split at h
  · simp at h
  · dsimp only [] at h
    split at h
    · -- YAML
      split at h
      · rename_i s_y h_y
        simp only [Except.ok.injEq] at h; subst h
        show (skipToEndOfLine s_y).directivesPresent = true
        rw [skipToEndOfLine_dp]
        exact scanYamlDirective_directivesPresent h_y
      · simp at h
    · split at h
      · -- TAG
        split at h
        · rename_i s_t h_t
          simp only [Except.ok.injEq] at h; subst h
          show (skipToEndOfLine s_t).directivesPresent = true
          rw [skipToEndOfLine_dp]
          exact scanTagDirective_directivesPresent h_t
        · simp at h
      · -- reserved: the record update sets the flag directly
        simp only [Except.ok.injEq] at h; subst h
        rfl

/-- A successful `scanDocumentEnd` implies no directives were pending
    (Fix B: the guard is a bare `directivesPresent` check). -/
lemma scanDocumentEnd_ok_directivesPresent {s s' : ScannerState}
    (h : scanDocumentEnd s = .ok s') : s.directivesPresent = false := by
  cases hdp : s.directivesPresent with
  | false => rfl
  | true =>
    exfalso
    unfold scanDocumentEnd at h
    rw [hdp] at h
    simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- `scanDocumentEnd` clears `directivesPresent` in its result. -/
lemma scanDocumentEnd_result_dp {s s' : ScannerState}
    (h : scanDocumentEnd s = .ok s') : s'.directivesPresent = false := by
  unfold scanDocumentEnd at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; rfl)
    | simp at h

/-- `scanDocumentStart` clears `directivesPresent`. -/
lemma scanDocumentStart_dp (s : ScannerState) :
    (scanDocumentStart s).directivesPresent = false := by
  unfold scanDocumentStart; rfl

/-- Snoc a final element onto a `GPlus` chain. -/
lemma GPlus_snoc {P : SurfPos → SurfPos → Prop} {a b c : SurfPos}
    (h : GPlus P a b) (hlast : P b c) : GPlus P a c := by
  cases h with
  | mk m _ hfirst hrest =>
    exact GPlus.mk a m c hfirst
      (GStar_trans hrest (GStar.cons _ _ _ hlast (GStar.nil _)))

end L4YAML.Proofs.ScanStrictCoupling
