/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Proofs.ScannerCoupling

/-!
# Scalar Collection Coupling

Coupling theorems for scalar content collection functions, connecting the
scanner's scalar-scanning loops to the formal surface syntax.

Each scalar scanning function preserves `ScannerSurfCorr` on every `.ok`
return path.  Content-string accumulation and token emission are irrelevant
to correspondence since they only affect `tokens`/`simpleKey`/`comments`
fields, none of which appear in `ScannerSurfCorr`.
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.ScalarCoupling

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScannerCoupling

/-! ## §1 Core Helpers -/

/-- All `some` branches of `collectPlainScalar_terminates?` return `state := s`. -/
theorem terminates_state_eq (c : Char) (s : ScannerState)
    (content spaces : String) (inFlow : Bool) (r : PlainScalarResult)
    (h : collectPlainScalar_terminates? c s content spaces inFlow = some r) :
    r.state = s := by
  unfold collectPlainScalar_terminates? at h
  -- Branch 1: c == '#' && spaces.length > 0
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · -- Branch 2: c == ':'
    split at h
    · -- let next := ...; let terminates := match next with ...; if terminates then some ... else none
      dsimp only [] at h
      split at h  -- match on peekAt? 1
      · split at h  -- if terminates
        · simp only [Option.some.injEq] at h; subst h; rfl
        · simp at h
      · split at h  -- if terminates (none case → terminates = true)
        · simp only [Option.some.injEq] at h; subst h; rfl
        · simp at h
    · -- Branch 3: inFlow && isFlowIndicatorBool c
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · -- Branch 4: s.col == 0 && atDocumentBoundary s
        split at h
        · simp only [Option.some.injEq] at h; subst h; rfl
        · simp at h

/-- A single `advance` preserves correspondence for some surface position.
    Handles newline, non-newline, and EOF (identity) uniformly. -/
theorem advance_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr sc.advance sp' := by
  by_cases hmore : sc.offset < sc.inputEnd
  · obtain ⟨c, rest, hchars, hpeek⟩ := peek_corr sc sp hcorr hmore
    have hcol := hcorr.col_eq
    have hsp_eq : sp = ⟨c :: rest, sc.col⟩ := by
      cases sp with | mk cs cl =>
      simp only [] at hchars hcol; subst hchars; subst hcol; rfl
    subst hsp_eq
    by_cases hnl : c = '\n'
    · subst hnl
      exact ⟨⟨rest, 0⟩, advance_newline_corr sc rest hcorr hmore⟩
    · by_cases hcr : c = '\r'
      · subst hcr
        exact ⟨⟨rest, 0⟩, advance_cr_corr sc rest hcorr hmore⟩
      · exact ⟨⟨rest, sc.col + 1⟩,
               advance_non_newline_corr sc c rest hcorr hmore hnl hcr⟩
  · have : sc.advance = sc := by unfold ScannerState.advance; simp [hmore]
    rw [this]; exact ⟨sp, hcorr⟩

/-- `consumeNewline` preserves correspondence unconditionally. -/
theorem consumeNewline_unconditional_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (consumeNewline sc) sp' := by
  unfold consumeNewline
  split
  · -- peek? = some '\n': advance + needIndentCheck
    obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
    exact ⟨sp', corr_of_needIndentCheck_update true hcorr'⟩
  · -- peek? = some '\r': advance, then check for LF
    obtain ⟨sp1, hcorr1⟩ := advance_corr sc sp hcorr
    dsimp only []  -- inline let s' := sc.advance
    split
    · -- CRLF: raw offset skip (not another advance)
      rename_i hpeek2
      have hmore2 : sc.advance.offset < sc.advance.inputEnd :=
        peek_some_hasMore sc.advance '\n' hpeek2
      obtain ⟨c2, rest2, hchars2, _⟩ := peek_corr sc.advance sp1 hcorr1 hmore2
      have hcol1 := hcorr1.col_eq
      have hsp1_eq : sp1 = ⟨c2 :: rest2, sc.advance.col⟩ := by
        cases sp1 with | mk cs cl =>
        simp only [] at hchars2 hcol1; subst hchars2; subst hcol1; rfl
      subst hsp1_eq
      have hskip := skip_byte_corr sc.advance c2 rest2 sc.advance.col hcorr1 hmore2
      exact ⟨⟨rest2, sc.advance.col⟩, corr_of_needIndentCheck_update true hskip⟩
    · -- lone CR
      exact ⟨sp1, corr_of_needIndentCheck_update true hcorr1⟩
  · -- not a line break: identity
    exact ⟨sp, hcorr⟩

/-- `emitAt` only modifies `tokens`, preserving correspondence. -/
theorem corr_of_emitAt {sc : ScannerState} {sp : SurfPos}
    (pos : YamlPos) (tok : YamlToken)
    (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr (sc.emitAt pos tok) sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩

/-! ## §2 Utility Loops -/

/-- `collectHexDigitsLoop` preserves correspondence. -/
theorem collectHexDigitsLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hex : String) (n : Nat) (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (collectHexDigitsLoop sc hex n).2 sp' := by
  induction n generalizing sc sp hex with
  | zero => simp [collectHexDigitsLoop]; exact ⟨sp, hcorr⟩
  | succ n' ih =>
    unfold collectHexDigitsLoop; split
    · rename_i c hpeek; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' _ hcorr'
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

/-- `parseHexEscape` preserves correspondence on `.ok` paths. -/
theorem parseHexEscape_corr (sc : ScannerState) (sp : SurfPos) (n : Nat)
    {c : Char} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : parseHexEscape sc n = .ok (c, s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold parseHexEscape at hok
  dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · injection hok with a_eq
      injection a_eq with _ hs'
      rw [← hs']
      exact collectHexDigitsLoop_corr sc sp "" n hcorr
    · exact absurd hok (by simp)

/-- `processEscape` preserves correspondence on `.ok` paths. -/
theorem processEscape_corr (sc : ScannerState) (sp : SurfPos)
    {c : Char} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : processEscape sc = .ok (c, s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold processEscape at hok
  split at hok
  · simp at hok  -- none → error
  · rename_i c_esc hpeek
    dsimp only [] at hok
    obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
    -- Each match arm: named escape → sc.advance, hex → parseHexEscape, error → ⊥
    split at hok <;> (first
      | exact parseHexEscape_corr sc.advance sp' _ hcorr' hok  -- hex escapes
      | (obtain ⟨-, rfl⟩ := hok; exact ⟨sp', hcorr'⟩)  -- named escapes: .ok (ch, sc.advance)
      | (simp at hok))  -- wildcard error arm

/-- `skipTrailingSpaces` preserves correspondence. -/
theorem skipTrailingSpaces_corr (sc : ScannerState) (sp : SurfPos) (fuel : Nat)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (skipTrailingSpaces sc fuel) sp' := by
  induction fuel generalizing sc sp with
  | zero => simp [skipTrailingSpaces]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold skipTrailingSpaces; split
    · rename_i c hpeek; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr'
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

/-! ## §3 Shared Helpers -/

/-- `foldQuotedNewlinesLoop` preserves correspondence (1st component).
    Note: the non-recursive cases return the ORIGINAL input `s`, not `skipSpaces s`. -/
theorem foldQuotedNewlinesLoop_corr (sc : ScannerState) (sp : SurfPos)
    (cnt fuel : Nat) (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (foldQuotedNewlinesLoop sc cnt fuel).1 sp' := by
  induction fuel generalizing sc sp cnt with
  | zero => simp [foldQuotedNewlinesLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    dsimp only []  -- inline let saved, let s_skipped
    obtain ⟨_, sp_sk, _, hcorr_sk⟩ := skipSpaces_corr sc sp hcorr
    split
    · rename_i c hpeek; split
      · rename_i hlb
        obtain ⟨sp_cn, hcorr_cn⟩ :=
          consumeNewline_corr (skipSpaces sc) sp_sk c hcorr_sk hpeek hlb
        exact ih (consumeNewline (skipSpaces sc)) sp_cn (cnt + 1) hcorr_cn
      · exact ⟨sp, hcorr⟩  -- return saved = original s
    · exact ⟨sp, hcorr⟩

/-- `foldQuotedNewlines` preserves correspondence on `.ok` paths. -/
theorem foldQuotedNewlines_corr (sc : ScannerState) (sp : SurfPos)
    {content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : foldQuotedNewlines sc = .ok (content, s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold foldQuotedNewlines at hok
  dsimp only [] at hok
  -- consumeNewline sc (unconditional) → foldQuotedNewlinesLoop → skipSpaces → tab check → skipWhitespace
  obtain ⟨sp_cn, hcorr_cn⟩ := consumeNewline_unconditional_corr sc sp hcorr
  obtain ⟨sp_fold, hcorr_fold⟩ :=
    foldQuotedNewlinesLoop_corr (consumeNewline sc) sp_cn 0 _ hcorr_cn
  obtain ⟨_, sp_sk, _, hcorr_sk⟩ :=
    skipSpaces_corr (foldQuotedNewlinesLoop (consumeNewline sc) 0
                      (sc.inputEnd - (consumeNewline sc).offset + 1)).1
                    sp_fold hcorr_fold
  split at hok
  · -- inFlow && col ≤ currentIndent: check for tab
    split at hok
    · -- tab error case: throw (.tabInIndentation ...)
      simp only [bind, Except.bind] at hok; simp at hok
    · -- no tab: continue to skipWhitespace
      -- First, we must define the skipWhitespace result to use it in the goal
      obtain ⟨sp_ws, _, hcorr_ws⟩ := skipWhitespace_corr _ sp_sk hcorr_sk
      split at hok
      · -- case 0 < .snd: multiple newlines
        injection hok with a_eq
        injection a_eq with _ hs'
        rw [← hs']
        exact ⟨sp_ws, hcorr_ws⟩
      · -- case ¬(0 < .snd): single space
        injection hok with a_eq
        injection a_eq with _ hs'
        rw [← hs']
        exact ⟨sp_ws, hcorr_ws⟩
  · obtain ⟨sp_ws, _, hcorr_ws⟩ := skipWhitespace_corr _ sp_sk hcorr_sk
    split at hok
    · have hinj := Except.ok.inj hok; obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
      exact ⟨sp_ws, hcorr_ws⟩
    · have hinj := Except.ok.inj hok; obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
      exact ⟨sp_ws, hcorr_ws⟩

/-! ## §4 Double-Quoted Scalar -/

/-- `collectDoubleQuotedLoop` preserves correspondence on `.ok` paths. -/
theorem collectDoubleQuotedLoop_corr (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  induction fuel generalizing sc sp content with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)  -- none → error
    · -- peek? = some '"': closing quote
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok; exact advance_corr sc sp hcorr
    · -- peek? = some '\\': escape sequence
      obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
      dsimp only [] at hok
      split at hok
      · -- next peek = some c
        rename_i c2 hpeek2
        split at hok
        · -- isLineBreakBool c2: escaped newline
          obtain ⟨sp_cn, hcorr_cn⟩ :=
            consumeNewline_unconditional_corr sc.advance sp_adv hcorr_adv
          obtain ⟨sp_ws, _, hcorr_ws⟩ :=
            skipWhitespace_corr (consumeNewline sc.advance) sp_cn hcorr_cn
          exact ih _ sp_ws content hcorr_ws hok
        · -- not line break: processEscape
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)  -- processEscape error
          · rename_i esc_result hproc
            obtain ⟨sp_esc, hcorr_esc⟩ :=
              processEscape_corr sc.advance sp_adv hcorr_adv hproc
            exact ih _ sp_esc _ hcorr_esc hok
      · exact absurd hok (by simp)  -- none → error
    · -- peek? = some c (regular)
      rename_i c hpeek hne_dq hne_bs
      split at hok
      · -- isLineBreakBool c: fold newlines
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)  -- fold error
        · rename_i fold_result hfold
          obtain ⟨sp_fold, hcorr_fold⟩ := foldQuotedNewlines_corr sc sp hcorr hfold
          -- After fold: do-notation guards for document marker + indentation
          split at hok  -- doc marker if
          · simp at hok  -- doc marker true → error
          · split at hok  -- underIndented if
            · simp at hok  -- underIndented true → error
            · -- After both guards pass, there may be do-notation match residue
              split at hok
              · simp at hok  -- .error case impossible
              · exact ih _ sp_fold _ hcorr_fold hok
      · split at hok
        · simp at hok  -- invalid control char
        · -- valid nb-json char: advance
          obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
          exact ih sc.advance sp_adv _ hcorr_adv hok

/-- `scanDoubleQuoted` preserves correspondence on `.ok` paths. -/
theorem scanDoubleQuoted_corr (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok  -- collectDoubleQuotedLoop error
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
    obtain ⟨sp_close, hcorr_close⟩ :=
      collectDoubleQuotedLoop_corr sc.advance sp_adv "" _ _ _ _ _ hcorr_adv hloop
    -- validateTrailingContent: do-notation bind on Except Unit
    split at hok  -- if !sc.inFlow
    · -- !inFlow = true: validate
      split at hok  -- match on validateTrailingContent result
      · simp at hok  -- validation error
      · -- validation ok: state unchanged
        have h := Except.ok.inj hok; subst h
        exact ⟨sp_close, corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_close)⟩
    · -- !inFlow = false: no validate (pure ())
      split at hok  -- match on .ok ()
      · simp at hok  -- .error case impossible
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close, corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_close)⟩

/-! ## §5 Single-Quoted Scalar -/

/-- `collectSingleQuotedLoop` preserves correspondence on `.ok` paths. -/
theorem collectSingleQuotedLoop_corr (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : collectSingleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  induction fuel generalizing sc sp content with
  | zero => simp [collectSingleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- peek? = some '\''
      obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
      dsimp only [] at hok
      split at hok
      · -- next peek = some '\'': escaped quote → advance again → recurse
        obtain ⟨sp_adv2, hcorr_adv2⟩ := advance_corr sc.advance sp_adv hcorr_adv
        exact ih sc.advance.advance sp_adv2 _ hcorr_adv2 hok
      · -- closing quote
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok; exact ⟨sp_adv, hcorr_adv⟩
    · -- peek? = some c (not '\'')
      rename_i c hpeek hne_sq
      split at hok
      · -- isLineBreakBool c: fold newlines
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · rename_i fold_result hfold
          obtain ⟨sp_fold, hcorr_fold⟩ := foldQuotedNewlines_corr sc sp hcorr hfold
          split at hok  -- doc marker if
          · simp at hok  -- documentMarker
          · split at hok  -- underIndented if
            · simp at hok  -- underIndented
            · split at hok
              · simp at hok  -- .error case impossible
              · exact ih _ sp_fold _ hcorr_fold hok
      · split at hok
        · simp at hok  -- invalid control char
        · obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
          exact ih sc.advance sp_adv _ hcorr_adv hok

/-- `scanSingleQuoted` preserves correspondence on `.ok` paths. -/
theorem scanSingleQuoted_corr (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanSingleQuoted sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok  -- collectSingleQuotedLoop error
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
    obtain ⟨sp_close, hcorr_close⟩ :=
      collectSingleQuotedLoop_corr sc.advance sp_adv "" _ _ _ _ _ hcorr_adv hloop
    -- validateTrailingContent: do-notation bind on Except Unit
    split at hok  -- if !sc.inFlow
    · -- !inFlow = true: validate
      split at hok  -- match on validateTrailingContent result
      · simp at hok  -- validation error
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close, corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_close)⟩
    · -- !inFlow = false: no validate (pure ())
      split at hok  -- match on .ok ()
      · simp at hok  -- .error case impossible
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close, corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_close)⟩

/-! ## §6 Plain Scalar -/

/-- `skipBlankLinesLoop` preserves correspondence (2nd component). -/
theorem skipBlankLinesLoop_corr (sc : ScannerState) (sp : SurfPos)
    (cnt fuel : Nat) (inputEnd : Nat)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (skipBlankLinesLoop sc cnt fuel inputEnd).2 sp' := by
  induction fuel generalizing sc sp cnt with
  | zero => simp [skipBlankLinesLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold skipBlankLinesLoop
    dsimp only []  -- inline let saved, let s_after_spaces
    obtain ⟨_, sp_sk, _, hcorr_sk⟩ := skipSpaces_corr sc sp hcorr
    split
    · rename_i c hpeek; split
      · rename_i hlb
        obtain ⟨sp_cn, hcorr_cn⟩ :=
          consumeNewline_corr (skipSpaces sc) sp_sk c hcorr_sk hpeek hlb
        exact ih (consumeNewline (skipSpaces sc)) sp_cn (cnt + 1) hcorr_cn
      · exact ⟨sp, hcorr⟩  -- return saved
    · exact ⟨sp, hcorr⟩

/-- `collectPlainScalar_handleBlockLineBreak` preserves correspondence
    when it returns `some`. -/
theorem handleBlockLineBreak_corr (sc : ScannerState) (sp : SurfPos)
    (content : String) (contentIndent inputEnd : Nat)
    {content' : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hsome : collectPlainScalar_handleBlockLineBreak sc content contentIndent inputEnd
             = some (content', s')) :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold collectPlainScalar_handleBlockLineBreak at hsome
  dsimp only [] at hsome
  obtain ⟨sp_cn, hcorr_cn⟩ := consumeNewline_unconditional_corr sc sp hcorr
  obtain ⟨sp_bl, hcorr_bl⟩ :=
    skipBlankLinesLoop_corr (consumeNewline sc) sp_cn 0 _ inputEnd hcorr_cn
  obtain ⟨_, sp_sk, _, hcorr_sk⟩ :=
    skipSpaces_corr (skipBlankLinesLoop (consumeNewline sc) 0
                      (inputEnd - (consumeNewline sc).offset + 1) inputEnd).2
                    sp_bl hcorr_bl
  split at hsome
  · exact absurd hsome (by simp)  -- col < contentIndent → none
  · split at hsome
    · exact absurd hsome (by simp)  -- document boundary → none
    · simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨-, rfl⟩ := hsome; exact ⟨sp_sk, hcorr_sk⟩

/-- `collectPlainScalarLoop` preserves correspondence on `.ok` paths. -/
theorem collectPlainScalarLoop_corr (sc : ScannerState) (sp : SurfPos)
    (content spaces : String) (fuel : Nat)
    (inFlow : Bool) (contentIndent : Nat) (inputEnd : Nat)
    {result : PlainScalarResult}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : collectPlainScalarLoop sc content spaces fuel inFlow contentIndent inputEnd
           = .ok result) :
    ∃ sp', ScannerSurfCorr result.state sp' := by
  induction fuel generalizing sc sp content spaces with
  | zero =>
    simp [collectPlainScalarLoop] at hok; subst hok
    exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at hok
    split at hok
    · -- peek? = none
      have h := Except.ok.inj hok; subst h
      exact ⟨sp, hcorr⟩
    · -- peek? = some c
      rename_i c hpeek
      split at hok
      · -- terminates?: state preserved by collectPlainScalar_terminates?
        rename_i r_term h_term
        have h := Except.ok.inj hok; subst h
        have hst := terminates_state_eq c sc content spaces inFlow r_term h_term
        rw [hst]; exact ⟨sp, hcorr⟩
      · -- not terminated
        split at hok
        · -- isLineBreakBool c
          split at hok
          · -- inFlow: foldQuotedNewlines
            simp only [bind, Except.bind] at hok
            split at hok
            · exact absurd hok (by simp)
            · rename_i fold_result hfold
              obtain ⟨sp_fold, hcorr_fold⟩ := foldQuotedNewlines_corr sc sp hcorr hfold
              split at hok
              · have h := Except.ok.inj hok; subst h; exact ⟨sp_fold, hcorr_fold⟩  -- '#'
              · exact ih _ sp_fold _ _ hcorr_fold hok
          · -- not inFlow: handleBlockLineBreak
            split at hok
            · -- none
              have h := Except.ok.inj hok; subst h; exact ⟨sp, hcorr⟩
            · -- some (content', s_hb)
              rename_i pair hhandle
              obtain ⟨sp_hb, hcorr_hb⟩ :=
                handleBlockLineBreak_corr sc sp content contentIndent inputEnd hcorr hhandle
              split at hok
              · have h := Except.ok.inj hok; subst h; exact ⟨sp_hb, hcorr_hb⟩  -- '#'
              · exact ih _ sp_hb _ _ hcorr_hb hok
        · -- not line break
          split at hok
          · -- isWhiteSpaceBool c
            obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
            exact ih sc.advance sp_adv _ _ hcorr_adv hok
          · -- not whitespace
            split at hok
            · -- not plain safe: terminate
              have h := Except.ok.inj hok; subst h; exact ⟨sp, hcorr⟩
            · -- plain content char: advance
              obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
              exact ih sc.advance sp_adv _ _ hcorr_adv hok

/-- `scanPlainScalar` preserves correspondence on `.ok` paths. -/
theorem scanPlainScalar_corr (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok  -- collectPlainScalarLoop error
  · rename_i result hloop
    simp only [Except.ok.injEq] at hok; subst hok
    obtain ⟨sp_loop, hcorr_loop⟩ := collectPlainScalarLoop_corr sc sp "" "" _ _ _ _ hcorr hloop
    exact ⟨sp_loop,
      corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_loop)⟩

/-! ## §7 Block Scalar -/

/-- `consumeExactSpaces` preserves correspondence (2nd component). -/
theorem consumeExactSpaces_corr (sc : ScannerState) (sp : SurfPos) (count : Nat)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (consumeExactSpaces sc count).2 sp' := by
  induction count generalizing sc sp with
  | zero => simp [consumeExactSpaces]; exact ⟨sp, hcorr⟩
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
      exact ih sc.advance sp' hcorr'
    · exact ⟨sp, hcorr⟩

/-- `collectLineContentLoop` preserves correspondence (2nd component). -/
theorem collectLineContentLoop_corr (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (collectLineContentLoop sc content fuel).2 sp' := by
  induction fuel generalizing sc sp content with
  | zero => simp [collectLineContentLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectLineContentLoop; split
    · rename_i c hpeek; split
      · exact ⟨sp, hcorr⟩  -- line break: stop
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' _ hcorr'
    · exact ⟨sp, hcorr⟩

/-- `collectBlockScalarLoop` preserves correspondence (2nd component). -/
theorem collectBlockScalarLoop_corr (sc : ScannerState) (sp : SurfPos)
    (rawContent : String) (fuel : Nat) (contentIndent inputEnd : Nat)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (collectBlockScalarLoop sc rawContent fuel contentIndent inputEnd).2 sp' := by
  induction fuel generalizing sc sp rawContent with
  | zero => simp [collectBlockScalarLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · exact ⟨sp, hcorr⟩  -- document boundary
    · -- else branch
      generalize hce : consumeExactSpaces sc contentIndent = p at *
      obtain ⟨spacesConsumed, s_after_spaces⟩ := p
      simp only [] at *
      obtain ⟨sp_spaces, hcorr_spaces⟩ : ∃ sp', ScannerSurfCorr s_after_spaces sp' := by
        have := consumeExactSpaces_corr sc sp contentIndent hcorr
        rw [hce] at this; exact this
      split
      · exact ⟨sp_spaces, hcorr_spaces⟩  -- none
      · rename_i c hpeek
        split
        · -- line break: consumeNewline + recurse
          rename_i hlb
          obtain ⟨sp_cn, hcorr_cn⟩ :=
            consumeNewline_corr _ sp_spaces c hcorr_spaces hpeek hlb
          exact ih _ sp_cn _ hcorr_cn
        · split
          · exact ⟨sp, hcorr⟩  -- under-indent: returns original (rawContent, s)
          · -- collect content
            generalize hcl : collectLineContentLoop s_after_spaces "" _ = q2 at *
            obtain ⟨lineContent, s_after_line⟩ := q2
            simp only [] at *
            obtain ⟨sp_line, hcorr_line⟩ : ∃ sp', ScannerSurfCorr s_after_line sp' := by
              have := collectLineContentLoop_corr s_after_spaces sp_spaces ""
                (inputEnd - s_after_spaces.offset + 1) hcorr_spaces
              rw [hcl] at this; exact this
            split
            · -- line break after content
              rename_i c2 hpeek2
              split
              · rename_i hlb2
                obtain ⟨sp_cn, hcorr_cn⟩ :=
                  consumeNewline_corr _ sp_line c2 hcorr_line hpeek2 hlb2
                exact ih _ sp_cn _ hcorr_cn
              · exact ih _ sp_line _ hcorr_line
            · exact ⟨sp_line, hcorr_line⟩  -- none after content

/-- `parseBlockHeaderLoop` preserves correspondence (3rd component). -/
theorem parseBlockHeaderLoop_corr (sc : ScannerState) (sp : SurfPos)
    (chomp : ChompStyle) (explicitOffset : Option Nat) (fuel : Nat)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (parseBlockHeaderLoop sc chomp explicitOffset fuel).2.2 sp' := by
  induction fuel generalizing sc sp chomp explicitOffset with
  | zero => simp [parseBlockHeaderLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
      exact ih sc.advance sp' .strip explicitOffset hcorr'
    · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
      exact ih sc.advance sp' .keep explicitOffset hcorr'
    · rename_i c hpeek hne_minus hne_plus; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' chomp _ hcorr'
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

/-- `scanBlockScalarSkipComment` preserves correspondence. -/
theorem scanBlockScalarSkipComment_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (scanBlockScalarSkipComment sc) sp' := by
  unfold scanBlockScalarSkipComment
  split
  · -- peek? = some '#'
    dsimp only []
    split  -- match on peekBack?
    · -- peekBack? = some c
      split  -- if (isWhiteSpaceBool c || ...)
      · -- commentOk = true
        obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
        obtain ⟨sp_ct, _, hcorr_ct⟩ :=
          collectCommentTextLoop_corr sc.advance sp_adv ""
            (sc.advance.inputEnd - sc.advance.offset) hcorr_adv (Nat.le.refl)
        exact ⟨sp_ct, ⟨hcorr_ct.chars_from, hcorr_ct.col_eq, hcorr_ct.end_eq, hcorr_ct.input_prefix, hcorr_ct.indent_cols_nonneg⟩⟩
      · -- commentOk = false
        exact ⟨sp, hcorr⟩
    · -- peekBack? = none → commentOk = false
      exact ⟨sp, hcorr⟩
  · -- peek? ≠ some '#'
    exact ⟨sp, hcorr⟩

/-- `scanBlockScalarConsumeNewline` preserves correspondence on `.ok` paths. -/
theorem scanBlockScalarConsumeNewline_corr (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanBlockScalarConsumeNewline sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanBlockScalarConsumeNewline at hok
  split at hok
  · rename_i c hpeek
    split at hok
    · -- isLineBreak: consumeNewline
      rename_i hlb
      have h := Except.ok.inj hok; subst h
      exact consumeNewline_corr sc sp c hcorr hpeek hlb
    · split at hok
      · have h := Except.ok.inj hok; subst h; exact ⟨sp, hcorr⟩
      · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; exact ⟨sp, hcorr⟩

/-- `scanBlockScalarBody` preserves correspondence on `.ok` paths. -/
theorem scanBlockScalarBody_corr (sc_orig sc_after_nl : ScannerState)
    (sp : SurfPos) (chomp : ChompStyle) (explicitOffset : Option Nat)
    (isLiteral : Bool) (startPos : YamlPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc_after_nl sp)
    (hok : scanBlockScalarBody sc_orig sc_after_nl chomp explicitOffset isLiteral startPos
           = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanBlockScalarBody at hok
  dsimp only [] at hok  -- inline let bindings
  -- split on match autoDetectErr? (the outer match)
  split at hok
  · -- some err: impossible (Except.error = Except.ok)
    exact absurd hok (by simp)
  · -- none: body
    -- contentIndent is the .fst of the match-on-explicitOffset pair, not yet reduced
    let contentIndent := (match explicitOffset with
      | some m => ((max 0 (sc_orig.currentIndent + (m : Int))).toNat, (none : Option ScanError))
      | none => autoDetectBlockScalarIndent sc_after_nl
          (max 0 (sc_orig.currentIndent + 1)).toNat sc_orig.inputEnd).fst
    let fuel := sc_orig.inputEnd - sc_after_nl.offset + 1
    have hcorr_res : ∃ sp', ScannerSurfCorr
        (collectBlockScalarLoop sc_after_nl "" fuel contentIndent sc_orig.inputEnd).snd sp' :=
      collectBlockScalarLoop_corr sc_after_nl sp "" fuel contentIndent sc_orig.inputEnd hcorr
    obtain ⟨sp_loop, hcorr_loop⟩ := hcorr_res
    have h := Except.ok.inj hok; subst h
    exact ⟨sp_loop, ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq, hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩⟩

/-- `scanBlockScalar` preserves correspondence on `.ok` paths. -/
theorem scanBlockScalar_corr (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanBlockScalar sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanBlockScalar at hok
  dsimp only [] at hok  -- inline lets
  -- advance (past '|' or '>')
  obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
  -- parseBlockHeaderLoop
  obtain ⟨sp_hdr, hcorr_hdr⟩ := parseBlockHeaderLoop_corr sc.advance sp_adv .clip none 2 hcorr_adv
  -- skipWhitespace
  obtain ⟨sp_ws, _, hcorr_ws⟩ := skipWhitespace_corr _ sp_hdr hcorr_hdr
  -- scanBlockScalarSkipComment
  obtain ⟨sp_cmt, hcorr_cmt⟩ :=
    scanBlockScalarSkipComment_corr _ sp_ws hcorr_ws
  -- match on scanBlockScalarConsumeNewline
  split at hok
  · simp at hok  -- error
  · rename_i s_after_nl hcn
    obtain ⟨sp_nl, hcorr_nl⟩ := scanBlockScalarConsumeNewline_corr _ sp_cmt hcorr_cmt hcn
    exact scanBlockScalarBody_corr sc s_after_nl sp_nl _ _ _ _ hcorr_nl hok

end Lean4Yaml.Proofs.ScalarCoupling
