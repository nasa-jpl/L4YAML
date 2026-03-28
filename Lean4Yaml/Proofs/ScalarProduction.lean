import Lean4Yaml.Proofs.ScalarCoupling

/-! # Scalar Production Coupling (Phase B of v0.4.4)

    Strengthen the `_corr` theorems from `ScalarCoupling.lean` to additionally
    produce surface-syntax derivation trees (`SCDoubleQuoted`, `SCSingleQuoted`,
    `SNsPlain`, `SCLLiteral`, `SCLFolded`).

    Strategy: use `n = 0` and `c = .blockIn` existentially so that indentation
    requirements (`SIndent 0`, `SFlowLinePrefix 0`) become trivial.

    **Status**: Double-quoted scalar proven modulo 3 sorry'd sub-lemmas
    (processEscape_prod, foldQuotedNewlines_prod, escaped-linebreak construction).
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.ScalarProduction

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScannerCoupling
open Lean4Yaml.Proofs.ScalarCoupling

/-! ## §1 Helpers -/

-- Derive `offset < inputEnd` from `peek? = some c`
private theorem peek_some_has_more {sc : ScannerState} {c : Char}
    (hpeek : sc.peek? = some c) : sc.offset < sc.inputEnd := by
  unfold ScannerState.peek? at hpeek
  split at hpeek
  · assumption
  · cases hpeek

-- Derive exact surface position from `peek? = some c` + `ScannerSurfCorr`
private theorem peek_some_sp {sc : ScannerState} {sp : SurfPos} {c : Char}
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some c) :
    ∃ rest, sp = ⟨c :: rest, sc.col⟩ := by
  have hmore := peek_some_has_more hpeek
  obtain ⟨c', rest, hchars, hpeek'⟩ := peek_corr sc sp hcorr hmore
  have : c' = c := Option.some.inj (hpeek'.symm.trans hpeek)
  subst this
  exact ⟨rest, by
    cases sp with | mk cs cl =>
    simp only [SurfPos.mk.injEq]
    exact ⟨hchars, hcorr.col_eq⟩⟩

-- Prepend a `SNbDoubleChar` to the first line of `SNbDoubleMultiLine`
private theorem SNbDoubleMultiLine_prepend (s s₁ s_end : SurfPos)
    (hchar : SNbDoubleChar s s₁)
    (hrest : SNbDoubleMultiLine 0 s₁ s_end) :
    SNbDoubleMultiLine 0 s s_end := by
  cases hrest with
  | single _ _ hline =>
    exact SNbDoubleMultiLine.single 0 s s_end
      (GStar.cons s s₁ s_end hchar hline)
  | multi _ s₁' s₂ s₃ _ hline hbreak hcont =>
    exact SNbDoubleMultiLine.multi 0 s s₁' s₂ s₃ s_end
      (GStar.cons s s₁ s₁' hchar hline) hbreak hcont

-- Bridge: `¬isLineBreakBool c = true → ¬isLineBreakProp c`
private theorem not_lineBreak_bool_to_prop {c : Char}
    (h : ¬isLineBreakBool c = true) : ¬isLineBreakProp c :=
  fun hlb => h ((isLineBreak_iff c).mpr hlb)

/-! ## §2 Sorry'd sub-lemmas -/

-- When `foldQuotedNewlines` succeeds at a line-break position,
-- the consumed chars form an `SSDoubleBreak`.
-- **TODO**: prove by decomposing consumeNewline + foldQuotedNewlinesLoop + skipWhitespace
-- into SBBreak + GStar SLEmpty + SFlowLinePrefix
theorem foldQuotedNewlines_prod (sc : ScannerState) (sp : SurfPos)
    {content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hfold : foldQuotedNewlines sc = .ok (content, s')) :
    ∃ sp', SSDoubleBreak 0 sp sp' ∧ ScannerSurfCorr s' sp' := by
  sorry

-- When `processEscape` succeeds, the `\` + escape chars form a valid `SNbDoubleChar`
-- starting from `⟨'\\' :: rest, col⟩`.
-- **TODO**: prove by case analysis on escape type (named / hex2 / hex4 / hex8)
theorem processEscape_prod (sc_bs : ScannerState) (rest : List Char) (col : Nat)
    {ch : Char} {s' : ScannerState}
    (hcorr_bs : ScannerSurfCorr sc_bs ⟨rest, col + 1⟩)
    (hproc : processEscape sc_bs = .ok (ch, s')) :
    ∃ sp', SNbDoubleChar ⟨'\\' :: rest, col⟩ sp' ∧ ScannerSurfCorr s' sp' := by
  sorry

/-! ## §3 Double-Quoted Scalar -/

-- `collectDoubleQuotedLoop` success produces:
-- 1. Body: `SNbDoubleMultiLine 0` from current position to before closing `"`
-- 2. Close: `GLit '"'` consuming the closing `"`
-- 3. `ScannerSurfCorr` preserved after closing `"`
theorem collectDoubleQuotedLoop_prod (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s')) :
    ∃ sp_body sp_close,
      SNbDoubleMultiLine 0 sp sp_body ∧
      GLit '"' sp_body sp_close ∧
      ScannerSurfCorr s' sp_close := by
  induction fuel generalizing sc sp content with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)  -- none → error
    · -- peek? = some '"': closing quote
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      exact ⟨⟨'"' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
             SNbDoubleMultiLine.single 0 _ _ (GStar.nil _),
             GLit.mk rest sc.col,
             advance_non_newline_corr sc '"' rest hcorr
               (peek_some_has_more hpeek) (by decide)⟩
    · -- peek? = some '\\': escape sequence
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv :=
        advance_non_newline_corr sc '\\' rest hcorr
          (peek_some_has_more hpeek) (by decide)
      dsimp only [] at hok
      split at hok
      · -- next peek = some c2
        rename_i c2 hpeek2
        split at hok
        · -- isLineBreakBool c2: escaped newline → multiline break
          obtain ⟨sp_cn, hcorr_cn⟩ :=
            consumeNewline_unconditional_corr sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv
          obtain ⟨sp_ws, _, hcorr_ws⟩ :=
            skipWhitespace_corr (consumeNewline sc.advance) sp_cn hcorr_cn
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
            ih _ sp_ws content hcorr_ws hok
          -- Need SSDoubleBreak.escaped from ⟨'\\' :: rest, sc.col⟩ to sp_ws
          sorry -- constructing SSDoubleBreak.escaped (deferred)
        · -- not line break: processEscape → SNbDoubleChar
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)  -- processEscape error
          · rename_i esc_result hproc
            obtain ⟨sp_esc, h_dq_char, hcorr_esc⟩ :=
              processEscape_prod sc.advance rest sc.col hcorr_adv hproc
            obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
              ih _ sp_esc _ hcorr_esc hok
            exact ⟨sp_body, sp_close,
                   SNbDoubleMultiLine_prepend _ _ _ h_dq_char h_body,
                   h_glit, h_corr⟩
      · exact absurd hok (by simp)  -- none → error
    · -- peek? = some c (regular char, c ≠ '"', c ≠ '\\')
      rename_i _opt c hne_dq hne_bs hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      split at hok
      · -- isLineBreakBool c: fold newlines → SNbDoubleMultiLine.multi
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)  -- fold error
        · rename_i fold_result hfold
          obtain ⟨sp_fold, h_break, hcorr_fold⟩ :=
            foldQuotedNewlines_prod sc ⟨c :: rest, sc.col⟩ hcorr hfold
          split at hok  -- doc marker guard
          · simp at hok
          · split at hok  -- underIndented guard
            · simp at hok
            · split at hok  -- do-notation residue
              · simp at hok
              · obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
                  ih _ sp_fold _ hcorr_fold hok
                exact ⟨sp_body, sp_close,
                       SNbDoubleMultiLine.multi 0
                         ⟨c :: rest, sc.col⟩ ⟨c :: rest, sc.col⟩
                         sp_fold ⟨[], 0⟩ _
                         (GStar.nil _) h_break h_body,
                       h_glit, h_corr⟩
      · -- not line break: control char check
        split at hok
        · simp at hok  -- invalid control char → error
        · -- valid char: advance + recurse
          rename_i hne_lb hne_ctrl
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc c rest hcorr hmore h_not_nl
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
            ih sc.advance ⟨rest, sc.col + 1⟩ _ hcorr_adv hok
          have h_dq_char : SNbDoubleChar ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
            SNbDoubleChar.plain c rest sc.col
              (not_lineBreak_bool_to_prop hne_lb) hne_bs hne_dq
          exact ⟨sp_body, sp_close,
                 SNbDoubleMultiLine_prepend _ _ _ h_dq_char h_body,
                 h_glit, h_corr⟩

-- `scanDoubleQuoted` success produces a complete `SCDoubleQuoted 0 .blockIn`.
-- Precondition: `sc.peek? = some '"'` (from scanner dispatch).
theorem scanDoubleQuoted_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_dq : sc.peek? = some '"')
    (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp', SCDoubleQuoted 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  -- Extract opening quote position
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek_dq
  subst hsp_eq
  have hmore := peek_some_has_more hpeek_dq
  have hcorr_adv :=
    advance_non_newline_corr sc '"' rest hcorr hmore (by decide)
  -- Loop: collectDoubleQuotedLoop
  split at hok
  · simp at hok  -- loop error
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    obtain ⟨sp_body, sp_close, h_body, h_glit_close, hcorr_close⟩ :=
      collectDoubleQuotedLoop_prod sc.advance ⟨rest, sc.col + 1⟩ "" _ _ _ _ _
        hcorr_adv hloop
    -- validateTrailingContent: do-notation bind on Except Unit
    split at hok  -- if !sc.inFlow
    · -- !inFlow = true: validate
      split at hok  -- match on validateTrailingContent result
      · simp at hok  -- validation error
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close,
               SCDoubleQuoted.mk 0 .blockIn _ _ _ _
                 (GLit.mk rest sc.col) h_body h_glit_close,
               corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_close)⟩
    · -- !inFlow = false: no validate
      split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close,
               SCDoubleQuoted.mk 0 .blockIn _ _ _ _
                 (GLit.mk rest sc.col) h_body h_glit_close,
               corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_close)⟩

end Lean4Yaml.Proofs.ScalarProduction
