import Lean4Yaml.Proofs.ScannerCoupling
import Lean4Yaml.Proofs.NodeProduction

/-! # Preprocessing Production Coupling (Layer 4b)

    Connects scanner preprocessing to surface grammar productions:
    - `skipToContentLoop` at col=0 → `GStar SLComment` (for `SLDocumentPrefix`)
    - `skipToContentLoop` after break → `SSLComments` (for separation between tokens)
    - `scanNextToken_preprocess` → correspondence preservation (already exists; this file adds grammar output)

    ## Architecture

    Each `skipToContentLoop` iteration: `skipToContentWs` → `skipToContentComment` → break check.
    - Break → `SBBreak` resets col to 0, then recurse
    - Non-break or EOF → stop

    An iteration that ends with break produces `SLComment sp ⟨rest, 0⟩`:
      `SSeparateInLine · GOpt SCNbCommentText · SBComment(break)`

    The `SLComment` constructor requires `SSeparateInLine` — satisfied by
    `startOfLine` when sp.col = 0, or by `whites` when whitespace precedes.
    After every break, col resets to 0, so the invariant propagates.

    The final non-break/EOF iteration does NOT produce `SLComment` — it just
    consumes whitespace that becomes part of the next token's indentation.
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.PreprocessProduction

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScannerCoupling
open Lean4Yaml.Proofs.NodeProduction

/-! ## §1 Helpers -/

/-- `GStar SSWhite` at col=0 gives `SSeparateInLine`. -/
theorem GStar_SSWhite_to_SSeparateInLine_col0 (sp sp' : SurfPos)
    (h_ws : GStar SSWhite sp sp') (hcol : sp.col = 0) :
    SSeparateInLine sp sp' := by
  by_cases h : sp = sp'
  · subst h
    cases sp with | mk chars col =>
    dsimp only [] at hcol; subst hcol
    exact SSeparateInLine.startOfLine chars
  · exact SSeparateInLine.whites sp sp' (GStar_to_GPlus h_ws h)

/-- Strengthened `consumeNewline`: produces `SBBreak` and land at col=0. -/
theorem consumeNewline_break_prod (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true) :
    ∃ sp', SBBreak sp sp' ∧ sp'.col = 0 ∧
           ScannerSurfCorr (consumeNewline sc) sp' := by
  have hmore := peek_some_hasMore sc c hpeek
  obtain ⟨rest, hchars⟩ := peek_some_chars sc sp c hcorr hpeek
  have hcol := hcorr.col_eq
  have hsp_eq : sp = ⟨c :: rest, sc.col⟩ := by
    cases sp with | mk cs cl => simp only [] at hchars hcol; subst hchars; subst hcol; rfl
  subst hsp_eq
  simp [isLineBreakBool, Bool.or_eq_true, beq_iff_eq] at hlb
  unfold consumeNewline
  rcases hlb with rfl | rfl
  · -- '\n'
    simp only [hpeek]
    exact ⟨⟨rest, 0⟩, SBBreak.lf rest sc.col, rfl,
      corr_of_needIndentCheck_update true (advance_newline_corr sc rest hcorr hmore)⟩
  · -- '\r'
    simp only [hpeek]
    have hadv := advance_cr_corr sc rest hcorr hmore
    split
    · -- CRLF
      rename_i hpeek2
      have hmore2 := peek_some_hasMore sc.advance '\n' hpeek2
      obtain ⟨rest2, hchars2⟩ := peek_some_chars sc.advance ⟨rest, 0⟩ '\n' hadv hpeek2
      subst hchars2
      exact ⟨⟨rest2, 0⟩, SBBreak.crLf rest2 sc.col, rfl,
        corr_of_needIndentCheck_update true (skip_byte_corr sc.advance '\n' rest2 0 hadv hmore2)⟩
    · -- lone CR
      exact ⟨⟨rest, 0⟩, SBBreak.cr rest sc.col, rfl,
        corr_of_needIndentCheck_update true hadv⟩

/-! ## §1b Column-monotonicity lemmas for whitespace/comment productions

    SSWhite and SCNbCommentText strictly increment column. GStar SSWhite
    is therefore col-monotone. When both endpoints are at col=0,
    GStar SSWhite and GOpt SCNbCommentText must be nil/none. -/

theorem sswhite_col_succ (sp sp' : SurfPos) (h : SSWhite sp sp') : sp'.col = sp.col + 1 := by
  cases h <;> rfl

theorem gstar_sswhite_col_ge (sp sp' : SurfPos) (h : GStar SSWhite sp sp') :
    sp'.col ≥ sp.col := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ s₁ _ hw _ ih =>
    have := sswhite_col_succ _ s₁ hw
    omega

/-- If GStar SSWhite starts and ends at the same column, it must be nil. -/
theorem gstar_sswhite_col_eq_nil (sp sp' : SurfPos)
    (hcol : sp.col = sp'.col) (h : GStar SSWhite sp sp') : sp' = sp := by
  cases h with
  | nil => rfl
  | cons _ s₁ _ hw hrest =>
    exfalso
    have h1 := sswhite_col_succ _ s₁ hw
    have h2 := gstar_sswhite_col_ge s₁ sp' hrest
    omega

theorem snbchar_col_succ (sp sp' : SurfPos) (h : SNbChar sp sp') : sp'.col = sp.col + 1 := by
  cases h <;> rfl

theorem gstar_snbchar_col_ge (sp sp' : SurfPos) (h : GStar SNbChar sp sp') :
    sp'.col ≥ sp.col := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ s₁ _ hc _ ih =>
    have := snbchar_col_succ _ s₁ hc
    omega

/-- SCNbCommentText strictly increments column (consumes '#' + body). -/
theorem scnb_comment_col_gt (sp sp' : SurfPos)
    (h : SCNbCommentText sp sp') : sp'.col > sp.col := by
  cases h
  rename_i rest col hstar
  have := gstar_snbchar_col_ge ⟨rest, col + 1⟩ sp' hstar
  dsimp only [] at this ⊢; omega

/-- GOpt SCNbCommentText at same column implies none. -/
theorem gopt_comment_col_eq_none (sp sp' : SurfPos)
    (hcol : sp.col = sp'.col) (h : GOpt SCNbCommentText sp sp') : sp' = sp := by
  cases h
  · rfl
  · rename_i hc
    exfalso; have := scnb_comment_col_gt _ _ hc; omega

/-! ## §1c collectCommentTextLoop stops at break or EOF

    The scanner's `collectCommentTextLoop` greedily consumes all non-break
    characters. After it stops, the scanner's `peek?` returns either `none`
    (EOF/end-of-input) or `some c` where `c` is a line break. -/

/-- After `collectCommentTextLoop`, the next character is a line break or EOF. -/
theorem collectCommentTextLoop_stops_at_break_or_eof
    (sc : ScannerState) (text : String) (fuel : Nat)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset) :
    let s' := (collectCommentTextLoop sc text fuel).2
    s'.peek? = none ∨ ∃ c, s'.peek? = some c ∧ isLineBreakBool c = true := by
  induction fuel generalizing sc text with
  | zero =>
    -- fuel = 0: returns sc unchanged. hfuel → offset ≥ inputEnd → peek? = none
    unfold collectCommentTextLoop; dsimp only []
    left; unfold ScannerState.peek?; split
    · exfalso; omega
    · rfl
  | succ n ih =>
    unfold collectCommentTextLoop; dsimp only []
    split
    · -- peek? = some c
      rename_i c hpeek
      split
      · -- isLineBreakBool c = true: stops, returns sc
        right; exact ⟨c, hpeek, ‹_›⟩
      · -- ¬isLineBreakBool: advance and recurse
        exact ih sc.advance (text.push c)
          (advance_fuel_budget sc n (peek_some_hasMore sc c hpeek) hfuel)
    · -- peek? = none: stops, returns sc
      left; assumption

/-! ## §1a BOM Grammar Gap

    The YAML scanner allows `#` comments when `peekBack?` is the BOM character
    (U+FEFF), even without preceding whitespace. The grammar requires
    `SSeparateInLine` (s-white+ or start-of-line) before comment text,
    but after BOM at col=1, neither constructor applies. This is a genuine
    gap between the scanner and the formalized grammar. We capture it in
    a single sorry theorem used by multiple proofs. -/

-- BOM grammar gap: comment at col≠0 without preceding whitespace.
-- SSBComment.withSep needs SSeparateInLine which can't be built
-- without whitespace at col≠0; SSBComment.noSep needs SBComment
-- at the start position, but the start has '#' (not a break/eof).
theorem bom_noWhitespace_ssbcomment (sp sp_cmt sp_end : SurfPos)
    (h_cmtv : SCNbCommentText sp sp_cmt) (h_break : SBComment sp_cmt sp_end) :
    SSBComment sp sp_end := sorry

/-! ## §2 skipToContentLoop at col=0 → GStar SLComment

    When entering at column 0, each iteration produces one `SLComment`
    (if a break is hit) or stops (non-break/EOF). The col=0 invariant
    is maintained because every `SBBreak` resets col to 0.

    **Return type decomposition**: The loop produces `GStar SLComment sp sp_mid`
    (complete comment lines) separately from `ScannerSurfCorr s_result sp'`
    (scanner position after trailing whitespace/comment in the final iteration).
    The gap `sp_mid → sp'` represents whitespace consumed by the final iteration
    that becomes indentation/separation for the following content production. -/

/-- `skipToContentLoop` at col=0 produces comment lines + correspondence.
    `sp_mid` is where comment lines end; `sp_ws` is after trailing whitespace;
    `sp'` is after optional comment. The gap `sp_mid → sp_ws → sp'` is the
    final iteration’s whitespace + comment that is NOT part of `GStar SLComment`. -/
theorem skipToContentLoop_col0_prod
    (sc : ScannerState) (sp : SurfPos) (fuel : Nat) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result) :
    ∃ sp_mid sp_ws sp', GStar SLComment sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' := by
  induction fuel generalizing sc sp s_result with
  | zero =>
    simp [skipToContentLoop] at hok; subst hok
    exact ⟨sp, sp, sp, GStar.nil _, hcol, GStar.nil _, GOpt.none _, hcorr⟩
  | succ fuel' ih =>
    unfold skipToContentLoop at hok
    dsimp only [] at hok
    split at hok
    · -- skipToContentWs = .error
      simp at hok
    · -- skipToContentWs = .ok s1
      rename_i s1 hok_ws
      obtain ⟨sp_ws, hstar_ws, hcorr_ws⟩ := skipToContentWs_ok_corr sc sp s1 hcorr hok_ws
      obtain ⟨sp_cmt, hopt_cmt, hcorr_cmt⟩ := skipToContentComment_corr s1 sp_ws hcorr_ws
      split at hok
      · -- peek? = some c
        rename_i c hpeek
        split at hok
        · -- isLineBreakBool c = true → break → recurse
          rename_i hlb
          obtain ⟨sp_brk, h_break, hcol_brk, hcorr_brk⟩ :=
            consumeNewline_break_prod (skipToContentComment s1) sp_cmt c hcorr_cmt hpeek hlb
          -- Build SLComment from this iteration
          have h_sep : SSeparateInLine sp sp_ws :=
            GStar_SSWhite_to_SSeparateInLine_col0 sp sp_ws hstar_ws hcol
          have h_lcomment : SLComment sp sp_brk :=
            SLComment.mk sp sp_ws sp_cmt sp_brk h_sep hopt_cmt
              (SBComment.break _ _ h_break)
          -- Fuel budget for recursion
          have ⟨h_ws_off, h_ws_end⟩ := skipToContentWs_offset_mono sc s1 hok_ws
          have ⟨h_sc_off, h_sc_end⟩ := skipToContentComment_offset_mono s1
          have ⟨h_cn_off, h_cn_end⟩ :=
            consumeNewline_offset_advance (skipToContentComment s1) c hpeek hlb
          have h_scc_lt : (skipToContentComment s1).offset < (skipToContentComment s1).inputEnd :=
            peek_some_hasMore (skipToContentComment s1) c hpeek
          have h_cn_inputEnd : (consumeNewline (skipToContentComment s1)).inputEnd = sc.inputEnd := by
            rw [h_cn_end, h_sc_end, h_ws_end]
          have h_scc_end_eq : (skipToContentComment s1).inputEnd = sc.inputEnd := by
            rw [h_sc_end, h_ws_end]
          have h_sc_lt_inputEnd : sc.offset < sc.inputEnd := by omega
          have hfuel' : fuel' ≥ (consumeNewline (skipToContentComment s1)).inputEnd -
                                 (consumeNewline (skipToContentComment s1)).offset + 1 := by
            rw [h_cn_inputEnd]
            by_cases hle : (consumeNewline (skipToContentComment s1)).offset ≤ sc.inputEnd
            · omega
            · -- cn.offset > sc.inputEnd → Nat subtraction gives 0
              have hgt : (consumeNewline (skipToContentComment s1)).offset > sc.inputEnd := by
                omega
              have : sc.inputEnd - (consumeNewline (skipToContentComment s1)).offset = 0 := by omega
              rw [this]; omega
          -- Recurse — two sub-cases from the if
          split at hok
          · -- !isInFlowSequence: simpleKeyAllowed update
            have hcorr_next : ScannerSurfCorr
                { consumeNewline (skipToContentComment s1) with simpleKeyAllowed := true }
                ⟨sp_brk.chars, 0⟩ := by
              rw [← show sp_brk.col = 0 from hcol_brk]
              cases sp_brk; dsimp only [] at hcol_brk ⊢
              subst hcol_brk
              exact corr_of_simpleKeyAllowed_update true hcorr_brk
            obtain ⟨sp_mid, sp_ws_r, sp', hstar_lc, hcol_mid, hws_r, hcmt_r, hcorr'⟩ :=
              ih _ ⟨sp_brk.chars, 0⟩ s_result hcorr_next rfl hfuel' hok
            exact ⟨sp_mid, sp_ws_r, sp', GStar.cons _ ⟨sp_brk.chars, 0⟩ _
              (by cases sp_brk; dsimp only [] at hcol_brk ⊢; subst hcol_brk; exact h_lcomment)
              hstar_lc, hcol_mid, hws_r, hcmt_r, hcorr'⟩
          · -- isInFlowSequence
            obtain ⟨sp_mid, sp_ws_r, sp', hstar_lc, hcol_mid, hws_r, hcmt_r, hcorr'⟩ :=
              ih _ sp_brk s_result hcorr_brk hcol_brk hfuel' hok
            exact ⟨sp_mid, sp_ws_r, sp', GStar.cons _ sp_brk _ h_lcomment hstar_lc,
                   hcol_mid, hws_r, hcmt_r, hcorr'⟩
        · -- not line break → stop (trailing ws from final iteration)
          have hinj := Except.ok.inj hok; subst hinj
          exact ⟨sp, sp_ws, sp_cmt, GStar.nil _, hcol, hstar_ws, hopt_cmt, hcorr_cmt⟩
      · -- peek? = none → stop (EOF, trailing ws/comment from final iteration)
        have hinj := Except.ok.inj hok; subst hinj
        exact ⟨sp, sp_ws, sp_cmt, GStar.nil _, hcol, hstar_ws, hopt_cmt, hcorr_cmt⟩

/-- Top-level: `skipToContent` at col=0 produces `GStar SLComment` + correspondence. -/
theorem skipToContent_col0_prod
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : skipToContent sc = .ok s_result) :
    ∃ sp_mid sp_ws sp', GStar SLComment sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' := by
  unfold skipToContent at hok
  exact skipToContentLoop_col0_prod sc sp _ s_result hcorr hcol (by omega) hok

/-! ## §3 skipToContent at col=0 → SLDocumentPrefix -/

/-- `skipToContent` at col=0 produces `SLDocumentPrefix` + correspondence.
    The `sp_mid` is where the prefix ends (after comment lines);
    `sp'` is the scanner position (after trailing whitespace). -/
theorem skipToContent_documentPrefix_prod
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : skipToContent sc = .ok s_result) :
    ∃ sp_mid sp_ws sp', SLDocumentPrefix sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' := by
  obtain ⟨sp_mid, sp_ws, sp', hstar, hcol_mid, hws, hcmt, hcorr'⟩ :=
    skipToContent_col0_prod sc sp s_result hcorr hcol hok
  exact ⟨sp_mid, sp_ws, sp', SLDocumentPrefix.comments sp sp_mid hstar, hcol_mid, hws, hcmt, hcorr'⟩

/-! ## §4 skipToContentLoop after break → SSLComments

    When preceded by a break (SSBComment), the loop produces SSLComments:
    `SSBComment sp sp_after_break → skipToContentLoop → SSLComments sp sp'`. -/

/-- `skipToContentLoop` after a break produces `SSLComments`. -/
theorem skipToContentLoop_after_break_prod
    (sp : SurfPos) (sp_after_break : SurfPos)
    (sc : ScannerState) (fuel : Nat) (s_result : ScannerState)
    (h_sbcomment : SSBComment sp sp_after_break)
    (hcorr : ScannerSurfCorr sc sp_after_break)
    (hcol : sp_after_break.col = 0)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result) :
    ∃ sp_mid sp_ws sp', SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' := by
  obtain ⟨sp_mid, sp_ws, sp', hstar_lc, hcol_mid, hws, hcmt, hcorr'⟩ :=
    skipToContentLoop_col0_prod sc sp_after_break fuel s_result hcorr hcol hfuel hok
  exact ⟨sp_mid, sp_ws, sp', SSLComments.withComment sp sp_after_break sp_mid h_sbcomment hstar_lc,
         hcol_mid, hws, hcmt, hcorr'⟩

/-- `skipToContentLoop` at any column → `SSLComments` OR flat whitespace.
    Returns a disjunction: if a break was consumed, produces full `SSLComments`
    with `sp_mid.col = 0`; if not, `sp_mid = sp` (loop stopped on first iteration). -/
theorem skipToContentLoop_anyCol_prod
    (sc : ScannerState) (sp : SurfPos) (fuel : Nat) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result) :
    ∃ sp_mid sp_ws sp',
      (SSLComments sp sp_mid ∧ sp_mid.col = 0 ∨ sp_mid = sp) ∧
      GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
      ScannerSurfCorr s_result sp' := by
  by_cases hcol : sp.col = 0
  · -- col=0: use existing theorem, wrap as SSLComments.startOfLine
    obtain ⟨sp_mid, sp_ws, sp', hstar, hcol_mid, hws, hcmt, hcorr'⟩ :=
      skipToContentLoop_col0_prod sc sp fuel s_result hcorr hcol hfuel hok
    cases sp with | mk chars col =>
    dsimp only [] at hcol; subst hcol
    exact ⟨sp_mid, sp_ws, sp',
      Or.inl ⟨SSLComments.startOfLine chars sp_mid hstar, hcol_mid⟩,
      hws, hcmt, hcorr'⟩
  · -- col≠0: induction on fuel; first break builds SSBComment
    induction fuel generalizing sc sp s_result with
    | zero =>
      simp [skipToContentLoop] at hok; subst hok
      exact ⟨sp, sp, sp, Or.inr rfl, GStar.nil _, GOpt.none _, hcorr⟩
    | succ fuel' ih =>
      unfold skipToContentLoop at hok
      dsimp only [] at hok
      split at hok
      · simp at hok
      · rename_i s1 hok_ws
        obtain ⟨sp_ws, hstar_ws, hcorr_ws⟩ := skipToContentWs_ok_corr sc sp s1 hcorr hok_ws
        obtain ⟨sp_cmt, hopt_cmt, hcorr_cmt⟩ := skipToContentComment_corr s1 sp_ws hcorr_ws
        split at hok
        · rename_i c hpeek
          split at hok
          · -- Break found: build SSBComment, delegate rest to col0
            rename_i hlb
            obtain ⟨sp_brk, h_break, hcol_brk, hcorr_brk⟩ :=
              consumeNewline_break_prod (skipToContentComment s1) sp_cmt c hcorr_cmt hpeek hlb
            -- Build SSBComment for this iteration
            have h_sbc : SSBComment sp sp_brk := by
              by_cases h_eq : sp = sp_ws
              · -- No whitespace: use noSep path
                subst h_eq
                cases hopt_cmt
                · exact SSBComment.noSep sp sp_brk (SBComment.break _ _ h_break)
                · rename_i h_cmtv
                  exact bom_noWhitespace_ssbcomment sp sp_cmt sp_brk
                    h_cmtv (SBComment.break _ _ h_break)
              · -- Whitespace present: use withSep
                exact SSBComment.withSep sp sp_ws sp_cmt sp_brk
                  (SSeparateInLine.whites sp sp_ws (GStar_to_GPlus hstar_ws h_eq))
                  hopt_cmt (SBComment.break _ _ h_break)
            -- Fuel budget for remaining iterations
            have ⟨h_ws_off, h_ws_end⟩ := skipToContentWs_offset_mono sc s1 hok_ws
            have ⟨h_sc_off, h_sc_end⟩ := skipToContentComment_offset_mono s1
            have ⟨h_cn_off, h_cn_end⟩ :=
              consumeNewline_offset_advance (skipToContentComment s1) c hpeek hlb
            have h_cn_inputEnd :
                (consumeNewline (skipToContentComment s1)).inputEnd = sc.inputEnd := by
              rw [h_cn_end, h_sc_end, h_ws_end]
            have h_scc_lt :
                (skipToContentComment s1).offset < (skipToContentComment s1).inputEnd :=
              peek_some_hasMore (skipToContentComment s1) c hpeek
            have h_scc_end_eq : (skipToContentComment s1).inputEnd = sc.inputEnd := by
              rw [h_sc_end, h_ws_end]
            have hfuel' : fuel' ≥ (consumeNewline (skipToContentComment s1)).inputEnd -
                                   (consumeNewline (skipToContentComment s1)).offset + 1 := by
              rw [h_cn_inputEnd]
              by_cases hle : (consumeNewline (skipToContentComment s1)).offset ≤ sc.inputEnd
              · omega
              · have : sc.inputEnd - (consumeNewline (skipToContentComment s1)).offset = 0 := by
                  omega
                rw [this]; omega
            -- Recurse: after break, col=0 so use skipToContentLoop_after_break_prod
            split at hok
            · -- !isInFlowSequence: simpleKeyAllowed update
              have hcorr_next : ScannerSurfCorr
                  { consumeNewline (skipToContentComment s1) with simpleKeyAllowed := true }
                  ⟨sp_brk.chars, 0⟩ := by
                rw [← show sp_brk.col = 0 from hcol_brk]
                cases sp_brk; dsimp only [] at hcol_brk ⊢
                subst hcol_brk
                exact corr_of_simpleKeyAllowed_update true hcorr_brk
              obtain ⟨sp_mid, sp_ws_r, sp', hssl, hcol_mid, hws_r, hcmt_r, hcorr'⟩ :=
                skipToContentLoop_after_break_prod sp ⟨sp_brk.chars, 0⟩
                  { consumeNewline (skipToContentComment s1) with simpleKeyAllowed := true }
                  fuel' s_result
                  (by cases sp_brk; dsimp only [] at hcol_brk ⊢; subst hcol_brk; exact h_sbc)
                  hcorr_next rfl hfuel' hok
              exact ⟨sp_mid, sp_ws_r, sp', Or.inl ⟨hssl, hcol_mid⟩, hws_r, hcmt_r, hcorr'⟩
            · -- isInFlowSequence
              obtain ⟨sp_mid, sp_ws_r, sp', hssl, hcol_mid, hws_r, hcmt_r, hcorr'⟩ :=
                skipToContentLoop_after_break_prod sp sp_brk
                  (consumeNewline (skipToContentComment s1)) fuel' s_result
                  h_sbc hcorr_brk hcol_brk hfuel' hok
              exact ⟨sp_mid, sp_ws_r, sp', Or.inl ⟨hssl, hcol_mid⟩, hws_r, hcmt_r, hcorr'⟩
          · -- Not break: stop
            have hinj := Except.ok.inj hok; subst hinj
            exact ⟨sp, sp_ws, sp_cmt, Or.inr rfl, hstar_ws, hopt_cmt, hcorr_cmt⟩
        · -- peek? = none: stop
          have hinj := Except.ok.inj hok; subst hinj
          exact ⟨sp, sp_ws, sp_cmt, Or.inr rfl, hstar_ws, hopt_cmt, hcorr_cmt⟩

/-- `skipToContentLoop` starting at col=0 produces `SSLComments`. -/
theorem skipToContentLoop_startOfLine_prod
    (sc : ScannerState) (sp : SurfPos) (fuel : Nat) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result) :
    ∃ sp_mid sp_ws sp', SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' := by
  obtain ⟨sp_mid, sp_ws, sp', hstar_lc, hcol_mid, hws, hcmt, hcorr'⟩ :=
    skipToContentLoop_col0_prod sc sp fuel s_result hcorr hcol hfuel hok
  cases sp with | mk chars col =>
  dsimp only [] at hcol; subst hcol
  exact ⟨sp_mid, sp_ws, sp', SSLComments.startOfLine chars sp_mid hstar_lc, hcol_mid, hws, hcmt, hcorr'⟩

/-- `skipToContent` starting at col=0 produces `SSLComments`. -/
theorem skipToContent_startOfLine_comments_prod
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : skipToContent sc = .ok s_result) :
    ∃ sp_mid sp_ws sp', SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' := by
  unfold skipToContent at hok
  exact skipToContentLoop_startOfLine_prod sc sp _ s_result hcorr hcol (by omega) hok

/-- `skipToContent` at any column → `SSLComments` (with col=0) OR flat whitespace. -/
theorem skipToContent_anyCol_prod
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : skipToContent sc = .ok s_result) :
    ∃ sp_mid sp_ws sp',
      (SSLComments sp sp_mid ∧ sp_mid.col = 0 ∨ sp_mid = sp) ∧
      GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
      ScannerSurfCorr s_result sp' := by
  unfold skipToContent at hok
  exact skipToContentLoop_anyCol_prod sc sp _ s_result hcorr (by omega) hok

/-! ## §5 scanNextToken_preprocess correspondence

    `scanNextToken_preprocess` calls `skipToContent`, then `unwindIndents`,
    then `saveSimpleKey`. All preserve correspondence. This extends the
    existing `ScanStrictCoupling` result with grammar output. -/

-- These are already in ScanStrictCoupling/StructureProduction:
-- - `skipToContent` (via `skipToContentLoop_ok_corr`)
-- - `unwindIndents` (via `unwindIndents_corr_exact`)
-- - `saveSimpleKey` (doesn't modify offset/col/input)
-- The grammar output is `SSLComments` or `SLDocumentPrefix` from §2–§4.

/-! ## §6 EOF-Complete SSLComments from skipToContent

    When `skipToContentLoop` at col=0 terminates because the scanner
    has no more input, the ENTIRE content (including the final iteration's
    whitespace and optional comment) forms `SSLComments`.

    Unlike `skipToContentLoop_col0_prod` (which leaves the final iteration
    as an uncovered gap between `sp_mid` and `sp'`), this theorem uses
    `SBComment.eof` to incorporate the terminal whitespace into an
    `SLComment`, yielding `SSLComments` with `sp_final.chars = []`. -/

/-- Convert `SSBComment` to `SLComment` when starting at column 0.
    `SSBComment.withSep` already has `SSeparateInLine`; `SSBComment.noSep`
    gets `SSeparateInLine.startOfLine` manufactured from the col=0 invariant. -/
theorem SSBComment_to_SLComment_col0 (sp sp' : SurfPos) (hcol : sp.col = 0)
    (h : SSBComment sp sp') : SLComment sp sp' := by
  cases h
  case withSep s₁ s₂ hsep hopt hbreak =>
    exact SLComment.mk sp s₁ s₂ sp' hsep hopt hbreak
  case noSep hbreak =>
    cases sp with | mk chars col =>
    dsimp only [] at hcol; subst hcol
    exact SLComment.mk ⟨chars, 0⟩ ⟨chars, 0⟩ ⟨chars, 0⟩ sp'
      (SSeparateInLine.startOfLine chars) (GOpt.none _) hbreak

/-- Extract `GStar SLComment` from `SSLComments` when starting at column 0.
    `SSLComments.startOfLine` already carries `GStar SLComment`;
    `SSLComments.withComment` has `SSBComment` + `GStar SLComment`,
    and the `SSBComment` converts to `SLComment` at col=0. -/
theorem SSLComments_to_GStar_col0 (sp sp' : SurfPos) (hcol : sp.col = 0)
    (h : SSLComments sp sp') : GStar SLComment sp sp' := by
  cases h
  case withComment s₁ hsbc hstar =>
    exact GStar.cons sp s₁ sp' (SSBComment_to_SLComment_col0 sp s₁ hcol hsbc) hstar
  case startOfLine chars hstar =>
    exact hstar

/-- `skipToContentLoop` at col=0, terminating at EOF, produces `SSLComments`
    covering all remaining characters (including the final iteration's
    whitespace) with `sp_final.chars = []`.

    Proof: induction on fuel, same structure as `skipToContentLoop_col0_prod`.
    - Break iteration: builds `SLComment`, recurses to get `SSLComments`,
      extracts `GStar SLComment`, prepends, re-wraps as `SSLComments.startOfLine`.
    - EOF iteration (peek? = none): builds single `SLComment` using
      `SBComment.eof`, wraps in `SSLComments.startOfLine`.
    - Non-break iteration (peek? = some, not break): contradicts `heof`
      since the content character implies `hasMore`. -/
theorem skipToContentLoop_eof_ssl_comments_col0
    (sc : ScannerState) (sp : SurfPos) (fuel : Nat) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result)
    (heof : ¬s_result.hasMore) :
    ∃ sp_final, SSLComments sp sp_final ∧ sp_final.chars = [] := by
  induction fuel generalizing sc sp s_result with
  | zero =>
    simp [skipToContentLoop] at hok; subst hok
    have heof' : ¬sc.offset < sc.inputEnd := by
      simp [ScannerState.hasMore] at heof; omega
    have hempty := eof_corr sc sp hcorr heof'
    cases sp with | mk chars col =>
    dsimp only [] at hcol hempty; subst hcol; subst hempty
    exact ⟨⟨[], 0⟩,
      SSLComments.withComment ⟨[], 0⟩ ⟨[], 0⟩ ⟨[], 0⟩
        (SSBComment.noSep _ _ (SBComment.eof _)) (GStar.nil _),
      rfl⟩
  | succ fuel' ih =>
    unfold skipToContentLoop at hok
    dsimp only [] at hok
    split at hok
    · -- skipToContentWs = .error
      simp at hok
    · -- skipToContentWs = .ok s1
      rename_i s1 hok_ws
      obtain ⟨sp_ws, hstar_ws, hcorr_ws⟩ := skipToContentWs_ok_corr sc sp s1 hcorr hok_ws
      obtain ⟨sp_cmt, hopt_cmt, hcorr_cmt⟩ := skipToContentComment_corr s1 sp_ws hcorr_ws
      split at hok
      · -- peek? = some c
        rename_i c hpeek
        split at hok
        · -- isLineBreakBool c = true → break → recurse
          rename_i hlb
          obtain ⟨sp_brk, h_break, hcol_brk, hcorr_brk⟩ :=
            consumeNewline_break_prod (skipToContentComment s1) sp_cmt c hcorr_cmt hpeek hlb
          -- Build SLComment from this iteration
          have h_sep : SSeparateInLine sp sp_ws :=
            GStar_SSWhite_to_SSeparateInLine_col0 sp sp_ws hstar_ws hcol
          have h_lcomment : SLComment sp sp_brk :=
            SLComment.mk sp sp_ws sp_cmt sp_brk h_sep hopt_cmt
              (SBComment.break _ _ h_break)
          -- Fuel budget for recursion (same as skipToContentLoop_col0_prod)
          have ⟨h_ws_off, h_ws_end⟩ := skipToContentWs_offset_mono sc s1 hok_ws
          have ⟨h_sc_off, h_sc_end⟩ := skipToContentComment_offset_mono s1
          have ⟨h_cn_off, h_cn_end⟩ :=
            consumeNewline_offset_advance (skipToContentComment s1) c hpeek hlb
          have h_scc_lt : (skipToContentComment s1).offset < (skipToContentComment s1).inputEnd :=
            peek_some_hasMore (skipToContentComment s1) c hpeek
          have h_cn_inputEnd : (consumeNewline (skipToContentComment s1)).inputEnd = sc.inputEnd := by
            rw [h_cn_end, h_sc_end, h_ws_end]
          have h_scc_end_eq : (skipToContentComment s1).inputEnd = sc.inputEnd := by
            rw [h_sc_end, h_ws_end]
          have h_sc_lt_inputEnd : sc.offset < sc.inputEnd := by omega
          have hfuel' : fuel' ≥ (consumeNewline (skipToContentComment s1)).inputEnd -
                                 (consumeNewline (skipToContentComment s1)).offset + 1 := by
            rw [h_cn_inputEnd]
            by_cases hle : (consumeNewline (skipToContentComment s1)).offset ≤ sc.inputEnd
            · omega
            · have hgt : (consumeNewline (skipToContentComment s1)).offset > sc.inputEnd := by
                omega
              have : sc.inputEnd - (consumeNewline (skipToContentComment s1)).offset = 0 := by omega
              rw [this]; omega
          -- Recurse — two sub-cases from the if
          split at hok
          · -- !isInFlowSequence: simpleKeyAllowed update
            have hcorr_next : ScannerSurfCorr
                { consumeNewline (skipToContentComment s1) with simpleKeyAllowed := true }
                ⟨sp_brk.chars, 0⟩ := by
              rw [← show sp_brk.col = 0 from hcol_brk]
              cases sp_brk; dsimp only [] at hcol_brk ⊢
              subst hcol_brk
              exact corr_of_simpleKeyAllowed_update true hcorr_brk
            obtain ⟨sp_final, h_ssl_rec, h_empty⟩ := ih _ ⟨sp_brk.chars, 0⟩ s_result
              hcorr_next rfl hfuel' hok heof
            -- Compose: SLComment sp sp_brk + SSLComments sp_brk sp_final → SSLComments sp sp_final
            have h_gstar_rec := SSLComments_to_GStar_col0 ⟨sp_brk.chars, 0⟩ sp_final rfl h_ssl_rec
            cases sp with | mk chars col =>
            dsimp only [] at hcol; subst hcol
            have h_lcomment' : SLComment ⟨chars, 0⟩ ⟨sp_brk.chars, 0⟩ := by
              cases sp_brk; dsimp only [] at hcol_brk ⊢; subst hcol_brk; exact h_lcomment
            exact ⟨sp_final,
              SSLComments.startOfLine chars sp_final
                (GStar.cons ⟨chars, 0⟩ ⟨sp_brk.chars, 0⟩ sp_final h_lcomment' h_gstar_rec),
              h_empty⟩
          · -- isInFlowSequence
            obtain ⟨sp_final, h_ssl_rec, h_empty⟩ := ih _ sp_brk s_result
              hcorr_brk hcol_brk hfuel' hok heof
            have h_gstar_rec := SSLComments_to_GStar_col0 sp_brk sp_final hcol_brk h_ssl_rec
            cases sp with | mk chars col =>
            dsimp only [] at hcol; subst hcol
            exact ⟨sp_final,
              SSLComments.startOfLine chars sp_final
                (GStar.cons ⟨chars, 0⟩ sp_brk sp_final h_lcomment h_gstar_rec),
              h_empty⟩
        · -- isLineBreakBool c = false → non-break stop
          -- peek? = some c means (skipToContentComment s1).hasMore
          -- So s_result = skipToContentComment s1 and s_result.hasMore = true
          -- This contradicts heof
          have hinj := Except.ok.inj hok; subst hinj
          have h_lt := peek_some_hasMore (skipToContentComment s1) c hpeek
          simp [ScannerState.hasMore] at heof
          exact absurd h_lt (by omega)
      · -- peek? = none → EOF in this iteration
        -- s_result = skipToContentComment s1, and sp_cmt.chars = []
        have hinj := Except.ok.inj hok; subst hinj
        have hpeek_none : (skipToContentComment s1).peek? = none := by assumption
        have heof_sc : ¬(skipToContentComment s1).offset < (skipToContentComment s1).inputEnd := by
          unfold ScannerState.peek? at hpeek_none
          split at hpeek_none
          · cases hpeek_none
          · assumption
        have hempty := eof_corr (skipToContentComment s1) sp_cmt hcorr_cmt heof_sc
        -- Build SLComment: SSeparateInLine + GOpt SCNbCommentText + SBComment.eof
        have h_sep : SSeparateInLine sp sp_ws :=
          GStar_SSWhite_to_SSeparateInLine_col0 sp sp_ws hstar_ws hcol
        -- sp_cmt.chars = [] so sp_cmt = ⟨[], sp_cmt.col⟩
        cases sp_cmt with | mk cmt_chars cmt_col =>
        dsimp only [] at hempty; subst hempty
        have h_eof_break : SBComment ⟨[], cmt_col⟩ ⟨[], cmt_col⟩ := SBComment.eof cmt_col
        have h_lcomment : SLComment sp ⟨[], cmt_col⟩ :=
          SLComment.mk sp sp_ws ⟨[], cmt_col⟩ ⟨[], cmt_col⟩ h_sep hopt_cmt h_eof_break
        cases sp with | mk chars col =>
        dsimp only [] at hcol; subst hcol
        exact ⟨⟨[], cmt_col⟩,
          SSLComments.startOfLine chars ⟨[], cmt_col⟩
            (GStar.cons ⟨chars, 0⟩ ⟨[], cmt_col⟩ ⟨[], cmt_col⟩ h_lcomment (GStar.nil _)),
          rfl⟩

/-- Top-level: `skipToContent` at col=0, reaching EOF, produces `SSLComments`. -/
theorem skipToContent_eof_ssl_comments_col0
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : skipToContent sc = .ok s_result)
    (heof : ¬s_result.hasMore) :
    ∃ sp_final, SSLComments sp sp_final ∧ sp_final.chars = [] := by
  unfold skipToContent at hok
  exact skipToContentLoop_eof_ssl_comments_col0 sc sp _ s_result hcorr hcol (by omega) hok heof

/-! ## §7 SSLComments extension

    Append one `SLComment` to an existing `SSLComments`, and a general
    EOF theorem for `skipToContent` at any starting column. -/

-- Append one SLComment to SSLComments.
theorem SSLComments_snoc {sp sp_mid sp' : SurfPos}
    (h_ssl : SSLComments sp sp_mid) (h_lc : SLComment sp_mid sp') :
    SSLComments sp sp' := by
  cases h_ssl
  · rename_i mid hsbc hgstar
    exact .withComment _ mid _ hsbc (GStar_trans hgstar (.cons _ _ _ h_lc (.nil _)))
  · rename_i chars hgstar
    exact .startOfLine chars _ (GStar_trans hgstar (.cons _ _ _ h_lc (.nil _)))

-- `skipToContent` reaching EOF produces `SSLComments` at any starting column.
theorem skipToContent_eof_ssl_comments
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : skipToContent sc = .ok s_result)
    (heof : ¬s_result.hasMore) :
    ∃ sp_final, SSLComments sp sp_final ∧ sp_final.chars = [] := by
  by_cases hcol : sp.col = 0
  · exact skipToContent_eof_ssl_comments_col0 sc sp s_result hcorr hcol hok heof
  · -- col≠0: use anyCol_prod + SBComment.eof
    obtain ⟨sp_mid, sp_ws, sp', hcase, hws, hcmt, hcorr'⟩ :=
      skipToContent_anyCol_prod sc sp s_result hcorr hok
    have h_not_lt : ¬s_result.offset < s_result.inputEnd := by
      simp [ScannerState.hasMore] at heof; omega
    have hchars : sp'.chars = [] := eof_corr s_result sp' hcorr' h_not_lt
    cases hcase with
    | inl h =>
      -- Break was consumed: SSLComments sp sp_mid at col=0, extend with eof SLComment
      obtain ⟨h_ssl, hcol_mid⟩ := h
      have h_sep := GStar_SSWhite_to_SSeparateInLine_col0 sp_mid sp_ws hws hcol_mid
      cases sp' with | mk chars' col' =>
      simp only [] at hchars; subst hchars
      exact ⟨⟨[], col'⟩,
        SSLComments_snoc h_ssl
          (SLComment.mk sp_mid sp_ws ⟨[], col'⟩ ⟨[], col'⟩ h_sep hcmt (SBComment.eof col')),
        rfl⟩
    | inr h =>
      -- No break: sp_mid = sp, build SSLComments from whitespace + eof
      rw [h] at hws
      -- hws : GStar SSWhite sp sp_ws, hcmt : GOpt SCNbCommentText sp_ws sp'
      cases sp' with | mk chars' col' =>
      simp only [] at hchars; subst hchars
      -- hcmt : GOpt SCNbCommentText sp_ws ⟨[], col'⟩
      by_cases h_ws_eq : sp = sp_ws
      · -- No whitespace consumed at col≠0
        rw [h_ws_eq]
        cases hcmt
        · -- GOpt.none: sp_ws = ⟨[], col'⟩
          exact ⟨⟨[], col'⟩,
            .withComment _ _ _ (.noSep _ _ (SBComment.eof col')) (.nil _),
            rfl⟩
        · -- GOpt.some: BOM edge case — use centralized sorry
          rename_i h_cmtv
          exact ⟨⟨[], col'⟩,
            .withComment _ _ _
              (bom_noWhitespace_ssbcomment sp_ws ⟨[], col'⟩ ⟨[], col'⟩
                h_cmtv (SBComment.eof col'))
              (.nil _),
            rfl⟩
      · -- Whitespace present: SSBComment.withSep + SBComment.eof
        exact ⟨⟨[], col'⟩,
          .withComment sp ⟨[], col'⟩ ⟨[], col'⟩
            (.withSep sp sp_ws ⟨[], col'⟩ ⟨[], col'⟩
              (SSeparateInLine.whites sp sp_ws (GStar_to_GPlus hws h_ws_eq))
              hcmt (SBComment.eof col'))
            (.nil _),
          rfl⟩

/-! ## §8 Document marker productions (status note)

    `scanDocumentStart_prod` and `scanDocumentEnd_prod` already exist in
    StructureProduction.lean (Layer 4a). `SLDocumentSuffix` composition
    already exists in DocumentProduction.lean (Layer 3). No new theorems
    needed here — this layer provides the preprocessing coupling that
    feeds into those existing results. -/

end Lean4Yaml.Proofs.PreprocessProduction
