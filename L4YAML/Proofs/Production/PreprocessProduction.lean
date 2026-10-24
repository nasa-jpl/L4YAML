/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Coupling.ScannerCoupling
public import L4YAML.Proofs.Production.NodeProduction
public import L4YAML.Proofs.Scanner.ScannerLinePreservation
public import L4YAML.Proofs.Scanner.PreprocessIndentStable
public import L4YAML.Proofs.Coupling.LandingTab
public import L4YAML.Proofs.Scanner.EntryBoundaryLayout

@[expose] public section Blanket

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

namespace L4YAML.Proofs.PreprocessProduction

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.NodeProduction
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.LandingTab
open L4YAML.Proofs.EntryBoundaryLayout

/-! ## §1 Helpers -/

/-- `GStar SSWhite` gives `SSeparateInLine`: a nonempty run is `whites`, and an
    empty run is `[66]`'s `startOfLine`, which the caller must place at column 0
    (`h0`). -/
lemma GStar_SSWhite_to_SSeparateInLine (sp sp' : SurfPos)
    (h_ws : GStar SSWhite sp sp') (h0 : sp = sp' → sp.col = 0) :
    SSeparateInLine sp sp' := by
  by_cases h : sp = sp'
  · subst h; exact .startOfLine_of_col0 (h0 rfl)
  · exact .whites sp sp' (GStar_to_GPlus h_ws h)

/-- A white run is an inline separation, or it is empty at a position off the
    line start — the one case `[66]` has no arm for, returned by name so the
    consumer can route it (an optional `s-separate?` slot, or a refutation). -/
lemma GStar_SSWhite_sep_or_eps {sp sp' : SurfPos} (h_ws : GStar SSWhite sp sp') :
    SSeparateInLine sp sp' ∨ (sp' = sp ∧ 0 < sp.col) := by
  by_cases hc : sp.col = 0
  · exact Or.inl (GStar_SSWhite_to_SSeparateInLine sp sp' h_ws (fun _ => hc))
  · cases h_ws with
    | nil _ => exact Or.inr ⟨rfl, Nat.pos_of_ne_zero hc⟩
    | cons _ s₂ _ hx hrest => exact Or.inl (.whites _ _ (GPlus.mk _ s₂ _ hx hrest))

/-- Strengthened `consumeNewline`: produces `SBBreak` and land at col=0. -/
lemma consumeNewline_break_prod (sc : ScannerState) (sp : SurfPos) (c : Char)
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
  simp [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
        Bool.or_eq_true, beq_iff_eq] at hlb
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

lemma sswhite_col_succ (sp sp' : SurfPos) (h : SSWhite sp sp') : sp'.col = sp.col + 1 := by
  cases h <;> rfl

lemma gstar_sswhite_col_ge (sp sp' : SurfPos) (h : GStar SSWhite sp sp') :
    sp'.col ≥ sp.col := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ s₁ _ hw _ ih =>
    have := sswhite_col_succ _ s₁ hw
    omega

/-- If GStar SSWhite starts and ends at the same column, it must be nil. -/
lemma gstar_sswhite_col_eq_nil (sp sp' : SurfPos)
    (hcol : sp.col = sp'.col) (h : GStar SSWhite sp sp') : sp' = sp := by
  cases h with
  | nil => rfl
  | cons _ s₁ _ hw hrest =>
    exfalso
    have h1 := sswhite_col_succ _ s₁ hw
    have h2 := gstar_sswhite_col_ge s₁ sp' hrest
    omega

lemma snbchar_col_succ (sp sp' : SurfPos) (h : SCommentChar sp sp') : sp'.col = sp.col + 1 := by
  cases h <;> rfl

lemma gstar_snbchar_col_ge (sp sp' : SurfPos) (h : GStar SCommentChar sp sp') :
    sp'.col ≥ sp.col := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ s₁ _ hc _ ih =>
    have := snbchar_col_succ _ s₁ hc
    omega

/-- SCNbCommentText strictly increments column (consumes '#' + body). -/
lemma scnb_comment_col_gt (sp sp' : SurfPos)
    (h : SCNbCommentText sp sp') : sp'.col > sp.col := by
  cases h
  rename_i rest col hstar
  have := gstar_snbchar_col_ge ⟨rest, col + 1⟩ sp' hstar
  dsimp only [] at this ⊢; omega

/-- GOpt SCNbCommentText at same column implies none. -/
lemma gopt_comment_col_eq_none (sp sp' : SurfPos)
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
lemma collectCommentTextLoop_stops_at_break_or_eof
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

/-! ## §1b skipToContentComment identity when peek is non-break

    When `skipToContentComment` is called and its output has a non-break
    `peek?`, the function was identity (no comment consumed). This follows
    from `collectCommentTextLoop_stops_at_break_or_eof`: if a comment HAD
    been consumed, the resulting peek would be break or EOF. -/

/-- `skipToContentComment sc = sc` when the output peek is non-break content. -/
lemma skipToContentComment_identity_of_content_peek
    (sc : ScannerState) (c : Char)
    (hpeek : (skipToContentComment sc).peek? = some c)
    (hnlb : ¬(isLineBreakBool c = true)) :
    skipToContentComment sc = sc := by
  unfold skipToContentComment at hpeek ⊢
  dsimp only [] at hpeek ⊢
  -- Synchronize splits: generalize the match discriminant so both hpeek and ⊢ share it
  generalize h_pk : sc.peek? = pk at hpeek ⊢
  cases pk with
  | none => rfl  -- _ => sc
  | some ch =>
    -- match (some ch) with | some '#' => ... | _ => sc
    -- Split goal, then align hpeek
    split
    · -- ch = '#' → comment branch in goal
      split at hpeek
      · -- ch = '#' in hpeek too → aligned
        -- Now split on peekBack?
        generalize h_pb : sc.peekBack? = pb at hpeek ⊢
        cases pb with
        | none =>
          dsimp only [] at hpeek ⊢
          -- commentOk = true (none case → true)
          -- comment consumed → contradiction
          exfalso
          have h_stop := collectCommentTextLoop_stops_at_break_or_eof
              sc.advance "" (sc.advance.inputEnd - sc.advance.offset) (Nat.le_refl _)
          simp only [ScannerState.peek?] at hpeek
          cases h_stop with
          | inl h_none =>
            simp only [ScannerState.peek?] at h_none
            simp [h_none] at hpeek
          | inr h_break =>
            obtain ⟨c', hpeek', hlb'⟩ := h_break
            simp only [ScannerState.peek?] at hpeek'
            simp [hpeek'] at hpeek
            subst hpeek; exact absurd hlb' hnlb
        | some cb =>
          dsimp only [] at hpeek ⊢
          -- Split on commentOk (the boolean condition)
          split
          · -- commentOk = true → comment consumed → contradiction
            split at hpeek
            · -- commentOk = true in hpeek too
              exfalso
              have h_stop := collectCommentTextLoop_stops_at_break_or_eof
                  sc.advance "" (sc.advance.inputEnd - sc.advance.offset) (Nat.le_refl _)
              simp only [ScannerState.peek?] at hpeek
              cases h_stop with
              | inl h_none =>
                simp only [ScannerState.peek?] at h_none
                simp [h_none] at hpeek
              | inr h_break =>
                obtain ⟨c', hpeek', hlb'⟩ := h_break
                simp only [ScannerState.peek?] at hpeek'
                simp [hpeek'] at hpeek
                subst hpeek; exact absurd hlb' hnlb
            · -- commentOk = false in hpeek but true in goal: contradiction
              rename_i h1 h2; exact absurd h1 h2
          · rfl  -- commentOk = false → identity
      · -- ch ≠ '#' in hpeek: contradiction with ch = '#' in goal
        contradiction
    · rfl  -- ch ≠ '#' → _ => sc

/-! ## §1a BOM Grammar Gap

    The YAML scanner allows `#` comments when `peekBack?` is the BOM character
    (U+FEFF), even without preceding whitespace. The grammar requires
    `SSeparateInLine` (s-white+ or start-of-line) before comment text,
    but after BOM at col=1, neither constructor applies. This is a genuine
    gap between the scanner and the formalized grammar. We capture it in
    a single sorry theorem used by multiple proofs. -/

-- A comment with no whitespace before it is `[76]`'s `withSep` only at column
-- 0, where the zero-width `[66]` applies; a `#` the scanner accepts at `col > 0`
-- without consumed whitespace sits after a white the previous token swallowed,
-- and that white is the separator the caller must exhibit.
lemma noWhitespace_ssbcomment_col0 (chars : List Char) (sp_cmt sp_end : SurfPos)
    (h_cmtv : SCNbCommentText ⟨chars, 0⟩ sp_cmt) (h_break : SBComment sp_cmt sp_end) :
    SSBComment ⟨chars, 0⟩ sp_end :=
  .withSep _ _ sp_cmt sp_end (.startOfLine chars) (.some _ sp_cmt h_cmtv) h_break

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
lemma skipToContentLoop_col0_prod
    (sc : ScannerState) (sp : SurfPos) (fuel : Nat) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result) :
    ∃ sp_mid sp_ws sp', GStar SLComment sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' ∧
                  (sp' = sp_ws ∨ s_result.peek? = none) ∧
                  LandingTabFacts sc.currentIndent sc.needIndentCheck
                    s_result.peek? sp sp_mid := by
  induction fuel generalizing sc sp s_result with
  | zero =>
    -- `hfuel` is `0 ≥ _ + 1`: the loop is never entered with no fuel at all.
    exact absurd hfuel (by omega)
  | succ fuel' ih =>
    unfold skipToContentLoop at hok
    dsimp only [] at hok
    split at hok
    · -- skipToContentWs = .error
      simp at hok
    · -- skipToContentWs = .ok s1
      rename_i s1 hok_ws
      obtain ⟨sp_ws, hstar_ws, hcorr_ws⟩ := skipToContentWs_ok_corr sc sp s1 hcorr hok_ws
      obtain ⟨sp_cmt, hopt_cmt, hcorr_cmt, h_cok⟩ := skipToContentComment_corr s1 sp_ws hcorr_ws
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
            GStar_SSWhite_to_SSeparateInLine sp sp_ws hstar_ws (fun _ => hcol)
          have h_lcomment : SLComment sp sp_brk :=
            SLComment.mk sp sp_ws sp_cmt sp_brk h_sep hopt_cmt
              (SBComment.break _ _ h_break)
          -- Item 64: the iteration transports §6.1's fact — nothing on the way
          -- writes the indent stack, and the break re-arms the check.
          have h_next_ind : (consumeNewline (skipToContentComment s1)).indents = sc.indents := by
            rw [consumeNewline_indents, skipToContentComment_preserves_indents,
              skipToContentWs_preserves_indents sc s1 hok_ws]
          have h_next_nic : (consumeNewline (skipToContentComment s1)).needIndentCheck = true :=
            consumeNewline_needIndentCheck_of_break _ c hpeek hlb
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
            obtain ⟨sp_mid, sp_ws_r, sp', hstar_lc, hcol_mid, hws_r, hcmt_r, hcorr', h_pk,
                h_ltsl⟩ :=
              ih _ ⟨sp_brk.chars, 0⟩ s_result hcorr_next rfl hfuel' hok
            exact ⟨sp_mid, sp_ws_r, sp', GStar.cons _ ⟨sp_brk.chars, 0⟩ _
              (by cases sp_brk; dsimp only [] at hcol_brk ⊢; subst hcol_brk; exact h_lcomment)
              hstar_lc, hcol_mid, hws_r, hcmt_r, hcorr', h_pk,
              h_ltsl.transport (currentIndent_of_indents_eq h_next_ind) h_next_nic⟩
          · -- isInFlowSequence
            obtain ⟨sp_mid, sp_ws_r, sp', hstar_lc, hcol_mid, hws_r, hcmt_r, hcorr', h_pk,
                h_ltsl⟩ :=
              ih _ sp_brk s_result hcorr_brk hcol_brk hfuel' hok
            exact ⟨sp_mid, sp_ws_r, sp', GStar.cons _ sp_brk _ h_lcomment hstar_lc,
                   hcol_mid, hws_r, hcmt_r, hcorr', h_pk,
                   h_ltsl.transport (currentIndent_of_indents_eq h_next_ind) h_next_nic⟩
        · -- not line break → stop (trailing ws from final iteration)
          rename_i hnlb
          have hinj := Except.ok.inj hok; subst hinj
          -- skipToContentComment was identity (non-break peek proves no comment consumed)
          have h_id := skipToContentComment_identity_of_content_peek s1 c hpeek hnlb
          rw [h_id]
          refine ⟨sp, sp_ws, sp_ws, GStar.nil _, hcol, hstar_ws, GOpt.none _, hcorr_ws,
                 Or.inl rfl, ?_⟩
          -- Item 64: this is the line preprocessing STOPS on, so §6.1's gate
          -- has already run on it — a tab at or left of the indent would have
          -- been `tabInIndentation` unless the line ended there.
          intro hprem hci j sx hind hj htab
          have hnic : sc.needIndentCheck = true := by
            rcases hprem with h | h
            · exact h
            · exact absurd rfl h
          obtain ⟨htab_pk, hcol_sp⟩ := skipSpaces_lands_at_tab hcorr hind htab
          have hle : ((skipSpaces sc).col : Int) ≤ sc.currentIndent := by
            rw [hcol_sp, ← SIndent_col' hind]; exact hj
          rcases skipToContentWs_tab_under_indent hok_ws hnic hci htab_pk hle with
            h_none | ⟨ch, hch, hclass⟩
          · exact Or.inl h_none
          · rcases hclass with rfl | hlb
            · exact Or.inr hch
            · exact absurd (by
                have : s1.peek? = some c := by rw [← h_id]; exact hpeek
                rw [hch] at this
                cases this; exact hlb) hnlb
      · -- peek? = none → stop (EOF, trailing ws/comment from final iteration)
        rename_i hpeek_none
        have hinj := Except.ok.inj hok; subst hinj
        exact ⟨sp, sp_ws, sp_cmt, GStar.nil _, hcol, hstar_ws, hopt_cmt, hcorr_cmt,
               Or.inr hpeek_none, fun _ _ _ _ _ _ _ => Or.inl hpeek_none⟩

/-- Top-level: `skipToContent` at col=0 produces `GStar SLComment` + correspondence. -/
lemma skipToContent_col0_prod
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : skipToContent sc = .ok s_result) :
    ∃ sp_mid sp_ws sp', GStar SLComment sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' ∧
                  (sp' = sp_ws ∨ s_result.peek? = none) := by
  unfold skipToContent at hok
  obtain ⟨sp_mid, sp_ws, sp', hstar, hcol_mid, hws, hcmt, hcorr', h_pk, _⟩ :=
    skipToContentLoop_col0_prod sc sp _ s_result hcorr hcol (by omega) hok
  exact ⟨sp_mid, sp_ws, sp', hstar, hcol_mid, hws, hcmt, hcorr', h_pk⟩

/-! ## §3 skipToContent at col=0 → SLDocumentPrefix -/

/-- `skipToContent` at col=0 produces `SLDocumentPrefix` + correspondence.
    The `sp_mid` is where the prefix ends (after comment lines);
    `sp'` is the scanner position (after trailing whitespace). -/
lemma skipToContent_documentPrefix_prod
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : skipToContent sc = .ok s_result) :
    ∃ sp_mid sp_ws sp', SLDocumentPrefix sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' ∧
                  (sp' = sp_ws ∨ s_result.peek? = none) := by
  obtain ⟨sp_mid, sp_ws, sp', hstar, hcol_mid, hws, hcmt, hcorr', h_pk⟩ :=
    skipToContent_col0_prod sc sp s_result hcorr hcol hok
  exact ⟨sp_mid, sp_ws, sp', SLDocumentPrefix.comments sp sp_mid hstar, hcol_mid, hws, hcmt, hcorr', h_pk⟩

/-! ## §4 skipToContentLoop after break → SSLComments

    When preceded by a break (SSBComment), the loop produces SSLComments:
    `SSBComment sp sp_after_break → skipToContentLoop → SSLComments sp sp'`. -/

/-- `[79] s-l-comments` read from the scanner cursor `sp`, or — at a cursor off
    the line start — a comment whose `[66]` separator is the white the previous
    token swallowed (`a #b`: `collectPlainScalarLoop` stops after the space):
    `c-nb-comment-text` at `sp`, its break, then `l-comment` lines.  The consumer
    that holds that white (`GStar SSWhite a sp`) turns the second shape back
    into `SSLComments a _` with `SSLCommentsFrom_prepend_white`; at column 0 the
    second shape is empty (`SSLCommentsFrom.toSSL`). -/
def SSLCommentsFrom (sp sp_mid : SurfPos) : Prop :=
  SSLComments sp sp_mid ∨
    (0 < sp.col ∧ ∃ sp_cmt sp_brk, SCNbCommentText sp sp_cmt ∧ SBComment sp_cmt sp_brk ∧
      GStar SLComment sp_brk sp_mid)

/-- The first break of a comment walk, with or without a separator before its
    comment, followed by the comment lines. -/
lemma SSLCommentsFrom.ofBreak {sp sp_brk sp_mid : SurfPos}
    (h : SSBComment sp sp_brk ∨
      (0 < sp.col ∧ ∃ sp_cmt, SCNbCommentText sp sp_cmt ∧ SBComment sp_cmt sp_brk))
    (hstar : GStar SLComment sp_brk sp_mid) : SSLCommentsFrom sp sp_mid := by
  rcases h with h | ⟨hc, sp_cmt, h_cmt, h_bc⟩
  · exact Or.inl (.withComment _ _ _ h hstar)
  · exact Or.inr ⟨hc, sp_cmt, sp_brk, h_cmt, h_bc, hstar⟩

/-- At column 0 the separator-less shape cannot occur. -/
lemma SSLCommentsFrom.toSSL {sp sp_mid : SurfPos} (h : SSLCommentsFrom sp sp_mid)
    (hcol : sp.col = 0) : SSLComments sp sp_mid := by
  rcases h with h | ⟨hc, _⟩
  · exact h
  · omega

/-- A comment text consumes its `#`, so it never ends where it started. -/
lemma SCNbCommentText_ne {sp sp' : SurfPos} (h : SCNbCommentText sp sp') : sp' ≠ sp := by
  cases h with
  | mk rest col s' hstar =>
    intro heq
    have := gstar_gchar_col_le hstar
    rw [heq] at this
    dsimp only at this
    omega

/-- With no whites consumed, `skipToContentWs` leaves input, offset and column
    alone — so the comment gate it then passes is a fact about the ENTRY state,
    i.e. about the token that parked there. -/
lemma CommentOk_of_skipToContentWs_zero {sc s1 : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hcorr1 : ScannerSurfCorr s1 sp)
    (hok : skipToContentWs sc = .ok s1) (h : CommentOk s1) : CommentOk sc := by
  have hin := skipToContentWs_input sc s1 hok
  have hoff := ScannerSurfCorr_same_offset hcorr1 hcorr hin
  have hcol : s1.col = sc.col := hcorr1.col_eq.symm.trans hcorr.col_eq
  have hpb : s1.peekBack? = sc.peekBack? := by
    simp only [ScannerState.peekBack?, hin, hoff]
  unfold CommentOk at h ⊢
  rw [hcol, hpb] at h
  exact h

/-- `skipToContentLoop` after a break produces `[79]` from the cursor the
    break's comment started at (`SSLCommentsFrom`). -/
lemma skipToContentLoop_after_break_prod
    (sp : SurfPos) (sp_after_break : SurfPos)
    (sc : ScannerState) (fuel : Nat) (s_result : ScannerState)
    (h_sbcomment : SSBComment sp sp_after_break ∨
      (0 < sp.col ∧ ∃ sp_cmt, SCNbCommentText sp sp_cmt ∧ SBComment sp_cmt sp_after_break))
    (hcorr : ScannerSurfCorr sc sp_after_break)
    (hcol : sp_after_break.col = 0)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result) :
    ∃ sp_mid sp_ws sp', SSLCommentsFrom sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SLComment sp_after_break sp_mid ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' ∧
                  (sp' = sp_ws ∨ s_result.peek? = none) ∧
                  LandingTabFacts sc.currentIndent sc.needIndentCheck
                    s_result.peek? sp_after_break sp_mid := by
  obtain ⟨sp_mid, sp_ws, sp', hstar_lc, hcol_mid, hws, hcmt, hcorr', h_pk, h_ltsl⟩ :=
    skipToContentLoop_col0_prod sc sp_after_break fuel s_result hcorr hcol hfuel hok
  exact ⟨sp_mid, sp_ws, sp', SSLCommentsFrom.ofBreak h_sbcomment hstar_lc,
         hcol_mid, hstar_lc, hws, hcmt, hcorr', h_pk, h_ltsl⟩

/-- `skipToContentLoop` at any column → `SSLComments` OR flat whitespace.
    Returns a disjunction: if a break was consumed, produces full `SSLComments`
    with `sp_mid.col = 0`; if not, `sp_mid = sp` (loop stopped on first
    iteration) — and then `needIndentCheck` is untouched, because the no-break
    stop paths run only the line-transparent whitespace/comment helpers (the
    witness DOCS item 12's depth-0 props coupling reads). -/
lemma skipToContentLoop_anyCol_prod
    (sc : ScannerState) (sp : SurfPos) (fuel : Nat) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result) :
    ∃ sp_mid sp_ws sp',
      (SSLCommentsFrom sp sp_mid ∧ sp_mid.col = 0 ∧
          -- N3: the separator-less shape is only produced when the scanner's
          -- comment gate passed at the park — a fact about the parking token.
          (SSLComments sp sp_mid ∨ CommentOk sc) ∧
          -- **Item 76: the landing's own re-arm.**  A park that is NOT at a
          -- line start reaches a column-0 landing only across a BREAK, and
          -- `skipToContentLoop` re-arms the simple key on every break outside a
          -- flow — so the walk itself says the next `saveSimpleKey` will be a
          -- FRESH one.  Guarded by the park's column because the col-0 entry
          -- lands without crossing anything, and by the flow level because
          -- §7.4.2's gate is what suppresses the re-arm inside a collection.
          (sp.col ≠ 0 → sc.inFlow = false → s_result.simpleKeyAllowed = true) ∧
          -- **Item 147: the walk's own FLAG, beside the re-arm.**  The break
          -- that carries a park off a line start down to column 0 is the same
          -- break `consumeNewline` raises `needIndentCheck` on, and the flag
          -- only ever goes up for the rest of the loop
          -- (`skipToContentLoop_needIndentCheck_mono`).  So a landing from a
          -- park that is NOT at a line start hands preprocessing a state whose
          -- unwind is ARMED — which is what makes the landing's own floor a
          -- fact rather than a disjunct.  Ungated by the flow level: a break
          -- raises the check inside a collection too; only the key's re-arm
          -- above is §7.4.2's to suppress.
          (sp.col ≠ 0 → s_result.needIndentCheck = true) ∨
        sp_mid = sp ∧ s_result.needIndentCheck = sc.needIndentCheck ∧
          -- N3: a comment with no whites before it passed the scanner's gate.
          (sp_ws = sp → sp' ≠ sp_ws → CommentOk sc)) ∧
      GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
      ScannerSurfCorr s_result sp' ∧
      (sp' = sp_ws ∨ s_result.peek? = none) ∧
      LandingTabFacts sc.currentIndent sc.needIndentCheck s_result.peek? sp sp_mid := by
  by_cases hcol : sp.col = 0
  · -- col=0: use existing theorem, wrap as SSLComments.startOfLine
    obtain ⟨sp_mid, sp_ws, sp', hstar, hcol_mid, hws, hcmt, hcorr', h_pk, h_ltsl⟩ :=
      skipToContentLoop_col0_prod sc sp fuel s_result hcorr hcol hfuel hok
    cases sp with | mk chars col =>
    dsimp only [] at hcol; subst hcol
    exact ⟨sp_mid, sp_ws, sp',
      Or.inl ⟨Or.inl (SSLComments.startOfLine chars sp_mid hstar), hcol_mid,
        Or.inl (SSLComments.startOfLine chars sp_mid hstar),
        fun h _ => absurd rfl h, fun h => absurd rfl h⟩,
      hws, hcmt, hcorr', h_pk, h_ltsl⟩
  · -- col≠0: induction on fuel; first break builds SSBComment
    induction fuel generalizing sc sp s_result with
    | zero =>
      exact absurd hfuel (by omega)
    | succ fuel' ih =>
      unfold skipToContentLoop at hok
      dsimp only [] at hok
      split at hok
      · simp at hok
      · rename_i s1 hok_ws
        obtain ⟨sp_ws, hstar_ws, hcorr_ws⟩ := skipToContentWs_ok_corr sc sp s1 hcorr hok_ws
        obtain ⟨sp_cmt, hopt_cmt, hcorr_cmt, h_cok⟩ := skipToContentComment_corr s1 sp_ws hcorr_ws
        split at hok
        · rename_i c hpeek
          split at hok
          · -- Break found: build SSBComment, delegate rest to col0
            rename_i hlb
            obtain ⟨sp_brk, h_break, hcol_brk, hcorr_brk⟩ :=
              consumeNewline_break_prod (skipToContentComment s1) sp_cmt c hcorr_cmt hpeek hlb
            -- Build SSBComment for this iteration
            have h_sbc : SSBComment sp sp_brk ∨
                (0 < sp.col ∧ ∃ sp_cmt, SCNbCommentText sp sp_cmt ∧ SBComment sp_cmt sp_brk) := by
              by_cases h_eq : sp = sp_ws
              · -- No whitespace: a bare break is `noSep`; a comment with no
                -- separator at `col > 0` is the shape whose white the previous
                -- token swallowed.
                subst h_eq
                cases hopt_cmt
                · exact Or.inl (SSBComment.noSep sp sp_brk (SBComment.break _ _ h_break))
                · rename_i h_cmtv
                  exact Or.inr ⟨Nat.pos_of_ne_zero hcol, sp_cmt, h_cmtv,
                    SBComment.break _ _ h_break⟩
              · -- Whitespace present: use withSep
                exact Or.inl (SSBComment.withSep sp sp_ws sp_cmt sp_brk
                  (SSeparateInLine.whites sp sp_ws (GStar_to_GPlus hstar_ws h_eq))
                  hopt_cmt (SBComment.break _ _ h_break))
            -- N3: the same split read scanner-side — the separator-less
            -- shape passed `commentOk` at the park.
            have h_sbc_ok : SSBComment sp sp_brk ∨ CommentOk sc := by
              by_cases h_eq : sp = sp_ws
              · subst h_eq
                cases hopt_cmt
                · exact Or.inl (SSBComment.noSep sp sp_brk (SBComment.break _ _ h_break))
                · rename_i h_cmtv
                  exact Or.inr (CommentOk_of_skipToContentWs_zero hcorr hcorr_ws hok_ws
                    (h_cok.resolve_left (SCNbCommentText_ne h_cmtv)))
              · exact Or.inl (SSBComment.withSep sp sp_ws sp_cmt sp_brk
                  (SSeparateInLine.whites sp sp_ws (GStar_to_GPlus hstar_ws h_eq))
                  hopt_cmt (SBComment.break _ _ h_break))
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
            -- Item 64: §6.1's fact rides the iteration — the stack is
            -- untouched and the break re-arms the check.
            have h_next_ind : (consumeNewline (skipToContentComment s1)).indents = sc.indents := by
              rw [consumeNewline_indents, skipToContentComment_preserves_indents,
                skipToContentWs_preserves_indents sc s1 hok_ws]
            have h_next_nic : (consumeNewline (skipToContentComment s1)).needIndentCheck = true :=
              consumeNewline_needIndentCheck_of_break _ c hpeek hlb
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
              obtain ⟨sp_mid, sp_ws_r, sp', hssl, hcol_mid, h_lc, hws_r, hcmt_r, hcorr', h_pk,
                  h_ltsl⟩ :=
                skipToContentLoop_after_break_prod sp ⟨sp_brk.chars, 0⟩
                  { consumeNewline (skipToContentComment s1) with simpleKeyAllowed := true }
                  fuel' s_result
                  (by cases sp_brk; dsimp only [] at hcol_brk ⊢; subst hcol_brk; exact h_sbc)
                  hcorr_next rfl hfuel' hok
              exact ⟨sp_mid, sp_ws_r, sp',
                Or.inl ⟨hssl, hcol_mid,
                  h_sbc_ok.imp_left (fun h => SSLComments.withComment _ _ _ h
                    (by cases sp_brk; dsimp only [] at hcol_brk h_lc; subst hcol_brk; exact h_lc)),
                  fun _ _ =>
                  skipToContentLoop_simpleKeyAllowed_mono _ s_result fuel' rfl hok,
                  -- Item 147: the break armed the check and the loop keeps it up.
                  fun _ => skipToContentLoop_needIndentCheck_mono _ s_result fuel' hok
                    (by simpa using h_next_nic)⟩,
                hws_r, hcmt_r, hcorr', h_pk,
                h_ltsl.transport (currentIndent_of_indents_eq h_next_ind) h_next_nic⟩
            · -- isInFlowSequence: §7.4.2 suppresses the re-arm, and the walk
              -- carries no flow level of its own — so the payload's premise is
              -- refuted from the entry state's.
              rename_i h_inflow
              obtain ⟨sp_mid, sp_ws_r, sp', hssl, hcol_mid, h_lc, hws_r, hcmt_r, hcorr', h_pk,
                  h_ltsl⟩ :=
                skipToContentLoop_after_break_prod sp sp_brk
                  (consumeNewline (skipToContentComment s1)) fuel' s_result
                  h_sbc hcorr_brk hcol_brk hfuel' hok
              refine ⟨sp_mid, sp_ws_r, sp',
                Or.inl ⟨hssl, hcol_mid,
                  h_sbc_ok.imp_left (fun h => SSLComments.withComment _ _ _ h h_lc),
                  fun _ h_nf => absurd ?_ h_inflow,
                  -- Item 147: §7.4.2 suppresses the KEY's re-arm inside a
                  -- collection, never the indent check — the break raises it
                  -- here exactly as it does outside one.
                  fun _ => skipToContentLoop_needIndentCheck_mono _ s_result fuel' hok
                    h_next_nic⟩,
                hws_r, hcmt_r, hcorr', h_pk,
                h_ltsl.transport (currentIndent_of_indents_eq h_next_ind) h_next_nic⟩
              show (!(consumeNewline (skipToContentComment s1)).inFlow) = true
              unfold ScannerState.inFlow at h_nf ⊢
              rw [ScannerCorrectness.consumeNewline_preserves_flowLevel,
                  ScannerCorrectness.skipToContentComment_preserves_flowLevel,
                  ScannerCorrectness.skipToContentWs_preserves_flowLevel sc s1 hok_ws]
              simpa using h_nf
          · -- Not break: stop
            rename_i hnlb
            have hinj := Except.ok.inj hok; subst hinj
            have h_id := skipToContentComment_identity_of_content_peek s1 c hpeek hnlb
            rw [h_id]
            refine ⟨sp, sp_ws, sp_ws,
                   Or.inr ⟨rfl, skipToContentWs_preserves_needIndentCheck sc s1 hok_ws,
                     fun _ h => absurd rfl h⟩,
                   hstar_ws, GOpt.none _, hcorr_ws, Or.inl rfl, ?_⟩
            intro hprem hci j sx hind hj htab
            have hnic : sc.needIndentCheck = true := by
              rcases hprem with h | h
              · exact h
              · exact absurd rfl h
            obtain ⟨htab_pk, hcol_sp⟩ := skipSpaces_lands_at_tab hcorr hind htab
            have hle : ((skipSpaces sc).col : Int) ≤ sc.currentIndent := by
              rw [hcol_sp, ← SIndent_col' hind]; exact hj
            rcases skipToContentWs_tab_under_indent hok_ws hnic hci htab_pk hle with
              h_none | ⟨ch, hch, hclass⟩
            · exact Or.inl h_none
            · rcases hclass with rfl | hlb
              · exact Or.inr hch
              · exact absurd (by
                  have : s1.peek? = some c := by rw [← h_id]; exact hpeek
                  rw [hch] at this
                  cases this; exact hlb) hnlb
        · -- peek? = none: stop
          rename_i hpeek_none
          have hinj := Except.ok.inj hok; subst hinj
          exact ⟨sp, sp_ws, sp_cmt,
                 Or.inr ⟨rfl, (skipToContentComment_preserves_needIndentCheck s1).trans
                   (skipToContentWs_preserves_needIndentCheck sc s1 hok_ws),
                   fun h_eq h_ne => by
                     subst h_eq
                     exact CommentOk_of_skipToContentWs_zero hcorr hcorr_ws hok_ws
                       (h_cok.resolve_left h_ne)⟩,
                 hstar_ws, hopt_cmt, hcorr_cmt, Or.inr hpeek_none,
                 fun _ _ _ _ _ _ _ => Or.inl hpeek_none⟩

/-- `skipToContentLoop` starting at col=0 produces `SSLComments`. -/
lemma skipToContentLoop_startOfLine_prod
    (sc : ScannerState) (sp : SurfPos) (fuel : Nat) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result) :
    ∃ sp_mid sp_ws sp', SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' ∧
                  (sp' = sp_ws ∨ s_result.peek? = none) := by
  obtain ⟨sp_mid, sp_ws, sp', hstar_lc, hcol_mid, hws, hcmt, hcorr', h_pk, _⟩ :=
    skipToContentLoop_col0_prod sc sp fuel s_result hcorr hcol hfuel hok
  cases sp with | mk chars col =>
  dsimp only [] at hcol; subst hcol
  exact ⟨sp_mid, sp_ws, sp', SSLComments.startOfLine chars sp_mid hstar_lc, hcol_mid, hws, hcmt, hcorr', h_pk⟩

/-- `skipToContent` starting at col=0 produces `SSLComments`. -/
lemma skipToContent_startOfLine_comments_prod
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col = 0)
    (hok : skipToContent sc = .ok s_result) :
    ∃ sp_mid sp_ws sp', SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧
                  GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
                  ScannerSurfCorr s_result sp' ∧
                  (sp' = sp_ws ∨ s_result.peek? = none) := by
  unfold skipToContent at hok
  exact skipToContentLoop_startOfLine_prod sc sp _ s_result hcorr hcol (by omega) hok

/-- `skipToContent` at any column → `SSLComments` (with col=0) OR flat whitespace
    (and then the loop crossed no break, so `needIndentCheck` is untouched). -/
lemma skipToContent_anyCol_prod
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : skipToContent sc = .ok s_result) :
    ∃ sp_mid sp_ws sp',
      (SSLCommentsFrom sp sp_mid ∧ sp_mid.col = 0 ∧
          -- N3: the separator-less shape is only produced when the scanner's
          -- comment gate passed at the park — a fact about the parking token.
          (SSLComments sp sp_mid ∨ CommentOk sc) ∧
          -- **Item 76: the landing's own re-arm.**  A park that is NOT at a
          -- line start reaches a column-0 landing only across a BREAK, and
          -- `skipToContentLoop` re-arms the simple key on every break outside a
          -- flow — so the walk itself says the next `saveSimpleKey` will be a
          -- FRESH one.  Guarded by the park's column because the col-0 entry
          -- lands without crossing anything, and by the flow level because
          -- §7.4.2's gate is what suppresses the re-arm inside a collection.
          (sp.col ≠ 0 → sc.inFlow = false → s_result.simpleKeyAllowed = true) ∧
          -- **Item 147: the walk's own FLAG, beside the re-arm.**  The break
          -- that carries a park off a line start down to column 0 is the same
          -- break `consumeNewline` raises `needIndentCheck` on, and the flag
          -- only ever goes up for the rest of the loop
          -- (`skipToContentLoop_needIndentCheck_mono`).  So a landing from a
          -- park that is NOT at a line start hands preprocessing a state whose
          -- unwind is ARMED — which is what makes the landing's own floor a
          -- fact rather than a disjunct.  Ungated by the flow level: a break
          -- raises the check inside a collection too; only the key's re-arm
          -- above is §7.4.2's to suppress.
          (sp.col ≠ 0 → s_result.needIndentCheck = true) ∨
        sp_mid = sp ∧ s_result.needIndentCheck = sc.needIndentCheck ∧
          -- N3: a comment with no whites before it passed the scanner's gate.
          (sp_ws = sp → sp' ≠ sp_ws → CommentOk sc)) ∧
      GStar SSWhite sp_mid sp_ws ∧ GOpt SCNbCommentText sp_ws sp' ∧
      ScannerSurfCorr s_result sp' ∧
      (sp' = sp_ws ∨ s_result.peek? = none) ∧
      LandingTabFacts sc.currentIndent sc.needIndentCheck s_result.peek? sp sp_mid := by
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

/-- Convert `SSBComment` to `SLComment` at column 0.
    `SSBComment.withSep` already has `SSeparateInLine`; `SSBComment.noSep`
    gets `SSeparateInLine.startOfLine`, which is why the line must start at
    column 0: a bare break after content (`a:⏎`) is an `s-b-comment` but not
    an `l-comment` line. -/
lemma SSBComment_to_SLComment (sp sp' : SurfPos)
    (h : SSBComment sp sp') (hcol : sp.col = 0) : SLComment sp sp' := by
  cases h
  case withSep s₁ s₂ hsep hopt hbreak =>
    exact SLComment.mk sp s₁ s₂ sp' hsep hopt hbreak
  case noSep hbreak =>
    exact SLComment.mk sp sp sp sp' (.startOfLine_of_col0 hcol) (GOpt.none _) hbreak

/-- Where `[76] s-b-comment` ends: at column 0 (after its break) or at the end
    of the input. -/
lemma SBComment_end_col0_or_eof {a b : SurfPos} (h : SBComment a b) :
    b.col = 0 ∨ b.chars = [] := by
  cases h
  · rename_i hb
    left; cases hb <;> rfl
  · right; rfl

lemma SSBComment_end_col0_or_eof {a b : SurfPos} (h : SSBComment a b) :
    b.col = 0 ∨ b.chars = [] := by
  cases h
  · rename_i hbc; exact SBComment_end_col0_or_eof hbc
  · rename_i hbc; exact SBComment_end_col0_or_eof hbc

lemma SLComment_end_col0_or_eof {a b : SurfPos} (h : SLComment a b) :
    b.col = 0 ∨ b.chars = [] := by
  cases h
  rename_i hbc
  exact SBComment_end_col0_or_eof hbc

lemma GStar_SLComment_end_col0_or_eof {a b : SurfPos} (h : GStar SLComment a b)
    (ha : a.col = 0 ∨ a.chars = []) : b.col = 0 ∨ b.chars = [] := by
  induction h with
  | nil _ => exact ha
  | cons _ _ _ hx _ ih => exact ih (SLComment_end_col0_or_eof hx)

/-- Where `[79] s-l-comments` ends: at column 0 or at the end of the input. -/
lemma SSLComments_end_col0_or_eof {a b : SurfPos} (h : SSLComments a b) :
    b.col = 0 ∨ b.chars = [] := by
  cases h with
  | withComment _ _ _ hsbc hstar =>
    exact GStar_SLComment_end_col0_or_eof hstar (SSBComment_end_col0_or_eof hsbc)
  | startOfLine _ _ hstar => exact GStar_SLComment_end_col0_or_eof hstar (Or.inl rfl)

/-- Extract `GStar SLComment` from `SSLComments` at any column.
    `SSLComments.startOfLine` already carries `GStar SLComment`;
    `SSLComments.withComment` has `SSBComment` + `GStar SLComment`,
    and the `SSBComment` converts to `SLComment`. -/
lemma SSLComments_to_GStar (sp sp' : SurfPos)
    (h : SSLComments sp sp') (hcol : sp.col = 0) : GStar SLComment sp sp' := by
  cases h
  case withComment s₁ hsbc hstar =>
    exact GStar.cons sp s₁ sp' (SSBComment_to_SLComment sp s₁ hsbc hcol) hstar
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
lemma skipToContentLoop_eof_ssl_comments_col0
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
      obtain ⟨sp_cmt, hopt_cmt, hcorr_cmt, h_cok⟩ := skipToContentComment_corr s1 sp_ws hcorr_ws
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
            GStar_SSWhite_to_SSeparateInLine sp sp_ws hstar_ws (fun _ => hcol)
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
            have h_gstar_rec := SSLComments_to_GStar ⟨sp_brk.chars, 0⟩ sp_final h_ssl_rec rfl
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
            have h_gstar_rec := SSLComments_to_GStar sp_brk sp_final h_ssl_rec hcol_brk
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
          GStar_SSWhite_to_SSeparateInLine sp sp_ws hstar_ws (fun _ => hcol)
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
lemma skipToContent_eof_ssl_comments_col0
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
lemma SSLComments_snoc {sp sp_mid sp' : SurfPos}
    (h_ssl : SSLComments sp sp_mid) (h_lc : SLComment sp_mid sp') :
    SSLComments sp sp' := by
  cases h_ssl
  · rename_i mid hsbc hgstar
    exact .withComment _ mid _ hsbc (GStar_trans hgstar (.cons _ _ _ h_lc (.nil _)))
  · rename_i chars hgstar
    exact .startOfLine chars _ (GStar_trans hgstar (.cons _ _ _ h_lc (.nil _)))

/-- Appending an `l-comment` line keeps either shape of `SSLCommentsFrom`. -/
lemma SSLCommentsFrom.snoc {sp sp_mid sp' : SurfPos} (h : SSLCommentsFrom sp sp_mid)
    (hl : SLComment sp_mid sp') : SSLCommentsFrom sp sp' := by
  rcases h with h | ⟨hc, sp_cmt, sp_brk, h_cmt, h_bc, h_rest⟩
  · exact Or.inl (SSLComments_snoc h hl)
  · exact Or.inr ⟨hc, sp_cmt, sp_brk, h_cmt, h_bc,
      GStar_trans h_rest (GStar.cons _ _ _ hl (GStar.nil _))⟩

-- `skipToContent` reaching EOF produces `SSLComments` at any starting column.
lemma skipToContent_eof_ssl_comments
    (sc : ScannerState) (sp : SurfPos) (s_result : ScannerState)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : skipToContent sc = .ok s_result)
    (heof : ¬s_result.hasMore) :
    ∃ sp_final, SSLCommentsFrom sp sp_final ∧ sp_final.chars = [] ∧
      -- N3: the separator-less shape passed the scanner's comment gate at `sp`.
      (SSLComments sp sp_final ∨ CommentOk sc) := by
  by_cases hcol : sp.col = 0
  · obtain ⟨sp_final, h1, h2⟩ :=
      skipToContent_eof_ssl_comments_col0 sc sp s_result hcorr hcol hok heof
    exact ⟨sp_final, Or.inl h1, h2, Or.inl h1⟩
  · -- col≠0: use anyCol_prod + SBComment.eof
    obtain ⟨sp_mid, sp_ws, sp', hcase, hws, hcmt, hcorr', _⟩ :=
      skipToContent_anyCol_prod sc sp s_result hcorr hok
    have h_not_lt : ¬s_result.offset < s_result.inputEnd := by
      simp [ScannerState.hasMore] at heof; omega
    have hchars : sp'.chars = [] := eof_corr s_result sp' hcorr' h_not_lt
    cases hcase with
    | inl h =>
      -- Break was consumed: SSLComments sp sp_mid at col=0, extend with eof SLComment
      obtain ⟨h_ssl, hcol_mid, h_ok, -⟩ := h
      have h_sep := GStar_SSWhite_to_SSeparateInLine sp_mid sp_ws hws (fun _ => hcol_mid)
      cases sp' with | mk chars' col' =>
      simp only [] at hchars; subst hchars
      exact ⟨⟨[], col'⟩,
        SSLCommentsFrom.snoc h_ssl
          (SLComment.mk sp_mid sp_ws ⟨[], col'⟩ ⟨[], col'⟩ h_sep hcmt (SBComment.eof col')),
        rfl,
        h_ok.imp_left (fun h => SSLComments_snoc h
          (SLComment.mk sp_mid sp_ws ⟨[], col'⟩ ⟨[], col'⟩ h_sep hcmt (SBComment.eof col')))⟩
    | inr h =>
      -- No break: sp_mid = sp, build SSLComments from whitespace + eof
      rw [h.1] at hws
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
            Or.inl (SSLComments.withComment _ _ _ (.noSep _ _ (SBComment.eof col')) (.nil _)),
            rfl,
            Or.inl (SSLComments.withComment _ _ _ (.noSep _ _ (SBComment.eof col')) (.nil _))⟩
        · -- GOpt.some: a comment at the cursor with no separator — the white
          -- before it belongs to the previous token (`SSLCommentsFrom`).
          rename_i h_cmtv
          exact ⟨⟨[], col'⟩,
            Or.inr ⟨by rw [← h_ws_eq]; exact Nat.pos_of_ne_zero hcol, ⟨[], col'⟩, ⟨[], col'⟩,
              h_cmtv, SBComment.eof col', .nil _⟩,
            rfl,
            Or.inr (h.2.2 h_ws_eq.symm (SCNbCommentText_ne h_cmtv))⟩
      · -- Whitespace present: SSBComment.withSep + SBComment.eof
        have h_ssl : SSLComments sp ⟨[], col'⟩ :=
          SSLComments.withComment sp ⟨[], col'⟩ ⟨[], col'⟩
            (.withSep sp sp_ws ⟨[], col'⟩ ⟨[], col'⟩
              (SSeparateInLine.whites sp sp_ws (GStar_to_GPlus hws h_ws_eq))
              hcmt (SBComment.eof col'))
            (.nil _)
        exact ⟨⟨[], col'⟩, Or.inl h_ssl, rfl, Or.inl h_ssl⟩

/-! ## §7 skipToContent non-break guarantee

    `skipToContentLoop` only stops at non-break characters or EOF.
    When it returns with `peek? = some c`, `c` is NOT a line break. -/

-- skipToContentLoop returns at non-break chars (given sufficient fuel).
lemma skipToContentLoop_peek_not_break
    (sc : ScannerState) (fuel : Nat) (s_result : ScannerState) (c : Char)
    (hfuel : fuel ≥ sc.inputEnd - sc.offset + 1)
    (hok : skipToContentLoop sc fuel = .ok s_result)
    (hpeek : s_result.peek? = some c) :
    isLineBreakBool c = false := by
  induction fuel generalizing sc s_result with
  | zero =>
    -- fuel ≥ inputEnd - offset + 1 ≥ 1, contradicting fuel = 0
    simp [skipToContentLoop] at hok; subst hok
    have : sc.inputEnd - sc.offset + 1 ≤ 0 := hfuel
    omega
  | succ fuel' ih =>
    unfold skipToContentLoop at hok
    dsimp only [] at hok
    split at hok
    · simp at hok
    · rename_i s1 hok_ws
      split at hok
      · rename_i c' hpeek_c'
        split at hok
        · -- Break: consume newline and recurse
          rename_i hlb
          have ⟨h_ws_off, h_ws_end⟩ := skipToContentWs_offset_mono sc s1 hok_ws
          have ⟨h_sc_off, h_sc_end⟩ := skipToContentComment_offset_mono s1
          have ⟨h_cn_off, h_cn_end⟩ :=
            consumeNewline_offset_advance (skipToContentComment s1) c' hpeek_c' hlb
          have h_cn_inputEnd :
              (consumeNewline (skipToContentComment s1)).inputEnd = sc.inputEnd := by
            rw [h_cn_end, h_sc_end, h_ws_end]
          have hfuel' : fuel' ≥ (consumeNewline (skipToContentComment s1)).inputEnd -
                                 (consumeNewline (skipToContentComment s1)).offset + 1 := by
            have h_scc_lt := peek_some_hasMore (skipToContentComment s1) c' hpeek_c'
            have : sc.offset < sc.inputEnd := by
              have : (skipToContentComment s1).inputEnd = sc.inputEnd := by rw [h_sc_end, h_ws_end]
              omega
            have : (consumeNewline (skipToContentComment s1)).offset ≥ sc.offset + 1 := by omega
            rw [h_cn_inputEnd]; omega
          split at hok
          · -- !isInFlowSequence: simpleKeyAllowed update
            exact ih
              { consumeNewline (skipToContentComment s1) with simpleKeyAllowed := true }
              s_result hfuel' hok hpeek
          · -- isInFlowSequence
            exact ih (consumeNewline (skipToContentComment s1)) s_result hfuel' hok hpeek
        · -- Not a break: stop and return
          rename_i hnlb
          have hinj := Except.ok.inj hok; subst hinj
          have : c = c' := Option.some.inj (hpeek.symm.trans hpeek_c')
          subst this; exact Bool.eq_false_iff.mpr hnlb
      · -- peek? = none: stop — contradicts hpeek
        rename_i hpeek_none
        have hinj := Except.ok.inj hok; subst hinj
        rw [hpeek_none] at hpeek; exact absurd hpeek (by simp)

-- skipToContent returns at non-break chars.
lemma skipToContent_peek_not_break
    (sc s_result : ScannerState) (c : Char)
    (hok : skipToContent sc = .ok s_result)
    (hpeek : s_result.peek? = some c) :
    isLineBreakBool c = false := by
  unfold skipToContent at hok
  exact skipToContentLoop_peek_not_break sc _ s_result c (by omega) hok hpeek

/-! ## §8 Document marker productions (status note)

    `scanDocumentStart_prod` and `scanDocumentEnd_prod` already exist in
    StructureProduction.lean (Layer 4a). `SLDocumentSuffix` composition
    already exists in DocumentProduction.lean (Layer 3). No new theorems
    needed here — this layer provides the preprocessing coupling that
    feeds into those existing results. -/

/-! ## §9 Separator composition algebra (Fix A B.4β.2, sep-threading)

    Transitivity of the separation productions: two adjacent separations
    compose into one. This is the enabling primitive for the flow-interior
    sep-threading rule (each accumulation step consumes its OWN leading
    separation, which must be folded into the trailing separator slot of the
    grammar construct built by the PREVIOUS step — an entry's trailing
    `GOpt (SSeparate n c)`, a `held` frame's post-comma slot, or the
    collection's post-bracket slot). With composition, those retrofits are
    total algebra: no reachability reasoning about which slot shapes occur.

    Derivability rests on the deliberate col-agnostic weakening of
    `SSeparateInLine.startOfLine` (any zero-width match, §5.2 BOM note): the
    only refutations needed are column-arithmetic (whitespace runs strictly
    increase the column, so none can end at an actual start of line). -/

/-- An inline separation is a whitespace run (`startOfLine` is the empty run). -/
lemma SSeparateInLine_to_GStar_SSWhite {a b : SurfPos}
    (h : SSeparateInLine a b) : GStar SSWhite a b :=
  match h with
  | .whites _ _ (.mk _ _ _ hw hrest) => .cons _ _ _ hw hrest
  | .startOfLine _ => .nil _

/-- Inline separations compose. -/
lemma SSeparateInLine_trans {a b c : SurfPos}
    (h₁ : SSeparateInLine a b) (h₂ : SSeparateInLine b c) : SSeparateInLine a c :=
  match h₁ with
  | .startOfLine _ => h₂
  | .whites _ _ (.mk _ s₂ _ hx hrest) =>
    .whites _ _ (GPlus.mk _ s₂ _ hx (GStar_trans hrest (SSeparateInLine_to_GStar_SSWhite h₂)))

/-- A nonempty whitespace run strictly increases the column. -/
lemma gplus_sswhite_col_gt {a b : SurfPos} (h : GPlus SSWhite a b) :
    b.col ≥ a.col + 1 := by
  cases h
  rename_i hw hrest
  have h1 := sswhite_col_succ _ _ hw
  have h2 := gstar_sswhite_col_ge _ _ hrest
  omega

/-- Indentation is a whitespace run. -/
lemma SIndent_to_GStar_SSWhite {n : Nat} {a b : SurfPos}
    (h : SIndent n a b) : GStar SSWhite a b := by
  induction h with
  | zero => exact .nil _
  | succ n rest col s' _ ih => exact .cons _ ⟨rest, col + 1⟩ _ (.space rest col) ih

/-- A flow line prefix (indent + optional inline separation) is a whitespace run. -/
lemma SFlowLinePrefix_to_GStar_SSWhite {n : Nat} {a b : SurfPos}
    (h : SFlowLinePrefix n a b) : GStar SSWhite a b := by
  cases h
  rename_i hind hopt
  refine GStar_trans (SIndent_to_GStar_SSWhite hind) ?_
  cases hopt with
  | none => exact .nil _
  | some _ hil => exact SSeparateInLine_to_GStar_SSWhite hil

/-- Prepend an inline separation to an `SSBComment` (folds into its leading
    `s-separate-in-line` slot). -/
lemma SSBComment_prepend {a b c : SurfPos}
    (h_il : SSeparateInLine a b) (h : SSBComment b c) : SSBComment a c := by
  cases h with
  | withSep s₁ s₂ _ hsep hopt hbc =>
    exact .withSep _ s₁ s₂ _ (SSeparateInLine_trans h_il hsep) hopt hbc
  | noSep _ hbc => exact .withSep _ b b _ h_il (GOpt.none b) hbc

/-- A whitespace run followed by an `s-b-comment` is a full `l-comment` line. -/
lemma SLComment_of_ws_SSBComment {a b c : SurfPos}
    (h_ws : GStar SSWhite a b) (h : SSBComment b c) (h0 : a = b → a.col = 0) :
    SLComment a c := by
  cases h with
  | withSep s₁ s₂ _ hsep hopt hbc =>
    exact .mk _ s₁ s₂ _
      (SSeparateInLine_trans (GStar_SSWhite_to_SSeparateInLine a b h_ws h0) hsep) hopt hbc
  | noSep _ hbc =>
    exact .mk _ b b _ (GStar_SSWhite_to_SSeparateInLine a b h_ws h0) (GOpt.none b) hbc

/-- Append a run of `l-comment` lines to an `SSLComments` (generalizes
    `SSLComments_snoc`). -/
lemma SSLComments_append_gstar {a b c : SurfPos}
    (h_ssl : SSLComments a b) (h_lcs : GStar SLComment b c) : SSLComments a c := by
  cases h_ssl
  · rename_i mid hsbc hgstar
    exact .withComment _ mid _ hsbc (GStar_trans hgstar h_lcs)
  · rename_i chars hgstar
    exact .startOfLine chars _ (GStar_trans hgstar h_lcs)

/-- Prepend an inline separation to an `SSLComments`. The `startOfLine` head is
    reachable only by the empty run (a nonempty whitespace run cannot end at
    column 0). -/
lemma SSLComments_prepend_inline {a b c : SurfPos}
    (h_il : SSeparateInLine a b) (h : SSLComments b c) : SSLComments a c := by
  cases h
  · rename_i mid hsbc hgstar
    exact .withComment _ mid _ (SSBComment_prepend h_il hsbc) hgstar
  · rename_i chars hgstar
    cases h_il
    · rename_i hp
      exact absurd (gplus_sswhite_col_gt hp) (by simp)
    · exact .startOfLine _ _ hgstar

/-- The swallowed white, handed back: a run into the cursor turns the
    separator-less comment shape into `[79]` from the run's start. -/
lemma SSLCommentsFrom_prepend_white {a sp sp_mid : SurfPos}
    (h_ws : GStar SSWhite a sp) (h0 : a = sp → a.col = 0)
    (h : SSLCommentsFrom sp sp_mid) : SSLComments a sp_mid := by
  rcases h with h | ⟨_, sp_cmt, sp_brk, h_cmt, h_bc, h_rest⟩
  · exact SSLComments_prepend_inline (GStar_SSWhite_to_SSeparateInLine a sp h_ws h0) h
  · exact .withComment a sp_brk sp_mid
      (.withSep a sp sp_cmt sp_brk (GStar_SSWhite_to_SSeparateInLine a sp h_ws h0)
        (.some _ _ h_cmt) h_bc) h_rest

/-- Prepend a whitespace run to an `s-separate-lines(n)`.

    **β.3's trailing-whitespace bridge.** A flow-interior plain scalar ends its
    *grammar* production before the whitespace the scanner then consumes
    (`trimTrailingWS` drops it from the token value, but `collectPlainScalarLoop`
    has already advanced past it), so the accumulation's flow endpoint sits a
    whitespace run behind the scanner cursor.  The next step's leading separation
    is derived from the cursor; this lemma walks it back to the endpoint, which is
    where the frame's pending `GOpt (SSeparate n c)` slot expects it. -/
lemma SSeparateLines_prepend_white {n : Nat} {a b c : SurfPos}
    (h_ws : GStar SSWhite a b) (h : SSeparateLines n b c) : SSeparateLines n a c := by
  cases h_ws with
  | nil _ => exact h
  | cons _ s₂ _ hx hrest =>
  have h_il : SSeparateInLine a b := .whites _ _ (GPlus.mk _ s₂ _ hx hrest)
  cases h with
  | commented _ _ h_ssl h_pre =>
    exact .commented _ _ _ _ (SSLComments_prepend_inline h_il h_ssl) h_pre
  | inline _ h_inl =>
    exact .inline _ _ _ (SSeparateInLine_trans h_il h_inl)

/-- Splice `SSLComments + flow-line-prefix + SSLComments` into one
    `SSLComments` (the prefix + the second block's head comment fold into one
    additional `l-comment` line). -/
lemma SSLComments_trans_prefix {n : Nat} {a s₁ b c : SurfPos}
    (h₁ : SSLComments a s₁) (h_pre : SFlowLinePrefix n s₁ b)
    (h₂ : SSLComments b c) : SSLComments a c := by
  have h_ws := SFlowLinePrefix_to_GStar_SSWhite h_pre
  cases h₂
  · rename_i mid hsbc hgstar
    cases h_ws with
    | nil _ =>
      rcases SSLComments_end_col0_or_eof h₁ with hcol | heof
      · exact SSLComments_append_gstar
          (SSLComments_snoc h₁ (SSBComment_to_SLComment _ _ hsbc hcol)) hgstar
      · have h1 := ScalarProduction.ssbcomment_at_eof heof hsbc
        subst h1
        have h2 := ScalarProduction.gstar_slcomment_at_eof heof hgstar
        subst h2
        exact h₁
    | cons _ _ _ hx hrest =>
      exact SSLComments_append_gstar
        (SSLComments_snoc h₁ (SLComment_of_ws_SSBComment (GStar.cons _ _ _ hx hrest) hsbc
          (fun heq => by
            have := gplus_sswhite_col_gt (GPlus.mk _ _ _ hx hrest)
            rw [heq] at this; omega))) hgstar
  · rename_i chars hgstar
    have h_eq : (⟨chars, 0⟩ : SurfPos) = s₁ :=
      gstar_sswhite_col_eq_nil s₁ ⟨chars, 0⟩
        (by have := gstar_sswhite_col_ge _ _ h_ws; simp at this ⊢; omega) h_ws
    exact SSLComments_append_gstar h₁ (h_eq ▸ hgstar)

/-- Extend a flow line prefix by an inline separation (folds into its optional
    trailing `s-separate-in-line` slot). -/
lemma SFlowLinePrefix_extend_inline {n : Nat} {a b c : SurfPos}
    (h : SFlowLinePrefix n a b) (h_il : SSeparateInLine b c) :
    SFlowLinePrefix n a c := by
  cases h
  rename_i hind hopt
  cases hopt with
  | none => exact .mk n _ _ _ hind (GOpt.some _ _ h_il)
  | some _ hil => exact .mk n _ _ _ hind (GOpt.some _ _ (SSeparateInLine_trans hil h_il))

/-- `s-separate-lines(n)` composes. -/
lemma SSeparateLines_trans {n : Nat} {a b c : SurfPos}
    (h₁ : SSeparateLines n a b) (h₂ : SSeparateLines n b c) :
    SSeparateLines n a c := by
  cases h₁ with
  | inline _ hil₁ =>
    cases h₂ with
    | inline _ hil₂ => exact .inline n _ _ (SSeparateInLine_trans hil₁ hil₂)
    | commented s₁ _ hssl hpre =>
      exact .commented n _ s₁ _ (SSLComments_prepend_inline hil₁ hssl) hpre
  | commented s₁ _ hssl₁ hpre₁ =>
    cases h₂ with
    | inline _ hil₂ =>
      exact .commented n _ s₁ _ hssl₁ (SFlowLinePrefix_extend_inline hpre₁ hil₂)
    | commented s₂ _ hssl₂ hpre₂ =>
      exact .commented n _ s₂ _ (SSLComments_trans_prefix hssl₁ hpre₁ hssl₂) hpre₂

/-- `s-separate(n,c)` composes (context-generic). -/
lemma SSeparate_trans {n : Nat} {c : YamlContext} {a b c' : SurfPos}
    (h₁ : SSeparate n c a b) (h₂ : SSeparate n c b c') : SSeparate n c a c' := by
  cases c with
  | blockOut | blockIn | flowOut | flowIn => exact SSeparateLines_trans h₁ h₂
  | blockKey | flowKey => exact SSeparateInLine_trans h₁ h₂

/-- Extend an optional separation by a further separation (retrofit primitive:
    fold a step's leading separation into the previous construct's trailing
    `GOpt` slot). -/
lemma GOpt_SSeparate_extend {n : Nat} {c : YamlContext} {a b c' : SurfPos}
    (h : GOpt (SSeparate n c) a b) (h_sep : SSeparate n c b c') :
    GOpt (SSeparate n c) a c' := by
  cases h with
  | none => exact .some _ _ h_sep
  | some _ hs => exact .some _ _ (SSeparate_trans hs h_sep)

/-- Extend an optional separation by an optional separation. -/
lemma GOpt_SSeparate_extend_opt {n : Nat} {c : YamlContext} {a b c' : SurfPos}
    (h : GOpt (SSeparate n c) a b) (h' : GOpt (SSeparate n c) b c') :
    GOpt (SSeparate n c) a c' := by
  cases h' with
  | none => exact h
  | some _ hs => exact GOpt_SSeparate_extend h hs

/-- Retrofit a trailing separation onto closeable flow-seq entries: the
    separation folds into the innermost entry's trailing `GOpt` slot. -/
lemma SFlowSeqEntries_extendSep {n : Nat} {c : YamlContext} {s s_e s' : SurfPos}
    {h_entries : SFlowSeqEntries n c s s_e}
    (h_cl : FlowSeqEntriesCloseable h_entries)
    (h_sep : SSeparate n c s_e s') :
    ∃ h' : SFlowSeqEntries n c s s', FlowSeqEntriesCloseable h' := by
  induction h_cl with
  | single he hsep =>
    have hsep2 := GOpt_SSeparate_extend hsep h_sep
    exact ⟨.single _ _ _ _ _ he hsep2, .single he hsep2⟩
  | consMore he hsep hcomma hsep' tail _ ih =>
    obtain ⟨tail', h_cl'⟩ := ih h_sep
    exact ⟨.consMore _ _ _ _ _ _ _ _ he hsep hcomma hsep' tail',
           .consMore he hsep hcomma hsep' tail' h_cl'⟩

/-- Retrofit a trailing separation onto closeable flow-map entries. -/
lemma SFlowMapEntries_extendSep {n : Nat} {c : YamlContext} {s s_e s' : SurfPos}
    {h_entries : SFlowMapEntries n c s s_e}
    (h_cl : FlowMapEntriesCloseable h_entries)
    (h_sep : SSeparate n c s_e s') :
    ∃ h' : SFlowMapEntries n c s s', FlowMapEntriesCloseable h' := by
  induction h_cl with
  | single he hsep =>
    have hsep2 := GOpt_SSeparate_extend hsep h_sep
    exact ⟨.single _ _ _ _ _ he hsep2, .single he hsep2⟩
  | consMore he hsep hcomma hsep' tail _ ih =>
    obtain ⟨tail', h_cl'⟩ := ih h_sep
    exact ⟨.consMore _ _ _ _ _ _ _ _ he hsep hcomma hsep' tail',
           .consMore he hsep hcomma hsep' tail' h_cl'⟩


/-! ## N3: the frame's one conversion at a park -/

/-- A park whose characters begin with `c` has `c` under the scanner's cursor. -/
lemma peek_of_corr_cons {sc : ScannerState} {c : Char} {rest : List Char} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩) : sc.peek? = some c := by
  have hmore : sc.offset < sc.inputEnd := by
    rcases Nat.lt_or_ge sc.offset sc.inputEnd with h | h
    · exact h
    · exfalso
      have h2 := eof_corr sc _ hcorr (Nat.not_lt.mpr h)
      simp at h2
  obtain ⟨c', rest', hch, hpk⟩ := peek_corr sc _ hcorr hmore
  simp only [List.cons.injEq] at hch
  rw [← hch.1] at hpk
  exact hpk

/-- The scanner's comment gate FAILS right after it consumed a character that
    is neither white, break nor BOM, away from column 0: `peekBack?` is that
    character.  The uniform refutation for indicator and closing-quote parks. -/
lemma CommentOk_false_of_advance {sc : ScannerState} {c : Char} {rest : List Char}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, sc.col⟩)
    (hmore : sc.offset < sc.inputEnd)
    (hnl : c ≠ '\n') (hcr : c ≠ '\r')
    (hcol : sc.advance.col ≠ 0)
    (hc : (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false) :
    ¬ CommentOk sc.advance := by
  intro h
  have hpb := advance_peekBack_eq_peek hcorr hmore hnl hcr
  rcases h with h | h | ⟨c', hc', hw⟩
  · exact hcol h
  · rw [hpb] at h; cases h
  · rw [hpb] at hc'
    cases hc'
    rw [hc] at hw
    cases hw

/-- **The frame's one conversion.**  A landing read from the scanner park
    `sp_scan` becomes `[79] s-l-comments` from the GRAMMAR endpoint `sp_gram`:
    the whites the token swallowed are the comment's `[66]` separator, and with
    no whites the separator-less shape is refuted by the park's own comment
    gate (`h_gate`: plain parks never stop on `#` without whites, indicator
    parks fail `commentOk`). -/
lemma SSLCommentsFrom_at_park {sc : ScannerState} {sp_gram sp_scan sp_mid : SurfPos}
    (hcorr : ScannerSurfCorr sc sp_scan)
    (h_run : GStar SSWhite sp_gram sp_scan)
    (h_gate : sp_gram = sp_scan → sc.col ≠ 0 → ¬ (CommentOk sc ∧ sc.peek? = some '#'))
    (h_from : SSLCommentsFrom sp_scan sp_mid)
    (h_ok : SSLComments sp_scan sp_mid ∨ CommentOk sc) :
    SSLComments sp_gram sp_mid := by
  have h_ord : SSLComments sp_scan sp_mid → SSLComments sp_gram sp_mid := by
    intro h
    by_cases h_eq : sp_gram = sp_scan
    · subst h_eq; exact h
    · exact SSLComments_prepend_inline
        (GStar_SSWhite_to_SSeparateInLine _ _ h_run (fun he => absurd he h_eq)) h
  rcases h_ok with h | hcok
  · exact h_ord h
  · rcases h_from with h | ⟨hpos, sp_cmt, sp_brk, h_cmt, h_bc, h_rest⟩
    · exact h_ord h
    · have hpk : sc.peek? = some '#' := by
        cases h_cmt with
        | mk rest col s' _ => exact peek_of_corr_cons hcorr
      by_cases h_eq : sp_gram = sp_scan
      · exact absurd ⟨hcok, hpk⟩ (h_gate h_eq (by rw [← hcorr.col_eq]; omega))
      · exact .withComment _ sp_brk _
          (.withSep sp_gram sp_scan sp_cmt sp_brk
            (.whites _ _ (GStar_to_GPlus h_run h_eq)) (.some _ _ h_cmt) h_bc) h_rest



/-- The anchor/alias name walk only consumes characters that FAIL the scanner's
    comment gate (`ns-anchor-char`: no white, break or BOM), so after a
    nonempty name the park's `peekBack?` is such a character. -/
lemma collectAnchorNameLoop_peekBack (fuel : Nat) :
    ∀ (sc : ScannerState) (sp : SurfPos) (name : String),
    ScannerSurfCorr sc sp →
    (collectAnchorNameLoop sc name fuel).snd = sc ∨
    ∃ c, (collectAnchorNameLoop sc name fuel).snd.peekBack? = some c ∧
      (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false := by
  induction fuel with
  | zero => intro sc sp name _; simp [collectAnchorNameLoop]
  | succ fuel' ih =>
    intro sc sp name hcorr
    unfold collectAnchorNameLoop
    split
    · rename_i c hpeek
      split
      · rename_i hguard
        have hmore : sc.offset < sc.inputEnd := by
          by_cases h : sc.offset < sc.inputEnd
          · exact h
          · exfalso
            have hz := eof_corr sc sp hcorr h
            obtain ⟨c', rest', hch, hpk⟩ := peek_corr sc sp hcorr (by
              -- peek? = some c forces hasMore
              unfold ScannerState.peek? at hpeek
              split at hpeek
              · assumption
              · cases hpeek)
            rw [hz] at hch; cases hch
        obtain ⟨c', rest, hch, hpk⟩ := peek_corr sc sp hcorr hmore
        rw [hpeek] at hpk; cases hpk
        have hcorr_c : ScannerSurfCorr sc ⟨c :: rest, sc.col⟩ := by
          have hsp : sp = ⟨c :: rest, sc.col⟩ := by
            cases sp; simp only [SurfPos.mk.injEq]; exact ⟨hch, hcorr.col_eq⟩
          exact hsp ▸ hcorr
        simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hguard
        obtain ⟨⟨⟨⟨-, hws⟩, hbr⟩, -⟩, hbom⟩ := hguard
        have hnl : c ≠ '\n' := fun h => by subst h; exact absurd hbr (by decide)
        have hcr : c ≠ '\r' := fun h => by subst h; exact absurd hbr (by decide)
        have hpb := advance_peekBack_eq_peek hcorr_c hmore hnl hcr
        have hflag : (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false := by
          simp [hws, hbr, hbom]
        obtain ⟨sp', hcorr'⟩ := L4YAML.Proofs.ScalarCoupling.advance_corr sc sp hcorr
        rcases ih sc.advance sp' (name.push c) hcorr' with heq | ⟨c2, hpb2, hflag2⟩
        · exact Or.inr ⟨c, by rw [heq]; exact hpb, hflag⟩
        · exact Or.inr ⟨c2, hpb2, hflag2⟩
      · exact Or.inl rfl
    · exact Or.inl rfl


/-- A park whose last consumed character is neither white, break nor BOM fails
    the scanner's comment gate off a line start. -/
lemma CommentOk_false_of_peekBack {sc : ScannerState} {c : Char}
    (hcol : sc.col ≠ 0) (hpb : sc.peekBack? = some c)
    (hc : (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false) :
    ¬ CommentOk sc := by
  intro h
  rcases h with h0 | hnone | ⟨c', hc', hflag⟩
  · exact hcol h0
  · rw [hpb] at hnone; cases hnone
  · rw [hpb] at hc'; cases hc'; rw [hc] at hflag; cases hflag


/-- An anchor/alias park's last consumed character is the marker or an
    `ns-anchor-char`: never white, break or BOM. -/
lemma scanAnchorOrAlias_peekBack {sc : ScannerState} {sp : SurfPos} {marker : Char}
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some marker)
    (hmk : (isWhiteSpaceBool marker || isLineBreakBool marker || marker == '\uFEFF') = false)
    (hnl : marker ≠ '\n') (hcr : marker ≠ '\r')
    {isAnchor : Bool} {s' : ScannerState}
    (hok : scanAnchorOrAlias sc isAnchor = .ok s') :
    ∃ c, s'.peekBack? = some c ∧
      (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false := by
  obtain ⟨rest, hsp_eq⟩ := L4YAML.Proofs.ScalarProduction.peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := L4YAML.Proofs.ScalarProduction.peek_some_has_more hpeek
  have hpb0 := advance_peekBack_eq_peek hcorr hmore hnl hcr
  obtain ⟨sp_adv, hcorr_adv⟩ := L4YAML.Proofs.ScalarCoupling.advance_corr sc _ hcorr
  have hloop := collectAnchorNameLoop_peekBack (sc.inputEnd - sc.advance.offset)
    sc.advance sp_adv "" hcorr_adv
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h
    rcases hloop with heq | ⟨c, hpb, hflag⟩
    · exact ⟨marker, by
        show (collectAnchorNameLoop sc.advance "" _).snd.peekBack? = some marker
        rw [heq]; exact hpb0, hmk⟩
    · exact ⟨c, hpb, hflag⟩


/-! ### Tag parks: the last consumed character fails the comment gate -/

lemma advance_peekBack_of_peek {sc : ScannerState} {sp : SurfPos} {c : Char}
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some c)
    (hnl : c ≠ '\n') (hcr : c ≠ '\r') : sc.advance.peekBack? = some c := by
  obtain ⟨rest, hsp_eq⟩ := L4YAML.Proofs.ScalarProduction.peek_some_sp hcorr hpeek
  subst hsp_eq
  exact advance_peekBack_eq_peek hcorr
    (L4YAML.Proofs.ScalarProduction.peek_some_has_more hpeek) hnl hcr

lemma isUriChar_flag_false (c : Char) (h : isUriCharBool c = true) :
    (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false := by
  have hlb : isLineBreakBool c = false := by
    have := L4YAML.Proofs.StructureProduction.isUriChar_not_isLineBreak c h; simpa using this
  rw [hlb]
  simp only [isUriCharBool, decide_eq_true_eq] at h
  by_cases hs : c = ' '
  · subst hs; simp [isUriCharProp, isWordCharProp, isAsciiLetterProp] at h
  by_cases ht : c = '\t'
  · subst ht; simp [isUriCharProp, isWordCharProp, isAsciiLetterProp] at h
  by_cases hb : c = '\uFEFF'
  · subst hb; simp [isUriCharProp, isWordCharProp, isAsciiLetterProp] at h
  simp [isWhiteSpaceBool, isSpaceBool, isTabBool, hs, ht, hb]

lemma isTagChar_flag_false (c : Char) (h : isTagCharBool c = true) :
    (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false :=
  isUriChar_flag_false c ((isUriChar_iff c).2 ((isTagChar_iff c).1 h).1)

lemma isWordChar_flag_false (c : Char) (h : isWordCharBool c = true) :
    (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false :=
  isUriChar_flag_false c ((isUriChar_iff c).2 (Or.inl ((isWordChar_iff c).1 h)))

lemma collectVerbatimTagLoop_peekBack (fuel : Nat) :
    ∀ (sc : ScannerState) (sp : SurfPos) (uri : String), ScannerSurfCorr sc sp →
    (collectVerbatimTagLoop sc uri fuel).2.2 = sc ∨
    ∃ c, (collectVerbatimTagLoop sc uri fuel).2.2.peekBack? = some c ∧
      (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false := by
  induction fuel with
  | zero => intro sc sp uri _; simp [collectVerbatimTagLoop]
  | succ fuel' ih =>
    intro sc sp uri hcorr
    unfold collectVerbatimTagLoop
    split
    · have hpk : sc.peek? = some '>' := by assumption
      exact Or.inr ⟨'>', advance_peekBack_of_peek hcorr hpk (by decide) (by decide), by decide⟩
    · rename_i c _ _
      have hpk : sc.peek? = some c := by assumption
      split
      · rename_i hguard
        have hflag := isUriChar_flag_false c hguard
        have hpb := advance_peekBack_of_peek hcorr hpk
          (fun h => by subst h; exact absurd hflag (by decide))
          (fun h => by subst h; exact absurd hflag (by decide))
        obtain ⟨sp', hcorr'⟩ := L4YAML.Proofs.ScalarCoupling.advance_corr sc sp hcorr
        rcases ih sc.advance sp' (uri.push c) hcorr' with heq | ⟨c2, hpb2, hflag2⟩
        · exact Or.inr ⟨c, by rw [heq]; exact hpb, hflag⟩
        · exact Or.inr ⟨c2, hpb2, hflag2⟩
      · exact Or.inl rfl
    · exact Or.inl rfl

lemma collectTagSuffixLoop_peekBack (fuel : Nat) :
    ∀ (sc : ScannerState) (sp : SurfPos) (suffix : String), ScannerSurfCorr sc sp →
    (collectTagSuffixLoop sc suffix fuel).snd = sc ∨
    ∃ c, (collectTagSuffixLoop sc suffix fuel).snd.peekBack? = some c ∧
      (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false := by
  induction fuel with
  | zero => intro sc sp suffix _; simp [collectTagSuffixLoop]
  | succ fuel' ih =>
    intro sc sp suffix hcorr
    unfold collectTagSuffixLoop
    split
    · rename_i c _
      have hpk : sc.peek? = some c := by assumption
      split
      · rename_i hguard
        have hflag := isTagChar_flag_false c hguard
        have hpb := advance_peekBack_of_peek hcorr hpk
          (fun h => by subst h; exact absurd hflag (by decide))
          (fun h => by subst h; exact absurd hflag (by decide))
        obtain ⟨sp', hcorr'⟩ := L4YAML.Proofs.ScalarCoupling.advance_corr sc sp hcorr
        rcases ih sc.advance sp' (suffix.push c) hcorr' with heq | ⟨c2, hpb2, hflag2⟩
        · exact Or.inr ⟨c, by rw [heq]; exact hpb, hflag⟩
        · exact Or.inr ⟨c2, hpb2, hflag2⟩
      · exact Or.inl rfl
    · exact Or.inl rfl

lemma collectTagHandleLoop_peekBack (fuel : Nat) :
    ∀ (sc : ScannerState) (sp : SurfPos) (chars : String), ScannerSurfCorr sc sp →
    (∃ sp', ScannerSurfCorr (collectTagHandleLoop sc chars fuel).2.2 sp') ∧
    ((collectTagHandleLoop sc chars fuel).2.2 = sc ∨
    ∃ c, (collectTagHandleLoop sc chars fuel).2.2.peekBack? = some c ∧
      (isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF') = false) := by
  induction fuel with
  | zero => intro sc sp chars hcorr; simp [collectTagHandleLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    intro sc sp chars hcorr
    unfold collectTagHandleLoop
    split
    · have hpk : sc.peek? = some '!' := by assumption
      obtain ⟨sp', hcorr'⟩ := L4YAML.Proofs.ScalarCoupling.advance_corr sc sp hcorr
      exact ⟨⟨sp', hcorr'⟩,
        Or.inr ⟨'!', advance_peekBack_of_peek hcorr hpk (by decide) (by decide), by decide⟩⟩
    · rename_i c _ _
      have hpk : sc.peek? = some c := by assumption
      split
      · rename_i hguard
        have hflag := isWordChar_flag_false c hguard
        have hpb := advance_peekBack_of_peek hcorr hpk
          (fun h => by subst h; exact absurd hflag (by decide))
          (fun h => by subst h; exact absurd hflag (by decide))
        obtain ⟨sp', hcorr'⟩ := L4YAML.Proofs.ScalarCoupling.advance_corr sc sp hcorr
        obtain ⟨hc, hrest⟩ := ih sc.advance sp' (chars.push c) hcorr'
        refine ⟨hc, ?_⟩
        rcases hrest with heq | ⟨c2, hpb2, hflag2⟩
        · exact Or.inr ⟨c, by rw [heq]; exact hpb, hflag⟩
        · exact Or.inr ⟨c2, hpb2, hflag2⟩
      · exact ⟨⟨sp, hcorr⟩, Or.inl rfl⟩
    · exact ⟨⟨sp, hcorr⟩, Or.inl rfl⟩

end L4YAML.Proofs.PreprocessProduction

end Blanket
