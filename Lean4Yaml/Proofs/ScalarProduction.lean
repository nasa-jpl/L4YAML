import Lean4Yaml.Proofs.ScalarCoupling
import Lean4Yaml.Proofs.ScannerCorrectness

/-! # Scalar Production Coupling (Phase B of v0.4.4)

    Strengthen the `_corr` theorems from `ScalarCoupling.lean` to additionally
    produce surface-syntax derivation trees (`SCDoubleQuoted`, `SCSingleQuoted`,
    `SNsPlain`, `SCLLiteral`, `SCLFolded`).

    Strategy: use `n = 0` and `c = .blockIn` existentially so that indentation
    requirements (`SIndent 0`, `SFlowLinePrefix 0`) become trivial.

    **Status**: Double-quoted scalar fully proven (1 known limitation:
    lone <CR> column tracking in scanner — see `consumeNewline_sbreak_corr`).
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.ScalarProduction

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScannerCoupling
open Lean4Yaml.Proofs.ScalarCoupling
open Lean4Yaml.Grammar
open Lean4Yaml (ChompStyle)
open Lean4Yaml.Proofs.ScannerProgress (advance_offset_lt)
open Lean4Yaml.Proofs.ScannerCorrectness (skipWhitespaceLoop_offset_ge)

/-! ## §1 Helpers -/

-- Derive `offset < inputEnd` from `peek? = some c`
theorem peek_some_has_more {sc : ScannerState} {c : Char}
    (hpeek : sc.peek? = some c) : sc.offset < sc.inputEnd := by
  unfold ScannerState.peek? at hpeek
  split at hpeek
  · assumption
  · cases hpeek

-- Derive exact surface position from `peek? = some c` + `ScannerSurfCorr`
theorem peek_some_sp {sc : ScannerState} {sp : SurfPos} {c : Char}
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
theorem SNbDoubleMultiLine_prepend (s s₁ s_end : SurfPos)
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
theorem not_lineBreak_bool_to_prop {c : Char}
    (h : ¬isLineBreakBool c = true) : ¬isLineBreakProp c :=
  fun hlb => h ((isLineBreak_iff c).mpr hlb)

/-! ## §1b Surface construction helpers -/

-- SIndent → GStar SSWhite
theorem sindent_to_gstar_sswhite {n : Nat} {sp sp' : SurfPos}
    (h : SIndent n sp sp') : GStar SSWhite sp sp' := by
  induction h with
  | zero => exact GStar.nil _
  | succ n rest col s' _ ih => exact GStar.cons _ _ _ (SSWhite.space rest col) ih

-- Concatenation of GStar SSWhite
theorem gstar_sswhite_append {sp1 sp2 sp3 : SurfPos}
    (h1 : GStar SSWhite sp1 sp2) (h2 : GStar SSWhite sp2 sp3) :
    GStar SSWhite sp1 sp3 := by
  induction h1 with
  | nil => exact h2
  | cons _ _ _ hx _ ih => exact GStar.cons _ _ _ hx (ih h2)

-- GStar SSWhite → GOpt SSeparateInLine
theorem gstar_sswhite_to_gopt_sep {sp sp' : SurfPos}
    (h : GStar SSWhite sp sp') : GOpt SSeparateInLine sp sp' := by
  match h with
  | GStar.nil _ => exact GOpt.none _
  | GStar.cons a b c hfirst hrest =>
    exact GOpt.some a c (SSeparateInLine.whites a c (GPlus.mk a b c hfirst hrest))

/-! ## §1c consumeNewline with SBBreak production

  When the scanner is at a linebreak, `consumeNewline` produces both an
  `SBBreak` and preserves `ScannerSurfCorr`.  The scanner's `advance`
  treats both `\n` and `\r` as line terminators (col:=0, line+1) per
  YAML spec §5.4 [28].  For CRLF, the `\n` byte is skipped by raw
  offset increment to avoid double-counting the line. -/
theorem consumeNewline_sbreak_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true) :
    ∃ sp', SBBreak sp sp' ∧ ScannerSurfCorr (consumeNewline sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  simp [isLineBreakBool, Bool.or_eq_true, beq_iff_eq] at hlb
  rcases hlb with rfl | rfl
  · -- c = '\n'
    have hadv := advance_newline_corr sc rest hcorr hmore
    refine ⟨⟨rest, 0⟩, SBBreak.lf rest sc.col, ?_⟩
    show ScannerSurfCorr (consumeNewline sc) ⟨rest, 0⟩
    unfold consumeNewline; simp only [hpeek]
    exact corr_of_needIndentCheck_update true hadv
  · -- c = '\r': advance sets col:=0 (line break)
    have hadv := advance_cr_corr sc rest hcorr hmore
    unfold consumeNewline; simp only [hpeek]
    split
    · -- sc.advance.peek? = some '\n' (CRLF)
      rename_i hpeek2
      have hmore2 := peek_some_has_more hpeek2
      obtain ⟨rest2, hchars2⟩ := peek_some_sp hadv hpeek2
      simp only [SurfPos.mk.injEq] at hchars2
      obtain ⟨hrest_eq, _⟩ := hchars2
      subst hrest_eq
      -- Raw offset skip for the \n byte (line count already handled by \r)
      have hskip := skip_byte_corr sc.advance '\n' rest2 0 hadv hmore2
      refine ⟨⟨rest2, 0⟩, SBBreak.crLf rest2 sc.col, ?_⟩
      exact corr_of_needIndentCheck_update true hskip
    · -- lone '\r': col=0, line+1 done by advance
      refine ⟨⟨rest, 0⟩, SBBreak.cr rest sc.col, ?_⟩
      exact corr_of_needIndentCheck_update true hadv

/-! ## §1d foldQuotedNewlinesLoop production -/

theorem foldQuotedNewlinesLoop_prod (sc : ScannerState) (sp : SurfPos)
    (cnt fuel : Nat) (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', GStar (SLEmpty 0 .flowIn) sp sp' ∧
           ScannerSurfCorr (foldQuotedNewlinesLoop sc cnt fuel).1 sp' := by
  induction fuel generalizing sc sp cnt with
  | zero =>
    simp [foldQuotedNewlinesLoop]
    exact ⟨sp, GStar.nil _, hcorr⟩
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop; dsimp only []
    obtain ⟨n_sk, sp_sk, h_indent, hcorr_sk⟩ := skipSpaces_corr sc sp hcorr
    split
    · rename_i c hpeek; split
      · rename_i hlb
        obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
          consumeNewline_sbreak_corr (skipSpaces sc) sp_sk c hcorr_sk hpeek hlb
        have h_gstar_ws := sindent_to_gstar_sswhite h_indent
        have h_gopt_sep := gstar_sswhite_to_gopt_sep h_gstar_ws
        have h_flp : SFlowLinePrefix 0 sp sp_sk :=
          SFlowLinePrefix.mk 0 sp sp sp_sk (SIndent.zero sp) h_gopt_sep
        have h_lempty : SLEmpty 0 .flowIn sp sp_cn :=
          SLEmpty.flow 0 sp sp_sk sp_cn .flowIn (Or.inr rfl)
            (GOpt.some sp sp_sk h_flp) h_sbreak
        obtain ⟨sp_rest, h_gstar_rest, hcorr_rest⟩ :=
          ih (consumeNewline (skipSpaces sc)) sp_cn (cnt + 1) hcorr_cn
        exact ⟨sp_rest,
               GStar.cons sp sp_cn sp_rest h_lempty h_gstar_rest,
               hcorr_rest⟩
      · exact ⟨sp, GStar.nil _, hcorr⟩
    · exact ⟨sp, GStar.nil _, hcorr⟩

/-! ## §1e Hex escape helpers -/

theorem scanner_hex_to_surface_hex (c : Char)
    (h : (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = true) :
    isNsHexDigit c := by
  unfold isNsHexDigit; unfold Char.isDigit at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with (⟨h1, h2⟩ | h) | h
  · left; exact ⟨h1, h2⟩
  · right; left; exact h
  · right; right; exact h

theorem hex_char_ne_newline (c : Char)
    (h : (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = true) :
    c ≠ '\n' := by
  intro heq; subst heq; simp [Char.isDigit] at h

theorem hex_char_ne_cr (c : Char)
    (h : (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = true) :
    c ≠ '\r' := by
  intro heq; subst heq; simp [Char.isDigit] at h

theorem collectHexDigitsLoop_prod (sc : ScannerState) (chars : List Char) (col : Nat)
    (hex : String) (n : Nat)
    (hcorr : ScannerSurfCorr sc ⟨chars, col⟩)
    (hlen : (collectHexDigitsLoop sc hex n).1.length = hex.length + n) :
    ∃ consumed rest,
      chars = consumed ++ rest ∧
      consumed.length = n ∧
      (∀ c, c ∈ consumed → isNsHexDigit c) ∧
      ScannerSurfCorr (collectHexDigitsLoop sc hex n).2 ⟨rest, col + n⟩ := by
  induction n generalizing sc chars col hex with
  | zero =>
    simp only [collectHexDigitsLoop] at hlen ⊢
    exact ⟨[], chars, rfl, rfl, (fun _ h => nomatch h), hcorr⟩
  | succ n ih =>
    cases hpeek_eq : sc.peek? with
    | none =>
      simp only [collectHexDigitsLoop, hpeek_eq] at hlen; omega
    | some c =>
      by_cases hhex : (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = true
      · have hstep : collectHexDigitsLoop sc hex (n + 1) =
            collectHexDigitsLoop sc.advance (hex.push c) n := by
          simp only [collectHexDigitsLoop, hpeek_eq, hhex, ite_true]
        rw [hstep] at hlen ⊢
        obtain ⟨rest_after, hsp_eq⟩ := peek_some_sp hcorr hpeek_eq
        obtain ⟨hchars_eq, hcol_eq⟩ : chars = c :: rest_after ∧ col = sc.col := by
          exact ⟨by injection hsp_eq, by injection hsp_eq⟩
        subst hchars_eq; subst hcol_eq
        have hmore := peek_some_has_more hpeek_eq
        have hcorr_adv := advance_non_newline_corr sc c rest_after hcorr hmore
          (hex_char_ne_newline c hhex) (hex_char_ne_cr c hhex)
        have hlen_ih : (collectHexDigitsLoop sc.advance (hex.push c) n).1.length
            = (hex.push c).length + n := by
          have : (hex.push c).length = hex.length + 1 := String.length_push c; omega
        obtain ⟨consumed', rest', hchars', hlen_c', hhex_c', hcorr'⟩ :=
          ih sc.advance rest_after (sc.col + 1) (hex.push c) hcorr_adv hlen_ih
        exact ⟨c :: consumed', rest',
          by simp [hchars'],
          by simp [hlen_c'],
          (fun d hd => by cases hd with
            | head => exact scanner_hex_to_surface_hex c hhex
            | tail _ hm => exact hhex_c' d hm),
          by rw [show sc.col + (n + 1) = sc.col + 1 + n from by omega]; exact hcorr'⟩
      · have hhex_f : (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = false :=
          Bool.not_eq_true _ |>.mp hhex
        simp [collectHexDigitsLoop, hpeek_eq, hhex_f] at hlen

theorem parseHexEscape_prod (sc : ScannerState) (chars : List Char) (col : Nat)
    (n : Nat) {ch : Char} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc ⟨chars, col⟩)
    (hok : parseHexEscape sc n = .ok (ch, s')) :
    ∃ consumed rest,
      chars = consumed ++ rest ∧
      consumed.length = n ∧
      (∀ c, c ∈ consumed → isNsHexDigit c) ∧
      ScannerSurfCorr s' ⟨rest, col + n⟩ := by
  unfold parseHexEscape at hok
  dsimp only [] at hok
  split at hok
  · simp at hok
  · rename_i hlen_ok
    split at hok
    · obtain ⟨-, rfl⟩ := hok
      have hlen : (collectHexDigitsLoop sc "" n).1.length = "".length + n := by
        simp [bne] at hlen_ok
        have : ("" : String).length = 0 := rfl; omega
      exact collectHexDigitsLoop_prod sc chars col "" n hcorr hlen
    · simp at hok

theorem list_eq_cons {α : Type} {n : Nat} {l : List α} (h : l.length = n + 1) :
    ∃ a t, l = a :: t ∧ t.length = n := by
  cases l with | nil => simp at h | cons a t => exact ⟨a, t, rfl, by simpa using h⟩

/-! ## §2 Sub-lemmas -/

-- Abbreviation for the loop result expression
abbrev loopResult (sc : ScannerState) :=
  foldQuotedNewlinesLoop (consumeNewline sc) 0 (sc.inputEnd - (consumeNewline sc).offset + 1)

-- When `foldQuotedNewlines` succeeds at a line-break position,
-- the consumed chars form a flow-folded break: `SBBreak + GStar SLEmpty + SFlowLinePrefix`.
theorem foldQuotedNewlines_prod (sc : ScannerState) (sp : SurfPos)
    (c : Char)
    {content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true)
    (hfold : foldQuotedNewlines sc = .ok (content, s')) :
    ∃ sp₁ sp₂ sp',
      SBBreak sp sp₁ ∧
      GStar (SLEmpty 0 .flowIn) sp₁ sp₂ ∧
      SFlowLinePrefix 0 sp₂ sp' ∧
      ScannerSurfCorr s' sp' := by
  -- Step 1: consumeNewline → SBBreak
  obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
    consumeNewline_sbreak_corr sc sp c hcorr hpeek hlb
  -- Step 2: foldQuotedNewlinesLoop → GStar (SLEmpty 0 .flowIn)
  obtain ⟨sp_loop, h_gstar_empty, hcorr_loop⟩ :=
    foldQuotedNewlinesLoop_prod (consumeNewline sc) sp_cn 0 _ hcorr_cn
  -- Step 3: skipSpaces on loop result → SIndent
  obtain ⟨n_sk2, sp_sk2, h_indent2, hcorr_sk2⟩ :=
    skipSpaces_corr (loopResult sc).1 sp_loop hcorr_loop
  -- Unfold to trace through the do-notation
  unfold foldQuotedNewlines at hfold; dsimp only [] at hfold
  split at hfold
  · -- tab check branch
    split at hfold
    · simp only [bind, Except.bind] at hfold; simp at hfold
    · obtain ⟨sp_ws, h_gstar_ws, hcorr_ws⟩ :=
        skipWhitespace_corr _ sp_sk2 hcorr_sk2
      have h_all_ws := gstar_sswhite_append
        (sindent_to_gstar_sswhite h_indent2) h_gstar_ws
      have h_gopt := gstar_sswhite_to_gopt_sep h_all_ws
      have h_flp : SFlowLinePrefix 0 sp_loop sp_ws :=
        SFlowLinePrefix.mk 0 sp_loop sp_loop sp_ws (SIndent.zero sp_loop) h_gopt
      split at hfold
      · have hinj := Except.ok.inj hfold
        obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
        exact ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty, h_flp, hcorr_ws⟩
      · have hinj := Except.ok.inj hfold
        obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
        exact ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty, h_flp, hcorr_ws⟩
  · -- no tab check branch
    obtain ⟨sp_ws, h_gstar_ws, hcorr_ws⟩ :=
      skipWhitespace_corr _ sp_sk2 hcorr_sk2
    have h_all_ws := gstar_sswhite_append
      (sindent_to_gstar_sswhite h_indent2) h_gstar_ws
    have h_gopt := gstar_sswhite_to_gopt_sep h_all_ws
    have h_flp : SFlowLinePrefix 0 sp_loop sp_ws :=
      SFlowLinePrefix.mk 0 sp_loop sp_loop sp_ws (SIndent.zero sp_loop) h_gopt
    split at hfold
    · have hinj := Except.ok.inj hfold
      obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
      exact ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty, h_flp, hcorr_ws⟩
    · have hinj := Except.ok.inj hfold
      obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
      exact ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty, h_flp, hcorr_ws⟩

-- When `processEscape` succeeds, the `\` + escape chars form a valid `SNbDoubleChar`
-- starting from `⟨'\\' :: rest, col⟩`.
theorem processEscape_prod (sc_bs : ScannerState) (rest : List Char) (col : Nat)
    {ch : Char} {s' : ScannerState}
    (hcorr_bs : ScannerSurfCorr sc_bs ⟨rest, col + 1⟩)
    (hproc : processEscape sc_bs = .ok (ch, s')) :
    ∃ sp', SNbDoubleChar ⟨'\\' :: rest, col⟩ sp' ∧ ScannerSurfCorr s' sp' := by
  unfold processEscape at hproc
  split at hproc
  · simp at hproc
  · rename_i c_esc hpeek
    obtain ⟨rest_tail, hsp_eq⟩ := peek_some_sp hcorr_bs hpeek
    injection hsp_eq with h_rest h_col
    subst h_rest
    have h_col_eq : sc_bs.col = col + 1 := h_col.symm
    have hcorr_sc : ScannerSurfCorr sc_bs ⟨c_esc :: rest_tail, sc_bs.col⟩ := by
      rw [h_col_eq]; exact hcorr_bs
    have hmore := peek_some_has_more hpeek
    dsimp only [] at hproc
    split at hproc <;> (first
      | (obtain ⟨-, rfl⟩ := hproc; try subst_vars
         have ha := advance_non_newline_corr sc_bs _ rest_tail hcorr_sc hmore (by decide) (by decide)
         rw [h_col_eq] at ha
         exact ⟨⟨rest_tail, col + 2⟩,
                SNbDoubleChar.escape _ rest_tail col (by decide),
                ha⟩)
      | skip)
    · -- 'x': hex escape (n=2)
      try subst_vars
      have ha := advance_non_newline_corr sc_bs 'x' rest_tail hcorr_sc hmore (by decide) (by decide)
      rw [h_col_eq] at ha
      obtain ⟨consumed, rest_hex, hchars_hex, hlen_c, hhex_all, hcorr_hex⟩ :=
        parseHexEscape_prod sc_bs.advance rest_tail (col + 2) 2 ha hproc
      obtain ⟨h1, tl1, rfl, htl1⟩ := list_eq_cons hlen_c
      obtain ⟨h2, tl2, rfl, htl2⟩ := list_eq_cons htl1
      cases tl2 with | cons => simp at htl2 | nil =>
      simp only [List.cons_append, List.nil_append] at hchars_hex
      subst hchars_hex
      exact ⟨⟨rest_hex, col + 4⟩,
             SNbDoubleChar.hexEscape2 rest_hex col h1 h2
               (hhex_all h1 (by simp)) (hhex_all h2 (by simp)),
             hcorr_hex⟩
    · -- 'u': hex escape (n=4)
      try subst_vars
      have ha := advance_non_newline_corr sc_bs 'u' rest_tail hcorr_sc hmore (by decide) (by decide)
      rw [h_col_eq] at ha
      obtain ⟨consumed, rest_hex, hchars_hex, hlen_c, hhex_all, hcorr_hex⟩ :=
        parseHexEscape_prod sc_bs.advance rest_tail (col + 2) 4 ha hproc
      obtain ⟨h1, tl4, rfl, htl4⟩ := list_eq_cons hlen_c
      obtain ⟨h2, tl3, rfl, htl3⟩ := list_eq_cons htl4
      obtain ⟨h3, tl2, rfl, htl2⟩ := list_eq_cons htl3
      obtain ⟨h4, tl1, rfl, htl1⟩ := list_eq_cons htl2
      cases tl1 with | cons => simp at htl1 | nil =>
      simp only [List.cons_append, List.nil_append] at hchars_hex
      subst hchars_hex
      exact ⟨⟨rest_hex, col + 6⟩,
             SNbDoubleChar.hexEscape4 rest_hex col h1 h2 h3 h4
               (hhex_all h1 (by simp)) (hhex_all h2 (by simp))
               (hhex_all h3 (by simp)) (hhex_all h4 (by simp)),
             hcorr_hex⟩
    · -- 'U': hex escape (n=8)
      try subst_vars
      have ha := advance_non_newline_corr sc_bs 'U' rest_tail hcorr_sc hmore (by decide) (by decide)
      rw [h_col_eq] at ha
      obtain ⟨consumed, rest_hex, hchars_hex, hlen_c, hhex_all, hcorr_hex⟩ :=
        parseHexEscape_prod sc_bs.advance rest_tail (col + 2) 8 ha hproc
      obtain ⟨h1, tl8, rfl, htl8⟩ := list_eq_cons hlen_c
      obtain ⟨h2, tl7, rfl, htl7⟩ := list_eq_cons htl8
      obtain ⟨h3, tl6, rfl, htl6⟩ := list_eq_cons htl7
      obtain ⟨h4, tl5, rfl, htl5⟩ := list_eq_cons htl6
      obtain ⟨h5, tl4, rfl, htl4⟩ := list_eq_cons htl5
      obtain ⟨h6, tl3, rfl, htl3⟩ := list_eq_cons htl4
      obtain ⟨h7, tl2, rfl, htl2⟩ := list_eq_cons htl3
      obtain ⟨h8, tl1, rfl, htl1⟩ := list_eq_cons htl2
      cases tl1 with | cons => simp at htl1 | nil =>
      simp only [List.cons_append, List.nil_append] at hchars_hex
      subst hchars_hex
      exact ⟨⟨rest_hex, col + 10⟩,
             SNbDoubleChar.hexEscape8 rest_hex col h1 h2 h3 h4 h5 h6 h7 h8
               (hhex_all h1 (by simp)) (hhex_all h2 (by simp))
               (hhex_all h3 (by simp)) (hhex_all h4 (by simp))
               (hhex_all h5 (by simp)) (hhex_all h6 (by simp))
               (hhex_all h7 (by simp)) (hhex_all h8 (by simp)),
             hcorr_hex⟩
    · simp at hproc

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
               (peek_some_has_more hpeek) (by decide) (by decide)⟩
    · -- peek? = some '\\': escape sequence
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv :=
        advance_non_newline_corr sc '\\' rest hcorr
          (peek_some_has_more hpeek) (by decide) (by decide)
      dsimp only [] at hok
      split at hok
      · -- next peek = some c2
        rename_i c2 hpeek2
        split at hok
        · -- isLineBreakBool c2: escaped newline → multiline break
          rename_i hlb2
          obtain ⟨sp_cn, h_break_nl, hcorr_cn⟩ :=
            consumeNewline_sbreak_corr sc.advance ⟨rest, sc.col + 1⟩ c2 hcorr_adv hpeek2 hlb2
          obtain ⟨sp_ws, h_gstar_ws, hcorr_ws⟩ :=
            skipWhitespace_corr (consumeNewline sc.advance) sp_cn hcorr_cn
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
            ih _ sp_ws content hcorr_ws hok
          -- Build SSDoubleEscaped: no leading ws, backslash, linebreak, no empty lines, flow prefix
          have h_gopt := gstar_sswhite_to_gopt_sep h_gstar_ws
          have h_flp : SFlowLinePrefix 0 sp_cn sp_ws :=
            SFlowLinePrefix.mk 0 sp_cn sp_cn sp_ws (SIndent.zero sp_cn) h_gopt
          have h_escaped : SSDoubleEscaped 0 ⟨'\\' :: rest, sc.col⟩ sp_ws :=
            SSDoubleEscaped.mk 0
              ⟨'\\' :: rest, sc.col⟩ ⟨'\\' :: rest, sc.col⟩
              ⟨rest, sc.col + 1⟩ sp_cn sp_cn sp_ws
              (GStar.nil _) (GLit.mk rest sc.col) h_break_nl
              (GStar.nil sp_cn) h_flp
          exact ⟨sp_body, sp_close,
                 SNbDoubleMultiLine.multi 0
                   ⟨'\\' :: rest, sc.col⟩ ⟨'\\' :: rest, sc.col⟩
                   sp_ws ⟨[], 0⟩ sp_body
                   (GStar.nil _)
                   (SSDoubleBreak.escaped 0 _ _ h_escaped)
                   h_body,
                 h_glit, h_corr⟩
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
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)  -- fold error
        · rename_i fold_result hfold
          obtain ⟨sp_cn, sp_loop, sp_fold, h_sbreak, h_gstar_empty, h_flp, hcorr_fold⟩ :=
            foldQuotedNewlines_prod sc ⟨c :: rest, sc.col⟩ c hcorr hpeek hlb hfold
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
                         (GStar.nil _)
                         (SSDoubleBreak.flowFold 0 _ sp_cn sp_loop _
                           h_sbreak h_gstar_empty h_flp)
                         h_body,
                       h_glit, h_corr⟩
      · -- not line break: control char check
        split at hok
        · simp at hok  -- invalid control char → error
        · -- valid char: advance + recurse
          rename_i hne_lb hne_ctrl
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
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
    advance_non_newline_corr sc '"' rest hcorr hmore (by decide) (by decide)
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

/-! ## §4 Single-Quoted Scalar -/

-- Prepend a `SNbSingleChar` to the first line of `SNbSingleMultiLine`
theorem SNbSingleMultiLine_prepend (s s₁ s_end : SurfPos)
    (hchar : SNbSingleChar s s₁)
    (hrest : SNbSingleMultiLine 0 s₁ s_end) :
    SNbSingleMultiLine 0 s s_end := by
  cases hrest with
  | single _ _ hline =>
    exact SNbSingleMultiLine.single 0 s s_end
      (GStar.cons s s₁ s_end hchar hline)
  | multi _ s₁' s₂ s₃ s₄ _ hline hbreak hgstar hflp hcont =>
    exact SNbSingleMultiLine.multi 0 s s₁' s₂ s₃ s₄ s_end
      (GStar.cons s s₁ s₁' hchar hline) hbreak hgstar hflp hcont

-- `collectSingleQuotedLoop` success produces:
-- 1. Body: `SNbSingleMultiLine 0` from current position to before closing `'`
-- 2. Close: `GLit '\'' ` consuming the closing `'`
-- 3. `ScannerSurfCorr` preserved after closing `'`
theorem collectSingleQuotedLoop_prod (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : collectSingleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s')) :
    ∃ sp_body sp_close,
      SNbSingleMultiLine 0 sp sp_body ∧
      GLit '\'' sp_body sp_close ∧
      ScannerSurfCorr s' sp_close := by
  induction fuel generalizing sc sp content with
  | zero => simp [collectSingleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)  -- none → error
    · -- peek? = some '\'': could be closing quote or escaped ''
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      dsimp only [] at hok
      split at hok
      · -- next peek = some '\'': escaped quote ''
        rename_i hpeek2
        have hcorr_adv :=
          advance_non_newline_corr sc '\'' rest hcorr hmore (by decide) (by decide)
        obtain ⟨rest2, hsp_adv⟩ := peek_some_sp hcorr_adv hpeek2
        injection hsp_adv with h_rest2 h_col2
        subst h_rest2
        -- h_col2 : sc.col + 1 = sc.advance.col
        rw [h_col2] at hcorr_adv
        have hmore2 := peek_some_has_more hpeek2
        have hcorr_adv2 :=
          advance_non_newline_corr sc.advance '\'' rest2 hcorr_adv hmore2 (by decide) (by decide)
        rw [show sc.advance.col + 1 = sc.col + 2 from by omega] at hcorr_adv2
        obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
          ih sc.advance.advance ⟨rest2, sc.col + 2⟩ _ hcorr_adv2 hok
        have h_esc : SNbSingleChar ⟨'\'' :: '\'' :: rest2, sc.col⟩ ⟨rest2, sc.col + 2⟩ :=
          SNbSingleChar.escapedQuote rest2 sc.col
        exact ⟨sp_body, sp_close,
               SNbSingleMultiLine_prepend _ _ _ h_esc h_body,
               h_glit, h_corr⟩
      · -- closing quote (next peek ≠ '\'')
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        exact ⟨⟨'\'' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
               SNbSingleMultiLine.single 0 _ _ (GStar.nil _),
               GLit.mk rest sc.col,
               advance_non_newline_corr sc '\'' rest hcorr hmore (by decide) (by decide)⟩
    · -- peek? = some c (not '\'')
      rename_i c hne_sq hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      split at hok
      · -- isLineBreakBool c: fold newlines → SNbSingleMultiLine.multi
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)  -- fold error
        · rename_i fold_result hfold
          obtain ⟨sp_cn, sp_loop, sp_fold, h_sbreak, h_gstar_empty, h_flp, hcorr_fold⟩ :=
            foldQuotedNewlines_prod sc ⟨c :: rest, sc.col⟩ c hcorr hpeek hlb hfold
          split at hok  -- doc marker guard
          · simp at hok
          · split at hok  -- underIndented guard
            · simp at hok
            · split at hok  -- do-notation residue
              · simp at hok
              · obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
                  ih _ sp_fold _ hcorr_fold hok
                exact ⟨sp_body, sp_close,
                       SNbSingleMultiLine.multi 0
                         ⟨c :: rest, sc.col⟩ ⟨c :: rest, sc.col⟩
                         sp_cn sp_loop sp_fold _
                         (GStar.nil _)
                         h_sbreak h_gstar_empty h_flp
                         h_body,
                       h_glit, h_corr⟩
      · split at hok
        · simp at hok  -- invalid control char → error
        · -- valid char: advance + recurse
          rename_i hne_lb hne_ctrl
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
            ih sc.advance ⟨rest, sc.col + 1⟩ _ hcorr_adv hok
          have h_sq_char : SNbSingleChar ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
            SNbSingleChar.plain c rest sc.col
              (not_lineBreak_bool_to_prop hne_lb) hne_sq
          exact ⟨sp_body, sp_close,
                 SNbSingleMultiLine_prepend _ _ _ h_sq_char h_body,
                 h_glit, h_corr⟩

-- `scanSingleQuoted` success produces a complete `SCSingleQuoted 0 .blockIn`.
-- Precondition: `sc.peek? = some '\''` (from scanner dispatch).
theorem scanSingleQuoted_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_sq : sc.peek? = some '\'')
    (hok : scanSingleQuoted sc = .ok s') :
    ∃ sp', SCSingleQuoted 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  -- Extract opening quote position
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek_sq
  subst hsp_eq
  have hmore := peek_some_has_more hpeek_sq
  have hcorr_adv :=
    advance_non_newline_corr sc '\'' rest hcorr hmore (by decide) (by decide)
  -- Loop: collectSingleQuotedLoop
  split at hok
  · simp at hok  -- loop error
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    obtain ⟨sp_body, sp_close, h_body, h_glit_close, hcorr_close⟩ :=
      collectSingleQuotedLoop_prod sc.advance ⟨rest, sc.col + 1⟩ "" _ _ _ _ _
        hcorr_adv hloop
    -- SNbSingleText 0 .blockIn = SNbSingleMultiLine 0
    have h_text : SNbSingleText 0 .blockIn ⟨rest, sc.col + 1⟩ sp_body := h_body
    -- validateTrailingContent: do-notation bind on Except Unit
    split at hok  -- if !sc.inFlow
    · -- !inFlow = true: validate
      split at hok  -- match on validateTrailingContent result
      · simp at hok  -- validation error
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close,
               SCSingleQuoted.mk 0 .blockIn _ _ _ _
                 (GLit.mk rest sc.col) h_text h_glit_close,
               corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_close)⟩
    · -- !inFlow = false: no validate
      split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close,
               SCSingleQuoted.mk 0 .blockIn _ _ _ _
                 (GLit.mk rest sc.col) h_text h_glit_close,
               corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_close)⟩

/-! ## §5 Plain-safe bridge (Layer 4a)

  Connect scanner's `isPlainSafeBool c inFlow` to the surface grammar's
  `isNsPlainSafe ctx ch`. The Bool predicate decomposes as
  `¬WS ∧ ¬LB [∧ ¬flow]`; the surface predicate uses `isNsChar = ¬LB ∧ ¬WS`
  (flipped conjunction), plus `¬flow` for flow contexts. -/

-- Bool → Prop for block context: `isPlainSafeBool c false ↔ isNsChar c`.
theorem isPlainSafe_block_to_nsChar {c : Char}
    (h : isPlainSafeBool c false = true) : isNsChar c := by
  have hp := (isPlainSafe_iff c false).mp h
  simp only [isPlainSafeProp] at hp
  exact ⟨hp.2, hp.1⟩

-- Bool → surface Prop for blockIn: `isPlainSafeBool c false → isNsPlainSafe .blockIn c`.
theorem isPlainSafe_to_nsPlainSafe_blockIn {c : Char}
    (h : isPlainSafeBool c false = true) : isNsPlainSafe .blockIn c :=
  isPlainSafe_block_to_nsChar h

-- Bool → surface Prop for blockOut: same as blockIn.
theorem isPlainSafe_to_nsPlainSafe_blockOut {c : Char}
    (h : isPlainSafeBool c false = true) : isNsPlainSafe .blockOut c :=
  isPlainSafe_block_to_nsChar h

-- Bool → surface Prop for flowIn: adds flow indicator exclusion.
theorem isPlainSafe_to_nsPlainSafe_flowIn {c : Char}
    (h : isPlainSafeBool c true = true) : isNsPlainSafe .flowIn c := by
  have hp := (isPlainSafe_iff c true).mp h
  simp only [isPlainSafeProp] at hp
  exact ⟨⟨hp.2.1, hp.1⟩, hp.2.2⟩

-- isPlainSafeBool c inFlow → c is not a linebreak (useful for advance proofs).
theorem isPlainSafe_not_linebreak {c : Char} {inFlow : Bool}
    (h : isPlainSafeBool c inFlow = true) : ¬isLineBreakProp c := by
  have hp := (isPlainSafe_iff c inFlow).mp h
  cases inFlow
  · -- false (block): hp : ¬isWhiteSpaceProp c ∧ ¬isLineBreakProp c
    simp only [isPlainSafeProp] at hp; exact hp.2
  · -- true (flow): hp : ¬isWhiteSpaceProp c ∧ ¬isLineBreakProp c ∧ ¬isFlowIndicatorProp c
    simp only [isPlainSafeProp] at hp; exact hp.2.1

-- isPlainSafeBool c inFlow → c ≠ '\n' ∧ c ≠ '\r' (for advance_non_newline_corr).
theorem isPlainSafe_not_newline {c : Char} {inFlow : Bool}
    (h : isPlainSafeBool c inFlow = true) : c ≠ '\n' ∧ c ≠ '\r' := by
  have hlb := isPlainSafe_not_linebreak h
  constructor
  · intro heq; subst heq; exact hlb (by unfold isLineBreakProp; left; native_decide)
  · intro heq; subst heq; exact hlb (by unfold isLineBreakProp; right; native_decide)

/-! ## §6 Block header loop production (Layer 4a)

  `parseBlockHeaderLoop` reads 0–2 header indicator characters (`-`/`+`/digit),
  each of which satisfies `isBlockScalarHeaderChar`. This produces
  `GStar (GChar (fun c => isBlockScalarHeaderChar c = true))`. -/

-- Header chars are not newlines: used for advance_non_newline_corr.
theorem blockHeaderChar_not_newline {c : Char}
    (h : Grammar.isBlockScalarHeaderChar c = true) : c ≠ '\n' ∧ c ≠ '\r' := by
  constructor
  · intro heq; subst heq; simp [Grammar.isBlockScalarHeaderChar] at h
  · intro heq; subst heq; simp [Grammar.isBlockScalarHeaderChar] at h

-- isDigit && != '0' → isBlockScalarHeaderChar (digit 1-9 is a header char).
theorem isDigitNotZero_isBlockHeaderChar {c : Char}
    (h : (c.isDigit && (c != '0')) = true) :
    Grammar.isBlockScalarHeaderChar c = true := by
  have ⟨hdig, hne⟩ := Bool.and_eq_true_iff.mp h
  have hne' : c ≠ '0' := by intro heq; subst heq; simp at hne
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hdig
  simp only [Grammar.isBlockScalarHeaderChar, Bool.or_eq_true, beq_iff_eq,
             Bool.and_eq_true, decide_eq_true_eq]
  right
  refine ⟨?_, hdig.2⟩
  -- '1' ≤ c from '0' ≤ c and c ≠ '0': reduce to Nat via UInt32.toNat
  simp only [Char.le_def, UInt32.le_iff_toNat_le] at hdig ⊢
  have h0_val : ('0' : Char).val.toNat = 48 := by native_decide
  have h1_val : ('1' : Char).val.toNat = 49 := by native_decide
  rw [h0_val] at hdig; rw [h1_val]
  have h2' : c.val.toNat ≠ 48 := by
    intro heq; apply hne'
    exact Char.ext (UInt32.toNat_inj.mp (by omega))
  omega

-- `parseBlockHeaderLoop` produces `GStar (GChar isBlockScalarHeaderChar)`.
theorem parseBlockHeaderLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (chomp : ChompStyle)
    (explicitOffset : Option Nat) (fuel : Nat) :
    let (_, _, sc') := parseBlockHeaderLoop sc chomp explicitOffset fuel
    ∃ sp', GStar (GChar (fun c => Grammar.isBlockScalarHeaderChar c = true)) sp sp' ∧
           ScannerSurfCorr sc' sp' := by
  induction fuel generalizing sc sp chomp explicitOffset with
  | zero =>
    simp only [parseBlockHeaderLoop]
    exact ⟨sp, GStar.nil sp, hcorr⟩
  | succ fuel' ih =>
    simp only [parseBlockHeaderLoop]
    split
    · -- peek? = some '-'
      rename_i hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      have hcorr_adv := advance_non_newline_corr sc '-' rest hcorr
        hmore (by decide) (by decide)
      obtain ⟨sp', h_tail, hcorr'⟩ :=
        ih sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv .strip explicitOffset
      exact ⟨sp',
             GStar.cons _ ⟨rest, sc.col + 1⟩ _
               (GChar.mk '-' rest sc.col (by native_decide)) h_tail,
             hcorr'⟩
    · -- peek? = some '+'
      rename_i hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      have hcorr_adv := advance_non_newline_corr sc '+' rest hcorr
        hmore (by decide) (by decide)
      obtain ⟨sp', h_tail, hcorr'⟩ :=
        ih sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv .keep explicitOffset
      exact ⟨sp',
             GStar.cons _ ⟨rest, sc.col + 1⟩ _
               (GChar.mk '+' rest sc.col (by native_decide)) h_tail,
             hcorr'⟩
    · -- peek? = some c (potentially digit)
      rename_i c hpeek_ne_minus hpeek_ne_plus hpeek
      split
      · -- isDigit c ∧ c ≠ '0': header char
        rename_i hdigit
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have hHdr := isDigitNotZero_isBlockHeaderChar hdigit
        have ⟨hne_nl, hne_cr⟩ := blockHeaderChar_not_newline hHdr
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          hmore hne_nl hne_cr
        obtain ⟨sp', h_tail, hcorr'⟩ :=
          ih sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv chomp (some (c.toNat - '0'.toNat))
        exact ⟨sp',
               GStar.cons _ ⟨rest, sc.col + 1⟩ _
                 (GChar.mk c rest sc.col hHdr) h_tail,
               hcorr'⟩
      · -- not a header char: stop
        exact ⟨sp, GStar.nil sp, hcorr⟩
    · -- peek? = none: stop
      exact ⟨sp, GStar.nil sp, hcorr⟩

/-! ## §6b Sub-function Grammar Productions

  Helper `_prod` theorems for sub-functions used by block and plain scalar loops.
  These construct grammar witnesses for `consumeExactSpaces`, `collectLineContentLoop`,
  and `consumeNewline`. -/

-- Helper: when peek? = some ' ', first component of consumeExactSpaces (n+1)
--   = first component of consumeExactSpaces sc.advance n + 1
theorem consumeExactSpaces_succ_space_fst (sc : ScannerState) (n : Nat)
    (hpeek : sc.peek? = some ' ') :
    (consumeExactSpaces sc (n + 1)).1 = (consumeExactSpaces sc.advance n).1 + 1 := by
  -- generalize the recursive call BEFORE unfolding to keep both sides in sync
  generalize h : consumeExactSpaces sc.advance n = p
  unfold consumeExactSpaces; split
  · rw [h]
  · contradiction

-- Helper: when peek? = some ' ', second component of consumeExactSpaces (n+1)
--   = second component of consumeExactSpaces sc.advance n
theorem consumeExactSpaces_succ_space_snd (sc : ScannerState) (n : Nat)
    (hpeek : sc.peek? = some ' ') :
    (consumeExactSpaces sc (n + 1)).2 = (consumeExactSpaces sc.advance n).2 := by
  generalize h : consumeExactSpaces sc.advance n = p
  unfold consumeExactSpaces; split
  · rw [h]
  · contradiction

-- Helper: when peek? ≠ some ' ', consumeExactSpaces (n+1) returns (0, sc)
theorem consumeExactSpaces_succ_not_space (sc : ScannerState) (n : Nat)
    (hpeek : sc.peek? ≠ some ' ') :
    consumeExactSpaces sc (n + 1) = (0, sc) := by
  unfold consumeExactSpaces; split
  · exact absurd ‹_› hpeek
  · rfl

-- `consumeExactSpaces` returns at most `count` spaces.
theorem consumeExactSpaces_fst_le (sc : ScannerState) (count : Nat) :
    (consumeExactSpaces sc count).1 ≤ count := by
  induction count generalizing sc with
  | zero => simp [consumeExactSpaces]
  | succ n ih =>
    by_cases hpeek : sc.peek? = some ' '
    · rw [consumeExactSpaces_succ_space_fst sc n hpeek]
      have := ih sc.advance; omega
    · rw [consumeExactSpaces_succ_not_space sc n hpeek]; simp

-- `consumeExactSpaces` produces `SIndent` for however many spaces were actually consumed.
theorem consumeExactSpaces_sindent_partial (sc : ScannerState) (sp : SurfPos)
    (count : Nat) (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', SIndent (consumeExactSpaces sc count).1 sp sp' ∧
           ScannerSurfCorr (consumeExactSpaces sc count).2 sp' := by
  induction count generalizing sc sp with
  | zero =>
    simp [consumeExactSpaces]; exact ⟨sp, SIndent.zero sp, hcorr⟩
  | succ n ih =>
    by_cases hpeek : sc.peek? = some ' '
    · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      have hcorr_adv := advance_non_newline_corr sc ' ' rest hcorr hmore (by decide) (by decide)
      rw [show (consumeExactSpaces sc (n + 1)).2 = (consumeExactSpaces sc.advance n).2
        from consumeExactSpaces_succ_space_snd sc n hpeek]
      rw [consumeExactSpaces_succ_space_fst sc n hpeek]
      obtain ⟨sp', h_indent, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv
      exact ⟨sp', SIndent.succ _ rest sc.col sp' h_indent, hcorr'⟩
    · -- Not a space: consumed = 0
      rw [consumeExactSpaces_succ_not_space sc n hpeek]
      exact ⟨sp, SIndent.zero sp, hcorr⟩

-- `consumeExactSpaces` with full count consumed produces `SIndent count`.
theorem consumeExactSpaces_sindent_prod (sc : ScannerState) (sp : SurfPos)
    (count : Nat) (hcorr : ScannerSurfCorr sc sp)
    (hfull : (consumeExactSpaces sc count).1 = count) :
    ∃ sp', SIndent count sp sp' ∧ ScannerSurfCorr (consumeExactSpaces sc count).2 sp' := by
  induction count generalizing sc sp with
  | zero =>
    simp [consumeExactSpaces]; exact ⟨sp, SIndent.zero sp, hcorr⟩
  | succ n ih =>
    -- peek? must be some ' ', otherwise .1 = 0 ≠ n+1
    by_cases hpeek : sc.peek? = some ' '
    · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      have hcorr_adv := advance_non_newline_corr sc ' ' rest hcorr hmore (by decide) (by decide)
      have hfull' : (consumeExactSpaces sc.advance n).1 = n := by
        have := consumeExactSpaces_succ_space_fst sc n hpeek
        omega
      rw [show (consumeExactSpaces sc (n + 1)).2 = (consumeExactSpaces sc.advance n).2
        from consumeExactSpaces_succ_space_snd sc n hpeek]
      obtain ⟨sp', h_indent, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv hfull'
      exact ⟨sp', SIndent.succ n rest sc.col sp' h_indent, hcorr'⟩
    · -- peek? ≠ some ' ': consumeExactSpaces returns (0, sc), but hfull says 0 = n+1
      rw [consumeExactSpaces_succ_not_space sc n hpeek] at hfull; omega

-- `collectLineContentLoop` produces `GStar SNbChar` + correspondence.
-- Each consumed character is non-break (since the loop stops at breaks).
theorem collectLineContentLoop_nbchar_prod (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat) (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', GStar SNbChar sp sp' ∧
           ScannerSurfCorr (collectLineContentLoop sc content fuel).2 sp' := by
  induction fuel generalizing sc sp content with
  | zero =>
    simp [collectLineContentLoop]; exact ⟨sp, GStar.nil sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · -- peek? = some c
      rename_i c hpeek
      split
      · -- isLineBreakBool c: stop
        exact ⟨sp, GStar.nil sp, hcorr⟩
      · -- not break: consume + recurse
        rename_i hne_lb
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have h_not_nl := not_isLineBreak_not_newline c hne_lb
        have h_not_cr := not_isLineBreak_not_cr c hne_lb
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
        obtain ⟨sp', h_tail, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ _ hcorr_adv
        exact ⟨sp',
               GStar.cons _ ⟨rest, sc.col + 1⟩ _
                 (not_isLineBreak_gives_SNbChar c rest sc.col hne_lb) h_tail,
               hcorr'⟩
    · -- peek? = none: stop
      exact ⟨sp, GStar.nil sp, hcorr⟩

-- GStar → GPlus conversion when at least one element exists (from known first char).
theorem gstar_to_gplus_from_first {P : SurfPos → SurfPos → Prop}
    {sp sp₁ sp' : SurfPos}
    (h_first : P sp sp₁) (h_rest : GStar P sp₁ sp') :
    GPlus P sp sp' := GPlus.mk sp sp₁ sp' h_first h_rest

-- When collectLineContentLoop is called with peek? = some c (not break),
-- the first char WILL be consumed, giving GPlus SNbChar.
theorem collectLineContentLoop_gplus_prod (sc : ScannerState) (sp : SurfPos)
    (c : Char) (content : String) (fuel : Nat)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some c)
    (hne_lb : ¬isLineBreakBool c = true) (hfuel : fuel ≥ 1) :
    ∃ sp', GPlus SNbChar sp sp' ∧
           ScannerSurfCorr (collectLineContentLoop sc content fuel).2 sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  have h_not_nl := not_isLineBreak_not_newline c hne_lb
  have h_not_cr := not_isLineBreak_not_cr c hne_lb
  have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
  -- With fuel ≥ 1, unfold one step: the first char is consumed
  match fuel, hfuel with
  | fuel' + 1, _ =>
    simp only [collectLineContentLoop]
    rw [hpeek]
    simp only [hne_lb]
    obtain ⟨sp', h_tail, hcorr'⟩ :=
      collectLineContentLoop_nbchar_prod sc.advance ⟨rest, sc.col + 1⟩ _ fuel' hcorr_adv
    have h_first := not_isLineBreak_gives_SNbChar c rest sc.col hne_lb
    exact ⟨sp', gstar_to_gplus_from_first h_first h_tail, hcorr'⟩

/-! ## §7 Plain Scalar Production (Layer 4b)

  `scanPlainScalar` produces `SNsPlain 0 .blockIn` (= `SNsPlainMultiLine 0 .blockIn`).

  Grammar bridge:
  - First char: `canStartPlainScalarBool` → `SNsPlainFirst .blockIn`
    (`safe` for regular chars, `dashSafe`/`colonSafe`/`questionSafe` for `-`/`:`/`?`)
  - Continuation chars: `isPlainSafeBool` → `SNsPlainChar .blockIn` via §5 bridge
  - Intra-line whitespace: accumulated `spaces` → `GStar SSWhite`
    (combined with next char into `SNbNsPlainInLineEntry`)
  - Multi-line: `handleBlockLineBreak` → `SSNsPlainNextLine` (line fold + indent + continuation)
  - Trailing whitespace: scanner past trailing WS not in grammar; bridge via `GStar SSWhite`

  Status: grammar witness sorry — correlation from `scanPlainScalar_corr`.
  Helper theorems ready for future grammar proof:
  - `isPlainSafe_to_plainChar_basic`: basic char → `SNsPlainChar`
  - `isPlainSafe_to_inlineEntry_basic`: basic char → `SNbNsPlainInLineEntry`
  - First char `SNsPlainFirst` extraction from `canStartPlainScalarBool`
  - `handleBlockLineBreak_prod`: multi-line `SSNsPlainNextLine` construction -/

-- Bridge: `isPlainSafeBool c false` + not-colon + not-hash → `SNsPlainChar .blockIn`.
-- (`:` needs next char safe via `colonSafe` constructor; `#` needs col > 0 via `hashAfterNs`.)
theorem isPlainSafe_to_plainChar_basic (c : Char) (rest : List Char) (col : Nat)
    (hSafe : isPlainSafeBool c false = true)
    (hNotColon : c ≠ ':') (hNotHash : c ≠ '#') :
    SNsPlainChar .blockIn ⟨c :: rest, col⟩ ⟨rest, col + 1⟩ :=
  SNsPlainChar.safe .blockIn c rest col
    (isPlainSafe_to_nsPlainSafe_blockIn hSafe) hNotColon hNotHash

-- Bridge: `isPlainSafeBool c false` + not-colon + not-hash →
-- `SNbNsPlainInLineEntry .blockIn` with empty whitespace prefix.
theorem isPlainSafe_to_inlineEntry_basic (c : Char) (rest : List Char) (col : Nat)
    (hSafe : isPlainSafeBool c false = true)
    (hNotColon : c ≠ ':') (hNotHash : c ≠ '#') :
    SNbNsPlainInLineEntry .blockIn ⟨c :: rest, col⟩ ⟨rest, col + 1⟩ :=
  SNbNsPlainInLineEntry.mk .blockIn ⟨c :: rest, col⟩ ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
    (GStar.nil _)
    (isPlainSafe_to_plainChar_basic c rest col hSafe hNotColon hNotHash)

-- `scanPlainScalar` produces `SNsPlain 0 .blockIn` and preserves correspondence.
-- Correlation: fully proven (delegated to `scanPlainScalar_corr`).
-- Grammar: requires decomposing the loop into first char (`SNsPlainFirst`) +
-- intra-line entries (`GStar SNbNsPlainInLineEntry`) + continuation lines
-- (`GStar SSNsPlainNextLine`). The helpers `isPlainSafe_to_plainChar_basic` and
-- `isPlainSafe_to_inlineEntry_basic` are ready for the basic-char case;
-- remaining: first-char extraction, `:` colonSafe, `#` hashAfterNs, multi-line.
theorem scanPlainScalar_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp', SNsPlain 0 .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨sp', hcorr'⟩ := scanPlainScalar_corr sc sp hcorr hok
  exact ⟨sp', sorry, hcorr'⟩

/-! ## §8 Block Scalar Production (Layer 4b)

  `scanBlockScalar` produces `SCLLiteral 0` (for `|`) or `SCLFolded 0` (for `>`),
  and preserves correspondence.

  Pipeline structure (each step has proven `_corr` and most have `_prod`):
  1. Advance past `|`/`>` → `GLit` delimiter
  2. `parseBlockHeaderLoop` → `GStar (GChar isBlockScalarHeaderChar)` (proven §6)
  3. `skipWhitespace` + `scanBlockScalarSkipComment` → whitespace + optional comment text
  4. `scanBlockScalarConsumeNewline` → line break
  5. Steps 2–4 combined → `SCBBlockHeader`
  6. `scanBlockScalarBody` → `SLLiteralContent`/`GOpt SLNbFoldedLines` content

  §8b adds sub-function _prod theorems for content body.
  §8c composes header + body into complete `SCLLiteral`/`SCLFolded`. -/

-- `scanBlockScalarSkipComment` produces `GOpt SCNbCommentText`.
-- Mirrors `skipToContentComment_corr` structure.
theorem scanBlockScalarSkipComment_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', GOpt SCNbCommentText sp sp' ∧
           ScannerSurfCorr (scanBlockScalarSkipComment sc) sp' := by
  unfold scanBlockScalarSkipComment
  split
  · -- peek? = some '#'
    rename_i hpeek
    dsimp only []
    split
    · -- peekBack? = some c
      split
      · -- commentOk = true: consume # + text
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have hcorr_adv := advance_non_newline_corr sc '#' rest hcorr
          hmore (by decide) (by decide)
        obtain ⟨sp', hstar, hcorr'⟩ :=
          collectCommentTextLoop_corr sc.advance ⟨rest, sc.col + 1⟩ ""
            (sc.advance.inputEnd - sc.advance.offset) hcorr_adv (Nat.le_refl _)
        exact ⟨sp', GOpt.some _ _ (SCNbCommentText.mk rest sc.col sp' hstar),
               corr_of_comments_update _ hcorr'⟩
      · -- commentOk = false
        exact ⟨sp, GOpt.none sp, hcorr⟩
    · -- peekBack? = none
      -- commentOk = false
      exact ⟨sp, GOpt.none sp, hcorr⟩
  · -- peek? ≠ some '#'
    exact ⟨sp, GOpt.none sp, hcorr⟩

-- `peek? = none` implies scanner is at/past end of input.
theorem peek_none_not_lt {sc : ScannerState}
    (hpeek : sc.peek? = none) : ¬ sc.offset < sc.inputEnd := by
  unfold ScannerState.peek? at hpeek
  split at hpeek
  · cases hpeek
  · assumption

-- `scanBlockScalarConsumeNewline` produces `SBComment`.
theorem scanBlockScalarConsumeNewline_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanBlockScalarConsumeNewline sc = .ok s') :
    ∃ sp', SBComment sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanBlockScalarConsumeNewline at hok
  split at hok
  · -- peek? = some c
    rename_i c hpeek
    split at hok
    · -- isLineBreakBool c: consumeNewline
      rename_i hlb
      have h := Except.ok.inj hok; subst h
      obtain ⟨sp', h_sbreak, hcorr'⟩ :=
        consumeNewline_sbreak_corr sc sp c hcorr hpeek hlb
      exact ⟨sp', SBComment.break sp sp' h_sbreak, hcorr'⟩
    · -- ¬isLineBreak
      split at hok
      · -- !hasMore: return sc unchanged
        -- peek? = some c implies hasMore, so !hasMore is contradictory
        have hmore := peek_some_has_more hpeek
        rename_i h_not_has
        simp only [ScannerState.hasMore, Bool.not_eq_eq_eq_not, Bool.not_true,
                    decide_eq_false_iff_not] at h_not_has
        omega
      · -- else: error
        simp at hok
  · -- peek? = none: EOF
    rename_i hpeek
    have h := Except.ok.inj hok; subst h
    have hchars := eof_corr sc sp hcorr (peek_none_not_lt hpeek)
    have hsp : sp = ⟨[], sc.col⟩ := by
      cases sp with | mk chars col =>
      simp only [SurfPos.mk.injEq] at hchars ⊢
      exact ⟨hchars, hcorr.col_eq⟩
    subst hsp
    exact ⟨⟨[], sc.col⟩, SBComment.eof sc.col, hcorr⟩

-- Combine: `GStar SSWhite` + `GOpt SCNbCommentText` + `SBComment` → `SSBComment`.
-- Fully proven for non-empty whitespace and empty-whitespace-no-comment.
-- The empty-whitespace-with-comment case is handled at the call site (absorbed
-- into the call site's existing sorry — unreachable from scanner).
theorem whitespace_comment_break_to_SSBComment_withWS
    (sp_hdr sp_first sp_ws sp_cmt sp_nl : SurfPos)
    (h_first : SSWhite sp_hdr sp_first) (h_rest : GStar SSWhite sp_first sp_ws)
    (h_cmt : GOpt SCNbCommentText sp_ws sp_cmt)
    (h_brk : SBComment sp_cmt sp_nl) :
    SSBComment sp_hdr sp_nl :=
  SSBComment.withSep sp_hdr sp_ws sp_cmt sp_nl
    (SSeparateInLine.whites sp_hdr sp_ws (GPlus.mk sp_hdr sp_first sp_ws h_first h_rest))
    h_cmt h_brk

/-! ## §8b Block Scalar Content Sub-function Productions

  Grammar witnesses for `collectBlockScalarLoop` and `scanBlockScalarBody`.
  These are the remaining pieces needed to close the `scanBlockScalar_prod` sorry. -/

-- Compose: text line + break + recursive SLLiteralContent → SLLiteralContent.
-- The first line becomes the head of the GSeq, and if the recursive content
-- has text lines they become SBNbLiteralNext entries in the GStar tail.
-- Prepend an `SLEmpty` to an `SLNbLiteralText`'s GStar prefix.
theorem prepend_empty_to_text_line {n : Nat}
    {sp sp_cn sp_end : SurfPos}
    (h_empty : SLEmpty n .blockIn sp sp_cn)
    (h_text : SLNbLiteralText n sp_cn sp_end) :
    SLNbLiteralText n sp sp_end := by
  match h_text with
  | .mk _ _ sp_after_empties _ h_empties h_indent_content =>
    exact SLNbLiteralText.mk n sp sp_after_empties sp_end
      (GStar.cons sp sp_cn sp_after_empties h_empty h_empties)
      h_indent_content

/-! ## §8c Block Scalar Composition

  Compose header (proven) + body to get complete `SCLLiteral`/`SCLFolded`.
  Header = advance past `|`/`>` + `parseBlockHeaderLoop_prod` + whitespace/comment/break.
  Body = `scanBlockScalarBody_corr` (correspondence only; grammar sorry).

  Helper theorems ready for future grammar proof:
  - `consumeExactSpaces_sindent_prod`: full indent → `SIndent n`
  - `consumeExactSpaces_sindent_partial`: partial indent → `SIndentLe n`
  - `collectLineContentLoop_gplus_prod`: content chars → `GPlus SNbChar`
  - `prepend_empty_to_text_line`: empty line + text line → `SLNbLiteralText`
  - `consumeNewline_sbreak_corr`: newline → `SBBreak` -/

-- Block scalar header chars are not whitespace, line-break, or BOM.
private theorem headerChar_notWsLbBom (c : Char)
    (h : Grammar.isBlockScalarHeaderChar c = true) : notWsLbBom c := by
  unfold notWsLbBom Grammar.isBlockScalarHeaderChar at *
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (rfl | rfl) | ⟨h1, h2⟩
  · exact ⟨by native_decide, by native_decide, by native_decide⟩
  · exact ⟨by native_decide, by native_decide, by native_decide⟩
  · simp only [isWhiteSpaceBool, isLineBreakBool, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> (intro heq; subst heq; simp at h1 h2 <;> omega)

-- `parseBlockHeaderLoop` preserves the property that `peekBack?` is not ws/lb/BOM.
theorem parseBlockHeaderLoop_preserves_peekBack_not_ws
    (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (chomp : ChompStyle) (off : Option Nat) (fuel : Nat)
    (h_pb : ∀ c, sc.peekBack? = some c → notWsLbBom c) :
    ∀ c, (parseBlockHeaderLoop sc chomp off fuel).2.2.peekBack? = some c → notWsLbBom c := by
  induction fuel generalizing sc sp chomp off with
  | zero => simp only [parseBlockHeaderLoop]; exact h_pb
  | succ fuel' ih =>
    simp only [parseBlockHeaderLoop]
    split
    · rename_i hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek; subst hsp_eq
      have hmore := peek_some_has_more hpeek
      exact ih sc.advance ⟨rest, sc.col + 1⟩
        (advance_non_newline_corr sc '-' rest hcorr hmore (by decide) (by decide))
        .strip off (fun c hc => by
          rw [advance_peekBack_eq_peek hcorr hmore (by decide) (by decide)] at hc
          cases hc; exact ⟨by decide, by decide, by decide⟩)
    · rename_i hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek; subst hsp_eq
      have hmore := peek_some_has_more hpeek
      exact ih sc.advance ⟨rest, sc.col + 1⟩
        (advance_non_newline_corr sc '+' rest hcorr hmore (by decide) (by decide))
        .keep off (fun c hc => by
          rw [advance_peekBack_eq_peek hcorr hmore (by decide) (by decide)] at hc
          cases hc; exact ⟨by decide, by decide, by decide⟩)
    · rename_i c_peek _ _ hpeek
      split
      · rename_i hdigit
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek; subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have hBlockHdr := isDigitNotZero_isBlockHeaderChar hdigit
        have ⟨hnl, hcr⟩ := blockHeaderChar_not_newline hBlockHdr
        exact ih sc.advance ⟨rest, sc.col + 1⟩
          (advance_non_newline_corr sc c_peek rest hcorr hmore hnl hcr) chomp
          (some (c_peek.toNat - '0'.toNat)) (fun c hc => by
            rw [advance_peekBack_eq_peek hcorr hmore hnl hcr] at hc
            cases hc; exact headerChar_notWsLbBom c_peek hBlockHdr)
      · exact h_pb
    · exact h_pb

-- `skipWhitespace` is identity when the SurfPos is unchanged across it.
private theorem skipWhitespace_eq_of_same_surfpos {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp)
    (hcorr' : ScannerSurfCorr (skipWhitespace sc) sp) :
    skipWhitespace sc = sc := by
  have h_off := ScannerSurfCorr_same_offset hcorr' hcorr (skipWhitespace_input sc)
  apply skipWhitespace_noop
  generalize hm : sc.peek? = p; cases p with
  | none => trivial
  | some c =>
    show isWhiteSpaceBool c = false
    cases hws : isWhiteSpaceBool c with
    | false => rfl
    | true =>
      exfalso
      have h_has := peek_some_hasMore sc c hm
      unfold skipWhitespace at h_off
      obtain ⟨fuel', hfuel_eq⟩ := Nat.exists_eq_succ_of_ne_zero
        (show sc.inputEnd - sc.offset ≠ 0 from by omega)
      rw [hfuel_eq] at h_off
      unfold skipWhitespaceLoop at h_off
      simp only [hm, hws, ↓reduceIte] at h_off
      have := skipWhitespaceLoop_offset_ge sc.advance fuel'
      have := advance_offset_lt sc h_has
      omega

-- `scanBlockScalarSkipComment` is identity when `peekBack?` returns a non-ws/lb/BOM char.
private theorem scanBlockScalarSkipComment_noop (sc : ScannerState)
    (h : ∀ c, sc.peekBack? = some c → notWsLbBom c) :
    scanBlockScalarSkipComment sc = sc := by
  unfold scanBlockScalarSkipComment
  split
  · dsimp only []
    split
    · rename_i c hpb
      have ⟨h1, h2, h3⟩ := h c hpb
      simp only [h1, h2, h3, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    · rfl
  · rfl

-- `SCNbCommentText sp sp` is impossible (column contradiction).
private theorem scNbCommentText_irrefl (sp : SurfPos) : ¬ SCNbCommentText sp sp := by
  intro h
  match h with
  | .mk rest col _ hstar =>
    have : col ≥ col + 1 := gstar_gchar_col_le hstar
    omega

-- Unreachability: `#` comment without preceding whitespace after block header.
private theorem scanBlockScalar_unreachable_comment_without_ws
    (sc : ScannerState) (sp_adv sp_hdr sp_cmt : SurfPos)
    (c₀ : Char) (rest : List Char)
    (hcorr : ScannerSurfCorr sc ⟨c₀ :: rest, sc.col⟩)
    (hmore : sc.offset < sc.inputEnd)
    (hnl : c₀ ≠ '\n') (hcr : c₀ ≠ '\r')
    (hc₀_not_ws : notWsLbBom c₀)
    (hcorr_adv : ScannerSurfCorr sc.advance sp_adv)
    (hcorr_hdr : ScannerSurfCorr (parseBlockHeaderLoop sc.advance .clip none 2).2.2 sp_hdr)
    (hcorr_ws : ScannerSurfCorr (skipWhitespace (parseBlockHeaderLoop sc.advance .clip none 2).2.2) sp_hdr)
    (hcorr_cmt : ScannerSurfCorr (scanBlockScalarSkipComment (skipWhitespace (parseBlockHeaderLoop sc.advance .clip none 2).2.2)) sp_cmt)
    (hcnt : SCNbCommentText sp_hdr sp_cmt)
    : False := by
  have h_pb_adv : sc.advance.peekBack? = some c₀ :=
    advance_peekBack_eq_peek hcorr hmore hnl hcr
  have hcorr_adv' := advance_non_newline_corr sc c₀ rest hcorr hmore hnl hcr
  have h_sp_adv : sp_adv = ⟨rest, sc.col + 1⟩ := ScannerSurfCorr_unique hcorr_adv hcorr_adv'
  subst h_sp_adv
  have h_pb_hdr : ∀ c, (parseBlockHeaderLoop sc.advance .clip none 2).2.2.peekBack? = some c → notWsLbBom c :=
    parseBlockHeaderLoop_preserves_peekBack_not_ws sc.advance ⟨rest, sc.col + 1⟩
      hcorr_adv' .clip none 2 (fun c hc => by rw [h_pb_adv] at hc; cases hc; exact hc₀_not_ws)
  have h_ws_eq := skipWhitespace_eq_of_same_surfpos hcorr_hdr hcorr_ws
  rw [h_ws_eq] at hcorr_cmt
  rw [scanBlockScalarSkipComment_noop _ h_pb_hdr] at hcorr_cmt
  have := ScannerSurfCorr_unique hcorr_hdr hcorr_cmt
  subst this
  exact scNbCommentText_irrefl sp_hdr hcnt

-- `scanBlockScalar` produces `SCLLiteral 0` or `SCLFolded 0` and preserves correspondence.
-- Header: FULLY PROVEN (delimiter + header chars + SSBComment).
-- Body grammar: sorry (composition of per-iteration fragments into SLLiteralContent).
-- Dispatch: FULLY PROVEN for literal (`|`), sorry for folded (`>`) content type conversion.
theorem scanBlockScalar_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hchar : sc.peek? = some '|' ∨ sc.peek? = some '>')
    (hok : scanBlockScalar sc = .ok s') :
    ∃ sp', (SCLLiteral 0 sp sp' ∨ SCLFolded 0 sp sp') ∧ ScannerSurfCorr s' sp' := by
  unfold scanBlockScalar at hok
  dsimp only [] at hok
  -- Step 1: advance past '|' or '>'
  -- Step 2: parseBlockHeaderLoop → GStar (GChar isBlockScalarHeaderChar)
  obtain ⟨sp_adv_gen, hcorr_adv⟩ := advance_corr sc sp hcorr
  obtain ⟨sp_hdr, h_hdr_chars, hcorr_hdr⟩ :=
    parseBlockHeaderLoop_prod sc.advance sp_adv_gen hcorr_adv .clip none 2
  -- Step 3: skipWhitespace → GStar SSWhite
  obtain ⟨sp_ws, h_ws, hcorr_ws⟩ :=
    skipWhitespace_corr (parseBlockHeaderLoop sc.advance .clip none 2).2.2 sp_hdr hcorr_hdr
  -- Step 3b: scanBlockScalarSkipComment → GOpt SCNbCommentText
  obtain ⟨sp_cmt, h_cmt, hcorr_cmt⟩ :=
    scanBlockScalarSkipComment_prod _ sp_ws hcorr_ws
  -- Step 4: match on scanBlockScalarConsumeNewline
  split at hok
  · simp at hok  -- error
  · rename_i s_after_nl hcn
    -- Step 4b: scanBlockScalarConsumeNewline → SBComment
    obtain ⟨sp_nl, h_brk, hcorr_nl⟩ :=
      scanBlockScalarConsumeNewline_prod _ sp_cmt hcorr_cmt hcn
    -- Step 5: compose header chars + WS + comment + break → SCBBlockHeader
    have h_ssbcomment : SSBComment sp_hdr sp_nl := by
      cases h_ws with
      | nil =>
        -- No whitespace: comment must be none (scanner: peekBack? not whitespace)
        match h_cmt with
        | .none _ => exact SSBComment.noSep sp_hdr sp_nl h_brk
        | .some _ _ hcnt =>
          exfalso
          rcases hchar with hlit | hfold
          · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hlit; subst hsp_eq
            exact scanBlockScalar_unreachable_comment_without_ws
              sc sp_adv_gen sp_hdr sp_cmt '|' rest
              hcorr (peek_some_has_more hlit) (by decide) (by decide)
              ⟨by native_decide, by native_decide, by native_decide⟩
              hcorr_adv hcorr_hdr hcorr_ws hcorr_cmt hcnt
          · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hfold; subst hsp_eq
            exact scanBlockScalar_unreachable_comment_without_ws
              sc sp_adv_gen sp_hdr sp_cmt '>' rest
              hcorr (peek_some_has_more hfold) (by decide) (by decide)
              ⟨by native_decide, by native_decide, by native_decide⟩
              hcorr_adv hcorr_hdr hcorr_ws hcorr_cmt hcnt
      | cons _ sp_mid _ h_first h_rest =>
        exact whitespace_comment_break_to_SSBComment_withWS
          sp_hdr sp_mid sp_ws sp_cmt sp_nl h_first h_rest h_cmt h_brk
    -- Step 6: body correspondence (grammar sorry)
    obtain ⟨sp_body, hcorr_body⟩ :=
      scanBlockScalarBody_corr sc s_after_nl sp_nl _ _ _ _ hcorr_nl hok
    -- Step 7: dispatch on '|' vs '>' to construct literal or folded
    rcases hchar with hlit | hfold
    · -- Literal: sc.peek? = some '|'
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hlit
      subst hsp_eq
      have hmore := peek_some_has_more hlit
      have hcorr_adv' := advance_non_newline_corr sc '|' rest hcorr hmore (by decide) (by decide)
      have hsp_adv_eq : sp_adv_gen = ⟨rest, sc.col + 1⟩ :=
        ScannerSurfCorr_unique hcorr_adv hcorr_adv'
      rw [hsp_adv_eq] at h_hdr_chars
      have h_header : SCBBlockHeader ⟨rest, sc.col + 1⟩ sp_nl :=
        SCBBlockHeader.mk ⟨rest, sc.col + 1⟩ sp_hdr sp_nl h_hdr_chars h_ssbcomment
      -- sorry: body grammar (SLLiteralContent) + m ≥ 1
      exact ⟨sp_body, Or.inl sorry, hcorr_body⟩
    · -- Folded: sc.peek? = some '>'
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hfold
      subst hsp_eq
      have hmore := peek_some_has_more hfold
      have hcorr_adv' := advance_non_newline_corr sc '>' rest hcorr hmore (by decide) (by decide)
      have hsp_adv_eq : sp_adv_gen = ⟨rest, sc.col + 1⟩ :=
        ScannerSurfCorr_unique hcorr_adv hcorr_adv'
      rw [hsp_adv_eq] at h_hdr_chars
      have h_header : SCBBlockHeader ⟨rest, sc.col + 1⟩ sp_nl :=
        SCBBlockHeader.mk ⟨rest, sc.col + 1⟩ sp_hdr sp_nl h_hdr_chars h_ssbcomment
      -- sorry: body grammar (GOpt SLNbFoldedLines) + m ≥ 1
      exact ⟨sp_body, Or.inr sorry, hcorr_body⟩

end Lean4Yaml.Proofs.ScalarProduction
