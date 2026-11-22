/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Coupling.ScalarCoupling
public import L4YAML.Proofs.Coupling.LandingTab
public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Scanner.ScannerLinePreservation

@[expose] public section Blanket

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

namespace L4YAML.Proofs.ScalarProduction

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Grammar
open L4YAML (ChompStyle)
open L4YAML.Proofs.ScannerProgress (advance_offset_lt)
open L4YAML.Proofs.ScannerCorrectness (skipWhitespaceLoop_offset_ge)

/-! ## §1 Helpers -/

-- Derive `offset < inputEnd` from `peek? = some c`
lemma peek_some_has_more {sc : ScannerState} {c : Char}
    (hpeek : sc.peek? = some c) : sc.offset < sc.inputEnd := by
  unfold ScannerState.peek? at hpeek
  split at hpeek
  · assumption
  · cases hpeek

-- Derive exact surface position from `peek? = some c` + `ScannerSurfCorr`
lemma peek_some_sp {sc : ScannerState} {sp : SurfPos} {c : Char}
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
lemma SNbDoubleMultiLine_prepend (s s₁ s_end : SurfPos)
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
lemma not_lineBreak_bool_to_prop {c : Char}
    (h : ¬isLineBreakBool c = true) : ¬isLineBreakProp c :=
  fun hlb => h ((isLineBreak_iff c).mpr hlb)

/-! ## §1b Surface construction helpers -/

-- SIndent split: SIndent (m + k) → ∃ sp_mid, SIndent m ∧ SIndent k.
-- Building block for making _prod theorems parametric in n.
lemma sindent_split {m k : Nat} {sp sp' : SurfPos}
    (h : SIndent (m + k) sp sp') :
    ∃ sp_mid, SIndent m sp sp_mid ∧ SIndent k sp_mid sp' := by
  induction m generalizing sp with
  | zero =>
    have : 0 + k = k := Nat.zero_add k
    exact ⟨sp, SIndent.zero sp, this ▸ h⟩
  | succ m' ih =>
    have heq : m' + 1 + k = (m' + k) + 1 := by omega
    rw [heq] at h
    cases h with
    | succ n rest col s' h_tail =>
      obtain ⟨sp_mid, h_first, h_second⟩ := ih h_tail
      exact ⟨sp_mid, SIndent.succ m' rest col sp_mid h_first, h_second⟩

-- SIndent → GStar SSWhite
lemma sindent_to_gstar_sswhite {n : Nat} {sp sp' : SurfPos}
    (h : SIndent n sp sp') : GStar SSWhite sp sp' := by
  induction h with
  | zero => exact GStar.nil _
  | succ n rest col s' _ ih => exact GStar.cons _ _ _ (SSWhite.space rest col) ih

-- Concatenation of GStar SSWhite
lemma gstar_sswhite_append {sp1 sp2 sp3 : SurfPos}
    (h1 : GStar SSWhite sp1 sp2) (h2 : GStar SSWhite sp2 sp3) :
    GStar SSWhite sp1 sp3 := by
  induction h1 with
  | nil => exact h2
  | cons _ _ _ hx _ ih => exact GStar.cons _ _ _ hx (ih h2)

-- GStar SSWhite → GOpt SSeparateInLine
lemma gstar_sswhite_to_gopt_sep {sp sp' : SurfPos}
    (h : GStar SSWhite sp sp') : GOpt SSeparateInLine sp sp' := by
  match h with
  | GStar.nil _ => exact GOpt.none _
  | GStar.cons a b c hfirst hrest =>
    exact GOpt.some a c (SSeparateInLine.whites a c (GPlus.mk a b c hfirst hrest))

-- SIndent with n_sk spaces → SFlowLinePrefix n for any n ≤ n_sk.
-- Decomposes spaces into SIndent n (indent) + remaining as GOpt SSeparateInLine.
lemma sindent_to_flowlineprefix {n n_sk : Nat} {sp sp' : SurfPos}
    (h : SIndent n_sk sp sp') (hle : n ≤ n_sk) :
    SFlowLinePrefix n sp sp' := by
  have h_eq : n_sk = n + (n_sk - n) := by omega
  rw [h_eq] at h
  obtain ⟨sp_mid, h_indent_n, h_indent_rest⟩ := sindent_split h
  have h_gstar := sindent_to_gstar_sswhite h_indent_rest
  have h_gopt := gstar_sswhite_to_gopt_sep h_gstar
  exact SFlowLinePrefix.mk n sp sp_mid sp' h_indent_n h_gopt

-- A run of s-white (spaces *and* tabs) is an `s-flow-line-prefix(0)`: the
-- indent is empty at n=0 and the whole run is `s-separate-in-line`.  This is
-- the bridge the tab-aware blank-line scans (`skipWhitespace`) need, since
-- `skipWhitespace_corr` yields `GStar SSWhite` rather than `SIndent`.
lemma gstar_sswhite_to_flowlineprefix0 {sp sp' : SurfPos}
    (h : GStar SSWhite sp sp') : SFlowLinePrefix 0 sp sp' :=
  SFlowLinePrefix.mk 0 sp sp sp' (SIndent.zero sp) (gstar_sswhite_to_gopt_sep h)

/-! ## §1c consumeNewline with SBBreak production

  When the scanner is at a linebreak, `consumeNewline` produces both an
  `SBBreak` and preserves `ScannerSurfCorr`.  The scanner's `advance`
  treats both `\n` and `\r` as line terminators (col:=0, line+1) per
  YAML spec §5.4 [28].  For CRLF, the `\n` byte is skipped by raw
  offset increment to avoid double-counting the line. -/
lemma consumeNewline_sbreak_corr (sc : ScannerState) (sp : SurfPos) (c : Char)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true) :
    ∃ sp', SBBreak sp sp' ∧ ScannerSurfCorr (consumeNewline sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  simp [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
        Bool.or_eq_true, beq_iff_eq] at hlb
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

-- Parametric version: produces `GStar (SLEmpty n .flowIn)` for any `n`.
-- Specialised to n = 0 (the only instantiation — see the caller in
-- `foldQuotedNewlines_prod`).  The loop now skips tab-bearing blank lines
-- (`skipWhitespace`, my B1 fix), which yield `GStar SSWhite` rather than a pure
-- `SIndent`; at n = 0 that whole run is `s-flow-line-prefix(0)` via
-- `gstar_sswhite_to_flowlineprefix0`, so every skipped line is `SLEmpty 0`.
lemma foldQuotedNewlinesLoop_prod (sc : ScannerState) (sp : SurfPos)
    (cnt fuel : Nat) (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', GStar (SLEmpty 0 .flowIn) sp sp' ∧
           ScannerSurfCorr (foldQuotedNewlinesLoop sc cnt fuel).1 sp' := by
  induction fuel generalizing sc sp cnt with
  | zero =>
    simp [foldQuotedNewlinesLoop]
    exact ⟨sp, GStar.nil _, hcorr⟩
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop; dsimp only []
    obtain ⟨sp_ws, h_gstar, hcorr_ws⟩ := skipWhitespace_corr sc sp hcorr
    split
    · rename_i c hpeek; split
      · rename_i hlb
        obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
          consumeNewline_sbreak_corr (skipWhitespace sc) sp_ws c hcorr_ws hpeek hlb
        have h_lempty : SLEmpty 0 .flowIn sp sp_cn :=
          SLEmpty.flow 0 sp sp_ws sp_cn .flowIn (Or.inr rfl)
            (GOpt.some sp sp_ws (gstar_sswhite_to_flowlineprefix0 h_gstar)) h_sbreak
        split
        · exact ⟨sp, GStar.nil _, hcorr⟩
        · obtain ⟨sp_rest, h_gstar_rest, hcorr_rest⟩ :=
            ih (consumeNewline (skipWhitespace sc)) sp_cn (cnt + 1) hcorr_cn
          exact ⟨sp_rest,
                 GStar.cons sp sp_cn sp_rest h_lempty h_gstar_rest,
                 hcorr_rest⟩
      · exact ⟨sp, GStar.nil _, hcorr⟩
    · exact ⟨sp, GStar.nil _, hcorr⟩

/-! ## §1e Hex escape helpers -/

lemma scanner_hex_to_surface_hex (c : Char)
    (h : (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = true) :
    isNsHexDigit c := by
  unfold isNsHexDigit; unfold Char.isDigit at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with (⟨h1, h2⟩ | h) | h
  · left; exact ⟨h1, h2⟩
  · right; left; exact h
  · right; right; exact h

lemma hex_char_ne_newline (c : Char)
    (h : (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = true) :
    c ≠ '\n' := by
  intro heq; subst heq; simp [Char.isDigit] at h

lemma hex_char_ne_cr (c : Char)
    (h : (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = true) :
    c ≠ '\r' := by
  intro heq; subst heq; simp [Char.isDigit] at h

lemma collectHexDigitsLoop_prod (sc : ScannerState) (chars : List Char) (col : Nat)
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

lemma parseHexEscape_prod (sc : ScannerState) (chars : List Char) (col : Nat)
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

lemma list_eq_cons {α : Type} {n : Nat} {l : List α} (h : l.length = n + 1) :
    ∃ a t, l = a :: t ∧ t.length = n := by
  cases l with | nil => simp at h | cons a t => exact ⟨a, t, rfl, by simpa using h⟩

/-! ## §2 Sub-lemmas -/

-- Abbreviation for the loop result expression
abbrev loopResult (sc : ScannerState) :=
  foldQuotedNewlinesLoop (consumeNewline sc) 0 (sc.inputEnd - (consumeNewline sc).offset + 1)

-- When `foldQuotedNewlines` succeeds at a line-break position,
-- the consumed chars form a flow-folded break: `SBBreak + GStar SLEmpty + SFlowLinePrefix`.
-- Uses n=0 (universally satisfiable): the grammar n+1→n fix means flowInBlock 0
-- needs SFlowNode 0 directly, so no parametric indent lifting is needed.
lemma foldQuotedNewlines_prod (sc : ScannerState) (sp : SurfPos)
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
lemma processEscape_prod (sc_bs : ScannerState) (rest : List Char) (col : Nat)
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
lemma collectDoubleQuotedLoop_prod (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s')) :
    ∃ sp_body sp_close,
      SNbDoubleMultiLine 0 sp sp_body ∧
      GLit '"' sp_body sp_close ∧
      s'.peekBack? = some '"' ∧
      ScannerSurfCorr s' sp_close := by
  -- protectedLen (default 0) generalised so the IH covers the fold shift (B2).
  suffices H : ∀ (p : Nat) (sc : ScannerState) (sp : SurfPos) (content : String),
      ScannerSurfCorr sc sp →
      collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd p
        = .ok (result_content, s') →
      (∃ sp_body sp_close,
        SNbDoubleMultiLine 0 sp sp_body ∧
        GLit '"' sp_body sp_close ∧
        s'.peekBack? = some '"' ∧
        ScannerSurfCorr s' sp_close) by
    exact H 0 sc sp content hcorr hok
  clear hok hcorr
  intro p sc sp content hcorr hok
  induction fuel generalizing sc sp content p with
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
             advance_peekBack_eq_peek hcorr (peek_some_has_more hpeek) (by decide) (by decide),
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
        · -- isLineBreakBool c2: escaped newline — the landing is a fold
          -- (item 87): its reader hands the break, the blank lines
          -- (`[112]`'s own `l-empty*` slot) and the prefix; throws contradict.
          rename_i hlb2
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)  -- fold error
          · rename_i fold_result hfold
            obtain ⟨sp_cn, sp_loop, sp_fold, h_sbreak, h_gstar_empty, h_flp, hcorr_fold⟩ :=
              foldQuotedNewlines_prod sc.advance ⟨rest, sc.col + 1⟩ c2 hcorr_adv hpeek2 hlb2 hfold
            repeat' split at hok
            all_goals first
              | contradiction
              | (obtain ⟨sp_body, sp_close, h_body, h_glit, h_pb, h_corr⟩ :=
                   ih _ _ sp_fold _ hcorr_fold hok
                 have h_escaped : SSDoubleEscaped 0 ⟨'\\' :: rest, sc.col⟩ sp_fold :=
                   SSDoubleEscaped.mk 0
                     ⟨'\\' :: rest, sc.col⟩ ⟨'\\' :: rest, sc.col⟩
                     ⟨rest, sc.col + 1⟩ sp_cn sp_loop sp_fold
                     (GStar.nil _) (GLit.mk rest sc.col) h_sbreak
                     h_gstar_empty h_flp
                 exact ⟨sp_body, sp_close,
                        SNbDoubleMultiLine.multi 0
                          ⟨'\\' :: rest, sc.col⟩ ⟨'\\' :: rest, sc.col⟩
                          sp_fold ⟨[], 0⟩ sp_body
                          (GStar.nil _)
                          (SSDoubleBreak.escaped 0 _ _ h_escaped)
                          h_body,
                        h_glit, h_pb, h_corr⟩)
        · -- not line break: processEscape → SNbDoubleChar
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)  -- processEscape error
          · rename_i esc_result hproc
            obtain ⟨sp_esc, h_dq_char, hcorr_esc⟩ :=
              processEscape_prod sc.advance rest sc.col hcorr_adv hproc
            obtain ⟨sp_body, sp_close, h_body, h_glit, h_pb, h_corr⟩ :=
              ih _ _ sp_esc _ hcorr_esc hok
            exact ⟨sp_body, sp_close,
                   SNbDoubleMultiLine_prepend _ _ _ h_dq_char h_body,
                   h_glit, h_pb, h_corr⟩
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
            · -- 4.32.0 reshaped the residue into a `== " "` guard (both branches
              -- recurse); close each via the IH, error branch (if any) via simp
              split at hok <;>
                first
                  | (obtain ⟨sp_body, sp_close, h_body, h_glit, h_pb, h_corr⟩ :=
                       ih _ _ sp_fold _ hcorr_fold hok
                     exact ⟨sp_body, sp_close,
                            SNbDoubleMultiLine.multi 0
                              ⟨c :: rest, sc.col⟩ ⟨c :: rest, sc.col⟩
                              sp_fold ⟨[], 0⟩ _
                              (GStar.nil _)
                              (SSDoubleBreak.flowFold 0 _ sp_cn sp_loop _
                                h_sbreak h_gstar_empty h_flp)
                              h_body,
                            h_glit, h_pb, h_corr⟩)
                  | simp at hok
      · -- not line break: control char check
        split at hok
        · simp at hok  -- invalid control char → error
        · -- valid char: advance + recurse
          rename_i hne_lb hne_ctrl
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_pb, h_corr⟩ :=
            ih _ sc.advance ⟨rest, sc.col + 1⟩ _ hcorr_adv hok
          have h_dq_char : SNbDoubleChar ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
            SNbDoubleChar.plain c rest sc.col
              (not_lineBreak_bool_to_prop hne_lb) hne_bs hne_dq
          exact ⟨sp_body, sp_close,
                 SNbDoubleMultiLine_prepend _ _ _ h_dq_char h_body,
                 h_glit, h_pb, h_corr⟩

-- `scanDoubleQuoted` success produces a complete `SCDoubleQuoted 0 .blockIn`.
-- Precondition: `sc.peek? = some '"'` (from scanner dispatch).
lemma scanDoubleQuoted_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_dq : sc.peek? = some '"')
    (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp', SCDoubleQuoted 0 .blockIn sp sp' ∧ s'.peekBack? = some '"' ∧ ScannerSurfCorr s' sp' := by
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
    obtain ⟨sp_body, sp_close, h_body, h_glit_close, h_pb_close, hcorr_close⟩ :=
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
               h_pb_close,
             corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_close)⟩
    · -- !inFlow = false: no validate; `hok` is a direct `.ok` equality now
      have h := Except.ok.inj hok; subst h
      exact ⟨sp_close,
             SCDoubleQuoted.mk 0 .blockIn _ _ _ _
               (GLit.mk rest sc.col) h_body h_glit_close,
             h_pb_close,
             corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_close)⟩

/-! ## §4 Single-Quoted Scalar -/

-- Prepend a `SNbSingleChar` to the first line of `SNbSingleMultiLine`
lemma SNbSingleMultiLine_prepend (s s₁ s_end : SurfPos)
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
lemma collectSingleQuotedLoop_prod (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hok : collectSingleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s')) :
    ∃ sp_body sp_close,
      SNbSingleMultiLine 0 sp sp_body ∧
      GLit '\'' sp_body sp_close ∧
      s'.peekBack? = some '\'' ∧
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
        obtain ⟨sp_body, sp_close, h_body, h_glit, h_pb, h_corr⟩ :=
          ih sc.advance.advance ⟨rest2, sc.col + 2⟩ _ hcorr_adv2 hok
        have h_esc : SNbSingleChar ⟨'\'' :: '\'' :: rest2, sc.col⟩ ⟨rest2, sc.col + 2⟩ :=
          SNbSingleChar.escapedQuote rest2 sc.col
        exact ⟨sp_body, sp_close,
               SNbSingleMultiLine_prepend _ _ _ h_esc h_body,
               h_glit, h_pb, h_corr⟩
      · -- closing quote (next peek ≠ '\'')
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        exact ⟨⟨'\'' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
               SNbSingleMultiLine.single 0 _ _ (GStar.nil _),
               GLit.mk rest sc.col,
               advance_peekBack_eq_peek hcorr hmore (by decide) (by decide),
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
            · -- 4.32.0: `hok` is directly the recursive call; recurse via IH
              obtain ⟨sp_body, sp_close, h_body, h_glit, h_pb, h_corr⟩ :=
                ih _ sp_fold _ hcorr_fold hok
              exact ⟨sp_body, sp_close,
                     SNbSingleMultiLine.multi 0
                       ⟨c :: rest, sc.col⟩ ⟨c :: rest, sc.col⟩
                       sp_cn sp_loop sp_fold _
                       (GStar.nil _)
                       h_sbreak h_gstar_empty h_flp
                       h_body,
                     h_glit, h_pb, h_corr⟩
      · split at hok
        · simp at hok  -- invalid control char → error
        · -- valid char: advance + recurse
          rename_i hne_lb hne_ctrl
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_pb, h_corr⟩ :=
            ih sc.advance ⟨rest, sc.col + 1⟩ _ hcorr_adv hok
          have h_sq_char : SNbSingleChar ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
            SNbSingleChar.plain c rest sc.col
              (not_lineBreak_bool_to_prop hne_lb) hne_sq
          exact ⟨sp_body, sp_close,
                 SNbSingleMultiLine_prepend _ _ _ h_sq_char h_body,
                 h_glit, h_pb, h_corr⟩

-- `scanSingleQuoted` success produces a complete `SCSingleQuoted 0 .blockIn`.
-- Precondition: `sc.peek? = some '\''` (from scanner dispatch).
lemma scanSingleQuoted_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_sq : sc.peek? = some '\'')
    (hok : scanSingleQuoted sc = .ok s') :
    ∃ sp', SCSingleQuoted 0 .blockIn sp sp' ∧ s'.peekBack? = some '\'' ∧ ScannerSurfCorr s' sp' := by
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
    obtain ⟨sp_body, sp_close, h_body, h_glit_close, h_pb_close, hcorr_close⟩ :=
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
               h_pb_close,
             corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_close)⟩
    · -- !inFlow = false: no validate; `hok` is a direct `.ok` equality now
      have h := Except.ok.inj hok; subst h
      exact ⟨sp_close,
             SCSingleQuoted.mk 0 .blockIn _ _ _ _
               (GLit.mk rest sc.col) h_text h_glit_close,
             h_pb_close,
             corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_close)⟩

/-! ## §5 Plain-safe bridge (Layer 4a)

  Connect scanner's `isPlainSafeBool c inFlow` to the surface grammar's
  `isNsPlainSafe ctx ch`. The Bool predicate decomposes as
  `¬WS ∧ ¬LB [∧ ¬flow]`; the surface predicate uses `isNsChar = ¬LB ∧ ¬WS`
  (flipped conjunction), plus `¬flow` for flow contexts. -/

-- Bool → Prop for block context: `isPlainSafeBool c false ↔ isNsChar c`.
lemma isPlainSafe_block_to_nsChar {c : Char}
    (h : isPlainSafeBool c false = true) : isNsChar c := by
  have hp := (isPlainSafe_iff c false).mp h
  simp only [isPlainSafeProp] at hp
  exact ⟨hp.2.1, hp.1, hp.2.2.1, hp.2.2.2⟩

-- Bool → surface Prop for blockIn: `isPlainSafeBool c false → isNsPlainSafe .blockIn c`.
lemma isPlainSafe_to_nsPlainSafe_blockIn {c : Char}
    (h : isPlainSafeBool c false = true) : isNsPlainSafe .blockIn c :=
  isPlainSafe_block_to_nsChar h

-- Bool → surface Prop for blockOut: same as blockIn.
lemma isPlainSafe_to_nsPlainSafe_blockOut {c : Char}
    (h : isPlainSafeBool c false = true) : isNsPlainSafe .blockOut c :=
  isPlainSafe_block_to_nsChar h

-- Bool → surface Prop for flowIn: adds flow indicator exclusion.
lemma isPlainSafe_to_nsPlainSafe_flowIn {c : Char}
    (h : isPlainSafeBool c true = true) : isNsPlainSafe .flowIn c := by
  have hp := (isPlainSafe_iff c true).mp h
  simp only [isPlainSafeProp] at hp
  exact ⟨⟨hp.2.1, hp.1, hp.2.2.2.1, hp.2.2.2.2⟩, hp.2.2.1⟩

-- isPlainSafeBool c inFlow → c is not a linebreak (useful for advance proofs).
lemma isPlainSafe_not_linebreak {c : Char} {inFlow : Bool}
    (h : isPlainSafeBool c inFlow = true) : ¬isLineBreakProp c := by
  have hp := (isPlainSafe_iff c inFlow).mp h
  cases inFlow
  · -- false (block): hp : ¬WS ∧ ¬LB ∧ printable ∧ ¬BOM
    simp only [isPlainSafeProp] at hp; exact hp.2.1
  · -- true (flow): hp : ¬WS ∧ ¬LB ∧ ¬flowInd ∧ printable ∧ ¬BOM
    simp only [isPlainSafeProp] at hp; exact hp.2.1

-- isPlainSafeBool c inFlow → c ≠ '\n' ∧ c ≠ '\r' (for advance_non_newline_corr).
lemma isPlainSafe_not_newline {c : Char} {inFlow : Bool}
    (h : isPlainSafeBool c inFlow = true) : c ≠ '\n' ∧ c ≠ '\r' := by
  have hlb := isPlainSafe_not_linebreak h
  constructor
  · intro heq; subst heq; exact hlb (by unfold isLineBreakProp; left; native_decide)
  · intro heq; subst heq; exact hlb (by unfold isLineBreakProp; right; native_decide)

/-! ## §6 Block header loop production (Layer 4a)

  `parseBlockHeaderLoop` reads at most one chomping indicator and at most one
  indentation indicator, in either order ([162]). Started from `.clip`/`none` it
  produces `GAlt (GSeq [163] [164]) (GSeq [164] [163])`; `peekBlockHeaderIndicator?`
  hides a repeated kind, so the saturated loop consumes nothing. -/

-- Header chars are not newlines: used for advance_non_newline_corr.
lemma blockHeaderChar_not_newline {c : Char}
    (h : Grammar.isBlockScalarHeaderChar c = true) : c ≠ '\n' ∧ c ≠ '\r' := by
  constructor
  · intro heq; subst heq; simp [Grammar.isBlockScalarHeaderChar] at h
  · intro heq; subst heq; simp [Grammar.isBlockScalarHeaderChar] at h

-- isDigit && != '0' → isBlockScalarHeaderChar (digit 1-9 is a header char).
lemma isDigitNotZero_isBlockHeaderChar {c : Char}
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

-- `parseBlockHeaderLoop` preserves or sets `explicitOffset` to `some d` with `d ≥ 1`.
-- Starting with `none`, any digit sets d = c.toNat - '0'.toNat ≥ 1.
-- Starting with `some d` where `d ≥ 1`, the value is preserved or overwritten with ≥ 1.
lemma parseBlockHeaderLoop_offset_preserves (sc : ScannerState) (chomp : ChompStyle)
    (off : Option Nat) (fuel : Nat)
    (hoff : ∀ d, off = some d → d ≥ 1) :
    ∀ d, (parseBlockHeaderLoop sc chomp off fuel).2.1 = some d → d ≥ 1 := by
  induction fuel generalizing sc chomp off with
  | zero => simp only [parseBlockHeaderLoop]; exact hoff
  | succ fuel' ih =>
    simp only [parseBlockHeaderLoop]
    split
    · exact ih sc.advance .strip off hoff  -- '-': same offset
    · exact ih sc.advance .keep off hoff   -- '+': same offset
    · rename_i c _ _ _
      split
      · -- digit 1–9: offset becomes some (c.toNat - '0'.toNat)
        rename_i hdigit
        exact ih sc.advance chomp (some (c.toNat - '0'.toNat)) (fun d h => by
          have heq := Option.some.inj h; subst heq
          -- c.isDigit && c != '0' implies c ∈ {'1',...,'9'}, so c.toNat - '0'.toNat ≥ 1
          have hne' : c ≠ '0' := by intro heq; subst heq; simp at hdigit
          have hdig : c.isDigit = true := by
            have := Bool.and_eq_true_iff.mp hdigit; exact this.1
          simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq,
                     UInt32.le_iff_toNat_le] at hdig
          have h0_val : ('0' : Char).val.toNat = 48 := by native_decide
          rw [h0_val] at hdig
          have h_ne_48 : c.val.toNat ≠ 48 := by
            intro heq; apply hne'
            exact Char.ext (UInt32.toNat_inj.mp (by omega))
          show c.toNat - '0'.toNat ≥ 1
          simp only [Char.toNat, h0_val]
          omega)
      · exact hoff  -- non-header: returns unchanged offset
    · exact hoff    -- none: returns unchanged offset

-- Digit 1–9 as the `[163]` character class.
lemma isDigitNotZero_indentDigit {c : Char}
    (h : (c.isDigit && (c != '0')) = true) : '1' ≤ c ∧ c ≤ '9' := by
  have ⟨hdig, hne⟩ := Bool.and_eq_true_iff.mp h
  have hne' : c ≠ '0' := by intro heq; subst heq; simp at hne
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hdig
  simp only [Char.le_def, UInt32.le_iff_toNat_le] at hdig ⊢
  have h0_val : ('0' : Char).val.toNat = 48 := by native_decide
  have h1_val : ('1' : Char).val.toNat = 49 := by native_decide
  have h9_val : ('9' : Char).val.toNat = 57 := by native_decide
  have h2' : c.val.toNat ≠ 48 := by
    intro heq; apply hne'
    exact Char.ext (UInt32.toNat_inj.mp (by omega))
  omega

-- `peekBlockHeaderIndicator?` reveals the real next char, and only while its kind is free.
lemma peekBlockHeaderIndicator?_some {sc : ScannerState} {chomp : ChompStyle}
    {off : Option Nat} {c : Char}
    (h : peekBlockHeaderIndicator? sc chomp off = some c) :
    sc.peek? = some c ∧ ((c = '-' ∨ c = '+') → chomp = .clip) ∧
      (c.isDigit = true → off = none) := by
  unfold peekBlockHeaderIndicator? at h
  split at h
  · rename_i c' hpeek
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · rename_i hnc hnd
        cases h
        refine ⟨hpeek, fun hc => ?_, fun hd => ?_⟩
        · by_cases hne : chomp = .clip
          · exact hne
          · exact absurd ⟨hc, hne⟩ hnc
        · by_cases hne : off = none
          · exact hne
          · exact absurd ⟨hd, hne⟩ hnd
  · exact absurd h (by simp)

-- Both indicator kinds already read: the loop consumes nothing.
lemma parseBlockHeaderLoop_saturated (sc : ScannerState) (chomp : ChompStyle)
    (off : Option Nat) (fuel : Nat) (hc : chomp ≠ .clip) (ho : off ≠ none) :
    parseBlockHeaderLoop sc chomp off fuel = (chomp, off, sc) := by
  cases fuel with
  | zero => simp only [parseBlockHeaderLoop]
  | succ fuel' =>
    simp only [parseBlockHeaderLoop]
    split
    · rename_i hpk; exact absurd ((peekBlockHeaderIndicator?_some hpk).2.1 (Or.inl rfl)) hc
    · rename_i hpk; exact absurd ((peekBlockHeaderIndicator?_some hpk).2.1 (Or.inr rfl)) hc
    · rename_i c _ _ hpk
      split
      · rename_i hd
        exact absurd ((peekBlockHeaderIndicator?_some hpk).2.2
          (Bool.and_eq_true_iff.mp hd).1) ho
      · rfl
    · rfl

-- Chomping indicator already read: the rest of the header is `[163]`.
lemma parseBlockHeaderLoop_prod_indent (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (chomp : ChompStyle) (fuel : Nat)
    (hc : chomp ≠ .clip) :
    ∃ sp', SCIndentationIndicator sp sp' ∧
      ScannerSurfCorr (parseBlockHeaderLoop sc chomp none fuel).2.2 sp' := by
  cases fuel with
  | zero => exact ⟨sp, .empty sp, by simp only [parseBlockHeaderLoop]; exact hcorr⟩
  | succ fuel' =>
    simp only [parseBlockHeaderLoop]
    split
    · rename_i hpk; exact absurd ((peekBlockHeaderIndicator?_some hpk).2.1 (Or.inl rfl)) hc
    · rename_i hpk; exact absurd ((peekBlockHeaderIndicator?_some hpk).2.1 (Or.inr rfl)) hc
    · rename_i c _ _ hpk
      have hpeek := (peekBlockHeaderIndicator?_some hpk).1
      split
      · rename_i hdigit
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have ⟨hne_nl, hne_cr⟩ :=
          blockHeaderChar_not_newline (isDigitNotZero_isBlockHeaderChar hdigit)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          (peek_some_has_more hpeek) hne_nl hne_cr
        rw [parseBlockHeaderLoop_saturated sc.advance chomp (some (c.toNat - '0'.toNat))
          fuel' hc (by simp)]
        exact ⟨⟨rest, sc.col + 1⟩,
          .digit _ _ (GChar.mk c rest sc.col (isDigitNotZero_indentDigit hdigit)), hcorr_adv⟩
      · exact ⟨sp, .empty sp, hcorr⟩
    · exact ⟨sp, .empty sp, hcorr⟩

-- Indentation indicator already read: the rest of the header is `[164]`.
lemma parseBlockHeaderLoop_prod_chomp (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (off : Option Nat) (fuel : Nat) (ho : off ≠ none) :
    ∃ sp', SCChompingIndicator sp sp' ∧
      ScannerSurfCorr (parseBlockHeaderLoop sc .clip off fuel).2.2 sp' := by
  cases fuel with
  | zero => exact ⟨sp, .empty sp, by simp only [parseBlockHeaderLoop]; exact hcorr⟩
  | succ fuel' =>
    simp only [parseBlockHeaderLoop]
    split
    · rename_i hpk
      have hpeek := (peekBlockHeaderIndicator?_some hpk).1
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv := advance_non_newline_corr sc '-' rest hcorr
        (peek_some_has_more hpeek) (by decide) (by decide)
      rw [parseBlockHeaderLoop_saturated sc.advance .strip off fuel' (by decide) ho]
      exact ⟨⟨rest, sc.col + 1⟩, .strip _ _ (GLit.mk rest sc.col), hcorr_adv⟩
    · rename_i hpk
      have hpeek := (peekBlockHeaderIndicator?_some hpk).1
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv := advance_non_newline_corr sc '+' rest hcorr
        (peek_some_has_more hpeek) (by decide) (by decide)
      rw [parseBlockHeaderLoop_saturated sc.advance .keep off fuel' (by decide) ho]
      exact ⟨⟨rest, sc.col + 1⟩, .keep _ _ (GLit.mk rest sc.col), hcorr_adv⟩
    · rename_i c _ _ hpk
      split
      · rename_i hd
        exact absurd ((peekBlockHeaderIndicator?_some hpk).2.2
          (Bool.and_eq_true_iff.mp hd).1) ho
      · exact ⟨sp, .empty sp, hcorr⟩
    · exact ⟨sp, .empty sp, hcorr⟩

-- `parseBlockHeaderLoop` from `.clip`/`none` produces the `[162]` indicator part.
lemma parseBlockHeaderLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (fuel : Nat) :
    ∃ sp', GAlt (GSeq SCIndentationIndicator SCChompingIndicator)
                (GSeq SCChompingIndicator SCIndentationIndicator) sp sp' ∧
           ScannerSurfCorr (parseBlockHeaderLoop sc .clip none fuel).2.2 sp' := by
  cases fuel with
  | zero =>
    exact ⟨sp, .left _ _ (.mk _ _ _ (.empty sp) (.empty sp)),
      by simp only [parseBlockHeaderLoop]; exact hcorr⟩
  | succ fuel' =>
    simp only [parseBlockHeaderLoop]
    split
    · rename_i hpk
      have hpeek := (peekBlockHeaderIndicator?_some hpk).1
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv := advance_non_newline_corr sc '-' rest hcorr
        (peek_some_has_more hpeek) (by decide) (by decide)
      obtain ⟨sp', h_ind, hcorr'⟩ :=
        parseBlockHeaderLoop_prod_indent sc.advance _ hcorr_adv .strip fuel' (by decide)
      exact ⟨sp', .right _ _ (.mk _ _ _ (.strip _ _ (GLit.mk rest sc.col)) h_ind), hcorr'⟩
    · rename_i hpk
      have hpeek := (peekBlockHeaderIndicator?_some hpk).1
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv := advance_non_newline_corr sc '+' rest hcorr
        (peek_some_has_more hpeek) (by decide) (by decide)
      obtain ⟨sp', h_ind, hcorr'⟩ :=
        parseBlockHeaderLoop_prod_indent sc.advance _ hcorr_adv .keep fuel' (by decide)
      exact ⟨sp', .right _ _ (.mk _ _ _ (.keep _ _ (GLit.mk rest sc.col)) h_ind), hcorr'⟩
    · rename_i c _ _ hpk
      have hpeek := (peekBlockHeaderIndicator?_some hpk).1
      split
      · rename_i hdigit
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have ⟨hne_nl, hne_cr⟩ :=
          blockHeaderChar_not_newline (isDigitNotZero_isBlockHeaderChar hdigit)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          (peek_some_has_more hpeek) hne_nl hne_cr
        obtain ⟨sp', h_ch, hcorr'⟩ := parseBlockHeaderLoop_prod_chomp sc.advance _ hcorr_adv
          (some (c.toNat - '0'.toNat)) fuel' (by simp)
        exact ⟨sp', .left _ _ (.mk _ _ _
          (.digit _ _ (GChar.mk c rest sc.col (isDigitNotZero_indentDigit hdigit))) h_ch), hcorr'⟩
      · exact ⟨sp, .left _ _ (.mk _ _ _ (.empty sp) (.empty sp)), hcorr⟩
    · exact ⟨sp, .left _ _ (.mk _ _ _ (.empty sp) (.empty sp)), hcorr⟩

/-! ## §6b Sub-function Grammar Productions

  Helper `_prod` theorems for sub-functions used by block and plain scalar loops.
  These construct grammar witnesses for `consumeExactSpaces`, `collectLineContentLoop`,
  and `consumeNewline`. -/

-- Helper: when peek? = some ' ', first component of consumeExactSpaces (n+1)
--   = first component of consumeExactSpaces sc.advance n + 1
lemma consumeExactSpaces_succ_space_fst (sc : ScannerState) (n : Nat)
    (hpeek : sc.peek? = some ' ') :
    (consumeExactSpaces sc (n + 1)).1 = (consumeExactSpaces sc.advance n).1 + 1 := by
  -- generalize the recursive call BEFORE unfolding to keep both sides in sync
  generalize h : consumeExactSpaces sc.advance n = p
  unfold consumeExactSpaces; split
  · rw [h]
  · contradiction

-- Helper: when peek? = some ' ', second component of consumeExactSpaces (n+1)
--   = second component of consumeExactSpaces sc.advance n
lemma consumeExactSpaces_succ_space_snd (sc : ScannerState) (n : Nat)
    (hpeek : sc.peek? = some ' ') :
    (consumeExactSpaces sc (n + 1)).2 = (consumeExactSpaces sc.advance n).2 := by
  generalize h : consumeExactSpaces sc.advance n = p
  unfold consumeExactSpaces; split
  · rw [h]
  · contradiction

-- Helper: when peek? ≠ some ' ', consumeExactSpaces (n+1) returns (0, sc)
lemma consumeExactSpaces_succ_not_space (sc : ScannerState) (n : Nat)
    (hpeek : sc.peek? ≠ some ' ') :
    consumeExactSpaces sc (n + 1) = (0, sc) := by
  unfold consumeExactSpaces; split
  · exact absurd ‹_› hpeek
  · rfl

-- `consumeExactSpaces` returns at most `count` spaces.
lemma consumeExactSpaces_fst_le (sc : ScannerState) (count : Nat) :
    (consumeExactSpaces sc count).1 ≤ count := by
  induction count generalizing sc with
  | zero => simp [consumeExactSpaces]
  | succ n ih =>
    by_cases hpeek : sc.peek? = some ' '
    · rw [consumeExactSpaces_succ_space_fst sc n hpeek]
      have := ih sc.advance; omega
    · rw [consumeExactSpaces_succ_not_space sc n hpeek]; simp

-- `consumeExactSpaces` produces `SIndent` for however many spaces were actually consumed.
lemma consumeExactSpaces_sindent_partial (sc : ScannerState) (sp : SurfPos)
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
lemma consumeExactSpaces_sindent_prod (sc : ScannerState) (sp : SurfPos)
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
lemma collectLineContentLoop_nbchar_prod (sc : ScannerState) (sp : SurfPos)
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
      · -- nb-char (not break, printable, not BOM): consume + recurse
        rename_i hcond
        have hne_lb : ¬isLineBreakBool c = true := fun h => hcond (by simp [h])
        have hpr : isPrintableBool c = true := by
          cases h : isPrintableBool c with
          | true => rfl
          | false => exact absurd (by simp [h]) hcond
        have hbom : (c == '﻿') = false := by
          cases h : (c == '﻿') with
          | false => rfl
          | true => exact absurd (by simp [h]) hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have h_not_nl := not_isLineBreak_not_newline c hne_lb
        have h_not_cr := not_isLineBreak_not_cr c hne_lb
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
        obtain ⟨sp', h_tail, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩ _ hcorr_adv
        exact ⟨sp',
               GStar.cons _ ⟨rest, sc.col + 1⟩ _
                 (not_isLineBreak_gives_SNbChar c rest sc.col hne_lb hpr hbom) h_tail,
               hcorr'⟩
    · -- peek? = none: stop
      exact ⟨sp, GStar.nil sp, hcorr⟩

-- GStar → GPlus conversion when at least one element exists (from known first char).
lemma gstar_to_gplus_from_first {P : SurfPos → SurfPos → Prop}
    {sp sp₁ sp' : SurfPos}
    (h_first : P sp sp₁) (h_rest : GStar P sp₁ sp') :
    GPlus P sp sp' := GPlus.mk sp sp₁ sp' h_first h_rest

-- When collectLineContentLoop is called with peek? = some c (not break),
-- the first char WILL be consumed, giving GPlus SNbChar.
lemma collectLineContentLoop_gplus_prod (sc : ScannerState) (sp : SurfPos)
    (c : Char) (content : String) (fuel : Nat)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some c)
    (hne_lb : ¬isLineBreakBool c = true)
    (hpr : isPrintableBool c = true) (hbom : (c == '﻿') = false)
    (hfuel : fuel ≥ 1) :
    ∃ sp', GPlus SNbChar sp sp' ∧
           ScannerSurfCorr (collectLineContentLoop sc content fuel).2 sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  have h_not_nl := not_isLineBreak_not_newline c hne_lb
  have h_not_cr := not_isLineBreak_not_cr c hne_lb
  have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
  have hlb_f : isLineBreakBool c = false := by
    cases h : isLineBreakBool c with
    | false => rfl
    | true => exact absurd h hne_lb
  -- With fuel ≥ 1, unfold one step: the first char is consumed
  match fuel, hfuel with
  | fuel' + 1, _ =>
    simp only [collectLineContentLoop]
    rw [hpeek]
    simp only [hlb_f, hpr, hbom, Bool.not_true, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte]
    obtain ⟨sp', h_tail, hcorr'⟩ :=
      collectLineContentLoop_nbchar_prod sc.advance ⟨rest, sc.col + 1⟩ _ fuel' hcorr_adv
    have h_first := not_isLineBreak_gives_SNbChar c rest sc.col hne_lb hpr hbom
    exact ⟨sp', gstar_to_gplus_from_first h_first h_tail, hcorr'⟩

-- The line loop never shortens its accumulator.
private lemma collectLineContentLoop_length_ge (sc : ScannerState) (content : String) (fuel : Nat) :
    content.length ≤ (collectLineContentLoop sc content fuel).1.length := by
  induction fuel generalizing sc content with
  | zero => simp [collectLineContentLoop]
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · exact Nat.le_refl _
      · exact Nat.le_trans (by simp [String.length_push]) (ih sc.advance _)
    · exact Nat.le_refl _

-- With an nb-char first and fuel, the collected line is non-empty.
lemma collectLineContentLoop_fst_nonempty (sc : ScannerState) (c : Char) (content : String)
    (fuel : Nat) (hpeek : sc.peek? = some c) (hne_lb : ¬isLineBreakBool c = true)
    (hpr : isPrintableBool c = true) (hbom : (c == '\uFEFF') = false) (hfuel : fuel ≥ 1) :
    (collectLineContentLoop sc content fuel).1.isEmpty = false := by
  have hlb_f : isLineBreakBool c = false := by
    cases h : isLineBreakBool c with
    | false => rfl
    | true => exact absurd h hne_lb
  match fuel, hfuel with
  | fuel' + 1, _ =>
    simp only [collectLineContentLoop]
    rw [hpeek]
    simp only [hlb_f, hpr, hbom, Bool.not_true, Bool.or_self,
      Bool.false_eq_true, ↓reduceIte]
    have h := collectLineContentLoop_length_ge sc.advance (content.push c) fuel'
    rw [String.length_push] at h
    cases hE : (collectLineContentLoop sc.advance (content.push c) fuel').1.isEmpty with
    | false => rfl
    | true => exact absurd h (by rw [String.isEmpty_iff.mp hE]; simp)

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

/-- Maps scanner's `inFlow : Bool` to the grammar context for plain scalars. -/
def ctxOfInFlow : Bool → YamlContext
  | false => .blockIn
  | true => .flowIn

-- Bridge: `isPlainSafeBool c inFlow` → `isNsPlainSafe (ctxOfInFlow inFlow) c`.
lemma isPlainSafe_to_nsPlainSafe {c : Char} {inFlow : Bool}
    (h : isPlainSafeBool c inFlow = true) : isNsPlainSafe (ctxOfInFlow inFlow) c := by
  cases inFlow with
  | false => exact isPlainSafe_to_nsPlainSafe_blockIn h
  | true => exact isPlainSafe_to_nsPlainSafe_flowIn h

-- Bridge: `isFlowIndicatorProp c → isIndicatorProp c`.
lemma flowIndicatorProp_to_indicatorProp {c : Char}
    (h : isFlowIndicatorProp c) : isIndicatorProp c := by
  unfold isFlowIndicatorProp isIndicatorProp at *
  have hsub : [',', '[', ']', '{', '}'] ⊆
    ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
     '\'', '"', '%', '@', '`'] := by decide
  exact hsub h

-- Bridge: `isPlainSafeBool c inFlow` + not-colon + not-hash → `SNsPlainChar (ctxOfInFlow inFlow)`.
-- (`:` needs next char safe via `colonSafe` constructor; `#` only right after a plain
-- char, via `[132]`'s `hash` entry — an empty `s-white*`.)
lemma isPlainSafe_to_plainChar_basic (c : Char) (rest : List Char) (col : Nat) (inFlow : Bool)
    (hSafe : isPlainSafeBool c inFlow = true)
    (hNotColon : c ≠ ':') (hNotHash : c ≠ '#') :
    SNsPlainChar (ctxOfInFlow inFlow) ⟨c :: rest, col⟩ ⟨rest, col + 1⟩ :=
  SNsPlainChar.safe (ctxOfInFlow inFlow) c rest col
    (isPlainSafe_to_nsPlainSafe hSafe) hNotColon hNotHash

-- Bridge: `isPlainSafeBool c inFlow` + not-colon + not-hash →
-- `SNbNsPlainInLineEntry (ctxOfInFlow inFlow)` with empty whitespace prefix.
lemma isPlainSafe_to_inlineEntry_basic (c : Char) (rest : List Char) (col : Nat) (inFlow : Bool)
    (hSafe : isPlainSafeBool c inFlow = true)
    (hNotColon : c ≠ ':') (hNotHash : c ≠ '#') :
    SNbNsPlainInLineEntry (ctxOfInFlow inFlow) ⟨c :: rest, col⟩ ⟨rest, col + 1⟩ :=
  SNbNsPlainInLineEntry.mk (ctxOfInFlow inFlow) ⟨c :: rest, col⟩ ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
    (GStar.nil _)
    (isPlainSafe_to_plainChar_basic c rest col inFlow hSafe hNotColon hNotHash)

-- Bridge: `canStartPlainScalarBool` → `SNsPlainFirst (ctxOfInFlow inFlow)`.
-- Connects the scanner's first-char predicate to the surface grammar type.
-- For non-indicator chars: uses `nonIndicator` constructor.
-- For `-`/`?`/`:`: uses `dashSafe`/`questionSafe`/`colonSafe` with the
-- next-char safety from `canStartPlainScalarBool`.
--
-- The `next` parameter corresponds to `sc.peekAt? 1` from the scanner, and
-- for exception chars must match `rest.head?` (the next char in the surface).
-- When `next = some n`, rest must start with `n` (hrest_head).
-- When `next = none`, the exception branch of canStart returns false, so
-- the hypothesis is contradictory for exception chars.
lemma canStartPlainScalar_to_SNsPlainFirst (c : Char) (rest : List Char)
    (col : Nat) (next : Option Char) (inFlow : Bool)
    (hstart : canStartPlainScalarBool c next inFlow = true)
    (hrest_head : ∀ n, next = some n → ∃ rest', rest = n :: rest') :
    SNsPlainFirst (ctxOfInFlow inFlow) ⟨c :: rest, col⟩ ⟨rest, col + 1⟩ := by
  have hprop := (canStartPlainScalar_iff c next inFlow).mp hstart
  unfold canStartPlainScalarProp at hprop
  split at hprop
  · -- Exception char: c ∈ {'-', '?', ':'}
    rename_i hexc
    match next with
    | none => exact absurd hprop id
    | some n =>
      obtain ⟨rest', hrst⟩ := hrest_head n rfl
      subst hrst
      obtain ⟨h_nws, h_nlb, h_nfi, h_pr, h_nbom⟩ := hprop
      have h_safe : isNsPlainSafe (ctxOfInFlow inFlow) n := by
        cases inFlow with
        | false => exact ⟨fun hlb => h_nlb hlb, fun hws => h_nws hws, h_pr, h_nbom⟩
        | true => exact ⟨⟨fun hlb => h_nlb hlb, fun hws => h_nws hws, h_pr, h_nbom⟩,
                         h_nfi rfl⟩
      rcases hexc with rfl | rfl | rfl
      · exact SNsPlainFirst.dashSafe (ctxOfInFlow inFlow) n rest' col h_safe
      · exact SNsPlainFirst.questionSafe (ctxOfInFlow inFlow) n rest' col h_safe
      · exact SNsPlainFirst.colonSafe (ctxOfInFlow inFlow) n rest' col h_safe
  · -- Non-exception: non-indicator, non-whitespace, non-linebreak
    obtain ⟨h_ni, h_nws, h_nlb, h_pr, h_nbom⟩ := hprop
    have h_safe : isNsPlainSafe (ctxOfInFlow inFlow) c := by
      cases inFlow with
      | false => exact ⟨fun hlb => h_nlb hlb, fun hws => h_nws hws, h_pr, h_nbom⟩
      | true =>
        exact ⟨⟨fun hlb => h_nlb hlb, fun hws => h_nws hws, h_pr, h_nbom⟩,
               fun hfi => h_ni (flowIndicatorProp_to_indicatorProp hfi)⟩
    exact SNsPlainFirst.nonIndicator (ctxOfInFlow inFlow) c rest col h_safe h_ni

-- `scanPlainScalar` produces `SNsPlain 0 .blockIn` + trailing WS and preserves
-- correspondence.
--
-- Precondition: `canStartPlainScalarBool` for the first character (guaranteed
-- by `scanNextToken_dispatchContent` call site).
--
-- Conclusion includes trailing `GStar SSWhite` because the scanner advances
-- past trailing whitespace that is NOT covered by `SNsPlain` (per YAML spec
-- [129] `nb-ns-plain-in-line(c) = (s-white* ns-plain-char(c))*` — no trailing
-- WS in the production).
--
-- Correlation: fully proven (delegated to `scanPlainScalar_corr`).
-- Grammar: requires decomposing the loop into first char (`SNsPlainFirst`) +
-- intra-line entries (`GStar SNbNsPlainInLineEntry`) + continuation lines
-- (`GStar SSNsPlainNextLine`). The helpers `isPlainSafe_to_plainChar_basic` and
-- `isPlainSafe_to_inlineEntry_basic` are ready for the basic-char case;
-- remaining: loop theorem (`collectPlainScalarLoop_prod`), `:` colonSafe,
-- `#` via the `[132]` `hash` entry, multi-line (`handleBlockLineBreak_prod`).

-- Bridge: terminates?=none at ':' → next char exists and is not blank
-- (and in flow context, not a flow indicator).
lemma colon_not_terminated_next (sc : ScannerState) (content spaces : String) (inFlow : Bool)
    (h : collectPlainScalar_terminates? ':' sc content spaces inFlow = none) :
    ∃ n, sc.peekAt? 1 = some n ∧ isBlankBool n = false ∧
         (inFlow = true → isFlowIndicatorBool n = false) ∧
         isPrintableBool n = true ∧ (n == '﻿') = false := by
  simp [collectPlainScalar_terminates?] at h
  split at h
  · -- peekAt? 1 = some n
    rename_i n hn
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    obtain ⟨⟨⟨hblank, hflow⟩, hpr⟩, hbom⟩ := h
    refine ⟨n, hn, hblank, ?_, hpr, hbom⟩
    cases inFlow with
    | false => exact fun hh => absurd hh (by decide)
    | true => simpa using hflow
  · -- peekAt? 1 = none → true = false → contradiction
    cases inFlow <;> simp at h

-- Bridge: ¬isBlankBool (+ printable, ¬BOM) → isNsChar (for colonSafe)
lemma not_blank_to_nsChar {c : Char} (h : isBlankBool c = false)
    (hpr : isPrintableBool c = true) (hbom : (c == '﻿') = false) : isNsChar c := by
  have hpr' : isPrintableProp c := (isPrintable_iff c).mp hpr
  have hbom' : c ≠ '﻿' := by simpa using hbom
  simp [isNsChar, isLineBreakProp, isLineFeedProp, isCarriageReturnProp,
    isWhiteSpaceProp, isSpaceProp, isTabProp,
    isBlankBool, isWhiteSpaceBool, isSpaceBool, isTabBool,
    isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
    beq_iff_eq, Bool.or_eq_false_iff, hpr', hbom'] at *
  -- h : (¬c = ' ' ∧ ¬c = '\t') ∧ ¬c = '\n' ∧ ¬c = '\r'
  -- goal (after simp discharges printable/BOM): LB pair ∧ WS pair
  exact ⟨h.2, h.1⟩

-- Helper: create a new inline entry from a safe char + prepend to continuation.
lemma prepend_char_to_continuation
    {sp sp_adv sp_end sp_trail : SurfPos}
    (hchar : SNsPlainChar .blockIn sp sp_adv)
    (h_ent : GStar (SNbNsPlainInLineEntry .blockIn) sp_adv sp_end)
    (h_trail : GStar SSWhite sp_end sp_trail) :
    ∃ sp_end', GStar (SNbNsPlainInLineEntry .blockIn) sp sp_end' ∧
               GStar SSWhite sp_end' sp_trail :=
  ⟨sp_end,
   GStar.cons _ _ _ (SNbNsPlainInLineEntry.mk .blockIn sp _ _ (GStar.nil _) hchar) h_ent,
   h_trail⟩

/-! ## §5b skipBlankLinesLoop production (block context blank lines)

  Analogous to `foldQuotedNewlinesLoop_prod` (§1d) but for the block-context
  `skipBlankLinesLoop`.  Each iteration consumes `skipSpaces + consumeNewline`,
  producing one `SLEmpty 0 .flowIn` per blank line.  Uses `.flowIn` context
  because `s-flow-folded(n)` (YAML §6.8 [75]) always uses `l-empty(n, flow-in)`
  regardless of outer context. -/
lemma skipBlankLinesLoop_prod (sc : ScannerState) (sp : SurfPos)
    (cnt fuel : Nat) (inputEnd : Nat)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', GStar (SLEmpty 0 .flowIn) sp sp' ∧
           ScannerSurfCorr (skipBlankLinesLoop sc cnt fuel inputEnd).2 sp' := by
  induction fuel generalizing sc sp cnt with
  | zero =>
    simp [skipBlankLinesLoop]
    exact ⟨sp, GStar.nil _, hcorr⟩
  | succ fuel' ih =>
    unfold skipBlankLinesLoop; dsimp only []
    obtain ⟨sp_ws, h_gstar, hcorr_sk⟩ := skipWhitespace_corr sc sp hcorr
    split
    · rename_i c hpeek; split
      · rename_i hlb
        obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
          consumeNewline_sbreak_corr (skipWhitespace sc) sp_ws c hcorr_sk hpeek hlb
        have h_lempty : SLEmpty 0 .flowIn sp sp_cn :=
          SLEmpty.flow 0 sp sp_ws sp_cn .flowIn (Or.inr rfl)
            (GOpt.some sp sp_ws (gstar_sswhite_to_flowlineprefix0 h_gstar)) h_sbreak
        obtain ⟨sp_rest, h_gstar_rest, hcorr_rest⟩ :=
          ih (consumeNewline (skipWhitespace sc)) sp_cn (cnt + 1) hcorr_cn
        -- item 100: the gate's arm returns the saved state, reading nothing
        split
        · exact ⟨sp, GStar.nil _, hcorr⟩
        · exact ⟨sp_rest,
                 GStar.cons sp sp_cn sp_rest h_lempty h_gstar_rest,
                 hcorr_rest⟩
      · exact ⟨sp, GStar.nil _, hcorr⟩
    · exact ⟨sp, GStar.nil _, hcorr⟩

/-! ## §5b′ The gate's own arithmetic (item 100)

    `skipBlankLinesLoop`'s §6.1 gate stops the blank run at a line whose white
    prefix reaches a tab before the floor.  Such a line is UNDER the
    continuation indent, so the handler's own first test ends the scalar there:
    past that test the gate is known false, which is what the fold's landing
    lemma reads.  The premise is the floor's arithmetic —
    `minContentIndentOf`'s `max 0 (currentIndent+1)` in block context, §8.1's
    column in flow — and it is the caller's, because the handler takes its
    floor as a parameter. -/

/-- The blank-line skipper leaves the indent stack alone. -/
lemma skipBlankLinesLoop_indents (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).2.indents = s.indents := by
  induction fuel generalizing s cnt with
  | zero => rfl
  | succ fuel' ih =>
    unfold skipBlankLinesLoop; dsimp only []
    split
    · split
      · split
        · rfl
        · rw [ih, L4YAML.Proofs.ScannerWhitespace.consumeNewline_preserves_indents,
              L4YAML.Proofs.EmitterScannability.skipWhitespace_preserves_indents]
      · rfl
    · rfl

/-- …so does the whole handler. -/
lemma handleBlockLineBreak_indents' {s s' : ScannerState} {content content' : String}
    {ci ie : Nat}
    (h : collectPlainScalar_handleBlockLineBreak s content ci ie = some (content', s')) :
    s'.indents = s.indents := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  dsimp only [] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [L4YAML.Proofs.EmitterScannability.skipWhitespace_preserves_indents,
          L4YAML.Proofs.EmitterScannability.skipSpaces_preserves_indents,
          skipBlankLinesLoop_indents,
          L4YAML.Proofs.ScannerWhitespace.consumeNewline_preserves_indents]

/-- The block continuation floor sits strictly above the block indent —
    `minContentIndentOf`'s `max 0 (currentIndent + 1)`, read as an `Int`. -/
lemma currentIndent_lt_blockContentIndent {s : ScannerState} (h : s.inFlow = false) :
    (s.currentIndent : Int) <
      ((if s.inFlow then s.col else (max 0 (s.currentIndent + 1)).toNat : Nat) : Int) := by
  rw [ite_eq_right (by simp [h])]
  omega

/-- **Past the handler's under-indent test the gate did not fire.**  A run the
    gate stopped sits at a column at or below the block indent, and the
    continuation floor is above it. -/
lemma handleBlockLineBreak_gate_false {s s' : ScannerState} {content content' : String}
    {ci ie : Nat} (hcin : (s.currentIndent : Int) < (ci : Int))
    (h : collectPlainScalar_handleBlockLineBreak s content ci ie = some (content', s')) :
    blankLineTabUnderFloor (skipBlankLinesLoop (consumeNewline s) 0
      (ie - (consumeNewline s).offset + 1) ie).2 = false := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  dsimp only [] at h
  split at h
  · exact absurd h (by simp)
  · rename_i h_guard
    cases hg : blankLineTabUnderFloor (skipBlankLinesLoop (consumeNewline s) 0
        (ie - (consumeNewline s).offset + 1) ie).2 with
    | false => rfl
    | true =>
      exfalso
      simp only [blankLineTabUnderFloor, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hg
      have hci : (skipSpaces (skipBlankLinesLoop (consumeNewline s) 0
          (ie - (consumeNewline s).offset + 1) ie).2).currentIndent = s.currentIndent := by
        simp only [ScannerState.currentIndent,
          L4YAML.Proofs.EmitterScannability.skipSpaces_preserves_indents,
          skipBlankLinesLoop_indents,
          L4YAML.Proofs.ScannerWhitespace.consumeNewline_preserves_indents]
      rw [hci] at hg
      omega

/-! ## §5c handleBlockLineBreak production

  Production theorem for `collectPlainScalar_handleBlockLineBreak`:
  `SBBreak + GStar (SLEmpty 0 .flowIn) + SFlowLinePrefix 0 + corr`.
  Analogous to `foldQuotedNewlines_prod` (§1e) for flow context. -/
lemma handleBlockLineBreak_prod (sc : ScannerState) (sp : SurfPos) (c : Char)
    (content : String) (contentIndent inputEnd : Nat)
    {content' : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true)
    (hblk : collectPlainScalar_handleBlockLineBreak sc content contentIndent inputEnd
            = some (content', s')) :
    ∃ sp₁ sp₂ sp',
      SBBreak sp sp₁ ∧
      GStar (SLEmpty 0 .flowIn) sp₁ sp₂ ∧
      SFlowLinePrefix 0 sp₂ sp' ∧
      ScannerSurfCorr s' sp' := by
  -- Step 1: consumeNewline → SBBreak
  obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
    consumeNewline_sbreak_corr sc sp c hcorr hpeek hlb
  -- Step 2: skipBlankLinesLoop → GStar (SLEmpty 0 .flowIn)
  obtain ⟨sp_loop, h_gstar_empty, hcorr_loop⟩ :=
    skipBlankLinesLoop_prod (consumeNewline sc) sp_cn 0 _ inputEnd hcorr_cn
  -- Step 3: skipSpaces (indent) then skipWhitespace (separation, my B3 fix).
  -- The returned state now sits past both, so build `SFlowLinePrefix 0` from the
  -- combined `GStar SSWhite` (indent-spaces ++ separation-white).
  obtain ⟨n_sk, sp_sk, h_indent, hcorr_sk⟩ :=
    skipSpaces_corr
      (skipBlankLinesLoop (consumeNewline sc) 0
        (inputEnd - (consumeNewline sc).offset + 1) inputEnd).2
      sp_loop hcorr_loop
  obtain ⟨sp_ws, h_gstar_ws, hcorr_ws⟩ :=
    skipWhitespace_corr
      (skipSpaces (skipBlankLinesLoop (consumeNewline sc) 0
        (inputEnd - (consumeNewline sc).offset + 1) inputEnd).2)
      sp_sk hcorr_sk
  have h_gstar_all : GStar SSWhite sp_loop sp_ws :=
    gstar_sswhite_append (sindent_to_gstar_sswhite h_indent) h_gstar_ws
  -- Unfold to trace through the definition
  unfold collectPlainScalar_handleBlockLineBreak at hblk
  dsimp only [] at hblk
  split at hblk
  · exact absurd hblk (by simp)
  · split at hblk
    · exact absurd hblk (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at hblk
      obtain ⟨-, rfl⟩ := hblk
      exact ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty,
             gstar_sswhite_to_flowlineprefix0 h_gstar_all, hcorr_ws⟩

/-! ## §5c' Line monotonicity of the plain-scalar walk (item 15)

  The implicit-key arm needs the ONE-LINE reading of a plain scalar: a walk
  whose final line equals its entry line appended no `s-ns-plain-next-line`.
  The witness is line arithmetic — every next-line append routes through a
  fold helper whose first step is `consumeNewline` (strictly +1), and the
  walk never decreases the line — so a same-line exit refutes the fold arms
  outright.  These are the `_line_*` facts that induction consumes. -/

-- `advance` on a break character moves to the next line.
lemma advance_line_succ_of_break (s : ScannerState) (c : Char)
    (hp : s.peek? = some c) (hlb : isLineBreakBool c = true) :
    s.advance.line = s.line + 1 := by
  have hlt : s.offset < s.inputEnd := peek_some_has_more hp
  have hc : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
    unfold ScannerState.peek? at hp; rw [ite_eq_left hlt] at hp; injection hp
  simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
             Bool.or_eq_true, beq_iff_eq] at hlb
  unfold ScannerState.advance
  rw [ite_eq_left hlt]
  dsimp only []
  rw [hc]
  rcases hlb with rfl | rfl <;> simp

-- `consumeNewline` at a break character moves to the next line exactly once
-- (the CRLF second byte is skipped by raw offset, not a second advance).
lemma consumeNewline_line_succ (s : ScannerState) (c : Char)
    (hp : s.peek? = some c) (hlb : isLineBreakBool c = true) :
    (consumeNewline s).line = s.line + 1 := by
  unfold consumeNewline
  split
  · rename_i heq
    show ({ s.advance with needIndentCheck := true }).line = s.line + 1
    exact advance_line_succ_of_break s '\n' heq (by native_decide)
  · rename_i heq
    have hadv : s.advance.line = s.line + 1 :=
      advance_line_succ_of_break s '\r' heq (by native_decide)
    dsimp only []
    split
    · exact hadv
    · exact hadv
  · rename_i hne1 hne2
    exfalso
    simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
               Bool.or_eq_true, beq_iff_eq] at hlb
    rcases hlb with rfl | rfl
    · exact hne1 hp
    · exact hne2 hp

-- `skipBlankLinesLoop` never returns to an earlier line.
lemma skipBlankLinesLoop_line_ge (s : ScannerState) (cnt fuel inputEnd : Nat) :
    s.line ≤ (skipBlankLinesLoop s cnt fuel inputEnd).2.line := by
  induction fuel generalizing s cnt with
  | zero => exact Nat.le_refl _
  | succ fuel' ih =>
    unfold skipBlankLinesLoop
    dsimp only
    split
    · rename_i c hpk
      split
      · rename_i hlb
        have h1 : (skipWhitespace s).line = s.line := skipWhitespace_preserves_line s
        have h2 := consumeNewline_line_succ (skipWhitespace s) c hpk hlb
        have h3 := ih (consumeNewline (skipWhitespace s)) (cnt + 1)
        -- item 100: the gate's arm rests on the same line
        split
        · exact Nat.le_refl _
        · omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _

-- `foldQuotedNewlinesLoop` never returns to an earlier line.
lemma foldQuotedNewlinesLoop_line_ge (s : ScannerState) (ec fuel : Nat) :
    s.line ≤ (foldQuotedNewlinesLoop s ec fuel).1.line := by
  induction fuel generalizing s ec with
  | zero => exact Nat.le_refl _
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    dsimp only
    split
    · rename_i c hpk
      split
      · rename_i hlb
        split
        · exact Nat.le_refl _
        · have h1 : (skipWhitespace s).line = s.line := skipWhitespace_preserves_line s
          have h2 := consumeNewline_line_succ (skipWhitespace s) c hpk hlb
          have h3 := ih (consumeNewline (skipWhitespace s)) (ec + 1)
          omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _

-- A successful flow fold lands strictly past its entry line: its first step is
-- `consumeNewline` (+1) and nothing after it moves back.
lemma foldQuotedNewlines_line_lt {s : ScannerState} {c : Char}
    {folded : String} {s' : ScannerState}
    (hp : s.peek? = some c) (hlb : isLineBreakBool c = true)
    (hfold : foldQuotedNewlines s = .ok (folded, s')) :
    s.line < s'.line := by
  unfold foldQuotedNewlines at hfold
  simp only [bind, Except.bind, pure, Except.pure] at hfold
  have h1 := consumeNewline_line_succ s c hp hlb
  have h2 := foldQuotedNewlinesLoop_line_ge (consumeNewline s) 0
    (s.inputEnd - (consumeNewline s).offset + 1)
  split at hfold
  · split at hfold
    · exact absurd hfold (by simp)
    · split at hfold <;>
      · have h := Except.ok.inj hfold
        have h3 : (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0
            (s.inputEnd - (consumeNewline s).offset + 1)).1).line
            = (foldQuotedNewlinesLoop (consumeNewline s) 0
            (s.inputEnd - (consumeNewline s).offset + 1)).1.line :=
          skipSpaces_preserves_line _
        have h4 := skipWhitespace_preserves_line (skipSpaces
          (foldQuotedNewlinesLoop (consumeNewline s) 0
            (s.inputEnd - (consumeNewline s).offset + 1)).1)
        have h5 : s' = skipWhitespace (skipSpaces
            (foldQuotedNewlinesLoop (consumeNewline s) 0
              (s.inputEnd - (consumeNewline s).offset + 1)).1) :=
          congrArg Prod.snd h.symm
        rw [h5, h4, h3]
        omega
  · split at hfold <;>
    · have h := Except.ok.inj hfold
      have h3 : (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0
          (s.inputEnd - (consumeNewline s).offset + 1)).1).line
          = (foldQuotedNewlinesLoop (consumeNewline s) 0
          (s.inputEnd - (consumeNewline s).offset + 1)).1.line :=
        skipSpaces_preserves_line _
      have h4 := skipWhitespace_preserves_line (skipSpaces
        (foldQuotedNewlinesLoop (consumeNewline s) 0
          (s.inputEnd - (consumeNewline s).offset + 1)).1)
      have h5 : s' = skipWhitespace (skipSpaces
          (foldQuotedNewlinesLoop (consumeNewline s) 0
            (s.inputEnd - (consumeNewline s).offset + 1)).1) :=
        congrArg Prod.snd h.symm
      rw [h5, h4, h3]
      omega

-- A continuing block fold lands strictly past its entry line.
lemma handleBlockLineBreak_line_lt {s : ScannerState} {c : Char}
    {content : String} {contentIndent inputEnd : Nat}
    {content' : String} {s' : ScannerState}
    (hp : s.peek? = some c) (hlb : isLineBreakBool c = true)
    (hblk : collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd
            = some (content', s')) :
    s.line < s'.line := by
  unfold collectPlainScalar_handleBlockLineBreak at hblk
  dsimp only [] at hblk
  have h1 := consumeNewline_line_succ s c hp hlb
  have h2 := skipBlankLinesLoop_line_ge (consumeNewline s) 0
    (inputEnd - (consumeNewline s).offset + 1) inputEnd
  have h3 := skipSpaces_preserves_line
    (skipBlankLinesLoop (consumeNewline s) 0
      (inputEnd - (consumeNewline s).offset + 1) inputEnd).2
  split at hblk
  · exact absurd hblk (by simp)
  · split at hblk
    · exact absurd hblk (by simp)
    · have h := Option.some.inj hblk
      have h5 : s' = skipWhitespace (skipSpaces
          (skipBlankLinesLoop (consumeNewline s) 0
            (inputEnd - (consumeNewline s).offset + 1) inputEnd).2) :=
        congrArg Prod.snd h.symm
      have h4 := skipWhitespace_preserves_line (skipSpaces
        (skipBlankLinesLoop (consumeNewline s) 0
          (inputEnd - (consumeNewline s).offset + 1) inputEnd).2)
      rw [h5, h4, h3]
      omega

-- The whole plain-scalar walk never returns to an earlier line.
lemma collectPlainScalarLoop_line_le (sc : ScannerState) (content spaces : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat)
    {result : PlainScalarResult}
    (hok : collectPlainScalarLoop sc content spaces fuel inFlow contentIndent inputEnd
           = .ok result) :
    sc.line ≤ result.state.line := by
  induction fuel generalizing sc content spaces with
  | zero =>
    simp [collectPlainScalarLoop] at hok; subst hok; exact Nat.le_refl _
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at hok
    split at hok
    · have h := Except.ok.inj hok; subst h; exact Nat.le_refl _
    · rename_i c hpeek
      split at hok
      · rename_i r_term h_term
        have h := Except.ok.inj hok; subst h
        rw [terminates_state_eq c sc content spaces inFlow r_term h_term]
        exact Nat.le_refl _
      · rename_i h_term_none
        split at hok
        · rename_i hlb
          split at hok
          · simp only [bind, Except.bind] at hok
            split at hok <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk folded s_fold =>
              split at hok
              · have h := Except.ok.inj hok; subst h; exact Nat.le_refl _
              · -- item 50: the flow floor's throw contradicts `.ok`
                split at hok
                · cases hok
                generalize h_loop : collectPlainScalarLoop s_fold _ "" fuel' inFlow
                  contentIndent inputEnd = cont_result at hok
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at hok
                  split at hok
                  · have h := Except.ok.inj hok; subst h; exact Nat.le_refl _
                  · have h := Except.ok.inj hok; subst h
                    have h1 := foldQuotedNewlines_line_lt hpeek hlb heq
                    have h2 := ih s_fold _ "" h_loop
                    omega
                | error e => simp at hok
          · split at hok
            · have h := Except.ok.inj hok; subst h; exact Nat.le_refl _
            · rename_i content' s'' hblk
              split at hok
              · have h := Except.ok.inj hok; subst h; exact Nat.le_refl _
              · generalize h_loop : collectPlainScalarLoop s'' content' "" fuel' inFlow
                  contentIndent inputEnd = cont_result at hok
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at hok
                  split at hok
                  · have h := Except.ok.inj hok; subst h; exact Nat.le_refl _
                  · have h := Except.ok.inj hok; subst h
                    have h1 := handleBlockLineBreak_line_lt hpeek hlb hblk
                    have h2 := ih s'' content' "" h_loop
                    omega
                | error e => simp at hok
        · split at hok
          · rename_i hws_char
            have hnl := isWhiteSpace_not_newline c hws_char
            have hcr := isWhiteSpace_not_cr c hws_char
            have hadv := advance_preserves_line_of_ne_break sc c hpeek hnl hcr
            have h := ih sc.advance content (spaces.push c) hok
            omega
          · split at hok
            · have h := Except.ok.inj hok; subst h; exact Nat.le_refl _
            · rename_i h_unsafe
              have h_safe : isPlainSafeBool c inFlow = true := by
                cases hb : isPlainSafeBool c inFlow <;> simp_all
              have hnl := (isPlainSafe_not_newline h_safe).1
              have hcr := (isPlainSafe_not_newline h_safe).2
              have hadv := advance_preserves_line_of_ne_break sc c hpeek hnl hcr
              have h := ih sc.advance _ "" hok
              omega


/-- `ScannerSurfCorr` at a non-empty surface position: the scanner peeks its head. -/
lemma corr_peek_head {sc : ScannerState} {c : Char} {rest : List Char} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩) : sc.peek? = some c := by
  have hmore : sc.offset < sc.inputEnd := by
    cases Nat.lt_or_ge sc.offset sc.inputEnd with
    | inl h => exact h
    | inr h =>
      have := eof_corr sc _ hcorr (Nat.not_lt.mpr h)
      simp at this
  obtain ⟨c', rest', hchars, hpeek⟩ := peek_corr sc _ hcorr hmore
  simp only [List.cons.injEq] at hchars
  obtain ⟨rfl, rfl⟩ := hchars
  exact hpeek

/-- Item 71 under the corrected `[130]`: a `[132]` run at a landing the scanner shows is
    content (not white, not `#`) opens with a bare `ns-plain-char` — its first entry has
    no whites and is not `hash`. -/
lemma gplus_entries_at_landing {sc : ScannerState} {c : L4YAML.YamlContext} {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (h : GPlus (SNbNsPlainInLineEntry c) sp sp')
    (hland : ∀ ch, sc.peek? = some ch → isWhiteSpaceBool ch = false ∧ isLineBreakBool ch = false)
    (hnh : sc.peek? ≠ some '#') :
    ∃ s₄, SNsPlainChar c sp s₄ ∧ GStar (SNbNsPlainInLineEntry c) s₄ sp' := by
  cases h with
  | mk s₂ _ hfirst hrest =>
    cases hfirst with
    | mk s₁ _ hws hch =>
      cases hws with
      | nil _ => exact ⟨s₂, hch, hrest⟩
      | cons _ _ _ hw _ =>
        exfalso
        cases hw with
        | space rest col =>
          have := (hland ' ' (corr_peek_head hcorr)).1
          simp [isWhiteSpaceBool, isSpaceBool, isTabBool] at this
        | tab rest col =>
          have := (hland '\t' (corr_peek_head hcorr)).1
          simp [isWhiteSpaceBool, isSpaceBool, isTabBool] at this
    | hash _ hlit =>
      cases hlit
      exact absurd (corr_peek_head hcorr) hnh

/-- `[134]` from the scanner's fold: the landing's `[132]` run, split by
    `gplus_entries_at_landing` into the leading `ns-plain-char` and the rest. -/
lemma ssNsPlainNextLine_of_gplus (n : Nat) (c : L4YAML.YamlContext) {sc : ScannerState}
    (s s_ws s₁ s₂ s₃ s' : SurfPos)
    (hw : GStar SSWhite s s_ws) (hb : SBBreak s_ws s₁) (he : GStar (SLEmpty n .flowIn) s₁ s₂)
    (hp : SFlowLinePrefix n s₂ s₃) (hcorr : ScannerSurfCorr sc s₃)
    (hg : GPlus (SNbNsPlainInLineEntry c) s₃ s')
    (hland : ∀ ch, sc.peek? = some ch → isWhiteSpaceBool ch = false ∧ isLineBreakBool ch = false)
    (hnh : sc.peek? ≠ some '#') : SSNsPlainNextLine n c s s' := by
  obtain ⟨s₄, hch, hrest⟩ := gplus_entries_at_landing hcorr hg hland hnh
  exact SSNsPlainNextLine.mk n c s s_ws s₁ s₂ s₃ s₄ s' hw hb he hp hch hrest

-- Full production for `collectPlainScalarLoop`: given accumulated whitespace
-- `GStar SSWhite sp_ent sp`, produces inline entries and trailing WS.
-- Parameterized over `inFlow` for both block and flow contexts.
-- Item 15 adds the ONE-LINE conjunct: a walk that exits on its entry line
-- appended no `s-ns-plain-next-line` — `sp_next = sp_entries`.
/-- Every `some` arm of `collectPlainScalar_terminates?` is TERMINATED. -/
lemma terminates?_terminated {c : Char} {s : ScannerState} {content spaces : String}
    {inFlow : Bool} {r : PlainScalarResult}
    (h : collectPlainScalar_terminates? c s content spaces inFlow = some r) :
    r.terminated = true := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · injection h with h; subst h; rfl
  · split at h
    · simp only [] at h
      split at h <;> split at h <;>
        first
          | (injection h with h; subst h; rfl)
          | cases h
    · split at h
      · injection h with h; subst h; rfl
      · split at h
        · injection h with h; subst h; rfl
        · cases h

private lemma foldQuotedNewlines_progress {s s' : ScannerState} {folded : String} {c : Char}
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true)
    (h : foldQuotedNewlines s = .ok (folded, s')) : s.offset < s'.offset := by
  have hcn := (consumeNewline_offset_advance s c hpk hbr).1
  have h1 := ScannerCorrectness.foldQuotedNewlinesLoop_offset_ge (consumeNewline s) 0
    (s.inputEnd - (consumeNewline s).offset + 1)
  have h2 := ScannerCorrectness.skipSpaces_offset_ge (foldQuotedNewlinesLoop (consumeNewline s) 0
    (s.inputEnd - (consumeNewline s).offset + 1)).1
  have h3 := ScannerCorrectness.skipWhitespace_offset_ge (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0
    (s.inputEnd - (consumeNewline s).offset + 1)).1)
  unfold foldQuotedNewlines at h
  dsimp only at h
  have hs' : s' = skipWhitespace (skipSpaces
      (foldQuotedNewlinesLoop (consumeNewline s) 0
        (s.inputEnd - (consumeNewline s).offset + 1)).1) → s.offset < s'.offset := by
    intro he; rw [he]; omega
  split at h
  · split at h
    · simp only [pure, Except.pure] at h
      split at h <;> contradiction
    · exact hs' (by
        split at h <;>
          (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm))
  · exact hs' (by
      split at h <;>
        (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm))

private lemma handleBlockLineBreak_progress' {s s' : ScannerState} {content content' : String}
    {ci ie : Nat} {c : Char}
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true)
    (h : collectPlainScalar_handleBlockLineBreak s content ci ie = some (content', s')) :
    s.offset < s'.offset := by
  have hcn := (consumeNewline_offset_advance s c hpk hbr).1
  have h1 := ScannerCorrectness.skipBlankLinesLoop_offset_ge (consumeNewline s) 0
    (ie - (consumeNewline s).offset + 1) ie
  have h2 := ScannerCorrectness.skipSpaces_offset_ge (skipBlankLinesLoop (consumeNewline s) 0
    (ie - (consumeNewline s).offset + 1) ie).2
  have h3 := ScannerCorrectness.skipWhitespace_offset_ge (skipSpaces (skipBlankLinesLoop (consumeNewline s) 0
    (ie - (consumeNewline s).offset + 1) ie).2)
  unfold collectPlainScalar_handleBlockLineBreak at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · have hs' : s' = skipWhitespace (skipSpaces
          (skipBlankLinesLoop (consumeNewline s) 0
            (ie - (consumeNewline s).offset + 1) ie).2) := by
        split at h <;>
          (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm)
      rw [hs']; omega

/-- With more fuel than remaining bytes the plain-scalar walk never exits on
    fuel: its result is TERMINATED (`scanPlainScalar` supplies twice the input). -/
lemma collectPlainScalarLoop_terminated_of_fuel (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (inFlow : Bool) (ci ie : Nat)
      (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel inFlow ci ie = .ok r →
    s.inputEnd - s.offset < fuel →
    r.terminated = true := by
  induction fuel with
  | zero => intro s _ _ _ _ _ r _ hb; omega
  | succ fuel' ih =>
    intro s content spaces inFlow ci ie r hok hb
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq; rfl
    · rename_i c hpk
      have hlt : s.offset < s.inputEnd := peek_some_has_more hpk
      split at hok
      · rename_i hterm
        injection hok with h_eq; subst h_eq
        exact terminates?_terminated hterm
      · split at hok
        · -- line break
          rename_i hbr
          split at hok
          · -- flow context: fold
            simp only [bind, Except.bind] at hok
            split at hok <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk folded s_fold =>
              split at hok
              · injection hok with h_eq; subst h_eq; rfl
              · split at hok
                · cases hok
                generalize h_loop : collectPlainScalarLoop s_fold _ "" fuel' inFlow ci ie
                  = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq; rfl
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    have hprog := foldQuotedNewlines_progress hpk hbr heq
                    have hend := foldQuotedNewlines_inputEnd heq
                    exact ih s_fold _ "" inFlow ci ie _ h_loop (by omega)
                | error e => simp at hok
          · -- block context
            split at hok
            · injection hok with h_eq; subst h_eq; rfl
            · rename_i content' s2 hblk
              have hprog := handleBlockLineBreak_progress' hpk hbr hblk
              have hend := handleBlockLineBreak_inputEnd hblk
              split at hok
              · injection hok with h_eq; subst h_eq; rfl
              · dsimp only [] at hok
                generalize h_loop : collectPlainScalarLoop s2 content' "" fuel' inFlow ci ie
                  = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq; rfl
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exact ih s2 content' "" inFlow ci ie _ h_loop (by omega)
                | error e => simp at hok
        · split at hok
          · -- whitespace: advance
            have hadv := advance_offset_lt s hlt
            have hend2 := advance_inputEnd s
            exact ih s.advance content _ inFlow ci ie r hok (by omega)
          · split at hok
            · injection hok with h_eq; subst h_eq; rfl
            · -- plain-safe content: advance
              simp only [] at hok
              have hadv := advance_offset_lt s hlt
              have hend2 := advance_inputEnd s
              exact ih s.advance _ "" inFlow ci ie r hok (by omega)

/-- `collectPlainScalar_terminates?` stops on `#` only with buffered whites
    (its other arms need `:`, a flow indicator, or a document marker). -/
lemma terminates_hash_spaces_pos (s : ScannerState) (content spaces : String)
    (inFlow : Bool) (r : PlainScalarResult)
    (h : collectPlainScalar_terminates? '#' s content spaces inFlow = some r)
    (hcol0 : spaces.length = 0 → s.col > 0) : spaces.length > 0 := by
  by_cases hpos : spaces.length > 0
  · exact hpos
  · exfalso
    have hz : spaces.length = 0 := by omega
    have hc := hcol0 hz
    unfold collectPlainScalar_terminates? at h
    simp [hz, isFlowIndicatorBool] at h
    omega

lemma gstar_sswhite_col_ge' (sp sp' : SurfPos) (h : GStar SSWhite sp sp') :
    sp'.col ≥ sp.col := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ _ _ hw _ ih => cases hw <;> simp only at ih ⊢ <;> omega

lemma collectPlainScalarLoop_prod (sc : ScannerState) (sp : SurfPos)
    (content spaces : String) (fuel : Nat)
    (contentIndent inputEnd : Nat)
    (sp_ent : SurfPos) (inFlow : Bool)
    (hcorr : ScannerSurfCorr sc sp)
    (h_ws : GStar SSWhite sp_ent sp)
    (h_sp : spaces.length = 0 → sp_ent = sp)
    (h_hash_col : sc.peek? = some '#' → spaces.length = 0 → sc.col > 0)
    (h_sp_len : spaces.length > 0 → sp_ent ≠ sp)
    (h_ie : sc.inputEnd ≤ inputEnd)
    -- Item 100: in BLOCK context the continuation floor sits above the block
    -- indent (`minContentIndentOf`'s own arithmetic), which is what says a
    -- blank line the fold's §6.1 gate stopped at is under-indented — so the
    -- handler ended the scalar there rather than folding it.
    (hcin : inFlow = false → (sc.currentIndent : Int) < (contentIndent : Int))
    {result : PlainScalarResult}
    (hok : collectPlainScalarLoop sc content spaces fuel inFlow contentIndent inputEnd
           = .ok result) :
    ∃ sp_entries sp_next sp_trail,
      GStar (SNbNsPlainInLineEntry (ctxOfInFlow inFlow)) sp_ent sp_entries ∧
      GStar (SSNsPlainNextLine 0 (ctxOfInFlow inFlow)) sp_entries sp_next ∧
      GStar SSWhite sp_next sp_trail ∧
      ScannerSurfCorr result.state sp_trail ∧
      -- N3: a `#` stop needs buffered whites, so an EMPTY trailing run never
      -- parks the scanner on `#` (the whites of `a #b` are the run).
      (result.terminated = true → sp_next = sp_trail → result.state.peek? ≠ some '#') ∧
      (result.state.line = sc.line → sp_next = sp_entries) ∧
      ((∀ ch, sc.peek? = some ch →
          isWhiteSpaceBool ch = false ∧ isLineBreakBool ch = false) →
        content.length < result.content.length →
        GPlus (SNbNsPlainInLineEntry (ctxOfInFlow inFlow)) sp_ent sp_entries) := by
  induction fuel generalizing sc sp content spaces sp_ent with
  | zero =>
    simp [collectPlainScalarLoop] at hok; subst hok
    exact ⟨sp_ent, sp_ent, sp, GStar.nil _, GStar.nil _, h_ws, hcorr,
      fun ht => absurd ht Bool.false_ne_true, fun _ => rfl,
      fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at hok
    split at hok
    · -- peek? = none (EOF)
      have h := Except.ok.inj hok; subst h
      exact ⟨sp_ent, sp_ent, sp, GStar.nil _, GStar.nil _, h_ws, hcorr,
      (fun _ _ hpk => by
        have hnone : sc.peek? = none := by assumption
        simp [hnone] at hpk),
      fun _ => rfl,
      fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
    · -- peek? = some c
      rename_i c hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      have hmore := peek_some_has_more hpeek
      subst hsp_eq
      split at hok
      · -- terminates? = some
        rename_i r_term h_term
        have h := Except.ok.inj hok; subst h
        rw [terminates_state_eq c sc content spaces inFlow r_term h_term]
        exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
               h_ws, hcorr,
               (fun _ heq hpk => by
                 simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                 exact h_sp_len (terminates_hash_spaces_pos sc content spaces inFlow r_term
                   h_term (h_hash_col hpeek)) heq),
               fun _ => rfl,
               fun _ hlen => absurd hlen (by
                 rw [terminates_content_eq c sc content spaces inFlow r_term h_term]
                 exact Nat.lt_irrefl _)⟩
      · -- terminates? = none
        rename_i h_term_none
        split at hok
        · -- isLineBreakBool c = true
          split at hok
          · -- inFlow = true: flow line break (foldQuotedNewlines)
            simp only [bind, Except.bind] at hok
            split at hok <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk folded s_fold =>
              split at hok
              · -- s_fold.peek? = some '#': terminate → state = sc
                have h := Except.ok.inj hok; subst h
                exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
                       h_ws, hcorr, (fun _ _ hpk => by
                         simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                         first
                         | (have hlb' : isLineBreakBool '#' = true := by assumption
                            exact absurd hlb' (by decide))
                         | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                            cases inFlow <;> exact absurd hps (by decide))),
                       fun _ => rfl,
                       fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
              · -- s_fold.peek? ≠ '#': recurse with content-length check
                rename_i hfoldpeek
                -- item 50: the flow floor's throw contradicts `.ok`
                split at hok
                · cases hok
                generalize h_loop : collectPlainScalarLoop s_fold _ "" fuel' inFlow
                  contentIndent inputEnd = cont_result at hok
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at hok
                  split at hok
                  · -- ≤ prevLen: no content grew → state = sc
                    have h := Except.ok.inj hok; subst h
                    exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
                           h_ws, hcorr, (fun _ _ hpk => by
                             simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                             first
                             | (have hlb' : isLineBreakBool '#' = true := by assumption
                                exact absurd hlb' (by decide))
                             | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                                cases inFlow <;> exact absurd hps (by decide))),
                           fun _ => rfl,
                           fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
                  · -- > prevLen: content grew → flow multi-line production
                    rename_i h_grew
                    have h_eq := Except.ok.inj hok; subst h_eq
                    have hlb : isLineBreakBool c = true := by assumption
                    have h_inf : inFlow = true := by assumption
                    simp only [h_inf, ctxOfInFlow]
                    -- Get fold production: SBBreak + GStar SLEmpty + SFlowLinePrefix + corr
                    obtain ⟨sp₁, sp₂, sp_fold, h_sbreak, h_gstar_empty, h_flp, hcorr_fold⟩ :=
                      foldQuotedNewlines_prod sc ⟨c :: rest, sc.col⟩ c hcorr hpeek hlb heq
                    -- Get IH result for recursive call
                    have h_ctx : ctxOfInFlow inFlow = .flowIn := by simp [ctxOfInFlow, h_inf]
                    obtain ⟨sp_entries_ih, sp_next_ih, sp_trail_ih,
                            h_entries_ih, h_next_ih, h_ws_ih, hcorr_ih, h_hash_ih, -, h_plus_ih⟩ :=
                      h_ctx ▸ ih s_fold sp_fold _ "" sp_fold hcorr_fold (GStar.nil _)
                        (fun _ => rfl)
                        (fun hpk _ => absurd hpk hfoldpeek)
                        (fun h => by simp at h)
                        (by rw [foldQuotedNewlines_inputEnd heq]; exact h_ie)
                        (fun hnf => absurd hnf (by simp [h_inf])) h_loop
                    -- Item 71: `[134]` demands an `ns-plain-char` on the continuation
                    -- line.  The fold lands on neither `s-white` nor a break, so the
                    -- scanner's own content-length check IS that character.
                    have h_entries_plus := h_plus_ih (foldQuotedNewlines_landing heq)
                      (Nat.lt_of_not_le h_grew)
                    -- Build SSNsPlainNextLine 0 .flowIn.  The one-line conjunct
                    -- refutes its hypothesis: the fold strictly advanced the line
                    -- and the inner walk never moves back (item 15).
                    exact ⟨sp_ent, sp_next_ih, sp_trail_ih,
                           GStar.nil _,
                           GStar.cons sp_ent sp_entries_ih sp_next_ih
                             (ssNsPlainNextLine_of_gplus 0 .flowIn
                               sp_ent ⟨c :: rest, sc.col⟩ sp₁ sp₂ sp_fold sp_entries_ih
                               h_ws h_sbreak h_gstar_empty h_flp hcorr_fold h_entries_plus
                               (foldQuotedNewlines_landing heq) hfoldpeek)
                             h_next_ih,
                           h_ws_ih,
                           hcorr_ih,
                           h_hash_ih,
                           fun h_same => False.elim (by
                             have h1 := foldQuotedNewlines_line_lt hpeek hlb heq
                             have h2 := collectPlainScalarLoop_line_le s_fold _ "" fuel'
                               inFlow contentIndent inputEnd h_loop
                             omega),
                           fun hpre _ => by simp [(hpre c hpeek).2] at hlb⟩
                | error e => simp at hok
          · -- inFlow = false: block line break (handleBlockLineBreak)
            rename_i h_notflow
            have h_nf : inFlow = false := by
              revert h_notflow; cases inFlow <;> simp
            split at hok
            · -- handleBlockLineBreak = none: terminate → state = sc
              have h := Except.ok.inj hok; subst h
              exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
                     h_ws, hcorr, (fun _ _ hpk => by
                       simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                       first
                       | (have hlb' : isLineBreakBool '#' = true := by assumption
                          exact absurd hlb' (by decide))
                       | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                          cases inFlow <;> exact absurd hps (by decide))),
                     fun _ => rfl,
                     fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
            · -- handleBlockLineBreak = some (content', s')
              rename_i content' s' hblk
              split at hok
              · -- s'.peek? = some '#': terminate → state = sc
                have h := Except.ok.inj hok; subst h
                exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
                       h_ws, hcorr, (fun _ _ hpk => by
                         simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                         first
                         | (have hlb' : isLineBreakBool '#' = true := by assumption
                            exact absurd hlb' (by decide))
                         | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                            cases inFlow <;> exact absurd hps (by decide))),
                       fun _ => rfl,
                       fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
              · -- s'.peek? ≠ '#': recurse with content-length check
                rename_i hblkpeek
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow
                  contentIndent inputEnd = cont_result at hok
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at hok
                  split at hok
                  · -- ≤ prevLen: no content grew → state = sc
                    have h := Except.ok.inj hok; subst h
                    exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
                           h_ws, hcorr, (fun _ _ hpk => by
                             simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                             first
                             | (have hlb' : isLineBreakBool '#' = true := by assumption
                                exact absurd hlb' (by decide))
                             | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                                cases inFlow <;> exact absurd hps (by decide))),
                           fun _ => rfl,
                           fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
                  · -- > prevLen: content grew → block multi-line production
                    rename_i h_grew
                    have h_eq := Except.ok.inj hok; subst h_eq
                    have hlb : isLineBreakBool c = true := by assumption
                    -- Get block line break production
                    obtain ⟨sp₁, sp₂, sp_fold, h_sbreak, h_gstar_empty, h_flp, hcorr_fold⟩ :=
                      handleBlockLineBreak_prod sc ⟨c :: rest, sc.col⟩ c content
                        contentIndent inputEnd hcorr hpeek hlb hblk
                    -- Get IH result for recursive call
                    obtain ⟨sp_entries_ih, sp_next_ih, sp_trail_ih,
                            h_entries_ih, h_next_ih, h_ws_ih, hcorr_ih, h_hash_ih, -, h_plus_ih⟩ :=
                      ih s' sp_fold content' "" sp_fold hcorr_fold (GStar.nil _)
                        (fun _ => rfl)
                        (fun hpk _ => absurd hpk hblkpeek)
                        (fun h => by simp at h)
                        (by rw [handleBlockLineBreak_inputEnd hblk]; exact h_ie)
                        (fun hnf => by
                          have hci : s'.currentIndent = sc.currentIndent := by
                            simp only [ScannerState.currentIndent,
                              handleBlockLineBreak_indents' hblk]
                          rw [hci]; exact hcin hnf) h_loop
                    -- Item 71: the block fold also lands on a content character.
                    have h_entries_plus :=
                      h_plus_ih
                        (handleBlockLineBreak_landing (by omega)
                          (handleBlockLineBreak_gate_false
                            (hcin h_nf) hblk) hblk)
                        (Nat.lt_of_not_le h_grew)
                    -- Build SSNsPlainNextLine 0 (ctxOfInFlow inFlow).  One-line
                    -- conjunct: the fold strictly advanced the line (item 15).
                    exact ⟨sp_ent, sp_next_ih, sp_trail_ih,
                           GStar.nil _,
                           GStar.cons sp_ent sp_entries_ih sp_next_ih
                             (ssNsPlainNextLine_of_gplus 0 (ctxOfInFlow inFlow)
                               sp_ent ⟨c :: rest, sc.col⟩ sp₁ sp₂ sp_fold sp_entries_ih
                               h_ws h_sbreak h_gstar_empty h_flp hcorr_fold h_entries_plus
                               (handleBlockLineBreak_landing (by omega)
                                 (handleBlockLineBreak_gate_false (hcin h_nf) hblk) hblk)
                               hblkpeek)
                             h_next_ih,
                           h_ws_ih,
                           hcorr_ih,
                           h_hash_ih,
                           fun h_same => False.elim (by
                             have h1 := handleBlockLineBreak_line_lt hpeek hlb hblk
                             have h2 := collectPlainScalarLoop_line_le s' content' "" fuel'
                               inFlow contentIndent inputEnd h_loop
                             omega),
                           fun hpre _ => by simp [(hpre c hpeek).2] at hlb⟩
                | error e => simp at hok
        · -- not line break
          split at hok
          · -- whitespace: extend accumulated WS and recurse
            have hws_char : isWhiteSpaceBool c = true := by assumption
            have hnl := isWhiteSpace_not_newline c hws_char
            have hcr := isWhiteSpace_not_cr c hws_char
            have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
            have hw : SSWhite ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ := by
              simp [isWhiteSpaceBool, isSpaceBool, isTabBool, Bool.or_eq_true,
                beq_iff_eq] at hws_char
              rcases hws_char with rfl | rfl
              · exact SSWhite.space rest sc.col
              · exact SSWhite.tab rest sc.col
            obtain ⟨sp_entries_r, sp_next_r, sp_trail_r, h_ent_r, h_next_r, h_ws_r,
                    hcorr_r, h_hash_r, h_one_r, -⟩ :=
              ih sc.advance ⟨rest, sc.col + 1⟩ content (spaces.push c) sp_ent
                hcorr_adv (gstar_sswhite_append h_ws (GStar.cons _ _ _ hw (GStar.nil _)))
                (fun hlen => by simp [String.length_push] at hlen)
                (fun _ hlen => by simp [String.length_push] at hlen)
                (fun _ heq => by
                  have hle := gstar_sswhite_col_ge' sp_ent ⟨c :: rest, sc.col⟩ h_ws
                  rw [heq] at hle; dsimp only at hle; omega)
                (by rw [advance_inputEnd]; exact h_ie)
                (fun hnf => by
                  simp only [ScannerState.currentIndent,
                    L4YAML.Proofs.EmitterScannability.advance_preserves_indents]
                  exact hcin hnf)
                hok
            exact ⟨sp_entries_r, sp_next_r, sp_trail_r, h_ent_r, h_next_r, h_ws_r, hcorr_r,
                   h_hash_r,
                   fun h_same => h_one_r (by
                     rw [advance_preserves_line_of_ne_break sc c hpeek hnl hcr]
                     exact h_same),
                   fun hpre _ => by simp [(hpre c hpeek).1] at hws_char⟩
          · -- not whitespace
            split at hok
            · -- not plain safe: terminate
              have h := Except.ok.inj hok; subst h
              exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, GStar.nil _,
                     h_ws, hcorr, (fun _ _ hpk => by
                       simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                       first
                       | (have hlb' : isLineBreakBool '#' = true := by assumption
                          exact absurd hlb' (by decide))
                       | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                          cases inFlow <;> exact absurd hps (by decide))),
                     fun _ => rfl,
                     fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
            · -- content char: form grammar entry and recurse
              have h_safe : isPlainSafeBool c inFlow = true := by
                cases hb : isPlainSafeBool c inFlow <;> simp_all
              have hnl := (isPlainSafe_not_newline h_safe).1
              have hcr := (isPlainSafe_not_newline h_safe).2
              have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
              -- Construct SNsPlainChar for the content character
              have h_entry : SNbNsPlainInLineEntry (ctxOfInFlow inFlow) sp_ent
                  ⟨rest, sc.col + 1⟩ := by
                by_cases hcolon : c = ':'
                · -- ':' followed by ns-plain-safe (colonSafe)
                  subst hcolon
                  obtain ⟨n, hpn, hnb, hfi, hprn, hbomn⟩ :=
                    colon_not_terminated_next sc content spaces inFlow h_term_none
                  unfold ScannerState.peekAt? at hpn
                  obtain ⟨pre, rest', hcs, hlen⟩ :=
                    peekAtLoop_some_chars hcorr.end_eq hpn (':' :: rest) hcorr.chars_from
                  have ⟨a, ha⟩ : ∃ a, pre = [a] := by
                    cases pre with
                    | nil => simp at hlen
                    | cons a as => cases as with
                      | nil => exact ⟨a, rfl⟩
                      | cons => simp at hlen
                  subst ha; simp at hcs
                  obtain ⟨ha', hrst⟩ := hcs; subst ha'; subst hrst
                  have h_ns_safe : isNsPlainSafe (ctxOfInFlow inFlow) n := by
                    cases inFlow with
                    | false => exact not_blank_to_nsChar hnb hprn hbomn
                    | true =>
                      exact ⟨not_blank_to_nsChar hnb hprn hbomn, fun hfp => by
                        have h1 := hfi rfl
                        have h2 := (isFlowIndicator_iff n).mpr hfp
                        simp [h1] at h2⟩
                  exact SNbNsPlainInLineEntry.mk _ sp_ent _ _ h_ws
                    (SNsPlainChar.colonSafe (ctxOfInFlow inFlow) '_' n rest' sc.col h_ns_safe)
                · by_cases hhash : c = '#'
                  · -- '#' at col=0: use h_hash_col precondition
                    subst hhash
                    have h_sp_zero : spaces.length = 0 := by
                      suffices ¬(spaces.length > 0) by omega
                      intro h_pos
                      have h_dec : decide (spaces.length > 0) = true :=
                        decide_eq_true_eq.mpr h_pos
                      unfold collectPlainScalar_terminates? at h_term_none
                      simp [h_dec] at h_term_none
                    have h_ent := h_sp h_sp_zero
                    subst h_ent
                    exact SNbNsPlainInLineEntry.hash _ _ _ (GLit.mk rest sc.col)
                  · -- safe: not ':' and not '#'
                    exact SNbNsPlainInLineEntry.mk _ sp_ent _ _ h_ws
                        (SNsPlainChar.safe (ctxOfInFlow inFlow) c rest sc.col
                          (isPlainSafe_to_nsPlainSafe h_safe) hcolon hhash)
              -- Recursive call with empty WS accumulator
              obtain ⟨sp_entries, sp_next, sp_trail, h_ent_rest, h_next_rest,
                      h_ws_rest, hcorr_rest, h_hash_rest, h_one_rest, -⟩ :=
                ih sc.advance ⟨rest, sc.col + 1⟩ _ "" ⟨rest, sc.col + 1⟩
                  hcorr_adv (GStar.nil _)
                  (fun _ => rfl)
                  (fun _ _ => by
                    have h : sc.col + 1 = sc.advance.col := hcorr_adv.col_eq
                    omega)
                  (fun h => by simp at h)
                  (by rw [advance_inputEnd]; exact h_ie)
                  (fun hnf => by
                    simp only [ScannerState.currentIndent,
                      L4YAML.Proofs.EmitterScannability.advance_preserves_indents]
                    exact hcin hnf)
                  hok
              exact ⟨sp_entries, sp_next, sp_trail,
                GStar.cons sp_ent ⟨rest, sc.col + 1⟩ sp_entries h_entry h_ent_rest,
                h_next_rest, h_ws_rest, hcorr_rest, h_hash_rest,
                fun h_same => h_one_rest (by
                  rw [advance_preserves_line_of_ne_break sc c hpeek hnl hcr]
                  exact h_same),
                fun _ _ =>
                  GPlus.mk sp_ent ⟨rest, sc.col + 1⟩ sp_entries h_entry h_ent_rest⟩

-- Helper: canStartPlainScalar → first char is not whitespace.
lemma canStartPlainScalar_not_ws {c : Char} {next : Option Char} {inFlow : Bool}
    (h : canStartPlainScalarBool c next inFlow = true) : isWhiteSpaceBool c = false := by
  unfold canStartPlainScalarBool at h
  split at h
  · rename_i hexc; rcases hexc with rfl | rfl | rfl <;> native_decide
  · revert h; cases isWhiteSpaceBool c <;> simp

-- Helper: GStar SSWhite starting at a non-WS char must be nil.
lemma gstar_sswhite_at_non_ws {c : Char} {rest : List Char} {col : Nat} {s₁ : SurfPos}
    (h : GStar SSWhite ⟨c :: rest, col⟩ s₁)
    (h_nws : isWhiteSpaceBool c = false) :
    s₁ = ⟨c :: rest, col⟩ := by
  cases h
  · rfl
  · rename_i sp_mid hw _; exfalso
    cases hw <;> simp [isWhiteSpaceBool, isSpaceBool, isTabBool] at h_nws

-- Helper: SNsPlainChar at ⟨c :: rest, col⟩ always produces ⟨rest, col + 1⟩.
lemma SNsPlainChar_at_head {c : Char} {rest : List Char} {col : Nat} {sp' : SurfPos}
    (h : SNsPlainChar .blockIn ⟨c :: rest, col⟩ sp') :
    sp' = ⟨rest, col + 1⟩ := by
  cases h <;> rfl

-- Context lift: SNsPlainChar .blockIn → .flowOut (definitional: isNsPlainSafe
-- .blockIn = isNsPlainSafe .flowOut = isNsChar for non-flow contexts).
lemma SNsPlainChar_blockIn_to_flowOut {sp sp' : SurfPos}
    (h : SNsPlainChar .blockIn sp sp') : SNsPlainChar .flowOut sp sp' := by
  cases h with
  | safe ch rest col hS hNC hNH =>
    exact SNsPlainChar.safe .flowOut ch rest col hS hNC hNH
  | colonSafe prev next rest col hS =>
    exact SNsPlainChar.colonSafe .flowOut prev next rest col hS

-- Context lift: SNbNsPlainInLineEntry .blockIn → .flowOut.
lemma SNbNsPlainInLineEntry_blockIn_to_flowOut {sp sp' : SurfPos}
    (h : SNbNsPlainInLineEntry .blockIn sp sp') : SNbNsPlainInLineEntry .flowOut sp sp' :=
  match h with
  | SNbNsPlainInLineEntry.mk _ _ s₁ _ ws_pre char =>
    SNbNsPlainInLineEntry.mk .flowOut _ s₁ _ ws_pre (SNsPlainChar_blockIn_to_flowOut char)
  | SNbNsPlainInLineEntry.hash _ _ _ hlit => SNbNsPlainInLineEntry.hash .flowOut _ _ hlit

-- Context lift: GStar (SNbNsPlainInLineEntry .blockIn) → GStar (...flowOut).
lemma GStar_entries_blockIn_to_flowOut {sp sp' : SurfPos}
    (h : GStar (SNbNsPlainInLineEntry .blockIn) sp sp') :
    GStar (SNbNsPlainInLineEntry .flowOut) sp sp' := by
  induction h with
  | nil => exact GStar.nil _
  | cons s₁ s₂ s₃ entry _ ih =>
    exact GStar.cons s₁ s₂ s₃ (SNbNsPlainInLineEntry_blockIn_to_flowOut entry) ih

-- Context lift: SNsPlainFirst .blockIn → .flowOut (avoids circular import
-- with NodeProduction.lean which has the same theorem).
lemma SNsPlainFirst_blockIn_to_flowOut' {s s' : SurfPos}
    (h : SNsPlainFirst .blockIn s s') : SNsPlainFirst .flowOut s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hNotInd =>
    exact SNsPlainFirst.nonIndicator .flowOut ch rest col hSafe hNotInd
  | dashSafe next rest col hSafe => exact SNsPlainFirst.dashSafe .flowOut next rest col hSafe
  | colonSafe next rest col hSafe => exact SNsPlainFirst.colonSafe .flowOut next rest col hSafe
  | questionSafe next rest col hSafe =>
    exact SNsPlainFirst.questionSafe .flowOut next rest col hSafe

-- Context lift: SNsPlainChar .flowIn → .flowOut (flowIn is more restrictive,
-- so isNsPlainSafe .flowIn c → isNsPlainSafe .flowOut c by dropping flow indicator exclusion).
lemma SNsPlainChar_flowIn_to_flowOut {sp sp' : SurfPos}
    (h : SNsPlainChar .flowIn sp sp') : SNsPlainChar .flowOut sp sp' := by
  cases h with
  | safe ch rest col hS hNC hNH =>
    exact SNsPlainChar.safe .flowOut ch rest col hS.1 hNC hNH
  | colonSafe prev next rest col hS =>
    exact SNsPlainChar.colonSafe .flowOut prev next rest col hS.1

-- Context lift: SNbNsPlainInLineEntry .flowIn → .flowOut.
lemma SNbNsPlainInLineEntry_flowIn_to_flowOut {sp sp' : SurfPos}
    (h : SNbNsPlainInLineEntry .flowIn sp sp') : SNbNsPlainInLineEntry .flowOut sp sp' :=
  match h with
  | SNbNsPlainInLineEntry.mk _ _ s₁ _ ws_pre char =>
    SNbNsPlainInLineEntry.mk .flowOut _ s₁ _ ws_pre (SNsPlainChar_flowIn_to_flowOut char)
  | SNbNsPlainInLineEntry.hash _ _ _ hlit => SNbNsPlainInLineEntry.hash .flowOut _ _ hlit

-- Context lift: GStar (SNbNsPlainInLineEntry .flowIn) → GStar (...flowOut).
lemma GStar_entries_flowIn_to_flowOut {sp sp' : SurfPos}
    (h : GStar (SNbNsPlainInLineEntry .flowIn) sp sp') :
    GStar (SNbNsPlainInLineEntry .flowOut) sp sp' := by
  induction h with
  | nil => exact GStar.nil _
  | cons s₁ s₂ s₃ entry _ ih =>
    exact GStar.cons s₁ s₂ s₃ (SNbNsPlainInLineEntry_flowIn_to_flowOut entry) ih

-- Context lift: SNsPlainFirst .flowIn → .flowOut.
lemma SNsPlainFirst_flowIn_to_flowOut {s s' : SurfPos}
    (h : SNsPlainFirst .flowIn s s') : SNsPlainFirst .flowOut s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hNotInd =>
    exact SNsPlainFirst.nonIndicator .flowOut ch rest col hSafe.1 hNotInd
  | dashSafe next rest col hSafe => exact SNsPlainFirst.dashSafe .flowOut next rest col hSafe.1
  | colonSafe next rest col hSafe => exact SNsPlainFirst.colonSafe .flowOut next rest col hSafe.1
  | questionSafe next rest col hSafe =>
    exact SNsPlainFirst.questionSafe .flowOut next rest col hSafe.1

-- Generic context lift: ctxOfInFlow inFlow → .flowOut (dispatches to block/flow lifts).
lemma SNsPlainFirst_ctxOfInFlow_to_flowOut {s s' : SurfPos} {inFlow : Bool}
    (h : SNsPlainFirst (ctxOfInFlow inFlow) s s') : SNsPlainFirst .flowOut s s' := by
  cases inFlow with
  | false => exact SNsPlainFirst_blockIn_to_flowOut' h
  | true => exact SNsPlainFirst_flowIn_to_flowOut h

lemma GStar_entries_ctxOfInFlow_to_flowOut {sp sp' : SurfPos} {inFlow : Bool}
    (h : GStar (SNbNsPlainInLineEntry (ctxOfInFlow inFlow)) sp sp') :
    GStar (SNbNsPlainInLineEntry .flowOut) sp sp' := by
  cases inFlow with
  | false => exact GStar_entries_blockIn_to_flowOut h
  | true => exact GStar_entries_flowIn_to_flowOut h

-- The same lift for `[134]`'s one-or-more entries (item 71).
lemma GPlus_entries_ctxOfInFlow_to_flowOut {sp sp' : SurfPos} {inFlow : Bool}
    (h : GPlus (SNbNsPlainInLineEntry (ctxOfInFlow inFlow)) sp sp') :
    GPlus (SNbNsPlainInLineEntry .flowOut) sp sp' := by
  cases h with
  | mk s₂ _ hfirst hrest =>
    refine GPlus.mk _ s₂ _ ?_ (GStar_entries_ctxOfInFlow_to_flowOut hrest)
    cases inFlow with
    | false => exact SNbNsPlainInLineEntry_blockIn_to_flowOut hfirst
    | true => exact SNbNsPlainInLineEntry_flowIn_to_flowOut hfirst

-- Context lift: SSNsPlainNextLine n (ctxOfInFlow inFlow) → SSNsPlainNextLine n .flowOut.
-- Only the entries component depends on context; SLEmpty uses hardcoded .flowIn.
lemma SSNsPlainNextLine_ctxOfInFlow_to_flowOut {n : Nat} {s s' : SurfPos} {inFlow : Bool}
    (h : SSNsPlainNextLine n (ctxOfInFlow inFlow) s s') :
    SSNsPlainNextLine n .flowOut s s' := by
  match h with
  | .mk _ _ _ _ _ _ _ _ _ h_ws h_break h_empty h_flp h_ch h_entries =>
    refine SSNsPlainNextLine.mk n .flowOut _ _ _ _ _ _ _ h_ws h_break h_empty h_flp ?_
      (GStar_entries_ctxOfInFlow_to_flowOut h_entries)
    cases inFlow with
    | false => exact SNsPlainChar_blockIn_to_flowOut h_ch
    | true => exact SNsPlainChar_flowIn_to_flowOut h_ch

-- Context lift for GStar of next-lines.
lemma GStar_SSNsPlainNextLine_ctxOfInFlow_to_flowOut
    {n : Nat} {s s' : SurfPos} {inFlow : Bool}
    (h : GStar (SSNsPlainNextLine n (ctxOfInFlow inFlow)) s s') :
    GStar (SSNsPlainNextLine n .flowOut) s s' := by
  induction h with
  | nil => exact GStar.nil _
  | cons _ _ _ hfirst _ ih =>
    exact GStar.cons _ _ _ (SSNsPlainNextLine_ctxOfInFlow_to_flowOut hfirst) ih

-- Whole-scalar context lift: SNsPlainMultiLine n (ctxOfInFlow inFlow) → n .flowOut.
-- Composes the three component lifts (first char, in-line entries, next lines),
-- so a native-context plain-scalar producer can be reused for both `.flowOut`
-- (top-level flow node) via this lift and `.flowIn` (flow-collection entry)
-- directly. Used by `scanPlainScalar_to_flowNode`.
lemma SNsPlainMultiLine_ctxOfInFlow_to_flowOut {n : Nat} {s s' : SurfPos} {inFlow : Bool}
    (h : SNsPlainMultiLine n (ctxOfInFlow inFlow) s s') :
    SNsPlainMultiLine n .flowOut s s' := by
  obtain ⟨s₁, _, h_one, h_next⟩ := h
  obtain ⟨s₂, _, h_first, h_entries⟩ := h_one
  exact SNsPlainMultiLine.mk n .flowOut _ _ _
    (SNsPlainOneLine.mk .flowOut _ _ _
      (SNsPlainFirst_ctxOfInFlow_to_flowOut h_first)
      (GStar_entries_ctxOfInFlow_to_flowOut h_entries))
    (GStar_SSNsPlainNextLine_ctxOfInFlow_to_flowOut h_next)

-- canStartPlainScalar → isPlainSafeBool (first char is plain safe)
lemma canStartPlain_implies_safe {c : Char} {next : Option Char} {inFlow : Bool}
    (h : canStartPlainScalarBool c next inFlow = true) :
    isPlainSafeBool c inFlow = true := by
  unfold canStartPlainScalarBool at h
  split at h
  · rename_i hexc
    rcases hexc with rfl | rfl | rfl <;> cases inFlow <;> native_decide
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨hind, hws⟩, hlb⟩, hpr⟩, hbom⟩ := h
    have hfi : isFlowIndicatorBool c = false := by
      cases h_fi : isFlowIndicatorBool c with
      | false => rfl
      | true =>
        have hind' : isIndicatorBool c = true := by
          simp [isFlowIndicatorBool, List.mem_cons] at h_fi
          rcases h_fi with rfl | rfl | rfl | rfl | rfl <;> decide
        simp [hind'] at hind
    unfold isPlainSafeBool
    split <;> simp [hws, hlb, hfi, hpr, hbom]

-- canStartPlainScalar → not a line break (Bool form)
lemma canStartPlain_not_linebreak {c : Char} {next : Option Char} {inFlow : Bool}
    (h : canStartPlainScalarBool c next inFlow = true) :
    isLineBreakBool c = false := by
  have hs := canStartPlain_implies_safe h
  cases inFlow <;> simp only [isPlainSafeBool, ite_true] at hs <;>
    (revert hs; cases isLineBreakBool c <;> simp)

-- First char satisfying canStartPlainScalar doesn't trigger terminates?
-- (given no document boundary at column 0).
lemma canStartPlain_first_not_terminates (c : Char) (sc : ScannerState) (inFlow : Bool)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false) :
    collectPlainScalar_terminates? c sc "" "" inFlow = none := by
  match h : collectPlainScalar_terminates? c sc "" "" inFlow with
  | none => rfl
  | some r =>
    exfalso
    unfold collectPlainScalar_terminates? at h
    split at h
    · -- '#' && "".length > 0: impossible (empty spaces)
      simp [String.length] at *
    · split at h
      · -- c == ':'
        rename_i h_colon
        have hceq : c = ':' := by simpa using h_colon
        subst hceq
        dsimp only [] at h
        split at h  -- match peekAt? 1
        · rename_i n hn
          rw [hn] at hstart
          cases inFlow with
          | false =>
            simp only [Bool.false_and, Bool.or_false] at h
            split at h
            · rename_i h_blank
              simp only [canStartPlainScalarBool, or_true, ↓reduceIte,
                          Bool.false_and, Bool.and_eq_true,
                          Bool.not_eq_true'] at hstart
              simp only [isBlankBool, Bool.or_eq_true] at h_blank
              rcases h_blank with h | h <;> simp_all
            · simp at h
          | true =>
            simp only [Bool.true_and] at h
            split at h
            · rename_i h_blank
              simp only [canStartPlainScalarBool, or_true, ↓reduceIte,
                          Bool.true_and, Bool.and_eq_true, Bool.not_eq_true'] at hstart
              simp only [isBlankBool, Bool.or_eq_true] at h_blank
              rcases h_blank with h | h <;> simp_all
            · simp at h
        · -- peekAt? 1 = none: canStart ':' none inFlow = false → contradiction
          rename_i h_none; rw [h_none] at hstart
          simp [canStartPlainScalarBool] at hstart
      · split at h
        · -- inFlow && isFlowIndicator
          rename_i h_flow_ind
          cases inFlow with
          | false => simp at h_flow_ind
          | true =>
            simp only [Bool.true_and] at h_flow_ind
            -- c is a flow indicator but canStart excludes indicators
            have hprop := (canStartPlainScalar_iff c (sc.peekAt? 1) true).mp hstart
            unfold canStartPlainScalarProp at hprop
            split at hprop
            · -- exception char: c ∈ {-, ?, :} — these are not flow indicators
              rename_i hexc
              rcases hexc with rfl | rfl | rfl <;>
                simp [isFlowIndicatorBool] at h_flow_ind
            · -- non-exception: ¬isIndicatorProp c
              have := hprop.1
              have := flowIndicatorProp_to_indicatorProp ((isFlowIndicator_iff c).mp h_flow_ind)
              contradiction
        · split at h
          · -- col == 0 && docBoundary: use h_not_doc
            rename_i h_doc
            simp only [Bool.and_eq_true, beq_iff_eq] at h_doc
            exact absurd h_doc.2 (by simp [h_not_doc h_doc.1])
          · simp at h

-- When the first char is valid content and terminates? = none, extract the
-- recursive call from collectPlainScalarLoop at fuel (n+1).
lemma collectPlainScalarLoop_content_first_step
    {c : Char} {sc : ScannerState} {fuel ci ie : Nat}
    {result : PlainScalarResult} {inFlow : Bool}
    (hpeek : sc.peek? = some c)
    (h_term : collectPlainScalar_terminates? c sc "" "" inFlow = none)
    (h_nlb : isLineBreakBool c = false)
    (h_nws : isWhiteSpaceBool c = false)
    (h_safe : isPlainSafeBool c inFlow = true)
    (hok : collectPlainScalarLoop sc "" "" (fuel + 1) inFlow ci ie = .ok result) :
    collectPlainScalarLoop sc.advance (String.singleton c) "" fuel inFlow ci ie
      = .ok result := by
  unfold collectPlainScalarLoop at hok
  -- fuel + 1 matches succ branch; sc.peek? = some c
  split at hok
  · simp [hpeek] at *
  · rename_i c' hpeek'; have : c' = c := by rw [hpeek] at hpeek'; exact Option.some.inj hpeek'.symm
    subst this
    split at hok
    · rename_i r h_term'; simp [h_term] at h_term'
    · split at hok
      · simp [h_nlb] at *
      · split at hok
        · simp [h_nws] at *
        · split at hok
          · simp [h_safe] at *
          · exact hok

-- Native-context core: scanPlainScalar → SNsPlainMultiLine 0 (ctxOfInFlow inFlow)
-- + trailing WS + corr. Composes: canStartPlainScalar → SNsPlainFirst, loop →
-- entries + trailing WS, entry decomposition → SNsPlainOneLine. Builds the
-- scalar in its NATIVE context (`.blockIn` when block, `.flowIn` when in a flow
-- collection) with NO context lift, so it can be reused for both `.flowOut`
-- (top-level flow node, via `SNsPlainMultiLine_ctxOfInFlow_to_flowOut`) and
-- `.flowIn` (flow-collection entry, directly under `inFlow = true`).
-- Requires: not at document boundary at column 0 (callers check this via
-- scanNextToken_dispatchStructural before reaching content dispatch).
lemma scanPlainScalar_to_multiLine_native (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp_gram sp', SNsPlainMultiLine 0 (ctxOfInFlow sc.inFlow) sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   (sp_gram = sp' → s'.peek? ≠ some '#') ∧
                   ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  have hrest_head : ∀ n, sc.peekAt? 1 = some n → ∃ rest', rest = n :: rest' := by
    intro n hn; unfold ScannerState.peekAt? at hn
    have hcorr' := hsp_eq ▸ hcorr
    obtain ⟨pre, rest', hcs, hlen⟩ :=
      peekAtLoop_some_chars hcorr'.end_eq hn (c :: rest) hcorr'.chars_from
    have ⟨a, ha⟩ : ∃ a, pre = [a] := by
      cases pre with
      | nil => simp at hlen
      | cons a as => cases as with
        | nil => exact ⟨a, rfl⟩
        | cons => simp at hlen
    subst ha; simp at hcs; obtain ⟨_, rfl⟩ := hcs; exact ⟨rest', rfl⟩
  rw [hsp_eq]; rw [hsp_eq] at hcorr
  have h_first : SNsPlainFirst (ctxOfInFlow sc.inFlow) ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
    canStartPlainScalar_to_SNsPlainFirst c rest sc.col (sc.peekAt? 1) sc.inFlow hstart hrest_head
  -- Unfold scanPlainScalar to extract loop
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i result hloop
    simp only [Except.ok.injEq] at hok; subst hok
    -- Step 1: First char is valid content — extract recursive call from loop
    have h_term_none := canStartPlain_first_not_terminates c sc sc.inFlow hstart h_not_doc
    have h_safe := canStartPlain_implies_safe hstart
    have h_nws := canStartPlainScalar_not_ws hstart
    have h_nlb := canStartPlain_not_linebreak hstart
    have h_has_more := peek_some_has_more hpeek
    have h_fuel_pos : (sc.inputEnd - sc.offset + 1) * 2 ≥ 1 := by omega
    obtain ⟨fuel', h_fuel_eq⟩ : ∃ n, (sc.inputEnd - sc.offset + 1) * 2 = n + 1 :=
      ⟨(sc.inputEnd - sc.offset + 1) * 2 - 1, by omega⟩
    rw [h_fuel_eq] at hloop
    have hloop' := collectPlainScalarLoop_content_first_step
      hpeek h_term_none h_nlb h_nws h_safe hloop
    -- Step 2: Apply collectPlainScalarLoop_prod on the remaining loop
    have hcorr_adv := advance_non_newline_corr sc c rest hcorr h_has_more
      (isPlainSafe_not_newline h_safe).1 (isPlainSafe_not_newline h_safe).2
    obtain ⟨sp_entries, sp_next, sp_trail, h_entries, _h_next_lines, h_trail, hcorr_result,
            h_hash, -, -⟩ :=
      collectPlainScalarLoop_prod sc.advance ⟨rest, sc.col + 1⟩ _ "" _ _ _
        ⟨rest, sc.col + 1⟩ sc.inFlow hcorr_adv (GStar.nil _)
        (fun _ => rfl)
        (fun _ _ => by
          have h : sc.col + 1 = sc.advance.col := hcorr_adv.col_eq
          omega)
        (fun h => by simp at h)
        (by rw [advance_inputEnd]; exact Nat.le_refl _)
        (fun hnf => by
          have hci : sc.advance.currentIndent = sc.currentIndent := by
            simp only [ScannerState.currentIndent,
              L4YAML.Proofs.EmitterScannability.advance_preserves_indents]
          rw [hci]
          exact currentIndent_lt_blockContentIndent (s := sc) (by simpa using hnf))
        hloop'
    -- Step 3: Build the native-context scalar (no lift)
    exact ⟨sp_next, sp_trail,
      SNsPlainMultiLine.mk 0 (ctxOfInFlow sc.inFlow) _ _ sp_next
        (SNsPlainOneLine.mk (ctxOfInFlow sc.inFlow) _ ⟨rest, sc.col + 1⟩ sp_entries
          h_first h_entries)
        _h_next_lines,
      h_trail,
      fun heq hpk => h_hash
        (collectPlainScalarLoop_terminated_of_fuel _ sc "" "" sc.inFlow _ sc.inputEnd result hloop
            (by omega))
        heq hpk,
      corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_result)⟩

/-! ## §7' The BLOCK-KEY one-line reading (item 15)

  `[131] ns-plain(0, block-key)` is `ns-plain-one-line(block-key)` — what
  `[193] ns-s-block-map-implicit-key`'s YAML arm consumes.  A block-context
  plain scalar whose scan exits on its entry line is exactly that reading:
  the one-line conjunct of `collectPlainScalarLoop_prod` kills the next-line
  star, and `.blockIn → .blockKey` is definitional (`isNsPlainSafe` maps both
  to `isNsChar`). -/

-- Context lift: SNsPlainChar .blockIn → .blockKey (definitional safety).
lemma SNsPlainChar_blockIn_to_blockKey {sp sp' : SurfPos}
    (h : SNsPlainChar .blockIn sp sp') : SNsPlainChar .blockKey sp sp' := by
  cases h with
  | safe ch rest col hS hNC hNH =>
    exact SNsPlainChar.safe .blockKey ch rest col hS hNC hNH
  | colonSafe prev next rest col hS =>
    exact SNsPlainChar.colonSafe .blockKey prev next rest col hS

-- Context lift: SNbNsPlainInLineEntry .blockIn → .blockKey.
lemma SNbNsPlainInLineEntry_blockIn_to_blockKey {sp sp' : SurfPos}
    (h : SNbNsPlainInLineEntry .blockIn sp sp') : SNbNsPlainInLineEntry .blockKey sp sp' :=
  match h with
  | SNbNsPlainInLineEntry.mk _ _ s₁ _ ws_pre char =>
    SNbNsPlainInLineEntry.mk .blockKey _ s₁ _ ws_pre (SNsPlainChar_blockIn_to_blockKey char)
  | SNbNsPlainInLineEntry.hash _ _ _ hlit => SNbNsPlainInLineEntry.hash .blockKey _ _ hlit

-- Context lift: GStar (SNbNsPlainInLineEntry .blockIn) → GStar (...blockKey).
lemma GStar_entries_blockIn_to_blockKey {sp sp' : SurfPos}
    (h : GStar (SNbNsPlainInLineEntry .blockIn) sp sp') :
    GStar (SNbNsPlainInLineEntry .blockKey) sp sp' := by
  induction h with
  | nil => exact GStar.nil _
  | cons s₁ s₂ s₃ entry _ ih =>
    exact GStar.cons s₁ s₂ s₃ (SNbNsPlainInLineEntry_blockIn_to_blockKey entry) ih

-- Context lift: SNsPlainFirst .blockIn → .blockKey.
lemma SNsPlainFirst_blockIn_to_blockKey {s s' : SurfPos}
    (h : SNsPlainFirst .blockIn s s') : SNsPlainFirst .blockKey s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hNotInd =>
    exact SNsPlainFirst.nonIndicator .blockKey ch rest col hSafe hNotInd
  | dashSafe next rest col hSafe => exact SNsPlainFirst.dashSafe .blockKey next rest col hSafe
  | colonSafe next rest col hSafe => exact SNsPlainFirst.colonSafe .blockKey next rest col hSafe
  | questionSafe next rest col hSafe =>
    exact SNsPlainFirst.questionSafe .blockKey next rest col hSafe

-- Context lift: SNsPlainOneLine .blockIn → .blockKey.
lemma SNsPlainOneLine_blockIn_to_blockKey {s s' : SurfPos}
    (h : SNsPlainOneLine .blockIn s s') : SNsPlainOneLine .blockKey s s' :=
  match h with
  | SNsPlainOneLine.mk _ _ s₁ _ h_first h_entries =>
    SNsPlainOneLine.mk .blockKey _ s₁ _
      (SNsPlainFirst_blockIn_to_blockKey h_first)
      (GStar_entries_blockIn_to_blockKey h_entries)

-- The ONE-LINE key production (item 15): a block-context plain scalar whose
-- scan exits on its entry line reads as `ns-plain-one-line(block-key)` —
-- `[193]`'s YAML implicit key — plus its trailing `s-white*`.  The line
-- hypothesis fires the one-line conjunct of `collectPlainScalarLoop_prod`;
-- everything else mirrors `scanPlainScalar_to_multiLine_native`.
lemma scanPlainScalar_to_blockKey_oneLine (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (h_flow : sc.inFlow = false)
    (h_line : s'.line = sc.line)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp_gram sp', SNsPlainOneLine .blockKey sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   (sp_gram = sp' → s'.peek? ≠ some '#') ∧
                   ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  have hrest_head : ∀ n, sc.peekAt? 1 = some n → ∃ rest', rest = n :: rest' := by
    intro n hn; unfold ScannerState.peekAt? at hn
    have hcorr' := hsp_eq ▸ hcorr
    obtain ⟨pre, rest', hcs, hlen⟩ :=
      peekAtLoop_some_chars hcorr'.end_eq hn (c :: rest) hcorr'.chars_from
    have ⟨a, ha⟩ : ∃ a, pre = [a] := by
      cases pre with
      | nil => simp at hlen
      | cons a as => cases as with
        | nil => exact ⟨a, rfl⟩
        | cons => simp at hlen
    subst ha; simp at hcs; obtain ⟨_, rfl⟩ := hcs; exact ⟨rest', rfl⟩
  rw [hsp_eq]; rw [hsp_eq] at hcorr
  have h_first : SNsPlainFirst (ctxOfInFlow sc.inFlow) ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
    canStartPlainScalar_to_SNsPlainFirst c rest sc.col (sc.peekAt? 1) sc.inFlow hstart hrest_head
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i result hloop
    have h_rline : result.state.line = sc.line := by
      have h := Except.ok.inj hok
      rw [← h] at h_line
      exact h_line
    have h_term_none := canStartPlain_first_not_terminates c sc sc.inFlow hstart h_not_doc
    have h_safe := canStartPlain_implies_safe hstart
    have h_nws := canStartPlainScalar_not_ws hstart
    have h_nlb := canStartPlain_not_linebreak hstart
    have h_has_more := peek_some_has_more hpeek
    obtain ⟨fuel', h_fuel_eq⟩ : ∃ n, (sc.inputEnd - sc.offset + 1) * 2 = n + 1 :=
      ⟨(sc.inputEnd - sc.offset + 1) * 2 - 1, by omega⟩
    rw [h_fuel_eq] at hloop
    have hloop' := collectPlainScalarLoop_content_first_step
      hpeek h_term_none h_nlb h_nws h_safe hloop
    have hcorr_adv := advance_non_newline_corr sc c rest hcorr h_has_more
      (isPlainSafe_not_newline h_safe).1 (isPlainSafe_not_newline h_safe).2
    obtain ⟨sp_entries, sp_next, sp_trail, h_entries, _h_next_lines, h_trail, hcorr_result,
            h_hash, h_one, -⟩ :=
      collectPlainScalarLoop_prod sc.advance ⟨rest, sc.col + 1⟩ _ "" _ _ _
        ⟨rest, sc.col + 1⟩ sc.inFlow hcorr_adv (GStar.nil _)
        (fun _ => rfl)
        (fun _ _ => by
          have h : sc.col + 1 = sc.advance.col := hcorr_adv.col_eq
          omega)
        (fun h => by simp at h)
        (by rw [advance_inputEnd]; exact Nat.le_refl _)
        (fun hnf => by
          have hci : sc.advance.currentIndent = sc.currentIndent := by
            simp only [ScannerState.currentIndent,
              L4YAML.Proofs.EmitterScannability.advance_preserves_indents]
          rw [hci]
          exact currentIndent_lt_blockContentIndent (s := sc) (by simpa using hnf))
        hloop'
    -- The same-line exit kills the next-line star: sp_next = sp_entries.
    have hadv_line : sc.advance.line = sc.line :=
      advance_preserves_line_of_ne_break sc c hpeek
        (isPlainSafe_not_newline h_safe).1 (isPlainSafe_not_newline h_safe).2
    have h_pos_eq : sp_next = sp_entries := h_one (by rw [hadv_line]; exact h_rline)
    rw [h_pos_eq] at h_trail
    have h_ctx : ctxOfInFlow sc.inFlow = .blockIn := by rw [h_flow]; rfl
    have h_first' : SNsPlainFirst .blockIn ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
      h_ctx ▸ h_first
    have h_entries' : GStar (SNbNsPlainInLineEntry .blockIn) ⟨rest, sc.col + 1⟩ sp_entries :=
      h_ctx ▸ h_entries
    have h_corr_final : ScannerSurfCorr s' sp_trail := by
      have h := Except.ok.inj hok
      rw [← h]
      exact corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_result)
    exact ⟨sp_entries, sp_trail,
      SNsPlainOneLine_blockIn_to_blockKey
        (SNsPlainOneLine.mk .blockIn _ ⟨rest, sc.col + 1⟩ sp_entries h_first' h_entries'),
      h_trail,
      fun heq hpk => h_hash
        (collectPlainScalarLoop_terminated_of_fuel _ sc "" "" sc.inFlow _ sc.inputEnd result hloop
            (by omega))
        (h_pos_eq.trans heq) (by
          have h := Except.ok.inj hok
          rw [← h] at hpk
          exact hpk),
      h_corr_final⟩

/-! ## §7'' The BLOCK-KEY one-line reading of a QUOTED scalar (item 16)

  `[110] nb-double-text(n, block-key)` is `[111] nb-double-one-line`, a bare
  `nb-double-char*` with no `s-double-break` in it, and `[121]` reads the same
  way for single quotes.  So the quoted key's one-line witness needs no
  collapse fact about existentially bound positions the way the plain key's
  did (item 15's conjunct): the reading is a DIFFERENT, self-contained
  conclusion over the same walk, and a same-line exit simply refutes the two
  arms that consume a break — the escaped break (`\` + `b-char`) and the
  flow fold — each of which begins with `consumeNewline` (+1) and is followed
  by a walk that never returns.  The escape body is line-transparent for the
  same reason `s-white` is: `ns-hex-digit` and the simple escape characters
  are not `b-char`. -/

-- Hex digits are `[36] ns-hex-digit`, never `b-char`: the escape body leaves
-- the line alone.
lemma collectHexDigitsLoop_line (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).2.line = s.line := by
  induction n generalizing s hex with
  | zero => rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    split
    · rename_i c hp
      split
      · rename_i hhex
        have hn : c ≠ '\n' := by intro h; rw [h] at hhex; exact absurd hhex (by decide)
        have hr : c ≠ '\r' := by intro h; rw [h] at hhex; exact absurd hhex (by decide)
        rw [ih, advance_preserves_line_of_ne_break s c hp hn hr]
      · rfl
    · rfl

lemma parseHexEscape_line {s : ScannerState} {n : Nat} {ch : Char} {s' : ScannerState}
    (hok : parseHexEscape s n = .ok (ch, s')) : s'.line = s.line := by
  unfold parseHexEscape at hok
  dsimp only [] at hok
  split at hok
  · simp at hok
  · split at hok
    · obtain ⟨-, rfl⟩ := hok
      exact collectHexDigitsLoop_line s "" n
    · simp at hok

-- Every escape `[62] c-ns-esc-char` admits is a non-break character, so
-- `processEscape` moves the column only.  (The ESCAPED break is not routed
-- here: `collectDoubleQuotedLoop` tests `isLineBreakBool` first.)
lemma processEscape_line {s : ScannerState} {ch : Char} {s' : ScannerState}
    (hproc : processEscape s = .ok (ch, s')) : s'.line = s.line := by
  unfold processEscape at hproc
  split at hproc
  · simp at hproc
  · rename_i c_esc hpeek
    dsimp only [] at hproc
    split at hproc <;> (first
      | (obtain ⟨-, rfl⟩ := hproc; try subst_vars
         exact advance_preserves_line_of_ne_break s _ hpeek (by decide) (by decide))
      | skip)
    · -- 'x': hex escape (n = 2)
      try subst_vars
      rw [parseHexEscape_line hproc,
          advance_preserves_line_of_ne_break s 'x' hpeek (by decide) (by decide)]
    · -- 'u': hex escape (n = 4)
      try subst_vars
      rw [parseHexEscape_line hproc,
          advance_preserves_line_of_ne_break s 'u' hpeek (by decide) (by decide)]
    · -- 'U': hex escape (n = 8)
      try subst_vars
      rw [parseHexEscape_line hproc,
          advance_preserves_line_of_ne_break s 'U' hpeek (by decide) (by decide)]
    · simp at hproc

-- The double-quoted walk never returns to an earlier line.
lemma collectDoubleQuotedLoop_line_ge (sc : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int)
    (inputEnd protectedLen : Nat)
    {result_content : String} {s' : ScannerState}
    (hok : collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd protectedLen = .ok (result_content, s')) :
    sc.line ≤ s'.line := by
  induction fuel generalizing sc content protectedLen with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- closing quote
      rename_i _ hpeek
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      exact Nat.le_of_eq
        (advance_preserves_line_of_ne_break sc '"' hpeek (by decide) (by decide)).symm
    · -- backslash
      rename_i _ hpeek
      dsimp only [] at hok
      split at hok
      · rename_i c2 hpeek2
        split at hok
        · -- escaped break: the landing is a fold (item 87), strictly past
          -- the entry line; throws contradict.
          rename_i hlb2
          have h1 := advance_preserves_line_of_ne_break sc '\\' hpeek (by decide) (by decide)
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i fold_result hfold
            have h2 := foldQuotedNewlines_line_lt hpeek2 hlb2 hfold
            repeat' split at hok
            all_goals first
              | contradiction
              | (have h4 := ih _ _ _ hok; omega)
        · simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i esc_result hproc
            have h1 := advance_preserves_line_of_ne_break sc '\\' hpeek (by decide) (by decide)
            have h2 := processEscape_line hproc
            have h3 := ih _ _ _ hok
            omega
      · exact absurd hok (by simp)
    · -- regular character
      rename_i _opt c hne_dq hne_bs hpeek
      split at hok
      · -- line break: the fold lands strictly past the entry line
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · rename_i fold_result hfold
          have h1 := foldQuotedNewlines_line_lt hpeek hlb hfold
          split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · split at hok <;>
                first
                  | (have h2 := ih _ _ _ hok; omega)
                  | simp at hok
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have h1 := advance_preserves_line_of_ne_break sc c hpeek
            (not_isLineBreak_not_newline c hne_lb) (not_isLineBreak_not_cr c hne_lb)
          have h2 := ih _ _ _ hok
          omega

-- The ONE-LINE body: a double-quoted walk that exits on its entry line
-- appended no `[113] s-double-break`, so `[110] nb-double-text(0, block-key)`
-- — `[111] nb-double-one-line` — reads it.
lemma collectDoubleQuotedLoop_oneLine_prod (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int)
    (inputEnd protectedLen : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (h_line : s'.line = sc.line)
    (hok : collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd protectedLen = .ok (result_content, s')) :
    ∃ sp_body sp_close,
      SNbDoubleOneLine sp sp_body ∧
      GLit '"' sp_body sp_close ∧
      ScannerSurfCorr s' sp_close := by
  induction fuel generalizing sc sp content protectedLen with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- closing quote: the body is empty here
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      exact ⟨⟨'"' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
             GStar.nil _,
             GLit.mk rest sc.col,
             advance_non_newline_corr sc '"' rest hcorr
               (peek_some_has_more hpeek) (by decide) (by decide)⟩
    · -- backslash
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv :=
        advance_non_newline_corr sc '\\' rest hcorr
          (peek_some_has_more hpeek) (by decide) (by decide)
      have hadv_line := advance_preserves_line_of_ne_break sc '\\' hpeek (by decide) (by decide)
      dsimp only [] at hok
      split at hok
      · rename_i c2 hpeek2
        split at hok
        · -- escaped break: the landing is a fold (item 87), refuted by the
          -- same-line exit; throws contradict before the refutation is needed.
          exfalso
          rename_i hlb2
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i fold_result hfold
            have h2 := foldQuotedNewlines_line_lt hpeek2 hlb2 hfold
            repeat' split at hok
            all_goals first
              | contradiction
              | (have h4 := collectDoubleQuotedLoop_line_ge _ _ fuel' startPos inFlow
                   currentIndent inputEnd _ hok
                 omega)
        · simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i esc_result hproc
            obtain ⟨sp_esc, h_dq_char, hcorr_esc⟩ :=
              processEscape_prod sc.advance rest sc.col hcorr_adv hproc
            obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
              ih _ sp_esc _ _ hcorr_esc
                (by rw [h_line, ← hadv_line, ← processEscape_line hproc]) hok
            exact ⟨sp_body, sp_close,
                   GStar.cons _ sp_esc sp_body h_dq_char h_body,
                   h_glit, h_corr⟩
      · exact absurd hok (by simp)
    · -- regular character
      rename_i _opt c hne_dq hne_bs hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      split at hok
      · -- line break: the fold is refuted by the same-line exit
        exfalso
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · rename_i fold_result hfold
          have h1 := foldQuotedNewlines_line_lt hpeek hlb hfold
          split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · split at hok <;>
                first
                  | (have h2 := collectDoubleQuotedLoop_line_ge _ _ fuel' startPos inFlow
                       currentIndent inputEnd _ hok
                     omega)
                  | simp at hok
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
            ih sc.advance ⟨rest, sc.col + 1⟩ _ _ hcorr_adv
              (by rw [h_line, advance_preserves_line_of_ne_break sc c hpeek h_not_nl h_not_cr])
              hok
          have h_dq_char : SNbDoubleChar ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
            SNbDoubleChar.plain c rest sc.col
              (not_lineBreak_bool_to_prop hne_lb) hne_bs hne_dq
          exact ⟨sp_body, sp_close,
                 GStar.cons _ ⟨rest, sc.col + 1⟩ sp_body h_dq_char h_body,
                 h_glit, h_corr⟩

-- `scanDoubleQuoted` at a same-line exit produces `[109] c-double-quoted(0,
-- block-key)` — `[188]`'s JSON implicit key.
lemma scanDoubleQuoted_to_blockKey_oneLine (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_dq : sc.peek? = some '"')
    (h_line : s'.line = sc.line)
    (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp', SCDoubleQuoted 0 .blockKey sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek_dq
  subst hsp_eq
  have hmore := peek_some_has_more hpeek_dq
  have hcorr_adv :=
    advance_non_newline_corr sc '"' rest hcorr hmore (by decide) (by decide)
  have hadv_line :=
    advance_preserves_line_of_ne_break sc '"' hpeek_dq (by decide) (by decide)
  split at hok
  · simp at hok
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    -- The trailing emit/flag updates are line-transparent, so the loop's own
    -- exit line is the scan's.
    have h_cl : s_after_close.line = sc.advance.line := by
      rw [hadv_line]
      split at hok
      · split at hok
        · simp at hok
        · have h := Except.ok.inj hok; rw [← h] at h_line; exact h_line
      · have h := Except.ok.inj hok; rw [← h] at h_line; exact h_line
    obtain ⟨sp_body, sp_close, h_body, h_glit_close, hcorr_close⟩ :=
      collectDoubleQuotedLoop_oneLine_prod sc.advance ⟨rest, sc.col + 1⟩ "" _ _ _ _ _ _
        hcorr_adv h_cl hloop
    have h_text : SNbDoubleText 0 .blockKey ⟨rest, sc.col + 1⟩ sp_body := h_body
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close,
               SCDoubleQuoted.mk 0 .blockKey _ _ _ _
                 (GLit.mk rest sc.col) h_text h_glit_close,
               corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_close)⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨sp_close,
             SCDoubleQuoted.mk 0 .blockKey _ _ _ _
               (GLit.mk rest sc.col) h_text h_glit_close,
             corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_close)⟩

-- The single-quoted walk never returns to an earlier line.
lemma collectSingleQuotedLoop_line_ge (sc : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int)
    (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hok : collectSingleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd = .ok (result_content, s')) :
    sc.line ≤ s'.line := by
  induction fuel generalizing sc content with
  | zero => simp [collectSingleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · rename_i _ hpeek
      have h1 := advance_preserves_line_of_ne_break sc '\'' hpeek (by decide) (by decide)
      dsimp only [] at hok
      split at hok
      · -- escaped quote ''
        rename_i hpeek2
        have h2 := advance_preserves_line_of_ne_break sc.advance '\'' hpeek2
          (by decide) (by decide)
        have h3 := ih _ _ hok
        omega
      · -- closing quote
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        omega
    · rename_i c hne_sq hpeek
      split at hok
      · -- line break: the fold lands strictly past the entry line
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · rename_i fold_result hfold
          have h1 := foldQuotedNewlines_line_lt hpeek hlb hfold
          split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · have h2 := ih _ _ hok
              omega
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have h1 := advance_preserves_line_of_ne_break sc c hpeek
            (not_isLineBreak_not_newline c hne_lb) (not_isLineBreak_not_cr c hne_lb)
          have h2 := ih _ _ hok
          omega

-- The ONE-LINE body: `[121] nb-single-text(0, block-key)` = `[122]
-- nb-single-one-line`.
lemma collectSingleQuotedLoop_oneLine_prod (sc : ScannerState) (sp : SurfPos)
    (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (h_line : s'.line = sc.line)
    (hok : collectSingleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd = .ok (result_content, s')) :
    ∃ sp_body sp_close,
      SNbSingleOneLine sp sp_body ∧
      GLit '\'' sp_body sp_close ∧
      ScannerSurfCorr s' sp_close := by
  induction fuel generalizing sc sp content with
  | zero => simp [collectSingleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      have hadv_line := advance_preserves_line_of_ne_break sc '\'' hpeek
        (by decide) (by decide)
      dsimp only [] at hok
      split at hok
      · -- escaped quote ''
        rename_i hpeek2
        have hcorr_adv :=
          advance_non_newline_corr sc '\'' rest hcorr hmore (by decide) (by decide)
        obtain ⟨rest2, hsp_adv⟩ := peek_some_sp hcorr_adv hpeek2
        injection hsp_adv with h_rest2 h_col2
        subst h_rest2
        rw [h_col2] at hcorr_adv
        have hmore2 := peek_some_has_more hpeek2
        have hcorr_adv2 :=
          advance_non_newline_corr sc.advance '\'' rest2 hcorr_adv hmore2
            (by decide) (by decide)
        rw [show sc.advance.col + 1 = sc.col + 2 from by omega] at hcorr_adv2
        have hadv2_line := advance_preserves_line_of_ne_break sc.advance '\'' hpeek2
          (by decide) (by decide)
        obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
          ih sc.advance.advance ⟨rest2, sc.col + 2⟩ _ hcorr_adv2
            (by rw [h_line, ← hadv_line, ← hadv2_line]) hok
        have h_esc : SNbSingleChar ⟨'\'' :: '\'' :: rest2, sc.col⟩ ⟨rest2, sc.col + 2⟩ :=
          SNbSingleChar.escapedQuote rest2 sc.col
        exact ⟨sp_body, sp_close,
               GStar.cons _ ⟨rest2, sc.col + 2⟩ sp_body h_esc h_body,
               h_glit, h_corr⟩
      · -- closing quote: the body is empty here
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        exact ⟨⟨'\'' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
               GStar.nil _,
               GLit.mk rest sc.col,
               advance_non_newline_corr sc '\'' rest hcorr hmore (by decide) (by decide)⟩
    · rename_i c hne_sq hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      split at hok
      · -- line break: refuted by the same-line exit
        exfalso
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · rename_i fold_result hfold
          have h1 := foldQuotedNewlines_line_lt hpeek hlb hfold
          split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · have h2 := collectSingleQuotedLoop_line_ge _ _ fuel' startPos inFlow
                currentIndent inputEnd hok
              omega
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
            ih sc.advance ⟨rest, sc.col + 1⟩ _ hcorr_adv
              (by rw [h_line, advance_preserves_line_of_ne_break sc c hpeek h_not_nl h_not_cr])
              hok
          have h_sq_char : SNbSingleChar ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
            SNbSingleChar.plain c rest sc.col
              (not_lineBreak_bool_to_prop hne_lb) hne_sq
          exact ⟨sp_body, sp_close,
                 GStar.cons _ ⟨rest, sc.col + 1⟩ sp_body h_sq_char h_body,
                 h_glit, h_corr⟩

-- `scanSingleQuoted` at a same-line exit produces `[120] c-single-quoted(0,
-- block-key)`.
lemma scanSingleQuoted_to_blockKey_oneLine (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_sq : sc.peek? = some '\'')
    (h_line : s'.line = sc.line)
    (hok : scanSingleQuoted sc = .ok s') :
    ∃ sp', SCSingleQuoted 0 .blockKey sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek_sq
  subst hsp_eq
  have hmore := peek_some_has_more hpeek_sq
  have hcorr_adv :=
    advance_non_newline_corr sc '\'' rest hcorr hmore (by decide) (by decide)
  have hadv_line :=
    advance_preserves_line_of_ne_break sc '\'' hpeek_sq (by decide) (by decide)
  split at hok
  · simp at hok
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    have h_cl : s_after_close.line = sc.advance.line := by
      rw [hadv_line]
      split at hok
      · split at hok
        · simp at hok
        · have h := Except.ok.inj hok; rw [← h] at h_line; exact h_line
      · have h := Except.ok.inj hok; rw [← h] at h_line; exact h_line
    obtain ⟨sp_body, sp_close, h_body, h_glit_close, hcorr_close⟩ :=
      collectSingleQuotedLoop_oneLine_prod sc.advance ⟨rest, sc.col + 1⟩ "" _ _ _ _ _
        hcorr_adv h_cl hloop
    have h_text : SNbSingleText 0 .blockKey ⟨rest, sc.col + 1⟩ sp_body := h_body
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_close,
               SCSingleQuoted.mk 0 .blockKey _ _ _ _
                 (GLit.mk rest sc.col) h_text h_glit_close,
               corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_close)⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨sp_close,
             SCSingleQuoted.mk 0 .blockKey _ _ _ _
               (GLit.mk rest sc.col) h_text h_glit_close,
             corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcorr_close)⟩

-- Full production: scanPlainScalar → SFlowNode 0 .flowOut + trailing WS + corr.
-- Lifts the native-context core to `.flowOut` (top-level flow node context).
-- Parameterized over inFlow: works for both block and flow contexts.
lemma scanPlainScalar_to_flowNode (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp_gram sp', SFlowNode 0 .flowOut sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   (sp_gram = sp' → s'.peek? ≠ some '#') ∧
                   ScannerSurfCorr s' sp' := by
  obtain ⟨sp_gram, sp', h_ml, h_trail, h_hash, hcorr'⟩ :=
    scanPlainScalar_to_multiLine_native sc sp hcorr hpeek hstart h_not_doc hok
  exact ⟨sp_gram, sp',
    SFlowNode.content 0 .flowOut _ _
      (SFlowContent.plain 0 .flowOut _ _ (SNsPlainMultiLine_ctxOfInFlow_to_flowOut h_ml)),
    h_trail, h_hash, hcorr'⟩

-- Content-level `.flowOut` sibling of `scanPlainScalar_to_flowNode` (item 12):
-- exposes the `SFlowContent` before the `SFlowNode.content` wrap, which is what
-- a held depth-0 props run decorates (`SFlowNode.propsContent` wraps content,
-- not a node).
lemma scanPlainScalar_to_flowContent (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp_gram sp', SFlowContent 0 .flowOut sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   (sp_gram = sp' → s'.peek? ≠ some '#') ∧
                   ScannerSurfCorr s' sp' := by
  obtain ⟨sp_gram, sp', h_ml, h_trail, h_hash, hcorr'⟩ :=
    scanPlainScalar_to_multiLine_native sc sp hcorr hpeek hstart h_not_doc hok
  exact ⟨sp_gram, sp',
    SFlowContent.plain 0 .flowOut _ _ (SNsPlainMultiLine_ctxOfInFlow_to_flowOut h_ml),
    h_trail, h_hash, hcorr'⟩

-- Flow-interior production: scanPlainScalar → SFlowNode 0 .flowIn + trailing WS
-- + corr, for a plain scalar scanned INSIDE a flow collection (`inFlow = true`).
-- Uses the native-context core directly (its context is already `.flowIn`), with
-- no lift — the `.flowIn` sibling of `scanPlainScalar_to_flowNode`. Feeds flow
-- sequence/mapping entries (`ns-flow-node(n, in-flow(c))`).
lemma scanPlainScalar_to_flowNode_flowIn (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (hInFlow : sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp_gram sp', SFlowNode 0 .flowIn sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   (sp_gram = sp' → s'.peek? ≠ some '#') ∧
                   ScannerSurfCorr s' sp' := by
  obtain ⟨sp_gram, sp', h_ml, h_trail, h_hash, hcorr'⟩ :=
    scanPlainScalar_to_multiLine_native sc sp hcorr hpeek hstart h_not_doc hok
  rw [hInFlow] at h_ml
  exact ⟨sp_gram, sp',
    SFlowNode.content 0 .flowIn _ _ (SFlowContent.plain 0 .flowIn _ _ h_ml),
    h_trail, h_hash, hcorr'⟩

/-- `scanPlainScalar` in block context reads `[131] ns-plain(0, block-in)` up to
    its grammar endpoint `sp_gram`; the scanner parks at `sp'` past the
    trailing `s-white*` it swallowed (`a #b`).  When nothing was swallowed the
    walk did NOT stop on `#` (`collectPlainScalar_terminates?` needs buffered
    whites for that), so a comment can only follow across the run. -/
lemma scanPlainScalar_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) false = true)
    (hflow : sc.inFlow = false)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp_gram sp', SNsPlain 0 .blockIn sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   (sp_gram = sp' → s'.peek? ≠ some '#') ∧
                   ScannerSurfCorr s' sp' := by
  have hstart' : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true := by
    rw [hflow]; exact hstart
  obtain ⟨sp_gram, sp', h_ml, h_trail, h_hash, hcorr'⟩ :=
    scanPlainScalar_to_multiLine_native sc sp hcorr hpeek hstart' h_not_doc hok
  have h_ctx : ctxOfInFlow sc.inFlow = .blockIn := by rw [hflow]; rfl
  rw [h_ctx] at h_ml
  exact ⟨sp_gram, sp', h_ml, h_trail, h_hash, hcorr'⟩

/-! ## §8 Block Scalar Production (Layer 4b)

  `scanBlockScalar` produces `SCLLiteral 0` (for `|`) or `SCLFolded 0` (for `>`),
  and preserves correspondence.

  Pipeline structure (each step has proven `_corr` and most have `_prod`):
  1. Advance past `|`/`>` → `GLit` delimiter
  2. `parseBlockHeaderLoop` → `[163]`/`[164]` indicators in either order (proven §6)
  3. `skipWhitespace` + `scanBlockScalarSkipComment` → whitespace + optional comment text
  4. `scanBlockScalarConsumeNewline` → line break
  5. Steps 2–4 combined → `SCBBlockHeader`
  6. `scanBlockScalarBody` → `SLLiteralContent`/`GOpt SLNbFoldedLines` content

  §8b adds sub-function _prod theorems for content body.
  §8c composes header + body into complete `SCLLiteral`/`SCLFolded`. -/

-- `scanBlockScalarSkipComment` produces `GOpt SCNbCommentText`.
-- Mirrors `skipToContentComment_corr` structure.
-- Proof that if the comment is successfully consumed,
-- the characters strictly form a GOpt SCNbCommentText derivation tree
-- and preserve scanner-surface correspondence.
lemma scanBlockScalarSkipComment_prod (sc : ScannerState) (sp : SurfPos)
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
lemma peek_none_not_lt {sc : ScannerState}
    (hpeek : sc.peek? = none) : ¬ sc.offset < sc.inputEnd := by
  unfold ScannerState.peek? at hpeek
  split at hpeek
  · cases hpeek
  · assumption

-- `scanBlockScalarConsumeNewline` produces `SBComment`.
lemma scanBlockScalarConsumeNewline_prod (sc : ScannerState) (sp : SurfPos)
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
lemma whitespace_comment_break_to_SSBComment_withWS
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

-- `autoDetectBlockScalarIndentLoop` returns indent ≥ minContentIndent when no error.
lemma autoDetectBlockScalarIndentLoop_ge_min
    (probe : ScannerState) (maxWSCol maxWSLine min fuel ie : Nat) :
    (autoDetectBlockScalarIndentLoop probe maxWSCol maxWSLine min fuel ie).2.2.2 = none →
    (autoDetectBlockScalarIndentLoop probe maxWSCol maxWSLine min fuel ie).1 ≥ min := by
  induction fuel generalizing probe maxWSCol maxWSLine with
  | zero =>
    unfold autoDetectBlockScalarIndentLoop
    split <;> omega
  | succ fuel' ih =>
    unfold autoDetectBlockScalarIndentLoop
    dsimp only []
    split
    · -- peek? = some c
      split
      · intro h; cases h  -- tab error: none ≠ some
      · split
        · -- linebreak: recurse
          exact ih _ _ _
        · -- content line
          split
          · intro h; cases h  -- indent mismatch: none ≠ some
          · intro _; exact Nat.le_max_left min _
    · -- peek? = none
      split <;> omega

-- `autoDetectBlockScalarIndent` returns indent ≥ minContentIndent when no error.
lemma autoDetectBlockScalarIndent_ge_min
    (s : ScannerState) (min ie : Nat) :
    (autoDetectBlockScalarIndent s min ie).2 = none →
    (autoDetectBlockScalarIndent s min ie).1 ≥ min := by
  unfold autoDetectBlockScalarIndent
  simp only []
  generalize hq : autoDetectBlockScalarIndentLoop s 0 0 min (ie - s.offset + 1) ie = q
  obtain ⟨indent, wsLine, probe', err⟩ := q
  simp only [] at *
  intro h_none; subst h_none
  have := autoDetectBlockScalarIndentLoop_ge_min s 0 0 min (ie - s.offset + 1) ie
  rw [hq] at this
  exact this rfl

-- Compose: text line + break + recursive SLLiteralContent → SLLiteralContent.
-- The first line becomes the head of the GSeq, and if the recursive content
-- has text lines they become SBNbLiteralNext entries in the GStar tail.
-- Prepend an `SLEmpty` to an `SLNbLiteralText`'s GStar prefix.
lemma prepend_empty_to_text_line {n : Nat}
    {sp sp_cn sp_end : SurfPos}
    (h_empty : SLEmpty n .blockIn sp sp_cn)
    (h_text : SLNbLiteralText n sp_cn sp_end) :
    SLNbLiteralText n sp sp_end := by
  match h_text with
  | .mk _ _ sp_after_empties _ h_empties h_indent_content =>
    exact SLNbLiteralText.mk n sp sp_after_empties sp_end
      (GStar.cons sp sp_cn sp_after_empties h_empty h_empties)
      h_indent_content

/-! ### SLLiteralContent composition helpers

  Helpers for building `SLLiteralContent` incrementally from loop iterations. -/

-- Empty literal content: no text, no break, no trailing.
lemma empty_literal_content {n : Nat} (sp : SurfPos) :
    SLLiteralContent n sp sp :=
  SLLiteralContent.mk n sp sp sp sp sp sp
    (GOpt.none sp) (GOpt.none sp) (GStar.nil sp) (GOpt.none sp) (GOpt.none sp)

-- Trailing indent only: `SIndentLe n` at EOF (the tail is EOF-confined).
lemma indent_only_literal_content {n : Nat} {sp sp' : SurfPos}
    (h : SIndentLe n sp sp') (hend : sp'.chars = []) : SLLiteralContent n sp sp' :=
  SLLiteralContent.mk n sp sp sp sp sp sp'
    (GOpt.none sp) (GOpt.none sp) (GStar.nil sp) (GOpt.none sp) (GOpt.some sp sp' ⟨h, hend⟩)

-- Prepend an `SLEmpty n .blockIn` to `SLLiteralContent n`.
-- The empty line either joins the first text line's prefix or the trailing empties.
lemma prepend_empty_to_literal_content {n : Nat}
    {sp sp₁ sp' : SurfPos}
    (h_empty : SLEmpty n .blockIn sp sp₁)
    (h_tail : SLLiteralContent n sp₁ sp') :
    SLLiteralContent n sp sp' := by
  match h_tail with
  | .mk _ _ sp_t1 sp_t2 sp_t3 sp_t4 _ h_opt_text h_opt_break h_trail_empties h_trail_cmts h_trail_indent =>
    match h_opt_text with
    | .some _ _ (GSeq.mk _ sp_first_end _ h_first_text h_conts) =>
      -- Has text: prepend empty to first text line's prefix
      exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp_t4 sp'
        (GOpt.some sp sp_t1 (GSeq.mk sp sp_first_end sp_t1
          (prepend_empty_to_text_line h_empty h_first_text) h_conts))
        h_opt_break h_trail_empties h_trail_cmts h_trail_indent
    | .none _ =>
      -- No text: add our empty to trailing empties, handling tail's break
      match h_opt_break with
      | .none _ =>
        -- sp_t1 = sp₁, sp_t2 = sp₁: chain directly
        exact SLLiteralContent.mk n sp sp sp sp_t3 sp_t4 sp'
          (GOpt.none sp) (GOpt.none sp)
          (GStar.cons sp sp₁ sp_t3 h_empty h_trail_empties)
          h_trail_cmts h_trail_indent
      | .some _ _ h_brk =>
        -- sp_t1 = sp₁: convert tail's break to SLEmpty, chain
        let brk_empty : SLEmpty n .blockIn sp₁ sp_t2 :=
          SLEmpty.block n sp₁ sp₁ sp_t2 .blockIn (Or.inr rfl) (GOpt.none sp₁) h_brk
        exact SLLiteralContent.mk n sp sp sp sp_t3 sp_t4 sp'
          (GOpt.none sp) (GOpt.none sp)
          (GStar.cons sp sp₁ sp_t3 h_empty
            (GStar.cons sp₁ sp_t2 sp_t3 brk_empty h_trail_empties))
          h_trail_cmts h_trail_indent

-- Single content line without trailing break → `SLLiteralContent`.
lemma content_only_to_literal {n : Nat}
    {sp sp' : SurfPos}
    (h_text : SLNbLiteralText n sp sp') :
    SLLiteralContent n sp sp' :=
  SLLiteralContent.mk n sp sp' sp' sp' sp' sp'
    (GOpt.some sp sp' (GSeq.mk sp sp' sp' h_text (GStar.nil sp')))
    (GOpt.none sp') (GStar.nil sp') (GOpt.none sp') (GOpt.none sp')

-- Content line + trailing break + body tail → `SLLiteralContent`.
-- The break + tail's text lines become `SBNbLiteralNext` continuations.
lemma content_break_tail_to_literal {n : Nat}
    {sp sp₁ sp₂ sp' : SurfPos}
    (h_text : SLNbLiteralText n sp sp₁)
    (h_break : SBBreak sp₁ sp₂)
    (h_tail : SLLiteralContent n sp₂ sp') :
    SLLiteralContent n sp sp' := by
  match h_tail with
  | .mk _ _ sp_t1 sp_t2 sp_t3 sp_t4 _ h_opt_text h_opt_break h_trail_empties h_trail_cmts h_trail_indent =>
    match h_opt_text with
    | .some _ _ (GSeq.mk _ sp_tail_first_end _ h_tail_first h_tail_conts) =>
      -- Tail has text: break + tail_first = SBNbLiteralNext, prepend to continuations
      let new_next : SBNbLiteralNext n sp₁ sp_tail_first_end :=
        SBNbLiteralNext.mk n sp₁ sp₂ sp_tail_first_end h_break h_tail_first
      let new_conts := GStar.cons sp₁ sp_tail_first_end sp_t1 new_next h_tail_conts
      exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp_t4 sp'
        (GOpt.some sp sp_t1 (GSeq.mk sp sp₁ sp_t1 h_text new_conts))
        h_opt_break h_trail_empties h_trail_cmts h_trail_indent
    | .none _ =>
      -- Tail has no text: our break is the trailing break.
      -- The tail's break (if any) becomes an SLEmpty (break = indent(0) + break).
      match h_opt_break with
      | .none _ =>
        -- No tail break: straightforward
        exact SLLiteralContent.mk n sp sp₁ sp₂ sp_t3 sp_t4 sp'
          (GOpt.some sp sp₁ (GSeq.mk sp sp₁ sp₁ h_text (GStar.nil sp₁)))
          (GOpt.some sp₁ sp₂ h_break)
          h_trail_empties h_trail_cmts h_trail_indent
      | .some _ _ h_tail_break =>
        -- Tail has a break too: convert it to an SLEmpty and prepend to empties
        let new_empty : SLEmpty n .blockIn sp₂ sp_t2 :=
          SLEmpty.block n sp₂ sp₂ sp_t2 .blockIn (Or.inr rfl) (GOpt.none sp₂) h_tail_break
        exact SLLiteralContent.mk n sp sp₁ sp₂ sp_t3 sp_t4 sp'
          (GOpt.some sp sp₁ (GSeq.mk sp sp₁ sp₁ h_text (GStar.nil sp₁)))
          (GOpt.some sp₁ sp₂ h_break)
          (GStar.cons sp₂ sp_t2 sp_t3 new_empty h_trail_empties)
          h_trail_cmts h_trail_indent

-- Content line + trailing break + trailing indent → `SLLiteralContent`.
lemma content_break_indent_to_literal {n : Nat}
    {sp sp₁ sp₂ sp' : SurfPos}
    (h_text : SLNbLiteralText n sp sp₁)
    (h_break : SBBreak sp₁ sp₂)
    (h_indent : GOpt (fun a b => SIndentLe n a b ∧ b.chars = []) sp₂ sp') :
    SLLiteralContent n sp sp' :=
  SLLiteralContent.mk n sp sp₁ sp₂ sp₂ sp₂ sp'
    (GOpt.some sp sp₁ (GSeq.mk sp sp₁ sp₁ h_text (GStar.nil sp₁)))
    (GOpt.some sp₁ sp₂ h_break) (GStar.nil sp₂) (GOpt.none sp₂) h_indent

-- Prefix a text line to `SLLiteralContent` when no break separates them.
-- (The "tail has text" sub-case is unreachable when contentIndent ≥ 1 and
-- collectLineContentLoop has sufficient fuel — it always ends at break/EOF.)

-- SIndent n converts to GStar SNbChar (each indent space is non-break).
lemma SIndent_gives_GStar_SNbChar {n : Nat} {sp sp' : SurfPos}
    (h : SIndent n sp sp') : GStar SNbChar sp sp' := by
  induction h with
  | zero => exact GStar.nil _
  | succ k rest col _ _ ih =>
    exact GStar.cons _ _ _ (not_isLineBreak_gives_SNbChar ' ' rest col (by decide) (by decide) (by decide)) ih

-- SIndentLe n converts to GStar SNbChar.
lemma SIndentLe_gives_GStar_SNbChar {n : Nat} {sp sp' : SurfPos}
    (h : SIndentLe n sp sp') : GStar SNbChar sp sp' := by
  obtain ⟨_, _, h_indent⟩ := h
  exact SIndent_gives_GStar_SNbChar h_indent

-- Extend GPlus with additional GStar elements.
lemma GPlus_extend_GStar {P : SurfPos → SurfPos → Prop} {sp₁ sp₂ sp₃ : SurfPos}
    (h₁ : GPlus P sp₁ sp₂) (h₂ : GStar P sp₂ sp₃) : GPlus P sp₁ sp₃ :=
  match h₁ with
  | .mk _ sp_m _ h_first h_rest => GPlus.mk _ sp_m _ h_first (GStar_trans h_rest h₂)

-- Convert GPlus to GStar.
lemma GPlus_to_GStar {P : SurfPos → SurfPos → Prop} {sp₁ sp₂ : SurfPos}
    (h : GPlus P sp₁ sp₂) : GStar P sp₁ sp₂ :=
  match h with
  | .mk _ _ _ h_first h_rest => GStar.cons _ _ _ h_first h_rest

lemma prefix_text_literal_content {n : Nat}
    {sp sp₁ sp' : SurfPos}
    (h_text : SLNbLiteralText n sp sp₁)
    (h_tail : SLLiteralContent n sp₁ sp') :
    SLLiteralContent n sp sp' := by
  match h_tail with
  | .mk _ _ sp_t1 sp_t2 sp_t3 sp_t4 _ h_opt_text h_opt_break h_trail_empties h_trail_cmts h_trail_indent =>
    match h_opt_text with
    | .none _ =>
      exact SLLiteralContent.mk n sp sp₁ sp_t2 sp_t3 sp_t4 sp'
        (GOpt.some sp sp₁ (GSeq.mk sp sp₁ sp₁ h_text (GStar.nil sp₁)))
        h_opt_break h_trail_empties h_trail_cmts h_trail_indent
    | .some _ _ h_gseq =>
      -- The tail starts with text: compose h_text with the tail's text
      match h_gseq with
      | GSeq.mk _ sp_m _ h_text2 h_conts =>
        match h_text with
        | SLNbLiteralText.mk _ _ sp_e1 _ h_empties1 h_seq1 =>
          match h_seq1 with
          | GSeq.mk _ sp_i1 _ h_indent1 h_chars1 =>
            match h_text2 with
            | SLNbLiteralText.mk _ _ sp_e2 _ h_empties2 h_seq2 =>
              match h_seq2 with
              | GSeq.mk _ sp_i2 _ h_indent2 h_chars2 =>
                match h_empties2 with
                | GStar.nil _ =>
                  -- No empties between texts: merge GPlus spans through indent
                  exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp_t4 sp'
                    (GOpt.some sp sp_t1
                      (GSeq.mk sp sp_m sp_t1
                        (SLNbLiteralText.mk n sp sp_e1 sp_m h_empties1
                          (GSeq.mk sp_e1 sp_i1 sp_m h_indent1
                            (GPlus_extend_GStar h_chars1
                              (GStar_trans (SIndent_gives_GStar_SNbChar h_indent2)
                                (GPlus_to_GStar h_chars2)))))
                        h_conts))
                    h_opt_break h_trail_empties h_trail_cmts h_trail_indent
                | GStar.cons _ sp_f _ h_first_empty h_rest_empties =>
                  -- Has empties: first empty contains a break we can use
                  match h_first_empty with
                  | SLEmpty.block _ _ sp_x _ _ _ h_opt_ile h_break =>
                    have new_text : SLNbLiteralText n sp_f sp_m :=
                      SLNbLiteralText.mk n sp_f sp_e2 sp_m h_rest_empties
                        (GSeq.mk sp_e2 sp_i2 sp_m h_indent2 h_chars2)
                    have cont_line : SBNbLiteralNext n sp_x sp_m :=
                      SBNbLiteralNext.mk n sp_x sp_f sp_m h_break new_text
                    match h_opt_ile with
                    | GOpt.none _ =>
                      -- No indent before break: use h_text as-is
                      exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp_t4 sp'
                        (GOpt.some sp sp_t1
                          (GSeq.mk sp sp₁ sp_t1 h_text
                            (GStar.cons sp₁ sp_m sp_t1 cont_line h_conts)))
                        h_opt_break h_trail_empties h_trail_cmts h_trail_indent
                    | GOpt.some _ _ h_ile =>
                      -- Absorb indent-le spaces into GPlus, extend text to sp_x
                      exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp_t4 sp'
                        (GOpt.some sp sp_t1
                          (GSeq.mk sp sp_x sp_t1
                            (SLNbLiteralText.mk n sp sp_e1 sp_x h_empties1
                              (GSeq.mk sp_e1 sp_i1 sp_x h_indent1
                                (GPlus_extend_GStar h_chars1
                                  (SIndentLe_gives_GStar_SNbChar h_ile))))
                            (GStar.cons sp_x sp_m sp_t1 cont_line h_conts)))
                        h_opt_break h_trail_empties h_trail_cmts h_trail_indent
                  | .flow _ _ _ _ _ hc _ _ =>
                    exact absurd hc (by obtain h | h := hc <;> cases h)
                  | .flowLt _ _ _ _ _ hc _ _ =>
                    exact absurd hc (by obtain h | h := hc <;> cases h)

/-! ### §8b-walk  The landing walk at a block-scalar stop

`collectBlockScalarLoop` stops at end of input, at a document boundary, or at
a line the scalar does not own: fewer than `contentIndent` spaces and then a
non-space non-break character.  A `[79] s-l-comments` walk read from the stop
is pinned by the characters alone:

* at end of input every unit is zero-width, so the walk goes nowhere;
* at a stop line whose character is not `#` and not a tab, no unit derives at
  all — `[66] s-separate-in-line` cannot cross the character and
  `[76] b-comment` cannot end on it;
* at a `#` line the first unit is forced to consume exactly the spaces, the
  comment text, and its break — `[169] l-trail-comments`' head — and the
  walk's remaining units are `[78] l-comment`, `[169]`'s own rider, verbatim.

The TAB stop is the one shape the walk can enter (`[66]`'s `s-white+` admits
tabs) but `[168]`/`[169]` cannot absorb (`s-indent` is spaces-only); it is
returned as the named residue `BlockScalarTabStop`, not absorbed. -/

/-- The loop's TAB stop: a line of spaces headed by a TAB.  A `[79]` walk can
    cross such a line but no `[170]`/`[174]` derivation absorbs it, so the
    runtime refuses it — `blockScalarTabStop`, the gate in
    `scanBlockScalarBody`, reads exactly this shape at the loop's stop and
    throws `tabInIndentation` there.  The residue therefore survives only in
    the LOOP lemma (which has no error channel); every `.ok` face refutes it
    via `not_blockScalarTabStop_of_gate` below. -/
def BlockScalarTabStop (sp : SurfPos) : Prop :=
  ∃ j rest, sp.chars = List.replicate j ' ' ++ '\t' :: rest

-- Build the `[63]` run a spaces-then-tab opening describes, landing on the
-- tab (existentially: the landing column is `sp.col + j`, which the consumer
-- below does not need).
private lemma sindent_of_replicate {j : Nat} {tail : List Char} :
    ∀ {sp : SurfPos}, sp.chars = List.replicate j ' ' ++ tail →
      ∃ sx, SIndent j sp sx ∧ sx.chars = tail := by
  induction j with
  | zero =>
    intro sp h
    exact ⟨sp, SIndent.zero sp, by simpa using h⟩
  | succ j' ih =>
    intro sp h
    obtain ⟨cs, col⟩ := sp
    simp only [List.replicate_succ, List.cons_append] at h
    subst h
    obtain ⟨sx, hind, hxchars⟩ :=
      ih (sp := ⟨List.replicate j' ' ' ++ tail, col + 1⟩) rfl
    exact ⟨sx, SIndent.succ j' _ col sx hind, hxchars⟩

/-- The gate refutes the residue: at a state whose `blockScalarTabStop` test
    did not fire, no corresponding surface position opens with spaces and
    then a tab — `skipSpaces` would land exactly on that tab
    (`skipSpaces_lands_at_tab`), which is the gate's firing condition. -/
lemma not_blockScalarTabStop_of_gate {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp)
    (hgate : ¬ blockScalarTabStop sc = true) :
    ¬ BlockScalarTabStop sp := by
  rintro ⟨j, rest, hchars⟩
  obtain ⟨sx, hind, hxchars⟩ := sindent_of_replicate hchars
  have hpk := (L4YAML.Proofs.LandingTab.skipSpaces_lands_at_tab hcorr hind
    (by rw [hxchars]; rfl)).1
  exact hgate (by simp [blockScalarTabStop, hpk])

-- SurfPos extensionality: the two fields determine the position.
private lemma surfpos_ext {a b : SurfPos} (hc : a.chars = b.chars)
    (hl : a.col = b.col) : a = b := by
  cases a; cases b; simp_all

-- `[63]`'s characters and column, locally (the coupling file's versions sit
-- in a namespace this file does not open).
private lemma sindent_chars' {k : Nat} {sp sp' : SurfPos} (h : SIndent k sp sp') :
    sp.chars = List.replicate k ' ' ++ sp'.chars := by
  induction h with
  | zero => rfl
  | succ n rest col s' _ ih => simpa [List.replicate_succ] using ih

private lemma sindent_col' {k : Nat} {sp sp' : SurfPos} (h : SIndent k sp sp') :
    sp'.col = sp.col + k := by
  induction h with
  | zero => exact (Nat.add_zero _).symm
  | succ n rest col s' _ ih => simp only [] at ih ⊢; omega

-- `[33]`: one `s-white` step consumes the head, which is a space or tab.
lemma sswhite_head {sp sp' : SurfPos} (h : SSWhite sp sp') :
    ∃ ch rest, sp.chars = ch :: rest ∧ (ch = ' ' ∨ ch = '\t') ∧
      sp' = ⟨rest, sp.col + 1⟩ := by
  cases h with
  | space rest col => exact ⟨' ', rest, rfl, Or.inl rfl, rfl⟩
  | tab rest col => exact ⟨'\t', rest, rfl, Or.inr rfl, rfl⟩

-- A white run read at `j` spaces followed by a non-white character stays
-- inside the spaces: `k ≤ j` consumed, landing characters and column pinned.
lemma gstar_white_spaces_stop {c : Char} {rest : List Char} {sp sp' : SurfPos}
    (h : GStar SSWhite sp sp') :
    ∀ j : Nat, sp.chars = List.replicate j ' ' ++ c :: rest →
      c ≠ ' ' → c ≠ '\t' →
      ∃ k, k ≤ j ∧ sp'.chars = List.replicate (j - k) ' ' ++ c :: rest ∧
        sp'.col = sp.col + k := by
  induction h with
  | nil =>
    intro j hchars _ _
    exact ⟨0, Nat.zero_le _, by simpa using hchars, (Nat.add_zero _).symm⟩
  | cons s mid e h1 _ ih =>
    intro j hchars hc_sp hc_tab
    obtain ⟨ch, rest', hch, hcw, hmid⟩ := sswhite_head h1
    match j with
    | 0 =>
      rw [hchars] at hch
      simp only [List.replicate, List.nil_append, List.cons.injEq] at hch
      cases hcw with
      | inl h' => exact absurd (hch.1.trans h') hc_sp
      | inr h' => exact absurd (hch.1.trans h') hc_tab
    | j' + 1 =>
      rw [hchars] at hch
      rw [List.replicate_succ, List.cons_append] at hch
      have hch' := List.cons.injEq .. ▸ hch
      obtain ⟨-, hrest⟩ := List.cons.inj hch
      have hmidchars : mid.chars = List.replicate j' ' ' ++ c :: rest := by
        rw [hmid]; exact hrest.symm
      obtain ⟨k, hk, hchars', hcol⟩ := ih j' hmidchars hc_sp hc_tab
      have hmidcol : mid.col = s.col + 1 := by rw [hmid]
      refine ⟨k + 1, by omega, ?_, by omega⟩
      have : j' + 1 - (k + 1) = j' - k := by omega
      rw [this]; exact hchars'

-- A character other than `\\n`/`\\r` is not a break, at the Prop face.
private lemma not_break_char {c : Char} (h1 : c ≠ '\n') (h2 : c ≠ '\r') :
    ¬ isLineBreakProp c := by
  intro h
  rcases h with h | h
  · exact h1 (by simpa [isLineFeedProp, beq_iff_eq] using h)
  · exact h2 (by simpa [isCarriageReturnProp, beq_iff_eq] using h)

-- `[76]` cannot fire at a nonempty position whose head is not a line break.
lemma sbcomment_head_refuted {c : Char} {rest : List Char} {sp sp' : SurfPos}
    (hchars : sp.chars = c :: rest) (hcb : ¬ isLineBreakProp c)
    (h : SBComment sp sp') : False := by
  cases h with
  | «break» =>
    rename_i hb
    cases hb <;>
      · injection hchars with h1 _
        first
        | exact hcb (h1 ▸ show isLineBreakProp '\r' from Or.inr (by simp [isCarriageReturnProp]))
        | exact hcb (h1 ▸ show isLineBreakProp '\n' from Or.inl (by simp [isLineFeedProp]))
  | eof => cases hchars

-- …and at a spaces-then-`c` line it cannot fire anywhere in the spaces either.
lemma sbcomment_at_spaces_refuted {j : Nat} {c : Char} {rest : List Char}
    {sp sp' : SurfPos}
    (hchars : sp.chars = List.replicate j ' ' ++ c :: rest)
    (hcb : ¬ isLineBreakProp c)
    (h : SBComment sp sp') : False := by
  match j with
  | 0 => exact sbcomment_head_refuted (by simpa using hchars) hcb h
  | j' + 1 =>
    refine sbcomment_head_refuted (c := ' ')
      (rest := List.replicate j' ' ' ++ c :: rest) ?_ ?_ h
    · rw [hchars, List.replicate_succ, List.cons_append]
    · exact not_break_char (by decide) (by decide)

-- One `[78]`-shaped unit (separation, optional comment text, comment break)
-- read at a line of `j` spaces and then a non-space non-tab non-break
-- character `c`: it derives only if `c = '#'`, and then the separation
-- consumed exactly the spaces and the text is present, pinned past them.
lemma comment_unit_at_spaces {j : Nat} {c : Char} {rest : List Char}
    {sp sp₁ sp₂ sp' : SurfPos}
    (hchars : sp.chars = List.replicate j ' ' ++ c :: rest)
    (hc_sp : c ≠ ' ') (hc_tab : c ≠ '\t') (hcb : ¬ isLineBreakProp c)
    (hsep : SSeparateInLine sp sp₁)
    (hopt : GOpt SCNbCommentText sp₁ sp₂)
    (hbc : SBComment sp₂ sp') :
    c = '#' ∧ sp₁ = ⟨c :: rest, sp.col + j⟩ ∧ SCNbCommentText sp₁ sp₂ := by
  have hpin : ∃ k, k ≤ j ∧ sp₁.chars = List.replicate (j - k) ' ' ++ c :: rest ∧
      sp₁.col = sp.col + k := by
    cases hsep with
    | whites =>
      rename_i hp
      match hp with
      | GPlus.mk _ m _ h1 h2 =>
        exact gstar_white_spaces_stop (GStar.cons _ m _ h1 h2) j hchars hc_sp hc_tab
    | startOfLine => exact ⟨0, Nat.zero_le _, by simpa using hchars, (Nat.add_zero _).symm⟩
  obtain ⟨k, hk, hch1, hcol1⟩ := hpin
  rcases Nat.lt_or_ge k j with hlt | hge
  · -- spaces remain at sp₁: the text needs `#`, the break needs a break —
    -- both stare at a space.
    exfalso
    have hj : j - k = (j - k - 1) + 1 := by omega
    rw [hj, List.replicate_succ, List.cons_append] at hch1
    cases hopt with
    | none =>
      exact sbcomment_head_refuted hch1 (not_break_char (by decide) (by decide)) hbc
    | some _ htext =>
      cases htext with
      | mk =>
        injection hch1 with h1 _
        cases h1
  · -- the separation consumed all `j` spaces
    have hkj : k = j := Nat.le_antisymm (by omega) hge
    subst hkj
    have hch1' : sp₁.chars = c :: rest := by simpa using hch1
    have hpos : sp₁ = ⟨c :: rest, sp.col + k⟩ := surfpos_ext hch1' hcol1
    cases hopt with
    | none => exact absurd hbc (fun h => sbcomment_head_refuted hch1' hcb h)
    | some _ htext =>
      have hc_hash : c = '#' := by
        cases htext with
        | mk =>
          injection hch1' with h1 _
          exact h1.symm
      exact ⟨hc_hash, hpos, htext⟩

/-- `[79]` at a stop line whose character is not `#`, not a tab, not a space
    and not a break: the walk is forced empty. -/
lemma sslcomments_forced_trivial {j : Nat} {c : Char} {rest : List Char}
    {sp sp_mid : SurfPos}
    (hchars : sp.chars = List.replicate j ' ' ++ c :: rest)
    (hc_sp : c ≠ ' ') (hc_tab : c ≠ '\t') (hc_hash : c ≠ '#')
    (hcb : ¬ isLineBreakProp c)
    (h : SSLComments sp sp_mid) : sp_mid = sp := by
  cases h with
  | withComment =>
    rename_i hsb hstar
    cases hsb with
    | withSep =>
      rename_i hsep hopt hbc
      exact absurd (comment_unit_at_spaces hchars hc_sp hc_tab hcb hsep hopt hbc).1 hc_hash
    | noSep =>
      rename_i hbc
      exact (sbcomment_at_spaces_refuted hchars hcb hbc).elim
  | startOfLine =>
    rename_i hstar
    cases hstar with
    | nil => rfl
    | cons =>
      rename_i h1 h2
      cases h1 with
      | mk =>
        rename_i hsep hopt hbc
        exact absurd (comment_unit_at_spaces hchars hc_sp hc_tab hcb hsep hopt hbc).1 hc_hash

/-- `[79]` at a `#`-headed stop line: the walk is empty, or it opens with the
    comment — text and break pinned past the spaces — and the rest of the
    walk is bare `[78] l-comment`s, `[169]`'s own rider, verbatim. -/
lemma sslcomments_peel_hash {j : Nat} {rest : List Char} {sp sp_mid : SurfPos}
    (hchars : sp.chars = List.replicate j ' ' ++ '#' :: rest)
    (h : SSLComments sp sp_mid) :
    sp_mid = sp ∨
    ∃ sp_t sp_b, SCNbCommentText ⟨'#' :: rest, sp.col + j⟩ sp_t ∧
      SBComment sp_t sp_b ∧ GStar SLComment sp_b sp_mid := by
  have hcb : ¬ isLineBreakProp '#' := not_break_char (by decide) (by decide)
  cases h with
  | withComment =>
    rename_i hsb hstar
    cases hsb with
    | withSep =>
      rename_i hsep hopt hbc
      obtain ⟨-, hpin, htext⟩ :=
        comment_unit_at_spaces hchars (by decide) (by decide) hcb hsep hopt hbc
      exact Or.inr ⟨_, _, hpin ▸ htext, hbc, hstar⟩
    | noSep =>
      rename_i hbc
      exact (sbcomment_at_spaces_refuted hchars hcb hbc).elim
  | startOfLine =>
    rename_i hstar
    cases hstar with
    | nil => exact Or.inl rfl
    | cons =>
      rename_i h1 h2
      cases h1 with
      | mk =>
        rename_i hsep hopt hbc
        obtain ⟨-, hpin, htext⟩ :=
          comment_unit_at_spaces hchars (by decide) (by decide) hcb hsep hopt hbc
        exact Or.inr ⟨_, _, hpin ▸ htext, hbc, h2⟩

-- `[79]` at end of input: every unit is zero-width, so the walk goes nowhere.
lemma ssepinline_at_eof {sp sp' : SurfPos} (hchars : sp.chars = [])
    (h : SSeparateInLine sp sp') : sp' = sp := by
  cases h with
  | whites =>
    rename_i hp
    match hp with
    | GPlus.mk _ m _ h1 _ =>
      obtain ⟨ch, rest, hch, -, -⟩ := sswhite_head h1
      rw [hchars] at hch; cases hch
  | startOfLine => rfl

lemma sbcomment_at_eof {sp sp' : SurfPos} (hchars : sp.chars = [])
    (h : SBComment sp sp') : sp' = sp := by
  cases h with
  | «break» =>
    rename_i hb
    cases hb <;> cases hchars
  | eof => rfl

lemma gopt_text_at_eof {sp sp' : SurfPos} (hchars : sp.chars = [])
    (h : GOpt SCNbCommentText sp sp') : sp' = sp := by
  cases h with
  | none => rfl
  | some _ htext => cases htext with | mk => cases hchars

lemma ssbcomment_at_eof {sp sp' : SurfPos} (hchars : sp.chars = [])
    (h : SSBComment sp sp') : sp' = sp := by
  cases h with
  | withSep =>
    rename_i hsep hopt hbc
    rw [ssepinline_at_eof hchars hsep] at hopt
    rw [gopt_text_at_eof hchars hopt] at hbc
    exact sbcomment_at_eof hchars hbc
  | noSep =>
    rename_i hbc
    exact sbcomment_at_eof hchars hbc

lemma slcomment_at_eof {sp sp' : SurfPos} (hchars : sp.chars = [])
    (h : SLComment sp sp') : sp' = sp := by
  cases h with
  | mk =>
    rename_i hsep hopt hbc
    rw [ssepinline_at_eof hchars hsep] at hopt
    rw [gopt_text_at_eof hchars hopt] at hbc
    exact sbcomment_at_eof hchars hbc

lemma gstar_slcomment_at_eof {sp sp' : SurfPos} (hchars : sp.chars = [])
    (h : GStar SLComment sp sp') : sp' = sp := by
  induction h with
  | nil => rfl
  | cons s m e h1 h2 ih =>
    have hm : m = s := slcomment_at_eof hchars h1
    subst hm
    exact ih hchars

lemma sslcomments_at_eof {sp sp_mid : SurfPos} (hchars : sp.chars = [])
    (h : SSLComments sp sp_mid) : sp_mid = sp := by
  cases h with
  | withComment =>
    rename_i hsb hstar
    rw [ssbcomment_at_eof hchars hsb] at hstar
    exact gstar_slcomment_at_eof hchars hstar
  | startOfLine =>
    rename_i hstar
    exact gstar_slcomment_at_eof hchars hstar

-- The runtime side of the stop shape: a partial `consumeExactSpaces` run
-- ends staring at a non-space.
lemma consumeExactSpaces_partial_stop (sc : ScannerState) (count : Nat)
    (hlt : (consumeExactSpaces sc count).1 < count) :
    (consumeExactSpaces sc count).2.peek? ≠ some ' ' := by
  induction count generalizing sc with
  | zero => omega
  | succ n ih =>
    by_cases hpeek : sc.peek? = some ' '
    · rw [consumeExactSpaces_succ_space_fst sc n hpeek] at hlt
      rw [consumeExactSpaces_succ_space_snd sc n hpeek]
      exact ih sc.advance (by omega)
    · rw [consumeExactSpaces_succ_not_space sc n hpeek]
      exact hpeek

-- …and the document-boundary stop peeks a `-` or a `.`.
lemma atDocumentBoundary_peek (sc : ScannerState)
    (h : atDocumentBoundary sc = true) :
    sc.peek? = some '-' ∨ sc.peek? = some '.' := by
  have h0 : sc.peekAt? 0 = sc.peek? := rfl
  unfold atDocumentBoundary atDocumentStart atDocumentEnd at h
  rw [Bool.or_eq_true] at h
  cases h with
  | inl h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact Or.inl (h0 ▸ h.1.1.1.2)
  | inr h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact Or.inr (h0 ▸ h.1.1.1.2)

-- Offset monotonicity for the loop's fuel invariant.
private lemma advance_offset_ge' (s : ScannerState) : s.advance.offset ≥ s.offset := by
  by_cases h : s.offset < s.inputEnd
  · have := advance_offset_eq s h
    have := raw_next_gt s.input s.offset
    omega
  · unfold ScannerState.advance
    simp only [h, ↓reduceIte]
    exact Nat.le_refl _

lemma consumeExactSpaces_offset_ge (sc : ScannerState) (count : Nat) :
    (consumeExactSpaces sc count).2.offset ≥ sc.offset := by
  induction count generalizing sc with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    by_cases hpeek : sc.peek? = some ' '
    · rw [consumeExactSpaces_succ_space_snd sc n hpeek]
      exact Nat.le_trans (advance_offset_ge' sc) (ih sc.advance)
    · rw [consumeExactSpaces_succ_not_space sc n hpeek]
      exact Nat.le_refl _

lemma collectLineContentLoop_offset_ge (sc : ScannerState) (content : String)
    (fuel : Nat) :
    (collectLineContentLoop sc content fuel).2.offset ≥ sc.offset := by
  induction fuel generalizing sc content with
  | zero => exact Nat.le_refl _
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · exact Nat.le_refl _
      · exact Nat.le_trans (advance_offset_ge' sc) (ih sc.advance _)
    · exact Nat.le_refl _

-- `peek? = none` at a correspondence: the surface characters are exhausted.
lemma peek_none_chars_nil {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = none) : sp.chars = [] := by
  cases hch : sp.chars with
  | nil => rfl
  | cons c cs =>
    exfalso
    obtain ⟨pre, hcat, hsize⟩ := hcorr.input_prefix
    have hend := hcorr.end_eq
    have hlt := peek_none_not_lt hpeek
    have h1 : listByteSize sc.input.toList = listByteSize pre + listByteSize sp.chars := by
      rw [hcat, listByteSize_append]
    have h2 := utf8ByteSize_eq_listByteSize sc.input
    have h3 : 0 < listByteSize sp.chars :=
      listByteSize_pos_of_ne_nil (by rw [hch]; simp)
    omega

-- State `inputEnd` is untouched by the loops the block-scalar body composes.
lemma consumeExactSpaces_inputEnd (sc : ScannerState) (count : Nat) :
    (consumeExactSpaces sc count).2.inputEnd = sc.inputEnd := by
  induction count generalizing sc with
  | zero => rfl
  | succ n ih =>
    by_cases hpeek : sc.peek? = some ' '
    · rw [consumeExactSpaces_succ_space_snd sc n hpeek]
      rw [ih sc.advance, advance_inputEnd]
    · rw [consumeExactSpaces_succ_not_space sc n hpeek]

lemma collectLineContentLoop_inputEnd (sc : ScannerState) (content : String)
    (fuel : Nat) :
    (collectLineContentLoop sc content fuel).2.inputEnd = sc.inputEnd := by
  induction fuel generalizing sc content with
  | zero => rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih sc.advance, advance_inputEnd]
    · rfl

-- The character the line loop stops on fails its continue test: it is a
-- break, a non-printable, or a BOM.  The fuel premise mirrors the runtime's
-- own computation (`fuel ≥ B - offset + 1` with the state's window inside
-- `B`), so a fuel-out stop cannot masquerade as a character stop.
lemma collectLineContentLoop_stop_char {B : Nat} (sc : ScannerState)
    (content : String) (fuel : Nat) {c' : Char}
    (h_fuel : fuel ≥ B - sc.offset + 1) (h_ie : sc.inputEnd ≤ B)
    (hpk : (collectLineContentLoop sc content fuel).2.peek? = some c') :
    (isLineBreakBool c' || !isPrintableBool c' || c' == '﻿') = true := by
  induction fuel generalizing sc content with
  | zero => omega
  | succ fuel' ih =>
    unfold collectLineContentLoop at hpk
    split at hpk
    · rename_i c hpeek
      split at hpk
      · rename_i hstop
        rw [hpeek] at hpk
        cases hpk
        exact hstop
      · rename_i hstop
        have hmore := peek_some_has_more hpeek
        have hadv : sc.advance.offset > sc.offset := by
          have := advance_offset_eq sc hmore
          have := raw_next_gt sc.input sc.offset
          omega
        exact ih sc.advance (content.push _)
          (by have := advance_inputEnd sc; omega)
          (by rw [advance_inputEnd]; exact h_ie) hpk
    · rename_i hpeek
      rw [hpeek] at hpk
      cases hpk

/-! ### §8b-main collectBlockScalarLoop literal production

  The main loop theorem: `collectBlockScalarLoop` produces `SLLiteralContent n`.
  By induction on fuel, each iteration either:
  - stops (empty content / trailing indent),
  - processes an empty line (prepend to tail),
  - processes a content line + break (content_break_tail_to_literal),
  - processes a content line without break (content_only or prefix_text). -/

-- Two characters a non-printable stop can never be (printable, non-BOM).
private lemma nonprint_ne (c d : Char)
    (hd : isPrintableBool d = true ∧ (d == '\uFEFF') = false)
    (h : ¬ isPrintableBool c = true ∨ (c == '\uFEFF') = true) : c ≠ d := by
  intro hceq
  subst hceq
  rcases h with h | h
  · exact h hd.1
  · rw [hd.2] at h; cases h

-- `collectBlockScalarLoop` produces `SLLiteralContent n`, preserves
-- correspondence, and (item 95) pins the landing walk at its stop: either
-- any `[79] s-l-comments` walk from the end of the derivation is absorbable
-- into the SAME `SLLiteralContent` (extended through the trailing `[169]`
-- slot, or forced empty by the stop character), or the stop is the named
-- TAB residue.  The fuel premises mirror the runtime's own computation, so
-- a fuel-out exit is unreachable.
lemma collectBlockScalarLoop_literal_prod
    (sc : ScannerState) (sp : SurfPos)
    (rawContent : String) (fuel : Nat) (contentIndent inputEnd : Nat)
    (hcorr : ScannerSurfCorr sc sp)
    (h_fuel : fuel ≥ inputEnd - sc.offset + 1) (h_ie : sc.inputEnd ≤ inputEnd) :
    ∃ sp', SLLiteralContent contentIndent sp sp' ∧
           ScannerSurfCorr (collectBlockScalarLoop sc rawContent fuel contentIndent inputEnd).2 sp' ∧
           ((∀ sp_mid : SurfPos, SSLComments sp' sp_mid →
               SLLiteralContent contentIndent sp sp_mid) ∨
             BlockScalarTabStop sp') := by
  induction fuel generalizing sc sp rawContent with
  | zero => omega
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    dsimp only []
    split
    · -- Document boundary: stop.  The boundary's own character (`-` or `.`)
      -- pins the walk empty.
      rename_i hbdry
      have hpeekb : sc.peek? = some '-' ∨ sc.peek? = some '.' :=
        atDocumentBoundary_peek sc (Bool.and_eq_true_iff.mp hbdry).2
      refine ⟨sp, empty_literal_content sp, hcorr, Or.inl fun sp_mid W => ?_⟩
      rcases hpeekb with hpk | hpk
      · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpk
        rw [sslcomments_forced_trivial (j := 0) (c := '-') (rest := rest)
          (by rw [hsp_eq]; simp) (by decide) (by decide) (by decide)
          (not_break_char (by decide) (by decide)) W]
        exact empty_literal_content sp
      · obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpk
        rw [sslcomments_forced_trivial (j := 0) (c := '.') (rest := rest)
          (by rw [hsp_eq]; simp) (by decide) (by decide) (by decide)
          (not_break_char (by decide) (by decide)) W]
        exact empty_literal_content sp
    · -- Not document boundary
      -- Get correspondence and indent for consumeExactSpaces result
      obtain ⟨sp_spaces, h_sindent, hcorr_spaces⟩ :=
        consumeExactSpaces_sindent_partial sc sp contentIndent hcorr
      have hle : (consumeExactSpaces sc contentIndent).1 ≤ contentIndent :=
        consumeExactSpaces_fst_le sc contentIndent
      split
      · -- peek? = none after spaces: EOF → trailing indent; the walk is
        -- zero-width at end of input.
        rename_i hpeek
        have hnil : sp_spaces.chars = [] := peek_none_chars_nil hcorr_spaces hpeek
        exact ⟨sp_spaces,
               indent_only_literal_content ⟨_, hle, h_sindent⟩ hnil,
               hcorr_spaces,
               Or.inl fun sp_mid W => by
                 rw [sslcomments_at_eof hnil W]
                 exact indent_only_literal_content ⟨_, hle, h_sindent⟩ hnil⟩
      · rename_i c hpeek
        split
        · -- isLineBreakBool c = true: empty line
          rename_i hlb
          obtain ⟨sp_nl, h_break, hcorr_nl⟩ :=
            consumeNewline_sbreak_corr _ sp_spaces c hcorr_spaces hpeek hlb
          have h_empty : SLEmpty contentIndent .blockIn sp sp_nl :=
            SLEmpty.block contentIndent sp sp_spaces sp_nl .blockIn (Or.inr rfl)
              (GOpt.some sp sp_spaces ⟨_, hle, h_sindent⟩) h_break
          have ho1 := consumeExactSpaces_offset_ge sc contentIndent
          have hie1 := consumeExactSpaces_inputEnd sc contentIndent
          have hmore := peek_some_has_more hpeek
          have ho2 := consumeNewline_offset_advance _ c hpeek hlb
          have ho2a := ho2.1
          have hmore1 : (consumeExactSpaces sc contentIndent).2.offset < sc.inputEnd := by
            rw [← hie1]; exact hmore
          obtain ⟨sp_end, h_tail, hcorr_end, h_cl⟩ := ih _ sp_nl _ hcorr_nl
            (by omega) (by rw [ho2.2, hie1]; exact h_ie)
          exact ⟨sp_end, prepend_empty_to_literal_content h_empty h_tail, hcorr_end,
                 h_cl.imp_left fun cl sp_mid W =>
                   prepend_empty_to_literal_content h_empty (cl sp_mid W)⟩
        · split
          · -- Under-indent stop: `j < contentIndent` spaces, then a
            -- non-space non-break character.  The walk is pinned by that
            -- character: `#` re-parents into `[169]`'s slot, a TAB is the
            -- named residue, anything else forces the walk empty.
            rename_i hne_lb h_under
            have h_under' := h_under
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h_under'
            obtain ⟨hjlt, hlbf⟩ := h_under'
            have hc_sp : c ≠ ' ' := fun hceq =>
              consumeExactSpaces_partial_stop sc contentIndent hjlt (hceq ▸ hpeek)
            have hcbp : ¬ isLineBreakProp c := fun hp => by
              simp [(isLineBreak_iff c).mpr hp] at hlbf
            obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr_spaces hpeek
            have hchars : sp.chars =
                List.replicate (consumeExactSpaces sc contentIndent).1 ' ' ++ c :: rest := by
              rw [sindent_chars' h_sindent, hsp_eq]
            by_cases hc_tab : c = '\t'
            · subst hc_tab
              exact ⟨sp, empty_literal_content sp, hcorr,
                     Or.inr ⟨_, rest, hchars⟩⟩
            · by_cases hc_hash : c = '#'
              · -- `[169]` head: the walk re-parents verbatim
                subst hc_hash
                have hpos : sp_spaces =
                    ⟨'#' :: rest, sp.col + (consumeExactSpaces sc contentIndent).1⟩ :=
                  surfpos_ext (by rw [hsp_eq]) (sindent_col' h_sindent)
                refine ⟨sp, empty_literal_content sp, hcorr,
                        Or.inl fun sp_mid W => ?_⟩
                rcases sslcomments_peel_hash hchars W with heq | ⟨sp_t, sp_b, htext, hbc, hrider⟩
                · rw [heq]; exact empty_literal_content sp
                · exact SLLiteralContent.mk contentIndent sp sp sp sp sp_mid sp_mid
                    (GOpt.none sp) (GOpt.none sp) (GStar.nil sp)
                    (GOpt.some sp sp_mid
                      (SLTrailComments.mk contentIndent sp _ sp_t sp_b sp_mid
                        ⟨_, hjlt, hpos ▸ h_sindent⟩ htext hbc hrider))
                    (GOpt.none sp_mid)
              · -- any other character refuses every walk unit
                refine ⟨sp, empty_literal_content sp, hcorr,
                        Or.inl fun sp_mid W => ?_⟩
                rw [sslcomments_forced_trivial hchars hc_sp hc_tab hc_hash hcbp W]
                exact empty_literal_content sp
          · -- content line: full indent consumed
            rename_i hne_lb hne_under
            -- Derive: spacesConsumed = contentIndent (from ¬under-indent + ≤)
            have h_full : (consumeExactSpaces sc contentIndent).1 = contentIndent := by
              have : isLineBreakBool c = false := by
                cases h : isLineBreakBool c <;> simp_all
              simp only [this, Bool.not_false, Bool.and_true, decide_eq_true_eq] at hne_under
              omega
            -- Full indent proof
            obtain ⟨sp_spaces', h_sindent_full, hcorr_spaces'⟩ :=
              consumeExactSpaces_sindent_prod sc sp contentIndent hcorr h_full
            -- sp_spaces = sp_spaces' by uniqueness
            have hsp_eq : sp_spaces = sp_spaces' :=
              ScannerSurfCorr_unique hcorr_spaces hcorr_spaces'
            subst hsp_eq
            -- Content: collectLineContentLoop
            have hne_lb_bool : ¬isLineBreakBool c = true := hne_lb
            have hlb_f : isLineBreakBool c = false := by
              cases h : isLineBreakBool c with
              | false => rfl
              | true => exact absurd h hne_lb_bool
            by_cases hnb : (isPrintableBool c && c != '\uFEFF') = true
            · -- First char is nb-char: the line loop consumes ≥ 1 char.
              have hpr : isPrintableBool c = true := (Bool.and_eq_true_iff.mp hnb).1
              have hbom : (c == '\uFEFF') = false := by
                have h2 := (Bool.and_eq_true_iff.mp hnb).2
                cases h : (c == '\uFEFF') with
                | false => rfl
                | true => rw [bne, h] at h2; exact absurd h2 (by decide)
              -- GPlus SNbChar from content
              obtain ⟨sp_content, h_gplus, hcorr_content⟩ :=
                collectLineContentLoop_gplus_prod _ sp_spaces c ""
                  (inputEnd - (consumeExactSpaces sc contentIndent).2.offset + 1)
                  hcorr_spaces' hpeek hne_lb_bool hpr hbom (by omega)
              -- Build SLNbLiteralText
              have h_text_line : SLNbLiteralText contentIndent sp sp_content :=
                SLNbLiteralText.mk contentIndent sp sp sp_content (GStar.nil sp)
                  (GSeq.mk sp sp_spaces sp_content h_sindent_full h_gplus)
              -- Match on what follows: peek of result
              split
              · rename_i c' hpeek'
                split
                · -- Break after content: consume + recurse
                  rename_i hlb'
                  obtain ⟨sp_nl', h_break', hcorr_nl'⟩ :=
                    consumeNewline_sbreak_corr _ sp_content c' hcorr_content hpeek' hlb'
                  have ho1 := consumeExactSpaces_offset_ge sc contentIndent
                  have hie1 := consumeExactSpaces_inputEnd sc contentIndent
                  have ho3 := collectLineContentLoop_offset_ge
                    (consumeExactSpaces sc contentIndent).2 ""
                    (inputEnd - (consumeExactSpaces sc contentIndent).2.offset + 1)
                  have hie3 := collectLineContentLoop_inputEnd
                    (consumeExactSpaces sc contentIndent).2 ""
                    (inputEnd - (consumeExactSpaces sc contentIndent).2.offset + 1)
                  have hmore' := peek_some_has_more hpeek'
                  have ho4 := consumeNewline_offset_advance _ c' hpeek' hlb'
                  have ho4a := ho4.1
                  have hmore3 : (collectLineContentLoop (consumeExactSpaces sc contentIndent).2 ""
                      (inputEnd - (consumeExactSpaces sc contentIndent).2.offset + 1)).2.offset
                        < sc.inputEnd := by
                    rw [← hie1, ← hie3]; exact hmore'
                  obtain ⟨sp_end, h_tail, hcorr_end, h_cl⟩ := ih _ sp_nl' _ hcorr_nl'
                    (by omega) (by rw [ho4.2, hie3, hie1]; exact h_ie)
                  exact ⟨sp_end,
                         content_break_tail_to_literal h_text_line h_break' h_tail,
                         hcorr_end,
                         h_cl.imp_left fun cl sp_mid W =>
                           content_break_tail_to_literal h_text_line h_break' (cl sp_mid W)⟩
                · -- Line stopped at a non-nb-char: block scalar ends here,
                  -- and the stop character refuses every walk unit.
                  rename_i hlb'
                  have hne_fst := collectLineContentLoop_fst_nonempty
                    (consumeExactSpaces sc contentIndent).2 c ""
                    (inputEnd - (consumeExactSpaces sc contentIndent).2.offset + 1) hpeek
                    hne_lb_bool hpr hbom (by omega)
                  simp only [hne_fst, Bool.false_eq_true, ↓reduceIte]
                  have hstop := collectLineContentLoop_stop_char (B := inputEnd)
                    (consumeExactSpaces sc contentIndent).2 ""
                    (inputEnd - (consumeExactSpaces sc contentIndent).2.offset + 1)
                    (Nat.le_refl _)
                    (by rw [consumeExactSpaces_inputEnd]; exact h_ie) hpeek'
                  have hnp : ¬ isPrintableBool c' = true ∨ (c' == '\uFEFF') = true := by
                    rcases Bool.or_eq_true_iff.mp hstop with h | h
                    · rcases Bool.or_eq_true_iff.mp h with h | h
                      · exact absurd h hlb'
                      · exact Or.inl (by simpa using h)
                    · exact Or.inr h
                  obtain ⟨rest', hsp_eq'⟩ := peek_some_sp hcorr_content hpeek'
                  have hchars' : sp_content.chars =
                      List.replicate 0 ' ' ++ c' :: rest' := by
                    rw [hsp_eq']; simp
                  have hcbp' : ¬ isLineBreakProp c' := fun hp => hlb' ((isLineBreak_iff c').mpr hp)
                  refine ⟨sp_content, content_only_to_literal h_text_line, hcorr_content,
                          Or.inl fun sp_mid W => ?_⟩
                  rw [sslcomments_forced_trivial hchars'
                        (nonprint_ne c' ' ' (by decide) hnp)
                        (nonprint_ne c' '\t' (by decide) hnp)
                        (nonprint_ne c' '#' (by decide) hnp) hcbp' W]
                  exact content_only_to_literal h_text_line
              · -- peek? = none after content: EOF
                rename_i hpeek'
                have hnil := peek_none_chars_nil hcorr_content hpeek'
                exact ⟨sp_content, content_only_to_literal h_text_line, hcorr_content,
                       Or.inl fun sp_mid W => by
                         rw [sslcomments_at_eof hnil W]
                         exact content_only_to_literal h_text_line⟩
            · -- First char is NOT nb-char: the line loop consumes nothing and
              -- the block scalar ends after this line's indent.
              have hcond : (isLineBreakBool c || !isPrintableBool c || c == '\uFEFF') = true := by
                cases hp : isPrintableBool c with
                | false => simp
                | true =>
                  cases hb : (c == '\uFEFF') with
                  | true => simp
                  | false => exact absurd (by simp [hp, bne, hb]) hnb
              have hloop : collectLineContentLoop (consumeExactSpaces sc contentIndent).2 ""
                  (inputEnd - (consumeExactSpaces sc contentIndent).2.offset + 1)
                  = ("", (consumeExactSpaces sc contentIndent).2) := by
                unfold collectLineContentLoop
                simp only [hpeek, hcond, ↓reduceIte]
              rw [hloop]
              simp only [hpeek, hlb_f, Bool.false_eq_true, ↓reduceIte, String.isEmpty_iff]
              -- the stop character is non-printable or BOM: forced-trivial.
              -- An empty line run leaves the scanner at the line start `sc`:
              -- the line's indent belongs to the enclosing collection.
              have hnp : ¬ isPrintableBool c = true ∨ (c == '\uFEFF') = true := by
                cases hp : isPrintableBool c with
                | false => exact Or.inl (by simp)
                | true =>
                  cases hb : (c == '\uFEFF') with
                  | true => exact Or.inr rfl
                  | false => exact absurd (by simp [hp, bne, hb]) hnb
              obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr_spaces' hpeek
              have hchars : sp.chars = List.replicate contentIndent ' ' ++ c :: rest := by
                rw [sindent_chars' h_sindent_full, hsp_eq]
              have hcbp : ¬ isLineBreakProp c := fun hp => by
                simp [(isLineBreak_iff c).mpr hp] at hlb_f
              refine ⟨sp, empty_literal_content sp, hcorr, Or.inl fun sp_mid W => ?_⟩
              rw [sslcomments_forced_trivial hchars
                    (nonprint_ne c ' ' (by decide) hnp)
                    (nonprint_ne c '\t' (by decide) hnp)
                    (nonprint_ne c '#' (by decide) hnp) hcbp W]
              exact empty_literal_content sp

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
lemma headerChar_notWsLbBom (c : Char)
    (h : Grammar.isBlockScalarHeaderChar c = true) : notWsLbBom c := by
  unfold notWsLbBom Grammar.isBlockScalarHeaderChar at *
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (rfl | rfl) | ⟨h1, h2⟩
  · exact ⟨by native_decide, by native_decide, by native_decide⟩
  · exact ⟨by native_decide, by native_decide, by native_decide⟩
  · simp only [isWhiteSpaceBool, isSpaceBool, isTabBool,
               isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
               Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> (intro heq; subst heq; simp at h1 h2 <;> omega)

-- `parseBlockHeaderLoop` preserves the property that `peekBack?` is not ws/lb/BOM.
lemma parseBlockHeaderLoop_preserves_peekBack_not_ws
    (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (chomp : ChompStyle) (off : Option Nat) (fuel : Nat)
    (h_pb : ∀ c, sc.peekBack? = some c → notWsLbBom c) :
    ∀ c, (parseBlockHeaderLoop sc chomp off fuel).2.2.peekBack? = some c → notWsLbBom c := by
  induction fuel generalizing sc sp chomp off with
  | zero => simp only [parseBlockHeaderLoop]; exact h_pb
  | succ fuel' ih =>
    simp only [parseBlockHeaderLoop]
    split
    · rename_i hpk
      have hpeek := (peekBlockHeaderIndicator?_some hpk).1
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek; subst hsp_eq
      have hmore := peek_some_has_more hpeek
      exact ih sc.advance ⟨rest, sc.col + 1⟩
        (advance_non_newline_corr sc '-' rest hcorr hmore (by decide) (by decide))
        .strip off (fun c hc => by
          rw [advance_peekBack_eq_peek hcorr hmore (by decide) (by decide)] at hc
          cases hc; exact ⟨by decide, by decide, by decide⟩)
    · rename_i hpk
      have hpeek := (peekBlockHeaderIndicator?_some hpk).1
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek; subst hsp_eq
      have hmore := peek_some_has_more hpeek
      exact ih sc.advance ⟨rest, sc.col + 1⟩
        (advance_non_newline_corr sc '+' rest hcorr hmore (by decide) (by decide))
        .keep off (fun c hc => by
          rw [advance_peekBack_eq_peek hcorr hmore (by decide) (by decide)] at hc
          cases hc; exact ⟨by decide, by decide, by decide⟩)
    · rename_i c_peek _ _ hpk
      have hpeek := (peekBlockHeaderIndicator?_some hpk).1
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
lemma skipWhitespace_eq_of_same_surfpos {sc : ScannerState} {sp : SurfPos}
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

-- Proof that `scanBlockScalarSkipComment` is identity
-- when `peekBack?` returns a non-ws/lb/BOM char
-- and that it consumes nothing.
lemma scanBlockScalarSkipComment_noop (sc : ScannerState)
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
lemma scNbCommentText_irrefl (sp : SurfPos) : ¬ SCNbCommentText sp sp := by
  intro h
  match h with
  | .mk rest col _ hstar =>
    have : col ≥ col + 1 := gstar_gchar_col_le hstar
    omega

-- Mathematical unreachability: `#` comment without preceding whitespace after block header.
lemma scanBlockScalar_unreachable_comment_without_ws
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

-- `scanBlockScalarBody` for literal produces `SLLiteralContent` + correspondence.
-- Unwraps `scanBlockScalarBody` to expose `collectBlockScalarLoop`, applies
-- `collectBlockScalarLoop_literal_prod`, then adjusts for emitAt/simpleKey.
-- The header path's `inputEnd` preservation (private twins of
-- `LineOpenGuard`'s, which are not exported).
private lemma parseBlockHeaderLoop_inputEnd' (fuel : Nat) :
    ∀ (s : ScannerState) (chomp : ChompStyle) (eo : Option Nat),
    (parseBlockHeaderLoop s chomp eo fuel).2.2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s _ _; rfl
  | succ fuel' ih =>
    intro s chomp eo
    unfold parseBlockHeaderLoop
    split
    · exact (ih s.advance _ _).trans (advance_inputEnd s)
    · exact (ih s.advance _ _).trans (advance_inputEnd s)
    · split
      · exact (ih s.advance _ _).trans (advance_inputEnd s)
      · rfl
    · rfl

private lemma collectCommentTextLoop_inputEnd' (fuel : Nat) :
    ∀ (s : ScannerState) (text : String),
    (collectCommentTextLoop s text fuel).2.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s _; unfold collectCommentTextLoop; rfl
  | succ fuel' ih =>
    intro s text
    unfold collectCommentTextLoop
    split
    · split
      · rfl
      · exact (ih s.advance _).trans (advance_inputEnd s)
    · rfl

lemma skipWhitespaceLoop_inputEnd' (fuel : Nat) :
    ∀ (s : ScannerState), (skipWhitespaceLoop s fuel).inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s; simp [skipWhitespaceLoop]
  | succ fuel' ih =>
    intro s
    unfold skipWhitespaceLoop
    split
    · split
      · exact (ih s.advance).trans (advance_inputEnd s)
      · rfl
    · rfl

lemma skipWhitespace_inputEnd' (s : ScannerState) :
    (skipWhitespace s).inputEnd = s.inputEnd :=
  skipWhitespaceLoop_inputEnd' _ s

private lemma scanBlockScalarSkipComment_inputEnd' (s : ScannerState) :
    (scanBlockScalarSkipComment s).inputEnd = s.inputEnd := by
  unfold scanBlockScalarSkipComment
  split
  · dsimp only []
    generalize hp : collectCommentTextLoop s.advance ""
      (s.advance.inputEnd - s.advance.offset) = pr
    obtain ⟨text, s2⟩ := pr
    have hcc := collectCommentTextLoop_inputEnd'
      (s.advance.inputEnd - s.advance.offset) s.advance ""
    rw [hp] at hcc
    dsimp only [] at hcc
    split
    · split
      · exact hcc.trans (advance_inputEnd s)
      · rfl
    · rfl
  · rfl

private lemma scanBlockScalarConsumeNewline_inputEnd' {s s' : ScannerState}
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.inputEnd = s.inputEnd := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · have he := Except.ok.inj h; subst he
      exact consumeNewline_inputEnd s
    · split at h
      · have he := Except.ok.inj h; subst he; rfl
      · cases h
  · have he := Except.ok.inj h; subst he; rfl

/-- The composed header path (`|`/`>`, header chars, whitespace, comment,
    newline) leaves `inputEnd` alone — the fact the body lemmas' fuel premise
    needs at every caller. -/
lemma scanBlockScalar_afterNewline_inputEnd {sc s_after_nl : ScannerState}
    (hcn : scanBlockScalarConsumeNewline (scanBlockScalarSkipComment
      (skipWhitespace (parseBlockHeaderLoop sc.advance .clip none 2).2.2)) = .ok s_after_nl) :
    s_after_nl.inputEnd ≤ sc.inputEnd := by
  have h1 := scanBlockScalarConsumeNewline_inputEnd' hcn
  have h2 := scanBlockScalarSkipComment_inputEnd'
    (skipWhitespace (parseBlockHeaderLoop sc.advance .clip none 2).2.2)
  have h3 := skipWhitespace_inputEnd' (parseBlockHeaderLoop sc.advance .clip none 2).2.2
  have h4 := parseBlockHeaderLoop_inputEnd' 2 sc.advance .clip none
  have h5 := advance_inputEnd sc
  omega

lemma scanBlockScalarBody_literal_prod (sc_orig sc_after_nl : ScannerState)
    (sp : SurfPos) (chomp : ChompStyle) (explicitOffset : Option Nat)
    (startPos : YamlPos) {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc_after_nl sp)
    (h_ie : sc_after_nl.inputEnd ≤ sc_orig.inputEnd)
    (hok : scanBlockScalarBody sc_orig sc_after_nl chomp explicitOffset true startPos = .ok s') :
    ∃ sp' contentIndent,
      SLLiteralContent contentIndent sp sp' ∧ ScannerSurfCorr s' sp' ∧
      (∀ sp_mid : SurfPos, SSLComments sp' sp_mid →
        SLLiteralContent contentIndent sp sp_mid) := by
  unfold scanBlockScalarBody at hok
  dsimp only [] at hok
  cases hoff_eq : explicitOffset with
  | some d =>
    rw [hoff_eq] at hok
    -- autoDetectErr? = none, so the match on autoDetectErr? reduces to .ok path directly
    let contentIndent := (max 0 (sc_orig.currentIndent + (↑d : Int))).toNat
    let fuel := sc_orig.inputEnd - sc_after_nl.offset + 1
    obtain ⟨sp_loop, h_lit_content, hcorr_loop, h_absorb⟩ :=
      collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel contentIndent sc_orig.inputEnd hcorr
        (Nat.le_refl _) h_ie
    dsimp only [] at hok
    split at hok
    · cases hok
    · rename_i h_gate
      have h := Except.ok.inj hok; subst h
      exact ⟨sp_loop, contentIndent, h_lit_content,
             ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq, hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩,
             h_absorb.resolve_right (not_blockScalarTabStop_of_gate hcorr_loop h_gate)⟩
  | none =>
    rw [hoff_eq] at hok
    generalize h_auto : autoDetectBlockScalarIndent sc_after_nl
      (max 0 (sc_orig.currentIndent + 1)).toNat sc_orig.inputEnd = auto_res at hok
    obtain ⟨ci, err⟩ := auto_res
    simp only [] at h_auto hok
    cases h_err : err with
    | some e =>
      simp only [h_err] at hok
      cases hok
    | none =>
      simp only [h_err] at hok
      let fuel := sc_orig.inputEnd - sc_after_nl.offset + 1
      obtain ⟨sp_loop, h_lit_content, hcorr_loop, h_absorb⟩ :=
        collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel ci sc_orig.inputEnd hcorr
          (Nat.le_refl _) h_ie
      split at hok
      · cases hok
      · rename_i h_gate
        have h := Except.ok.inj hok; subst h
        exact ⟨sp_loop, ci, h_lit_content,
               ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq, hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩,
               h_absorb.resolve_right (not_blockScalarTabStop_of_gate hcorr_loop h_gate)⟩

-- `scanBlockScalarBody` for folded also produces `SLLiteralContent` + correspondence.
-- The scanner uses the same `collectBlockScalarLoop` for both literal and folded;
-- the only difference is post-processing of the collected content string.
lemma scanBlockScalarBody_folded_prod (sc_orig sc_after_nl : ScannerState)
    (sp : SurfPos) (chomp : ChompStyle) (explicitOffset : Option Nat)
    (startPos : YamlPos) {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc_after_nl sp)
    (h_ie : sc_after_nl.inputEnd ≤ sc_orig.inputEnd)
    (hok : scanBlockScalarBody sc_orig sc_after_nl chomp explicitOffset false startPos = .ok s') :
    ∃ sp' contentIndent,
      SLLiteralContent contentIndent sp sp' ∧ ScannerSurfCorr s' sp' ∧
      (∀ sp_mid : SurfPos, SSLComments sp' sp_mid →
        SLLiteralContent contentIndent sp sp_mid) := by
  unfold scanBlockScalarBody at hok
  dsimp only [] at hok
  cases hoff_eq : explicitOffset with
  | some d =>
    rw [hoff_eq] at hok
    let contentIndent := (max 0 (sc_orig.currentIndent + (↑d : Int))).toNat
    let fuel := sc_orig.inputEnd - sc_after_nl.offset + 1
    obtain ⟨sp_loop, h_lit_content, hcorr_loop, h_absorb⟩ :=
      collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel contentIndent sc_orig.inputEnd hcorr
        (Nat.le_refl _) h_ie
    dsimp only [] at hok
    split at hok
    · cases hok
    · rename_i h_gate
      have h := Except.ok.inj hok; subst h
      exact ⟨sp_loop, contentIndent, h_lit_content,
             ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq, hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩,
             h_absorb.resolve_right (not_blockScalarTabStop_of_gate hcorr_loop h_gate)⟩
  | none =>
    rw [hoff_eq] at hok
    generalize h_auto : autoDetectBlockScalarIndent sc_after_nl
      (max 0 (sc_orig.currentIndent + 1)).toNat sc_orig.inputEnd = auto_res at hok
    obtain ⟨ci, err⟩ := auto_res
    simp only [] at h_auto hok
    cases h_err : err with
    | some e =>
      simp only [h_err] at hok
      cases hok
    | none =>
      simp only [h_err] at hok
      let fuel := sc_orig.inputEnd - sc_after_nl.offset + 1
      obtain ⟨sp_loop, h_lit_content, hcorr_loop, h_absorb⟩ :=
        collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel ci sc_orig.inputEnd hcorr
          (Nat.le_refl _) h_ie
      split at hok
      · cases hok
      · rename_i h_gate
        have h := Except.ok.inj hok; subst h
        exact ⟨sp_loop, ci, h_lit_content,
               ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq, hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩,
               h_absorb.resolve_right (not_blockScalarTabStop_of_gate hcorr_loop h_gate)⟩

-- `scanBlockScalar` produces `SCLLiteral 0` or `SCLFolded 0` and preserves correspondence.
-- Header: FULLY PROVEN (delimiter + header chars + SSBComment).
-- Body: FULLY PROVEN for both literal and folded via `collectBlockScalarLoop_literal_prod`.
-- Dispatch: FULLY PROVEN for literal (`|`) and folded (`>`).
-- Note: hm constraint removed from SCLLiteral/SCLFolded (A11 — Nat encoding offset).
lemma scanBlockScalar_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hchar : sc.peek? = some '|' ∨ sc.peek? = some '>')
    (hok : scanBlockScalar sc = .ok s') :
    ∃ sp', (SCLLiteral 0 sp sp' ∨ SCLFolded 0 sp sp') ∧ ScannerSurfCorr s' sp' ∧
      (∀ sp_mid : SurfPos, SSLComments sp' sp_mid →
        SCLLiteral 0 sp sp_mid ∨ SCLFolded 0 sp sp_mid) := by
  unfold scanBlockScalar at hok
  dsimp only [] at hok
  -- Step 1: advance past '|' or '>'
  -- Step 2: parseBlockHeaderLoop → [163]/[164] indicators in either order
  obtain ⟨sp_adv_gen, hcorr_adv⟩ := advance_corr sc sp hcorr
  obtain ⟨sp_hdr, h_hdr_chars, hcorr_hdr⟩ :=
    parseBlockHeaderLoop_prod sc.advance sp_adv_gen hcorr_adv 2
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
    have h_ie : s_after_nl.inputEnd ≤ sc.inputEnd :=
      scanBlockScalar_afterNewline_inputEnd hcn
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
    -- Step 6: dispatch on '|' vs '>' to construct literal or folded
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
      -- Body grammar via scanBlockScalarBody_literal_prod (gives SLLiteralContent)
      have h_is_lit : (sc.peek? == some '|') = true := by rw [hlit]; decide
      rw [h_is_lit] at hok
      obtain ⟨sp_body, contentIndent, h_literal_content, hcorr_body, h_absorb⟩ :=
        scanBlockScalarBody_literal_prod sc s_after_nl sp_nl _ _ _ hcorr_nl h_ie hok
      have h_literal_content' : SLLiteralContent (0 + contentIndent) sp_nl sp_body := by
        rw [Nat.zero_add]; exact h_literal_content
      refine ⟨sp_body,
             Or.inl (SCLLiteral.mk 0 contentIndent rest sc.col sp_nl sp_body h_header
               h_literal_content'),
             hcorr_body, ?_⟩
      intro sp_mid W
      exact Or.inl (SCLLiteral.mk 0 contentIndent rest sc.col sp_nl sp_mid h_header
        (by rw [Nat.zero_add]; exact h_absorb sp_mid W))
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
      -- Body grammar via scanBlockScalarBody_folded_prod (gives SLLiteralContent)
      have h_is_fld : (sc.peek? == some '|') = false := by rw [hfold]; decide
      rw [h_is_fld] at hok
      obtain ⟨sp_body, contentIndent, h_literal_content, hcorr_body, h_absorb⟩ :=
        scanBlockScalarBody_folded_prod sc s_after_nl sp_nl _ _ _ hcorr_nl h_ie hok
      have h_literal_content' : SLLiteralContent (0 + contentIndent) sp_nl sp_body := by
        rw [Nat.zero_add]; exact h_literal_content
      refine ⟨sp_body,
             Or.inr (SCLFolded.mk 0 contentIndent rest sc.col sp_nl sp_body h_header
               h_literal_content'),
             hcorr_body, ?_⟩
      intro sp_mid W
      exact Or.inr (SCLFolded.mk 0 contentIndent rest sc.col sp_nl sp_mid h_header
        (by rw [Nat.zero_add]; exact h_absorb sp_mid W))

end L4YAML.Proofs.ScalarProduction

end Blanket
