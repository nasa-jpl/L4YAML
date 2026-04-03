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

-- SIndent split: SIndent (m + k) → ∃ sp_mid, SIndent m ∧ SIndent k.
-- Building block for making _prod theorems parametric in n.
theorem sindent_split {m k : Nat} {sp sp' : SurfPos}
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

-- SIndent with n_sk spaces → SFlowLinePrefix n for any n ≤ n_sk.
-- Decomposes spaces into SIndent n (indent) + remaining as GOpt SSeparateInLine.
theorem sindent_to_flowlineprefix {n n_sk : Nat} {sp sp' : SurfPos}
    (h : SIndent n_sk sp sp') (hle : n ≤ n_sk) :
    SFlowLinePrefix n sp sp' := by
  have h_eq : n_sk = n + (n_sk - n) := by omega
  rw [h_eq] at h
  obtain ⟨sp_mid, h_indent_n, h_indent_rest⟩ := sindent_split h
  have h_gstar := sindent_to_gstar_sswhite h_indent_rest
  have h_gopt := gstar_sswhite_to_gopt_sep h_gstar
  exact SFlowLinePrefix.mk n sp sp_mid sp' h_indent_n h_gopt

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

-- Parametric version: produces `GStar (SLEmpty n .flowIn)` for any `n`.
-- When spaces ≥ n: uses `SLEmpty.flow` via `sindent_to_flowlineprefix`.
-- When spaces < n: uses `SLEmpty.flowLt` via `SIndentLt`.
theorem foldQuotedNewlinesLoop_prod (n : Nat) (sc : ScannerState) (sp : SurfPos)
    (cnt fuel : Nat) (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', GStar (SLEmpty n .flowIn) sp sp' ∧
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
        have h_lempty : SLEmpty n .flowIn sp sp_cn := by
          by_cases h : n ≤ n_sk
          · -- Enough spaces: SFlowLinePrefix n via sindent_to_flowlineprefix
            exact SLEmpty.flow n sp sp_sk sp_cn .flowIn (Or.inr rfl)
              (GOpt.some sp sp_sk (sindent_to_flowlineprefix h_indent h)) h_sbreak
          · -- Fewer than n spaces: SIndentLt n
            have h_lt : n_sk < n := by omega
            exact SLEmpty.flowLt n sp sp_sk sp_cn .flowIn (Or.inr rfl)
              ⟨n_sk, h_lt, h_indent⟩ h_sbreak
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
-- Uses n=0 (universally satisfiable): the grammar n+1→n fix means flowInBlock 0
-- needs SFlowNode 0 directly, so no parametric indent lifting is needed.
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
    foldQuotedNewlinesLoop_prod 0 (consumeNewline sc) sp_cn 0 _ hcorr_cn
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

-- `parseBlockHeaderLoop` preserves or sets `explicitOffset` to `some d` with `d ≥ 1`.
-- Starting with `none`, any digit sets d = c.toNat - '0'.toNat ≥ 1.
-- Starting with `some d` where `d ≥ 1`, the value is preserved or overwritten with ≥ 1.
theorem parseBlockHeaderLoop_offset_preserves (sc : ScannerState) (chomp : ChompStyle)
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

-- Bridge: `canStartPlainScalarBool` → `SNsPlainFirst .blockIn`.
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
theorem canStartPlainScalar_to_SNsPlainFirst (c : Char) (rest : List Char)
    (col : Nat) (next : Option Char)
    (hstart : canStartPlainScalarBool c next false = true)
    (hrest_head : ∀ n, next = some n → ∃ rest', rest = n :: rest') :
    SNsPlainFirst .blockIn ⟨c :: rest, col⟩ ⟨rest, col + 1⟩ := by
  have hprop := (canStartPlainScalar_iff c next false).mp hstart
  unfold canStartPlainScalarProp at hprop
  split at hprop
  · -- Exception char: c ∈ {'-', '?', ':'}
    rename_i hexc
    match next with
    | none => exact absurd hprop id
    | some n =>
      obtain ⟨rest', hrst⟩ := hrest_head n rfl
      subst hrst
      obtain ⟨h_nws, h_nlb, _⟩ := hprop
      have h_safe : isNsPlainSafe .blockIn n := by
        unfold isNsPlainSafe
        exact ⟨fun hlb => h_nlb hlb, fun hws => h_nws hws⟩
      rcases hexc with rfl | rfl | rfl
      · exact SNsPlainFirst.dashSafe .blockIn n rest' col h_safe
      · exact SNsPlainFirst.questionSafe .blockIn n rest' col h_safe
      · exact SNsPlainFirst.colonSafe .blockIn n rest' col h_safe
  · -- Non-exception: non-indicator, non-whitespace, non-linebreak
    obtain ⟨h_ni, h_nws, h_nlb⟩ := hprop
    have h_safe : isNsPlainSafe .blockIn c := by
      unfold isNsPlainSafe
      exact ⟨fun hlb => h_nlb hlb, fun hws => h_nws hws⟩
    exact SNsPlainFirst.nonIndicator .blockIn c rest col h_safe h_ni

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
-- `#` hashAfterNs, multi-line (`handleBlockLineBreak_prod`).

-- Bridge: terminates?=none at ':' → next char exists and is not blank.
theorem colon_not_terminated_next (sc : ScannerState) (content spaces : String)
    (h : collectPlainScalar_terminates? ':' sc content spaces false = none) :
    ∃ n, sc.peekAt? 1 = some n ∧ isBlankBool n = false := by
  simp [collectPlainScalar_terminates?] at h
  -- h : (match sc.peekAt? 1 with | some n => isBlankBool n | none => true) = false
  split at h
  · -- peekAt? 1 = some n
    rename_i n hn
    exact ⟨n, hn, h⟩
  · -- peekAt? 1 = none → true = false → contradiction
    exact absurd h (by decide)

-- Bridge: ¬isBlankBool → isNsChar (for colonSafe)
theorem not_blank_to_nsChar {c : Char} (h : isBlankBool c = false) : isNsChar c := by
  simp [isNsChar, isLineBreakProp, isWhiteSpaceProp, isBlankBool, isWhiteSpaceBool,
    isLineBreakBool, beq_iff_eq, Bool.or_eq_false_iff] at *
  -- h : (¬c = ' ' ∧ ¬c = '\t') ∧ ¬c = '\n' ∧ ¬c = '\r'
  -- goal : (¬c = '\n' ∧ ¬c = '\r') ∧ ¬c = ' ' ∧ ¬c = '\t'
  exact ⟨h.2, h.1⟩

-- Helper: prepend a single whitespace char to inline continuation.
-- If no entries follow, it extends trailing WS.
-- If entries follow, it extends the first entry's GStar SSWhite prefix.
theorem prepend_white_to_continuation
    {sp sp_adv sp_end sp_trail : SurfPos}
    (hws : SSWhite sp sp_adv)
    (h_ent : GStar (SNbNsPlainInLineEntry .blockIn) sp_adv sp_end)
    (h_trail : GStar SSWhite sp_end sp_trail) :
    ∃ sp_end', GStar (SNbNsPlainInLineEntry .blockIn) sp sp_end' ∧
               GStar SSWhite sp_end' sp_trail := by
  cases h_ent with
  | nil =>
    -- No entries: WS becomes trailing
    exact ⟨sp, GStar.nil _, GStar.cons _ _ _ hws h_trail⟩
  | cons _ _ _ entry rest_entries =>
    -- Entries exist: extend first entry's WS prefix
    cases entry with
    | mk s₁_inner a₁ ws_pre char_body =>
      exact ⟨sp_end,
        GStar.cons _ _ _ (SNbNsPlainInLineEntry.mk _ _ _ _ (GStar.cons _ _ _ hws ws_pre) char_body)
          rest_entries,
        h_trail⟩

-- Helper: create a new inline entry from a safe char + prepend to continuation.
theorem prepend_char_to_continuation
    {sp sp_adv sp_end sp_trail : SurfPos}
    (hchar : SNsPlainChar .blockIn sp sp_adv)
    (h_ent : GStar (SNbNsPlainInLineEntry .blockIn) sp_adv sp_end)
    (h_trail : GStar SSWhite sp_end sp_trail) :
    ∃ sp_end', GStar (SNbNsPlainInLineEntry .blockIn) sp sp_end' ∧
               GStar SSWhite sp_end' sp_trail :=
  ⟨sp_end,
   GStar.cons _ _ _ (SNbNsPlainInLineEntry.mk .blockIn sp _ _ (GStar.nil _) hchar) h_ent,
   h_trail⟩

-- Full production for `collectPlainScalarLoop`: given accumulated whitespace
-- `GStar SSWhite sp_ent sp`, produces inline entries and trailing WS.
-- Single-line only: line-break branches are sorry.
-- The `#` at col=0 case (unreachable from `scanPlainScalar` since `#` is an
-- indicator excluded by `canStartPlainScalarBool`, and after any content char
-- col ≥ 1) is sorry'd as well.
theorem collectPlainScalarLoop_prod (sc : ScannerState) (sp : SurfPos)
    (content spaces : String) (fuel : Nat)
    (contentIndent inputEnd : Nat)
    (sp_ent : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (h_ws : GStar SSWhite sp_ent sp)
    {result : PlainScalarResult}
    (hok : collectPlainScalarLoop sc content spaces fuel false contentIndent inputEnd
           = .ok result) :
    ∃ sp_entries sp',
      GStar (SNbNsPlainInLineEntry .blockIn) sp_ent sp_entries ∧
      GStar SSWhite sp_entries sp' ∧
      ScannerSurfCorr result.state sp' := by
  induction fuel generalizing sc sp content spaces sp_ent with
  | zero =>
    simp [collectPlainScalarLoop] at hok; subst hok
    exact ⟨sp_ent, sp, GStar.nil _, h_ws, hcorr⟩
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at hok
    split at hok
    · -- peek? = none (EOF)
      have h := Except.ok.inj hok; subst h
      exact ⟨sp_ent, sp, GStar.nil _, h_ws, hcorr⟩
    · -- peek? = some c
      rename_i c hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      have hmore := peek_some_has_more hpeek
      subst hsp_eq
      split at hok
      · -- terminates? = some
        rename_i r_term h_term
        have h := Except.ok.inj hok; subst h
        rw [terminates_state_eq c sc content spaces false r_term h_term]
        exact ⟨sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, h_ws, hcorr⟩
      · -- terminates? = none
        rename_i h_term_none
        split at hok
        · sorry -- line break: multi-line deferred
        · -- not line break
          split at hok
          · -- whitespace: extend accumulated WS and recurse
            have hws_char : isWhiteSpaceBool c = true := by assumption
            have hnl := isWhiteSpace_not_newline c hws_char
            have hcr := isWhiteSpace_not_cr c hws_char
            have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
            have hw : SSWhite ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ := by
              simp [isWhiteSpaceBool, Bool.or_eq_true, beq_iff_eq] at hws_char
              rcases hws_char with rfl | rfl
              · exact SSWhite.space rest sc.col
              · exact SSWhite.tab rest sc.col
            exact ih sc.advance ⟨rest, sc.col + 1⟩ content (spaces.push c) sp_ent
              hcorr_adv (gstar_sswhite_append h_ws (GStar.cons _ _ _ hw (GStar.nil _)))
              hok
          · -- not whitespace
            split at hok
            · -- not plain safe: terminate
              have h := Except.ok.inj hok; subst h
              exact ⟨sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _, h_ws, hcorr⟩
            · -- content char: form grammar entry and recurse
              have h_safe : isPlainSafeBool c false = true := by
                cases hb : isPlainSafeBool c false <;> simp_all
              have hnl := (isPlainSafe_not_newline h_safe).1
              have hcr := (isPlainSafe_not_newline h_safe).2
              have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
              -- Construct SNsPlainChar for the content character
              have hchar : SNsPlainChar .blockIn ⟨c :: rest, sc.col⟩
                  ⟨rest, sc.col + 1⟩ := by
                by_cases hcolon : c = ':'
                · -- ':' followed by ns-plain-safe (colonSafe)
                  subst hcolon
                  obtain ⟨n, hpn, hnb⟩ :=
                    colon_not_terminated_next sc content spaces h_term_none
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
                  exact SNsPlainChar.colonSafe .blockIn '_' n rest' sc.col
                    (not_blank_to_nsChar hnb)
                · by_cases hhash : c = '#'
                  · -- '#' at col=0: unreachable (# is indicator, excluded by
                    -- canStartPlainScalarBool; after any content char col ≥ 1)
                    subst hhash
                    exact if h : sc.col > 0
                      then SNsPlainChar.hashAfterNs .blockIn rest sc.col h
                      else sorry
                  · -- safe: not ':' and not '#'
                    exact SNsPlainChar.safe .blockIn c rest sc.col
                      (isPlainSafe_to_nsPlainSafe_blockIn h_safe) hcolon hhash
              -- Recursive call with empty WS accumulator
              obtain ⟨sp_entries, sp', h_ent_rest, h_ws_rest, hcorr_rest⟩ :=
                ih sc.advance ⟨rest, sc.col + 1⟩ _ "" ⟨rest, sc.col + 1⟩
                  hcorr_adv (GStar.nil _) hok
              exact ⟨sp_entries, sp',
                GStar.cons sp_ent ⟨rest, sc.col + 1⟩ sp_entries
                  (SNbNsPlainInLineEntry.mk .blockIn sp_ent ⟨c :: rest, sc.col⟩
                    ⟨rest, sc.col + 1⟩ h_ws hchar)
                  h_ent_rest,
                h_ws_rest, hcorr_rest⟩

-- Helper: canStartPlainScalar → first char is not whitespace.
theorem canStartPlainScalar_not_ws {c : Char} {next : Option Char}
    (h : canStartPlainScalarBool c next false = true) : isWhiteSpaceBool c = false := by
  unfold canStartPlainScalarBool at h
  split at h
  · rename_i hexc; rcases hexc with rfl | rfl | rfl <;> native_decide
  · revert h; cases isWhiteSpaceBool c <;> simp

-- Helper: GStar SSWhite starting at a non-WS char must be nil.
theorem gstar_sswhite_at_non_ws {c : Char} {rest : List Char} {col : Nat} {s₁ : SurfPos}
    (h : GStar SSWhite ⟨c :: rest, col⟩ s₁)
    (h_nws : isWhiteSpaceBool c = false) :
    s₁ = ⟨c :: rest, col⟩ := by
  cases h
  · rfl
  · rename_i sp_mid hw _; exfalso; cases hw <;> simp [isWhiteSpaceBool] at h_nws

-- Helper: SNsPlainChar at ⟨c :: rest, col⟩ always produces ⟨rest, col + 1⟩.
theorem SNsPlainChar_at_head {c : Char} {rest : List Char} {col : Nat} {sp' : SurfPos}
    (h : SNsPlainChar .blockIn ⟨c :: rest, col⟩ sp') :
    sp' = ⟨rest, col + 1⟩ := by
  cases h <;> rfl

-- Context lift: SNsPlainChar .blockIn → .flowOut (definitional: isNsPlainSafe
-- .blockIn = isNsPlainSafe .flowOut = isNsChar for non-flow contexts).
theorem SNsPlainChar_blockIn_to_flowOut {sp sp' : SurfPos}
    (h : SNsPlainChar .blockIn sp sp') : SNsPlainChar .flowOut sp sp' := by
  cases h with
  | safe ch rest col hS hNC hNH =>
    exact SNsPlainChar.safe .flowOut ch rest col hS hNC hNH
  | colonSafe prev next rest col hS =>
    exact SNsPlainChar.colonSafe .flowOut prev next rest col hS
  | hashAfterNs rest col hC => exact SNsPlainChar.hashAfterNs .flowOut rest col hC

-- Context lift: SNbNsPlainInLineEntry .blockIn → .flowOut.
theorem SNbNsPlainInLineEntry_blockIn_to_flowOut {sp sp' : SurfPos}
    (h : SNbNsPlainInLineEntry .blockIn sp sp') : SNbNsPlainInLineEntry .flowOut sp sp' :=
  match h with
  | SNbNsPlainInLineEntry.mk _ _ s₁ _ ws_pre char =>
    SNbNsPlainInLineEntry.mk .flowOut _ s₁ _ ws_pre (SNsPlainChar_blockIn_to_flowOut char)

-- Context lift: GStar (SNbNsPlainInLineEntry .blockIn) → GStar (...flowOut).
theorem GStar_entries_blockIn_to_flowOut {sp sp' : SurfPos}
    (h : GStar (SNbNsPlainInLineEntry .blockIn) sp sp') :
    GStar (SNbNsPlainInLineEntry .flowOut) sp sp' := by
  induction h with
  | nil => exact GStar.nil _
  | cons s₁ s₂ s₃ entry _ ih =>
    exact GStar.cons s₁ s₂ s₃ (SNbNsPlainInLineEntry_blockIn_to_flowOut entry) ih

-- Context lift: SNsPlainFirst .blockIn → .flowOut (avoids circular import
-- with NodeProduction.lean which has the same theorem).
private theorem SNsPlainFirst_blockIn_to_flowOut' {s s' : SurfPos}
    (h : SNsPlainFirst .blockIn s s') : SNsPlainFirst .flowOut s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hNotInd =>
    exact SNsPlainFirst.nonIndicator .flowOut ch rest col hSafe hNotInd
  | dashSafe next rest col hSafe => exact SNsPlainFirst.dashSafe .flowOut next rest col hSafe
  | colonSafe next rest col hSafe => exact SNsPlainFirst.colonSafe .flowOut next rest col hSafe
  | questionSafe next rest col hSafe =>
    exact SNsPlainFirst.questionSafe .flowOut next rest col hSafe

-- Full production: scanPlainScalar → SFlowNode 0 .flowOut + trailing WS + corr.
-- Composes: canStartPlainScalar → SNsPlainFirst, loop → entries + trailing WS,
-- entry decomposition → SNsPlainOneLine, context lift → SFlowNode .flowOut.
-- Sorry'd: terminates? on first char (doc boundary edge), multi-line (line breaks),
-- # at col=0 (unreachable from callers).
theorem scanPlainScalar_to_flowNode (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) false = true)
    (h_block : sc.inFlow = false)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp_gram sp', SFlowNode 0 .flowOut sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
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
  have h_first : SNsPlainFirst .blockIn ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
    canStartPlainScalar_to_SNsPlainFirst c rest sc.col (sc.peekAt? 1) hstart hrest_head
  -- Unfold scanPlainScalar to extract loop
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i result hloop
    simp only [Except.ok.injEq] at hok; subst hok
    -- Normalize inFlow in hloop
    rw [h_block] at hloop
    -- Loop production: entries + trailing WS + corr
    obtain ⟨sp_entries, sp', h_entries, h_trail, hcorr_result⟩ :=
      collectPlainScalarLoop_prod sc ⟨c :: rest, sc.col⟩ "" "" _ _ _
        ⟨c :: rest, sc.col⟩ hcorr (GStar.nil _) hloop
    -- Analyze entries
    match h_entries with
    | GStar.nil _ =>
      -- No entries consumed (doc boundary edge case)
      sorry
    | GStar.cons _ sp_mid _ first_entry rest_entries =>
      -- Decompose first entry to recover sp_mid = ⟨rest, sc.col + 1⟩
      have h_nws := canStartPlainScalar_not_ws hstart
      match first_entry with
      | SNbNsPlainInLineEntry.mk _ _ ws_end _ ws_pre char =>
        have h_s1 := gstar_sswhite_at_non_ws ws_pre h_nws
        subst h_s1
        have h_mid := SNsPlainChar_at_head char
        subst h_mid
        -- Build: SNsPlainFirst + rest entries → SNsPlain 0 .flowOut → SFlowNode
        have h_plain : SNsPlain 0 .flowOut ⟨c :: rest, sc.col⟩ sp_entries :=
          SNsPlainMultiLine.mk 0 .flowOut _ _ sp_entries
            (SNsPlainOneLine.mk .flowOut _ ⟨rest, sc.col + 1⟩ sp_entries
              (SNsPlainFirst_blockIn_to_flowOut' h_first)
              (GStar_entries_blockIn_to_flowOut rest_entries))
            (GStar.nil _)
        exact ⟨sp_entries, sp',
          SFlowNode.content 0 .flowOut _ sp_entries
            (SFlowContent.plain 0 .flowOut _ sp_entries h_plain),
          h_trail,
          corr_of_simpleKeyAllowed_update false (corr_of_emitAt _ _ hcorr_result)⟩

theorem scanPlainScalar_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) false = true)
    (hok : scanPlainScalar sc = .ok s') :
    ∃ sp_gram sp', SNsPlain 0 .blockIn sp sp_gram ∧
                   ScannerSurfCorr s' sp' := by
  -- Extract surface position structure from peek
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  -- Bridge: peekAt? 1 connects to rest list structure
  have hrest_head : ∀ n, sc.peekAt? 1 = some n → ∃ rest', rest = n :: rest' := by
    intro n hn
    unfold ScannerState.peekAt? at hn
    have hcorr' := hsp_eq ▸ hcorr
    obtain ⟨pre, rest', hcs, hlen⟩ :=
      peekAtLoop_some_chars hcorr'.end_eq hn (c :: rest) hcorr'.chars_from
    have hp : ∃ a, pre = [a] := by
      cases pre with
      | nil => simp at hlen
      | cons a as =>
        cases as with
        | nil => exact ⟨a, rfl⟩
        | cons => simp at hlen
    obtain ⟨a, rfl⟩ := hp
    simp at hcs; obtain ⟨_, rfl⟩ := hcs
    exact ⟨rest', rfl⟩
  -- Get SNsPlainFirst for the first character
  rw [hsp_eq]
  have h_first : SNsPlainFirst .blockIn ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
    canStartPlainScalar_to_SNsPlainFirst c rest sc.col (sc.peekAt? 1) hstart hrest_head
  -- Grammar: wrap first char in SNsPlainOneLine → SNsPlainMultiLine = SNsPlain 0 .blockIn
  -- This is a valid (minimal) derivation covering at least the first character.
  have h_gram : SNsPlainMultiLine 0 .blockIn ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
    SNsPlainMultiLine.mk 0 .blockIn _ _ _
      (SNsPlainOneLine.mk .blockIn _ _ _ h_first (GStar.nil _))
      (GStar.nil _)
  -- Scanner correspondence from scanPlainScalar_corr (sorry-free)
  obtain ⟨sp', hcorr'⟩ := scanPlainScalar_corr sc sp hcorr hok
  exact ⟨⟨rest, sc.col + 1⟩, sp', h_gram, hcorr'⟩

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
-- Proof that if the comment is successfully consumed,
-- the characters strictly form a GOpt SCNbCommentText derivation tree
-- and preserve scanner-surface correspondence.
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

-- `autoDetectBlockScalarIndentLoop` returns indent ≥ minContentIndent when no error.
theorem autoDetectBlockScalarIndentLoop_ge_min
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
theorem autoDetectBlockScalarIndent_ge_min
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

-- `scanBlockScalarBody` on success implies the content indent is ≥ 1
-- when the parent indent is ≥ 0 and any explicit offset is ≥ 1.
theorem scanBlockScalarBody_indent_ge_one
    (sc_orig sc_after_nl : ScannerState)
    (chomp : ChompStyle) (explicitOffset : Option Nat)
    (isLiteral : Bool) (startPos : YamlPos) {s' : ScannerState}
    (hIndent : sc_orig.currentIndent ≥ 0)
    (hOff : ∀ d, explicitOffset = some d → d ≥ 1)
    (hok : scanBlockScalarBody sc_orig sc_after_nl chomp explicitOffset isLiteral startPos
           = .ok s') :
    ∃ m, m ≥ 1 := by
  unfold scanBlockScalarBody at hok
  dsimp only [] at hok
  cases hoff_eq : explicitOffset with
  | some d =>
    rw [hoff_eq] at hok
    -- autoDetectErr? = none, so the match reduces directly
    -- contentIndent = (max 0 (parentIndent + d)).toNat
    exact ⟨(max 0 (sc_orig.currentIndent + (↑d : Int))).toNat, by
      have := hOff d hoff_eq; omega⟩
  | none =>
    rw [hoff_eq] at hok
    -- (contentIndent, autoDetectErr?) = autoDetectBlockScalarIndent ...
    generalize h_auto : autoDetectBlockScalarIndent sc_after_nl
      (max 0 (sc_orig.currentIndent + 1)).toNat sc_orig.inputEnd = auto_res at hok
    obtain ⟨ci, err⟩ := auto_res
    simp only [] at h_auto hok
    cases h_err : err with
    | some e =>
      simp only [h_err] at hok
      cases hok  -- Except.error ≠ Except.ok
    | none =>
      simp only [h_err] at hok
      exact ⟨ci, by
        have h_min : (max 0 (sc_orig.currentIndent + 1)).toNat ≥ 1 := by omega
        have h_ge := autoDetectBlockScalarIndent_ge_min sc_after_nl
          (max 0 (sc_orig.currentIndent + 1)).toNat sc_orig.inputEnd
        rw [h_auto] at h_ge; simp only [] at h_ge
        exact Nat.le_trans h_min (h_ge h_err)⟩

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

/-! ### SLLiteralContent composition helpers

  Helpers for building `SLLiteralContent` incrementally from loop iterations. -/

-- Empty literal content: no text, no break, no trailing.
theorem empty_literal_content {n : Nat} (sp : SurfPos) :
    SLLiteralContent n sp sp :=
  SLLiteralContent.mk n sp sp sp sp sp
    (GOpt.none sp) (GOpt.none sp) (GStar.nil sp) (GOpt.none sp)

-- Trailing indent only: `SIndentLe n` at EOF.
theorem indent_only_literal_content {n : Nat} {sp sp' : SurfPos}
    (h : SIndentLe n sp sp') : SLLiteralContent n sp sp' :=
  SLLiteralContent.mk n sp sp sp sp sp'
    (GOpt.none sp) (GOpt.none sp) (GStar.nil sp) (GOpt.some sp sp' h)

-- Prepend an `SLEmpty n .blockIn` to `SLLiteralContent n`.
-- The empty line either joins the first text line's prefix or the trailing empties.
theorem prepend_empty_to_literal_content {n : Nat}
    {sp sp₁ sp' : SurfPos}
    (h_empty : SLEmpty n .blockIn sp sp₁)
    (h_tail : SLLiteralContent n sp₁ sp') :
    SLLiteralContent n sp sp' := by
  match h_tail with
  | .mk _ _ sp_t1 sp_t2 sp_t3 _ h_opt_text h_opt_break h_trail_empties h_trail_indent =>
    match h_opt_text with
    | .some _ _ (GSeq.mk _ sp_first_end _ h_first_text h_conts) =>
      -- Has text: prepend empty to first text line's prefix
      exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp'
        (GOpt.some sp sp_t1 (GSeq.mk sp sp_first_end sp_t1
          (prepend_empty_to_text_line h_empty h_first_text) h_conts))
        h_opt_break h_trail_empties h_trail_indent
    | .none _ =>
      -- No text: add our empty to trailing empties, handling tail's break
      match h_opt_break with
      | .none _ =>
        -- sp_t1 = sp₁, sp_t2 = sp₁: chain directly
        exact SLLiteralContent.mk n sp sp sp sp_t3 sp'
          (GOpt.none sp) (GOpt.none sp)
          (GStar.cons sp sp₁ sp_t3 h_empty h_trail_empties)
          h_trail_indent
      | .some _ _ h_brk =>
        -- sp_t1 = sp₁: convert tail's break to SLEmpty, chain
        let brk_empty : SLEmpty n .blockIn sp₁ sp_t2 :=
          SLEmpty.block n sp₁ sp₁ sp_t2 .blockIn (Or.inr rfl) (GOpt.none sp₁) h_brk
        exact SLLiteralContent.mk n sp sp sp sp_t3 sp'
          (GOpt.none sp) (GOpt.none sp)
          (GStar.cons sp sp₁ sp_t3 h_empty
            (GStar.cons sp₁ sp_t2 sp_t3 brk_empty h_trail_empties))
          h_trail_indent

-- Single content line without trailing break → `SLLiteralContent`.
theorem content_only_to_literal {n : Nat}
    {sp sp' : SurfPos}
    (h_text : SLNbLiteralText n sp sp') :
    SLLiteralContent n sp sp' :=
  SLLiteralContent.mk n sp sp' sp' sp' sp'
    (GOpt.some sp sp' (GSeq.mk sp sp' sp' h_text (GStar.nil sp')))
    (GOpt.none sp') (GStar.nil sp') (GOpt.none sp')

-- Content line + trailing break + body tail → `SLLiteralContent`.
-- The break + tail's text lines become `SBNbLiteralNext` continuations.
theorem content_break_tail_to_literal {n : Nat}
    {sp sp₁ sp₂ sp' : SurfPos}
    (h_text : SLNbLiteralText n sp sp₁)
    (h_break : SBBreak sp₁ sp₂)
    (h_tail : SLLiteralContent n sp₂ sp') :
    SLLiteralContent n sp sp' := by
  match h_tail with
  | .mk _ _ sp_t1 sp_t2 sp_t3 _ h_opt_text h_opt_break h_trail_empties h_trail_indent =>
    match h_opt_text with
    | .some _ _ (GSeq.mk _ sp_tail_first_end _ h_tail_first h_tail_conts) =>
      -- Tail has text: break + tail_first = SBNbLiteralNext, prepend to continuations
      let new_next : SBNbLiteralNext n sp₁ sp_tail_first_end :=
        SBNbLiteralNext.mk n sp₁ sp₂ sp_tail_first_end h_break h_tail_first
      let new_conts := GStar.cons sp₁ sp_tail_first_end sp_t1 new_next h_tail_conts
      exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp'
        (GOpt.some sp sp_t1 (GSeq.mk sp sp₁ sp_t1 h_text new_conts))
        h_opt_break h_trail_empties h_trail_indent
    | .none _ =>
      -- Tail has no text: our break is the trailing break.
      -- The tail's break (if any) becomes an SLEmpty (break = indent(0) + break).
      match h_opt_break with
      | .none _ =>
        -- No tail break: straightforward
        exact SLLiteralContent.mk n sp sp₁ sp₂ sp_t3 sp'
          (GOpt.some sp sp₁ (GSeq.mk sp sp₁ sp₁ h_text (GStar.nil sp₁)))
          (GOpt.some sp₁ sp₂ h_break)
          h_trail_empties h_trail_indent
      | .some _ _ h_tail_break =>
        -- Tail has a break too: convert it to an SLEmpty and prepend to empties
        let new_empty : SLEmpty n .blockIn sp₂ sp_t2 :=
          SLEmpty.block n sp₂ sp₂ sp_t2 .blockIn (Or.inr rfl) (GOpt.none sp₂) h_tail_break
        exact SLLiteralContent.mk n sp sp₁ sp₂ sp_t3 sp'
          (GOpt.some sp sp₁ (GSeq.mk sp sp₁ sp₁ h_text (GStar.nil sp₁)))
          (GOpt.some sp₁ sp₂ h_break)
          (GStar.cons sp₂ sp_t2 sp_t3 new_empty h_trail_empties)
          h_trail_indent

-- Content line + trailing break + trailing indent → `SLLiteralContent`.
theorem content_break_indent_to_literal {n : Nat}
    {sp sp₁ sp₂ sp' : SurfPos}
    (h_text : SLNbLiteralText n sp sp₁)
    (h_break : SBBreak sp₁ sp₂)
    (h_indent : GOpt (SIndentLe n) sp₂ sp') :
    SLLiteralContent n sp sp' :=
  SLLiteralContent.mk n sp sp₁ sp₂ sp₂ sp'
    (GOpt.some sp sp₁ (GSeq.mk sp sp₁ sp₁ h_text (GStar.nil sp₁)))
    (GOpt.some sp₁ sp₂ h_break) (GStar.nil sp₂) h_indent

-- Prefix a text line to `SLLiteralContent` when no break separates them.
-- (The "tail has text" sub-case is unreachable when contentIndent ≥ 1 and
-- collectLineContentLoop has sufficient fuel — it always ends at break/EOF.)

-- SIndent n converts to GStar SNbChar (each indent space is non-break).
theorem SIndent_gives_GStar_SNbChar {n : Nat} {sp sp' : SurfPos}
    (h : SIndent n sp sp') : GStar SNbChar sp sp' := by
  induction h with
  | zero => exact GStar.nil _
  | succ k rest col _ _ ih =>
    exact GStar.cons _ _ _ (not_isLineBreak_gives_SNbChar ' ' rest col (by decide)) ih

-- SIndentLe n converts to GStar SNbChar.
theorem SIndentLe_gives_GStar_SNbChar {n : Nat} {sp sp' : SurfPos}
    (h : SIndentLe n sp sp') : GStar SNbChar sp sp' := by
  obtain ⟨_, _, h_indent⟩ := h
  exact SIndent_gives_GStar_SNbChar h_indent

-- Extend GPlus with additional GStar elements.
theorem GPlus_extend_GStar {P : SurfPos → SurfPos → Prop} {sp₁ sp₂ sp₃ : SurfPos}
    (h₁ : GPlus P sp₁ sp₂) (h₂ : GStar P sp₂ sp₃) : GPlus P sp₁ sp₃ :=
  match h₁ with
  | .mk _ sp_m _ h_first h_rest => GPlus.mk _ sp_m _ h_first (GStar_trans h_rest h₂)

-- Convert GPlus to GStar.
theorem GPlus_to_GStar {P : SurfPos → SurfPos → Prop} {sp₁ sp₂ : SurfPos}
    (h : GPlus P sp₁ sp₂) : GStar P sp₁ sp₂ :=
  match h with
  | .mk _ _ _ h_first h_rest => GStar.cons _ _ _ h_first h_rest

theorem prefix_text_literal_content {n : Nat}
    {sp sp₁ sp' : SurfPos}
    (h_text : SLNbLiteralText n sp sp₁)
    (h_tail : SLLiteralContent n sp₁ sp') :
    SLLiteralContent n sp sp' := by
  match h_tail with
  | .mk _ _ sp_t1 sp_t2 sp_t3 _ h_opt_text h_opt_break h_trail_empties h_trail_indent =>
    match h_opt_text with
    | .none _ =>
      exact SLLiteralContent.mk n sp sp₁ sp_t2 sp_t3 sp'
        (GOpt.some sp sp₁ (GSeq.mk sp sp₁ sp₁ h_text (GStar.nil sp₁)))
        h_opt_break h_trail_empties h_trail_indent
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
                  exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp'
                    (GOpt.some sp sp_t1
                      (GSeq.mk sp sp_m sp_t1
                        (SLNbLiteralText.mk n sp sp_e1 sp_m h_empties1
                          (GSeq.mk sp_e1 sp_i1 sp_m h_indent1
                            (GPlus_extend_GStar h_chars1
                              (GStar_trans (SIndent_gives_GStar_SNbChar h_indent2)
                                (GPlus_to_GStar h_chars2)))))
                        h_conts))
                    h_opt_break h_trail_empties h_trail_indent
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
                      exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp'
                        (GOpt.some sp sp_t1
                          (GSeq.mk sp sp₁ sp_t1 h_text
                            (GStar.cons sp₁ sp_m sp_t1 cont_line h_conts)))
                        h_opt_break h_trail_empties h_trail_indent
                    | GOpt.some _ _ h_ile =>
                      -- Absorb indent-le spaces into GPlus, extend text to sp_x
                      exact SLLiteralContent.mk n sp sp_t1 sp_t2 sp_t3 sp'
                        (GOpt.some sp sp_t1
                          (GSeq.mk sp sp_x sp_t1
                            (SLNbLiteralText.mk n sp sp_e1 sp_x h_empties1
                              (GSeq.mk sp_e1 sp_i1 sp_x h_indent1
                                (GPlus_extend_GStar h_chars1
                                  (SIndentLe_gives_GStar_SNbChar h_ile))))
                            (GStar.cons sp_x sp_m sp_t1 cont_line h_conts)))
                        h_opt_break h_trail_empties h_trail_indent
                  | .flow _ _ _ _ _ hc _ _ =>
                    exact absurd hc (by obtain h | h := hc <;> cases h)
                  | .flowLt _ _ _ _ _ hc _ _ =>
                    exact absurd hc (by obtain h | h := hc <;> cases h)

/-! ### §8b-main collectBlockScalarLoop literal production

  The main loop theorem: `collectBlockScalarLoop` produces `SLLiteralContent n`.
  By induction on fuel, each iteration either:
  - stops (empty content / trailing indent),
  - processes an empty line (prepend to tail),
  - processes a content line + break (content_break_tail_to_literal),
  - processes a content line without break (content_only or prefix_text). -/

-- `collectBlockScalarLoop` produces `SLLiteralContent n` and preserves correspondence.
theorem collectBlockScalarLoop_literal_prod
    (sc : ScannerState) (sp : SurfPos)
    (rawContent : String) (fuel : Nat) (contentIndent inputEnd : Nat)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', SLLiteralContent contentIndent sp sp' ∧
           ScannerSurfCorr (collectBlockScalarLoop sc rawContent fuel contentIndent inputEnd).2 sp' := by
  induction fuel generalizing sc sp rawContent with
  | zero =>
    simp [collectBlockScalarLoop]
    exact ⟨sp, empty_literal_content sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    dsimp only []
    split
    · -- Document boundary: stop
      exact ⟨sp, empty_literal_content sp, hcorr⟩
    · -- Not document boundary
      -- Get correspondence and indent for consumeExactSpaces result
      obtain ⟨sp_spaces, h_sindent, hcorr_spaces⟩ :=
        consumeExactSpaces_sindent_partial sc sp contentIndent hcorr
      have hle : (consumeExactSpaces sc contentIndent).1 ≤ contentIndent :=
        consumeExactSpaces_fst_le sc contentIndent
      split
      · -- peek? = none after spaces: EOF → trailing indent
        exact ⟨sp_spaces,
               indent_only_literal_content ⟨_, hle, h_sindent⟩,
               hcorr_spaces⟩
      · rename_i c hpeek
        split
        · -- isLineBreakBool c = true: empty line
          rename_i hlb
          obtain ⟨sp_nl, h_break, hcorr_nl⟩ :=
            consumeNewline_sbreak_corr _ sp_spaces c hcorr_spaces hpeek hlb
          have h_empty : SLEmpty contentIndent .blockIn sp sp_nl :=
            SLEmpty.block contentIndent sp sp_spaces sp_nl .blockIn (Or.inr rfl)
              (GOpt.some sp sp_spaces ⟨_, hle, h_sindent⟩) h_break
          obtain ⟨sp_end, h_tail, hcorr_end⟩ := ih _ sp_nl _ hcorr_nl
          exact ⟨sp_end, prepend_empty_to_literal_content h_empty h_tail, hcorr_end⟩
        · split
          · -- under-indent: return original position
            exact ⟨sp, empty_literal_content sp, hcorr⟩
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
            -- GPlus SNbChar from content
            obtain ⟨sp_content, h_gplus, hcorr_content⟩ :=
              collectLineContentLoop_gplus_prod _ sp_spaces c ""
                (inputEnd - (consumeExactSpaces sc contentIndent).2.offset + 1)
                hcorr_spaces' hpeek hne_lb_bool (by omega)
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
                obtain ⟨sp_end, h_tail, hcorr_end⟩ := ih _ sp_nl' _ hcorr_nl'
                exact ⟨sp_end,
                       content_break_tail_to_literal h_text_line h_break' h_tail,
                       hcorr_end⟩
              · -- No break after content: recurse (fuel exhaustion edge case)
                obtain ⟨sp_end, h_tail, hcorr_end⟩ := ih _ sp_content _ hcorr_content
                exact ⟨sp_end,
                       prefix_text_literal_content h_text_line h_tail,
                       hcorr_end⟩
            · -- peek? = none after content: EOF
              exact ⟨sp_content, content_only_to_literal h_text_line, hcorr_content⟩

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
theorem headerChar_notWsLbBom (c : Char)
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
theorem skipWhitespace_eq_of_same_surfpos {sc : ScannerState} {sp : SurfPos}
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
theorem scanBlockScalarSkipComment_noop (sc : ScannerState)
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
theorem scNbCommentText_irrefl (sp : SurfPos) : ¬ SCNbCommentText sp sp := by
  intro h
  match h with
  | .mk rest col _ hstar =>
    have : col ≥ col + 1 := gstar_gchar_col_le hstar
    omega

-- Mathematical unreachability: `#` comment without preceding whitespace after block header.
theorem scanBlockScalar_unreachable_comment_without_ws
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
theorem scanBlockScalarBody_literal_prod (sc_orig sc_after_nl : ScannerState)
    (sp : SurfPos) (chomp : ChompStyle) (explicitOffset : Option Nat)
    (startPos : YamlPos) {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc_after_nl sp)
    (hIndent : sc_orig.currentIndent ≥ 0)
    (hOff : ∀ d, explicitOffset = some d → d ≥ 1)
    (hok : scanBlockScalarBody sc_orig sc_after_nl chomp explicitOffset true startPos = .ok s') :
    ∃ sp' contentIndent, contentIndent ≥ 1 ∧
      SLLiteralContent contentIndent sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanBlockScalarBody at hok
  dsimp only [] at hok
  cases hoff_eq : explicitOffset with
  | some d =>
    rw [hoff_eq] at hok
    -- autoDetectErr? = none, so the match on autoDetectErr? reduces to .ok path directly
    let contentIndent := (max 0 (sc_orig.currentIndent + (↑d : Int))).toNat
    let fuel := sc_orig.inputEnd - sc_after_nl.offset + 1
    obtain ⟨sp_loop, h_lit_content, hcorr_loop⟩ :=
      collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel contentIndent sc_orig.inputEnd hcorr
    have h := Except.ok.inj hok; subst h
    exact ⟨sp_loop, contentIndent, by have := hOff d hoff_eq; omega, h_lit_content,
           ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq, hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩⟩
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
      obtain ⟨sp_loop, h_lit_content, hcorr_loop⟩ :=
        collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel ci sc_orig.inputEnd hcorr
      have h := Except.ok.inj hok; subst h
      have h_min : (max 0 (sc_orig.currentIndent + 1)).toNat ≥ 1 := by omega
      have h_ge := autoDetectBlockScalarIndent_ge_min sc_after_nl
        (max 0 (sc_orig.currentIndent + 1)).toNat sc_orig.inputEnd
      rw [h_auto] at h_ge; simp only [] at h_ge
      exact ⟨sp_loop, ci, Nat.le_trans h_min (h_ge h_err), h_lit_content,
             ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq, hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩⟩

-- `scanBlockScalarBody` for folded also produces `SLLiteralContent` + correspondence.
-- The scanner uses the same `collectBlockScalarLoop` for both literal and folded;
-- the only difference is post-processing of the collected content string.
theorem scanBlockScalarBody_folded_prod (sc_orig sc_after_nl : ScannerState)
    (sp : SurfPos) (chomp : ChompStyle) (explicitOffset : Option Nat)
    (startPos : YamlPos) {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc_after_nl sp)
    (hIndent : sc_orig.currentIndent ≥ 0)
    (hOff : ∀ d, explicitOffset = some d → d ≥ 1)
    (hok : scanBlockScalarBody sc_orig sc_after_nl chomp explicitOffset false startPos = .ok s') :
    ∃ sp' contentIndent, contentIndent ≥ 1 ∧
      SLLiteralContent contentIndent sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanBlockScalarBody at hok
  dsimp only [] at hok
  cases hoff_eq : explicitOffset with
  | some d =>
    rw [hoff_eq] at hok
    let contentIndent := (max 0 (sc_orig.currentIndent + (↑d : Int))).toNat
    let fuel := sc_orig.inputEnd - sc_after_nl.offset + 1
    obtain ⟨sp_loop, h_lit_content, hcorr_loop⟩ :=
      collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel contentIndent sc_orig.inputEnd hcorr
    have h := Except.ok.inj hok; subst h
    exact ⟨sp_loop, contentIndent, by have := hOff d hoff_eq; omega, h_lit_content,
           ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq, hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩⟩
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
      obtain ⟨sp_loop, h_lit_content, hcorr_loop⟩ :=
        collectBlockScalarLoop_literal_prod sc_after_nl sp "" fuel ci sc_orig.inputEnd hcorr
      have h := Except.ok.inj hok; subst h
      have h_min : (max 0 (sc_orig.currentIndent + 1)).toNat ≥ 1 := by omega
      have h_ge := autoDetectBlockScalarIndent_ge_min sc_after_nl
        (max 0 (sc_orig.currentIndent + 1)).toNat sc_orig.inputEnd
      rw [h_auto] at h_ge; simp only [] at h_ge
      exact ⟨sp_loop, ci, Nat.le_trans h_min (h_ge h_err), h_lit_content,
             ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq, hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩⟩

-- `scanBlockScalar` produces `SCLLiteral 0` or `SCLFolded 0` and preserves correspondence.
-- Header: FULLY PROVEN (delimiter + header chars + SSBComment).
-- Body: FULLY PROVEN for both literal and folded via `collectBlockScalarLoop_literal_prod`.
-- m ≥ 1: FULLY PROVEN (autoDetect ≥ min ≥ 1, explicit offset ≥ 1).
-- Dispatch: FULLY PROVEN for literal (`|`) and folded (`>`).
theorem scanBlockScalar_prod (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hchar : sc.peek? = some '|' ∨ sc.peek? = some '>')
    (hIndent : sc.currentIndent ≥ 0)
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
    -- Step 6: offset preservation for body
    have hOff := parseBlockHeaderLoop_offset_preserves sc.advance .clip none 2
      (fun _ h => by cases h)
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
      -- Body grammar via scanBlockScalarBody_literal_prod (gives m ≥ 1 + SLLiteralContent)
      have h_is_lit : (sc.peek? == some '|') = true := by rw [hlit]; decide
      rw [h_is_lit] at hok
      obtain ⟨sp_body, contentIndent, h_ci_ge, h_literal_content, hcorr_body⟩ :=
        scanBlockScalarBody_literal_prod sc s_after_nl sp_nl _ _ _ hcorr_nl hIndent hOff hok
      have h_literal_content' : SLLiteralContent (0 + contentIndent) sp_nl sp_body := by
        rw [Nat.zero_add]; exact h_literal_content
      exact ⟨sp_body,
             Or.inl (SCLLiteral.mk 0 contentIndent rest sc.col sp_nl sp_body h_ci_ge h_header
               h_literal_content'),
             hcorr_body⟩
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
      -- Body grammar via scanBlockScalarBody_folded_prod (gives m ≥ 1 + SLLiteralContent)
      have h_is_fld : (sc.peek? == some '|') = false := by rw [hfold]; decide
      rw [h_is_fld] at hok
      obtain ⟨sp_body, contentIndent, h_ci_ge, h_literal_content, hcorr_body⟩ :=
        scanBlockScalarBody_folded_prod sc s_after_nl sp_nl _ _ _ hcorr_nl hIndent hOff hok
      have h_literal_content' : SLLiteralContent (0 + contentIndent) sp_nl sp_body := by
        rw [Nat.zero_add]; exact h_literal_content
      exact ⟨sp_body,
             Or.inr (SCLFolded.mk 0 contentIndent rest sc.col sp_nl sp_body h_ci_ge h_header
               h_literal_content'),
             hcorr_body⟩

end Lean4Yaml.Proofs.ScalarProduction
