/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.ScalarProduction

@[expose] public section Blanket

/-! # Acceptance (scanner converse) for quoted scalars

    The inverse of `scanDoubleQuoted_prod` / `scanSingleQuoted_prod`: a surface
    derivation at the scanner's position makes the scanner succeed and land at
    the derivation's end.  One-line (`SCDoubleQuotedOk`, `SCSingleQuotedOk`) and
    multi-line (`SCDoubleQuotedMultiOk n`, `SCSingleQuotedMultiOk n`) forms.

    The surface relations are STRICTLY wider than the scanner, so the converse
    holds only under narrowed character relations (`DQCharOk`, `SQCharOk`) and
    a trailing hypothesis.  Refuting inputs for the unnarrowed converse:
    * `"\x01"` / `'\x01'` — `[107]`/`[118]` admit any non-break char, the
      scanner refuses C0 controls (`invalidControlChar`, `[2] nb-json`).
    * `"\uD800"`, `"\UFFFFFFFF"` — `[60]`/`[61]` constrain digits only, the
      scanner refuses non-scalar values (`unicodeOutOfRange`).
    * `"a"b` in block context — `[109]` ends at the closing quote, the scanner
      refuses the trailing content (`trailingContent`, §7.3).
    * `''''` — `[120]` derives `''` with two quotes left, but the scanner reads
      the pair as `[117] c-quoted-quote`, lands after all four (`'''''` runs to
      `unterminatedScalar`); hence `hq` on the char after the closing quote.

    Multi-line (`[111]`/`[123]`, folded by `foldQuotedNewlines`):
    * `"a\n---\nb"` — `[69] s-flow-line-prefix` lands anywhere, the scanner refuses
      a document marker at column 0 (`documentMarkerInScalar`); hence `NotDocMarker`.
    * `"a\nb"` under a block collection at indent 0 — `[69]` with `n = 0` derives,
      the scanner needs the continuation to clear its indentation floor
      (`underIndentedScalar`); hence `(n : Int) > sc.currentIndent`.
    * `"a\n\tb"` at indent 1 — `[69]` reads the tab as `[66] s-separate-in-line`,
      the scanner refuses it (`tabInIndentation`); the floor hypothesis puts `n ≥ 1`
      spaces before any tab.
    * `"a\r\nb"` read by `[28] b-break` as a lone CR — the scanner takes CRLF as one
      break; hence `SBBreakOk`.
    * `"a\n  b"` with `[69]` stopping after one space — the scanner eats the whole
      white run; hence the maximal-landing hypotheses on the char after the prefix.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Acceptance

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Grammar

/-! ## §1 State bookkeeping the loop preserves -/

/-- Fields the collect loops never touch, read back at the token emission. -/
def Keeps (sc sc' : ScannerState) : Prop :=
  sc'.tokens = sc.tokens ∧ sc'.inputEnd = sc.inputEnd ∧ sc'.indents = sc.indents

lemma Keeps.refl (sc : ScannerState) : Keeps sc sc := ⟨rfl, rfl, rfl⟩

lemma Keeps.trans {a b c : ScannerState} (h₁ : Keeps a b) (h₂ : Keeps b c) : Keeps a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

lemma Keeps.currentIndent {a b : ScannerState} (h : Keeps a b) : b.currentIndent = a.currentIndent := by
  unfold ScannerState.currentIndent; rw [h.2.2]

lemma keeps_advance (sc : ScannerState) : Keeps sc sc.advance := by
  unfold Keeps ScannerState.advance
  by_cases h : sc.offset < sc.inputEnd
  · simp only [h, ite_true]
    split <;> (try split) <;> exact ⟨rfl, rfl, rfl⟩
  · simp only [h, ite_false, and_self]

/-! ## §2 Position facts read off `ScannerSurfCorr` -/

lemma peek_of_corr {sc : ScannerState} {c : Char} {rest : List Char} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩) :
    sc.peek? = some c ∧ sc.offset < sc.inputEnd := by
  have hmore : sc.offset < sc.inputEnd := by
    cases Nat.lt_or_ge sc.offset sc.inputEnd with
    | inl h => exact h
    | inr h =>
      have := eof_corr sc _ hcorr (Nat.not_lt.mpr h)
      simp at this
  obtain ⟨c', rest', hchars, hpeek⟩ := peek_corr sc _ hcorr hmore
  simp only [List.cons.injEq] at hchars
  obtain ⟨rfl, rfl⟩ := hchars
  exact ⟨hpeek, hmore⟩

lemma peek_none_of_corr {sc : ScannerState} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨[], col⟩) : sc.peek? = none := by
  cases h : sc.peek? with
  | none => rfl
  | some c =>
    obtain ⟨rest, hsp⟩ := peek_some_sp hcorr h
    simp at hsp

lemma length_le_listByteSize (l : List Char) : l.length ≤ listByteSize l := by
  induction l with
  | nil => simp [listByteSize]
  | cons c rest ih =>
    simp only [List.length_cons, listByteSize]
    have := Char.utf8Size_pos c
    omega

/-- The scanner's fuel `inputEnd - offset + 1` covers every remaining char. -/
lemma fuel_of_corr {sc : ScannerState} {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp) :
    sp.chars.length < sc.inputEnd - sc.offset + 1 := by
  obtain ⟨pre, hin, hpre⟩ := hcorr.input_prefix
  have hend := hcorr.end_eq
  rw [utf8ByteSize_eq_listByteSize, hin, listByteSize_append] at hend
  have := length_le_listByteSize sp.chars
  omega

/-- `advance_non_newline_corr` with the column read off the correspondence. -/
lemma advance_corr {sc : ScannerState} {c : Char} {rest : List Char} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩)
    (hnl : c ≠ '\n') (hcr : c ≠ '\r') :
    ScannerSurfCorr sc.advance ⟨rest, col + 1⟩ := by
  have hcol := hcorr.col_eq
  simp only at hcol
  subst hcol
  exact advance_non_newline_corr sc c rest hcorr (peek_of_corr hcorr).2 hnl hcr

/-! ## §3 Character facts -/

lemma isNbJson_ne_lf {c : Char} (hJ : isNbJsonProp c) : c ≠ '\n' := by
  intro h; subst h; exact absurd hJ (by decide)

lemma isNbJson_ne_cr {c : Char} (hJ : isNbJsonProp c) : c ≠ '\r' := by
  intro h; subst h; exact absurd hJ (by decide)

lemma isNbJson_not_lineBreak {c : Char} (hJ : isNbJsonProp c) : isLineBreakBool c = false := by
  cases h : isLineBreakBool c
  · rfl
  · exfalso
    rcases (isLineBreak_iff c).1 h with h' | h'
    · exact isNbJson_ne_lf hJ (by simpa [isLineFeedProp] using h')
    · exact isNbJson_ne_cr hJ (by simpa [isCarriageReturnProp] using h')

lemma hex_bool_of_isNsHexDigit {c : Char} (h : isNsHexDigit c) :
    (c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) = true := by
  unfold isNsHexDigit at h
  unfold Char.isDigit
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Or.inl ⟨h1, h2⟩)
  · exact Or.inl (Or.inr ⟨h1, h2⟩)
  · exact Or.inr ⟨h1, h2⟩

lemma isNsHexDigit_ne_lf {c : Char} (h : isNsHexDigit c) : c ≠ '\n' := by
  intro hc; subst hc; unfold isNsHexDigit at h; simp at h

lemma isNsHexDigit_ne_cr {c : Char} (h : isNsHexDigit c) : c ≠ '\r' := by
  intro hc; subst hc; unfold isNsHexDigit at h; simp at h

lemma namedEscape_ne_lf {c : Char} (h : isNamedEscapeChar c) : c ≠ '\n' := by
  intro hc; subst hc; exact h rfl

lemma namedEscape_ne_cr {c : Char} (h : isNamedEscapeChar c) : c ≠ '\r' := by
  intro hc; subst hc; exact h rfl

lemma namedEscape_not_lineBreak {c : Char} (h : isNamedEscapeChar c) : isLineBreakBool c = false := by
  cases hb : isLineBreakBool c
  · rfl
  · exfalso
    rcases (isLineBreak_iff c).1 hb with h' | h'
    · exact namedEscape_ne_lf h (by simpa [isLineFeedProp] using h')
    · exact namedEscape_ne_cr h (by simpa [isCarriageReturnProp] using h')

/-! ## §4 Hex escapes -/

/-- Digit value as `parseHexEscape` computes it. -/
def hexDigitVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if c >= 'a' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- Value of a digit run, most significant first (`[59]`–`[61]`). -/
def hexVal (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 16 + hexDigitVal c) 0

lemma collectHexDigitsLoop_accepts (ds : List Char) :
    ∀ (sc : ScannerState) (hex : String) (rest : List Char) (col : Nat),
      (∀ c, c ∈ ds → isNsHexDigit c) →
      ScannerSurfCorr sc ⟨ds ++ rest, col⟩ →
      (collectHexDigitsLoop sc hex ds.length).1.toList = hex.toList ++ ds ∧
      ScannerSurfCorr (collectHexDigitsLoop sc hex ds.length).2 ⟨rest, col + ds.length⟩ ∧
      Keeps sc (collectHexDigitsLoop sc hex ds.length).2 := by
  induction ds with
  | nil =>
    intro sc hex rest col _ hcorr
    simp only [List.length_nil, collectHexDigitsLoop, List.append_nil, Nat.add_zero]
    exact ⟨trivial, hcorr, Keeps.refl sc⟩
  | cons d ds ih =>
    intro sc hex rest col hhex hcorr
    have hd := hhex d (List.mem_cons_self ..)
    have hds : ∀ c, c ∈ ds → isNsHexDigit c := fun c hc => hhex c (List.mem_cons_of_mem d hc)
    simp only [List.cons_append] at hcorr
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (isNsHexDigit_ne_lf hd) (isNsHexDigit_ne_cr hd)
    obtain ⟨h1, h2, h3⟩ := ih sc.advance (hex.push d) rest (col + 1) hds hadv
    simp only [List.length_cons, collectHexDigitsLoop, hpeek, hex_bool_of_isNsHexDigit hd, ite_true]
    refine ⟨?_, ?_, (keeps_advance sc).trans h3⟩
    · rw [h1]; simp
    · have : col + 1 + ds.length = col + (ds.length + 1) := by omega
      rw [← this]; exact h2

lemma parseHexEscape_accepts (ds rest : List Char) (sc : ScannerState) (col n : Nat)
    (hn : ds.length = n)
    (hhex : ∀ c, c ∈ ds → isNsHexDigit c)
    (hval : (hexVal ds).isValidChar)
    (hcorr : ScannerSurfCorr sc ⟨ds ++ rest, col⟩) :
    ∃ s', parseHexEscape sc n = .ok (Char.ofNat (hexVal ds), s') ∧
      ScannerSurfCorr s' ⟨rest, col + n⟩ ∧ Keeps sc s' := by
  subst hn
  obtain ⟨h1, h2, h3⟩ := collectHexDigitsLoop_accepts ds sc "" rest col hhex hcorr
  refine ⟨(collectHexDigitsLoop sc "" ds.length).2, ?_, h2, h3⟩
  unfold parseHexEscape
  have hlen : (collectHexDigitsLoop sc "" ds.length).1.length = ds.length := by
    rw [← String.length_toList, h1]; simp
  have hfold : (collectHexDigitsLoop sc "" ds.length).1.foldl
      (fun acc c => acc * 16 + if c.isDigit then c.toNat - '0'.toNat
        else if c >= 'a' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10) 0
      = hexVal ds := by
    rw [String.foldl_eq_foldl_toList, h1]; rfl
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ite_false, hfold, hval, ite_true]

/-! ## §5 Named escapes -/

lemma processEscape_accepts_named (sc : ScannerState) (ec : Char) (rest : List Char) (col : Nat)
    (hValid : isNamedEscapeChar ec)
    (hcorr : ScannerSurfCorr sc ⟨ec :: rest, col⟩) :
    ∃ ch s', processEscape sc = .ok (ch, s') ∧
      ScannerSurfCorr s' ⟨rest, col + 1⟩ ∧ Keeps sc s' := by
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (namedEscape_ne_lf hValid) (namedEscape_ne_cr hValid)
  unfold isNamedEscapeChar resolveNamedEscape at hValid
  split at hValid <;> first
    | exact absurd rfl hValid
    | exact ⟨_, sc.advance, by unfold processEscape; rw [hpeek]; rfl, hadv, keeps_advance sc⟩

/-! ## §6 Double-quoted one-line content, narrowed to what the scanner accepts -/

/-- `[107] nb-double-char` narrowed by `[2] nb-json` on plain chars and by
    Unicode scalar-value validity on hex escapes (see the module docstring). -/
inductive DQCharOk : SurfPos → SurfPos → Prop where
  | plain (c : Char) (rest : List Char) (col : Nat)
      (hJson : isNbJsonProp c) (hNotBs : c ≠ '\\') (hNotDq : c ≠ '"') :
      DQCharOk ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
  | escape (ec : Char) (rest : List Char) (col : Nat)
      (hValid : isNamedEscapeChar ec) :
      DQCharOk ⟨'\\' :: ec :: rest, col⟩ ⟨rest, col + 2⟩
  | hexEscape2 (rest : List Char) (col : Nat) (h1 h2 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hVal : (hexVal [h1, h2]).isValidChar) :
      DQCharOk ⟨'\\' :: 'x' :: h1 :: h2 :: rest, col⟩ ⟨rest, col + 4⟩
  | hexEscape4 (rest : List Char) (col : Nat) (h1 h2 h3 h4 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hHex3 : isNsHexDigit h3) (hHex4 : isNsHexDigit h4)
      (hVal : (hexVal [h1, h2, h3, h4]).isValidChar) :
      DQCharOk ⟨'\\' :: 'u' :: h1 :: h2 :: h3 :: h4 :: rest, col⟩ ⟨rest, col + 6⟩
  | hexEscape8 (rest : List Char) (col : Nat) (h1 h2 h3 h4 h5 h6 h7 h8 : Char)
      (hHex1 : isNsHexDigit h1) (hHex2 : isNsHexDigit h2)
      (hHex3 : isNsHexDigit h3) (hHex4 : isNsHexDigit h4)
      (hHex5 : isNsHexDigit h5) (hHex6 : isNsHexDigit h6)
      (hHex7 : isNsHexDigit h7) (hHex8 : isNsHexDigit h8)
      (hVal : (hexVal [h1, h2, h3, h4, h5, h6, h7, h8]).isValidChar) :
      DQCharOk ⟨'\\' :: 'U' :: h1 :: h2 :: h3 :: h4 :: h5 :: h6 :: h7 :: h8 :: rest, col⟩
        ⟨rest, col + 10⟩

lemma DQCharOk.toSNbDoubleChar {s s' : SurfPos} (h : DQCharOk s s') : SNbDoubleChar s s' := by
  cases h with
  | plain c rest col hJ hBs hDq =>
    exact .plain c rest col (fun hb => by
      rcases hb with hb | hb
      · exact isNbJson_ne_lf hJ (by simpa [isLineFeedProp] using hb)
      · exact isNbJson_ne_cr hJ (by simpa [isCarriageReturnProp] using hb)) hBs hDq
  | escape ec rest col hV => exact .escape ec rest col hV
  | hexEscape2 rest col h1 h2 x1 x2 _ => exact .hexEscape2 rest col h1 h2 x1 x2
  | hexEscape4 rest col h1 h2 h3 h4 x1 x2 x3 x4 _ => exact .hexEscape4 rest col h1 h2 h3 h4 x1 x2 x3 x4
  | hexEscape8 rest col h1 h2 h3 h4 h5 h6 h7 h8 x1 x2 x3 x4 x5 x6 x7 x8 _ =>
    exact .hexEscape8 rest col h1 h2 h3 h4 h5 h6 h7 h8 x1 x2 x3 x4 x5 x6 x7 x8

lemma DQCharOk.length_lt {s s' : SurfPos} (h : DQCharOk s s') : s'.chars.length < s.chars.length := by
  cases h <;> simp only [List.length_cons] <;> omega

/-- Hex-escape arm of `processEscape` shared by the three widths. -/
lemma processEscape_accepts_hex (sc : ScannerState) (tag : Char) (ds rest : List Char) (col n : Nat)
    (htag : tag = 'x' ∧ n = 2 ∨ tag = 'u' ∧ n = 4 ∨ tag = 'U' ∧ n = 8)
    (hn : ds.length = n)
    (hhex : ∀ c, c ∈ ds → isNsHexDigit c)
    (hval : (hexVal ds).isValidChar)
    (hcorr : ScannerSurfCorr sc ⟨tag :: (ds ++ rest), col⟩) :
    ∃ s', processEscape sc = .ok (Char.ofNat (hexVal ds), s') ∧
      ScannerSurfCorr s' ⟨rest, col + 1 + n⟩ ∧ Keeps sc s' := by
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (by rcases htag with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> decide)
    (by rcases htag with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> subst h <;> decide)
  obtain ⟨s', hpar, hc', hk⟩ := parseHexEscape_accepts ds rest sc.advance (col + 1) n hn hhex hval hadv
  refine ⟨s', ?_, hc', (keeps_advance sc).trans hk⟩
  rcases htag with ⟨h, hn'⟩ | ⟨h, hn'⟩ | ⟨h, hn'⟩ <;> subst h <;> subst hn' <;>
    (unfold processEscape; rw [hpeek]; exact hpar)

/-- One `DQCharOk` step is one iteration of `collectDoubleQuotedLoop`. -/
lemma collectDoubleQuotedLoop_step (sc : ScannerState) {sp sp' : SurfPos}
    (hstep : DQCharOk sp sp') (hcorr : ScannerSurfCorr sc sp)
    (content : String) (fuel' : Nat) (startPos : YamlPos) (inFlow : Bool)
    (ind : Int) (iend : Nat) (pl : Nat) :
    ∃ ch sc' pl',
      collectDoubleQuotedLoop sc content (fuel' + 1) startPos inFlow ind iend pl =
        collectDoubleQuotedLoop sc' (content.push ch) fuel' startPos inFlow ind iend pl' ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  cases hstep with
  | plain c rest col hJ hBs hDq =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (isNbJson_ne_lf hJ) (isNbJson_ne_cr hJ)
    refine ⟨c, sc.advance, if c == ' ' || c == '\t' then pl else (content.push c).length, ?_, hadv, keeps_advance sc⟩
    simp only [collectDoubleQuotedLoop, hpeek, isNbJson_not_lineBreak hJ, (isNbJson_iff c).2 hJ,
      Bool.not_true, Bool.false_eq_true, ite_false]
  | escape ec rest col hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    obtain ⟨ch, s', hproc, hc', hk⟩ := processEscape_accepts_named sc.advance ec rest (col + 1) hV hadv
    refine ⟨ch, s', (content.push ch).length, ?_, ?_, (keeps_advance sc).trans hk⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, namedEscape_not_lineBreak hV, hproc,
        Bool.false_eq_true, ite_false, bind, Except.bind]
    · have : col + 1 + 1 = col + 2 := rfl
      rw [← this]; exact hc'
  | hexEscape2 rest col h1 h2 x1 x2 hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hhex : ∀ c, c ∈ [h1, h2] → isNsHexDigit c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> assumption
    obtain ⟨s', hproc, hc', hk⟩ := processEscape_accepts_hex sc.advance 'x' [h1, h2] rest (col + 1) 2
      (Or.inl ⟨rfl, rfl⟩) rfl hhex hV hadv
    refine ⟨Char.ofNat (hexVal [h1, h2]), s', (content.push (Char.ofNat (hexVal [h1, h2]))).length, ?_, ?_,
      (keeps_advance sc).trans hk⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hproc, Bool.false_eq_true, ite_false,
        bind, Except.bind, (by decide : isLineBreakBool 'x' = false)]
    · have : col + 1 + 1 + 2 = col + 4 := rfl
      rw [← this]; exact hc'
  | hexEscape4 rest col h1 h2 h3 h4 x1 x2 x3 x4 hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hhex : ∀ c, c ∈ [h1, h2, h3, h4] → isNsHexDigit c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨s', hproc, hc', hk⟩ := processEscape_accepts_hex sc.advance 'u' [h1, h2, h3, h4] rest (col + 1) 4
      (Or.inr (Or.inl ⟨rfl, rfl⟩)) rfl hhex hV hadv
    refine ⟨Char.ofNat (hexVal [h1, h2, h3, h4]), s', (content.push (Char.ofNat (hexVal [h1, h2, h3, h4]))).length, ?_, ?_,
      (keeps_advance sc).trans hk⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hproc, Bool.false_eq_true, ite_false,
        bind, Except.bind, (by decide : isLineBreakBool 'u' = false)]
    · have : col + 1 + 1 + 4 = col + 6 := rfl
      rw [← this]; exact hc'
  | hexEscape8 rest col h1 h2 h3 h4 h5 h6 h7 h8 x1 x2 x3 x4 x5 x6 x7 x8 hV =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hhex : ∀ c, c ∈ [h1, h2, h3, h4, h5, h6, h7, h8] → isNsHexDigit c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨s', hproc, hc', hk⟩ := processEscape_accepts_hex sc.advance 'U' [h1, h2, h3, h4, h5, h6, h7, h8] rest (col + 1) 8
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) rfl hhex hV hadv
    refine ⟨Char.ofNat (hexVal [h1, h2, h3, h4, h5, h6, h7, h8]), s', (content.push (Char.ofNat (hexVal [h1, h2, h3, h4, h5, h6, h7, h8]))).length, ?_, ?_,
      (keeps_advance sc).trans hk⟩
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hproc, Bool.false_eq_true, ite_false,
        bind, Except.bind, (by decide : isLineBreakBool 'U' = false)]
    · have : col + 1 + 1 + 8 = col + 10 := rfl
      rw [← this]; exact hc'

lemma collectDoubleQuotedLoop_accepts {sp sp' : SurfPos} (hder : GStar DQCharOk sp sp') :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
      (ind : Int) (iend pl : Nat) (rest : List Char),
      ScannerSurfCorr sc sp → sp.chars.length < fuel → sp'.chars = '"' :: rest →
      ∃ content' sc',
        collectDoubleQuotedLoop sc content fuel startPos inFlow ind iend pl = .ok (content', sc') ∧
        ScannerSurfCorr sc' ⟨rest, sp'.col + 1⟩ ∧ Keeps sc sc' := by
  induction hder with
  | nil s =>
    intro sc content fuel startPos inFlow ind iend pl rest hcorr hfuel hend
    obtain ⟨chars, col⟩ := s
    simp only at hend hfuel ⊢
    subst hend
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      have hpeek := (peek_of_corr hcorr).1
      refine ⟨content, sc.advance, ?_, advance_corr hcorr (by decide) (by decide), keeps_advance sc⟩
      simp only [collectDoubleQuotedLoop, hpeek]
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content fuel startPos inFlow ind iend pl rest hcorr hfuel hend
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      obtain ⟨ch, sc', pl', heq, hcorr', hk⟩ :=
        collectDoubleQuotedLoop_step sc hstep hcorr content fuel' startPos inFlow ind iend pl
      have hlt := hstep.length_lt
      obtain ⟨content', sc'', hok, hc'', hk'⟩ :=
        ih sc' (content.push ch) fuel' startPos inFlow ind iend pl' rest hcorr' (by omega) hend
      exact ⟨content', sc'', heq.trans hok, hc'', hk.trans hk'⟩

/-! ## §7 Trailing content after the closing quote (block context, §7.3) -/

/-- What may follow the closing quote in block context: white, then end, break, `#` or `:`. -/
def TrailingOk (rest : List Char) : Prop :=
  match rest.dropWhile (fun c => c == ' ' || c == '\t') with
  | [] => True
  | c :: _ => isLineBreakProp c ∨ c = '#' ∨ c = ':'

instance (rest : List Char) : Decidable (TrailingOk rest) := by
  unfold TrailingOk; split <;> exact inferInstance

lemma skipTrailingSpaces_corr (rest : List Char) :
    ∀ (sc : ScannerState) (col fuel : Nat),
      ScannerSurfCorr sc ⟨rest, col⟩ → rest.length < fuel →
      ∃ k, ScannerSurfCorr (skipTrailingSpaces sc fuel)
        ⟨rest.dropWhile (fun c => c == ' ' || c == '\t'), col + k⟩ := by
  induction rest with
  | nil =>
    intro sc col fuel hcorr hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      refine ⟨0, ?_⟩
      simp only [skipTrailingSpaces, peek_none_of_corr hcorr, List.dropWhile_nil, Nat.add_zero]
      exact hcorr
  | cons c rest ih =>
    intro sc col fuel hcorr hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      have hpeek := (peek_of_corr hcorr).1
      by_cases hw : (c == ' ' || c == '\t') = true
      · have hc : c = ' ' ∨ c = '\t' := by simpa using hw
        have hadv := advance_corr hcorr (by rcases hc with rfl | rfl <;> decide)
          (by rcases hc with rfl | rfl <;> decide)
        obtain ⟨k, hk⟩ := ih sc.advance (col + 1) fuel' hadv (by simp at hfuel; omega)
        refine ⟨k + 1, ?_⟩
        simp only [skipTrailingSpaces, hpeek, hw, ite_true, List.dropWhile_cons]
        have : col + 1 + k = col + (k + 1) := by omega
        rw [← this]; exact hk
      · refine ⟨0, ?_⟩
        simp only [skipTrailingSpaces, hpeek, hw, Bool.false_eq_true, ite_false, List.dropWhile_cons,
          Nat.add_zero]
        exact hcorr

lemma validateTrailingContent_accepts (sc : ScannerState) (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨rest, col⟩) (hok : TrailingOk rest) :
    validateTrailingContent sc sc.inputEnd = .ok () := by
  have hfuel := fuel_of_corr hcorr
  simp only at hfuel
  obtain ⟨k, hk⟩ := skipTrailingSpaces_corr rest sc col _ hcorr hfuel
  unfold validateTrailingContent
  unfold TrailingOk at hok
  split at hok
  · rename_i hdrop
    rw [hdrop] at hk
    simp only [peek_none_of_corr hk]
    rfl
  · rename_i c tl hdrop
    rw [hdrop] at hk
    have hpeek := (peek_of_corr hk).1
    simp only [hpeek]
    rcases hok with h | h | h
    · simp [(isLineBreak_iff c).2 h]; rfl
    · subst h; simp; rfl
    · subst h; simp; rfl

/-! ## §8 The double-quoted converse -/

/-- `[109] c-double-quoted` with its one-line content narrowed to `DQCharOk`. -/
inductive SCDoubleQuotedOk : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s' : SurfPos) :
      GLit '"' s s₁ → GStar DQCharOk s₁ s₂ → GLit '"' s₂ s' → SCDoubleQuotedOk s s'

lemma GStar_mono {P Q : SurfPos → SurfPos → Prop} (h : ∀ s s', P s s' → Q s s')
    {s s' : SurfPos} (hd : GStar P s s') : GStar Q s s' := by
  induction hd with
  | nil s => exact .nil s
  | cons s₁ s₂ s₃ h₁ _ ih => exact .cons s₁ s₂ s₃ (h _ _ h₁) ih

/-- The narrowed relation is a sub-relation of `[109]` at every `n` and `c`. -/
lemma SCDoubleQuotedOk.toSCDoubleQuoted (n : Nat) (c : L4YAML.YamlContext) {s s' : SurfPos}
    (h : SCDoubleQuotedOk s s') : SCDoubleQuoted n c s s' := by
  rcases h with ⟨a, b, d, h1, hstar, h2⟩
  have hone := GStar_mono (fun _ _ => DQCharOk.toSNbDoubleChar) hstar
  refine .mk n c _ _ _ _ h1 ?_ h2
  cases c <;> first | exact hone | exact .single n _ _ hone

/-- Converse of `scanDoubleQuoted_prod` (one-line): a `SCDoubleQuotedOk` derivation at the
    scanner's position is accepted, landing at its end with the `.doubleQuoted` token.
    `htrail` is the block-context §7.3 trailing check (`"a"b` refutes the converse without it). -/
lemma scanDoubleQuoted_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : SCDoubleQuotedOk sp sp')
    (htrail : sc.inFlow = true ∨ TrailingOk sp'.chars) :
    ∃ s' content, scanDoubleQuoted sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .doubleQuoted } := by
  rcases hder with ⟨a, b, d, h1, hstar, h2⟩
  cases h1 with | mk rest₁ col =>
  cases h2 with | mk rest col₂ =>
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (by decide) (by decide)
  have hfuel := fuel_of_corr hadv
  simp only at hfuel
  rw [(keeps_advance sc).2.1] at hfuel
  obtain ⟨content, sc₂, hloop, hc₂, hk⟩ := collectDoubleQuotedLoop_accepts hstar sc.advance ""
    _ sc.currentPos sc.inFlow sc.currentIndent sc.inputEnd 0 rest hadv hfuel rfl
  simp only at hc₂ htrail
  have hk' := (keeps_advance sc).trans hk
  refine ⟨{ sc₂.emitAt sc.currentPos (.scalar content .doubleQuoted) with
      simpleKeyAllowed := false, needIndentCheck := false }, content, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc₂), ?_⟩
  · unfold scanDoubleQuoted
    simp only [hloop, bind, Except.bind]
    rcases htrail with hf | ht
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false]
    · have hv := validateTrailingContent_accepts sc₂ rest (col₂ + 1) hc₂ ht
      rw [hk'.2.1] at hv
      cases hf : sc.inFlow
      · simp only [Bool.not_false, ite_true, hv]
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  · simp [ScannerState.emitAt, hk'.1]

/-! ## §9 The single-quoted converse -/

/-- `[118] nb-single-char` narrowed by `[2] nb-json` on plain chars. -/
inductive SQCharOk : SurfPos → SurfPos → Prop where
  | plain (c : Char) (rest : List Char) (col : Nat)
      (hJson : isNbJsonProp c) (hNotSq : c ≠ '\'') :
      SQCharOk ⟨c :: rest, col⟩ ⟨rest, col + 1⟩
  | escapedQuote (rest : List Char) (col : Nat) :
      SQCharOk ⟨'\'' :: '\'' :: rest, col⟩ ⟨rest, col + 2⟩

lemma SQCharOk.toSNbSingleChar {s s' : SurfPos} (h : SQCharOk s s') : SNbSingleChar s s' := by
  cases h with
  | plain c rest col hJ hSq =>
    exact .plain c rest col (fun hb => by
      rcases hb with hb | hb
      · exact isNbJson_ne_lf hJ (by simpa [isLineFeedProp] using hb)
      · exact isNbJson_ne_cr hJ (by simpa [isCarriageReturnProp] using hb)) hSq
  | escapedQuote rest col => exact .escapedQuote rest col

lemma SQCharOk.length_lt {s s' : SurfPos} (h : SQCharOk s s') : s'.chars.length < s.chars.length := by
  cases h <;> simp only [List.length_cons] <;> omega

/-- One `SQCharOk` step is one iteration of `collectSingleQuotedLoop`. -/
lemma collectSingleQuotedLoop_step (sc : ScannerState) {sp sp' : SurfPos}
    (hstep : SQCharOk sp sp') (hcorr : ScannerSurfCorr sc sp)
    (content : String) (fuel' : Nat) (startPos : YamlPos) (inFlow : Bool) (ind : Int) (iend : Nat) :
    ∃ ch sc',
      collectSingleQuotedLoop sc content (fuel' + 1) startPos inFlow ind iend =
        collectSingleQuotedLoop sc' (content.push ch) fuel' startPos inFlow ind iend ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  cases hstep with
  | plain c rest col hJ hSq =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (isNbJson_ne_lf hJ) (isNbJson_ne_cr hJ)
    refine ⟨c, sc.advance, ?_, hadv, keeps_advance sc⟩
    simp only [collectSingleQuotedLoop, hpeek, isNbJson_not_lineBreak hJ, (isNbJson_iff c).2 hJ,
      Bool.not_true, Bool.false_eq_true, ite_false]
  | escapedQuote rest col =>
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpeek2 := (peek_of_corr hadv).1
    have hadv2 := advance_corr hadv (by decide) (by decide)
    refine ⟨'\'', sc.advance.advance, ?_, hadv2, (keeps_advance sc).trans (keeps_advance _)⟩
    simp only [collectSingleQuotedLoop, hpeek, hpeek2]

lemma collectSingleQuotedLoop_accepts {sp sp' : SurfPos} (hder : GStar SQCharOk sp sp') :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
      (ind : Int) (iend : Nat) (rest : List Char),
      ScannerSurfCorr sc sp → sp.chars.length < fuel → sp'.chars = '\'' :: rest →
      rest.head? ≠ some '\'' →
      ∃ content' sc',
        collectSingleQuotedLoop sc content fuel startPos inFlow ind iend = .ok (content', sc') ∧
        ScannerSurfCorr sc' ⟨rest, sp'.col + 1⟩ ∧ Keeps sc sc' := by
  induction hder with
  | nil s =>
    intro sc content fuel startPos inFlow ind iend rest hcorr hfuel hend hq
    obtain ⟨chars, col⟩ := s
    simp only at hend hfuel ⊢
    subst hend
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      have hpeek := (peek_of_corr hcorr).1
      have hadv := advance_corr hcorr (by decide) (by decide)
      refine ⟨content, sc.advance, ?_, hadv, keeps_advance sc⟩
      cases rest with
      | nil => simp only [collectSingleQuotedLoop, hpeek, peek_none_of_corr hadv]
      | cons c tl =>
        have hpeek2 := (peek_of_corr hadv).1
        have hc : c ≠ '\'' := fun h => hq (by simp [h])
        simp only [collectSingleQuotedLoop, hpeek, hpeek2]
        split
        · rename_i heq; exact absurd (Option.some.inj heq) hc
        · rfl
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content fuel startPos inFlow ind iend rest hcorr hfuel hend hq
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      obtain ⟨ch, sc', heq, hcorr', hk⟩ :=
        collectSingleQuotedLoop_step sc hstep hcorr content fuel' startPos inFlow ind iend
      have hlt := hstep.length_lt
      obtain ⟨content', sc'', hok, hc'', hk'⟩ :=
        ih sc' (content.push ch) fuel' startPos inFlow ind iend rest hcorr' (by omega) hend hq
      exact ⟨content', sc'', heq.trans hok, hc'', hk.trans hk'⟩

/-- `[120] c-single-quoted` with its one-line content narrowed to `SQCharOk`. -/
inductive SCSingleQuotedOk : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s' : SurfPos) :
      GLit '\'' s s₁ → GStar SQCharOk s₁ s₂ → GLit '\'' s₂ s' → SCSingleQuotedOk s s'

/-- The narrowed relation is a sub-relation of `[120]` at every `n` and `c`. -/
lemma SCSingleQuotedOk.toSCSingleQuoted (n : Nat) (c : L4YAML.YamlContext) {s s' : SurfPos}
    (h : SCSingleQuotedOk s s') : SCSingleQuoted n c s s' := by
  rcases h with ⟨a, b, d, h1, hstar, h2⟩
  have hone := GStar_mono (fun _ _ => SQCharOk.toSNbSingleChar) hstar
  refine .mk n c _ _ _ _ h1 ?_ h2
  cases c <;> first | exact hone | exact .single n _ _ hone

/-- Converse of `scanSingleQuoted_prod` (one-line).  `hq`: the char after the closing quote is
    not `'` (else the scanner reads `[117] c-quoted-quote`: `''''` lands after all four quotes);
    `htrail` is the block-context §7.3 trailing check. -/
lemma scanSingleQuoted_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : SCSingleQuotedOk sp sp')
    (hq : sp'.chars.head? ≠ some '\'')
    (htrail : sc.inFlow = true ∨ TrailingOk sp'.chars) :
    ∃ s' content, scanSingleQuoted sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .singleQuoted } := by
  rcases hder with ⟨a, b, d, h1, hstar, h2⟩
  cases h1 with | mk rest₁ col =>
  cases h2 with | mk rest col₂ =>
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (by decide) (by decide)
  have hfuel := fuel_of_corr hadv
  simp only at hfuel hq htrail
  rw [(keeps_advance sc).2.1] at hfuel
  obtain ⟨content, sc₂, hloop, hc₂, hk⟩ := collectSingleQuotedLoop_accepts hstar sc.advance ""
    _ sc.currentPos sc.inFlow sc.currentIndent sc.inputEnd rest hadv hfuel rfl hq
  simp only at hc₂
  have hk' := (keeps_advance sc).trans hk
  refine ⟨{ sc₂.emitAt sc.currentPos (.scalar content .singleQuoted) with
      simpleKeyAllowed := false, needIndentCheck := false }, content, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc₂), ?_⟩
  · unfold scanSingleQuoted
    simp only [hloop, bind, Except.bind]
    rcases htrail with hf | ht
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false]
    · have hv := validateTrailingContent_accepts sc₂ rest (col₂ + 1) hc₂ ht
      rw [hk'.2.1] at hv
      cases hf : sc.inFlow
      · simp only [Bool.not_false, ite_true, hv]
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  · simp [ScannerState.emitAt, hk'.1]

/-! ## §10 Multi-line quoted scalars — break and landing acceptance -/

/-- `[28] b-break` as `consumeNewline` reads it: a lone CR is a break only when no LF
    follows (else the scanner takes the pair as one CRLF break). -/
inductive SBBreakOk : SurfPos → SurfPos → Prop where
  | lf (rest : List Char) (col : Nat) : SBBreakOk ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩
  | crLf (rest : List Char) (col : Nat) : SBBreakOk ⟨'\r' :: '\n' :: rest, col⟩ ⟨rest, 0⟩
  | cr (rest : List Char) (col : Nat) (h : rest.head? ≠ some '\n') :
      SBBreakOk ⟨'\r' :: rest, col⟩ ⟨rest, 0⟩

lemma SBBreakOk.toSBBreak {s s' : SurfPos} (h : SBBreakOk s s') : SBBreak s s' := by
  cases h with
  | lf rest col => exact .lf rest col
  | crLf rest col => exact .crLf rest col
  | cr rest col _ => exact .cr rest col

lemma SBBreakOk.length_lt {s s' : SurfPos} (h : SBBreakOk s s') : s'.chars.length < s.chars.length := by
  cases h <;> simp only [List.length_cons] <;> omega

lemma keeps_needIndentCheck (sc : ScannerState) (b : Bool) :
    Keeps sc { sc with needIndentCheck := b } := ⟨rfl, rfl, rfl⟩

lemma consumeNewline_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hb : SBBreakOk sp sp') (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr (consumeNewline sc) sp' ∧ Keeps sc (consumeNewline sc) := by
  cases hb with
  | lf rest col =>
    obtain ⟨hpeek, hmore⟩ := peek_of_corr hcorr
    have hcol := hcorr.col_eq; simp only at hcol; subst hcol
    have hadv := advance_newline_corr sc rest hcorr hmore
    unfold consumeNewline; simp only [hpeek]
    exact ⟨corr_of_needIndentCheck_update true hadv, (keeps_advance sc).trans (keeps_needIndentCheck _ _)⟩
  | crLf rest col =>
    obtain ⟨hpeek, hmore⟩ := peek_of_corr hcorr
    have hcol := hcorr.col_eq; simp only at hcol; subst hcol
    have hadv := advance_cr_corr sc ('\n' :: rest) hcorr hmore
    obtain ⟨hpeek2, hmore2⟩ := peek_of_corr hadv
    have hskip := skip_byte_corr sc.advance '\n' rest 0 hadv hmore2
    unfold consumeNewline; simp only [hpeek, hpeek2]
    exact ⟨corr_of_needIndentCheck_update true hskip, (keeps_advance sc).1, (keeps_advance sc).2.1, (keeps_advance sc).2.2⟩
  | cr rest col hq =>
    obtain ⟨hpeek, hmore⟩ := peek_of_corr hcorr
    have hcol := hcorr.col_eq; simp only at hcol; subst hcol
    have hadv := advance_cr_corr sc rest hcorr hmore
    have hpeek2 : sc.advance.peek? ≠ some '\n' := by
      intro h
      obtain ⟨rest', hsp⟩ := peek_some_sp hadv h
      simp only [SurfPos.mk.injEq] at hsp
      exact hq (by rw [hsp.1]; rfl)
    unfold consumeNewline; simp only [hpeek]
    first
      | exact ⟨corr_of_needIndentCheck_update true hadv, (keeps_advance sc).trans (keeps_needIndentCheck _ _)⟩
      | (split
         · rename_i h; exact absurd h hpeek2
         · exact ⟨corr_of_needIndentCheck_update true hadv, (keeps_advance sc).trans (keeps_needIndentCheck _ _)⟩)

/-- `skipSpacesLoop` lands exactly at the end of an `SIndent n` run when that run is maximal. -/
lemma skipSpacesLoop_accepts (n : Nat) :
    ∀ (sc : ScannerState) (sp sp' : SurfPos) (fuel : Nat),
      SIndent n sp sp' → ScannerSurfCorr sc sp → sp'.chars.head? ≠ some ' ' → n ≤ fuel →
      ScannerSurfCorr (skipSpacesLoop sc fuel) sp' ∧ Keeps sc (skipSpacesLoop sc fuel) := by
  induction n with
  | zero =>
    intro sc sp sp' fuel hind hcorr hmax _
    cases hind
    cases fuel with
    | zero => simp only [skipSpacesLoop]; exact ⟨hcorr, Keeps.refl sc⟩
    | succ fuel' =>
      obtain ⟨chars, col⟩ := sp
      cases chars with
      | nil => simp only [skipSpacesLoop, peek_none_of_corr hcorr]; exact ⟨hcorr, Keeps.refl sc⟩
      | cons c tl =>
        have hpeek := (peek_of_corr hcorr).1
        have hc : c ≠ ' ' := fun h => hmax (by simp [h])
        simp only [skipSpacesLoop, hpeek]
        split
        · rename_i heq; exact absurd (Option.some.inj heq) hc
        · exact ⟨hcorr, Keeps.refl sc⟩
  | succ n ih =>
    intro sc sp sp' fuel hind hcorr hmax hfuel
    cases hind with
    | succ _ rest col _ hind' =>
      cases fuel with
      | zero => omega
      | succ fuel' =>
        have hpeek := (peek_of_corr hcorr).1
        have hadv := advance_corr hcorr (by decide) (by decide)
        obtain ⟨h1, h2⟩ := ih sc.advance _ sp' fuel' hind' hadv hmax (by omega)
        simp only [skipSpacesLoop, hpeek]
        exact ⟨h1, (keeps_advance sc).trans h2⟩

lemma SIndent_length_le {n : Nat} {s s' : SurfPos} (h : SIndent n s s') :
    s.chars.length = s'.chars.length + n := by
  induction h with
  | zero => simp
  | succ n rest col s' _ ih => dsimp only at ih ⊢; simp only [List.length_cons] at ih ⊢; omega

lemma skipSpaces_accepts (sc : ScannerState) {n : Nat} {sp sp' : SurfPos}
    (hind : SIndent n sp sp') (hcorr : ScannerSurfCorr sc sp) (hmax : sp'.chars.head? ≠ some ' ') :
    ScannerSurfCorr (skipSpaces sc) sp' ∧ Keeps sc (skipSpaces sc) := by
  have hfuel := fuel_of_corr hcorr
  have hlen := SIndent_length_le hind
  unfold skipSpaces
  exact skipSpacesLoop_accepts n sc sp sp' _ hind hcorr hmax (by omega)

lemma GStar_SSWhite_length {s s' : SurfPos} (h : GStar SSWhite s s') : s'.chars.length ≤ s.chars.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ _ _ h₁ _ ih => cases h₁ <;> (dsimp only at ih ⊢; simp only [List.length_cons] at ih ⊢; omega)

/-- `skipWhitespaceLoop` lands at the end of a maximal `GStar SSWhite` run. -/
lemma skipWhitespaceLoop_accepts {sp sp' : SurfPos} (hw : GStar SSWhite sp sp') :
    ∀ (sc : ScannerState) (fuel : Nat), ScannerSurfCorr sc sp →
      sp'.chars.head? ≠ some ' ' → sp'.chars.head? ≠ some '\t' →
      sp.chars.length - sp'.chars.length ≤ fuel →
      ScannerSurfCorr (skipWhitespaceLoop sc fuel) sp' ∧ Keeps sc (skipWhitespaceLoop sc fuel) := by
  induction hw with
  | nil s =>
    intro sc fuel hcorr hsp htab _
    cases fuel with
    | zero => simp only [skipWhitespaceLoop]; exact ⟨hcorr, Keeps.refl sc⟩
    | succ fuel' =>
      obtain ⟨chars, col⟩ := s
      cases chars with
      | nil => simp only [skipWhitespaceLoop, peek_none_of_corr hcorr]; exact ⟨hcorr, Keeps.refl sc⟩
      | cons c tl =>
        have hpeek := (peek_of_corr hcorr).1
        have hc : isWhiteSpaceBool c = false := by
          cases h : isWhiteSpaceBool c
          · rfl
          · exfalso
            simp only [isWhiteSpaceBool, isSpaceBool, isTabBool, Bool.or_eq_true, beq_iff_eq] at h
            rcases h with rfl | rfl
            · exact hsp (by simp)
            · exact htab (by simp)
        simp only [skipWhitespaceLoop, hpeek, hc, Bool.false_eq_true, ite_false]
        exact ⟨hcorr, Keeps.refl sc⟩
  | cons s₁ s₂ s₃ h₁ h₂ ih =>
    intro sc fuel hcorr hsp htab hfuel
    have hlt := GStar_SSWhite_length h₂
    cases h₁ with
    | space rest col =>
      cases fuel with
      | zero => simp at hfuel hlt; omega
      | succ fuel' =>
        have hpeek := (peek_of_corr hcorr).1
        have hadv := advance_corr hcorr (by decide) (by decide)
        obtain ⟨h1, h2⟩ := ih sc.advance fuel' hadv hsp htab (by
          have hf : rest.length - s₃.chars.length ≤ fuel' := by simp at hfuel; omega
          exact hf)
        simp only [skipWhitespaceLoop, hpeek, isWhiteSpaceBool, isSpaceBool, isTabBool]
        exact ⟨h1, (keeps_advance sc).trans h2⟩
    | tab rest col =>
      cases fuel with
      | zero => simp at hfuel hlt; omega
      | succ fuel' =>
        have hpeek := (peek_of_corr hcorr).1
        have hadv := advance_corr hcorr (by decide) (by decide)
        obtain ⟨h1, h2⟩ := ih sc.advance fuel' hadv hsp htab (by
          have hf : rest.length - s₃.chars.length ≤ fuel' := by simp at hfuel; omega
          exact hf)
        simp only [skipWhitespaceLoop, hpeek, isWhiteSpaceBool, isSpaceBool, isTabBool]
        exact ⟨h1, (keeps_advance sc).trans h2⟩

lemma skipWhitespace_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hw : GStar SSWhite sp sp') (hcorr : ScannerSurfCorr sc sp)
    (hsp : sp'.chars.head? ≠ some ' ') (htab : sp'.chars.head? ≠ some '\t') :
    ScannerSurfCorr (skipWhitespace sc) sp' ∧ Keeps sc (skipWhitespace sc) := by
  have hfuel := fuel_of_corr hcorr
  unfold skipWhitespace
  exact skipWhitespaceLoop_accepts hw sc _ hcorr hsp htab (by omega)

/-! ## §11 Folded breaks: blank lines and the landing line prefix -/

/-- `[70] l-empty(n,FLOW-IN)` with `SBBreakOk` breaks. -/
inductive SLEmptyOk (n : Nat) : SurfPos → SurfPos → Prop where
  | flow (s s₁ s' : SurfPos) : GOpt (SFlowLinePrefix n) s s₁ → SBBreakOk s₁ s' → SLEmptyOk n s s'
  | flowLt (s s₁ s' : SurfPos) : SIndentLt n s s₁ → SBBreakOk s₁ s' → SLEmptyOk n s s'

lemma SLEmptyOk.toSLEmpty {n : Nat} {s s' : SurfPos} (h : SLEmptyOk n s s') :
    SLEmpty n .flowIn s s' := by
  rcases h with ⟨_, _, h1, h2⟩ | ⟨_, _, h1, h2⟩
  · exact .flow n _ _ _ .flowIn (Or.inr rfl) h1 h2.toSBBreak
  · exact .flowLt n _ _ _ .flowIn (Or.inr rfl) h1 h2.toSBBreak

/-- No `---`/`...` at column 0 (conservative: `[203]`/`[204]` also need a blank after). -/
def NotDocMarker (sp : SurfPos) : Prop :=
  sp.col = 0 → (∀ r, sp.chars ≠ '-' :: '-' :: '-' :: r) ∧ (∀ r, sp.chars ≠ '.' :: '.' :: '.' :: r)

lemma atDocumentStart_false_of_corr {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (h : NotDocMarker sp) : atDocumentStart sc = false := by
  cases hd : atDocumentStart sc
  · rfl
  · exfalso
    obtain ⟨r, hc, hcol⟩ := atDocumentStart_chars sc sp hcorr hd
    exact (h hcol).1 r hc

lemma atDocumentEnd_false_of_corr {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (h : NotDocMarker sp) : atDocumentEnd sc = false := by
  cases hd : atDocumentEnd sc
  · rfl
  · exfalso
    obtain ⟨r, hc, hcol⟩ := atDocumentEnd_chars sc sp hcorr hd
    exact (h hcol).2 r hc

lemma keeps_skipSpacesLoop (fuel : Nat) : ∀ sc : ScannerState, Keeps sc (skipSpacesLoop sc fuel) := by
  induction fuel with
  | zero => intro sc; simp only [skipSpacesLoop]; exact Keeps.refl sc
  | succ f ih =>
    intro sc
    simp only [skipSpacesLoop]
    split
    · exact (keeps_advance sc).trans (ih _)
    · exact Keeps.refl sc

lemma keeps_skipWhitespaceLoop (fuel : Nat) : ∀ sc : ScannerState, Keeps sc (skipWhitespaceLoop sc fuel) := by
  induction fuel with
  | zero => intro sc; simp only [skipWhitespaceLoop]; exact Keeps.refl sc
  | succ f ih =>
    intro sc
    simp only [skipWhitespaceLoop]
    split
    · split
      · exact (keeps_advance sc).trans (ih _)
      · exact Keeps.refl sc
    · exact Keeps.refl sc

/-- `skipSpacesLoop` through a white run: it eats the leading spaces and stops at the
    first tab or non-white; the remainder is still a (maximal) white run to `sp'`. -/
lemma skipSpacesLoop_white_prefix {spa sp' : SurfPos} (hw : GStar SSWhite spa sp') :
    ∀ (sc : ScannerState) (fuel : Nat), ScannerSurfCorr sc spa → sp'.chars.head? ≠ some ' ' →
      spa.chars.length ≤ fuel →
      ∃ sp₁, ScannerSurfCorr (skipSpacesLoop sc fuel) sp₁ ∧ GStar SSWhite sp₁ sp' ∧
        sp₁.chars.head? ≠ some ' ' ∧ sp₁.col ≥ spa.col := by
  induction hw with
  | nil s =>
    intro sc fuel hcorr hmax _
    exact ⟨s, (skipSpacesLoop_accepts 0 sc s s fuel (.zero s) hcorr hmax (Nat.zero_le _)).1,
      .nil s, hmax, Nat.le_refl _⟩
  | cons s₁ s₂ s₃ h₁ h₂ ih =>
    intro sc fuel hcorr hmax hfuel
    cases h₁ with
    | space rest col =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpeek := (peek_of_corr hcorr).1
        have hadv := advance_corr hcorr (by decide) (by decide)
        obtain ⟨sp₁, h1, h2, h3, h4⟩ := ih sc.advance f hadv hmax (by simp at hfuel ⊢; omega)
        simp only [skipSpacesLoop, hpeek]
        exact ⟨sp₁, h1, h2, h3, by simp at h4 ⊢; omega⟩
    | tab rest col =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpeek := (peek_of_corr hcorr).1
        simp only [skipSpacesLoop, hpeek]
        exact ⟨⟨'\t' :: rest, col⟩, hcorr, .cons _ _ _ (.tab rest col) h₂, by simp, Nat.le_refl _⟩

lemma skipSpacesLoop_prefix_accepts (n : Nat) :
    ∀ (sc : ScannerState) (sp spa sp' : SurfPos) (fuel : Nat),
      SIndent n sp spa → GStar SSWhite spa sp' → ScannerSurfCorr sc sp →
      sp'.chars.head? ≠ some ' ' → sp.chars.length ≤ fuel →
      ∃ sp₁, ScannerSurfCorr (skipSpacesLoop sc fuel) sp₁ ∧ GStar SSWhite sp₁ sp' ∧
        sp₁.chars.head? ≠ some ' ' ∧ sp₁.col ≥ sp.col + n := by
  induction n with
  | zero =>
    intro sc sp spa sp' fuel hind hw hcorr hmax hfuel
    cases hind
    obtain ⟨sp₁, h1, h2, h3, h4⟩ := skipSpacesLoop_white_prefix hw sc fuel hcorr hmax hfuel
    exact ⟨sp₁, h1, h2, h3, by omega⟩
  | succ n ih =>
    intro sc sp spa sp' fuel hind hw hcorr hmax hfuel
    cases hind with
    | succ _ rest col _ hind' =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpeek := (peek_of_corr hcorr).1
        have hadv := advance_corr hcorr (by decide) (by decide)
        obtain ⟨sp₁, h1, h2, h3, h4⟩ := ih sc.advance _ spa sp' f hind' hw hadv hmax (by simp at hfuel ⊢; omega)
        simp only [skipSpacesLoop, hpeek]
        exact ⟨sp₁, h1, h2, h3, by simp at h4 ⊢; omega⟩

lemma GOpt_sepInLine_to_gstar {s s' : SurfPos} (h : GOpt SSeparateInLine s s') : GStar SSWhite s s' := by
  cases h with
  | none => exact .nil _
  | some _ h' =>
    cases h' with
    | whites =>
      rename_i hp
      cases hp
      rename_i h1 h2
      exact .cons _ _ _ h1 h2
    | startOfLine => exact .nil _

/-- `[69] s-flow-line-prefix(n)` landing: `skipSpaces`, the §6.1 tab gate (dead, since the
    column clears the floor), `skipWhitespace` — lands at `sp'` when the white run is maximal. -/
lemma flowLinePrefix_accepts (sc : ScannerState) {n : Nat} {sp sp' : SurfPos}
    (hpre : SFlowLinePrefix n sp sp') (hcorr : ScannerSurfCorr sc sp)
    (hsp : sp'.chars.head? ≠ some ' ') (htab : sp'.chars.head? ≠ some '\t')
    (hfloor : (n : Int) > sc.currentIndent) :
    ScannerSurfCorr (skipWhitespace (skipSpaces sc)) sp' ∧
    ¬ (((skipSpaces sc).col : Int) ≤ (skipSpaces sc).currentIndent) ∧
    Keeps sc (skipWhitespace (skipSpaces sc)) := by
  rcases hpre with ⟨_, _, hind, hopt⟩
  · have hw := GOpt_sepInLine_to_gstar hopt
    have hfuel := fuel_of_corr hcorr
    obtain ⟨sp₁, h1, h2, h3, h4⟩ :=
      skipSpacesLoop_prefix_accepts n sc sp _ sp' (sc.inputEnd - sc.offset) hind hw hcorr hsp (by omega)
    have hk1 : Keeps sc (skipSpaces sc) := keeps_skipSpacesLoop _ sc
    obtain ⟨h5, h6⟩ := skipWhitespace_accepts (skipSpaces sc) h2 h1 hsp htab
    refine ⟨h5, ?_, hk1.trans h6⟩
    have hcol : (skipSpaces sc).col = sp₁.col := h1.col_eq.symm
    rw [hk1.currentIndent, hcol]
    omega

/-! ## §12 Blank lines and the fold loop -/

lemma SBBreakOk.head {s s' : SurfPos} (h : SBBreakOk s s') :
    ∃ c rest, s.chars = c :: rest ∧ isLineBreakBool c = true := by
  cases h with
  | lf rest col => exact ⟨'\n', rest, rfl, rfl⟩
  | crLf rest col => exact ⟨'\r', '\n' :: rest, rfl, rfl⟩
  | cr rest col _ => exact ⟨'\r', rest, rfl, rfl⟩

lemma lineBreak_ne_space {c : Char} (h : isLineBreakBool c = true) : c ≠ ' ' := by
  intro hc; subst hc; simp [isLineBreakBool, isLineFeedBool, isCarriageReturnBool] at h

lemma lineBreak_ne_tab {c : Char} (h : isLineBreakBool c = true) : c ≠ '\t' := by
  intro hc; subst hc; simp [isLineBreakBool, isLineFeedBool, isCarriageReturnBool] at h

lemma SLEmptyOk.length_lt {n : Nat} {s s' : SurfPos} (h : SLEmptyOk n s s') :
    s'.chars.length < s.chars.length := by
  rcases h with ⟨_, _, hopt, hb⟩ | ⟨_, _, hlt, hb⟩
  · have h1 := hb.length_lt
    rcases hopt with _ | ⟨_, hp⟩
    · exact h1
    · rcases hp with ⟨_, _, hind, hsep⟩
      have h2 := SIndent_length_le hind
      have h3 := GStar_SSWhite_length (GOpt_sepInLine_to_gstar hsep)
      omega
  · obtain ⟨m, _, hind⟩ := hlt
    have h1 := hb.length_lt
    have h2 := SIndent_length_le hind
    omega

lemma flowLinePrefix_toGStar {n : Nat} {s s' : SurfPos} (h : SFlowLinePrefix n s s') :
    GStar SSWhite s s' := by
  rcases h with ⟨_, _, hind, hsep⟩
  exact gstar_sswhite_append (sindent_to_gstar_sswhite hind) (GOpt_sepInLine_to_gstar hsep)

/-- One `SLEmptyOk n` blank line as `foldQuotedNewlinesLoop` reads it from the line start:
    `skipWhitespace` reaches the break, the §6.1 tab test is dead (`n` clears the floor or
    the run has no tab), `consumeNewline` lands on the next line. -/
lemma blankLine_accepts (sc : ScannerState) {n : Nat} {sp sp' : SurfPos}
    (h : SLEmptyOk n sp sp') (hcorr : ScannerSurfCorr sc sp)
    (hfloor : (n : Int) > sc.currentIndent) :
    ∃ c, (skipWhitespace sc).peek? = some c ∧ isLineBreakBool c = true ∧
      blankLineTabUnderFloor sc = false ∧
      ScannerSurfCorr (consumeNewline (skipWhitespace sc)) sp' ∧
      Keeps sc (consumeNewline (skipWhitespace sc)) := by
  have hks : Keeps sc (skipSpaces sc) := keeps_skipSpacesLoop _ sc
  rcases h with ⟨_, _, hopt, hb⟩ | ⟨_, _, hlt, hb⟩
  · rename_i s₁
    obtain ⟨c, rest, hs₁, hlb⟩ := hb.head
    obtain ⟨cs, col⟩ := s₁
    simp only at hs₁; subst hs₁
    have hsp : _ := lineBreak_ne_space hlb
    have htb : _ := lineBreak_ne_tab hlb
    have hw : GStar SSWhite sp ⟨c :: rest, col⟩ := by
      rcases hopt with _ | ⟨_, hp⟩
      · exact .nil _
      · exact flowLinePrefix_toGStar hp
    obtain ⟨h1, h2⟩ := skipWhitespace_accepts sc hw hcorr (by simpa using hsp) (by simpa using htb)
    have hpeek := (peek_of_corr h1).1
    obtain ⟨h3, h4⟩ := consumeNewline_accepts (skipWhitespace sc) hb h1
    refine ⟨c, hpeek, hlb, ?_, h3, h2.trans h4⟩
    rcases hopt with _ | ⟨_, hp⟩
    · -- no prefix: skipSpaces stays at the break
      have h5 := (skipSpaces_accepts sc (.zero _) hcorr (by simpa using hsp)).1
      have hpk := (peek_of_corr h5).1
      simp [blankLineTabUnderFloor, hpk, htb]
    · rcases hp with ⟨_, _, hind, hsep⟩
      have hfuel := fuel_of_corr hcorr
      obtain ⟨sp₁, h5, _, _, h8⟩ := skipSpacesLoop_prefix_accepts n sc sp _ _ (sc.inputEnd - sc.offset)
        hind (GOpt_sepInLine_to_gstar hsep) hcorr (by simpa using hsp) (by omega)
      have hcol : (skipSpaces sc).col = sp₁.col := h5.col_eq.symm
      have hgate : ¬ (((skipSpaces sc).col : Int) ≤ (skipSpaces sc).currentIndent) := by
        rw [hks.currentIndent, hcol]; omega
      simp [blankLineTabUnderFloor, hgate]
  · rename_i s₁
    obtain ⟨m, _, hind⟩ := hlt
    obtain ⟨c, rest, hs₁, hlb⟩ := hb.head
    obtain ⟨cs, col⟩ := s₁
    simp only at hs₁; subst hs₁
    have hsp : _ := lineBreak_ne_space hlb
    have htb : _ := lineBreak_ne_tab hlb
    obtain ⟨h1, h2⟩ := skipWhitespace_accepts sc (sindent_to_gstar_sswhite hind) hcorr
      (by simpa using hsp) (by simpa using htb)
    have hpeek := (peek_of_corr h1).1
    obtain ⟨h3, h4⟩ := consumeNewline_accepts (skipWhitespace sc) hb h1
    refine ⟨c, hpeek, hlb, ?_, h3, h2.trans h4⟩
    have h5 := (skipSpaces_accepts sc hind hcorr (by simpa using hsp)).1
    have hpk := (peek_of_corr h5).1
    simp [blankLineTabUnderFloor, hpk, htb]

lemma foldQuotedNewlinesLoop_accepts {n : Nat} {sp sp₂ : SurfPos}
    (hblank : GStar (SLEmptyOk n) sp sp₂) :
    ∀ (sc : ScannerState) (cnt fuel : Nat) (sp' : SurfPos),
      ScannerSurfCorr sc sp → (n : Int) > sc.currentIndent →
      SFlowLinePrefix n sp₂ sp' → sp'.chars.head? ≠ some ' ' → sp'.chars.head? ≠ some '\t' →
      (∀ c, sp'.chars.head? = some c → isLineBreakBool c = false) →
      sp.chars.length < fuel →
      ∃ sc₂ k, foldQuotedNewlinesLoop sc cnt fuel = (sc₂, cnt + k) ∧
        ScannerSurfCorr sc₂ sp₂ ∧ Keeps sc sc₂ := by
  induction hblank with
  | nil s =>
    intro sc cnt fuel sp' hcorr _ hpre hsp htab hnb hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      obtain ⟨h1, _⟩ := skipWhitespace_accepts sc (flowLinePrefix_toGStar hpre) hcorr hsp htab
      refine ⟨sc, 0, ?_, hcorr, Keeps.refl sc⟩
      obtain ⟨chars, col⟩ := sp'
      cases chars with
      | nil => simp only [foldQuotedNewlinesLoop, peek_none_of_corr h1, Nat.add_zero]
      | cons c tl =>
        have hpeek := (peek_of_corr h1).1
        have hc := hnb c rfl
        simp only [foldQuotedNewlinesLoop, hpeek, hc, Bool.false_eq_true, ite_false, Nat.add_zero]
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc cnt fuel sp' hcorr hfloor hpre hsp htab hnb hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      obtain ⟨c, hpeek, hlb, hbt, h1, h2⟩ := blankLine_accepts sc hstep hcorr hfloor
      have hlt := hstep.length_lt
      obtain ⟨sc₂, k, h3, h4, h5⟩ := ih _ (cnt + 1) f sp' h1 (by rw [h2.currentIndent]; exact hfloor)
        hpre hsp htab hnb (by omega)
      refine ⟨sc₂, k + 1, ?_, h4, h2.trans h5⟩
      simp only [foldQuotedNewlinesLoop, hpeek, hlb, hbt, Bool.false_eq_true, ite_false, ite_true, h3]
      congr 1; omega

/-- `foldQuotedNewlines` at a break: the break, the `SLEmptyOk n` blank lines, then the
    `[69] s-flow-line-prefix(n)` landing (maximal whites, no break next). -/
lemma foldQuotedNewlines_accepts (sc : ScannerState) {n : Nat} {sp sp₁ sp₂ sp' : SurfPos}
    (hb : SBBreakOk sp sp₁) (hblank : GStar (SLEmptyOk n) sp₁ sp₂) (hpre : SFlowLinePrefix n sp₂ sp')
    (hcorr : ScannerSurfCorr sc sp) (hfloor : (n : Int) > sc.currentIndent)
    (hsp : sp'.chars.head? ≠ some ' ') (htab : sp'.chars.head? ≠ some '\t')
    (hnb : ∀ c, sp'.chars.head? = some c → isLineBreakBool c = false) :
    ∃ folded s_land, foldQuotedNewlines sc = .ok (folded, s_land) ∧
      ScannerSurfCorr s_land sp' ∧ Keeps sc s_land := by
  obtain ⟨h1, k1⟩ := consumeNewline_accepts sc hb hcorr
  have hfuel := fuel_of_corr h1
  obtain ⟨sc₂, k, hloop, h2, k2⟩ := foldQuotedNewlinesLoop_accepts hblank (consumeNewline sc) 0
    (sc.inputEnd - (consumeNewline sc).offset + 1) sp' h1 (by rw [k1.currentIndent]; exact hfloor)
    hpre hsp htab hnb (by rw [← k1.2.1]; exact hfuel)
  obtain ⟨h3, hgate, k3⟩ := flowLinePrefix_accepts sc₂ hpre h2 hsp htab
    (by rw [(k1.trans k2).currentIndent]; exact hfloor)
  unfold foldQuotedNewlines
  simp only [hloop, hgate, ite_false, bind, Except.bind, pure, Except.pure]
  split <;> exact ⟨_, _, rfl, h3, k1.trans (k2.trans k3)⟩

/-! ## §13 Multi-line double-quoted content -/

lemma SBBreakOk.head' {s s' : SurfPos} (h : SBBreakOk s s') :
    ∃ c rest, s.chars = c :: rest ∧ (c = '\n' ∨ c = '\r') := by
  cases h with
  | lf rest col => exact ⟨'\n', rest, rfl, Or.inl rfl⟩
  | crLf rest col => exact ⟨'\r', '\n' :: rest, rfl, Or.inr rfl⟩
  | cr rest col _ => exact ⟨'\r', rest, rfl, Or.inr rfl⟩

lemma SIndent_col {n : Nat} {s s' : SurfPos} (h : SIndent n s s') : s'.col = s.col + n := by
  induction h with
  | zero => simp
  | succ n rest col s' _ ih => simp at ih ⊢; omega

lemma GStar_SSWhite_col {s s' : SurfPos} (h : GStar SSWhite s s') : s'.col ≥ s.col := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ _ _ h₁ _ ih => cases h₁ <;> simp at ih ⊢ <;> omega

lemma flowLinePrefix_col {n : Nat} {s s' : SurfPos} (h : SFlowLinePrefix n s s') : s'.col ≥ n := by
  rcases h with ⟨_, _, hind, hsep⟩
  have h1 := SIndent_col hind
  have h2 := GStar_SSWhite_col (GOpt_sepInLine_to_gstar hsep)
  omega

lemma GStar_SLEmptyOk_length {n : Nat} {s s' : SurfPos} (h : GStar (SLEmptyOk n) s s') :
    s'.chars.length ≤ s.chars.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ _ _ h₁ _ ih => have := h₁.length_lt; omega

lemma flowLinePrefix_length {n : Nat} {s s' : SurfPos} (h : SFlowLinePrefix n s s') :
    s'.chars.length ≤ s.chars.length :=
  GStar_SSWhite_length (flowLinePrefix_toGStar h)

/-- `[112] s-double-break(n)` as `foldQuotedNewlines` reads it: `SBBreakOk` breaks, `SLEmptyOk n`
    blank lines, and a landing that is maximal, not a break and not a document marker. The
    `escaped` arm starts at the `\`; the `s-white*` before it is ordinary `DQCharOk` content. -/
inductive DQBreakOk (n : Nat) : SurfPos → SurfPos → Prop where
  | flowFold (s s₁ s₂ s' : SurfPos) :
      SBBreakOk s s₁ → GStar (SLEmptyOk n) s₁ s₂ → SFlowLinePrefix n s₂ s' →
      s'.chars.head? ≠ some ' ' → s'.chars.head? ≠ some '\t' →
      (∀ c, s'.chars.head? = some c → isLineBreakBool c = false) → NotDocMarker s' →
      DQBreakOk n s s'
  | escaped (rest : List Char) (col : Nat) (s₁ s₂ s' : SurfPos) :
      SBBreakOk ⟨rest, col + 1⟩ s₁ → GStar (SLEmptyOk n) s₁ s₂ → SFlowLinePrefix n s₂ s' →
      s'.chars.head? ≠ some ' ' → s'.chars.head? ≠ some '\t' →
      (∀ c, s'.chars.head? = some c → isLineBreakBool c = false) → NotDocMarker s' →
      DQBreakOk n ⟨'\\' :: rest, col⟩ s'

lemma DQBreakOk.toSSDoubleBreak {n : Nat} {s s' : SurfPos} (h : DQBreakOk n s s') :
    SSDoubleBreak n s s' := by
  cases h
  · have hb := ‹SBBreakOk _ _›
    have hbl := ‹GStar (SLEmptyOk n) _ _›
    have hpre := ‹SFlowLinePrefix n _ _›
    have hsp := ‹s'.chars.head? ≠ some ' '›
    have htab := ‹s'.chars.head? ≠ some '	'›
    have hnb := ‹∀ c, s'.chars.head? = some c → isLineBreakBool c = false›
    have hdoc := ‹NotDocMarker s'›
    exact .flowFold n _ _ _ _ hb.toSBBreak (GStar_mono (fun _ _ => SLEmptyOk.toSLEmpty) hbl) hpre
  · have hb := ‹SBBreakOk _ _›
    have hbl := ‹GStar (SLEmptyOk n) _ _›
    have hpre := ‹SFlowLinePrefix n _ _›
    have hsp := ‹s'.chars.head? ≠ some ' '›
    have htab := ‹s'.chars.head? ≠ some '	'›
    have hnb := ‹∀ c, s'.chars.head? = some c → isLineBreakBool c = false›
    have hdoc := ‹NotDocMarker s'›
    exact .escaped n _ _ (.mk n _ _ _ _ _ _ (.nil _) (.mk _ _) hb.toSBBreak
      (GStar_mono (fun _ _ => SLEmptyOk.toSLEmpty) hbl) hpre)

lemma DQBreakOk.length_lt {n : Nat} {s s' : SurfPos} (h : DQBreakOk n s s') :
    s'.chars.length < s.chars.length := by
  cases h
  · have hb := ‹SBBreakOk _ _›
    have hbl := ‹GStar (SLEmptyOk n) _ _›
    have hpre := ‹SFlowLinePrefix n _ _›
    have hsp := ‹s'.chars.head? ≠ some ' '›
    have htab := ‹s'.chars.head? ≠ some '	'›
    have hnb := ‹∀ c, s'.chars.head? = some c → isLineBreakBool c = false›
    have hdoc := ‹NotDocMarker s'›
    have := hb.length_lt; have := GStar_SLEmptyOk_length hbl; have := flowLinePrefix_length hpre
    omega
  · have hb := ‹SBBreakOk _ _›
    have hbl := ‹GStar (SLEmptyOk n) _ _›
    have hpre := ‹SFlowLinePrefix n _ _›
    have hsp := ‹s'.chars.head? ≠ some ' '›
    have htab := ‹s'.chars.head? ≠ some '	'›
    have hnb := ‹∀ c, s'.chars.head? = some c → isLineBreakBool c = false›
    have hdoc := ‹NotDocMarker s'›
    have h1 := hb.length_lt; have := GStar_SLEmptyOk_length hbl; have := flowLinePrefix_length hpre
    simp at h1 ⊢; omega

-- `hlb`/`ite_true` are needed in one of the two `rcases` branches only.
set_option linter.unusedSimpArgs false in
/-- The fold arm of `collectDoubleQuotedLoop` (plain or escaped break): one fuel unit, lands
    at `sp'` with the document-marker and indentation checks passed. -/
lemma collectDoubleQuotedLoop_break_step (sc : ScannerState) {n : Nat} {sp sp' : SurfPos} {ind : Int}
    (hbr : DQBreakOk n sp sp') (hcorr : ScannerSurfCorr sc sp)
    (hfloor : (n : Int) > ind) (hind : sc.currentIndent = ind)
    (content : String) (fuel' : Nat) (startPos : YamlPos) (inFlow : Bool) (iend pl : Nat) :
    ∃ content' sc' pl',
      collectDoubleQuotedLoop sc content (fuel' + 1) startPos inFlow ind iend pl =
        collectDoubleQuotedLoop sc' content' fuel' startPos inFlow ind iend pl' ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  cases hbr
  · have hb := ‹SBBreakOk _ _›
    have hbl := ‹GStar (SLEmptyOk n) _ _›
    have hpre := ‹SFlowLinePrefix n _ _›
    have hsp := ‹sp'.chars.head? ≠ some ' '›
    have htab := ‹sp'.chars.head? ≠ some '	'›
    have hnb := ‹∀ c, sp'.chars.head? = some c → isLineBreakBool c = false›
    have hdoc := ‹NotDocMarker sp'›
    obtain ⟨c, rest, hs, hc⟩ := hb.head'
    obtain ⟨cs, col⟩ := sp
    simp only at hs; subst hs
    have hlb : isLineBreakBool c = true := by rcases hc with rfl | rfl <;> rfl
    obtain ⟨folded, s_land, hfold, hland, hk⟩ :=
      foldQuotedNewlines_accepts sc hb hbl hpre hcorr (by rw [hind]; exact hfloor) hsp htab hnb
    have hds := atDocumentStart_false_of_corr hland hdoc
    have hde := atDocumentEnd_false_of_corr hland hdoc
    have hcol : ¬ ((s_land.col : Int) ≤ ind) := by
      have := flowLinePrefix_col hpre
      have := hland.col_eq
      omega
    have hpeek := (peek_of_corr hcorr).1
    rcases hc with rfl | rfl <;>
    · simp only [collectDoubleQuotedLoop, hpeek, hlb, hfold, hds, hde, hcol, Bool.or_false,
        Bool.false_eq_true, ite_false, ite_true, bind, Except.bind]
      exact ⟨_, _, _, rfl, hland, hk⟩
  · have hb := ‹SBBreakOk _ _›
    have hbl := ‹GStar (SLEmptyOk n) _ _›
    have hpre := ‹SFlowLinePrefix n _ _›
    have hsp := ‹sp'.chars.head? ≠ some ' '›
    have htab := ‹sp'.chars.head? ≠ some '	'›
    have hnb := ‹∀ c, sp'.chars.head? = some c → isLineBreakBool c = false›
    have hdoc := ‹NotDocMarker sp'›
    have hpeek := (peek_of_corr hcorr).1
    have hadv := advance_corr hcorr (by decide) (by decide)
    obtain ⟨c, rest', hs, hc⟩ := hb.head'
    simp only at hs; subst hs
    have hlb : isLineBreakBool c = true := by rcases hc with rfl | rfl <;> rfl
    have hpeek2 := (peek_of_corr hadv).1
    obtain ⟨folded, s_land, hfold, hland, hk⟩ :=
      foldQuotedNewlines_accepts sc.advance hb hbl hpre hadv
        (by rw [(keeps_advance sc).currentIndent, hind]; exact hfloor) hsp htab hnb
    have hds := atDocumentStart_false_of_corr hland hdoc
    have hde := atDocumentEnd_false_of_corr hland hdoc
    have hcol : ¬ ((s_land.col : Int) ≤ ind) := by
      have := flowLinePrefix_col hpre
      have := hland.col_eq
      omega
    rcases hc with rfl | rfl <;>
    · simp only [collectDoubleQuotedLoop, hpeek, hpeek2, hlb, hfold, hds, hde, hcol, Bool.or_false,
        Bool.false_eq_true, ite_false, ite_true, bind, Except.bind]
      exact ⟨_, _, _, rfl, hland, (keeps_advance sc).trans hk⟩

lemma collectDoubleQuotedLoop_chars {sp sp₁ : SurfPos} (h : GStar DQCharOk sp sp₁) :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
      (ind : Int) (iend pl : Nat), ScannerSurfCorr sc sp → sp.chars.length < fuel →
      ∃ sc₁ content₁ fuel₁ pl₁,
        collectDoubleQuotedLoop sc content fuel startPos inFlow ind iend pl =
          collectDoubleQuotedLoop sc₁ content₁ fuel₁ startPos inFlow ind iend pl₁ ∧
        ScannerSurfCorr sc₁ sp₁ ∧ Keeps sc sc₁ ∧ sp₁.chars.length < fuel₁ := by
  induction h with
  | nil s =>
    intro sc content fuel startPos inFlow ind iend pl hcorr hfuel
    exact ⟨sc, content, fuel, pl, rfl, hcorr, Keeps.refl sc, hfuel⟩
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content fuel startPos inFlow ind iend pl hcorr hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      obtain ⟨ch, sc', pl', heq, hcorr', hk⟩ :=
        collectDoubleQuotedLoop_step sc hstep hcorr content fuel' startPos inFlow ind iend pl
      have hlt := hstep.length_lt
      obtain ⟨sc₁, content₁, fuel₁, pl₁, heq', hc₁, hk', hf₁⟩ :=
        ih sc' (content.push ch) fuel' startPos inFlow ind iend pl' hcorr' (by omega)
      exact ⟨sc₁, content₁, fuel₁, pl₁, heq.trans heq', hc₁, hk.trans hk', hf₁⟩

/-- `[111] nb-double-multi-line(n)` with `DQCharOk` chars and `DQBreakOk n` folds. -/
inductive DQTextOk (n : Nat) : SurfPos → SurfPos → Prop where
  | single (s s' : SurfPos) : GStar DQCharOk s s' → DQTextOk n s s'
  | multi (s s₁ s₂ s' : SurfPos) :
      GStar DQCharOk s s₁ → DQBreakOk n s₁ s₂ → DQTextOk n s₂ s' → DQTextOk n s s'

lemma DQTextOk.toSNbDoubleMultiLine {n : Nat} {s s' : SurfPos} (h : DQTextOk n s s') :
    SNbDoubleMultiLine n s s' := by
  induction h with
  | single s s' h1 => exact .single n s s' (GStar_mono (fun _ _ => DQCharOk.toSNbDoubleChar) h1)
  | multi s s₁ s₂ s' h1 hbr _ ih =>
    exact .multi n s s₁ s₂ s₁ s' (GStar_mono (fun _ _ => DQCharOk.toSNbDoubleChar) h1)
      hbr.toSSDoubleBreak ih

lemma collectDoubleQuotedLoop_accepts_multi {n : Nat} {sp sp' : SurfPos} (hder : DQTextOk n sp sp') :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
      (ind : Int) (iend pl : Nat) (rest : List Char),
      ScannerSurfCorr sc sp → sp.chars.length < fuel → sp'.chars = '"' :: rest →
      (n : Int) > ind → sc.currentIndent = ind →
      ∃ content' sc',
        collectDoubleQuotedLoop sc content fuel startPos inFlow ind iend pl = .ok (content', sc') ∧
        ScannerSurfCorr sc' ⟨rest, sp'.col + 1⟩ ∧ Keeps sc sc' := by
  induction hder with
  | single s s' h1 =>
    intro sc content fuel startPos inFlow ind iend pl rest hcorr hfuel hend _ _
    exact collectDoubleQuotedLoop_accepts h1 sc content fuel startPos inFlow ind iend pl rest hcorr hfuel hend
  | multi s s₁ s₂ s' h1 hbr _ ih =>
    intro sc content fuel startPos inFlow ind iend pl rest hcorr hfuel hend hfloor hind
    obtain ⟨sc₁, content₁, fuel₁, pl₁, heq, hc₁, hk₁, hf₁⟩ :=
      collectDoubleQuotedLoop_chars h1 sc content fuel startPos inFlow ind iend pl hcorr hfuel
    cases fuel₁ with
    | zero => simp at hf₁
    | succ f =>
      obtain ⟨content₂, sc₂, pl₂, heq₂, hc₂, hk₂⟩ :=
        collectDoubleQuotedLoop_break_step sc₁ hbr hc₁ hfloor (by rw [hk₁.currentIndent]; exact hind)
          content₁ f startPos inFlow iend pl₁
      have hlt := hbr.length_lt
      obtain ⟨content', sc', hok, hc', hk'⟩ := ih sc₂ content₂ f startPos inFlow ind iend pl₂ rest hc₂
        (by omega) hend hfloor (by rw [(hk₁.trans hk₂).currentIndent]; exact hind)
      exact ⟨content', sc', heq.trans (heq₂.trans hok), hc', hk₁.trans (hk₂.trans hk')⟩

/-- `[109] c-double-quoted(n,c)` with multi-line `DQTextOk n` content. -/
inductive SCDoubleQuotedMultiOk (n : Nat) : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s' : SurfPos) :
      GLit '"' s s₁ → DQTextOk n s₁ s₂ → GLit '"' s₂ s' → SCDoubleQuotedMultiOk n s s'

lemma SCDoubleQuotedMultiOk.toSCDoubleQuoted (n : Nat) (c : L4YAML.YamlContext)
    (hc : c = .flowOut ∨ c = .flowIn) {s s' : SurfPos}
    (h : SCDoubleQuotedMultiOk n s s') : SCDoubleQuoted n c s s' := by
  rcases h with ⟨_, _, _, h1, htext, h2⟩
  rcases hc with rfl | rfl <;> exact .mk n _ _ _ _ _ h1 htext.toSNbDoubleMultiLine h2

/-- Multi-line double-quoted converse: `n` must clear the scanner's indentation floor. -/
lemma scanDoubleQuoted_accepts_multi (sc : ScannerState) {n : Nat} {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : SCDoubleQuotedMultiOk n sp sp')
    (hfloor : (n : Int) > sc.currentIndent)
    (htrail : sc.inFlow = true ∨ TrailingOk sp'.chars) :
    ∃ s' content, scanDoubleQuoted sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .doubleQuoted } := by
  rcases hder with ⟨_, _, _, h1, htext, h2⟩
  cases h1 with | mk rest₁ col =>
  cases h2 with | mk rest col₂ =>
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (by decide) (by decide)
  have hfuel := fuel_of_corr hadv
  simp only at hfuel
  rw [(keeps_advance sc).2.1] at hfuel
  obtain ⟨content, sc₂, hloop, hc₂, hk⟩ := collectDoubleQuotedLoop_accepts_multi htext sc.advance ""
    _ sc.currentPos sc.inFlow sc.currentIndent sc.inputEnd 0 rest hadv hfuel rfl hfloor
    (keeps_advance sc).currentIndent
  simp only at hc₂ htrail
  have hk' := (keeps_advance sc).trans hk
  refine ⟨{ sc₂.emitAt sc.currentPos (.scalar content .doubleQuoted) with
      simpleKeyAllowed := false, needIndentCheck := false }, content, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc₂), ?_⟩
  · unfold scanDoubleQuoted
    simp only [hloop, bind, Except.bind]
    rcases htrail with hf | ht
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false]
    · have hv := validateTrailingContent_accepts sc₂ rest (col₂ + 1) hc₂ ht
      rw [hk'.2.1] at hv
      cases hf : sc.inFlow
      · simp only [Bool.not_false, ite_true, hv]
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  · simp [ScannerState.emitAt, hk'.1]

/-! ## §14 Multi-line single-quoted content -/

/-- The fold of `[123] nb-single-multi-line(n)` as `foldQuotedNewlines` reads it (no escaped
    arm: `\` is an ordinary char in single quotes). -/
inductive SQBreakOk (n : Nat) : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s' : SurfPos) :
      SBBreakOk s s₁ → GStar (SLEmptyOk n) s₁ s₂ → SFlowLinePrefix n s₂ s' →
      s'.chars.head? ≠ some ' ' → s'.chars.head? ≠ some '\t' →
      (∀ c, s'.chars.head? = some c → isLineBreakBool c = false) → NotDocMarker s' →
      SQBreakOk n s s'

lemma SQBreakOk.length_lt {n : Nat} {s s' : SurfPos} (h : SQBreakOk n s s') :
    s'.chars.length < s.chars.length := by
  cases h
  have hb := ‹SBBreakOk _ _›
  have hbl := ‹GStar (SLEmptyOk n) _ _›
  have hpre := ‹SFlowLinePrefix n _ _›
  have := hb.length_lt; have := GStar_SLEmptyOk_length hbl; have := flowLinePrefix_length hpre
  omega

set_option linter.unusedSimpArgs false in
lemma collectSingleQuotedLoop_break_step (sc : ScannerState) {n : Nat} {sp sp' : SurfPos} {ind : Int}
    (hbr : SQBreakOk n sp sp') (hcorr : ScannerSurfCorr sc sp)
    (hfloor : (n : Int) > ind) (hind : sc.currentIndent = ind)
    (content : String) (fuel' : Nat) (startPos : YamlPos) (inFlow : Bool) (iend : Nat) :
    ∃ content' sc',
      collectSingleQuotedLoop sc content (fuel' + 1) startPos inFlow ind iend =
        collectSingleQuotedLoop sc' content' fuel' startPos inFlow ind iend ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  cases hbr
  have hb := ‹SBBreakOk _ _›
  have hbl := ‹GStar (SLEmptyOk n) _ _›
  have hpre := ‹SFlowLinePrefix n _ _›
  have hsp := ‹sp'.chars.head? ≠ some ' '›
  have htab := ‹sp'.chars.head? ≠ some '\t'›
  have hnb := ‹∀ c, sp'.chars.head? = some c → isLineBreakBool c = false›
  have hdoc := ‹NotDocMarker sp'›
  obtain ⟨c, rest, hs, hc⟩ := hb.head'
  obtain ⟨cs, col⟩ := sp
  simp only at hs; subst hs
  have hlb : isLineBreakBool c = true := by rcases hc with rfl | rfl <;> rfl
  obtain ⟨folded, s_land, hfold, hland, hk⟩ :=
    foldQuotedNewlines_accepts sc hb hbl hpre hcorr (by rw [hind]; exact hfloor) hsp htab hnb
  have hds := atDocumentStart_false_of_corr hland hdoc
  have hde := atDocumentEnd_false_of_corr hland hdoc
  have hcol : ¬ ((s_land.col : Int) ≤ ind) := by
    have := flowLinePrefix_col hpre
    have := hland.col_eq
    omega
  have hpeek := (peek_of_corr hcorr).1
  rcases hc with rfl | rfl <;>
  · simp only [collectSingleQuotedLoop, hpeek, hlb, hfold, hds, hde, hcol, Bool.or_false,
      Bool.false_eq_true, ite_false, ite_true, bind, Except.bind]
    exact ⟨_, _, rfl, hland, hk⟩

lemma collectSingleQuotedLoop_chars {sp sp₁ : SurfPos} (h : GStar SQCharOk sp sp₁) :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
      (ind : Int) (iend : Nat), ScannerSurfCorr sc sp → sp.chars.length < fuel →
      ∃ sc₁ content₁ fuel₁,
        collectSingleQuotedLoop sc content fuel startPos inFlow ind iend =
          collectSingleQuotedLoop sc₁ content₁ fuel₁ startPos inFlow ind iend ∧
        ScannerSurfCorr sc₁ sp₁ ∧ Keeps sc sc₁ ∧ sp₁.chars.length < fuel₁ := by
  induction h with
  | nil s =>
    intro sc content fuel startPos inFlow ind iend hcorr hfuel
    exact ⟨sc, content, fuel, rfl, hcorr, Keeps.refl sc, hfuel⟩
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content fuel startPos inFlow ind iend hcorr hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      obtain ⟨ch, sc', heq, hcorr', hk⟩ :=
        collectSingleQuotedLoop_step sc hstep hcorr content fuel' startPos inFlow ind iend
      have hlt := hstep.length_lt
      obtain ⟨sc₁, content₁, fuel₁, heq', hc₁, hk', hf₁⟩ :=
        ih sc' (content.push ch) fuel' startPos inFlow ind iend hcorr' (by omega)
      exact ⟨sc₁, content₁, fuel₁, heq.trans heq', hc₁, hk.trans hk', hf₁⟩

/-- `[123] nb-single-multi-line(n)` with `SQCharOk` chars and `SQBreakOk n` folds. -/
inductive SQTextOk (n : Nat) : SurfPos → SurfPos → Prop where
  | single (s s' : SurfPos) : GStar SQCharOk s s' → SQTextOk n s s'
  | multi (s s₁ s₂ s' : SurfPos) :
      GStar SQCharOk s s₁ → SQBreakOk n s₁ s₂ → SQTextOk n s₂ s' → SQTextOk n s s'

lemma SQTextOk.toSNbSingleMultiLine {n : Nat} {s s' : SurfPos} (h : SQTextOk n s s') :
    SNbSingleMultiLine n s s' := by
  induction h with
  | single s s' h1 => exact .single n s s' (GStar_mono (fun _ _ => SQCharOk.toSNbSingleChar) h1)
  | multi s s₁ s₂ s' h1 hbr _ ih =>
    cases hbr
    have hb := ‹SBBreakOk _ _›
    have hbl := ‹GStar (SLEmptyOk n) _ _›
    have hpre := ‹SFlowLinePrefix n _ _›
    exact .multi n s s₁ _ _ _ s' (GStar_mono (fun _ _ => SQCharOk.toSNbSingleChar) h1)
      hb.toSBBreak (GStar_mono (fun _ _ => SLEmptyOk.toSLEmpty) hbl) hpre ih

lemma collectSingleQuotedLoop_accepts_multi {n : Nat} {sp sp' : SurfPos} (hder : SQTextOk n sp sp') :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
      (ind : Int) (iend : Nat) (rest : List Char),
      ScannerSurfCorr sc sp → sp.chars.length < fuel → sp'.chars = '\'' :: rest →
      rest.head? ≠ some '\'' → (n : Int) > ind → sc.currentIndent = ind →
      ∃ content' sc',
        collectSingleQuotedLoop sc content fuel startPos inFlow ind iend = .ok (content', sc') ∧
        ScannerSurfCorr sc' ⟨rest, sp'.col + 1⟩ ∧ Keeps sc sc' := by
  induction hder with
  | single s s' h1 =>
    intro sc content fuel startPos inFlow ind iend rest hcorr hfuel hend hq _ _
    exact collectSingleQuotedLoop_accepts h1 sc content fuel startPos inFlow ind iend rest hcorr hfuel hend hq
  | multi s s₁ s₂ s' h1 hbr _ ih =>
    intro sc content fuel startPos inFlow ind iend rest hcorr hfuel hend hq hfloor hind
    obtain ⟨sc₁, content₁, fuel₁, heq, hc₁, hk₁, hf₁⟩ :=
      collectSingleQuotedLoop_chars h1 sc content fuel startPos inFlow ind iend hcorr hfuel
    cases fuel₁ with
    | zero => simp at hf₁
    | succ f =>
      obtain ⟨content₂, sc₂, heq₂, hc₂, hk₂⟩ :=
        collectSingleQuotedLoop_break_step sc₁ hbr hc₁ hfloor (by rw [hk₁.currentIndent]; exact hind)
          content₁ f startPos inFlow iend
      have hlt := hbr.length_lt
      obtain ⟨content', sc', hok, hc', hk'⟩ := ih sc₂ content₂ f startPos inFlow ind iend rest hc₂
        (by omega) hend hq hfloor (by rw [(hk₁.trans hk₂).currentIndent]; exact hind)
      exact ⟨content', sc', heq.trans (heq₂.trans hok), hc', hk₁.trans (hk₂.trans hk')⟩

/-- `[120] c-single-quoted(n,c)` with multi-line `SQTextOk n` content. -/
inductive SCSingleQuotedMultiOk (n : Nat) : SurfPos → SurfPos → Prop where
  | mk (s s₁ s₂ s' : SurfPos) :
      GLit '\'' s s₁ → SQTextOk n s₁ s₂ → GLit '\'' s₂ s' → SCSingleQuotedMultiOk n s s'

lemma SCSingleQuotedMultiOk.toSCSingleQuoted (n : Nat) (c : L4YAML.YamlContext)
    (hc : c = .flowOut ∨ c = .flowIn) {s s' : SurfPos}
    (h : SCSingleQuotedMultiOk n s s') : SCSingleQuoted n c s s' := by
  rcases h with ⟨_, _, _, h1, htext, h2⟩
  rcases hc with rfl | rfl <;> exact .mk n _ _ _ _ _ h1 htext.toSNbSingleMultiLine h2

/-- Multi-line single-quoted converse: `n` must clear the scanner's indentation floor. -/
lemma scanSingleQuoted_accepts_multi (sc : ScannerState) {n : Nat} {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : SCSingleQuotedMultiOk n sp sp')
    (hq : sp'.chars.head? ≠ some '\'')
    (hfloor : (n : Int) > sc.currentIndent)
    (htrail : sc.inFlow = true ∨ TrailingOk sp'.chars) :
    ∃ s' content, scanSingleQuoted sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .singleQuoted } := by
  rcases hder with ⟨_, _, _, h1, htext, h2⟩
  cases h1 with | mk rest₁ col =>
  cases h2 with | mk rest col₂ =>
  have hpeek := (peek_of_corr hcorr).1
  have hadv := advance_corr hcorr (by decide) (by decide)
  have hfuel := fuel_of_corr hadv
  simp only at hfuel hq htrail
  rw [(keeps_advance sc).2.1] at hfuel
  obtain ⟨content, sc₂, hloop, hc₂, hk⟩ := collectSingleQuotedLoop_accepts_multi htext sc.advance ""
    _ sc.currentPos sc.inFlow sc.currentIndent sc.inputEnd rest hadv hfuel rfl hq hfloor
    (keeps_advance sc).currentIndent
  simp only at hc₂
  have hk' := (keeps_advance sc).trans hk
  refine ⟨{ sc₂.emitAt sc.currentPos (.scalar content .singleQuoted) with
      simpleKeyAllowed := false, needIndentCheck := false }, content, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc₂), ?_⟩
  · unfold scanSingleQuoted
    simp only [hloop, bind, Except.bind]
    rcases htrail with hf | ht
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false]
    · have hv := validateTrailingContent_accepts sc₂ rest (col₂ + 1) hc₂ ht
      rw [hk'.2.1] at hv
      cases hf : sc.inFlow
      · simp only [Bool.not_false, ite_true, hv]
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  · simp [ScannerState.emitAt, hk'.1]

end L4YAML.Proofs.Acceptance
