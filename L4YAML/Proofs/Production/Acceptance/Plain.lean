/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.Acceptance.Quoted
public import L4YAML.Proofs.Scanner.ScannerPlainContent

@[expose] public section Blanket

/-!
# Acceptance — plain scalars, one line (Stream E)

Scanner converses of `scanPlainScalar_prod`: a narrowed `[133] ns-plain-one-line`
derivation at the scanner's position makes `scanPlainScalar` succeed and land at the
end of the derivation's trailing white run, emitting the trimmed `.plain` token.

The unnarrowed converse is false (probes in `Tests/Guards/Proofs/AcceptanceProbes.lean`):
* `a #b` — the scanner reads ` #` as a comment and stops at `a`; `[132]`'s `hash`
  entry agrees (`#` is content only with an EMPTY `s-white*`), and `PlainCharOk.hash`
  is likewise admitted only with no pending white.
* `--- x` / `---` — `[126]`'s `dashSafe` derives `---` at column 0; the scanner sees a
  document marker and emits an empty scalar without moving (→ `hdoc`).
* `a  ` — `[133]` ends at `a`; the scanner buffers the trailing whites and lands after
  them (→ the landing is `sp''`, the end of the `GStar SSWhite` run).
-/

namespace L4YAML.Proofs.Acceptance

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Grammar

/-- One plain content char the scanner keeps: `isPlainSafeBool` (printable, no BOM, in
    flow no indicator); `:` only before another safe char; `#` only with no white before
    it (`[132]`'s `hash` entry; ` #` is a comment for both). -/
inductive PlainCharOk (inFlow : Bool) : (afterWhite : Bool) → SurfPos → SurfPos → Prop where
  | safe (aw : Bool) (ch : Char) (rest : List Char) (col : Nat)
      (hSafe : isPlainSafeBool ch inFlow = true) (hNotColon : ch ≠ ':') (hNotHash : ch ≠ '#') :
      PlainCharOk inFlow aw ⟨ch :: rest, col⟩ ⟨rest, col + 1⟩
  | colonSafe (aw : Bool) (next : Char) (rest : List Char) (col : Nat)
      (hSafe : isPlainSafeBool next inFlow = true) :
      PlainCharOk inFlow aw ⟨':' :: next :: rest, col⟩ ⟨next :: rest, col + 1⟩
  | hash (rest : List Char) (col : Nat) (hColGt : col > 0) :
      PlainCharOk inFlow false ⟨'#' :: rest, col⟩ ⟨rest, col + 1⟩

/-- `[132]` entry: a white run then a char; `#` is admitted only when the run is empty. -/
inductive PlainEntryOk (inFlow : Bool) : SurfPos → SurfPos → Prop where
  | noWhite (s s' : SurfPos) : PlainCharOk inFlow false s s' → PlainEntryOk inFlow s s'
  | white (s s₁ s' : SurfPos) : GPlus SSWhite s s₁ → PlainCharOk inFlow true s₁ s' →
      PlainEntryOk inFlow s s'

/-- `[126]` narrowed to the scanner's Boolean predicates (`canStartPlainScalarBool`). -/
inductive PlainFirstOk (inFlow : Bool) : SurfPos → SurfPos → Prop where
  | nonIndicator (ch : Char) (rest : List Char) (col : Nat)
      (hSafe : isPlainSafeBool ch inFlow = true) (hInd : isIndicatorBool ch = false) :
      PlainFirstOk inFlow ⟨ch :: rest, col⟩ ⟨rest, col + 1⟩
  | indicator (ch next : Char) (rest : List Char) (col : Nat)
      (hInd : ch = '-' ∨ ch = '?' ∨ ch = ':') (hSafe : isPlainSafeBool next inFlow = true) :
      PlainFirstOk inFlow ⟨ch :: next :: rest, col⟩ ⟨next :: rest, col + 1⟩

lemma PlainFirstOk.toSNsPlainFirst {inFlow : Bool} {s s' : SurfPos}
    (h : PlainFirstOk inFlow s s') : SNsPlainFirst (ctxOfInFlow inFlow) s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hInd =>
    exact SNsPlainFirst.nonIndicator _ ch rest col (isPlainSafe_to_nsPlainSafe hSafe)
      (fun hi => by rw [← isIndicator_iff] at hi; simp_all)
  | indicator ch next rest col hInd hSafe =>
    rcases hInd with rfl | rfl | rfl
    · exact SNsPlainFirst.dashSafe _ next rest col (isPlainSafe_to_nsPlainSafe hSafe)
    · exact SNsPlainFirst.questionSafe _ next rest col (isPlainSafe_to_nsPlainSafe hSafe)
    · exact SNsPlainFirst.colonSafe _ next rest col (isPlainSafe_to_nsPlainSafe hSafe)

/-- `[133]` narrowed: the scanner's `canStartPlainScalarBool` first char, then entries. -/
inductive PlainOneLineOk (inFlow : Bool) : SurfPos → SurfPos → Prop where
  | mk (s s₁ s' : SurfPos) : PlainFirstOk inFlow s s₁ →
      GStar (PlainEntryOk inFlow) s₁ s' → PlainOneLineOk inFlow s s'

/-- What the scanner must see after the derivation's maximal trailing whites to stop
    there on the same line: EOF, a comment `#` (after at least one white), `:` before a
    blank / EOF / (flow) indicator, a flow indicator in flow, or any plain-unsafe char.
    Line breaks are not stops here: continuation is the multi-line relation's business. -/
def PlainStopOk (inFlow : Bool) (hadWhite : Bool) (chars : List Char) : Prop :=
  match chars with
  | [] => True
  | c :: rest =>
      (c = '#' ∧ hadWhite = true) ∨
      (c = ':' ∧ (match rest.head? with
        | none => True
        | some n => isBlankBool n = true ∨ (inFlow = true ∧ isFlowIndicatorBool n = true))) ∨
      (inFlow = true ∧ isFlowIndicatorBool c = true) ∨
      (isPlainSafeBool c inFlow = false ∧ isWhiteSpaceBool c = false ∧ isLineBreakBool c = false)

/-- A `PlainCharOk` that is not `#` is a `[130]` char (`#` is `[132]`'s `hash` entry). -/
lemma PlainCharOk.toSNsPlainChar {inFlow aw : Bool} {s s' : SurfPos}
    (h : PlainCharOk inFlow aw s s') (hhash : s.chars.head? ≠ some '#') :
    SNsPlainChar (ctxOfInFlow inFlow) s s' := by
  cases h with
  | safe aw ch rest col hSafe hc hh => exact isPlainSafe_to_plainChar_basic ch rest col inFlow hSafe hc hh
  | colonSafe aw next rest col hSafe =>
    exact SNsPlainChar.colonSafe _ ':' next rest col (isPlainSafe_to_nsPlainSafe hSafe)
  | hash rest col hcol => exact absurd rfl hhash

/-- After pending whites `PlainCharOk` never admits `#`, so it is a `[130]` char. -/
lemma PlainCharOk.toSNsPlainChar_afterWhite {inFlow aw : Bool} {s s' : SurfPos}
    (h : PlainCharOk inFlow aw s s') (haw : aw = true) :
    SNsPlainChar (ctxOfInFlow inFlow) s s' := by
  cases h with
  | safe aw ch rest col hSafe hc hh => exact isPlainSafe_to_plainChar_basic ch rest col inFlow hSafe hc hh
  | colonSafe aw next rest col hSafe =>
    exact SNsPlainChar.colonSafe _ ':' next rest col (isPlainSafe_to_nsPlainSafe hSafe)
  | hash rest col _ => exact Bool.noConfusion haw

/-- A `PlainCharOk` with no pending white is a `[132]` entry with an empty `s-white*`:
    a `[130]` char, or the `hash` entry. -/
lemma PlainCharOk.toEntry_noWhite {inFlow aw : Bool} {s s' : SurfPos}
    (h : PlainCharOk inFlow aw s s') : SNbNsPlainInLineEntry (ctxOfInFlow inFlow) s s' := by
  cases h with
  | safe aw ch rest col hSafe hc hh =>
    exact SNbNsPlainInLineEntry.mk _ _ _ _ (GStar.nil _)
      (isPlainSafe_to_plainChar_basic ch rest col inFlow hSafe hc hh)
  | colonSafe aw next rest col hSafe =>
    exact SNbNsPlainInLineEntry.mk _ _ _ _ (GStar.nil _)
      (SNsPlainChar.colonSafe _ ':' next rest col (isPlainSafe_to_nsPlainSafe hSafe))
  | hash rest col _ => exact SNbNsPlainInLineEntry.hash _ _ _ (GLit.mk rest col)

lemma GPlus.toGStar {P : SurfPos → SurfPos → Prop} {s s' : SurfPos}
    (h : GPlus P s s') : GStar P s s' :=
  match s, s', h with
  | _, _, .mk s₁ s₂ s₃ h₁ hs => GStar.cons s₁ s₂ s₃ h₁ hs

lemma GStar.imp' {P Q : SurfPos → SurfPos → Prop} (f : ∀ a b, P a b → Q a b) :
    ∀ {s s' : SurfPos}, GStar P s s' → GStar Q s s'
  | _, _, .nil s => .nil s
  | _, _, .cons s₁ s₂ s₃ h hs => .cons s₁ s₂ s₃ (f _ _ h) (GStar.imp' f hs)

lemma PlainEntryOk.toEntry {inFlow : Bool} {s s' : SurfPos}
    (h : PlainEntryOk inFlow s s') : SNbNsPlainInLineEntry (ctxOfInFlow inFlow) s s' :=
  match s, s', h with
  | _, _, .noWhite _ _ hc => hc.toEntry_noWhite
  | _, _, .white s s₁ s' hw hc =>
    SNbNsPlainInLineEntry.mk _ s s₁ s' (GPlus.toGStar hw) (hc.toSNsPlainChar_afterWhite rfl)

lemma PlainOneLineOk.toSNsPlainOneLine {inFlow : Bool} {s s' : SurfPos}
    (h : PlainOneLineOk inFlow s s') : SNsPlainOneLine (ctxOfInFlow inFlow) s s' :=
  match s, s', h with
  | _, _, .mk s s₁ s' hf hstar =>
    SNsPlainOneLine.mk _ s s₁ s' hf.toSNsPlainFirst (GStar.imp' (fun _ _ he => he.toEntry) hstar)

/-- `collectPlainScalar_terminates?` either falls through or stops where it stands. -/
lemma terminates_none_or_stop (c : Char) (sc : ScannerState) (content spaces : String)
    (inFlow : Bool) :
    collectPlainScalar_terminates? c sc content spaces inFlow = none ∨
    collectPlainScalar_terminates? c sc content spaces inFlow =
      some { content, spaces, state := sc, terminated := true } := by
  unfold collectPlainScalar_terminates?
  repeat' split
  all_goals simp

lemma flowIndicator_not_plain {c : Char} (h : isFlowIndicatorBool c = true) :
    isLineBreakBool c = false ∧ isWhiteSpaceBool c = false ∧ isPlainSafeBool c true = false := by
  simp only [isFlowIndicatorBool, decide_eq_true_eq, List.mem_cons,
    List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- At a `PlainStopOk` position the loop stops where it stands (`terminated := true`). -/
lemma collectPlainScalarLoop_stops (sc : ScannerState) {sp : SurfPos} {hadWhite : Bool}
    (content spaces : String) (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat)
    (hcorr : ScannerSurfCorr sc sp)
    (hstop : PlainStopOk inFlow hadWhite sp.chars)
    (hsp : hadWhite = true → spaces.length > 0) :
    collectPlainScalarLoop sc content spaces (fuel + 1) inFlow contentIndent inputEnd =
      .ok { content, spaces, state := sc, terminated := true } := by
  obtain ⟨chars, col⟩ := sp
  cases chars with
  | nil =>
    have hp := peek_none_of_corr hcorr
    simp [collectPlainScalarLoop, hp]
  | cons c rest =>
    have ⟨hp, _⟩ := peek_of_corr hcorr
    simp only [PlainStopOk] at hstop
    rw [collectPlainScalarLoop]
    simp only [hp]
    rcases hstop with ⟨rfl, hw⟩ | ⟨rfl, hnext⟩ | ⟨hf, hind⟩ | ⟨hunsafe, hnw, hnb⟩
    · have hl := hsp hw
      simp [collectPlainScalar_terminates?, hl]
    · have hadv := advance_corr hcorr (by decide) (by decide)
      have hpk : sc.peekAt? 1 = rest.head? := by
        rw [← L4YAML.Proofs.ScannerPlainContent.advance_peek_eq_peekAt_one sc ':' hp]
        cases rest with
        | nil => exact peek_none_of_corr hadv
        | cons n r => exact (peek_of_corr hadv).1
      cases rest with
      | nil => simp [collectPlainScalar_terminates?, hpk]
      | cons n r =>
        simp only [List.head?] at hnext hpk
        rcases hnext with hb | ⟨hfl, hfi⟩
        · simp [collectPlainScalar_terminates?, hpk, hb]
        · subst hfl
          simp [collectPlainScalar_terminates?, hpk, hfi]
    · subst hf
      obtain ⟨hnb, hnw, hns⟩ := flowIndicator_not_plain hind
      rcases terminates_none_or_stop c sc content spaces true with ht | ht <;> simp [ht, hnb, hnw, hns]
    · rcases terminates_none_or_stop c sc content spaces inFlow with ht | ht <;>
        simp [ht, hnb, hnw, hunsafe]

lemma isPlainSafe_facts {c : Char} {inFlow : Bool} (h : isPlainSafeBool c inFlow = true) :
    isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧
    (inFlow && isFlowIndicatorBool c) = false ∧ isPrintableBool c = true ∧ (c == '﻿') = false := by
  unfold isPlainSafeBool at h
  cases inFlow <;> simp_all

/-- Off column 0 the document-marker check is moot. -/
lemma doc_of_col_pos {sc : ScannerState} {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp)
    (hcol : sp.col > 0) : sc.col = 0 → atDocumentBoundary sc = false := fun h0 => by
  have := hcorr.col_eq; omega

/-- One `PlainCharOk` char: the loop takes it as content (with the pending whites) and advances. -/
lemma collectPlainScalarLoop_char_step (sc : ScannerState) {inFlow aw : Bool} {sp sp' : SurfPos}
    (content spaces : String) (contentIndent inputEnd : Nat)
    (hstep : PlainCharOk inFlow aw sp sp') (hcorr : ScannerSurfCorr sc sp)
    (hdoc : sc.col = 0 → atDocumentBoundary sc = false)
    (hsp : aw = false → spaces = "") :
    ∃ c, (∀ fuel, collectPlainScalarLoop sc content spaces (fuel + 1) inFlow contentIndent inputEnd =
        collectPlainScalarLoop sc.advance (content ++ spaces ++ String.singleton c) "" fuel
          inFlow contentIndent inputEnd) ∧
      ScannerSurfCorr sc.advance sp' ∧ Keeps sc sc.advance := by
  have hcol' : sp.col = sc.col := hcorr.col_eq
  cases hstep with
  | safe aw ch rest col hSafe hc hh =>
    obtain ⟨hnw, hnb, hfi, _, _⟩ := isPlainSafe_facts hSafe
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by intro h; subst h; exact absurd hnb (by decide))
      (by intro h; subst h; exact absurd hnb (by decide))
    refine ⟨ch, fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    have hnd : ¬ (sc.col = 0 ∧ atDocumentBoundary sc = true) := fun ⟨h0, h1⟩ => by
      rw [hdoc h0] at h1; exact Bool.noConfusion h1
    simp [hp, collectPlainScalar_terminates?, hh, hc, hfi, hnd, hnb, hnw, hSafe]
  | colonSafe aw next rest col hSafe =>
    obtain ⟨hnw, hnb, hfi, hpr, hbom⟩ := isPlainSafe_facts hSafe
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hpk : sc.peekAt? 1 = some next := by
      rw [← L4YAML.Proofs.ScannerPlainContent.advance_peek_eq_peekAt_one sc ':' hp]
      exact (peek_of_corr hadv).1
    have hblank : isBlankBool next = false := by simp [isBlankBool, hnw, hnb]
    refine ⟨':', fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    have hs : isPlainSafeBool ':' inFlow = true := by cases inFlow <;> decide
    obtain ⟨hw2, hb2, hf2, hp2, _⟩ := isPlainSafe_facts hs
    simp [hp, collectPlainScalar_terminates?, hpk, hblank, hfi, hpr, hbom, hs, hw2, hb2]
  | hash rest col hcolgt =>
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hc0 : (sc.col == 0) = false := by
      have h1 : col = sc.col := hcol'
      have h2 : 0 < col := hcolgt
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hsp' := hsp rfl
    subst hsp'
    refine ⟨'#', fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    have hs : isPlainSafeBool '#' inFlow = true := by cases inFlow <;> decide
    obtain ⟨hw2, hb2, hf2, hp2, _⟩ := isPlainSafe_facts hs
    simp [hp, collectPlainScalar_terminates?, hc0, hs, hw2, hb2, hf2]

/-- One white char: the loop buffers it into `spaces` and advances. -/
lemma collectPlainScalarLoop_white_step (sc : ScannerState) {sp sp' : SurfPos}
    (content spaces : String) (inFlow : Bool) (contentIndent inputEnd : Nat)
    (hw : SSWhite sp sp') (hcorr : ScannerSurfCorr sc sp) (hcol : sp.col > 0) :
    ∃ c, (∀ fuel, collectPlainScalarLoop sc content spaces (fuel + 1) inFlow contentIndent inputEnd =
        collectPlainScalarLoop sc.advance content (spaces.push c) fuel inFlow contentIndent inputEnd) ∧
      ScannerSurfCorr sc.advance sp' ∧ Keeps sc sc.advance := by
  have hcol' : sp.col = sc.col := hcorr.col_eq
  cases hw with
  | space rest col =>
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hc0 : (sc.col == 0) = false := by
      have h1 : col = sc.col := hcol'
      have h2 : 0 < col := hcol
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    refine ⟨' ', fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    simp [hp, collectPlainScalar_terminates?, hc0, (by decide : isWhiteSpaceBool ' ' = true),
      (by decide : isLineBreakBool ' ' = false), (by decide : isFlowIndicatorBool ' ' = false)]
  | tab rest col =>
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by decide) (by decide)
    have hc0 : (sc.col == 0) = false := by
      have h1 : col = sc.col := hcol'
      have h2 : 0 < col := hcol
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    refine ⟨'\t', fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    simp [hp, collectPlainScalar_terminates?, hc0, (by decide : isWhiteSpaceBool '\t' = true),
      (by decide : isLineBreakBool '\t' = false), (by decide : isFlowIndicatorBool '\t' = false)]

/-- A white run: the loop buffers every white into `spaces` (`k` steps of fuel). -/
lemma collectPlainScalarLoop_whites {sp sp' : SurfPos} (hw : GStar SSWhite sp sp') :
    ∀ (sc : ScannerState) (content spaces : String) (inFlow : Bool) (contentIndent inputEnd : Nat),
      ScannerSurfCorr sc sp → sp.col > 0 →
      ∃ sc' spaces' k,
        (∀ fuel, collectPlainScalarLoop sc content spaces (fuel + k) inFlow contentIndent inputEnd =
          collectPlainScalarLoop sc' content spaces' fuel inFlow contentIndent inputEnd) ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧
        sp.chars.length = sp'.chars.length + k ∧ spaces'.length = spaces.length + k := by
  induction hw with
  | nil s =>
    intro sc content spaces inFlow ci ie hcorr _
    exact ⟨sc, spaces, 0, fun _ => rfl, hcorr, Keeps.refl sc, rfl, rfl⟩
  | cons s₁ s₂ s₃ h1 _ ih =>
    intro sc content spaces inFlow ci ie hcorr hcol
    obtain ⟨c, heq, hadv, hk⟩ :=
      collectPlainScalarLoop_white_step sc content spaces inFlow ci ie h1 hcorr hcol
    have hcol2 : s₂.col > 0 := by cases h1 <;> exact Nat.succ_pos _
    obtain ⟨sc', spaces', k, heq', hcorr', hk', hl1, hl2⟩ :=
      ih sc.advance content (spaces.push c) inFlow ci ie hadv hcol2
    have hl0 : s₁.chars.length = s₂.chars.length + 1 := by cases h1 <;> rfl
    refine ⟨sc', spaces', k + 1, fun fuel => ?_, hcorr', hk.trans hk', by omega, ?_⟩
    · rw [show fuel + (k + 1) = (fuel + k) + 1 by omega, heq, heq']
    · simp [String.length_push] at hl2; omega

/-- The first char (`PlainFirstOk`): the loop takes it as content; at column 0 the state must
not sit on a document marker (`hdoc`). -/
lemma collectPlainScalarLoop_first_step (sc : ScannerState) {inFlow : Bool} {sp sp' : SurfPos}
    (contentIndent inputEnd : Nat)
    (hf : PlainFirstOk inFlow sp sp') (hcorr : ScannerSurfCorr sc sp)
    (hdoc : sc.col = 0 → atDocumentBoundary sc = false) :
    ∃ c, (∀ fuel, collectPlainScalarLoop sc "" "" (fuel + 1) inFlow contentIndent inputEnd =
        collectPlainScalarLoop sc.advance (String.singleton c) "" fuel inFlow contentIndent inputEnd) ∧
      ScannerSurfCorr sc.advance sp' ∧ Keeps sc sc.advance := by
  cases hf with
  | nonIndicator ch rest col hSafe hInd =>
    obtain ⟨hnw, hnb, hfi, hpr, hbom⟩ := isPlainSafe_facts hSafe
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by intro h; subst h; exact absurd hnb (by decide))
      (by intro h; subst h; exact absurd hnb (by decide))
    have hnd : ¬(ch = '-' ∨ ch = '?' ∨ ch = ':') := by
      rintro (rfl | rfl | rfl) <;> exact absurd hInd (by decide)
    have hstart : canStartPlainScalarBool ch (sc.peekAt? 1) inFlow = true := by
      simp [canStartPlainScalarBool, hnd, hInd, hnw, hnb, hpr, bne, hbom]
    have hterm := canStartPlain_first_not_terminates ch sc inFlow hstart hdoc
    refine ⟨ch, fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    simp [hp, hterm, hnb, hnw, hSafe]
  | indicator ch next rest col hInd hSafe =>
    obtain ⟨hnw, hnb, hfi, hpr, hbom⟩ := isPlainSafe_facts hSafe
    have ⟨hp, _⟩ := peek_of_corr hcorr
    have hadv := advance_corr hcorr (by rcases hInd with rfl | rfl | rfl <;> decide)
      (by rcases hInd with rfl | rfl | rfl <;> decide)
    have hpk : sc.peekAt? 1 = some next := by
      rw [← L4YAML.Proofs.ScannerPlainContent.advance_peek_eq_peekAt_one sc ch hp]
      exact (peek_of_corr hadv).1
    have hstart : canStartPlainScalarBool ch (sc.peekAt? 1) inFlow = true := by
      simp [canStartPlainScalarBool, hInd, hpk, hnw, hnb, hfi, hpr, bne, hbom]
    have hterm := canStartPlain_first_not_terminates ch sc inFlow hstart hdoc
    have hs : isPlainSafeBool ch inFlow = true := by
      rcases hInd with rfl | rfl | rfl <;> cases inFlow <;> decide
    obtain ⟨hw2, hb2, _, _, _⟩ := isPlainSafe_facts hs
    refine ⟨ch, fun fuel => ?_, hadv, keeps_advance sc⟩
    rw [collectPlainScalarLoop]
    simp [hp, hterm, hb2, hw2, hs]

lemma PlainCharOk.len_col {inFlow aw : Bool} {s s' : SurfPos} (h : PlainCharOk inFlow aw s s') :
    s.chars.length = s'.chars.length + 1 ∧ s'.col = s.col + 1 :=
  match s, s', h with
  | _, _, .safe _ _ _ _ _ _ _ => ⟨rfl, rfl⟩
  | _, _, .colonSafe _ _ _ _ _ => ⟨rfl, rfl⟩
  | _, _, .hash _ _ _ => ⟨rfl, rfl⟩

/-- One in-line entry (optional white run, then a content char): content grows, `spaces` resets. -/
lemma collectPlainScalarLoop_entry_step (sc : ScannerState) {inFlow : Bool} {sp sp' : SurfPos}
    (content : String) (contentIndent inputEnd : Nat)
    (he : PlainEntryOk inFlow sp sp') (hcorr : ScannerSurfCorr sc sp) (hcol : sp.col > 0) :
    ∃ sc' content' k,
      (∀ fuel, collectPlainScalarLoop sc content "" (fuel + k) inFlow contentIndent inputEnd =
        collectPlainScalarLoop sc' content' "" fuel inFlow contentIndent inputEnd) ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧ sp.chars.length = sp'.chars.length + k ∧
      sp.col < sp'.col ∧ content'.length = content.length + k :=
  match sp, sp', he with
  | _, _, .noWhite s s' hc => by
    obtain ⟨c, heq, hadv, hk⟩ :=
      collectPlainScalarLoop_char_step sc content "" contentIndent inputEnd hc hcorr
        (doc_of_col_pos hcorr hcol)
        (fun _ => rfl)
    obtain ⟨hl, hc'⟩ := hc.len_col
    exact ⟨sc.advance, content ++ "" ++ String.singleton c, 1, heq, hadv, hk, hl, by omega, by simp⟩
  | _, _, .white s s₁ s' hw hc => by
    have hws := GPlus.toGStar hw
    obtain ⟨scw, spaces', kw, heqw, hcorrw, hkw, hl1, hsl⟩ :=
      collectPlainScalarLoop_whites hws sc content "" inFlow contentIndent inputEnd hcorr hcol
    have hcolw : s₁.col > 0 := Nat.lt_of_lt_of_le hcol (GStar_SSWhite_col hws)
    obtain ⟨c, heq, hadv, hk⟩ :=
      collectPlainScalarLoop_char_step scw content spaces' contentIndent inputEnd hc hcorrw
        (doc_of_col_pos hcorrw hcolw)
        (fun h => Bool.noConfusion h)
    obtain ⟨hl, hc'⟩ := hc.len_col
    refine ⟨scw.advance, content ++ spaces' ++ String.singleton c, kw + 1, fun fuel => ?_, hadv,
      hkw.trans hk, by omega, by have := GStar_SSWhite_col hws; omega,
      by have h0 : ("" : String).length = 0 := rfl
         rw [h0] at hsl; simp [String.length_append]; omega⟩
    rw [show fuel + (kw + 1) = (fuel + 1) + kw by omega, heqw, heq]

/-- The in-line entries `[133]`: iterate `collectPlainScalarLoop_entry_step`. -/
lemma collectPlainScalarLoop_entries {inFlow : Bool} {sp sp' : SurfPos}
    (hs : GStar (PlainEntryOk inFlow) sp sp') :
    ∀ (sc : ScannerState) (content : String) (contentIndent inputEnd : Nat),
      ScannerSurfCorr sc sp → sp.col > 0 →
      ∃ sc' content' k,
        (∀ fuel, collectPlainScalarLoop sc content "" (fuel + k) inFlow contentIndent inputEnd =
          collectPlainScalarLoop sc' content' "" fuel inFlow contentIndent inputEnd) ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧ sp.chars.length = sp'.chars.length + k ∧
        sp.col ≤ sp'.col ∧ content'.length = content.length + k := by
  induction hs with
  | nil s =>
    intro sc content ci ie hcorr _
    exact ⟨sc, content, 0, fun _ => rfl, hcorr, Keeps.refl sc, rfl, Nat.le_refl _, rfl⟩
  | cons s₁ s₂ s₃ h1 _ ih =>
    intro sc content ci ie hcorr hcol
    obtain ⟨sc₂, content₂, k₁, heq₁, hcorr₂, hk₁, hl₁, hcol₁, hcl₁⟩ :=
      collectPlainScalarLoop_entry_step sc content ci ie h1 hcorr hcol
    obtain ⟨sc', content', k, heq', hcorr', hk', hl, hcl, hcl'⟩ :=
      ih sc₂ content₂ ci ie hcorr₂ (Nat.lt_trans hcol hcol₁)
    refine ⟨sc', content', k + k₁, fun fuel => ?_, hcorr', hk₁.trans hk', by omega, by omega,
      by omega⟩
    rw [show fuel + (k + k₁) = (fuel + k) + k₁ by omega, heq₁, heq']

lemma PlainFirstOk.len_col {inFlow : Bool} {s s' : SurfPos} (h : PlainFirstOk inFlow s s') :
    s.chars.length = s'.chars.length + 1 ∧ s'.col = s.col + 1 :=
  match s, s', h with
  | _, _, .nonIndicator _ _ _ _ _ => ⟨rfl, rfl⟩
  | _, _, .indicator _ _ _ _ _ _ => ⟨rfl, rfl⟩

/-- One-line plain-scalar converse of `scanPlainScalar_prod`: a `PlainOneLineOk` derivation
`sp → sp'` followed by the trailing white run `sp' → sp''` that the scanner also consumes, and
a `PlainStopOk` stop at `sp''`, is accepted; the scanner lands at `sp''` (not `sp'`: `"a  "`
lands at 3) with the `.plain` token. `hdoc`: at column 0 the scanner refuses a document
marker (`"--- x"` refutes the converse without it). -/
lemma scanPlainScalar_accepts (sc : ScannerState) {sp sp' sp'' : SurfPos} {hadWhite : Bool}
    (hcorr : ScannerSurfCorr sc sp)
    (hder : PlainOneLineOk sc.inFlow sp sp')
    (hwhite : GStar SSWhite sp' sp'')
    (hstop : PlainStopOk sc.inFlow hadWhite sp''.chars)
    (hhw : hadWhite = true → sp''.chars.length < sp'.chars.length)
    (hdoc : sc.col = 0 → atDocumentBoundary sc = false) :
    ∃ s' content, scanPlainScalar sc = .ok s' ∧ ScannerSurfCorr s' sp'' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .plain } := by
  have ⟨s₁, hf, hstar⟩ : ∃ s₁, PlainFirstOk sc.inFlow sp s₁ ∧
      GStar (PlainEntryOk sc.inFlow) s₁ sp' :=
    match sp, sp', hder with
    | _, _, .mk _ s₁ _ hf hstar => ⟨s₁, hf, hstar⟩
  have hfuel := fuel_of_corr hcorr
  obtain ⟨hl₁, hcol₁⟩ := hf.len_col
  obtain ⟨c, heq₁, hc₁, hk₁⟩ :=
    collectPlainScalarLoop_first_step sc (inFlow := sc.inFlow) (sp := sp) (sp' := s₁)
      (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd hf hcorr hdoc
  obtain ⟨sc₂, content₂, k₂, heq₂, hc₂, hk₂, hl₂, hcl₂⟩ :=
    collectPlainScalarLoop_entries hstar sc.advance (String.singleton c)
      (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd hc₁
      (by omega)
  obtain ⟨sc₃, spaces₃, k₃, heq₃, hc₃, hk₃, hl₃, hs₃⟩ :=
    collectPlainScalarLoop_whites hwhite sc₂ content₂ "" sc.inFlow
      (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd hc₂ (by omega)
  have hsp : hadWhite = true → spaces₃.length > 0 := fun h => by
    have := hhw h; simp at hs₃; omega
  have hk := hk₁.trans (hk₂.trans hk₃)
  obtain ⟨f, hF⟩ : ∃ f, (sc.inputEnd - sc.offset + 1) * 2 = (((f + 1) + k₃) + k₂) + 1 :=
    ⟨(sc.inputEnd - sc.offset + 1) * 2 - (k₂ + k₃ + 2), by omega⟩
  have hloop : collectPlainScalarLoop sc "" "" ((sc.inputEnd - sc.offset + 1) * 2)
      sc.inFlow (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd =
      .ok { content := content₂, spaces := spaces₃, state := sc₃, terminated := true } := by
    rw [hF, heq₁, heq₂, heq₃]
    exact collectPlainScalarLoop_stops sc₃ content₂ spaces₃ f sc.inFlow _ sc.inputEnd hc₃ hstop hsp
  refine ⟨{ sc₃.emitAt sc.currentPos (.scalar (trimTrailingWS content₂) .plain) with
      simpleKeyAllowed := false, needIndentCheck := false }, trimTrailingWS content₂, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hc₃), ?_⟩
  · unfold scanPlainScalar
    simp only [hloop, bind, Except.bind]
  · simp [ScannerState.emitAt, hk.1]

/-! ## Multi-line: the block fold `collectPlainScalar_handleBlockLineBreak` -/

/-- `skipBlankLinesLoop` consumes exactly the `SLEmptyOk n` blank lines (twin of
    `foldQuotedNewlinesLoop_accepts`). -/
lemma skipBlankLinesLoop_accepts {n : Nat} {sp sp₂ : SurfPos}
    (hblank : GStar (SLEmptyOk n) sp sp₂) :
    ∀ (sc : ScannerState) (cnt fuel inputEnd : Nat) (sp' : SurfPos),
      ScannerSurfCorr sc sp → (n : Int) > sc.currentIndent →
      GStar SSWhite sp₂ sp' → sp'.chars.head? ≠ some ' ' → sp'.chars.head? ≠ some '\t' →
      (∀ c, sp'.chars.head? = some c → isLineBreakBool c = false) →
      sp.chars.length < fuel →
      ∃ sc₂ k, skipBlankLinesLoop sc cnt fuel inputEnd = (cnt + k, sc₂) ∧
        ScannerSurfCorr sc₂ sp₂ ∧ Keeps sc sc₂ := by
  induction hblank with
  | nil s =>
    intro sc cnt fuel inputEnd sp' hcorr _ hpre hsp htab hnb hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      obtain ⟨h1, _⟩ := skipWhitespace_accepts sc hpre hcorr hsp htab
      refine ⟨sc, 0, ?_, hcorr, Keeps.refl sc⟩
      obtain ⟨chars, col⟩ := sp'
      cases chars with
      | nil => simp only [skipBlankLinesLoop, peek_none_of_corr h1, Nat.add_zero]
      | cons c tl =>
        have hpeek := (peek_of_corr h1).1
        have hc := hnb c rfl
        simp only [skipBlankLinesLoop, hpeek, hc, Bool.false_eq_true, ite_false, Nat.add_zero]
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc cnt fuel inputEnd sp' hcorr hfloor hpre hsp htab hnb hfuel
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      obtain ⟨c, hpeek, hlb, hbt, h1, h2⟩ := blankLine_accepts sc hstep hcorr hfloor
      have hlt := hstep.length_lt
      obtain ⟨sc₂, k, h3, h4, h5⟩ := ih _ (cnt + 1) f inputEnd sp' h1
        (by rw [h2.currentIndent]; exact hfloor) hpre hsp htab hnb (by omega)
      refine ⟨sc₂, k + 1, ?_, h4, h2.trans h5⟩
      simp only [skipBlankLinesLoop, hpeek, hlb, hbt, Bool.false_eq_true, ite_false, ite_true, h3]
      congr 1; omega

/-- A `[134]` landing is not a document marker once the spaces are gone: whites left
    before `sp'` start with a tab. -/
lemma notDocMarker_of_white {sp sp' : SurfPos} (hw : GStar SSWhite sp sp')
    (hsp : sp.chars.head? ≠ some ' ') (hdoc : NotDocMarker sp') : NotDocMarker sp := by
  cases hw with
  | nil => exact hdoc
  | cons _ _ _ h _ =>
    cases h with
    | space rest col => exact absurd rfl hsp
    | tab rest col => intro _; exact ⟨fun r h => by simp at h, fun r h => by simp at h⟩

/-- The block fold: break, `SLEmptyOk n` blank lines, `[69]` landing clearing the floor
    (`contentIndent ≤ n`), not a document marker.  Folds to `" "` or `k` line feeds. -/
lemma handleBlockLineBreak_accepts (sc : ScannerState) {n : Nat} {sp sp₁ sp₂ sp' : SurfPos}
    (content : String) (contentIndent : Nat)
    (hb : SBBreakOk sp sp₁) (hblank : GStar (SLEmptyOk n) sp₁ sp₂) (hpre : SFlowLinePrefix n sp₂ sp')
    (hcorr : ScannerSurfCorr sc sp) (hfloor : (n : Int) > sc.currentIndent)
    (hsp : sp'.chars.head? ≠ some ' ') (htab : sp'.chars.head? ≠ some '\t')
    (hnb : ∀ c, sp'.chars.head? = some c → isLineBreakBool c = false)
    (hci : contentIndent ≤ n) (hdoc : NotDocMarker sp') :
    ∃ k s', collectPlainScalar_handleBlockLineBreak sc content contentIndent sc.inputEnd =
        some (content ++ (if k > 0 then String.ofList (List.replicate k '\n') else " "), s') ∧
      ScannerSurfCorr s' sp' ∧ Keeps sc s' := by
  obtain ⟨h1, k1⟩ := consumeNewline_accepts sc hb hcorr
  have hfuel := fuel_of_corr h1
  obtain ⟨sc₂, k, hloop, h2, k2⟩ := skipBlankLinesLoop_accepts hblank (consumeNewline sc) 0
    (sc.inputEnd - (consumeNewline sc).offset + 1) sc.inputEnd sp' h1
    (by rw [k1.currentIndent]; exact hfloor) (flowLinePrefix_toGStar hpre) hsp htab hnb (by rw [← k1.2.1]; exact hfuel)
  obtain ⟨h3, _, k3⟩ := flowLinePrefix_accepts sc₂ hpre h2 hsp htab
    (by rw [(k1.trans k2).currentIndent]; exact hfloor)
  rcases hpre with ⟨_, _, hind, hopt⟩
  have hfuel₂ := fuel_of_corr h2
  obtain ⟨spa, ha, hw, hasp, hacol⟩ := skipSpacesLoop_prefix_accepts n sc₂ sp₂ _ sp'
    (sc₂.inputEnd - sc₂.offset) hind (GOpt_sepInLine_to_gstar hopt) h2 hsp (by omega)
  have hcol : ¬ ((skipSpaces sc₂).col < contentIndent) := by
    have := ha.col_eq; unfold skipSpaces; omega
  have hdb : atDocumentBoundary (skipSpaces sc₂) = false := by
    have hnd := notDocMarker_of_white hw hasp hdoc
    unfold skipSpaces
    simp [atDocumentBoundary, atDocumentStart_false_of_corr ha hnd, atDocumentEnd_false_of_corr ha hnd]
  refine ⟨k, _, ?_, h3, k1.trans (k2.trans k3)⟩
  unfold collectPlainScalar_handleBlockLineBreak
  simp only [hloop, Nat.zero_add, hcol, hdb, ite_false, Bool.false_eq_true]
  by_cases hk : k > 0 <;> simp [hk]

/-- Block-context fold step at a break: `collectPlainScalar_handleBlockLineBreak` lands at the
    `[134]` continuation, which must not start with `#` (`"a\n #b"` rolls back) and whose loop
    result must add content, else the scanner rolls back to the break. -/
lemma collectPlainScalarLoop_blockFold_step (sc : ScannerState) {n : Nat}
    {sp sp₁ sp₂ sp' : SurfPos} (content spaces : String) (contentIndent fuel : Nat)
    (hb : SBBreakOk sp sp₁) (hblank : GStar (SLEmptyOk n) sp₁ sp₂)
    (hpre : SFlowLinePrefix n sp₂ sp')
    (hcorr : ScannerSurfCorr sc sp) (hfloor : (n : Int) > sc.currentIndent)
    (hsp : sp'.chars.head? ≠ some ' ') (htab : sp'.chars.head? ≠ some '\t')
    (hnb : ∀ c, sp'.chars.head? = some c → isLineBreakBool c = false)
    (hhash : sp'.chars.head? ≠ some '#')
    (hci : contentIndent ≤ n) (hdoc : NotDocMarker sp') :
    ∃ k s', ScannerSurfCorr s' sp' ∧ Keeps sc s' ∧
      ∀ result,
        collectPlainScalarLoop s'
          (content ++ (if k > 0 then String.ofList (List.replicate k '\n') else " ")) ""
          fuel false contentIndent sc.inputEnd = .ok result →
        result.content.length >
          (content ++ (if k > 0 then String.ofList (List.replicate k '\n') else " ")).length →
        collectPlainScalarLoop sc content spaces (fuel + 1) false contentIndent sc.inputEnd =
          .ok result := by
  obtain ⟨k, s', hblk, hcorr', hk⟩ :=
    handleBlockLineBreak_accepts sc content contentIndent hb hblank hpre hcorr hfloor hsp htab
      hnb hci hdoc
  refine ⟨k, s', hcorr', hk, fun result hloop hlen => ?_⟩
  obtain ⟨c, rest, hs, hlb⟩ := hb.head
  obtain ⟨cs, col⟩ := sp
  simp only at hs; subst hs
  have hpeek : sc.peek? = some c := (peek_of_corr hcorr).1
  have hterm : collectPlainScalar_terminates? c sc content spaces false = none := by
    have hnd : NotDocMarker ⟨c :: rest, col⟩ := by
      cases hb <;> intro _ <;> exact ⟨fun r h => by simp at h, fun r h => by simp at h⟩
    have hdb : atDocumentBoundary sc = false := by
      simp [atDocumentBoundary, atDocumentStart_false_of_corr hcorr hnd,
        atDocumentEnd_false_of_corr hcorr hnd]
    cases hb <;> simp [collectPlainScalar_terminates?, hdb] <;> (intro _; decide)
  have hnotLe : ¬ (result.content.length ≤
      (content ++ (if k > 0 then String.ofList (List.replicate k '\n') else " ")).length) := by
    omega
  simp only [collectPlainScalarLoop, hpeek, hterm, hlb, ite_true, Bool.false_eq_true, ite_false,
    hblk]
  obtain ⟨chars, col⟩ := sp'
  cases chars with
  | nil => simp only [peek_none_of_corr hcorr', hloop, hnotLe, ite_false]
  | cons d tl =>
    have hpk := (peek_of_corr hcorr').1
    have hd : d ≠ '#' := by intro h; subst h; exact hhash rfl
    simp only [hpk]
    split
    · rename_i heq; exact absurd (Option.some.inj heq) hd
    · simp only [hloop, hnotLe, ite_false]

/-- A continuation line's first `PlainCharOk` (not `#`) is a maximal `[69]` landing: no white,
    no break ahead. -/
lemma PlainCharOk.landing_ok {inFlow aw : Bool} {s s' : SurfPos} (h : PlainCharOk inFlow aw s s')
    (hhash : s.chars.head? ≠ some '#') :
    s.chars.head? ≠ some ' ' ∧ s.chars.head? ≠ some '\t' ∧
      ∀ c, s.chars.head? = some c → isLineBreakBool c = false := by
  cases h with
  | safe aw ch rest col hSafe _ _ =>
    obtain ⟨hnw, hnb, _⟩ := isPlainSafe_facts hSafe
    refine ⟨?_, ?_, fun c hc => by simp at hc; subst hc; exact hnb⟩ <;>
      intro h <;> simp at h <;> subst h <;> simp [isWhiteSpaceBool] at hnw <;>
      first | exact absurd hnw.1 (by decide) | exact absurd hnw.2 (by decide)
  | colonSafe aw next rest col _ =>
    exact ⟨by simp, by simp, fun c hc => by simp at hc; subst hc; rfl⟩
  | hash rest col _ => exact absurd rfl hhash

/-- `[134] s-ns-plain-next-line` narrowed to the scanner (both contexts): trailing whites, a
    `SBBreakOk` break, `SLEmptyOk n` blank lines, a maximal `[69]` landing that is neither `#`
    nor a document marker, then a `PlainCharOk` and in-line entries. -/
inductive PlainNextLineOk (inFlow : Bool) (n : Nat) : SurfPos → SurfPos → Prop where
  | mk (s s_ws s₁ s₂ s₃ s₄ s' : SurfPos) :
      GStar SSWhite s s_ws →
      SBBreakOk s_ws s₁ →
      GStar (SLEmptyOk n) s₁ s₂ →
      SFlowLinePrefix n s₂ s₃ →
      s₃.chars.head? ≠ some '#' →
      NotDocMarker s₃ →
      PlainCharOk inFlow false s₃ s₄ →
      GStar (PlainEntryOk inFlow) s₄ s' →
      PlainNextLineOk inFlow n s s'

lemma atDocumentBoundary_false_of_corr {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hnd : NotDocMarker sp) : atDocumentBoundary sc = false := by
  simp [atDocumentBoundary, atDocumentStart_false_of_corr hcorr hnd,
    atDocumentEnd_false_of_corr hcorr hnd]

lemma SBBreakOk.col_zero {s s' : SurfPos} (h : SBBreakOk s s') : s'.col = 0 := by
  cases h <;> rfl

lemma GStar_SLEmptyOk_col {n : Nat} {s s' : SurfPos} (h : GStar (SLEmptyOk n) s s') :
    s.col = 0 → s'.col = 0 := by
  induction h with
  | nil => exact id
  | cons _ _ _ hs _ ih =>
    intro _; apply ih
    rcases hs with ⟨_, _, _, hb⟩ | ⟨_, _, _, hb⟩ <;> exact hb.col_zero

lemma SIndent_col_eq {m : Nat} {s s' : SurfPos} (h : SIndent m s s') : s'.col = s.col + m := by
  induction h with
  | zero => rfl
  | succ n rest col s' _ ih => simp only at ih ⊢; omega

/-- At a `SBBreakOk` break the block loop takes its line-break arm. -/
lemma break_peek_term {sc : ScannerState} {sp sp₁ : SurfPos} (hb : SBBreakOk sp sp₁)
    (hcorr : ScannerSurfCorr sc sp) (inFlow : Bool) :
    ∃ c, sc.peek? = some c ∧ isLineBreakBool c = true ∧
      ∀ content spaces, collectPlainScalar_terminates? c sc content spaces inFlow = none := by
  obtain ⟨c, rest, hs, hlb⟩ := hb.head
  obtain ⟨cs, col⟩ := sp
  simp only at hs; subst hs
  refine ⟨c, (peek_of_corr hcorr).1, hlb, fun content spaces => ?_⟩
  have hnd : NotDocMarker ⟨c :: rest, col⟩ := by
    cases hb <;> intro _ <;> exact ⟨fun r h => by simp at h, fun r h => by simp at h⟩
  have hdb := atDocumentBoundary_false_of_corr hcorr hnd
  cases hb <;> simp [collectPlainScalar_terminates?, hdb]
  all_goals (intro _; decide)

/-- Under-indented continuation: the leading spaces after the blank lines stop short of the
    content indent, so the block fold refuses. -/
lemma handleBlockLineBreak_refuses (sc : ScannerState) {n m : Nat}
    {sp sp₁ sp₂ sp₃ sp₄ : SurfPos} (content : String) (contentIndent : Nat)
    (hb : SBBreakOk sp sp₁) (hblank : GStar (SLEmptyOk n) sp₁ sp₂) (hind : SIndent m sp₂ sp₃)
    (hmax : sp₃.chars.head? ≠ some ' ') (hw : GStar SSWhite sp₃ sp₄)
    (hsp : sp₄.chars.head? ≠ some ' ') (htab : sp₄.chars.head? ≠ some '\t')
    (hnb : ∀ c, sp₄.chars.head? = some c → isLineBreakBool c = false)
    (hcorr : ScannerSurfCorr sc sp) (hfloor : (n : Int) > sc.currentIndent)
    (hm : m < contentIndent) :
    collectPlainScalar_handleBlockLineBreak sc content contentIndent sc.inputEnd = none := by
  obtain ⟨h1, k1⟩ := consumeNewline_accepts sc hb hcorr
  have hfuel := fuel_of_corr h1
  obtain ⟨sc₂, k, hloop, h2, _⟩ := skipBlankLinesLoop_accepts hblank (consumeNewline sc) 0
    (sc.inputEnd - (consumeNewline sc).offset + 1) sc.inputEnd sp₄ h1
    (by rw [k1.currentIndent]; exact hfloor)
    (gstar_sswhite_append (sindent_to_gstar_sswhite hind) hw) hsp htab hnb
    (by rw [← k1.2.1]; exact hfuel)
  have h3 := (skipSpaces_accepts sc₂ hind h2 hmax).1
  have hc₂ : sp₂.col = 0 := GStar_SLEmptyOk_col hblank hb.col_zero
  have hlt : (skipSpaces sc₂).col < contentIndent := by
    have := h3.col_eq; have := SIndent_col_eq hind; omega
  unfold collectPlainScalar_handleBlockLineBreak
  simp only [hloop, Nat.zero_add, hlt, ite_true]

lemma peekAtLoop_chars {input : String} {inputEnd : Nat} (hend : inputEnd = input.utf8ByteSize) :
    ∀ (n p : Nat) (cs : List Char), CharsFromOffset input p cs →
      ScannerState.peekAt?Loop input inputEnd ⟨p⟩ n = cs[n]? := by
  intro n
  induction n with
  | zero =>
    intro p cs hcf
    unfold ScannerState.peekAt?Loop
    cases hcf with
    | at_end _ hp => simp [show ¬ p < inputEnd by omega]
    | cons _ hp c rest hc _ => simp [show p < inputEnd by omega, hc]
  | succ n ih =>
    intro p cs hcf
    unfold ScannerState.peekAt?Loop
    cases hcf with
    | at_end _ hp => simp [show ¬ p < inputEnd by omega]
    | cons _ hp c rest _ hrest => simp [show p < inputEnd by omega, ih _ rest hrest]

/-- `peekAt? n` reads the `n`-th surface character. -/
lemma peekAt_of_corr {sc : ScannerState} {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp) (n : Nat) :
    sc.peekAt? n = sp.chars[n]? := by
  unfold ScannerState.peekAt?
  exact peekAtLoop_chars hcorr.end_eq n sc.offset sp.chars hcorr.chars_from

/-- A document marker as the scanner reads it: `---`/`...` then EOF or a blank. -/
def DocMarkerAt (sp : SurfPos) : Prop :=
  ∃ m r, (m = '-' ∨ m = '.') ∧ sp.chars = m :: m :: m :: r ∧
    (∀ c, r.head? = some c → isBlankBool c = true)

lemma atDocumentBoundary_true_of_marker {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hm : DocMarkerAt sp) (h0 : sp.col = 0) :
    atDocumentBoundary sc = true := by
  obtain ⟨m, r, hm, hchars, hr⟩ := hm
  have hcol : (sc.col == 0) = true := by
    have := hcorr.col_eq; simp; omega
  have hp := fun n => peekAt_of_corr hcorr n
  simp only [hchars] at hp
  have h3 : (match sc.peekAt? 3 with | none => true | some c => isBlankBool c) = true := by
    rw [hp 3]
    cases r with
    | nil => rfl
    | cons c t => exact hr c rfl
  rcases hm with rfl | rfl
  · simp [atDocumentBoundary, atDocumentStart, hcol, hp 0, hp 1, hp 2]; exact Or.inl h3
  · simp [atDocumentBoundary, atDocumentEnd, hcol, hp 0, hp 1, hp 2]; exact Or.inr h3

/-- A document marker on the continuation line: the block fold refuses. -/
lemma handleBlockLineBreak_refuses_marker (sc : ScannerState) {n : Nat}
    {sp sp₁ sp₂ : SurfPos} (content : String) (contentIndent : Nat)
    (hb : SBBreakOk sp sp₁) (hblank : GStar (SLEmptyOk n) sp₁ sp₂) (hm : DocMarkerAt sp₂)
    (hcorr : ScannerSurfCorr sc sp) (hfloor : (n : Int) > sc.currentIndent) :
    collectPlainScalar_handleBlockLineBreak sc content contentIndent sc.inputEnd = none := by
  obtain ⟨h1, k1⟩ := consumeNewline_accepts sc hb hcorr
  have hfuel := fuel_of_corr h1
  have hhead : ∀ c, sp₂.chars.head? = some c → c = '-' ∨ c = '.' := by
    obtain ⟨m, r, hm, hchars, _⟩ := hm
    intro c hc; rw [hchars] at hc; simp at hc; subst hc; exact hm
  have hsp : sp₂.chars.head? ≠ some ' ' := fun h => by
    rcases hhead _ h with h | h <;> simp at h
  have htab : sp₂.chars.head? ≠ some '\t' := fun h => by
    rcases hhead _ h with h | h <;> simp at h
  have hnb : ∀ c, sp₂.chars.head? = some c → isLineBreakBool c = false := fun c h => by
    rcases hhead c h with rfl | rfl <;> rfl
  obtain ⟨sc₂, k, hloop, h2, _⟩ := skipBlankLinesLoop_accepts hblank (consumeNewline sc) 0
    (sc.inputEnd - (consumeNewline sc).offset + 1) sc.inputEnd sp₂ h1
    (by rw [k1.currentIndent]; exact hfloor) (GStar.nil _) hsp htab hnb
    (by rw [← k1.2.1]; exact hfuel)
  have h3 := (skipSpaces_accepts sc₂ (SIndent.zero sp₂) h2 hsp).1
  have hc₂ : sp₂.col = 0 := GStar_SLEmptyOk_col hblank hb.col_zero
  have hdb := atDocumentBoundary_true_of_marker h3 hm hc₂
  unfold collectPlainScalar_handleBlockLineBreak
  by_cases hlt : (skipSpaces sc₂).col < contentIndent
  · simp only [hloop, Nat.zero_add, hlt, ite_true]
  · simp only [hloop, Nat.zero_add, hlt, ite_false, hdb, ite_true]

/-- Block-context stop at a break: the scanner tries the fold and rolls back to the break,
    either refusing an under-indented continuation or folding into a line that adds no
    content (`#`, EOF, `: `, an unsafe character), or refusing a document marker. -/
inductive PlainBreakStopOk (n contentIndent : Nat) : SurfPos → Prop where
  | underIndent (s s₁ s₂ s₃ s₄ : SurfPos) (m : Nat) :
      SBBreakOk s s₁ → GStar (SLEmptyOk n) s₁ s₂ → SIndent m s₂ s₃ →
      s₃.chars.head? ≠ some ' ' → GStar SSWhite s₃ s₄ →
      s₄.chars.head? ≠ some ' ' → s₄.chars.head? ≠ some '\t' →
      (∀ c, s₄.chars.head? = some c → isLineBreakBool c = false) →
      m < contentIndent → PlainBreakStopOk n contentIndent s
  | noContent (s s₁ s₂ s₃ : SurfPos) :
      SBBreakOk s s₁ → GStar (SLEmptyOk n) s₁ s₂ → SFlowLinePrefix n s₂ s₃ →
      s₃.chars.head? ≠ some ' ' → s₃.chars.head? ≠ some '\t' →
      (∀ c, s₃.chars.head? = some c → isLineBreakBool c = false) →
      NotDocMarker s₃ →
      (s₃.chars.head? = some '#' ∨ PlainStopOk false false s₃.chars) →
      PlainBreakStopOk n contentIndent s
  | docMarker (s s₁ s₂ : SurfPos) :
      SBBreakOk s s₁ → GStar (SLEmptyOk n) s₁ s₂ → DocMarkerAt s₂ →
      PlainBreakStopOk n contentIndent s

lemma collectPlainScalarLoop_breakStop (sc : ScannerState) {n contentIndent : Nat} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (h : PlainBreakStopOk n contentIndent sp)
    (hfloor : (n : Int) > sc.currentIndent) (hci : contentIndent ≤ n) :
    ∀ fuel content spaces,
      collectPlainScalarLoop sc content spaces (fuel + 1) false contentIndent sc.inputEnd =
        .ok { content, spaces, state := sc, terminated := true } := by
  intro fuel content spaces
  cases h with
  | underIndent s₁ s₂ s₃ s₄ m hb hblank hind hmax hw hsp htab hnb hm =>
    obtain ⟨c, hpeek, hlb, hterm⟩ := break_peek_term hb hcorr false
    have hr := handleBlockLineBreak_refuses sc content contentIndent hb hblank hind hmax hw
      hsp htab hnb hcorr hfloor hm
    simp only [collectPlainScalarLoop, hpeek, hterm, hlb, ite_true, Bool.false_eq_true,
      ite_false, hr]
  | docMarker s₁ s₂ hb hblank hm =>
    obtain ⟨c, hpeek, hlb, hterm⟩ := break_peek_term hb hcorr false
    have hr := handleBlockLineBreak_refuses_marker sc content contentIndent hb hblank hm hcorr hfloor
    simp only [collectPlainScalarLoop, hpeek, hterm, hlb, ite_true, Bool.false_eq_true,
      ite_false, hr]
  | noContent s₁ s₂ s₃ hb hblank hpre hsp htab hnb hdoc hcase =>
    obtain ⟨c, hpeek, hlb, hterm⟩ := break_peek_term hb hcorr false
    obtain ⟨k, s', hblk, hcorr', _⟩ :=
      handleBlockLineBreak_accepts sc content contentIndent hb hblank hpre hcorr hfloor hsp htab
        hnb hci hdoc
    simp only [collectPlainScalarLoop, hpeek, hterm, hlb, ite_true, Bool.false_eq_true,
      ite_false, hblk]
    rcases hcase with hh | hst
    · have hpk : s'.peek? = some '#' := by
        obtain ⟨cs, col⟩ := s₃
        cases cs with
        | nil => simp at hh
        | cons d tl => simp at hh; subst hh; exact (peek_of_corr hcorr').1
      simp [hpk]
    · split
      · rfl
      · cases fuel with
        | zero => simp [collectPlainScalarLoop]
        | succ f =>
          rw [collectPlainScalarLoop_stops s' _ "" f false _ _ hcorr' hst
            (fun h => Bool.noConfusion h)]
          simp

/-- Flow-context fold step at a break: `foldQuotedNewlines` lands at the `[134]` continuation
    (clearing the floor, so no `underIndentedScalar`), which must not start with `#` and whose
    loop result must add content, else the scanner rolls back to the break. -/
lemma collectPlainScalarLoop_flowFold_step (sc : ScannerState) {n : Nat}
    {sp sp₁ sp₂ sp' : SurfPos} (content spaces : String) (contentIndent fuel ie : Nat)
    (hb : SBBreakOk sp sp₁) (hblank : GStar (SLEmptyOk n) sp₁ sp₂)
    (hpre : SFlowLinePrefix n sp₂ sp')
    (hcorr : ScannerSurfCorr sc sp) (hfloor : (n : Int) > sc.currentIndent)
    (hsp : sp'.chars.head? ≠ some ' ') (htab : sp'.chars.head? ≠ some '\t')
    (hnb : ∀ c, sp'.chars.head? = some c → isLineBreakBool c = false)
    (hhash : sp'.chars.head? ≠ some '#') :
    ∃ folded s', ScannerSurfCorr s' sp' ∧ Keeps sc s' ∧
      ∀ result,
        collectPlainScalarLoop s' (content ++ folded) "" fuel true contentIndent ie =
          .ok result →
        result.content.length > (content ++ folded).length →
        collectPlainScalarLoop sc content spaces (fuel + 1) true contentIndent ie =
          .ok result := by
  obtain ⟨folded, s', hfold, hcorr', hk⟩ :=
    foldQuotedNewlines_accepts sc hb hblank hpre hcorr hfloor hsp htab hnb
  refine ⟨folded, s', hcorr', hk, fun result hloop hlen => ?_⟩
  obtain ⟨c, hpeek, hlb, hterm⟩ := break_peek_term hb hcorr true
  have hgate : (decide (s'.currentIndent ≥ 0) && decide ((s'.col : Int) ≤ s'.currentIndent))
      = false := by
    have h1 := hcorr'.col_eq
    have h2 := flowLinePrefix_col hpre
    have h4 := hk.currentIndent
    refine Bool.and_eq_false_iff.mpr (Or.inr ?_)
    rw [decide_eq_false_iff_not]; omega
  have hnotLe : ¬ (result.content.length ≤ (content ++ folded).length) := by omega
  simp only [collectPlainScalarLoop, hpeek, hterm, hlb, ite_true, hfold, bind, Except.bind]
  obtain ⟨chars, col⟩ := sp'
  cases chars with
  | nil =>
    simp only [peek_none_of_corr hcorr', hgate, Bool.false_eq_true, ite_false, hloop, hnotLe]
  | cons d tl =>
    have hpk := (peek_of_corr hcorr').1
    have hd : d ≠ '#' := by intro h; subst h; exact hhash rfl
    simp only [hpk]
    split
    · rename_i heq; exact absurd (Option.some.inj heq) hd
    · simp only [hgate, Bool.false_eq_true, ite_false, hloop, hnotLe]

/-- Flow-context stop at a break: the fold lands on a line that adds no content (`#`, a flow
    indicator, EOF, `: `, an unsafe character, or a document marker at column 0), so the scanner
    rolls back to the break.  Under-indentation is a hard `underIndentedScalar` error in flow
    context (`"a\nb"` under indent 0), hence no refusal arm. -/
inductive PlainFlowBreakStopOk (n : Nat) : SurfPos → Prop where
  | noContent (s s₁ s₂ s₃ : SurfPos) :
      SBBreakOk s s₁ → GStar (SLEmptyOk n) s₁ s₂ → SFlowLinePrefix n s₂ s₃ →
      s₃.chars.head? ≠ some ' ' → s₃.chars.head? ≠ some '\t' →
      (∀ c, s₃.chars.head? = some c → isLineBreakBool c = false) →
      (s₃.chars.head? = some '#' ∨ PlainStopOk true false s₃.chars ∨
        (s₃.col = 0 ∧ DocMarkerAt s₃)) →
      PlainFlowBreakStopOk n s

/-- At a column-0 document marker the plain loop stops where it stands. -/
lemma terminates_at_marker {sc : ScannerState} {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp)
    (hm : DocMarkerAt sp) (h0 : sp.col = 0) (content spaces : String) (inFlow : Bool) :
    ∃ m, sc.peek? = some m ∧ collectPlainScalar_terminates? m sc content spaces inFlow =
      some { content, spaces, state := sc, terminated := true } := by
  have hdb := atDocumentBoundary_true_of_marker hcorr hm h0
  have hc0 : sc.col = 0 := by have := hcorr.col_eq; omega
  obtain ⟨m, r, hm, hchars, _⟩ := hm
  obtain ⟨cs, col⟩ := sp
  simp only at hchars; subst hchars
  refine ⟨m, (peek_of_corr hcorr).1, ?_⟩
  rcases hm with rfl | rfl <;> simp [collectPlainScalar_terminates?, hdb, hc0]

lemma collectPlainScalarLoop_flowBreakStop (sc : ScannerState) {n contentIndent : Nat}
    {sp : SurfPos} (ie : Nat)
    (hcorr : ScannerSurfCorr sc sp) (h : PlainFlowBreakStopOk n sp)
    (hfloor : (n : Int) > sc.currentIndent) :
    ∀ fuel content spaces,
      collectPlainScalarLoop sc content spaces (fuel + 1) true contentIndent ie =
        .ok { content, spaces, state := sc, terminated := true } := by
  intro fuel content spaces
  cases h with
  | noContent s₁ s₂ s₃ hb hblank hpre hsp htab hnb hcase =>
    obtain ⟨c, hpeek, hlb, hterm⟩ := break_peek_term hb hcorr true
    obtain ⟨folded, s', hfold, hcorr', hk⟩ :=
      foldQuotedNewlines_accepts sc hb hblank hpre hcorr hfloor hsp htab hnb
    have hgate : (decide (s'.currentIndent ≥ 0) && decide ((s'.col : Int) ≤ s'.currentIndent))
        = false := by
      have h1 := hcorr'.col_eq
      have h2 := flowLinePrefix_col hpre
      have h4 := hk.currentIndent
      refine Bool.and_eq_false_iff.mpr (Or.inr ?_)
      rw [decide_eq_false_iff_not]; omega
    simp only [collectPlainScalarLoop, hpeek, hterm, hlb, ite_true, hfold, bind, Except.bind]
    rcases hcase with hh | hst | hm
    · have hpk : s'.peek? = some '#' := by
        obtain ⟨cs, col⟩ := s₃
        cases cs with
        | nil => simp at hh
        | cons d tl => simp at hh; subst hh; exact (peek_of_corr hcorr').1
      simp [hpk]
    · split
      · rfl
      · simp only [hgate, Bool.false_eq_true, ite_false]
        cases fuel with
        | zero => simp [collectPlainScalarLoop]
        | succ f =>
          rw [collectPlainScalarLoop_stops s' _ "" f true _ _ hcorr' hst
            (fun h => Bool.noConfusion h)]
          simp
    · obtain ⟨h0, hm⟩ := hm
      obtain ⟨m, hpk, hstop⟩ := terminates_at_marker hcorr' hm h0 (content ++ folded) "" true
      split
      · rfl
      · simp only [hgate, Bool.false_eq_true, ite_false]
        cases fuel with
        | zero => simp [collectPlainScalarLoop]
        | succ f =>
          simp [collectPlainScalarLoop, hpk, hstop]

/-- Continuation lines in either context: fold each `PlainNextLineOk inFlow n` line, then the
    trailing white run and the stop (in-line, or a break the scanner rolls back to).  The
    content only grows, so no fold rolls back. -/
lemma collectPlainScalarLoop_nextLines {inFlow : Bool} {n : Nat} {sp sp' : SurfPos}
    (hnext : GStar (PlainNextLineOk inFlow n) sp sp') :
    ∀ (sc : ScannerState) (content : String) (contentIndent fuel ie : Nat) (sp'' : SurfPos)
      (hadWhite : Bool),
      ScannerSurfCorr sc sp → sc.inputEnd = ie → (n : Int) > sc.currentIndent →
      (inFlow = false → contentIndent ≤ n) → sp.col > 0 →
      GStar SSWhite sp' sp'' →
      (PlainStopOk inFlow hadWhite sp''.chars ∨
        (inFlow = false ∧ PlainBreakStopOk n contentIndent sp'') ∨
        (inFlow = true ∧ PlainFlowBreakStopOk n sp'')) →
      (hadWhite = true → sp''.chars.length < sp'.chars.length) →
      sp.chars.length < fuel →
      ∃ result,
        collectPlainScalarLoop sc content "" fuel inFlow contentIndent ie = .ok result ∧
        ScannerSurfCorr result.state sp'' ∧ Keeps sc result.state ∧
        content.length ≤ result.content.length := by
  induction hnext with
  | nil s =>
    intro sc content ci fuel ie sp'' hw hcorr hie hfloor hci hcol hwhite hstop hhw hfuel
    obtain ⟨sc₃, spaces₃, k₃, heq₃, hc₃, hk₃, hl₃, hs₃⟩ :=
      collectPlainScalarLoop_whites hwhite sc content "" inFlow ci ie hcorr hcol
    obtain ⟨f, hF⟩ : ∃ f, fuel = (f + 1) + k₃ := ⟨fuel - k₃ - 1, by omega⟩
    refine ⟨{ content, spaces := spaces₃, state := sc₃, terminated := true }, ?_, hc₃, hk₃,
      Nat.le_refl _⟩
    rw [hF, heq₃]
    have hfloor₃ : (n : Int) > sc₃.currentIndent := by rw [hk₃.currentIndent]; exact hfloor
    rcases hstop with hstop | ⟨hf, hbrk⟩ | ⟨hf, hbrk⟩
    · have hsp : hw = true → spaces₃.length > 0 := fun h => by
        have := hhw h; simp at hs₃; omega
      exact collectPlainScalarLoop_stops sc₃ content spaces₃ f inFlow ci ie hc₃ hstop hsp
    · subst hf
      have hie' : ie = sc₃.inputEnd := by rw [← hie, hk₃.2.1]
      subst hie'
      exact collectPlainScalarLoop_breakStop sc₃ hc₃ hbrk hfloor₃ (hci rfl) f content spaces₃
    · subst hf
      exact collectPlainScalarLoop_flowBreakStop sc₃ ie hc₃ hbrk hfloor₃ f content spaces₃
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content ci fuel ie sp'' hw hcorr hie hfloor hci hcol hwhite hstop hhw hfuel
    obtain ⟨_, s_ws, t₁, t₂, t₃, t₄, hws, hb, hblank, hpre, hhash, hdoc, hch, hent⟩ := hstep
    obtain ⟨scw, spaces', kw, heqw, hcw, hkw, hlw, _⟩ :=
      collectPlainScalarLoop_whites hws sc content "" inFlow ci ie hcorr hcol
    obtain ⟨hsp, htab, hnb⟩ := hch.landing_ok hhash
    have hl₁ := hb.length_lt
    have hl₂ := GStar_SLEmptyOk_length hblank
    have hl₃ := flowLinePrefix_length hpre
    obtain ⟨hl₄, hcol₄⟩ := hch.len_col
    have hfold : ∃ folded s', ScannerSurfCorr s' t₂ ∧ Keeps scw s' ∧
        ∀ result,
          collectPlainScalarLoop s' (content ++ folded) "" (fuel - kw - 1) inFlow ci ie =
            .ok result →
          result.content.length > (content ++ folded).length →
          collectPlainScalarLoop scw content spaces' (fuel - kw - 1 + 1) inFlow ci ie =
            .ok result := by
      cases inFlow with
      | false =>
        obtain ⟨k, s', hc', hk', hstepF⟩ :=
          collectPlainScalarLoop_blockFold_step scw content spaces' ci (fuel - kw - 1) hb hblank
            hpre hcw (by rw [hkw.currentIndent]; exact hfloor) hsp htab hnb hhash (hci rfl) hdoc
        rw [hkw.2.1, hie] at hstepF
        exact ⟨_, s', hc', hk', hstepF⟩
      | true =>
        obtain ⟨folded, s', hc', hk', hstepF⟩ :=
          collectPlainScalarLoop_flowFold_step scw content spaces' ci (fuel - kw - 1) ie hb hblank
            hpre hcw (by rw [hkw.currentIndent]; exact hfloor) hsp htab hnb hhash
        exact ⟨folded, s', hc', hk', hstepF⟩
    obtain ⟨folded, s', hc', hk', hstepF⟩ := hfold
    obtain ⟨c, heqc, hcc, hkc⟩ :=
      collectPlainScalarLoop_char_step s' _ "" ci ie hch hc'
        (fun _ => atDocumentBoundary_false_of_corr hc' hdoc) (fun _ => rfl)
    obtain ⟨sc₂, content₂, k₂, heq₂, hc₂, hk₂, hl₅, hcl₂, hlen₂⟩ :=
      collectPlainScalarLoop_entries hent s'.advance _ ci ie hcc (by omega)
    obtain ⟨result, hloop, hcr, hkr, hlr⟩ :=
      ih sc₂ content₂ ci (fuel - kw - 2 - k₂) ie sp'' hw hc₂
        (by rw [hk₂.2.1, hkc.2.1, hk'.2.1, hkw.2.1, hie])
        (by rw [((hkw.trans hk').trans (hkc.trans hk₂)).currentIndent]; exact hfloor)
        hci (by omega) hwhite hstop hhw (by omega)
    have hX : (content ++ folded ++ "" ++ String.singleton c).length =
        (content ++ folded).length + 1 := by
      simp [String.length_append]
    have hcf : content.length ≤ (content ++ folded).length := by simp [String.length_append]
    rw [hX] at hlen₂
    refine ⟨result, ?_, hcr, (((hkw.trans hk').trans hkc).trans hk₂).trans hkr, by omega⟩
    rw [show fuel = (fuel - kw - 1 + 1) + kw by omega, heqw]
    apply hstepF result
    · rw [show fuel - kw - 1 = (fuel - kw - 2 - k₂ + k₂) + 1 by omega, heqc, heq₂]; exact hloop
    · omega

/-- Multi-line plain-scalar converse, `[135]` narrowed, both contexts: a `PlainOneLineOk` first
    line, `PlainNextLineOk` continuation lines, the trailing white run, then an in-line
    `PlainStopOk` stop or a break the scanner rolls back to (`PlainBreakStopOk` in block context,
    `PlainFlowBreakStopOk` in flow context).  `hfloor`/`hci`: the continuation floor `n` clears
    the current indent and, in block context, the scanner's content indent (`"a\n b"` under
    indent 1 refutes the converse; in flow context it is a hard `underIndentedScalar`). -/
lemma scanPlainScalar_accepts_multi (sc : ScannerState) {n : Nat} {sp sp₁ sp' sp'' : SurfPos}
    {hadWhite : Bool}
    (hcorr : ScannerSurfCorr sc sp)
    (hder : PlainOneLineOk sc.inFlow sp sp₁)
    (hnext : GStar (PlainNextLineOk sc.inFlow n) sp₁ sp')
    (hwhite : GStar SSWhite sp' sp'')
    (hstop : PlainStopOk sc.inFlow hadWhite sp''.chars ∨
      (sc.inFlow = false ∧ PlainBreakStopOk n (max 0 (sc.currentIndent + 1)).toNat sp'') ∨
      (sc.inFlow = true ∧ PlainFlowBreakStopOk n sp''))
    (hhw : hadWhite = true → sp''.chars.length < sp'.chars.length)
    (hdoc : sc.col = 0 → atDocumentBoundary sc = false)
    (hfloor : (n : Int) > sc.currentIndent)
    (hci : sc.inFlow = false → (max 0 (sc.currentIndent + 1)).toNat ≤ n) :
    ∃ s' content, scanPlainScalar sc = .ok s' ∧ ScannerSurfCorr s' sp'' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .plain } := by
  have ⟨s₁, hf, hstar⟩ : ∃ s₁, PlainFirstOk sc.inFlow sp s₁ ∧
      GStar (PlainEntryOk sc.inFlow) s₁ sp₁ :=
    match sp, sp₁, hder with
    | _, _, .mk _ s₁ _ hf hstar => ⟨s₁, hf, hstar⟩
  have hfuel := fuel_of_corr hcorr
  obtain ⟨hl₁, hcol₁⟩ := hf.len_col
  obtain ⟨c, heq₁, hc₁, hk₁⟩ :=
    collectPlainScalarLoop_first_step sc (inFlow := sc.inFlow) (sp := sp) (sp' := s₁)
      (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd hf hcorr hdoc
  obtain ⟨sc₂, content₂, k₂, heq₂, hc₂, hk₂, hl₂, hcl₂, _⟩ :=
    collectPlainScalarLoop_entries hstar sc.advance (String.singleton c)
      (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd hc₁
      (by omega)
  have hstop' : PlainStopOk sc.inFlow hadWhite sp''.chars ∨
      (sc.inFlow = false ∧ PlainBreakStopOk n
        (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sp'') ∨
      (sc.inFlow = true ∧ PlainFlowBreakStopOk n sp'') := by
    rcases hstop with h | ⟨hf, h⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hf, by rw [hf]; simpa using h⟩)
    · exact Or.inr (Or.inr h)
  obtain ⟨⟨rc, rs, rst, rt⟩, hloop₃, hcr, hkr, _⟩ :=
    collectPlainScalarLoop_nextLines hnext sc₂ content₂
      (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat)
      ((sc.inputEnd - sc.offset + 1) * 2 - (k₂ + 1)) sc.inputEnd sp'' hadWhite hc₂
      (hk₁.trans hk₂).2.1 (by rw [(hk₁.trans hk₂).currentIndent]; exact hfloor)
      (fun hf => by rw [hf]; simpa using hci hf) (by omega) hwhite hstop' hhw (by omega)
  simp only at hcr hkr
  have hk := hk₁.trans (hk₂.trans hkr)
  have hloop : collectPlainScalarLoop sc "" "" ((sc.inputEnd - sc.offset + 1) * 2)
      sc.inFlow (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat) sc.inputEnd =
      .ok { content := rc, spaces := rs, state := rst, terminated := rt } := by
    rw [show (sc.inputEnd - sc.offset + 1) * 2 =
      (((sc.inputEnd - sc.offset + 1) * 2 - (k₂ + 1)) + k₂) + 1 by omega, heq₁, heq₂]
    exact hloop₃
  refine ⟨{ rst.emitAt sc.currentPos (.scalar (trimTrailingWS rc) .plain) with
      simpleKeyAllowed := false, needIndentCheck := false }, trimTrailingWS rc, ?_,
    corr_of_simpleKeyAllowed_needIndentCheck_update false false (corr_of_emitAt _ _ hcr), ?_⟩
  · unfold scanPlainScalar
    simp only [hloop, bind, Except.bind]
  · simp [ScannerState.emitAt, hk.1]

/-- `PlainNextLineOk n` is a sub-relation of `[134] s-ns-plain-next-line(n,BLOCK)`. -/
lemma PlainNextLineOk.toSSNsPlainNextLine {inFlow : Bool} {n : Nat} {s s' : SurfPos}
    (h : PlainNextLineOk inFlow n s s') : SSNsPlainNextLine n (ctxOfInFlow inFlow) s s' :=
  match s, s', h with
  | _, _, .mk s s_ws s₁ s₂ s₃ s₄ s' hws hb hblank hpre hhash _ hch hent =>
    SSNsPlainNextLine.mk n _ s s_ws s₁ s₂ s₃ s₄ s' hws hb.toSBBreak
      (GStar.imp' (fun _ _ he => he.toSLEmpty) hblank) hpre (hch.toSNsPlainChar hhash)
      (GStar.imp' (fun _ _ he => he.toEntry) hent)

/-- The hypotheses of `scanPlainScalar_accepts_multi` derive `[135] ns-plain-multi-line`. -/
lemma toSNsPlainMultiLine {inFlow : Bool} {n : Nat} {s s₁ s' : SurfPos}
    (h₁ : PlainOneLineOk inFlow s s₁) (h₂ : GStar (PlainNextLineOk inFlow n) s₁ s') :
    SNsPlainMultiLine n (ctxOfInFlow inFlow) s s' :=
  SNsPlainMultiLine.mk n _ s s₁ s' h₁.toSNsPlainOneLine
    (GStar.imp' (fun _ _ he => he.toSSNsPlainNextLine) h₂)

end L4YAML.Proofs.Acceptance

end Blanket
