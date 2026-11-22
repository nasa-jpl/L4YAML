/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.Acceptance.Quoted
public import L4YAML.Proofs.Production.StructureProduction

@[expose] public section Blanket

/-!
# Acceptance — node properties (Stream E)

Scanner converses of `scanAnchorOrAlias_prod`: a `[101]`/`[104]` derivation (`&`/`*` then a
non-empty, maximal `ns-anchor-char` run) at the scanner's position makes `scanAnchorOrAlias`
succeed, land after the name and emit the `.anchor`/`.alias` token.
-/

namespace L4YAML.Proofs.Acceptance

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.StructureProduction
open L4YAML.Grammar
open L4YAML.Proofs.CharClass
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction

/-- The scanner's anchor-character test, from `[102] ns-anchor-char`. -/
lemma isNsAnchorChar_scanner_cond {c : Char} (h : isNsAnchorChar c) :
    (!isFlowIndicatorBool c && !isWhiteSpaceBool c &&
      !isLineBreakBool c && isPrintableBool c && (c != '﻿')) = true := by
  obtain ⟨⟨hlb, hws, hpr, hbom⟩, hfi⟩ := h
  have h1 : isLineBreakBool c = false := by
    cases hb : isLineBreakBool c
    · rfl
    · exact absurd ((isLineBreak_correspondence c).mpr hb) hlb
  have h2 : isWhiteSpaceBool c = false := by
    cases hb : isWhiteSpaceBool c
    · rfl
    · exact absurd ((isWhiteSpace_correspondence c).mpr hb) hws
  have h3 : isFlowIndicatorBool c = false := by
    cases hb : isFlowIndicatorBool c
    · rfl
    · exact absurd ((isFlowIndicator_correspondence c).mpr hb) hfi
  have h4 : isPrintableBool c = true := (isPrintable_iff c).mpr hpr
  simp [h1, h2, h3, h4, hbom]

/-- The scanner's anchor-character test fails where `[102]` does. -/
lemma not_isNsAnchorChar_scanner_cond {c : Char} (h : ¬ isNsAnchorChar c) :
    (!isFlowIndicatorBool c && !isWhiteSpaceBool c &&
      !isLineBreakBool c && isPrintableBool c && (c != '﻿')) = false := by
  cases hb : (!isFlowIndicatorBool c && !isWhiteSpaceBool c &&
      !isLineBreakBool c && isPrintableBool c && (c != '﻿'))
  · rfl
  · exact absurd (isNsAnchorChar_of_scanner_cond hb) h

lemma GStar_GChar_length {p : Char → Prop} {s s' : SurfPos} (h : GStar (GChar p) s s') :
    s'.chars.length ≤ s.chars.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ _ _ hstep _ ih => cases hstep; simp only [List.length_cons] at ih ⊢; omega

lemma GPlus_toGStar {P : SurfPos → SurfPos → Prop} {s s' : SurfPos} (h : GPlus P s s') :
    GStar P s s' := by
  cases h with
  | mk _ _ hstep hrest => exact GStar.cons _ _ _ hstep hrest

lemma GPlus_length_lt {p : Char → Prop} {s s' : SurfPos} (h : GPlus (GChar p) s s') :
    s'.chars.length < s.chars.length := by
  cases h with
  | mk _ _ hstep hrest =>
    cases hstep; have := GStar_GChar_length hrest; simp only [List.length_cons] at this ⊢; omega

/-- `collectAnchorNameLoop` consumes exactly a maximal `ns-anchor-char` run. -/
lemma collectAnchorNameLoop_accepts {sp sp' : SurfPos} (h : GStar (GChar isNsAnchorChar) sp sp')
    (hmax : ∀ c, sp'.chars.head? = some c → ¬ isNsAnchorChar c) :
    ∀ (sc : ScannerState) (name : String) (fuel : Nat), ScannerSurfCorr sc sp →
      sp.chars.length ≤ fuel →
      ∃ sc' name', collectAnchorNameLoop sc name fuel = (name', sc') ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧
        name'.length = name.length + (sp.chars.length - sp'.chars.length) := by
  induction h with
  | nil s =>
    intro sc name fuel hcorr _
    refine ⟨sc, name, ?_, hcorr, Keeps.refl sc, by simp⟩
    cases fuel with
    | zero => rfl
    | succ f =>
      obtain ⟨chars, col⟩ := s
      cases chars with
      | nil => simp [collectAnchorNameLoop, peek_none_of_corr hcorr]
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        have hc := not_isNsAnchorChar_scanner_cond (hmax c rfl)
        simp [collectAnchorNameLoop, hpk, hc]
  | cons s₁ s₂ s₃ hstep hrest ih =>
    intro sc name fuel hcorr hfuel
    cases hstep with
    | mk c rest col hc =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        obtain ⟨⟨hlb, _, _, _⟩, _⟩ := hc
        have hadv := advance_corr hcorr
          (by intro h; subst h; exact hlb (by decide)) (by intro h; subst h; exact hlb (by decide))
        obtain ⟨sc', name', heq, hcorr', hk, hlen⟩ := ih hmax sc.advance (name.push c) f hadv
          (by dsimp only at hfuel ⊢; simp only [List.length_cons] at hfuel; omega)
        refine ⟨sc', name', ?_, hcorr', (keeps_advance sc).trans hk, ?_⟩
        · simp [collectAnchorNameLoop, hpk, isNsAnchorChar_scanner_cond ⟨⟨hlb, ‹_›, ‹_›, ‹_›⟩, ‹_›⟩, heq]
        · have := GStar_GChar_length hrest
          dsimp only at hlen this ⊢
          simp only [List.length_cons, String.length_push] at hlen ⊢; omega

/-- Converse of `scanAnchorOrAlias_prod`: the marker (`&`/`*`), then a non-empty maximal
    `[102] ns-anchor-char` run, is accepted and emitted as the `.anchor`/`.alias` token.
    `"&"`/`"& a"` (empty name → `emptyAnchorName`) refute the converse without `GPlus`. -/
lemma scanAnchorOrAlias_accepts (sc : ScannerState) (isAnchor : Bool) {marker : Char}
    {sp sp₁ sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hlit : GLit marker sp sp₁)
    (hname : GPlus (GChar isNsAnchorChar) sp₁ sp')
    (hmax : ∀ c, sp'.chars.head? = some c → ¬ isNsAnchorChar c)
    (hnl : marker ≠ '\n') (hcr : marker ≠ '\r') :
    ∃ s' name, scanAnchorOrAlias sc isAnchor = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push
        { pos := sc.currentPos, val := if isAnchor then .anchor name else .alias name } := by
  cases hlit with
  | mk rest col =>
    have hadv := advance_corr hcorr hnl hcr
    have hfuel := fuel_of_corr hadv
    have hlt := GPlus_length_lt hname
    have hie := (keeps_advance sc).2.1
    obtain ⟨sc', name', heq, hcorr', hk, hlen⟩ :=
      collectAnchorNameLoop_accepts (GPlus_toGStar hname) hmax sc.advance "" (sc.inputEnd - sc.advance.offset)
        hadv (by omega)
    have hne : name'.isEmpty = false := by
      dsimp only at hlen hlt
      simp only [String.length_empty, Nat.zero_add] at hlen
      cases hn : name'.isEmpty
      · rfl
      · have : name'.length = 0 := by simpa [String.isEmpty_iff] using hn
        omega
    have hc := corr_of_emitAt sc.currentPos
      (if isAnchor then YamlToken.anchor name' else YamlToken.alias name') hcorr'
    refine ⟨{ sc'.emitAt sc.currentPos
        (if isAnchor then YamlToken.anchor name' else YamlToken.alias name') with
        simpleKeyAllowed := false }, name', ?_,
      ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩, ?_⟩
    · unfold scanAnchorOrAlias
      simp only [heq, hne, Bool.false_eq_true, ite_false]
    · simp [ScannerState.emitAt, ((keeps_advance sc).trans hk).1]

/-- `collectTagSuffixLoop` consumes exactly a maximal `[40] ns-tag-char` run. -/
lemma collectTagSuffixLoop_accepts {sp sp' : SurfPos} (h : GStar (GChar isTagCharProp) sp sp')
    (hmax : ∀ c, sp'.chars.head? = some c → ¬ isTagCharProp c) :
    ∀ (sc : ScannerState) (suffix : String) (fuel : Nat), ScannerSurfCorr sc sp →
      sp.chars.length ≤ fuel →
      ∃ sc' suffix', collectTagSuffixLoop sc suffix fuel = (suffix', sc') ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  induction h with
  | nil s =>
    intro sc suffix fuel hcorr _
    refine ⟨sc, suffix, ?_, hcorr, Keeps.refl sc⟩
    cases fuel with
    | zero => rfl
    | succ f =>
      obtain ⟨chars, col⟩ := s
      cases chars with
      | nil => simp [collectTagSuffixLoop, peek_none_of_corr hcorr]
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        have hc : isTagCharBool c = false := by
          cases hb : isTagCharBool c
          · rfl
          · exact absurd ((isTagChar_iff c).mp hb) (hmax c rfl)
        simp [collectTagSuffixLoop, hpk, hc]
  | cons s₁ s₂ s₃ hstep hrest ih =>
    intro sc suffix fuel hcorr hfuel
    cases hstep with
    | mk c rest col hc =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        have hcb : isTagCharBool c = true := (isTagChar_iff c).mpr hc
        have hu : isUriCharBool c = true := (isUriChar_iff c).mpr hc.1
        have hnlb := isUriChar_not_isLineBreak c hu
        have hadv := advance_corr hcorr
          (by intro h; subst h; exact hnlb rfl) (by intro h; subst h; exact hnlb rfl)
        obtain ⟨sc', suffix', heq, hcorr', hk⟩ := ih hmax sc.advance (suffix.push c) f hadv
          (by dsimp only at hfuel ⊢; simp only [List.length_cons] at hfuel; omega)
        refine ⟨sc', suffix', ?_, hcorr', (keeps_advance sc).trans hk⟩
        simp [collectTagSuffixLoop, hpk, hcb, heq]

lemma wordChar_not_break {c : Char} (hw : isWordCharProp c) : c ≠ '\n' ∧ c ≠ '\r' := by
  have hu : isUriCharBool c = true :=
    (isUriChar_iff c).mpr (isWordCharProp_to_isTagCharProp hw).1
  have h := isUriChar_not_isLineBreak c hu
  exact ⟨by intro e; subst e; exact h rfl, by intro e; subst e; exact h rfl⟩

-- `hne` discharges the `some '!'` match arm; the linter does not see that use.
set_option linter.unusedSimpArgs false in
/-- `collectTagHandleLoop` on a maximal `[38] ns-word-char` run that is NOT closed by `!`:
    returns `foundBang = false` and stays at the run's end. -/
lemma collectTagHandleLoop_accepts_open {sp sp' : SurfPos} (h : GStar (GChar isWordCharProp) sp sp')
    (hmax : ∀ c, sp'.chars.head? = some c → ¬ isWordCharProp c ∧ c ≠ '!') :
    ∀ (sc : ScannerState) (chars : String) (fuel : Nat), ScannerSurfCorr sc sp →
      sp.chars.length ≤ fuel →
      ∃ sc' chars', collectTagHandleLoop sc chars fuel = (chars', false, sc') ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  induction h with
  | nil s =>
    intro sc chars fuel hcorr _
    refine ⟨sc, chars, ?_, hcorr, Keeps.refl sc⟩
    cases fuel with
    | zero => rfl
    | succ f =>
      obtain ⟨cs, col⟩ := s
      cases cs with
      | nil => simp [collectTagHandleLoop, peek_none_of_corr hcorr]
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        obtain ⟨hnw, _⟩ := hmax c rfl
        have hc : isWordCharBool c = false := by
          cases hb : isWordCharBool c
          · rfl
          · exact absurd ((isWordChar_iff c).mp hb) hnw
        simp [collectTagHandleLoop, hpk, hc]
  | cons s₁ s₂ s₃ hstep hrest ih =>
    intro sc chars fuel hcorr hfuel
    cases hstep with
    | mk c rest col hc =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        have hcb : isWordCharBool c = true := (isWordChar_iff c).mpr hc
        obtain ⟨hnl, hcr⟩ := wordChar_not_break hc
        have hadv := advance_corr hcorr hnl hcr
        obtain ⟨sc', chars', heq, hcorr', hk⟩ := ih hmax sc.advance (chars.push c) f hadv
          (by dsimp only at hfuel ⊢; simp only [List.length_cons] at hfuel; omega)
        refine ⟨sc', chars', ?_, hcorr', (keeps_advance sc).trans hk⟩
        have hne : c ≠ '!' := by
          intro e; subst e
          simp [isWordCharProp, isAsciiLetterProp] at hc
        simp [collectTagHandleLoop, hpk, hcb, heq, hne]

-- `hne` discharges the `some '!'` match arm; the linter does not see that use.
set_option linter.unusedSimpArgs false in
/-- `collectTagHandleLoop` on a `[38] ns-word-char` run closed by `!`: returns
    `foundBang = true` just past the `!`. -/
lemma collectTagHandleLoop_accepts_bang {sp sp₁ sp' : SurfPos}
    (h : GStar (GChar isWordCharProp) sp sp₁) (hbang : GLit '!' sp₁ sp') :
    ∀ (sc : ScannerState) (chars : String) (fuel : Nat), ScannerSurfCorr sc sp →
      sp.chars.length ≤ fuel →
      ∃ sc' chars', collectTagHandleLoop sc chars fuel = (chars', true, sc') ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  induction h with
  | nil s =>
    intro sc chars fuel hcorr hfuel
    cases hbang with
    | mk rest col =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        have hadv := advance_corr hcorr (by decide) (by decide)
        exact ⟨sc.advance, chars, by simp [collectTagHandleLoop, hpk], hadv, keeps_advance sc⟩
  | cons s₁ s₂ s₃ hstep hrest ih =>
    intro sc chars fuel hcorr hfuel
    cases hstep with
    | mk c rest col hc =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        have hcb : isWordCharBool c = true := (isWordChar_iff c).mpr hc
        obtain ⟨hnl, hcr⟩ := wordChar_not_break hc
        have hadv := advance_corr hcorr hnl hcr
        obtain ⟨sc', chars', heq, hcorr', hk⟩ := ih hbang sc.advance (chars.push c) f hadv
          (by dsimp only at hfuel ⊢; simp only [List.length_cons] at hfuel; omega)
        refine ⟨sc', chars', ?_, hcorr', (keeps_advance sc).trans hk⟩
        have hne : c ≠ '!' := by
          intro e; subst e
          simp [isWordCharProp, isAsciiLetterProp] at hc
        simp [collectTagHandleLoop, hpk, hcb, heq, hne]

-- `hne` discharges the `some '>'` match arm; the linter does not see that use.
set_option linter.unusedSimpArgs false in
/-- `collectVerbatimTagLoop` on a `[39] ns-uri-char` run closed by `>`: consumes the run and
    the `>`, reporting `foundClose = true`. -/
lemma collectVerbatimTagLoop_accepts {sp sp₁ sp' : SurfPos}
    (h : GStar (GChar isUriCharProp) sp sp₁) (hclose : GLit '>' sp₁ sp') :
    ∀ (sc : ScannerState) (uri : String) (fuel : Nat), ScannerSurfCorr sc sp →
      sp.chars.length ≤ fuel →
      ∃ sc' uri', collectVerbatimTagLoop sc uri fuel = (uri', true, sc') ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧
        uri'.length = uri.length + (sp.chars.length - sp₁.chars.length) := by
  induction h with
  | nil s =>
    intro sc uri fuel hcorr hfuel
    cases hclose with
    | mk rest col =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        have hadv := advance_corr hcorr (by decide) (by decide)
        exact ⟨sc.advance, uri, by simp [collectVerbatimTagLoop, hpk], hadv, keeps_advance sc,
          by simp⟩
  | cons s₁ s₂ s₃ hstep hrest ih =>
    intro sc uri fuel hcorr hfuel
    cases hstep with
    | mk c rest col hc =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        have hcb : isUriCharBool c = true := (isUriChar_iff c).mpr hc
        have hnlb := isUriChar_not_isLineBreak c hcb
        have hadv := advance_corr hcorr
          (by intro e; subst e; exact hnlb rfl) (by intro e; subst e; exact hnlb rfl)
        obtain ⟨sc', uri', heq, hcorr', hk, hlen⟩ := ih hclose sc.advance (uri.push c) f hadv
          (by dsimp only at hfuel ⊢; simp only [List.length_cons] at hfuel; omega)
        have hne : c ≠ '>' := by
          intro e; subst e
          simp [isUriCharProp, isWordCharProp, isAsciiLetterProp] at hc
        refine ⟨sc', uri', ?_, hcorr', (keeps_advance sc).trans hk, ?_⟩
        · simp [collectVerbatimTagLoop, hpk, hcb, heq, hne]
        · have := GStar_GChar_length hrest
          dsimp only at hlen this ⊢
          simp only [List.length_cons, String.length_push] at hlen ⊢; omega

/-! ## §4 Tag property `[97]` narrowed to the scanner

`SCNsTagProperty.primary` admits any `[40] ns-tag-char` suffix after a bare `!`, but
`scanNamedTag` only collects `[38] ns-word-char`s there (refuters `!%21`, `!a:b`:
the scanner stops at `%` / `:`).  `TagOk` is the narrowing; every arm ends at the
scanner's maximal landing. -/
inductive TagOk : SurfPos → SurfPos → Prop where
  | verbatim (rest : List Char) (col : Nat) (s₁ s₂ s' : SurfPos) :
      GLit '<' ⟨rest, col + 1⟩ s₁ →
      GPlus (GChar isUriCharProp) s₁ s₂ →
      GLit '>' s₂ s' →
      TagOk ⟨'!' :: rest, col⟩ s'
  | secondary (srest : List Char) (col : Nat) (s' : SurfPos) :
      GStar (GChar isTagCharProp) ⟨srest, col + 2⟩ s' →
      (∀ c, s'.chars.head? = some c → ¬ isTagCharProp c) →
      TagOk ⟨'!' :: '!' :: srest, col⟩ s'
  | named (rest : List Char) (col : Nat) (s₁ s₂ s' : SurfPos) :
      GPlus (GChar isWordCharProp) ⟨rest, col + 1⟩ s₁ →
      GLit '!' s₁ s₂ →
      GStar (GChar isTagCharProp) s₂ s' →
      (∀ c, s'.chars.head? = some c → ¬ isTagCharProp c) →
      TagOk ⟨'!' :: rest, col⟩ s'
  | primary (rest : List Char) (col : Nat) (s₁ s' : SurfPos) :
      GStar (GChar isWordCharProp) ⟨rest, col + 1⟩ s₁ →
      (∀ c, s₁.chars.head? = some c → ¬ isWordCharProp c ∧ c ≠ '!') →
      GStar (GChar isTagCharProp) s₁ s' →
      (∀ c, s'.chars.head? = some c → ¬ isTagCharProp c) →
      rest.head? ≠ some '<' →
      TagOk ⟨'!' :: rest, col⟩ s'

private lemma gstar_append_local {P : SurfPos → SurfPos → Prop} {a b c : SurfPos}
    (h₁ : GStar P a b) : GStar P b c → GStar P a c := by
  induction h₁ with
  | nil _ => exact id
  | cons s₁ s₂ _ hx _ ih => exact fun h => GStar.cons s₁ s₂ c hx (ih h)

private lemma gnot_gchar_of_hmax {P : Char → Prop} {sp : SurfPos}
    (h : ∀ c, sp.chars.head? = some c → ¬ P c) : GNot (GChar P) sp := by
  intro s' hg; cases hg with | mk c _ _ hp => exact h c rfl hp

/-- `TagOk` is a sub-relation of `[97] c-ns-tag-property`. -/
lemma TagOk.toSCNsTagProperty {s s' : SurfPos} (h : TagOk s s') : SCNsTagProperty s s' := by
  cases h with
  | verbatim rest col s₁ s₂ s' h₁ h₂ h₃ => exact .verbatim rest col s₁ s₂ s' h₁ h₂ h₃
  | secondary srest col s' h hmax => exact .secondary srest col s' h (gnot_gchar_of_hmax hmax)
  | named rest col s₁ s₂ s' h₁ h₂ h₃ hmax =>
    exact .named rest col s₁ s₂ s' h₁ h₂ h₃ (gnot_gchar_of_hmax hmax)
  | primary rest col s₁ s' h _ hsuf hmax _ =>
    have hfull := gstar_append_local (GStar_gchar_lift (fun _ => isWordCharProp_to_isTagCharProp) h) hsuf
    by_cases h_ne : (⟨rest, col + 1⟩ : SurfPos) = s'
    · subst h_ne; exact .nonSpecific rest col (gnot_gchar_of_hmax hmax)
    · exact .primary rest col s' (GStar_to_GPlus hfull h_ne) (gnot_gchar_of_hmax hmax)

lemma wordChar_ne_lt_bang {c : Char} (hw : isWordCharProp c) : c ≠ '<' ∧ c ≠ '!' := by
  refine ⟨?_, ?_⟩ <;> intro e <;> subst e <;>
    simp [isWordCharProp, isAsciiLetterProp] at hw

set_option linter.unusedSimpArgs false in
/-- Tag property converse: on a `TagOk` derivation `scanTag` succeeds, lands at `sp'`, and
    emits one `.tag` token at the start position. -/
lemma scanTag_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hder : TagOk sp sp') :
    ∃ s' handle suffix, scanTag sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .tag handle suffix } := by
  cases hder with
  | verbatim rest col s₁ s₂ s' hlt huri hgt =>
    have hadv₁ := advance_corr hcorr (by decide) (by decide)
    cases hlt with
    | mk rest₂ _ =>
      have hpk₁ := (peek_of_corr hadv₁).1
      have hadv₂ := advance_corr hadv₁ (by decide) (by decide)
      have hfuel := fuel_of_corr hadv₂
      have hlt := GPlus_length_lt huri
      obtain ⟨sc', uri', heq, hcorr', hk, hlen⟩ :=
        collectVerbatimTagLoop_accepts (GPlus_toGStar huri) hgt sc.advance.advance ""
          (sc.currentPos.offset + sc.advance.inputEnd - sc.advance.advance.offset) hadv₂
          (by have := (keeps_advance sc).2.1; have := (keeps_advance sc.advance).2.1; omega)
      have hne : uri'.isEmpty = false := by
        dsimp only at hlen hlt
        simp only [String.length_empty, Nat.zero_add] at hlen
        cases hn : uri'.isEmpty
        · rfl
        · have : uri'.length = 0 := by simpa [String.isEmpty_iff] using hn
          omega
      have hc := corr_of_emitAt sc.currentPos (YamlToken.tag "" uri') hcorr'
      refine ⟨{ sc'.emitAt sc.currentPos (YamlToken.tag "" uri') with
          simpleKeyAllowed := false }, "", uri', ?_,
        ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩, ?_⟩
      · simp [scanTag, hpk₁, scanVerbatimTag, heq, hne, Functor.map, Except.map]
      · simp [ScannerState.emitAt, (((keeps_advance sc).trans (keeps_advance sc.advance)).trans hk).1]
  | secondary srest col s' hsuf hmax =>
    have hadv₁ := advance_corr hcorr (by decide) (by decide)
    have hpk₁ := (peek_of_corr hadv₁).1
    have hadv₂ := advance_corr hadv₁ (by decide) (by decide)
    have hfuel := fuel_of_corr hadv₂
    obtain ⟨sc', suf', heq, hcorr', hk⟩ :=
      collectTagSuffixLoop_accepts hsuf hmax sc.advance.advance ""
        (sc.currentPos.offset + sc.advance.inputEnd - sc.advance.advance.offset) hadv₂
        (by have := (keeps_advance sc).2.1; have := (keeps_advance sc.advance).2.1
            dsimp only at hfuel ⊢; omega)
    have hc := corr_of_emitAt sc.currentPos (YamlToken.tag "!!" suf') hcorr'
    refine ⟨{ sc'.emitAt sc.currentPos (YamlToken.tag "!!" suf') with
        simpleKeyAllowed := false }, "!!", suf', ?_,
      ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩, ?_⟩
    · simp [scanTag, hpk₁, scanSecondaryTag, heq]
    · simp [ScannerState.emitAt, (((keeps_advance sc).trans (keeps_advance sc.advance)).trans hk).1]
  | named rest col s₁ s₂ s' hhand hbang hsuf hmax =>
    have hadv₁ := advance_corr hcorr (by decide) (by decide)
    have hfuel := fuel_of_corr hadv₁
    obtain ⟨sc₁, chars', heq₁, hcorr₁, hk₁⟩ :=
      collectTagHandleLoop_accepts_bang (GPlus_toGStar hhand) hbang sc.advance ""
        (sc.inputEnd - sc.advance.offset) hadv₁ (by have := (keeps_advance sc).2.1; omega)
    have hfuel₂ := fuel_of_corr hcorr₁
    have hie₁ : sc₁.inputEnd = sc.inputEnd := by
      have h1 := hk₁.2.1; have h2 := (keeps_advance sc).2.1; omega
    obtain ⟨sc₂, suf', heq₂, hcorr₂, hk₂⟩ :=
      collectTagSuffixLoop_accepts hsuf hmax sc₁ "" (sc.inputEnd - sc₁.offset) hcorr₁ (by omega)
    have hpk₁ : ∃ c, sc.advance.peek? = some c ∧ c ≠ '<' ∧ c ≠ '!' := by
      cases hhand with
      | mk _ _ hstep _ =>
        cases hstep with
        | mk c _ _ hc => exact ⟨c, (peek_of_corr hadv₁).1, wordChar_ne_lt_bang hc⟩
    obtain ⟨c, hpk₁, hne₁, hne₂⟩ := hpk₁
    have hc := corr_of_emitAt sc.currentPos (YamlToken.tag ("!" ++ chars' ++ "!") suf') hcorr₂
    refine ⟨{ sc₂.emitAt sc.currentPos (YamlToken.tag ("!" ++ chars' ++ "!") suf') with
        simpleKeyAllowed := false }, "!" ++ chars' ++ "!", suf', ?_,
      ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩, ?_⟩
    · simp [scanTag, hpk₁, hne₁, hne₂, scanNamedTag, heq₁, heq₂]
    · simp [ScannerState.emitAt, (((keeps_advance sc).trans hk₁).trans hk₂).1]
  | primary rest col s₁ s' hhand hmax hsuf hmax₂ hlt =>
    have hadv₁ := advance_corr hcorr (by decide) (by decide)
    have hfuel := fuel_of_corr hadv₁
    obtain ⟨sc₁, chars', heq₁, hcorr₁, hk₁⟩ :=
      collectTagHandleLoop_accepts_open hhand hmax sc.advance ""
        (sc.inputEnd - sc.advance.offset) hadv₁ (by have := (keeps_advance sc).2.1; omega)
    have hfuel₂ := fuel_of_corr hcorr₁
    have hie₁ : sc₁.inputEnd = sc.inputEnd := by
      have h1 := hk₁.2.1; have h2 := (keeps_advance sc).2.1; omega
    obtain ⟨sc₂, suf', heq₂, hcorr₂, hk₂⟩ :=
      collectTagSuffixLoop_accepts hsuf hmax₂ sc₁ chars' (sc.inputEnd - sc₁.offset) hcorr₁ (by omega)
    have hc := corr_of_emitAt sc.currentPos (YamlToken.tag "!" suf') hcorr₂
    refine ⟨{ sc₂.emitAt sc.currentPos (YamlToken.tag "!" suf') with
        simpleKeyAllowed := false }, "!", suf', ?_,
      ⟨hc.chars_from, hc.col_eq, hc.end_eq, hc.input_prefix, hc.indent_cols_nonneg⟩, ?_⟩
    · cases rest with
      | nil =>
        have hpk₁ := peek_none_of_corr hadv₁
        simp [scanTag, hpk₁, scanNamedTag, heq₁, heq₂]
      | cons c tl =>
        have hpk₁ := (peek_of_corr hadv₁).1
        have hne₁ : c ≠ '<' := by intro e; subst e; exact hlt rfl
        have hne₂ : c ≠ '!' := by
          cases hhand with
          | nil _ => exact (hmax c rfl).2
          | cons _ _ _ hstep _ =>
            cases hstep with
            | mk _ _ _ hc => exact (wordChar_ne_lt_bang hc).2
        simp [scanTag, hpk₁, hne₁, hne₂, scanNamedTag, heq₁, heq₂]
    · simp [ScannerState.emitAt, (((keeps_advance sc).trans hk₁).trans hk₂).1]

end L4YAML.Proofs.Acceptance

end Blanket
