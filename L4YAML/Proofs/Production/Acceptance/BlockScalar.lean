/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Production.Acceptance.Plain

@[expose] public section Blanket

/-! # Acceptance (scanner converse) for block scalars

    The inverse of `scanBlockScalar_prod`, modulo `[162] c-b-block-header` (a separate
    hypothesis, `BlockHeaderOk`) and the content indent `n` (explicit, or the scanner's
    auto-detection — a state-side hypothesis).  `SLLiteralContent n` is STRICTLY wider
    than the scanner; refuters of the bare converse:
    * `|⏎  a⏎ b` — `[171]` at n = 1 derives both lines, the scanner detects 2 and stops
      at ` b`; hence `n` is pinned to the detected indent.
    * `|⏎a⏎---` — `[171]` at n = 0 derives `---`, the scanner stops at the document
      marker (`NotDocMarker` per content line).
    * `|⏎ a⏎# c` — `[169] l-trail-comments` is NOT consumed: the scanner stops before `#`.
    * `|x`, `|#c`, `|--` — `[162]` junk / unseparated comment / repeated indicator
      (`expectedNewline`).
    * `|⏎ a⏎  b⏎→c` — a tab where `s-indent(n)` is required (`tabInIndentation`). -/

namespace L4YAML.Proofs.Acceptance

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Grammar

/-! ## §1 `[63] s-indent` and one line of content -/

/-- `consumeExactSpaces` reads exactly an `SIndent n`. -/
lemma consumeExactSpaces_accepts {n : Nat} {sp sp' : SurfPos} (h : SIndent n sp sp') :
    ∀ sc : ScannerState, ScannerSurfCorr sc sp →
      ∃ sc', consumeExactSpaces sc n = (n, sc') ∧ ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  induction h with
  | zero s => intro sc hcorr; exact ⟨sc, rfl, hcorr, Keeps.refl sc⟩
  | succ n rest col s' _ ih =>
    intro sc hcorr
    have hpk := (peek_of_corr hcorr).1
    obtain ⟨sc', heq, hc', hk⟩ := ih sc.advance (advance_corr hcorr (by decide) (by decide))
    refine ⟨sc', ?_, hc', (keeps_advance sc).trans hk⟩
    simp [consumeExactSpaces, hpk, heq]

/-- The characters `collectLineContentLoop` consumes: `[27] nb-char` as the scanner reads
    it (printable, not a break, not the BOM). -/
def LineCharOk (c : Char) : Prop :=
  isLineBreakBool c = false ∧ isPrintableBool c = true ∧ c ≠ '\uFEFF'

lemma lineCharOk_cond {c : Char} (h : LineCharOk c) :
    (isLineBreakBool c || !isPrintableBool c || c == '\uFEFF') = false := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [h1, h2, h3]

lemma not_lineCharOk_cond {c : Char} (h : ¬ LineCharOk c) :
    (isLineBreakBool c || !isPrintableBool c || c == '\uFEFF') = true := by
  unfold LineCharOk at h
  by_cases h1 : isLineBreakBool c = false
  · by_cases h2 : isPrintableBool c = true
    · have h3 : c = '\uFEFF' := by
        by_cases h3 : c = '\uFEFF'
        · exact h3
        · exact absurd ⟨h1, h2, h3⟩ h
      simp [h3]
    · simp [Bool.not_eq_true] at h2; simp [h2]
  · simp [Bool.not_eq_false] at h1; simp [h1]

/-- `collectLineContentLoop` reads a maximal `LineCharOk` run. -/
lemma collectLineContentLoop_accepts {sp sp' : SurfPos} (h : GStar (GChar LineCharOk) sp sp')
    (hmax : ∀ c, sp'.chars.head? = some c → ¬ LineCharOk c) :
    ∀ (sc : ScannerState) (content : String) (fuel : Nat),
      ScannerSurfCorr sc sp → sp.chars.length ≤ fuel →
      ∃ sc' content', collectLineContentLoop sc content fuel = (content', sc') ∧
        ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  induction h with
  | nil s =>
    intro sc content fuel hcorr _
    refine ⟨sc, content, ?_, hcorr, Keeps.refl sc⟩
    cases fuel with
    | zero => rfl
    | succ f =>
      obtain ⟨chars, col⟩ := s
      cases chars with
      | nil => simp [collectLineContentLoop, peek_none_of_corr hcorr]
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        simp [collectLineContentLoop, hpk, not_lineCharOk_cond (hmax c rfl)]
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc content fuel hcorr hfuel
    cases hstep with
    | mk c rest col hc =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        have hnl : c ≠ '\n' := by intro e; subst e; exact absurd hc.1 (by decide)
        have hcr : c ≠ '\r' := by intro e; subst e; exact absurd hc.1 (by decide)
        obtain ⟨sc', content', heq, hc', hk⟩ :=
          ih hmax sc.advance (content.push c) f (advance_corr hcorr hnl hcr)
            (by dsimp only at hfuel ⊢; simp only [List.length_cons] at hfuel; omega)
        refine ⟨sc', content', ?_, hc', (keeps_advance sc).trans hk⟩
        simp [collectLineContentLoop, hpk, lineCharOk_cond hc, heq]

/-- `consumeExactSpaces` asked for `n` but finding only `k < n` spaces reads exactly them. -/
lemma consumeExactSpaces_short {k : Nat} {sp sp' : SurfPos} (h : SIndent k sp sp') :
    ∀ (n : Nat) (sc : ScannerState), k < n → ScannerSurfCorr sc sp → sp'.chars.head? ≠ some ' ' →
      ∃ sc', consumeExactSpaces sc n = (k, sc') ∧ ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  induction h with
  | zero s =>
    intro n sc hk hcorr hsp
    refine ⟨sc, ?_, hcorr, Keeps.refl sc⟩
    cases n with
    | zero => omega
    | succ m =>
      obtain ⟨chars, col⟩ := s
      cases chars with
      | nil => simp [consumeExactSpaces, peek_none_of_corr hcorr]
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        have hc : c ≠ ' ' := fun e => hsp (by simp [e])
        simp only [consumeExactSpaces, hpk]
        split
        · rename_i e; exact absurd (Option.some.inj e) hc
        · rfl
  | succ k rest col s' _ ih =>
    intro n sc hk hcorr hsp
    cases n with
    | zero => omega
    | succ m =>
      have hpk := (peek_of_corr hcorr).1
      obtain ⟨sc', heq, hc', hk'⟩ :=
        ih m sc.advance (by omega) (advance_corr hcorr (by decide) (by decide)) hsp
      refine ⟨sc', ?_, hc', (keeps_advance sc).trans hk'⟩
      simp [consumeExactSpaces, hpk, heq]

lemma atDocBoundary_false_of_corr {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hnd : NotDocMarker sp) : atDocumentBoundary sc = false := by
  simp [atDocumentBoundary, atDocumentStart_false_of_corr hcorr hnd,
    atDocumentEnd_false_of_corr hcorr hnd]

/-! ## §2 Content lines and the loop's stops -/

/-- One line `collectBlockScalarLoop` folds at indent `n` and continues past: a blank line
    (at most `n` spaces, then a break) or `s-indent(n)` + a maximal non-empty `LineCharOk`
    run + a break; never a document marker at column 0. -/
inductive BlockLineOk (n : Nat) : SurfPos → SurfPos → Prop where
  | blank (k : Nat) (s s₁ s' : SurfPos) :
      NotDocMarker s → k ≤ n → SIndent k s s₁ → SBBreakOk s₁ s' → BlockLineOk n s s'
  | content (s s₁ s₂ s' : SurfPos) :
      NotDocMarker s → SIndent n s s₁ → GPlus (GChar LineCharOk) s₁ s₂ →
      SBBreakOk s₂ s' → BlockLineOk n s s'

/-- Where `collectBlockScalarLoop` stops at indent `n`, and where it lands: end of input
    after a partial indent or a last line; a less-indented line (landing at its start — a
    tab there is the scanner's `tabInIndentation`); a non-`LineCharOk`, non-break
    character after a line; a document marker at column 0 (`|⏎a⏎---`: the loop stops
    before it). -/
inductive BlockStopOk (n : Nat) : SurfPos → SurfPos → Prop where
  | eofShort (k : Nat) (s s' : SurfPos) :
      NotDocMarker s → k < n → SIndent k s s' → s'.chars = [] → BlockStopOk n s s'
  | eofLine (s s₁ s' : SurfPos) :
      NotDocMarker s → SIndent n s s₁ → GStar (GChar LineCharOk) s₁ s' → s'.chars = [] →
      BlockStopOk n s s'
  | outdent (k : Nat) (s s₁ : SurfPos) (c : Char) :
      NotDocMarker s → k < n → SIndent k s s₁ → s₁.chars.head? = some c →
      isLineBreakBool c = false → c ≠ ' ' → c ≠ '\t' → BlockStopOk n s s
  | badChar (s s₁ s' : SurfPos) (c : Char) :
      NotDocMarker s → SIndent n s s₁ → GPlus (GChar LineCharOk) s₁ s' →
      s'.chars.head? = some c → isLineBreakBool c = false → ¬ LineCharOk c →
      BlockStopOk n s s'
  | docMarker (s : SurfPos) : DocMarkerAt s → s.col = 0 → BlockStopOk n s s

lemma SIndent.length_le {k : Nat} {s s' : SurfPos} (h : SIndent k s s') :
    s'.chars.length + k = s.chars.length := by
  induction h with
  | zero s => rfl
  | succ k rest col s' _ ih => dsimp only at ih ⊢; simp only [List.length_cons]; omega

lemma GStar_lineChar_length {s s' : SurfPos} (h : GStar (GChar LineCharOk) s s') :
    s'.chars.length ≤ s.chars.length := by
  induction h with
  | nil s => exact Nat.le_refl _
  | cons s₁ s₂ s₃ hstep _ ih => cases hstep; simp only [List.length_cons] at ih ⊢; omega

lemma GPlus_lineChar_length_lt {s s' : SurfPos} (h : GPlus (GChar LineCharOk) s s') :
    s'.chars.length < s.chars.length := by
  cases h with
  | mk _ _ hstep hrest => cases hstep; have := GStar_lineChar_length hrest; simp only [List.length_cons] at this ⊢; omega

/-- The stop of `collectBlockScalarLoop` on a `BlockStopOk` landing (one iteration). -/
lemma collectBlockScalarLoop_stops (sc : ScannerState) {n : Nat} {sp sp' : SurfPos}
    (hstop : BlockStopOk n sp sp') (hcorr : ScannerSurfCorr sc sp) (raw : String)
    (fuel ie : Nat) (hie : sc.inputEnd = ie) :
    ScannerSurfCorr (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 sp' ∧
      Keeps sc (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 := by
  cases hstop with
  | eofShort k s s' hnd hk hind heof =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_short hind n sc hk hcorr (by simp [heof])
    have hdb := atDocBoundary_false_of_corr hcorr hnd
    obtain ⟨chars, col⟩ := sp'
    simp only at heof; subst heof
    have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc₁ := by
      simp [collectBlockScalarLoop, hdb, heq, peek_none_of_corr hc₁]
    rw [hres]; exact ⟨hc₁, hk₁⟩
  | docMarker s hm h0 =>
    have hdb := atDocumentBoundary_true_of_marker hcorr hm h0
    have hcol : (sc.col == 0) = true := by have := hcorr.col_eq; simp; omega
    have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc := by
      simp [collectBlockScalarLoop, hdb, hcol]
    rw [hres]; exact ⟨hcorr, Keeps.refl sc⟩
  | eofLine s s₁ s' hnd hind hrun heof =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_accepts hind sc hcorr
    have hdb := atDocBoundary_false_of_corr hcorr hnd
    obtain ⟨chars, col⟩ := sp'
    simp only at heof; subst heof
    cases hrun with
    | nil _ =>
      have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc₁ := by
        simp [collectBlockScalarLoop, hdb, heq, peek_none_of_corr hc₁]
      rw [hres]; exact ⟨hc₁, hk₁⟩
    | cons _ s₂ _ hstep hrest =>
      cases hstep with
      | mk c rest col₁ hc =>
        have hmax : ∀ c, (⟨[], col⟩ : SurfPos).chars.head? = some c → ¬ LineCharOk c := by
          intro c hc; simp at hc
        obtain ⟨sc₂, content, heq₂, hc₂, hk₂⟩ :=
          collectLineContentLoop_accepts (GStar.cons _ _ _ (GChar.mk c rest col₁ hc) hrest) hmax
            sc₁ "" (ie - sc₁.offset + 1) hc₁
            (by have := fuel_of_corr hc₁; rw [hk₁.2.1, hie] at this; omega)
        have hpk := (peek_of_corr hc₁).1
        have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc₂ := by
          simp [collectBlockScalarLoop, hdb, heq, hpk, hc.1, heq₂, peek_none_of_corr hc₂]
        rw [hres]; exact ⟨hc₂, hk₁.trans hk₂⟩
  | outdent k s s₁ c hnd hk hind hhead hnb hsp htab =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_short hind n sc hk hcorr (by simp [hhead, hsp])
    have hdb := atDocBoundary_false_of_corr hcorr hnd
    obtain ⟨chars, col⟩ := s₁
    cases chars with
    | nil => simp at hhead
    | cons d tl =>
      simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      have hpk := (peek_of_corr hc₁).1
      have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc := by
        simp [collectBlockScalarLoop, hdb, heq, hpk, hnb, hk]
      rw [hres]; exact ⟨hcorr, Keeps.refl sc⟩
  | badChar s s₁ s' c hnd hind hrun hhead hnb hbad =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_accepts hind sc hcorr
    have hdb := atDocBoundary_false_of_corr hcorr hnd
    have hmax : ∀ d, sp'.chars.head? = some d → ¬ LineCharOk d := by
      intro d hd; rw [hhead] at hd; cases hd; exact hbad
    have hrun' : GStar (GChar LineCharOk) s₁ sp' :=
      match hrun with | .mk _ _ _ h₁ h₂ => .cons _ _ _ h₁ h₂
    obtain ⟨sc₂, content, heq₂, hc₂, hk₂⟩ :=
      collectLineContentLoop_accepts hrun' hmax sc₁ "" (ie - sc₁.offset + 1) hc₁
        (by have := fuel_of_corr hc₁; rw [hk₁.2.1, hie] at this; omega)
    obtain ⟨s₂, hstep, hrest⟩ :
        ∃ s₂, GChar LineCharOk s₁ s₂ ∧ GStar (GChar LineCharOk) s₂ sp' :=
      match hrun with | .mk _ s₂ _ h₁ h₂ => ⟨s₂, h₁, h₂⟩
    obtain ⟨chars, col⟩ := sp'
    cases chars with
    | nil => simp at hhead
    | cons d tl =>
      simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      have hpk₂ := (peek_of_corr hc₂).1
      cases hstep with
      | mk e rest col₁ he =>
        have hpk := (peek_of_corr hc₁).1
        -- the line run is non-empty, so the loop keeps `s_after_line`
        have hne : content.isEmpty = false := by
          have h := collectLineContentLoop_fst_nonempty sc₁ e "" (ie - sc₁.offset + 1) hpk
            (by simp [he.1]) he.2.1 (by simpa using he.2.2) (by omega)
          rw [heq₂] at h; exact h
        have hres : (collectBlockScalarLoop sc raw (fuel + 1) n ie).2 = sc₂ := by
          simp [collectBlockScalarLoop, hdb, heq, hpk, he.1, heq₂, hpk₂, hnb, hne]
        rw [hres]; exact ⟨hc₂, hk₁.trans hk₂⟩

lemma BlockLineOk.length_lt {n : Nat} {s s' : SurfPos} (h : BlockLineOk n s s') :
    s'.chars.length < s.chars.length := by
  cases h with
  | blank k _ s₁ _ _ _ hind hb => have := SIndent.length_le hind; have := hb.length_lt; omega
  | content _ s₁ s₂ _ _ hind hrun hb =>
    have := SIndent.length_le hind; have := GPlus_lineChar_length_lt hrun; have := hb.length_lt; omega

/-- One `BlockLineOk` line is folded and the loop continues on the rest. -/
lemma collectBlockScalarLoop_line_step (sc : ScannerState) {n : Nat} {sp sp' : SurfPos}
    (hline : BlockLineOk n sp sp') (hcorr : ScannerSurfCorr sc sp) (raw : String)
    (fuel ie : Nat) (hie : sc.inputEnd = ie) :
    ∃ sc' raw', ScannerSurfCorr sc' sp' ∧ Keeps sc sc' ∧
      collectBlockScalarLoop sc raw (fuel + 1) n ie = collectBlockScalarLoop sc' raw' fuel n ie := by
  have hdb := atDocBoundary_false_of_corr hcorr (by cases hline <;> assumption)
  cases hline with
  | blank k s s₁ s' hnd hk hind hb =>
    obtain ⟨c, rest, hs₁, hlb⟩ := hb.head
    have hns : s₁.chars.head? ≠ some ' ' := by
      rw [hs₁]; intro e; simp at e; subst e; exact absurd hlb (by decide)
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ : ∃ sc₁, consumeExactSpaces sc n = (k, sc₁) ∧
        ScannerSurfCorr sc₁ s₁ ∧ Keeps sc sc₁ := by
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · exact consumeExactSpaces_short hind n sc hlt hcorr hns
      · subst heq; exact consumeExactSpaces_accepts hind sc hcorr
    obtain ⟨chars, col⟩ := s₁
    simp only at hs₁; subst hs₁
    have hpk := (peek_of_corr hc₁).1
    obtain ⟨hc₂, hk₂⟩ := consumeNewline_accepts sc₁ hb hc₁
    refine ⟨consumeNewline sc₁, raw.push '\n', hc₂, hk₁.trans hk₂, ?_⟩
    simp [collectBlockScalarLoop, hdb, heq, hpk, hlb]
  | content s s₁ s₂ s' hnd hind hrun hb =>
    obtain ⟨sc₁, heq, hc₁, hk₁⟩ := consumeExactSpaces_accepts hind sc hcorr
    obtain ⟨c, rest, hs₂, hlb⟩ := hb.head
    have hmax : ∀ d, s₂.chars.head? = some d → ¬ LineCharOk d := by
      intro d hd; rw [hs₂] at hd; cases hd; intro h; rw [h.1] at hlb; cases hlb
    obtain ⟨sc₂, content, heq₂, hc₂, hk₂⟩ :=
      collectLineContentLoop_accepts (GPlus.toGStar hrun) hmax sc₁ "" (ie - sc₁.offset + 1) hc₁
        (by have := fuel_of_corr hc₁; rw [hk₁.2.1, hie] at this; omega)
    cases hrun with
    | mk _ _ hstep hrest =>
      cases hstep with
      | mk e rest₁ col₁ he =>
        have hpk := (peek_of_corr hc₁).1
        obtain ⟨chars, col⟩ := s₂
        simp only at hs₂; subst hs₂
        have hpk₂ := (peek_of_corr hc₂).1
        obtain ⟨hc₃, hk₃⟩ := consumeNewline_accepts sc₂ hb hc₂
        refine ⟨consumeNewline sc₂, (raw ++ content).push '\n', hc₃, (hk₁.trans hk₂).trans hk₃, ?_⟩
        simp [collectBlockScalarLoop, hdb, heq, hpk, he.1, heq₂, hpk₂, hlb]

/-- Converse of `collectBlockScalarLoop_literal_prod`: `BlockLineOk n` lines then a
    `BlockStopOk n` stop are read, landing at the stop's position. -/
lemma collectBlockScalarLoop_accepts {n : Nat} {sp sp' : SurfPos}
    (hlines : GStar (BlockLineOk n) sp sp') :
    ∀ (sc : ScannerState) (raw : String) (fuel ie : Nat) (sp'' : SurfPos),
      ScannerSurfCorr sc sp → sc.inputEnd = ie → BlockStopOk n sp' sp'' →
      sp.chars.length < fuel →
      ScannerSurfCorr (collectBlockScalarLoop sc raw fuel n ie).2 sp'' ∧
        Keeps sc (collectBlockScalarLoop sc raw fuel n ie).2 := by
  induction hlines with
  | nil s =>
    intro sc raw fuel ie sp'' hcorr hie hstop hfuel
    cases fuel with
    | zero => omega
    | succ f => exact collectBlockScalarLoop_stops sc hstop hcorr raw f ie hie
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc raw fuel ie sp'' hcorr hie hstop hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      obtain ⟨sc', raw', hc', hk', heq⟩ := collectBlockScalarLoop_line_step sc hstep hcorr raw f ie hie
      have hlt := hstep.length_lt
      obtain ⟨h1, h2⟩ := ih sc' raw' f ie sp'' hc' (by rw [hk'.2.1, hie]) hstop (by omega)
      rw [heq]; exact ⟨h1, hk'.trans h2⟩

/-! ## §3 `[162] c-b-block-header` as the scanner reads it -/

/-- `[164]`: the chomping style `parseBlockHeaderLoop` records for an optional `-`/`+`. -/
inductive ChompOk : ChompStyle → SurfPos → SurfPos → Prop where
  | clip (s : SurfPos) : ChompOk .clip s s
  | strip (rest : List Char) (col : Nat) : ChompOk .strip ⟨'-' :: rest, col⟩ ⟨rest, col + 1⟩
  | keep (rest : List Char) (col : Nat) : ChompOk .keep ⟨'+' :: rest, col⟩ ⟨rest, col + 1⟩

/-- `[163]`: the explicit offset `parseBlockHeaderLoop` records for an optional digit `1`–`9`. -/
inductive IndentOk : Option Nat → SurfPos → SurfPos → Prop where
  | auto (s : SurfPos) : IndentOk none s s
  | digit (d : Char) (rest : List Char) (col : Nat) (h1 : '1' ≤ d) (h9 : d ≤ '9') :
      IndentOk (some (d.toNat - '0'.toNat)) ⟨d :: rest, col⟩ ⟨rest, col + 1⟩

/-- The indicators of `[162]`: at most one of each kind, in either order. -/
inductive HeaderIndicatorsOk : ChompStyle → Option Nat → SurfPos → SurfPos → Prop where
  | indentFirst (chomp : ChompStyle) (m : Option Nat) (s s₁ s' : SurfPos) :
      IndentOk m s s₁ → ChompOk chomp s₁ s' → HeaderIndicatorsOk chomp m s s'
  | chompFirst (chomp : ChompStyle) (m : Option Nat) (s s₁ s' : SurfPos) :
      ChompOk chomp s s₁ → IndentOk m s₁ s' → HeaderIndicatorsOk chomp m s s'

/-- Comment text as `collectCommentTextLoop` reads it: anything up to a break. -/
def CommentCharOk (c : Char) : Prop := isLineBreakBool c = false

/-- The header line after the indicators: `skipWhitespace`'s maximal white run, then the
    break `scanBlockScalarConsumeNewline` takes (or EOF); or, only after at least one white,
    a `#` comment running to that break (or EOF). -/
inductive HeaderTailOk : SurfPos → SurfPos → Prop where
  | break_ (s s₁ s' : SurfPos) : GStar SSWhite s s₁ → SBBreakOk s₁ s' → HeaderTailOk s s'
  | eof (s : SurfPos) (col : Nat) : GStar SSWhite s ⟨[], col⟩ → HeaderTailOk s ⟨[], col⟩
  | commentBreak (s s₂ s' : SurfPos) (rest : List Char) (col : Nat) :
      GPlus SSWhite s ⟨'#' :: rest, col⟩ → GStar (GChar CommentCharOk) ⟨rest, col + 1⟩ s₂ →
      SBBreakOk s₂ s' → HeaderTailOk s s'
  | commentEof (s : SurfPos) (rest : List Char) (col col' : Nat) :
      GPlus SSWhite s ⟨'#' :: rest, col⟩ →
      GStar (GChar CommentCharOk) ⟨rest, col + 1⟩ ⟨[], col'⟩ → HeaderTailOk s ⟨[], col'⟩

/-- A header tail starts with white, a break, `#`, or EOF — never a header indicator. -/
def TailHead (c : Char) : Prop := c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r' ∨ c = '#'

lemma GStar_SSWhite_head {s s' : SurfPos} (hw : GStar SSWhite s s')
    (hs' : ∀ c, s'.chars.head? = some c → TailHead c) :
    ∀ c, s.chars.head? = some c → TailHead c := by
  cases hw with
  | nil _ => exact hs'
  | cons _ _ _ hstep _ =>
    cases hstep with
    | space rest col => intro c hc; simp at hc; subst hc; exact Or.inl rfl
    | tab rest col => intro c hc; simp at hc; subst hc; exact Or.inr (Or.inl rfl)

lemma lineBreak_cases {c : Char} (h : isLineBreakBool c = true) : c = '\n' ∨ c = '\r' := by
  simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool, Bool.or_eq_true,
    beq_iff_eq] at h
  exact h

lemma HeaderTailOk.head {s s' : SurfPos} (h : HeaderTailOk s s') :
    ∀ c, s.chars.head? = some c → TailHead c := by
  cases h with
  | break_ s₁ s' hw hb =>
    refine GStar_SSWhite_head hw ?_
    obtain ⟨c, rest, hc, hlb⟩ := hb.head
    intro d hd; rw [hc] at hd; simp at hd; subst hd
    rcases lineBreak_cases hlb with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | eof col hw => exact GStar_SSWhite_head hw (by intro c hc; simp at hc)
  | commentBreak s₂ s' rest col hw _ _ =>
    cases hw with
    | mk _ _ hstep _ =>
      cases hstep with
      | space rest col => intro c hc; simp at hc; subst hc; exact Or.inl rfl
      | tab rest col => intro c hc; simp at hc; subst hc; exact Or.inr (Or.inl rfl)
  | commentEof rest col col' hw _ =>
    cases hw with
    | mk _ _ hstep _ =>
      cases hstep with
      | space rest col => intro c hc; simp at hc; subst hc; exact Or.inl rfl
      | tab rest col => intro c hc; simp at hc; subst hc; exact Or.inr (Or.inl rfl)

/-! ## §4 Reading the header -/

lemma digit_facts {d : Char} (h1 : '1' ≤ d) (h9 : d ≤ '9') :
    d.isDigit = true ∧ d ≠ '0' ∧ d ≠ '-' ∧ d ≠ '+' ∧ d ≠ '\n' ∧ d ≠ '\r' := by
  have h1' : (49 : UInt32) ≤ d.val := h1
  have h9' : d.val ≤ 57 := h9
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Char.isDigit, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨UInt32.le_trans (by decide) h1', h9'⟩
  all_goals (rintro rfl; first | exact absurd h1 (by decide) | exact absurd h9 (by decide))

/-- From `.clip none`, `parseBlockHeaderLoop` stops at a header-tail character or EOF. -/
lemma parseBlockHeaderLoop_stop (sc : ScannerState) (chomp : ChompStyle) (m : Option Nat)
    (fuel : Nat) (hpk : sc.peek? = none ∨ ∃ c, sc.peek? = some c ∧ TailHead c) :
    parseBlockHeaderLoop sc chomp m fuel = (chomp, m, sc) := by
  cases fuel with
  | zero => rfl
  | succ f =>
    rcases hpk with h | ⟨c, h, hc⟩
    · simp [parseBlockHeaderLoop, peekBlockHeaderIndicator?, h]
    · rcases hc with rfl | rfl | rfl | rfl | rfl <;>
        simp [parseBlockHeaderLoop, peekBlockHeaderIndicator?, h, Char.isDigit]

lemma parseBlockHeaderLoop_strip (sc : ScannerState) (m : Option Nat) (fuel : Nat)
    (hpk : sc.peek? = some '-') :
    parseBlockHeaderLoop sc .clip m (fuel + 1) = parseBlockHeaderLoop sc.advance .strip m fuel := by
  simp [parseBlockHeaderLoop, peekBlockHeaderIndicator?, hpk]

lemma parseBlockHeaderLoop_keep (sc : ScannerState) (m : Option Nat) (fuel : Nat)
    (hpk : sc.peek? = some '+') :
    parseBlockHeaderLoop sc .clip m (fuel + 1) = parseBlockHeaderLoop sc.advance .keep m fuel := by
  simp [parseBlockHeaderLoop, peekBlockHeaderIndicator?, hpk]

lemma parseBlockHeaderLoop_digit (sc : ScannerState) (chomp : ChompStyle) (fuel : Nat) {d : Char}
    (hpk : sc.peek? = some d) (h1 : '1' ≤ d) (h9 : d ≤ '9') :
    parseBlockHeaderLoop sc chomp none (fuel + 1) =
      parseBlockHeaderLoop sc.advance chomp (some (d.toNat - '0'.toNat)) fuel := by
  obtain ⟨hd, h0, hm, hp, -, -⟩ := digit_facts h1 h9
  have hpeek : peekBlockHeaderIndicator? sc chomp none = some d := by
    simp [peekBlockHeaderIndicator?, hpk, hm, hp]
  simp only [parseBlockHeaderLoop, hpeek]
  split <;> simp_all

/-- `parseBlockHeaderLoop` from `.clip none` with fuel 2 reads exactly the indicators of
    `HeaderIndicatorsOk` and lands where the tail starts. -/
lemma parseBlockHeaderLoop_accepts (sc : ScannerState) {sp sp' : SurfPos}
    {chomp : ChompStyle} {m : Option Nat}
    (hcorr : ScannerSurfCorr sc sp) (h : HeaderIndicatorsOk chomp m sp sp')
    (hhead : ∀ c, sp'.chars.head? = some c → TailHead c) :
    ∃ sc', parseBlockHeaderLoop sc .clip none 2 = (chomp, m, sc') ∧
      ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  have stop : ∀ (sc : ScannerState) (chomp : ChompStyle) (m : Option Nat) (fuel : Nat),
      ScannerSurfCorr sc sp' → parseBlockHeaderLoop sc chomp m fuel = (chomp, m, sc) := by
    intro sc chomp m fuel hc
    apply parseBlockHeaderLoop_stop
    obtain ⟨chars, col⟩ := sp'
    cases chars with
    | nil => exact Or.inl (peek_none_of_corr hc)
    | cons c tl => exact Or.inr ⟨c, (peek_of_corr hc).1, hhead c rfl⟩
  match h with
  | .indentFirst _ _ _ s₁ _ hi hch =>
    cases hi with
    | auto =>
      cases hch with
      | clip => exact ⟨sc, stop sc _ _ _ hcorr, hcorr, Keeps.refl sc⟩
      | strip rest col =>
        have hpk := (peek_of_corr hcorr).1
        have hc₁ := advance_corr hcorr (by decide) (by decide)
        exact ⟨sc.advance, by rw [parseBlockHeaderLoop_strip sc none 1 hpk, stop _ _ _ _ hc₁],
          hc₁, keeps_advance sc⟩
      | keep rest col =>
        have hpk := (peek_of_corr hcorr).1
        have hc₁ := advance_corr hcorr (by decide) (by decide)
        exact ⟨sc.advance, by rw [parseBlockHeaderLoop_keep sc none 1 hpk, stop _ _ _ _ hc₁],
          hc₁, keeps_advance sc⟩
    | digit d rest col h1 h9 =>
      obtain ⟨-, -, -, -, hnl, hcr⟩ := digit_facts h1 h9
      have hpk := (peek_of_corr hcorr).1
      have hc₁ := advance_corr hcorr hnl hcr
      rw [parseBlockHeaderLoop_digit sc .clip 1 hpk h1 h9]
      cases hch with
      | clip => exact ⟨sc.advance, stop _ _ _ _ hc₁, hc₁, keeps_advance sc⟩
      | strip rest col =>
        have hpk₁ := (peek_of_corr hc₁).1
        have hc₂ := advance_corr hc₁ (by decide) (by decide)
        exact ⟨sc.advance.advance, by rw [parseBlockHeaderLoop_strip _ _ 0 hpk₁]; rfl, hc₂,
          (keeps_advance sc).trans (keeps_advance _)⟩
      | keep rest col =>
        have hpk₁ := (peek_of_corr hc₁).1
        have hc₂ := advance_corr hc₁ (by decide) (by decide)
        exact ⟨sc.advance.advance, by rw [parseBlockHeaderLoop_keep _ _ 0 hpk₁]; rfl, hc₂,
          (keeps_advance sc).trans (keeps_advance _)⟩
  | .chompFirst _ _ _ s₁ _ hch hi =>
    cases hch with
    | clip =>
      cases hi with
      | auto => exact ⟨sc, stop sc _ _ _ hcorr, hcorr, Keeps.refl sc⟩
      | digit d rest col h1 h9 =>
        obtain ⟨-, -, -, -, hnl, hcr⟩ := digit_facts h1 h9
        have hpk := (peek_of_corr hcorr).1
        have hc₁ := advance_corr hcorr hnl hcr
        exact ⟨sc.advance, by rw [parseBlockHeaderLoop_digit sc .clip 1 hpk h1 h9, stop _ _ _ _ hc₁],
          hc₁, keeps_advance sc⟩
    | strip rest col =>
      have hpk := (peek_of_corr hcorr).1
      have hc₁ := advance_corr hcorr (by decide) (by decide)
      rw [parseBlockHeaderLoop_strip sc none 1 hpk]
      cases hi with
      | auto => exact ⟨sc.advance, stop _ _ _ _ hc₁, hc₁, keeps_advance sc⟩
      | digit d rest col h1 h9 =>
        obtain ⟨-, -, -, -, hnl, hcr⟩ := digit_facts h1 h9
        have hpk₁ := (peek_of_corr hc₁).1
        have hc₂ := advance_corr hc₁ hnl hcr
        exact ⟨sc.advance.advance, by rw [parseBlockHeaderLoop_digit _ _ 0 hpk₁ h1 h9]; rfl, hc₂,
          (keeps_advance sc).trans (keeps_advance _)⟩
    | keep rest col =>
      have hpk := (peek_of_corr hcorr).1
      have hc₁ := advance_corr hcorr (by decide) (by decide)
      rw [parseBlockHeaderLoop_keep sc none 1 hpk]
      cases hi with
      | auto => exact ⟨sc.advance, stop _ _ _ _ hc₁, hc₁, keeps_advance sc⟩
      | digit d rest col h1 h9 =>
        obtain ⟨-, -, -, -, hnl, hcr⟩ := digit_facts h1 h9
        have hpk₁ := (peek_of_corr hc₁).1
        have hc₂ := advance_corr hc₁ hnl hcr
        exact ⟨sc.advance.advance, by rw [parseBlockHeaderLoop_digit _ _ 0 hpk₁ h1 h9]; rfl, hc₂,
          (keeps_advance sc).trans (keeps_advance _)⟩

/-- `collectCommentTextLoop` reads a `CommentCharOk` run up to a break or EOF. -/
lemma collectCommentTextLoop_accepts {sp sp' : SurfPos} (h : GStar (GChar CommentCharOk) sp sp')
    (hstop : ∀ c, sp'.chars.head? = some c → isLineBreakBool c = true) :
    ∀ (sc : ScannerState) (text : String) (fuel : Nat),
      ScannerSurfCorr sc sp → sp.chars.length ≤ fuel →
      ScannerSurfCorr (collectCommentTextLoop sc text fuel).2 sp' ∧
        Keeps sc (collectCommentTextLoop sc text fuel).2 := by
  induction h with
  | nil s =>
    intro sc text fuel hcorr _
    cases fuel with
    | zero => simp only [collectCommentTextLoop]; exact ⟨hcorr, Keeps.refl sc⟩
    | succ f =>
      obtain ⟨chars, col⟩ := s
      cases chars with
      | nil => simp only [collectCommentTextLoop, peek_none_of_corr hcorr]; exact ⟨hcorr, Keeps.refl sc⟩
      | cons c tl =>
        have hpk := (peek_of_corr hcorr).1
        simp only [collectCommentTextLoop, hpk, hstop c rfl, ite_true]
        exact ⟨hcorr, Keeps.refl sc⟩
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro sc text fuel hcorr hfuel
    cases hstep with
    | mk c rest col hc =>
      cases fuel with
      | zero => simp at hfuel
      | succ f =>
        have hpk := (peek_of_corr hcorr).1
        have hcc : isLineBreakBool c = false := hc
        have hnl : c ≠ '\n' := by intro e; subst e; exact absurd hcc (by decide)
        have hcr : c ≠ '\r' := by intro e; subst e; exact absurd hcc (by decide)
        obtain ⟨hc', hk⟩ := ih hstop sc.advance (text.push c) f (advance_corr hcorr hnl hcr)
          (by dsimp only at hfuel ⊢; simp only [List.length_cons] at hfuel; omega)
        simp only [collectCommentTextLoop, hpk, hcc, Bool.false_eq_true, ite_false]
        exact ⟨hc', (keeps_advance sc).trans hk⟩

lemma GStar_SSWhite_chars {s s' : SurfPos} (h : GStar SSWhite s s') :
    ∃ ws : List Char, s.chars = ws ++ s'.chars ∧ ∀ c ∈ ws, isWhiteSpaceBool c = true := by
  induction h with
  | nil s => exact ⟨[], rfl, by simp⟩
  | cons s₁ s₂ s₃ hstep _ ih =>
    obtain ⟨ws, hws, hall⟩ := ih
    cases hstep with
    | space rest col =>
      refine ⟨' ' :: ws, ?_, ?_⟩
      · dsimp only at hws ⊢; rw [hws]; rfl
      · intro c hc; rcases List.mem_cons.mp hc with rfl | hc
        · decide
        · exact hall c hc
    | tab rest col =>
      refine ⟨'\t' :: ws, ?_, ?_⟩
      · dsimp only at hws ⊢; rw [hws]; rfl
      · intro c hc; rcases List.mem_cons.mp hc with rfl | hc
        · decide
        · exact hall c hc

lemma corr_of_comments {sc : ScannerState} {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp)
    (cs : Array (YamlPos × String)) : ScannerSurfCorr { sc with comments := cs } sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩

/-- After `skipWhitespace` over a non-empty white run, the character behind the scanner is white. -/
lemma peekBack_white_of_whites {sc sc₁ : ScannerState} {s s₁ : SurfPos}
    (hcorr : ScannerSurfCorr sc s) (hc₁ : ScannerSurfCorr sc₁ s₁) (hin : sc₁.input = sc.input)
    (hw : GPlus SSWhite s s₁) :
    ∃ w, sc₁.peekBack? = some w ∧ isWhiteSpaceBool w = true := by
  obtain ⟨ws, hws, hall⟩ := GStar_SSWhite_chars (GPlus.toGStar hw)
  have hne : ws ≠ [] := by
    rintro rfl
    cases hw with
    | mk s₂ _ hstep hrest =>
      have hlen := GStar_SSWhite_length hrest
      have hlw := congrArg List.length hws
      cases hstep <;> simp at hlw hlen <;> omega
  obtain ⟨pre, hsplit, hoff⟩ := hcorr.input_prefix
  obtain ⟨pre₁, hsplit₁, hoff₁⟩ := hc₁.input_prefix
  have hpre₁ : pre₁ = pre ++ ws := by
    have h2 : sc₁.input.toList = (pre ++ ws) ++ s₁.chars := by
      rw [hin, hsplit, hws, List.append_assoc]
    exact List.append_cancel_right (hsplit₁.symm.trans h2)
  have hne₁ : pre₁ ≠ [] := by rw [hpre₁]; simp [hne]
  refine ⟨pre₁.getLast hne₁, peekBack_eq_last_prefix hsplit₁ hoff₁ hne₁, ?_⟩
  have hlast : pre₁.getLast hne₁ = ws.getLast hne := by
    subst hpre₁
    first
      | exact List.getLast_append_of_ne_nil _ hne
      | exact List.getLast_append_of_ne_nil hne
      | simp [List.getLast_append_of_ne_nil, hne]
  rw [hlast]
  exact hall _ (List.getLast_mem hne)

/-! ## §5 The header tail -/

lemma not_space_tab_of_break {c : Char} (hlb : isLineBreakBool c = true) :
    c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '#' := by
  rcases lineBreak_cases hlb with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

/-- `scanBlockScalarSkipComment` leaves a state not at `#` alone. -/
lemma scanBlockScalarSkipComment_id (sc : ScannerState) (h : sc.peek? ≠ some '#') :
    scanBlockScalarSkipComment sc = sc := by
  unfold scanBlockScalarSkipComment
  split
  · exact absurd ‹sc.peek? = some '#'› h
  · rfl

/-- `skipWhitespace`, `scanBlockScalarSkipComment` and `scanBlockScalarConsumeNewline` read a
    `HeaderTailOk` tail and land at the start of the body. -/
lemma blockHeaderTail_accepts (sc : ScannerState) {sp sp' : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (htail : HeaderTailOk sp sp') :
    ∃ sc', scanBlockScalarConsumeNewline (scanBlockScalarSkipComment (skipWhitespace sc)) =
        .ok sc' ∧ ScannerSurfCorr sc' sp' ∧ Keeps sc sc' := by
  cases htail with
  | break_ s₁ s' hw hb =>
    obtain ⟨c, rest, hc, hlb⟩ := hb.head
    obtain ⟨hns, hnt, hnh⟩ := not_space_tab_of_break hlb
    obtain ⟨chars, col⟩ := s₁
    simp only at hc; subst hc
    obtain ⟨hc₁, hk₁⟩ := skipWhitespace_accepts sc hw hcorr (by simpa using hns) (by simpa using hnt)
    have hpk := (peek_of_corr hc₁).1
    rw [scanBlockScalarSkipComment_id _ (by rw [hpk]; simpa using hnh)]
    refine ⟨consumeNewline (skipWhitespace sc), ?_, ?_⟩
    · simp [scanBlockScalarConsumeNewline, hpk, hlb]
    · obtain ⟨hc₂, hk₂⟩ := consumeNewline_accepts _ hb hc₁
      exact ⟨hc₂, hk₁.trans hk₂⟩
  | eof col hw =>
    obtain ⟨hc₁, hk₁⟩ := skipWhitespace_accepts sc hw hcorr (by simp) (by simp)
    have hpk := peek_none_of_corr hc₁
    rw [scanBlockScalarSkipComment_id _ (by rw [hpk]; simp)]
    exact ⟨skipWhitespace sc, by simp [scanBlockScalarConsumeNewline, hpk], hc₁, hk₁⟩
  | commentBreak s₂ s' rest col hw hcm hb =>
    obtain ⟨hc₁, hk₁⟩ := skipWhitespace_accepts sc (GPlus.toGStar hw) hcorr (by simp) (by simp)
    have hpk := (peek_of_corr hc₁).1
    obtain ⟨w, hpb, hww⟩ := peekBack_white_of_whites hcorr hc₁ (skipWhitespace_input sc) hw
    have hc₂ := advance_corr hc₁ (by decide) (by decide)
    obtain ⟨c, rest₂, hc, hlb⟩ := hb.head
    have hstop : ∀ d, s₂.chars.head? = some d → isLineBreakBool d = true := by
      intro d hd; rw [hc] at hd; simp at hd; subst hd; exact hlb
    have hlen := fuel_of_corr hc₂
    obtain ⟨hc₃, hk₃⟩ := collectCommentTextLoop_accepts hcm hstop (skipWhitespace sc).advance ""
      ((skipWhitespace sc).advance.inputEnd - (skipWhitespace sc).advance.offset) hc₂ (by omega)
    generalize hcl : collectCommentTextLoop (skipWhitespace sc).advance ""
      ((skipWhitespace sc).advance.inputEnd - (skipWhitespace sc).advance.offset) = r at hc₃ hk₃
    obtain ⟨text, sc₃⟩ := r
    have hsk : scanBlockScalarSkipComment (skipWhitespace sc) =
        { sc₃ with comments := sc₃.comments.push ((skipWhitespace sc).currentPos, text) } := by
      unfold scanBlockScalarSkipComment
      simp only [hpk, hpb, hww, Bool.true_or, ite_true, hcl]
    rw [hsk]
    have hc₄ : ScannerSurfCorr { sc₃ with comments := sc₃.comments.push ((skipWhitespace sc).currentPos, text) } s₂ :=
      corr_of_comments hc₃ _
    obtain ⟨chars, col₂⟩ := s₂
    simp only at hc; subst hc
    have hpk₄ := (peek_of_corr hc₄).1
    obtain ⟨hc₅, hk₅⟩ := consumeNewline_accepts _ hb hc₄
    exact ⟨_, by simp [scanBlockScalarConsumeNewline, hpk₄, hlb], hc₅,
      ((hk₁.trans (keeps_advance _)).trans ⟨hk₃.1, hk₃.2.1, hk₃.2.2⟩).trans hk₅⟩
  | commentEof rest col col' hw hcm =>
    obtain ⟨hc₁, hk₁⟩ := skipWhitespace_accepts sc (GPlus.toGStar hw) hcorr (by simp) (by simp)
    have hpk := (peek_of_corr hc₁).1
    obtain ⟨w, hpb, hww⟩ := peekBack_white_of_whites hcorr hc₁ (skipWhitespace_input sc) hw
    have hc₂ := advance_corr hc₁ (by decide) (by decide)
    have hlen := fuel_of_corr hc₂
    obtain ⟨hc₃, hk₃⟩ := collectCommentTextLoop_accepts hcm (by simp) (skipWhitespace sc).advance ""
      ((skipWhitespace sc).advance.inputEnd - (skipWhitespace sc).advance.offset) hc₂ (by omega)
    generalize hcl : collectCommentTextLoop (skipWhitespace sc).advance ""
      ((skipWhitespace sc).advance.inputEnd - (skipWhitespace sc).advance.offset) = r at hc₃ hk₃
    obtain ⟨text, sc₃⟩ := r
    have hsk : scanBlockScalarSkipComment (skipWhitespace sc) =
        { sc₃ with comments := sc₃.comments.push ((skipWhitespace sc).currentPos, text) } := by
      unfold scanBlockScalarSkipComment
      simp only [hpk, hpb, hww, Bool.true_or, ite_true, hcl]
    rw [hsk]
    have hc₄ : ScannerSurfCorr { sc₃ with comments := sc₃.comments.push ((skipWhitespace sc).currentPos, text) } ⟨[], col'⟩ :=
      corr_of_comments hc₃ _
    have hpk₄ := peek_none_of_corr hc₄
    exact ⟨_, by simp [scanBlockScalarConsumeNewline, hpk₄], hc₄,
      (hk₁.trans (keeps_advance _)).trans ⟨hk₃.1, hk₃.2.1, hk₃.2.2⟩⟩

/-! ## §6 No tab stop at a `BlockStopOk` landing -/

lemma lineCharOk_space : LineCharOk ' ' := ⟨by decide, by decide, by decide⟩
lemma lineCharOk_tab : LineCharOk '\t' := ⟨by decide, by decide, by decide⟩

lemma peek_none_of_nil {sc : ScannerState} {sp : SurfPos} (hcorr : ScannerSurfCorr sc sp)
    (h : sp.chars = []) : sc.peek? = none := by
  obtain ⟨chars, col⟩ := sp
  simp only at h; subst h
  exact peek_none_of_corr hcorr

lemma peek_eq_of_head {sc : ScannerState} {sp : SurfPos} {c : Char} (hcorr : ScannerSurfCorr sc sp)
    (h : sp.chars.head? = some c) : sc.peek? = some c := by
  obtain ⟨chars, col⟩ := sp
  cases chars with
  | nil => simp at h
  | cons d tl => simp at h; subst h; exact (peek_of_corr hcorr).1

/-- `blockScalarTabStop` is false wherever `collectBlockScalarLoop` stops on a `BlockStopOk`. -/
lemma blockScalarTabStop_false_of_stop {sc : ScannerState} {n : Nat} {sp sp' : SurfPos}
    (hstop : BlockStopOk n sp sp') (hcorr : ScannerSurfCorr sc sp') :
    blockScalarTabStop sc = false := by
  unfold blockScalarTabStop
  match hstop with
  | .eofShort k _ _ hnd hk hind hnil =>
    have hc₁ := (skipSpaces_accepts sc (SIndent.zero _) hcorr (by rw [hnil]; simp)).1
    simp [peek_none_of_nil hc₁ hnil]
  | .eofLine _ s₁ _ hnd hind hrun hnil =>
    have hc₁ := (skipSpaces_accepts sc (SIndent.zero _) hcorr (by rw [hnil]; simp)).1
    simp [peek_none_of_nil hc₁ hnil]
  | .outdent k _ s₁ c hnd hk hind hhead hlb hsp htab =>
    have hc₁ := (skipSpaces_accepts sc hind hcorr (by rw [hhead]; simpa using hsp)).1
    simp [peek_eq_of_head hc₁ hhead, htab]
  | .docMarker _ hm h0 =>
    obtain ⟨m, r, hm, hchars, -⟩ := hm
    have hhead : sp.chars.head? = some m := by rw [hchars]; rfl
    have hsp : m ≠ ' ' := by rcases hm with rfl | rfl <;> decide
    have htab : m ≠ '\t' := by rcases hm with rfl | rfl <;> decide
    have hc₁ := (skipSpaces_accepts sc (SIndent.zero _) hcorr (by rw [hhead]; simpa using hsp)).1
    simp [peek_eq_of_head hc₁ hhead, htab]
  | .badChar _ s₁ _ c hnd hind hrun hhead hlb hnot =>
    have hsp : c ≠ ' ' := by rintro rfl; exact hnot lineCharOk_space
    have htab : c ≠ '\t' := by rintro rfl; exact hnot lineCharOk_tab
    have hc₁ := (skipSpaces_accepts sc (SIndent.zero _) hcorr (by rw [hhead]; simpa using hsp)).1
    simp [peek_eq_of_head hc₁ hhead, htab]

/-! ## §7 Sub-relation lemmas into `[162]` -/

lemma ChompOk.toSCChompingIndicator {chomp : ChompStyle} {s s' : SurfPos}
    (h : ChompOk chomp s s') : SCChompingIndicator s s' := by
  cases h with
  | clip s => exact .empty s
  | strip rest col => exact .strip _ _ (.mk rest col)
  | keep rest col => exact .keep _ _ (.mk rest col)

lemma IndentOk.toSCIndentationIndicator {m : Option Nat} {s s' : SurfPos}
    (h : IndentOk m s s') : SCIndentationIndicator s s' := by
  cases h with
  | auto s => exact .empty s
  | digit d rest col h1 h9 => exact .digit _ _ (.mk d rest col ⟨h1, h9⟩)

lemma HeaderIndicatorsOk.toGAlt {chomp : ChompStyle} {m : Option Nat} {s s' : SurfPos}
    (h : HeaderIndicatorsOk chomp m s s') :
    GAlt (GSeq SCIndentationIndicator SCChompingIndicator)
         (GSeq SCChompingIndicator SCIndentationIndicator) s s' := by
  match h with
  | .indentFirst _ _ _ s₁ _ hi hch =>
    exact .left _ _ (.mk _ s₁ _ hi.toSCIndentationIndicator hch.toSCChompingIndicator)
  | .chompFirst _ _ _ s₁ _ hch hi =>
    exact .right _ _ (.mk _ s₁ _ hch.toSCChompingIndicator hi.toSCIndentationIndicator)

lemma GStar_commentCharOk_toSCommentChar {s s' : SurfPos}
    (h : GStar (GChar CommentCharOk) s s') : GStar SCommentChar s s' := by
  refine GStar_mono (fun _ _ hc => ?_) h
  cases hc with
  | mk c rest col hc =>
    refine GChar.mk c rest col ?_
    intro hlb
    have : isLineBreakBool c = true := (isLineBreak_iff c).mpr hlb
    exact absurd this (by rw [show isLineBreakBool c = false from hc]; decide)

lemma HeaderTailOk.toSSBComment {s s' : SurfPos} (h : HeaderTailOk s s') : SSBComment s s' := by
  cases h with
  | break_ s₁ s' hw hb =>
    cases hw with
    | nil _ => exact .noSep _ _ (.break _ _ hb.toSBBreak)
    | cons _ s₂ _ hstep hrest =>
      exact .withSep _ _ _ _ (.whites _ _ (.mk _ s₂ _ hstep hrest)) (.none _) (.break _ _ hb.toSBBreak)
  | eof col hw =>
    cases hw with
    | nil _ => exact .noSep _ _ (.eof col)
    | cons _ s₂ _ hstep hrest =>
      exact .withSep _ _ _ _ (.whites _ _ (.mk _ s₂ _ hstep hrest)) (.none _) (.eof col)
  | commentBreak s₂ s' rest col hw hcm hb =>
    exact .withSep _ _ _ _ (.whites _ _ hw)
      (.some _ _ (.mk rest col s₂ (GStar_commentCharOk_toSCommentChar hcm))) (.break _ _ hb.toSBBreak)
  | commentEof rest col col' hw hcm =>
    exact .withSep _ _ _ _ (.whites _ _ hw)
      (.some _ _ (.mk rest col _ (GStar_commentCharOk_toSCommentChar hcm))) (.eof col')

/-- `HeaderIndicatorsOk` then `HeaderTailOk` is a `[162] c-b-block-header` derivation. -/
lemma blockHeader_toSCBBlockHeader {chomp : ChompStyle} {m : Option Nat} {s s₁ s' : SurfPos}
    (hi : HeaderIndicatorsOk chomp m s s₁) (ht : HeaderTailOk s₁ s') : SCBBlockHeader s s' :=
  .mk s s₁ s' hi.toGAlt ht.toSSBComment

/-! ## §8 The auto-detected content indent -/

/-- `autoDetectBlockScalarIndentLoop` from `maxWS`: a blank line widens `maxWS` to its column;
    the first content line (no tab below `minCI`, no earlier blank wider than it) fixes
    `n = max minCI col`; at EOF the widest blank (or `minCI`) wins. -/
inductive AutoIndentOk (minCI : Nat) : Nat → Nat → SurfPos → Prop where
  | content (maxWS k : Nat) (s s₁ : SurfPos) (c : Char) :
      SIndent k s s₁ → s₁.chars.head? = some c → c ≠ ' ' → isLineBreakBool c = false →
      (c = '\t' → minCI ≤ s₁.col) → maxWS ≤ max minCI s₁.col →
      AutoIndentOk minCI maxWS (max minCI s₁.col) s
  | eof (maxWS k : Nat) (s s₁ : SurfPos) :
      SIndent k s s₁ → s₁.chars = [] →
      AutoIndentOk minCI maxWS (max minCI (max maxWS s₁.col)) s
  | blank (maxWS n k : Nat) (s s₁ s₂ : SurfPos) :
      SIndent k s s₁ → SBBreakOk s₁ s₂ → AutoIndentOk minCI (max maxWS s₁.col) n s₂ →
      AutoIndentOk minCI maxWS n s

lemma autoDetectBlockScalarIndentLoop_accepts {minCI maxWS n : Nat} {sp : SurfPos}
    (h : AutoIndentOk minCI maxWS n sp) :
    ∀ (sc : ScannerState) (mwl fuel ie : Nat), ScannerSurfCorr sc sp → sp.chars.length < fuel →
      ∃ line probe,
        autoDetectBlockScalarIndentLoop sc maxWS mwl minCI fuel ie = (n, line, probe, none) := by
  induction h with
  | content maxWS k s s₁ c hind hhead hsp hlb htab hmax =>
    intro sc mwl fuel ie hcorr hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      have hc₁ := (skipSpaces_accepts sc hind hcorr (by rw [hhead]; simpa using hsp)).1
      have hpk := peek_eq_of_head hc₁ hhead
      have hcol : (skipSpaces sc).col = s₁.col := hc₁.col_eq.symm
      have htabF : (c == '\t' && decide (s₁.col < minCI)) = false := by
        by_cases hct : c = '\t'
        · subst hct; simp [Nat.not_lt.mpr (htab rfl)]
        · simp [hct]
      have hmaxF : ¬ maxWS > max minCI s₁.col := Nat.not_lt.mpr hmax
      simp only [autoDetectBlockScalarIndentLoop, hpk, hcol, htabF, hlb, hmaxF, Bool.false_eq_true,
        ite_false]
      exact ⟨_, _, rfl⟩
  | eof maxWS k s s₁ hind hnil =>
    intro sc mwl fuel ie hcorr hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      have hc₁ := (skipSpaces_accepts sc hind hcorr (by rw [hnil]; simp)).1
      have hpk := peek_none_of_nil hc₁ hnil
      have hcol : (skipSpaces sc).col = s₁.col := hc₁.col_eq.symm
      simp only [autoDetectBlockScalarIndentLoop, hpk, hcol]
      refine ⟨mwl, sc, ?_⟩
      split <;> simp only [Prod.mk.injEq, and_true] <;> omega
  | blank maxWS n k s s₁ s₂ hind hb hrec ih =>
    intro sc mwl fuel ie hcorr hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      obtain ⟨c, rest, hc, hlb⟩ := hb.head
      obtain ⟨hns, hnt, -⟩ := not_space_tab_of_break hlb
      have hc₁ := (skipSpaces_accepts sc hind hcorr (by rw [hc]; simpa using hns)).1
      have hpk := peek_eq_of_head hc₁ (by rw [hc]; rfl)
      have hcol : (skipSpaces sc).col = s₁.col := hc₁.col_eq.symm
      obtain ⟨hc₂, -⟩ := consumeNewline_accepts _ hb hc₁
      have hl₁ := SIndent.length_le hind
      have hl₂ := hb.length_lt
      have hbt : (c == '\t') = false := by simp [hnt]
      have hm : (if s₁.col > maxWS then s₁.col else maxWS) = max maxWS s₁.col := by
        split <;> omega
      simp only [autoDetectBlockScalarIndentLoop, hpk, hcol, hbt, Bool.false_and, Bool.false_eq_true,
        ite_false, hlb, ite_true, hm]
      exact ih _ _ f ie hc₂ (by omega)

/-- `autoDetectBlockScalarIndent` detects exactly the `AutoIndentOk` indent, without error. -/
lemma autoDetectBlockScalarIndent_accepts (sc : ScannerState) {minCI n : Nat} {sp : SurfPos}
    (h : AutoIndentOk minCI 0 n sp) (hcorr : ScannerSurfCorr sc sp) (ie : Nat)
    (hie : sc.inputEnd = ie) :
    autoDetectBlockScalarIndent sc minCI ie = (n, none) := by
  have hfuel := fuel_of_corr hcorr
  obtain ⟨line, probe, heq⟩ :=
    autoDetectBlockScalarIndentLoop_accepts h sc 0 (ie - sc.offset + 1) ie hcorr (by omega)
  simp only [autoDetectBlockScalarIndent, heq]

/-! ## §9 `scanBlockScalar` -/

/-- The content indent `scanBlockScalarBody` uses: an explicit `k` relative to the parent
    indent, or the auto-detected one. -/
def BlockIndentOk (ci : Int) (m : Option Nat) (n : Nat) (sp : SurfPos) : Prop :=
  match m with
  | some k => n = (max 0 (ci + k)).toNat
  | none => AutoIndentOk ((max 0 (ci + 1)).toNat) 0 n sp

/-- `BlockLineOk n` lines then a `BlockStopOk n` stop: what `collectBlockScalarLoop` reads. -/
def BlockBodyOk (n : Nat) (sp sp' : SurfPos) : Prop :=
  ∃ sp₁, GStar (BlockLineOk n) sp sp₁ ∧ BlockStopOk n sp₁ sp'

/-- Converse of `scanBlockScalar_prod`, modulo the header (`HeaderIndicatorsOk` then
    `HeaderTailOk`, a sub-relation of `[162]` by `blockHeader_toSCBBlockHeader`) and the content
    indent (`BlockIndentOk`): the scanner reads a `BlockBodyOk n` body, lands at its stop and
    emits the scalar at the indicator's position. -/
lemma scanBlockScalar_accepts (sc : ScannerState) {sp sp₁ sp₂ sp₃ sp' : SurfPos}
    {chomp : ChompStyle} {m : Option Nat} {n : Nat}
    (hcorr : ScannerSurfCorr sc sp) (hind : GLit '|' sp sp₁ ∨ GLit '>' sp sp₁)
    (hhdr : HeaderIndicatorsOk chomp m sp₁ sp₂) (htail : HeaderTailOk sp₂ sp₃)
    (hn : BlockIndentOk sc.currentIndent m n sp₃) (hbody : BlockBodyOk n sp₃ sp') :
    ∃ s' content, scanBlockScalar sc = .ok s' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content (if sc.peek? == some '|' then ScalarStyle.literal else ScalarStyle.folded) } := by
  have hadv : ScannerSurfCorr sc.advance sp₁ := by
    rcases hind with h | h <;> cases h <;> exact advance_corr hcorr (by decide) (by decide)
  obtain ⟨sc₁, hhd, hc₁, hk₁⟩ := parseBlockHeaderLoop_accepts sc.advance hadv hhdr htail.head
  obtain ⟨sc₂, hnl, hc₂, hk₂⟩ := blockHeaderTail_accepts sc₁ hc₁ htail
  obtain ⟨sp₄, hlines, hstop⟩ := hbody
  have hie : sc₂.inputEnd = sc.inputEnd := by rw [hk₂.2.1, hk₁.2.1, (keeps_advance sc).2.1]
  have hfuel := fuel_of_corr hc₂
  obtain ⟨hc₃, hk₃⟩ := collectBlockScalarLoop_accepts hlines sc₂ "" (sc.inputEnd - sc₂.offset + 1)
    sc.inputEnd sp' hc₂ hie hstop (by rw [← hie]; exact hfuel)
  have htab := blockScalarTabStop_false_of_stop hstop hc₃
  generalize hcl : collectBlockScalarLoop sc₂ "" (sc.inputEnd - sc₂.offset + 1) n sc.inputEnd = r
    at hc₃ hk₃ htab
  obtain ⟨raw, sc₃⟩ := r
  have htab' : blockScalarTabStop sc₃ = false := htab
  have ht₃ : sc₃.tokens = sc₂.tokens := hk₃.1
  have hc₃' : ScannerSurfCorr sc₃ sp' := hc₃
  have htok : ∀ (content : String) (style : ScalarStyle),
      ({ (sc₃.emitAt sc.currentPos (.scalar content style)) with
          simpleKeyAllowed := true, simpleKey := { possible := false } } : ScannerState).tokens =
        sc.tokens.push { pos := sc.currentPos, val := .scalar content style } := by
    intro content style
    simp [ScannerState.emitAt, ht₃, hk₂.1, hk₁.1, (keeps_advance sc).1]
  have hcorr' : ∀ (content : String) (style : ScalarStyle),
      ScannerSurfCorr { (sc₃.emitAt sc.currentPos (.scalar content style)) with
          simpleKeyAllowed := true, simpleKey := { possible := false } } sp' := by
    intro content style
    exact ⟨hc₃'.chars_from, hc₃'.col_eq, hc₃'.end_eq, hc₃'.input_prefix, hc₃'.indent_cols_nonneg⟩
  unfold scanBlockScalar
  simp only [hhd, hnl]
  unfold scanBlockScalarBody
  cases m with
  | some k =>
    simp only [BlockIndentOk] at hn
    simp only [hn.symm, hcl, htab', Bool.false_eq_true, ite_false]
    exact ⟨_, _, rfl, hcorr' _ _, htok _ _⟩
  | none =>
    simp only [BlockIndentOk] at hn
    simp only [autoDetectBlockScalarIndent_accepts sc₂ hn hc₂ sc.inputEnd hie, hcl, htab',
      Bool.false_eq_true, ite_false]
    exact ⟨_, _, rfl, hcorr' _ _, htok _ _⟩

/-! ## §10 `BlockBodyOk n` is a `[173] l-literal-content(n)` derivation -/

lemma LineCharOk.toNbChar {c : Char} (h : LineCharOk c) : isNbChar c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun hb => ?_, (isPrintable_iff c).mp h2, h3⟩
  have := (isLineBreak_iff c).mpr hb
  rw [h1] at this; exact absurd this (by decide)

lemma GChar_lineChar_toNb {s s' : SurfPos} (h : GChar LineCharOk s s') : SNbChar s s' :=
  match h with
  | .mk c rest col hc => GChar.mk c rest col hc.toNbChar

lemma GStar_lineChar_toNb {s s' : SurfPos} (h : GStar (GChar LineCharOk) s s') :
    GStar SNbChar s s' :=
  GStar_mono (fun _ _ hc => GChar_lineChar_toNb hc) h

lemma GPlus_lineChar_toNb {s s' : SurfPos} (h : GPlus (GChar LineCharOk) s s') :
    GPlus SNbChar s s' :=
  match h with
  | .mk _ s₂ _ hstep hrest => .mk _ s₂ _ (GChar_lineChar_toNb hstep) (GStar_lineChar_toNb hrest)

lemma SIndentLe_of_le {k n : Nat} {s s' : SurfPos} (h : SIndent k s s') (hk : k ≤ n) :
    SIndentLe n s s' := ⟨k, hk, h⟩

/-- A blank body line is `[70] l-empty(n, BLOCK-IN)`. -/
lemma blank_toSLEmpty {n k : Nat} {s s₁ s' : SurfPos} (hk : k ≤ n) (hind : SIndent k s s₁)
    (hb : SBBreakOk s₁ s') : SLEmpty n .blockIn s s' :=
  .block n s s₁ s' .blockIn (Or.inr rfl) (.some _ _ (SIndentLe_of_le hind hk)) hb.toSBBreak

/-- The two shapes of a `[173]` tail the body induction builds: no content line yet
    (`blanks`), or at least one (`text`). -/
inductive BodyTail (n : Nat) : SurfPos → SurfPos → Prop where
  | blanks (s s₃ s₄ s' : SurfPos) :
      GStar (SLEmpty n .blockIn) s s₃ → GOpt (SLTrailComments n) s₃ s₄ →
      GOpt (fun a b => SIndentLe n a b ∧ b.chars = []) s₄ s' → BodyTail n s s'
  | text (s s₁ s₂ s₃ s₄ s' : SurfPos) :
      GSeq (SLNbLiteralText n) (GStar (SBNbLiteralNext n)) s s₁ → GOpt SBBreak s₁ s₂ →
      GStar (SLEmpty n .blockIn) s₂ s₃ → GOpt (SLTrailComments n) s₃ s₄ →
      GOpt (fun a b => SIndentLe n a b ∧ b.chars = []) s₄ s' → BodyTail n s s'

lemma BodyTail.toSLLiteralContent {n : Nat} {s s' : SurfPos} (h : BodyTail n s s') :
    SLLiteralContent n s s' :=
  match h with
  | .blanks _ s₃ s₄ _ he ht hi => .mk n s s s s₃ s₄ s' (.none s) (.none s) he ht hi
  | .text _ s₁ s₂ s₃ s₄ _ htx hb he ht hi => .mk n s s₁ s₂ s₃ s₄ s' (.some _ _ htx) hb he ht hi

lemma BodyTail.blank {n k : Nat} {s s₁ s₂ s' : SurfPos} (hk : k ≤ n) (hind : SIndent k s s₁)
    (hb : SBBreakOk s₁ s₂) (ht : BodyTail n s₂ s') : BodyTail n s s' :=
  have he := blank_toSLEmpty hk hind hb
  match ht with
  | .blanks _ s₃ s₄ _ hes htc hi => .blanks s s₃ s₄ s' (.cons _ _ _ he hes) htc hi
  | .text _ t₁ t₂ s₃ s₄ _ (.mk _ sm _ (.mk _ _ sm₁ _ hemp hseq) hnext) hbr hes htc hi =>
    .text s t₁ t₂ s₃ s₄ s'
      (.mk _ sm _ (.mk n _ sm₁ _ (.cons _ _ _ he hemp) hseq) hnext) hbr hes htc hi

lemma BodyTail.content {n : Nat} {s s₁ s₂ s₃ s' : SurfPos} (hind : SIndent n s s₁)
    (hrun : GPlus (GChar LineCharOk) s₁ s₂) (hb : SBBreakOk s₂ s₃) (ht : BodyTail n s₃ s') :
    BodyTail n s s' :=
  have htext : SLNbLiteralText n s s₂ :=
    .mk n s s s₂ (.nil s) (.mk s s₁ s₂ hind (GPlus_lineChar_toNb hrun))
  match ht with
  | .blanks _ s₄ s₅ _ hes htc hi =>
    .text s s₂ s₃ s₄ s₅ s' (.mk s s₂ s₂ htext (.nil s₂)) (.some _ _ hb.toSBBreak) hes htc hi
  | .text _ t₁ t₂ s₄ s₅ _ (.mk _ sm _ htext' hnext) hbr hes htc hi =>
    .text s t₁ t₂ s₄ s₅ s'
      (.mk s s₂ t₁ htext (.cons s₂ sm t₁ (.mk n s₂ s₃ sm hb.toSBBreak htext') hnext))
      hbr hes htc hi

/-- A non-empty content line with no break after it (EOF or a bad character). -/
lemma lineRunPlus_toBodyTail {n : Nat} {s s₁ s' : SurfPos} (hind : SIndent n s s₁)
    (hrun : GPlus (GChar LineCharOk) s₁ s') : BodyTail n s s' :=
  .text s s' s' s' s' s'
    (.mk s s' s' (.mk n s s s' (.nil s) (.mk s s₁ s' hind (GPlus_lineChar_toNb hrun))) (.nil s'))
    (.none s') (.nil s') (.none s') (.none s')

/-- A possibly empty line run at end of input: the empty run is `[173]`'s EOF-only
    partial-indent tail. -/
lemma lineRun_toBodyTail {n : Nat} {s s₁ s' : SurfPos} (hind : SIndent n s s₁)
    (hrun : GStar (GChar LineCharOk) s₁ s') (hend : s'.chars = []) : BodyTail n s s' :=
  match hrun with
  | .nil _ =>
    .blanks s s s s₁ (.nil s) (.none s) (.some _ _ ⟨SIndentLe_of_le hind (Nat.le_refl n), hend⟩)
  | .cons _ sm _ hstep hrest => lineRunPlus_toBodyTail hind (.mk _ sm _ hstep hrest)

lemma BlockStopOk.toBodyTail {n : Nat} {s s' : SurfPos} (h : BlockStopOk n s s') :
    BodyTail n s s' :=
  match h with
  | .eofShort _ _ _ _ hk hind hend =>
    .blanks s s s s' (.nil s) (.none s) (.some _ _ ⟨SIndentLe_of_le hind (Nat.le_of_lt hk), hend⟩)
  | .eofLine _ _ _ _ hind hrun hend => lineRun_toBodyTail hind hrun hend
  | .outdent _ _ _ _ _ _ _ _ _ _ _ => .blanks s s s s (.nil s) (.none s) (.none s)
  | .badChar _ _ _ _ _ hind hrun _ _ _ => lineRunPlus_toBodyTail hind hrun
  | .docMarker _ _ _ => .blanks s s s s (.nil s) (.none s) (.none s)

/-- `BlockBodyOk n` is a sub-relation of `[173] l-literal-content(n)` (and so of `[176]`
    `l-folded-content` as `SCLFolded` states it). -/
lemma BlockBodyOk.toSLLiteralContent {n : Nat} {sp sp' : SurfPos} (h : BlockBodyOk n sp sp') :
    SLLiteralContent n sp sp' := by
  obtain ⟨sp₁, hlines, hstop⟩ := h
  have hbase := hstop.toBodyTail
  clear hstop
  suffices hpre : ∀ t, BodyTail n sp₁ t → BodyTail n sp t from
    (hpre sp' hbase).toSLLiteralContent
  clear hbase
  induction hlines with
  | nil _ => exact fun _ ht => ht
  | cons s₁ s₂ s₃ hstep _ ih =>
    intro t ht
    match hstep with
    | .blank _ _ u₁ _ _ hk hind hb => exact BodyTail.blank hk hind hb (ih t ht)
    | .content _ u₁ u₂ _ _ hind hrun hb => exact BodyTail.content hind hrun hb (ih t ht)

end L4YAML.Proofs.Acceptance
