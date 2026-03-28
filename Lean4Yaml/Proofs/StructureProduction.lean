import Lean4Yaml.Proofs.ScalarProduction
import Lean4Yaml.Proofs.StructureCoupling
import Lean4Yaml.Proofs.CharClass

/-! # Structure Production Coupling (Phase C of v0.4.4)

    Strengthen the `_corr` theorems from `StructureCoupling.lean` to
    additionally produce surface-syntax derivation trees for flow indicators,
    block indicators, node properties, and document markers.

    **Strategy**: Each scanner operation that consumes known characters
    produces the corresponding surface syntax derivation as a witness.
    Flow indicators produce `GLit`, block indicators produce `GLit`.
    Anchor/alias scanning produces `GLit marker ∧ GStar (GChar isNsAnchorChar)`.
    Tag and document marker scanners delegate to `_corr` (deferred).
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.StructureProduction

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScannerCoupling
open Lean4Yaml.Proofs.ScalarCoupling
open Lean4Yaml.Proofs.StructureCoupling
open Lean4Yaml.Proofs.ScalarProduction
open Lean4Yaml.Proofs.CharClass

/-! ## §1 Flow Indicator Productions

Each flow indicator scanner advances past a single known character.
The production is `GLit c sp sp'` where `c` is the indicator character.

After unfolding the scanner function, the advance is on the emit'd state
(which preserves input/offset/col/inputEnd), so `advance_non_newline_corr`
applies. The final struct updates (flowLevel, simpleKeyAllowed, etc.) are
non-tracked, so correspondence transfers via field projection. -/

-- `scanFlowSequenceStart` produces `GLit '['`.
theorem scanFlowSequenceStart_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '[') :
    ∃ sp', GLit '[' sp sp' ∧ ScannerSurfCorr (scanFlowSequenceStart sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanFlowSequenceStart
  have hcorr_emit : ScannerSurfCorr
      ({ sc with simpleKey := { possible := false } }.emit .flowSequenceStart)
      ⟨'[' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq⟩
  have hcorr_adv := advance_non_newline_corr
    ({ sc with simpleKey := { possible := false } }.emit .flowSequenceStart)
    '[' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq⟩

-- `scanFlowSequenceEnd` produces `GLit ']'`.
theorem scanFlowSequenceEnd_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some ']') :
    ∃ sp', GLit ']' sp sp' ∧ ScannerSurfCorr (scanFlowSequenceEnd sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanFlowSequenceEnd
  have hcorr_emit : ScannerSurfCorr
      (sc.emit .flowSequenceEnd)
      ⟨']' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq⟩
  have hcorr_adv := advance_non_newline_corr
    (sc.emit .flowSequenceEnd)
    ']' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq⟩

-- `scanFlowMappingStart` produces `GLit '{'`.
theorem scanFlowMappingStart_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '{') :
    ∃ sp', GLit '{' sp sp' ∧ ScannerSurfCorr (scanFlowMappingStart sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanFlowMappingStart
  have hcorr_emit : ScannerSurfCorr
      ({ sc with simpleKey := { possible := false } }.emit .flowMappingStart)
      ⟨'{' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq⟩
  have hcorr_adv := advance_non_newline_corr
    ({ sc with simpleKey := { possible := false } }.emit .flowMappingStart)
    '{' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq⟩

-- `scanFlowMappingEnd` produces `GLit '}'`.
theorem scanFlowMappingEnd_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '}') :
    ∃ sp', GLit '}' sp sp' ∧ ScannerSurfCorr (scanFlowMappingEnd sc) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanFlowMappingEnd
  have hcorr_emit : ScannerSurfCorr
      (sc.emit .flowMappingEnd)
      ⟨'}' :: rest, sc.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq⟩
  have hcorr_adv := advance_non_newline_corr
    (sc.emit .flowMappingEnd)
    '}' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq⟩

-- `scanFlowEntry` preserves correspondence on success.
theorem scanFlowEntry_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (s' : ScannerState) (hok : scanFlowEntry sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' :=
  scanFlowEntry_corr sc sp hcorr s' hok

/-! ## §2 Block Indicator Productions

Block indicators (`-`, `?`, `:`) each advance past a single character.
On success they produce `GLit` for the indicator character.

The main complication vs flow indicators is that block scanners go through
`Except` (for tab-in-indentation checks) and `pushSequenceIndent`/
`pushMappingIndent` (which have an internal `if` that prevents definitional
col equality). The fix: repack `ScannerSurfCorr` with `⟨chars_from, rfl, end_eq⟩`
to use the intermediate state's col, then derive `hmore` from the nonempty
char list. -/

-- Derive `offset < inputEnd` from ScannerSurfCorr with nonempty chars.
-- Used when `peek_some_has_more` doesn't apply (intermediate state's peek?
-- isn't known, but the SurfPos chars are known nonempty after `peek_some_sp`).
theorem corr_nonempty_has_more {sc : ScannerState}
    {c : Char} {rest : List Char} {col : Nat}
    (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩) :
    sc.offset < sc.inputEnd := by
  match hcorr.chars_from with
  | .cons _ hlt _ _ _ _ => have := hcorr.end_eq; omega

-- `scanBlockEntry` produces `GLit '-'`.
theorem scanBlockEntry_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '-')
    (s' : ScannerState) (hok : scanBlockEntry sc = .ok s') :
    ∃ sp', GLit '-' sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · -- !inFlow: pushSequenceIndent
    split at hok
    · simp at hok
    · have h := Except.ok.inj hok; subst h
      have hcorr_ind := pushSequenceIndent_corr sc
        ⟨'-' :: rest, sc.col⟩ hcorr (sc.col : Int)
      have hcorr_emit : ScannerSurfCorr
          ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry)
          ⟨'-' :: rest, sc.col⟩ :=
        ⟨hcorr_ind.chars_from, hcorr_ind.col_eq, hcorr_ind.end_eq⟩
      -- Repack with sc_mid.col to satisfy advance_non_newline_corr
      have hcorr_at : ScannerSurfCorr
          ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry)
          ⟨'-' :: rest,
           ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry).col⟩ :=
        ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq⟩
      have hmore := corr_nonempty_has_more hcorr_at
      have hcorr_adv := advance_non_newline_corr
        ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry)
        '-' rest hcorr_at hmore (by decide) (by decide)
      exact ⟨hcorr_adv.chars_from,
             by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                dsimp only [] at *; omega,
             hcorr_adv.end_eq⟩
  · -- inFlow: no pushSequenceIndent
    have h := Except.ok.inj hok; subst h
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr
        (sc.emit .blockEntry) ⟨'-' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq⟩
    have hcorr_adv := advance_non_newline_corr
      (sc.emit .blockEntry) '-' rest hcorr_emit hmore (by decide) (by decide)
    exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq⟩

-- `scanKey` produces `GLit '?'`.
theorem scanKey_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '?')
    (s' : ScannerState) (hok : scanKey sc = .ok s') :
    ∃ sp', GLit '?' sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · -- !inFlow: pushMappingIndent
    have hcorr_ind := pushMappingIndent_corr sc
      ⟨'?' :: rest, sc.col⟩ hcorr (sc.col : Int)
    have hcorr_emit : ScannerSurfCorr
        ((pushMappingIndent sc (sc.col : Int)).emit .key)
        ⟨'?' :: rest, sc.col⟩ :=
      ⟨hcorr_ind.chars_from, hcorr_ind.col_eq, hcorr_ind.end_eq⟩
    have hcorr_at : ScannerSurfCorr
        ((pushMappingIndent sc (sc.col : Int)).emit .key)
        ⟨'?' :: rest,
         ((pushMappingIndent sc (sc.col : Int)).emit .key).col⟩ :=
      ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq⟩
    have hmore := corr_nonempty_has_more hcorr_at
    have hcorr_adv := advance_non_newline_corr
      ((pushMappingIndent sc (sc.col : Int)).emit .key)
      '?' rest hcorr_at hmore (by decide) (by decide)
    -- Tab check after advance, then .ok
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨hcorr_adv.chars_from,
               by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                  dsimp only [] at *; omega,
               hcorr_adv.end_eq⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨hcorr_adv.chars_from,
             by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                dsimp only [] at *; omega,
             hcorr_adv.end_eq⟩
  · -- inFlow
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr
        (sc.emit .key) ⟨'?' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq⟩
    have hcorr_adv := advance_non_newline_corr
      (sc.emit .key) '?' rest hcorr_emit hmore (by decide) (by decide)
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq⟩

-- `scanValue` produces `GLit ':'`.
theorem scanValue_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some ':')
    (s' : ScannerState) (hok : scanValue sc = .ok s') :
    ∃ sp', GLit ':' sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  refine ⟨⟨rest, sc.col + 1⟩, GLit.mk rest sc.col, ?_⟩
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  -- scanValueValidate (Except)
  split at hok
  · simp at hok
  · -- scanValueTabCheck (Except)
    split at hok
    · simp at hok
    · have h := Except.ok.inj hok; subst h
      have hcorr_ck := scanValueClearKey_corr sc ⟨':' :: rest, sc.col⟩ hcorr
      have hcorr_prep := scanValuePrepare_corr
        (scanValueClearKey sc) ⟨':' :: rest, sc.col⟩ hcorr_ck
      have hcorr_emit : ScannerSurfCorr
          ((scanValuePrepare (scanValueClearKey sc)).emit .value)
          ⟨':' :: rest, sc.col⟩ :=
        ⟨hcorr_prep.chars_from, hcorr_prep.col_eq, hcorr_prep.end_eq⟩
      have hcorr_at : ScannerSurfCorr
          ((scanValuePrepare (scanValueClearKey sc)).emit .value)
          ⟨':' :: rest,
           ((scanValuePrepare (scanValueClearKey sc)).emit .value).col⟩ :=
        ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq⟩
      have hmore := corr_nonempty_has_more hcorr_at
      have hcorr_adv := advance_non_newline_corr
        ((scanValuePrepare (scanValueClearKey sc)).emit .value)
        ':' rest hcorr_at hmore (by decide) (by decide)
      exact ⟨hcorr_adv.chars_from,
             by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                dsimp only [] at *; omega,
             hcorr_adv.end_eq⟩

/-! ## §3 Node Property Productions

Anchor, alias, and tag scanners produce surface syntax derivation trees.
The anchor name loop produces `GStar (GChar isNsAnchorChar)`.
The overall `scanAnchorOrAlias` produces `GLit marker ∧ GStar (GChar isNsAnchorChar)`.
Tag scanning delegates to `_corr` (4-variant analysis deferred). -/

-- Bridge: scanner's Bool conjunction → surface Prop `isNsAnchorChar`.
theorem not_of_bool_false {P : Prop} {b : Bool}
    (h_iff : P ↔ b = true) (hf : b = false) : ¬P :=
  fun hp => by rw [hf] at h_iff; exact absurd (h_iff.mp hp) Bool.false_ne_true

theorem bool_not_true_imp_false {b : Bool} (h : (!b) = true) :
    b = false := by cases b <;> simp_all

theorem isNsAnchorChar_of_scanner_cond {c : Char}
    (h : (!isFlowIndicatorBool c && !isWhiteSpaceBool c &&
          !isLineBreakBool c) = true) :
    isNsAnchorChar c := by
  have hab := Bool.and_eq_true_iff.mp h
  have hfw := Bool.and_eq_true_iff.mp hab.1
  have hfi := bool_not_true_imp_false hfw.1
  have hws := bool_not_true_imp_false hfw.2
  have hlb := bool_not_true_imp_false hab.2
  exact ⟨⟨not_of_bool_false (isLineBreak_correspondence c) hlb,
          not_of_bool_false (isWhiteSpace_correspondence c) hws⟩,
         not_of_bool_false (isFlowIndicator_correspondence c) hfi⟩

-- `collectAnchorNameLoop` produces `GStar (GChar isNsAnchorChar)`.
theorem collectAnchorNameLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (name : String) (fuel : Nat) :
    ∃ sp', GStar (GChar isNsAnchorChar) sp sp' ∧
           ScannerSurfCorr (collectAnchorNameLoop sc name fuel).snd sp' := by
  induction fuel generalizing sc sp name with
  | zero => exact ⟨sp, GStar.nil sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectAnchorNameLoop; split
    · rename_i c hpeek; split
      · -- anchor char: advance and recurse
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        -- Extract isLineBreakBool c = false from conjunction
        have hlb : isLineBreakBool c = false :=
          bool_not_true_imp_false (Bool.and_eq_true_iff.mp hcond).2
        -- c ≠ newlines: rw substitutes the literal, native_decide finishes
        have hne_nl : c ≠ '\n' := by
          intro heq; rw [heq] at hlb; exact absurd hlb (by native_decide)
        have hne_cr : c ≠ '\r' := by
          intro heq; rw [heq] at hlb; exact absurd hlb (by native_decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          hmore hne_nl hne_cr
        obtain ⟨sp', h_tail, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩
          hcorr_adv (name.push c)
        exact ⟨sp',
               GStar.cons _ _ _
                 (GChar.mk c rest sc.col (isNsAnchorChar_of_scanner_cond hcond))
                 h_tail,
               hcorr'⟩
      · -- not anchor char: stop
        exact ⟨sp, GStar.nil sp, hcorr⟩
    · -- none: stop
      exact ⟨sp, GStar.nil sp, hcorr⟩

-- `scanAnchorOrAlias` produces `GLit marker ∧ GStar (GChar isNsAnchorChar)`.
-- The marker character is `&` for anchors and `*` for aliases.
theorem scanAnchorOrAlias_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (isAnchor : Bool)
    (marker : Char) (hpeek : sc.peek? = some marker)
    (hne_nl : marker ≠ '\n') (hne_cr : marker ≠ '\r') :
    ∃ sp_mid sp', GLit marker sp sp_mid ∧
                  GStar (GChar isNsAnchorChar) sp_mid sp' ∧
                  ScannerSurfCorr (scanAnchorOrAlias sc isAnchor) sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  have hcorr_adv := advance_non_newline_corr sc marker rest hcorr
    hmore hne_nl hne_cr
  obtain ⟨sp', h_gstar, hcorr'⟩ :=
    collectAnchorNameLoop_prod sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv "" _
  refine ⟨⟨rest, sc.col + 1⟩, sp', GLit.mk rest sc.col, h_gstar, ?_⟩
  unfold scanAnchorOrAlias
  exact ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq⟩

-- `scanTag` preserves correspondence.
theorem scanTag_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (scanTag sc) sp' :=
  scanTag_corr sc sp hcorr

/-! ## §4 Document Marker Productions

`scanDocumentStart` and `scanDocumentEnd` advance 3 characters past
`---` and `...` respectively. They preserve correspondence. -/

-- `scanDocumentStart` preserves correspondence.
theorem scanDocumentStart_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (scanDocumentStart sc) sp' :=
  scanDocumentStart_corr sc sp hcorr

-- `scanDocumentEnd` preserves correspondence on success.
theorem scanDocumentEnd_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (s' : ScannerState) (hok : scanDocumentEnd sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' :=
  scanDocumentEnd_corr sc sp hcorr s' hok

-- `scanDirective` preserves correspondence on success.
theorem scanDirective_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (s' : ScannerState) (hok : scanDirective sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' :=
  scanDirective_corr sc sp hcorr s' hok

end Lean4Yaml.Proofs.StructureProduction
