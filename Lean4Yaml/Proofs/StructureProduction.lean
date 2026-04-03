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
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr
    ({ sc with simpleKey := { possible := false } }.emit .flowSequenceStart)
    '[' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

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
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr
    (sc.emit .flowSequenceEnd)
    ']' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

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
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr
    ({ sc with simpleKey := { possible := false } }.emit .flowMappingStart)
    '{' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

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
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have hcorr_adv := advance_non_newline_corr
    (sc.emit .flowMappingEnd)
    '}' rest hcorr_emit hmore (by decide) (by decide)
  exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

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
        ⟨'-' :: rest, sc.col⟩ hcorr (sc.col : Int) (Int.natCast_nonneg _)
      have hcorr_emit : ScannerSurfCorr
          ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry)
          ⟨'-' :: rest, sc.col⟩ :=
        ⟨hcorr_ind.chars_from, hcorr_ind.col_eq, hcorr_ind.end_eq, hcorr_ind.input_prefix, hcorr_ind.indent_cols_nonneg⟩
      -- Repack with sc_mid.col to satisfy advance_non_newline_corr
      have hcorr_at : ScannerSurfCorr
          ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry)
          ⟨'-' :: rest,
           ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry).col⟩ :=
        ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
      have hmore := corr_nonempty_has_more hcorr_at
      have hcorr_adv := advance_non_newline_corr
        ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry)
        '-' rest hcorr_at hmore (by decide) (by decide)
      exact ⟨hcorr_adv.chars_from,
             by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                dsimp only [] at *; omega,
             hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
  · -- inFlow: no pushSequenceIndent
    have h := Except.ok.inj hok; subst h
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr
        (sc.emit .blockEntry) ⟨'-' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    have hcorr_adv := advance_non_newline_corr
      (sc.emit .blockEntry) '-' rest hcorr_emit hmore (by decide) (by decide)
    exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

-- Bridge: isBlankBool c → ¬isNsChar c (converse of not_blank_to_nsChar in ScalarProduction).
theorem blank_to_not_nsChar {c : Char}
    (h : isBlankBool c = true) : ¬isNsChar c := by
  simp [isNsChar, isLineBreakProp, isWhiteSpaceProp, isBlankBool, isWhiteSpaceBool,
    isLineBreakBool, beq_iff_eq] at *
  intro h1 h2 h3
  rcases h with (rfl | rfl) | rfl | rfl <;> first | contradiction | rfl

-- GNot SNsChar at position after block entry indicator, given isBlockEntryCandidate.
-- The scanner checks `peekAt? 1` = blank/EOF. After advancing past `-`, the head
-- of the remaining chars is the character that was at `peekAt? 1`.
theorem blockEntryCandidate_gnot (sc : ScannerState) (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨'-' :: rest, col⟩)
    (h_candidate : isBlockEntryCandidate sc = true) :
    GNot SNsChar ⟨rest, col + 1⟩ := by
  intro s' h_ns
  cases rest with
  | nil => cases h_ns
  | cons c rest' =>
    cases h_ns with
    | mk c' rest'' col' h_pred =>
      have h_peekAt : sc.peekAt? 1 = some c := by
        unfold ScannerState.peekAt?
        have hlt : sc.offset < sc.inputEnd := by
          rw [hcorr.end_eq]
          exact match hcorr.chars_from with | .cons _ h _ _ _ _ => h
        rw [peekAtLoop_step hlt]
        have hcf_tail := chars_from_cons_tail hcorr.chars_from
        have hlt_next : (String.Pos.Raw.next sc.input ⟨sc.offset⟩).byteIdx < sc.inputEnd := by
          rw [hcorr.end_eq]
          exact match hcf_tail with | .cons _ h _ _ _ _ => h
        exact peekAtLoop_cons hlt_next hcf_tail
      unfold isBlockEntryCandidate at h_candidate
      rw [h_peekAt] at h_candidate
      exact blank_to_not_nsChar h_candidate h_pred

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
      ⟨'?' :: rest, sc.col⟩ hcorr (sc.col : Int) (Int.natCast_nonneg _)
    have hcorr_emit : ScannerSurfCorr
        ((pushMappingIndent sc (sc.col : Int)).emit .key)
        ⟨'?' :: rest, sc.col⟩ :=
      ⟨hcorr_ind.chars_from, hcorr_ind.col_eq, hcorr_ind.end_eq, hcorr_ind.input_prefix, hcorr_ind.indent_cols_nonneg⟩
    have hcorr_at : ScannerSurfCorr
        ((pushMappingIndent sc (sc.col : Int)).emit .key)
        ⟨'?' :: rest,
         ((pushMappingIndent sc (sc.col : Int)).emit .key).col⟩ :=
      ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
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
               hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨hcorr_adv.chars_from,
             by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                dsimp only [] at *; omega,
             hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
  · -- inFlow
    have hmore := peek_some_has_more hpeek
    have hcorr_emit : ScannerSurfCorr
        (sc.emit .key) ⟨'?' :: rest, sc.col⟩ :=
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    have hcorr_adv := advance_non_newline_corr
      (sc.emit .key) '?' rest hcorr_emit hmore (by decide) (by decide)
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

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
        ⟨hcorr_prep.chars_from, hcorr_prep.col_eq, hcorr_prep.end_eq, hcorr_prep.input_prefix, hcorr_prep.indent_cols_nonneg⟩
      have hcorr_at : ScannerSurfCorr
          ((scanValuePrepare (scanValueClearKey sc)).emit .value)
          ⟨':' :: rest,
           ((scanValuePrepare (scanValueClearKey sc)).emit .value).col⟩ :=
        ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
      have hmore := corr_nonempty_has_more hcorr_at
      have hcorr_adv := advance_non_newline_corr
        ((scanValuePrepare (scanValueClearKey sc)).emit .value)
        ':' rest hcorr_at hmore (by decide) (by decide)
      exact ⟨hcorr_adv.chars_from,
             by have h1 := hcorr_emit.col_eq; have h2 := hcorr_adv.col_eq
                dsimp only [] at *; omega,
             hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩

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
-- When starting from empty name and the result name grew, positions differ (sp ≠ sp').
theorem collectAnchorNameLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (name : String) (fuel : Nat) :
    ∃ sp', GStar (GChar isNsAnchorChar) sp sp' ∧
           ScannerSurfCorr (collectAnchorNameLoop sc name fuel).snd sp' ∧
           (sp = sp' → (collectAnchorNameLoop sc name fuel).fst = name) := by
  induction fuel generalizing sc sp name with
  | zero => exact ⟨sp, GStar.nil sp, hcorr, fun _ => rfl⟩
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
        obtain ⟨sp', h_tail, hcorr', _⟩ := ih sc.advance ⟨rest, sc.col + 1⟩
          hcorr_adv (name.push c)
        refine ⟨sp',
               GStar.cons _ _ _
                 (GChar.mk c rest sc.col (isNsAnchorChar_of_scanner_cond hcond))
                 h_tail,
               hcorr', ?_⟩
        intro h_eq; exfalso
        have h_col_ge : sp'.col ≥ sc.col + 1 := gstar_gchar_col_le h_tail
        have : sp'.col = sc.col := by rw [← h_eq]
        omega
      · -- not anchor char: stop
        exact ⟨sp, GStar.nil sp, hcorr, fun _ => rfl⟩
    · -- none: stop
      exact ⟨sp, GStar.nil sp, hcorr, fun _ => rfl⟩

-- `scanAnchorOrAlias` produces `GLit marker ∧ GStar (GChar isNsAnchorChar)` with `sp_mid ≠ sp'`.
-- The marker character is `&` for anchors and `*` for aliases.
-- Since `.ok` requires a non-empty name (A10 Except conversion), the GStar is always non-empty.
theorem scanAnchorOrAlias_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (isAnchor : Bool)
    (marker : Char) (hpeek : sc.peek? = some marker)
    (hne_nl : marker ≠ '\n') (hne_cr : marker ≠ '\r')
    (s' : ScannerState) (hok : scanAnchorOrAlias sc isAnchor = .ok s') :
    ∃ sp_mid sp', GLit marker sp sp_mid ∧
                  GStar (GChar isNsAnchorChar) sp_mid sp' ∧
                  sp_mid ≠ sp' ∧
                  ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  have hcorr_adv := advance_non_newline_corr sc marker rest hcorr
    hmore hne_nl hne_cr
  obtain ⟨sp', h_gstar, hcorr', h_sp_name⟩ :=
    collectAnchorNameLoop_prod sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv "" _
  refine ⟨⟨rest, sc.col + 1⟩, sp', GLit.mk rest sc.col, h_gstar, ?_, ?_⟩
  · -- sp_mid ≠ sp': .ok requires non-empty name, which requires sp advance
    intro h_eq
    have h_name_empty := h_sp_name h_eq
    unfold scanAnchorOrAlias at hok; dsimp only [] at hok
    rw [h_name_empty] at hok; simp at hok
  · unfold scanAnchorOrAlias at hok; dsimp only [] at hok
    split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      exact ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩

/-! ### Tag suffix loop production -/

-- `collectTagSuffixLoop` produces `GStar (GChar isTagCharProp)`.
theorem collectTagSuffixLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (suffix : String) (fuel : Nat) :
    ∃ sp', GStar (GChar isTagCharProp) sp sp' ∧
           ScannerSurfCorr (collectTagSuffixLoop sc suffix fuel).snd sp' := by
  induction fuel generalizing sc sp suffix with
  | zero => exact ⟨sp, GStar.nil sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectTagSuffixLoop; split
    · rename_i c hpeek; split
      · -- tag char: advance and recurse
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have htag : isTagCharProp c := (isTagChar_iff c).mp hcond
        have hne_nl : c ≠ '\n' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hne_cr : c ≠ '\r' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          hmore hne_nl hne_cr
        obtain ⟨sp', h_tail, hcorr'⟩ := ih sc.advance ⟨rest, sc.col + 1⟩
          hcorr_adv (suffix.push c)
        exact ⟨sp',
               GStar.cons _ _ _
                 (GChar.mk c rest sc.col htag)
                 h_tail,
               hcorr'⟩
      · -- not tag char: stop
        exact ⟨sp, GStar.nil sp, hcorr⟩
    · -- none: stop
      exact ⟨sp, GStar.nil sp, hcorr⟩

/-! ### Verbatim tag URI loop production -/

-- `collectVerbatimTagLoop` produces `GStar (GChar isUriCharProp)` for URI chars.
-- When the loop terminates at `>`, also produces `GLit '>'`.
-- Links grammar positions to scanner-level `foundClose` and `uri` values.
theorem collectVerbatimTagLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (uri : String) (fuel : Nat) :
    ∃ sp_mid sp', GStar (GChar isUriCharProp) sp sp_mid ∧
                  ScannerSurfCorr (collectVerbatimTagLoop sc uri fuel).snd.snd sp' ∧
                  (sp_mid = sp' ∨ GLit '>' sp_mid sp') ∧
                  (sp_mid = sp' → (collectVerbatimTagLoop sc uri fuel).snd.fst = false) ∧
                  (sp = sp_mid → (collectVerbatimTagLoop sc uri fuel).fst = uri) := by
  induction fuel generalizing sc sp uri with
  | zero => exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl rfl, fun _ => rfl, fun _ => rfl⟩
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop; split
    · -- peek? = some '>': advance past > and produce GLit
      rename_i hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      have hcorr_adv := advance_non_newline_corr sc '>' rest hcorr
        hmore (by decide) (by decide)
      exact ⟨⟨'>' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
             GStar.nil _,
             hcorr_adv,
             Or.inr (GLit.mk rest sc.col),
             fun h => by simp only [SurfPos.mk.injEq] at h; omega,
             fun _ => rfl⟩
    · -- peek? = some c (c ≠ '>'): check isUriCharBool
      rename_i c _ hpeek; split
      · -- isUriCharBool c = true: advance and recurse
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have huri : isUriCharProp c := (isUriChar_iff c).mp hcond
        have hne_nl : c ≠ '\n' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hne_cr : c ≠ '\r' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          hmore hne_nl hne_cr
        obtain ⟨sp_mid, sp', h_tail, hcorr', h_gt, h_close_link, _⟩ :=
          ih sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv (uri.push c)
        refine ⟨sp_mid, sp',
               GStar.cons _ _ sp_mid
                 (GChar.mk c rest sc.col huri)
                 h_tail,
               hcorr', h_gt, h_close_link, ?_⟩
        intro h_eq; exfalso
        have h_col_ge : sp_mid.col ≥ sc.col + 1 := gstar_gchar_col_le h_tail
        have : sp_mid.col = sc.col := by rw [← h_eq]
        omega
      · -- isUriCharBool c = false: stop
        exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl rfl, fun _ => rfl, fun _ => rfl⟩
    · -- peek? = none: stop
      exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl rfl, fun _ => rfl, fun _ => rfl⟩

/-! ### Tag handle loop production -/

-- `collectTagHandleLoop` produces `GStar (GChar isWordCharProp)` for word chars.
-- When the loop terminates at `!`, also produces `GLit '!'` and `foundBang = true`.
-- When stopping without `!`, produces `foundBang = false` and `sp_mid = sp'`.
theorem collectTagHandleLoop_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (chars : String) (fuel : Nat) :
    ∃ sp_mid sp', GStar (GChar isWordCharProp) sp sp_mid ∧
                  ScannerSurfCorr (collectTagHandleLoop sc chars fuel).snd.snd sp' ∧
                  ((sp_mid = sp' ∧ (collectTagHandleLoop sc chars fuel).snd.fst = false) ∨
                   (GLit '!' sp_mid sp' ∧ (collectTagHandleLoop sc chars fuel).snd.fst = true)) := by
  induction fuel generalizing sc sp chars with
  | zero => exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl ⟨rfl, rfl⟩⟩
  | succ fuel' ih =>
    unfold collectTagHandleLoop; split
    · -- peek? = some '!': advance past ! and produce GLit
      rename_i hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      have hcorr_adv := advance_non_newline_corr sc '!' rest hcorr
        hmore (by decide) (by decide)
      exact ⟨⟨'!' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
             GStar.nil _,
             hcorr_adv,
             Or.inr ⟨GLit.mk rest sc.col, rfl⟩⟩
    · -- peek? = some c (c ≠ '!'): check isWordCharBool
      rename_i c _ hpeek; split
      · -- isWordCharBool c = true: advance and recurse
        rename_i hcond
        obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
        subst hsp_eq
        have hmore := peek_some_has_more hpeek
        have hword : isWordCharProp c := (isWordChar_iff c).mp hcond
        have hne_nl : c ≠ '\n' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hne_cr : c ≠ '\r' := by
          intro heq; rw [heq] at hcond; exact absurd hcond (by native_decide)
        have hcorr_adv := advance_non_newline_corr sc c rest hcorr
          hmore hne_nl hne_cr
        obtain ⟨sp_mid, sp', h_tail, hcorr', h_bang⟩ :=
          ih sc.advance ⟨rest, sc.col + 1⟩ hcorr_adv (chars.push c)
        exact ⟨sp_mid, sp',
               GStar.cons _ _ sp_mid
                 (GChar.mk c rest sc.col hword)
                 h_tail,
               hcorr', h_bang⟩
      · -- isWordCharBool c = false: stop
        exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl ⟨rfl, rfl⟩⟩
    · -- peek? = none: stop
      exact ⟨sp, sp, GStar.nil sp, hcorr, Or.inl ⟨rfl, rfl⟩⟩

-- `scanTag` on the secondary branch (`!!suffix`) produces `SCNsTagProperty.secondary`.
-- Preconditions: first char `!`, second char `!`.
theorem scanTag_secondary_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '!') (hpeek2 : sc.advance.peek? = some '!')
    (s' : ScannerState) (hok : scanTag sc = .ok s') :
    ∃ sp', SCNsTagProperty sp sp' ∧ ScannerSurfCorr s' sp' := by
  -- Decompose first `!`
  obtain ⟨rest1, hsp_eq1⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq1
  have hmore1 := peek_some_has_more hpeek
  have hcorr_bang := advance_non_newline_corr sc '!' rest1 hcorr
    hmore1 (by decide) (by decide)
  -- Decompose second `!`
  obtain ⟨srest, hrest1_eq⟩ := peek_some_sp hcorr_bang hpeek2
  have hchars_eq := congrArg SurfPos.chars hrest1_eq
  dsimp only [] at hchars_eq; subst hchars_eq
  -- Now sp = ⟨'!' :: '!' :: srest, sc.col⟩
  -- Repack hcorr_bang with rfl col for advance_non_newline_corr
  have hcorr_bang' : ScannerSurfCorr sc.advance ⟨'!' :: srest, sc.advance.col⟩ :=
    ⟨hcorr_bang.chars_from, rfl, hcorr_bang.end_eq, hcorr_bang.input_prefix, hcorr_bang.indent_cols_nonneg⟩
  have hmore2 := peek_some_has_more hpeek2
  have hcorr_bang2 := advance_non_newline_corr sc.advance '!' srest hcorr_bang'
    hmore2 (by decide) (by decide)
  -- Repack for suffix loop with rfl col
  have hcorr_bang2' : ScannerSurfCorr sc.advance.advance
      ⟨srest, sc.advance.advance.col⟩ :=
    ⟨hcorr_bang2.chars_from, rfl, hcorr_bang2.end_eq, hcorr_bang2.input_prefix, hcorr_bang2.indent_cols_nonneg⟩
  -- Unfold scanTag and resolve match to secondary branch
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · -- some '<': contradicts hpeek2
    rename_i h_lt
    exact absurd (h_lt ▸ hpeek2) (by decide)
  · -- some '!': secondary tag
    have h_inj := Except.ok.inj hok; subst h_inj
    unfold scanSecondaryTag; dsimp only []
    obtain ⟨sp', h_gstar, hcorr_sfx⟩ :=
      collectTagSuffixLoop_prod sc.advance.advance ⟨srest, sc.advance.advance.col⟩
        hcorr_bang2' "" _
    -- Bridge col: sc.advance.advance.col = sc.col + 2
    have hcol_bridge : sc.advance.advance.col = sc.col + 2 := by
      have := hcorr_bang.col_eq; have := hcorr_bang2.col_eq
      dsimp only [] at *; omega
    rw [hcol_bridge] at h_gstar
    refine ⟨sp', SCNsTagProperty.secondary srest sc.col sp' h_gstar, ?_⟩
    exact ⟨hcorr_sfx.chars_from, hcorr_sfx.col_eq, hcorr_sfx.end_eq, hcorr_sfx.input_prefix, hcorr_sfx.indent_cols_nonneg⟩
  · -- fallthrough: contradicts hpeek2
    rename_i _ h_not_bang
    exact absurd hpeek2 h_not_bang

-- `scanTag` on non-secondary branches produces `SCNsTagProperty`.
-- Handles verbatim `!<uri>`, named `!handle!suffix`, and non-specific `!`.
-- Verbatim well-formed case fully proven. S8/S9 closed via A10 Except + linking lemmas.
-- S10 (named/non-specific) still sorry'd.
theorem scanTag_nonSecondary_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some '!') (hpeek2 : ¬(sc.advance.peek? = some '!'))
    (s' : ScannerState) (hok : scanTag sc = .ok s') :
    ∃ sp', SCNsTagProperty sp sp' ∧ ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  subst hsp_eq
  have hmore := peek_some_has_more hpeek
  have hcorr_bang := advance_non_newline_corr sc '!' rest hcorr
    hmore (by decide) (by decide)
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · -- sc.advance.peek? = some '<': verbatim tag
    rename_i hpeek_lt
    obtain ⟨rest2, hrest_eq⟩ := peek_some_sp hcorr_bang hpeek_lt
    have hchars_eq := congrArg SurfPos.chars hrest_eq
    dsimp only [] at hchars_eq; subst hchars_eq
    have hmore2 := peek_some_has_more hpeek_lt
    have hcorr_lt := advance_non_newline_corr sc.advance '<' rest2
      ⟨hcorr_bang.chars_from, rfl, hcorr_bang.end_eq, hcorr_bang.input_prefix, hcorr_bang.indent_cols_nonneg⟩
      hmore2 (by decide) (by decide)
    have hcorr_loop : ScannerSurfCorr sc.advance.advance ⟨rest2, sc.advance.advance.col⟩ :=
      ⟨hcorr_lt.chars_from, rfl, hcorr_lt.end_eq, hcorr_lt.input_prefix, hcorr_lt.indent_cols_nonneg⟩
    -- Separate the monadic bind from scanTag's do block
    simp only [bind, Except.bind] at hok
    generalize h_verb : scanVerbatimTag sc.advance sc.currentPos = verb_result at hok
    cases verb_result with
    | error e => simp at hok
    | ok s_verb =>
      -- hok has Pure.pure wrapped; normalize to Except.ok for injection
      change Except.ok { s_verb with simpleKeyAllowed := false } = Except.ok s' at hok
      have hok_eq := Except.ok.inj hok; subst hok_eq
      -- Unfold scanVerbatimTag at the clean h_verb (no Bind.bind wrapper)
      unfold scanVerbatimTag at h_verb; dsimp only [] at h_verb
      split at h_verb
      · exact absurd h_verb (by simp)  -- unterminatedVerbatimTag error
      · rename_i h_fc_true  -- ¬(!foundClose = true), i.e., foundClose = true
        split at h_verb
        · exact absurd h_verb (by simp)  -- emptyVerbatimTagURI error
        · rename_i h_uri_ne  -- ¬(uri.isEmpty = true), i.e., uri ≠ ""
          have h_sv := Except.ok.inj h_verb
          obtain ⟨sp_mid, sp', h_gstar, hcorr_uri, h_gt_or_eq, h_close_link, h_uri_link⟩ :=
            collectVerbatimTagLoop_prod sc.advance.advance ⟨rest2, sc.advance.advance.col⟩
              hcorr_loop "" _
          have hcol2 : sc.advance.advance.col = sc.col + 2 := by
            have := hcorr_bang.col_eq; have := hcorr_lt.col_eq; dsimp only [] at *; omega
          rw [hcol2] at h_gstar h_uri_link
          -- Build ScannerSurfCorr for { s_verb with simpleKeyAllowed := false }
          have hcorr_sv : ScannerSurfCorr s_verb sp' := by
            rw [← h_sv]; exact corr_of_emitAt _ _ hcorr_uri
          cases h_gt_or_eq with
          | inl h_eq =>
            -- S8: No '>' found — impossible since scanVerbatimTag returned .ok
            -- h_close_link gives foundClose = false, contradicting the split
            exfalso; simp [h_close_link h_eq] at h_fc_true
          | inr h_glit =>
            by_cases hne : ⟨rest2, sc.col + 2⟩ = sp_mid
            · -- S9: Empty URI !<> — impossible since scanVerbatimTag returned .ok
              -- h_uri_link gives uri = "", contradicting the split
              exfalso; simp [h_uri_link hne] at h_uri_ne
            · -- Well-formed !<uri>: construct verbatim evidence
              exact ⟨sp',
                     SCNsTagProperty.verbatim ('<' :: rest2) sc.col
                       ⟨rest2, sc.col + 2⟩ sp_mid sp'
                       (GLit.mk rest2 (sc.col + 1)) (GStar_to_GPlus h_gstar hne) h_glit,
                     corr_of_simpleKeyAllowed_update false hcorr_sv⟩
  · -- sc.advance.peek? = some '!': contradiction
    rename_i h_bang
    exact absurd h_bang hpeek2
  · -- catch-all: named/non-specific via scanNamedTag
    rename_i h_not_lt h_not_bang
    have h_inj := Except.ok.inj hok; subst h_inj
    obtain ⟨sp', hcorr'⟩ := scanNamedTag_corr sc.advance
      ⟨rest, sc.advance.col⟩
      ⟨hcorr_bang.chars_from, rfl, hcorr_bang.end_eq, hcorr_bang.input_prefix, hcorr_bang.indent_cols_nonneg⟩
      sc.currentPos sc.inputEnd
    -- S10: Named/non-specific: sorry for grammar (pending scanNamedTag full decomposition)
    exact ⟨sp', sorry,
      ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩

-- `scanTag` preserves correspondence on all branches.
theorem scanTag_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanTag sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' :=
  scanTag_corr sc sp hcorr s' hok

/-! ## §4 Document Marker Productions

`scanDocumentStart` and `scanDocumentEnd` advance 3 characters past
`---` and `...` respectively. When the start position has `col = 0`
and the chars are the expected marker sequence, these produce
`SCDirectivesEnd` / `SCDocumentEnd` witnesses.

Helper: `unwindIndents_corr_exact` shows `unwindIndents` preserves the
exact surface position (not just existential). -/

-- `unwindIndentsLoop` preserves the exact surface position.
theorem unwindIndentsLoop_corr_exact (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) (fuel : Nat) :
    ScannerSurfCorr (unwindIndentsLoop sc col fuel) sp := by
  induction fuel generalizing sc with
  | zero => simp [unwindIndentsLoop]; exact hcorr
  | succ fuel' ih =>
    unfold unwindIndentsLoop; split
    · exact ih { (sc.emit .blockEnd) with indents := _ }
        ⟨(corr_of_emit .blockEnd hcorr).chars_from,
         (corr_of_emit .blockEnd hcorr).col_eq,
         (corr_of_emit .blockEnd hcorr).end_eq, (corr_of_emit .blockEnd hcorr).input_prefix,
         fun i hi h0 => by
           simp only [ScannerState.emit] at hi ⊢
           rw [Array.getElem_pop]
           exact hcorr.indent_cols_nonneg i (by simp [Array.size_pop] at hi; omega) h0⟩
    · exact hcorr

-- `unwindIndents` preserves the exact surface position.
theorem unwindIndents_corr_exact (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) :
    ScannerSurfCorr (unwindIndents sc col) sp := by
  unfold unwindIndents
  exact unwindIndentsLoop_corr_exact sc sp hcorr col _

-- `scanDocumentStart` produces `SCDirectivesEnd` when chars = `---rest` at col 0.
theorem scanDocumentStart_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (rest : List Char) (hchars : sp.chars = '-' :: '-' :: '-' :: rest)
    (hcol : sp.col = 0) :
    ∃ sp', SCDirectivesEnd sp sp' ∧ ScannerSurfCorr (scanDocumentStart sc) sp' := by
  cases sp with | mk chars col =>
  dsimp only [] at hchars hcol ⊢
  subst hchars; subst hcol
  refine ⟨⟨rest, 3⟩, SCDirectivesEnd.mk rest, ?_⟩
  unfold scanDocumentStart
  simp only [ScannerState.advanceN, ScannerState.advanceNLoop]
  -- Thread through unwindIndents (preserves exact position)
  have hcorr_uw := unwindIndents_corr_exact sc ⟨'-' :: '-' :: '-' :: rest, 0⟩ hcorr (-1)
  have hcorr_key : ScannerSurfCorr
      { (unwindIndents sc (-1)) with simpleKey := { possible := false } }
      ⟨'-' :: '-' :: '-' :: rest, 0⟩ :=
    ⟨hcorr_uw.chars_from, hcorr_uw.col_eq, hcorr_uw.end_eq, hcorr_uw.input_prefix, hcorr_uw.indent_cols_nonneg⟩
  have hcorr_emit := corr_of_emit .documentStart hcorr_key
  -- Advance past first '-'
  have hcorr_at1 : ScannerSurfCorr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart)
      ⟨'-' :: '-' :: '-' :: rest,
       ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).col⟩ :=
    ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
  have hmore1 := corr_nonempty_has_more hcorr_at1
  have hcorr_adv1 := advance_non_newline_corr
    ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart)
    '-' ('-' :: '-' :: rest) hcorr_at1 hmore1 (by decide) (by decide)
  -- Advance past second '-'
  have hcorr_at2 : ScannerSurfCorr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance
      ⟨'-' :: '-' :: rest,
       ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance.col⟩ :=
    ⟨hcorr_adv1.chars_from, rfl, hcorr_adv1.end_eq, hcorr_adv1.input_prefix, hcorr_adv1.indent_cols_nonneg⟩
  have hmore2 := corr_nonempty_has_more hcorr_at2
  have hcorr_adv2 := advance_non_newline_corr
    ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance
    '-' ('-' :: rest) hcorr_at2 hmore2 (by decide) (by decide)
  -- Advance past third '-'
  have hcorr_at3 : ScannerSurfCorr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance.advance
      ⟨'-' :: rest,
       ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance.advance.col⟩ :=
    ⟨hcorr_adv2.chars_from, rfl, hcorr_adv2.end_eq, hcorr_adv2.input_prefix, hcorr_adv2.indent_cols_nonneg⟩
  have hmore3 := corr_nonempty_has_more hcorr_at3
  have hcorr_adv3 := advance_non_newline_corr
    ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart).advance.advance
    '-' rest hcorr_at3 hmore3 (by decide) (by decide)
  -- Final: ScannerSurfCorr (scanDocumentStart sc) ⟨rest, 3⟩
  exact ⟨hcorr_adv3.chars_from,
         by have h0 := hcorr_emit.col_eq
            have h1 := hcorr_adv1.col_eq
            have h2 := hcorr_adv2.col_eq
            have h3 := hcorr_adv3.col_eq
            dsimp only [] at *; omega,
         hcorr_adv3.end_eq, hcorr_adv3.input_prefix, hcorr_adv3.indent_cols_nonneg⟩

-- `scanDocumentEnd` produces `SCDocumentEnd` when chars = `...rest` at col 0.
theorem scanDocumentEnd_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (rest : List Char) (hchars : sp.chars = '.' :: '.' :: '.' :: rest)
    (hcol : sp.col = 0)
    (s' : ScannerState) (hok : scanDocumentEnd sc = .ok s') :
    ∃ sp', SCDocumentEnd sp sp' ∧ ScannerSurfCorr s' sp' := by
  cases sp with | mk chars col =>
  dsimp only [] at hchars hcol ⊢
  subst hchars; subst hcol
  refine ⟨⟨rest, 3⟩, SCDocumentEnd.mk rest, ?_⟩
  -- Unfold and handle Except
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · exact absurd hok (by simp)
  · -- Build correspondence through unwindIndents + emit + advanceN 3
    have hcorr_uw := unwindIndents_corr_exact sc
      ⟨'.' :: '.' :: '.' :: rest, 0⟩ hcorr (-1)
    have hcorr_key : ScannerSurfCorr
        { (unwindIndents sc (-1)) with simpleKey := { possible := false } }
        ⟨'.' :: '.' :: '.' :: rest, 0⟩ :=
      ⟨hcorr_uw.chars_from, hcorr_uw.col_eq, hcorr_uw.end_eq, hcorr_uw.input_prefix, hcorr_uw.indent_cols_nonneg⟩
    have hcorr_emit := corr_of_emit .documentEnd hcorr_key
    -- Advance past first '.'
    have hcorr_at1 : ScannerSurfCorr
        ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd)
        ⟨'.' :: '.' :: '.' :: rest,
         ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).col⟩ :=
      ⟨hcorr_emit.chars_from, rfl, hcorr_emit.end_eq, hcorr_emit.input_prefix, hcorr_emit.indent_cols_nonneg⟩
    have hmore1 := corr_nonempty_has_more hcorr_at1
    have hcorr_adv1 := advance_non_newline_corr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd)
      '.' ('.' :: '.' :: rest) hcorr_at1 hmore1 (by decide) (by decide)
    -- Advance past second '.'
    have hcorr_at2 : ScannerSurfCorr
        ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance
        ⟨'.' :: '.' :: rest,
         ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.col⟩ :=
      ⟨hcorr_adv1.chars_from, rfl, hcorr_adv1.end_eq, hcorr_adv1.input_prefix, hcorr_adv1.indent_cols_nonneg⟩
    have hmore2 := corr_nonempty_has_more hcorr_at2
    have hcorr_adv2 := advance_non_newline_corr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance
      '.' ('.' :: rest) hcorr_at2 hmore2 (by decide) (by decide)
    -- Advance past third '.'
    have hcorr_at3 : ScannerSurfCorr
        ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.advance
        ⟨'.' :: rest,
         ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.advance.col⟩ :=
      ⟨hcorr_adv2.chars_from, rfl, hcorr_adv2.end_eq, hcorr_adv2.input_prefix, hcorr_adv2.indent_cols_nonneg⟩
    have hmore3 := corr_nonempty_has_more hcorr_at3
    have hcorr_adv3 := advance_non_newline_corr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.advance
      '.' rest hcorr_at3 hmore3 (by decide) (by decide)
    -- Handle the validation match (all OK paths yield s' = result)
    -- Each OK branch gives s' = result; derive correspondence
    have mk_corr : ScannerSurfCorr
        { ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd).advance.advance.advance with
          simpleKeyAllowed := true, allowDirectives := true,
          directivesPresent := false, definedAnchors := #[] }
        ⟨rest, 3⟩ := by
      exact ⟨hcorr_adv3.chars_from,
             by have h0 := hcorr_emit.col_eq
                have h1 := hcorr_adv1.col_eq
                have h2 := hcorr_adv2.col_eq
                have h3 := hcorr_adv3.col_eq
                dsimp only [] at *; omega,
             hcorr_adv3.end_eq, hcorr_adv3.input_prefix, hcorr_adv3.indent_cols_nonneg⟩
    split at hok
    · have h := Except.ok.inj hok; subst h; exact mk_corr
    · have h := Except.ok.inj hok; subst h; exact mk_corr
    · split at hok
      · have h := Except.ok.inj hok; subst h; exact mk_corr
      · exact absurd hok (by simp)

-- `scanDirective` preserves correspondence on success.
theorem scanDirective_prod (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (s' : ScannerState) (hok : scanDirective sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' :=
  scanDirective_corr sc sp hcorr s' hok

end Lean4Yaml.Proofs.StructureProduction
