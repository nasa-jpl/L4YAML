/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Proofs.ScalarCoupling

/-!
# Structure, Document & Directive Coupling

Coupling theorems for structural scanning: flow/block indicators,
node properties (anchors + tags), indentation management,
document boundaries, and directives.

Each function preserves `ScannerSurfCorr` on every `.ok` return path.
Most field updates (tokens, flowLevel, indents, flowStack, simpleKey,
simpleKeyStack, simpleKeyAllowed, explicitKeyLine, allowDirectives,
seenYamlDirective, directivesPresent, documentEverStarted, definedAnchors)
are irrelevant to correspondence since they only affect fields outside
`ScannerSurfCorr`'s 4-field window (input, offset, col, inputEnd).
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.StructureCoupling

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.CharPredicates
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScannerCoupling
open Lean4Yaml.Proofs.ScalarCoupling

/-! ## §1 Shared Helpers -/

/-- `emit` only modifies `tokens`, preserving correspondence. -/
theorem corr_of_emit {sc : ScannerState} {sp : SurfPos}
    (tok : YamlToken)
    (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr (sc.emit tok) sp :=
  ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩

/-- `advanceNLoop` preserves correspondence by composing `advance_corr`. -/
theorem advanceNLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (n : Nat) :
    ∃ sp', ScannerSurfCorr (sc.advanceNLoop n) sp' := by
  induction n generalizing sc sp with
  | zero => exact ⟨sp, hcorr⟩
  | succ n' ih =>
    simp only [ScannerState.advanceNLoop]
    obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
    exact ih sc.advance sp' hcorr'

/-- `advanceN` preserves correspondence (wrapper for `advanceNLoop`). -/
theorem advanceN_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (n : Nat) :
    ∃ sp', ScannerSurfCorr (sc.advanceN n) sp' := by
  unfold ScannerState.advanceN
  exact advanceNLoop_corr sc sp hcorr n

/-! ## §2 Flow Indicators -/

theorem scanFlowSequenceStart_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (scanFlowSequenceStart sc) sp' := by
  unfold scanFlowSequenceStart
  obtain ⟨sp', hcorr'⟩ := advance_corr
    ({ sc with simpleKey := { possible := false } }.emit .flowSequenceStart) sp
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩

theorem scanFlowSequenceEnd_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (scanFlowSequenceEnd sc) sp' := by
  unfold scanFlowSequenceEnd
  obtain ⟨sp', hcorr'⟩ := advance_corr (sc.emit .flowSequenceEnd) sp
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩

theorem scanFlowMappingStart_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (scanFlowMappingStart sc) sp' := by
  unfold scanFlowMappingStart
  obtain ⟨sp', hcorr'⟩ := advance_corr
    ({ sc with simpleKey := { possible := false } }.emit .flowMappingStart) sp
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩

theorem scanFlowMappingEnd_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (scanFlowMappingEnd sc) sp' := by
  unfold scanFlowMappingEnd
  obtain ⟨sp', hcorr'⟩ := advance_corr (sc.emit .flowMappingEnd) sp
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩

theorem scanFlowEntry_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanFlowEntry sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanFlowEntry at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      obtain ⟨sp', hcorr'⟩ := advance_corr (sc.emit .flowEntry) sp
        ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
      exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  · have h := Except.ok.inj hok; subst h
    obtain ⟨sp', hcorr'⟩ := advance_corr (sc.emit .flowEntry) sp
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩

/-! ## §3 Indentation Management -/

theorem unwindIndentsLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (unwindIndentsLoop sc col fuel) sp' := by
  induction fuel generalizing sc sp with
  | zero => simp [unwindIndentsLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold unwindIndentsLoop; split
    · have hcorr_emit := corr_of_emit .blockEnd hcorr
      exact ih { (sc.emit .blockEnd) with indents := _ } sp
        ⟨hcorr_emit.chars_from, hcorr_emit.col_eq, hcorr_emit.end_eq, hcorr_emit.input_prefix,
         fun i hi h0 => by
           simp only [ScannerState.emit] at hi ⊢
           rw [Array.getElem_pop]
           exact hcorr.indent_cols_nonneg i (by simp [Array.size_pop] at hi; omega) h0⟩
    · exact ⟨sp, hcorr⟩

theorem unwindIndents_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) :
    ∃ sp', ScannerSurfCorr (unwindIndents sc col) sp' := by
  unfold unwindIndents
  exact unwindIndentsLoop_corr sc sp hcorr col _

theorem pushSequenceIndent_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) (hcol : col ≥ 0) :
    ScannerSurfCorr (pushSequenceIndent sc col) sp := by
  unfold pushSequenceIndent; split
  · exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix,
           fun i hi h0 => by
             simp only [ScannerState.emit] at hi ⊢
             by_cases h : i < sc.indents.size
             · rw [Array.getElem_push_lt h]; exact hcorr.indent_cols_nonneg i h h0
             · have : i = sc.indents.size := by
                 simp [Array.size_push] at hi; omega
               subst this; rw [Array.getElem_push_eq]; exact hcol⟩
  · exact hcorr

theorem pushMappingIndent_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (col : Int) (hcol : col ≥ 0) :
    ScannerSurfCorr (pushMappingIndent sc col) sp := by
  unfold pushMappingIndent; split
  · exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix,
           fun i hi h0 => by
             simp only [ScannerState.emit] at hi ⊢
             by_cases h : i < sc.indents.size
             · rw [Array.getElem_push_lt h]; exact hcorr.indent_cols_nonneg i h h0
             · have : i = sc.indents.size := by
                 simp [Array.size_push] at hi; omega
               subst this; rw [Array.getElem_push_eq]; exact hcol⟩
  · exact hcorr

/-! ## §4 Node Properties: Anchor & Tag Collection Loops -/

theorem collectAnchorNameLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (name : String) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (collectAnchorNameLoop sc name fuel).snd sp' := by
  induction fuel generalizing sc sp name with
  | zero => simp [collectAnchorNameLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectAnchorNameLoop; split
    · rename_i c _; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr' (name.push c)
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

theorem scanAnchorOrAlias_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (isAnchor : Bool) (s' : ScannerState)
    (hok : scanAnchorOrAlias sc isAnchor = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanAnchorOrAlias at hok
  dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h
    obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
    obtain ⟨sp_name, hcorr_name⟩ :=
      collectAnchorNameLoop_corr sc.advance sp_adv hcorr_adv "" _
    exact ⟨sp_name, ⟨hcorr_name.chars_from, hcorr_name.col_eq, hcorr_name.end_eq, hcorr_name.input_prefix, hcorr_name.indent_cols_nonneg⟩⟩

theorem collectVerbatimTagLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (uri : String) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (collectVerbatimTagLoop sc uri fuel).snd.snd sp' := by
  induction fuel generalizing sc sp uri with
  | zero => simp [collectVerbatimTagLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop; split
    · -- some '>'
      obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
      exact ⟨sp', hcorr'⟩
    · -- some c, isUriCharBool
      split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr' _
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

theorem collectTagSuffixLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (suffix : String) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (collectTagSuffixLoop sc suffix fuel).snd sp' := by
  induction fuel generalizing sc sp suffix with
  | zero => simp [collectTagSuffixLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectTagSuffixLoop; split
    · rename_i c _; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr' (suffix.push c)
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

theorem collectTagHandleLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (chars : String) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (collectTagHandleLoop sc chars fuel).snd.snd sp' := by
  induction fuel generalizing sc sp chars with
  | zero => simp [collectTagHandleLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectTagHandleLoop; split
    · -- some '!'
      obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
      exact ⟨sp', hcorr'⟩
    · -- some c, isWordCharBool
      split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr' _
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

/-! ## §5 Node Properties: Tag Scanning -/

theorem scanVerbatimTag_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (startPos : YamlPos) (s' : ScannerState)
    (hok : scanVerbatimTag sc startPos = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanVerbatimTag at hok
  dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
      obtain ⟨sp_uri, hcorr_uri⟩ :=
        collectVerbatimTagLoop_corr sc.advance sp_adv hcorr_adv "" _
      exact ⟨sp_uri, ⟨hcorr_uri.chars_from, hcorr_uri.col_eq, hcorr_uri.end_eq, hcorr_uri.input_prefix, hcorr_uri.indent_cols_nonneg⟩⟩

theorem scanSecondaryTag_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (startPos : YamlPos) :
    ∃ sp', ScannerSurfCorr (scanSecondaryTag sc startPos) sp' := by
  unfold scanSecondaryTag
  obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr sc sp hcorr
  obtain ⟨sp_sfx, hcorr_sfx⟩ :=
    collectTagSuffixLoop_corr sc.advance sp_adv hcorr_adv "" _
  exact ⟨sp_sfx, ⟨hcorr_sfx.chars_from, hcorr_sfx.col_eq, hcorr_sfx.end_eq, hcorr_sfx.input_prefix, hcorr_sfx.indent_cols_nonneg⟩⟩

theorem scanNamedTag_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (startPos : YamlPos) (inputEnd : Nat) :
    ∃ sp', ScannerSurfCorr (scanNamedTag sc startPos inputEnd) sp' := by
  unfold scanNamedTag; dsimp only []
  obtain ⟨sp_hdl, hcorr_hdl⟩ :=
    collectTagHandleLoop_corr sc sp hcorr "" _
  split
  · -- foundBang = true: collect suffix
    obtain ⟨sp_sfx, hcorr_sfx⟩ :=
      collectTagSuffixLoop_corr _ sp_hdl hcorr_hdl "" _
    exact ⟨sp_sfx, ⟨hcorr_sfx.chars_from, hcorr_sfx.col_eq, hcorr_sfx.end_eq, hcorr_sfx.input_prefix, hcorr_sfx.indent_cols_nonneg⟩⟩
  · -- foundBang = false
    exact ⟨sp_hdl, ⟨hcorr_hdl.chars_from, hcorr_hdl.col_eq, hcorr_hdl.end_eq, hcorr_hdl.input_prefix, hcorr_hdl.indent_cols_nonneg⟩⟩

theorem scanTag_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanTag sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanTag at hok; dsimp only [] at hok
  obtain ⟨sp_bang, hcorr_bang⟩ := advance_corr sc sp hcorr
  split at hok
  · -- verbatim: do-block with ← scanVerbatimTag
    simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag sc.advance sc.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok
      have h := Except.ok.inj hok; subst h
      obtain ⟨sp', hcorr'⟩ := scanVerbatimTag_corr sc.advance sp_bang hcorr_bang _ s_verb hv
      exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  · have h := Except.ok.inj hok; subst h
    obtain ⟨sp', hcorr'⟩ := scanSecondaryTag_corr sc.advance sp_bang hcorr_bang _
    exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  · have h := Except.ok.inj hok; subst h
    obtain ⟨sp', hcorr'⟩ := scanNamedTag_corr sc.advance sp_bang hcorr_bang sc.currentPos sc.inputEnd
    exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩

/-! ## §6 Block Structure -/

theorem scanValueClearKey_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr (scanValueClearKey sc) sp := by
  unfold scanValueClearKey
  split
  · split
    · exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    · split
      · exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
      · exact hcorr
  · exact hcorr

theorem scanValuePrepare_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr (scanValuePrepare sc) sp := by
  unfold scanValuePrepare
  split
  · -- simpleKey.possible
    split
    · -- !inFlow
      split
      · -- col > currentIndent (push mapping indent with simpleKey tokens)
        exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix,
               fun i hi h0 => by
                 by_cases h : i < sc.indents.size
                 · rw [Array.getElem_push_lt h]; exact hcorr.indent_cols_nonneg i h h0
                 · have : i = sc.indents.size := by
                     simp [Array.size_push] at hi; omega
                   subst this; rw [Array.getElem_push_eq]; exact Int.natCast_nonneg _⟩
      · -- col ≤ currentIndent
        exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    · -- inFlow
      exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  · -- !simpleKey.possible
    split
    · exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    · split
      · exact pushMappingIndent_corr sc sp hcorr _ (Int.natCast_nonneg _)
      · exact hcorr

theorem saveSimpleKey_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ScannerSurfCorr (saveSimpleKey sc) sp := by
  unfold saveSimpleKey
  split
  · exact hcorr
  · split
    · exact ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    · exact hcorr

theorem scanBlockEntry_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanBlockEntry sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · -- !inFlow
    split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      have hcorr_ind := pushSequenceIndent_corr sc sp hcorr (sc.col : Int) (Int.natCast_nonneg _)
      obtain ⟨sp', hcorr'⟩ := advance_corr
        ((pushSequenceIndent sc (sc.col : Int)).emit .blockEntry) sp
        ⟨hcorr_ind.chars_from, hcorr_ind.col_eq, hcorr_ind.end_eq, hcorr_ind.input_prefix, hcorr_ind.indent_cols_nonneg⟩
      exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩
  · -- inFlow
    have h := Except.ok.inj hok; subst h
    obtain ⟨sp', hcorr'⟩ := advance_corr (sc.emit .blockEntry) sp
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩

theorem scanKey_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanKey sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  -- The first let: s_with_indent := if !s.inFlow then pushMappingIndent ...
  -- After bind/Except.bind simplification, we split on !inFlow
  split at hok
  · -- !inFlow: pushMappingIndent
    have hcorr_ind := pushMappingIndent_corr sc sp hcorr (sc.col : Int) (Int.natCast_nonneg _)
    obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr
      ((pushMappingIndent sc (sc.col : Int)).emit .key) sp
      ⟨hcorr_ind.chars_from, hcorr_ind.col_eq, hcorr_ind.end_eq, hcorr_ind.input_prefix, hcorr_ind.indent_cols_nonneg⟩
    -- Tab check after advance (still in !inFlow branch)
    split at hok
    · split at hok
      · exact absurd hok (by simp)
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_adv, ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨sp_adv, ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩⟩
  · -- inFlow
    obtain ⟨sp_adv, hcorr_adv⟩ := advance_corr (sc.emit .key) sp
      ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
    split at hok
    · split at hok
      · exact absurd hok (by simp)
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_adv, ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨sp_adv, ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩⟩

theorem scanValue_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanValue sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  -- scanValueValidate returns Except ScanError Unit
  split at hok
  · exact absurd hok (by simp) -- validate error
  · -- scanValueTabCheck returns Except ScanError Unit
    split at hok
    · exact absurd hok (by simp) -- tabCheck error
    · have h := Except.ok.inj hok; subst h
      have hcorr_ck := scanValueClearKey_corr sc sp hcorr
      have hcorr_prep := scanValuePrepare_corr (scanValueClearKey sc) sp hcorr_ck
      obtain ⟨sp', hcorr'⟩ := advance_corr
        ((scanValuePrepare (scanValueClearKey sc)).emit .value) sp
        ⟨hcorr_prep.chars_from, hcorr_prep.col_eq, hcorr_prep.end_eq, hcorr_prep.input_prefix, hcorr_prep.indent_cols_nonneg⟩
      exact ⟨sp', ⟨hcorr'.chars_from, hcorr'.col_eq, hcorr'.end_eq, hcorr'.input_prefix, hcorr'.indent_cols_nonneg⟩⟩

/-! ## §7 Document Boundaries -/

theorem skipDocEndWhitespace_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (skipDocEndWhitespace sc fuel) sp' := by
  induction fuel generalizing sc sp with
  | zero => simp [skipDocEndWhitespace]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold skipDocEndWhitespace; split
    · rename_i c _; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr'
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

theorem scanDocumentStart_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) :
    ∃ sp', ScannerSurfCorr (scanDocumentStart sc) sp' := by
  unfold scanDocumentStart
  obtain ⟨sp_uw, hcorr_uw⟩ := unwindIndents_corr sc sp hcorr (-1)
  obtain ⟨sp_adv, hcorr_adv⟩ := advanceN_corr
    ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentStart)
    sp_uw ⟨hcorr_uw.chars_from, hcorr_uw.col_eq, hcorr_uw.end_eq, hcorr_uw.input_prefix, hcorr_uw.indent_cols_nonneg⟩ 3
  exact ⟨sp_adv, ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩⟩

theorem scanDocumentEnd_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanDocumentEnd sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · exact absurd hok (by simp) -- directiveWithoutDocument
  · obtain ⟨sp_uw, hcorr_uw⟩ := unwindIndents_corr sc sp hcorr (-1)
    obtain ⟨sp_adv, hcorr_adv⟩ := advanceN_corr
      ({ (unwindIndents sc (-1)) with simpleKey := { possible := false } }.emit .documentEnd)
      sp_uw ⟨hcorr_uw.chars_from, hcorr_uw.col_eq, hcorr_uw.end_eq, hcorr_uw.input_prefix, hcorr_uw.indent_cols_nonneg⟩ 3
    -- The match s''.peek? only validates; result is returned unchanged
    split at hok
    · have h := Except.ok.inj hok; subst h
      exact ⟨sp_adv, ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨sp_adv, ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩⟩
    · split at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_adv, ⟨hcorr_adv.chars_from, hcorr_adv.col_eq, hcorr_adv.end_eq, hcorr_adv.input_prefix, hcorr_adv.indent_cols_nonneg⟩⟩
      · exact absurd hok (by simp)

/-! ## §8 Directive Collection Loops -/

theorem collectDirectiveNameLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (name : String) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (collectDirectiveNameLoop sc name fuel).snd sp' := by
  induction fuel generalizing sc sp name with
  | zero => simp [collectDirectiveNameLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectDirectiveNameLoop; split
    · rename_i c _; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr' (name.push c)
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

theorem collectVersionMajorLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (major : String) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (collectVersionMajorLoop sc major fuel).snd sp' := by
  induction fuel generalizing sc sp major with
  | zero => simp [collectVersionMajorLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectVersionMajorLoop; split
    · -- some '.'
      obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
      exact ⟨sp', hcorr'⟩
    · -- some c, isDigit
      split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr' _
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

theorem collectVersionMinorLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (minor : String) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (collectVersionMinorLoop sc minor fuel).snd sp' := by
  induction fuel generalizing sc sp minor with
  | zero => simp [collectVersionMinorLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectVersionMinorLoop; split
    · rename_i c _; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr' (minor.push c)
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

theorem collectTagHandleDirectiveLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (handle : String) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (collectTagHandleDirectiveLoop sc handle fuel).snd sp' := by
  induction fuel generalizing sc sp handle with
  | zero => simp [collectTagHandleDirectiveLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectTagHandleDirectiveLoop; split
    · rename_i c _; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr' (handle.push c)
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

theorem collectTagPrefixLoop_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (pfx : String) (fuel : Nat) :
    ∃ sp', ScannerSurfCorr (collectTagPrefixLoop sc pfx fuel).snd sp' := by
  induction fuel generalizing sc sp pfx with
  | zero => simp [collectTagPrefixLoop]; exact ⟨sp, hcorr⟩
  | succ fuel' ih =>
    unfold collectTagPrefixLoop; split
    · rename_i c _; split
      · obtain ⟨sp', hcorr'⟩ := advance_corr sc sp hcorr
        exact ih sc.advance sp' hcorr' (pfx.push c)
      · exact ⟨sp, hcorr⟩
    · exact ⟨sp, hcorr⟩

/-! ## §9 Directive Scanning -/

theorem scanYamlDirective_corr (sc : ScannerState)
    (s_after_ws : ScannerState) (sp_ws : SurfPos)
    (hcorr_ws : ScannerSurfCorr s_after_ws sp_ws)
    (startPos : YamlPos) (s' : ScannerState)
    (hok : scanYamlDirective sc s_after_ws startPos = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanYamlDirective at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · exact absurd hok (by simp) -- duplicateYamlDirective
  · obtain ⟨sp_major, hcorr_major⟩ :=
      collectVersionMajorLoop_corr s_after_ws sp_ws hcorr_ws "" _
    obtain ⟨sp_minor, hcorr_minor⟩ :=
      collectVersionMinorLoop_corr _ sp_major hcorr_major "" _
    obtain ⟨sp_ws2, _, hcorr_ws2⟩ :=
      skipWhitespace_corr _ sp_minor hcorr_minor
    -- trailing content validation (3-way match on peek?)
    split at hok
    · -- some '#'
      split at hok
      · exact absurd hok (by simp)
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_ws2, ⟨hcorr_ws2.chars_from, hcorr_ws2.col_eq, hcorr_ws2.end_eq, hcorr_ws2.input_prefix, hcorr_ws2.indent_cols_nonneg⟩⟩
    · -- some c
      split at hok
      · exact absurd hok (by simp)
      · have h := Except.ok.inj hok; subst h
        exact ⟨sp_ws2, ⟨hcorr_ws2.chars_from, hcorr_ws2.col_eq, hcorr_ws2.end_eq, hcorr_ws2.input_prefix, hcorr_ws2.indent_cols_nonneg⟩⟩
    · -- none
      have h := Except.ok.inj hok; subst h
      exact ⟨sp_ws2, ⟨hcorr_ws2.chars_from, hcorr_ws2.col_eq, hcorr_ws2.end_eq, hcorr_ws2.input_prefix, hcorr_ws2.indent_cols_nonneg⟩⟩

theorem scanTagDirective_corr (sc : ScannerState) (sp : SurfPos)
    (_hcorr : ScannerSurfCorr sc sp) (s_after_ws : ScannerState) (sp_ws : SurfPos)
    (hcorr_ws : ScannerSurfCorr s_after_ws sp_ws)
    (startPos : YamlPos) (s' : ScannerState)
    (hok : scanTagDirective sc s_after_ws startPos = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanTagDirective at hok
  -- scanTagDirective is pure (no bind/throw), just let bindings ending in .ok
  have h := Except.ok.inj hok; subst h
  obtain ⟨sp_hdl, hcorr_hdl⟩ :=
    collectTagHandleDirectiveLoop_corr s_after_ws sp_ws hcorr_ws "" _
  obtain ⟨sp_ws2, _, hcorr_ws2⟩ :=
    skipWhitespace_corr _ sp_hdl hcorr_hdl
  obtain ⟨sp_pfx, hcorr_pfx⟩ :=
    collectTagPrefixLoop_corr _ sp_ws2 hcorr_ws2 "" _
  exact ⟨sp_pfx, ⟨hcorr_pfx.chars_from, hcorr_pfx.col_eq, hcorr_pfx.end_eq, hcorr_pfx.input_prefix, hcorr_pfx.indent_cols_nonneg⟩⟩

theorem scanDirective_corr (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (s' : ScannerState)
    (hok : scanDirective sc = .ok s') :
    ∃ sp', ScannerSurfCorr s' sp' := by
  unfold scanDirective at hok
  split at hok
  · exact absurd hok (by simp) -- directiveAfterContent
  · dsimp only [] at hok
    obtain ⟨sp_pct, hcorr_pct⟩ := advance_corr sc sp hcorr
    obtain ⟨sp_name, hcorr_name⟩ :=
      collectDirectiveNameLoop_corr sc.advance sp_pct hcorr_pct "" _
    obtain ⟨sp_ws, _, hcorr_ws⟩ :=
      skipWhitespace_corr _ sp_name hcorr_name
    split at hok
    · -- YAML directive
      exact scanYamlDirective_corr sc _ sp_ws hcorr_ws _ _ hok
    · split at hok
      · -- TAG directive
        exact scanTagDirective_corr sc sp hcorr _ sp_ws hcorr_ws _ _ hok
      · -- reserved directive: skipToEndOfLine
        have h := Except.ok.inj hok; subst h
        obtain ⟨sp', _, hcorr'⟩ := skipToEndOfLine_corr _ sp_ws hcorr_ws
        exact ⟨sp', hcorr'⟩

end Lean4Yaml.Proofs.StructureCoupling
