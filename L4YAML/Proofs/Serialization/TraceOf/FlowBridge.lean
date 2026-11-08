/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Serialization.TraceOf.Node
public import L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Proofs.Production.StructureProduction
public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Production.Acceptance.Quoted
/-!
# S3 slice (3), first PR — flow indicators and quoted scalars as `TraceOf` leaves
(EVENTSOF §10, capstone 7.7 `parse_iff_grammar`)

The scanner's `[` / `{` / `]` / `}` / `,` arms push exactly their indicator token over a
one-character span (`GLit`, the `Lift`ed leaf of `TraceOf/Node.lean`'s flow relations, trace `[]`),
and `scanDoubleQuoted` / `scanSingleQuoted` push one quoted-scalar token over the quoted lexeme
(`SCDoubleQuoted` / `SCSingleQuoted`, i.e. `TFlowContent … []`).  Every token named here is
trace-inert (`TokenEvents.tokenEvent` is `none`; `goOut_silent`), so what the slice adds to the
bridge is the token / span / landing shape the later flow re-walk composes.  The surface derivations
are `StructureProduction` / `ScalarProduction`'s producers; what is new is the token conclusion,
read off the arm the way `TagShape.scanDoubleQuoted_pushTag` reads it.
Rule 2 first: Priority 102 (`Tests/AdversarialInstantiation.lean`).
-/
namespace L4YAML.Proofs.Serialization.TraceOf.FlowBridge
@[expose] public section
open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.StructureProduction L4YAML.Proofs.ScalarProduction L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.ScannerCorrectness.ScanHelpers

/-- The token `[` / `{` / `]` / `}` / `,` push: one `Positioned` at the current position. -/
abbrev indicatorTok (sc : ScannerState) (v : YamlToken) : Positioned YamlToken :=
  Positioned.mk sc.currentPos v sc.currentPos

/-- `[`: `scanFlowSequenceStart` pushes `.flowSequenceStart` over `GLit '['`, trace `[]`. -/
lemma scanFlowSequenceStart_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '[') :
    ∃ sp', (scanFlowSequenceStart sc).tokens = sc.tokens.push (indicatorTok sc .flowSequenceStart) ∧
      ScannerSurfCorr (scanFlowSequenceStart sc) sp' ∧ Lift (GLit '[') sp sp' [] := by
  obtain ⟨sp', hglit, hcorr'⟩ := scanFlowSequenceStart_prod sc sp hcorr hpeek
  refine ⟨sp', ?_, hcorr', hglit, rfl⟩
  simp only [scanFlowSequenceStart, ScannerState.emit, advance_preserves_tokens, indicatorTok,
    ScannerState.currentPos]

/-- `{`: `scanFlowMappingStart` pushes `.flowMappingStart` over `GLit '{'`, trace `[]`. -/
lemma scanFlowMappingStart_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '{') :
    ∃ sp', (scanFlowMappingStart sc).tokens = sc.tokens.push (indicatorTok sc .flowMappingStart) ∧
      ScannerSurfCorr (scanFlowMappingStart sc) sp' ∧ Lift (GLit '{') sp sp' [] := by
  obtain ⟨sp', hglit, hcorr'⟩ := scanFlowMappingStart_prod sc sp hcorr hpeek
  refine ⟨sp', ?_, hcorr', hglit, rfl⟩
  simp only [scanFlowMappingStart, ScannerState.emit, advance_preserves_tokens, indicatorTok,
    ScannerState.currentPos]

/-- `]`: `scanFlowSequenceEnd` pushes `.flowSequenceEnd` over `GLit ']'`, trace `[]`. -/
lemma scanFlowSequenceEnd_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some ']') :
    ∃ sp', (scanFlowSequenceEnd sc).tokens = sc.tokens.push (indicatorTok sc .flowSequenceEnd) ∧
      ScannerSurfCorr (scanFlowSequenceEnd sc) sp' ∧ Lift (GLit ']') sp sp' [] := by
  obtain ⟨sp', hglit, hcorr'⟩ := scanFlowSequenceEnd_prod sc sp hcorr hpeek
  refine ⟨sp', ?_, hcorr', hglit, rfl⟩
  simp only [scanFlowSequenceEnd, ScannerState.emit, advance_preserves_tokens, indicatorTok]

/-- `}`: `scanFlowMappingEnd` pushes `.flowMappingEnd` over `GLit '}'`, trace `[]`. -/
lemma scanFlowMappingEnd_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '}') :
    ∃ sp', (scanFlowMappingEnd sc).tokens = sc.tokens.push (indicatorTok sc .flowMappingEnd) ∧
      ScannerSurfCorr (scanFlowMappingEnd sc) sp' ∧ Lift (GLit '}') sp sp' [] := by
  obtain ⟨sp', hglit, hcorr'⟩ := scanFlowMappingEnd_prod sc sp hcorr hpeek
  refine ⟨sp', ?_, hcorr', hglit, rfl⟩
  simp only [scanFlowMappingEnd, ScannerState.emit, advance_preserves_tokens, indicatorTok]

/-- `,`: an accepted `scanFlowEntry` pushes `.flowEntry` over `GLit ','`, trace `[]`. -/
lemma scanFlowEntry_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some ',')
    (s' : ScannerState) (hok : scanFlowEntry sc = .ok s') :
    ∃ sp', s'.tokens = sc.tokens.push (indicatorTok sc .flowEntry) ∧
      ScannerSurfCorr s' sp' ∧ Lift (GLit ',') sp sp' [] := by
  obtain ⟨sp', hglit, hcorr'⟩ := scanFlowEntry_glit sc sp hcorr hpeek s' hok
  refine ⟨sp', ?_, hcorr', hglit, rfl⟩
  unfold scanFlowEntry at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp only [ScannerState.emit, advance_preserves_tokens, indicatorTok]
  · have h := Except.ok.inj hok; subst h
    simp only [ScannerState.emit, advance_preserves_tokens, indicatorTok]

/-- `"…"`: an accepted `scanDoubleQuoted` pushes one `.scalar v .doubleQuoted` at the opening quote,
over an `SCDoubleQuoted 0 .blockIn` span — `TFlowContent.doubleQ`, trace `[]`. -/
lemma scanDoubleQuoted_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '"')
    (s' : ScannerState) (hok : scanDoubleQuoted sc = .ok s') :
    ∃ sp' v, s'.tokens = sc.tokens.push (indicatorTok sc (.scalar v .doubleQuoted)) ∧
      ScannerSurfCorr s' sp' ∧ TFlowContent 0 .blockIn sp sp' [] := by
  obtain ⟨sp', hdq, _, hcorr'⟩ := scanDoubleQuoted_prod sc sp hcorr hpeek hok
  have htr : TFlowContent 0 .blockIn sp sp' [] := TFlowContent.doubleQ _ _ _ _ hdq
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  rename_i heq
  have h_collect := collectDoubleQuotedLoop_preserves_tokens sc.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens sc
  split at hok
  · split at hok <;> try contradiction
    injection hok with h_eq; subst h_eq
    exact ⟨sp', _, by simp only [ScannerState.emitAt, indicatorTok]; rw [h_collect, h_adv], hcorr', htr⟩
  · injection hok with h_eq; subst h_eq
    exact ⟨sp', _, by simp only [ScannerState.emitAt, indicatorTok]; rw [h_collect, h_adv], hcorr', htr⟩

/-- `'…'`: the single-quoted twin — `TFlowContent.singleQ`, trace `[]`. -/
lemma scanSingleQuoted_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp) (hpeek : sc.peek? = some '\'')
    (s' : ScannerState) (hok : scanSingleQuoted sc = .ok s') :
    ∃ sp' v, s'.tokens = sc.tokens.push (indicatorTok sc (.scalar v .singleQuoted)) ∧
      ScannerSurfCorr s' sp' ∧ TFlowContent 0 .blockIn sp sp' [] := by
  obtain ⟨sp', hsq, _, hcorr'⟩ := scanSingleQuoted_prod sc sp hcorr hpeek hok
  have htr : TFlowContent 0 .blockIn sp sp' [] := TFlowContent.singleQ _ _ _ _ hsq
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  rename_i heq
  have h_collect := collectSingleQuotedLoop_preserves_tokens sc.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens sc
  split at hok
  · split at hok <;> try contradiction
    injection hok with h_eq; subst h_eq
    exact ⟨sp', _, by simp only [ScannerState.emitAt, indicatorTok]; rw [h_collect, h_adv], hcorr', htr⟩
  · injection hok with h_eq; subst h_eq
    exact ⟨sp', _, by simp only [ScannerState.emitAt, indicatorTok]; rw [h_collect, h_adv], hcorr', htr⟩

/-- Every token this module pushes is silent under `goOut`, from any pending state. -/
lemma goOut_indicator (sc : ScannerState) (v : YamlToken)
    (hv : TokenEvents.tokenEvent v = none) (p : List String)
    (hds : v ≠ .documentStart) (hdir : ∀ h pfx, v ≠ .tagDirective h pfx) :
    TokenEvents.goOut [indicatorTok sc v] p = ([], p) := by
  rw [TokenEvents.goOut_silent (indicatorTok sc v) hv hds hdir [] p]; rfl

end

end L4YAML.Proofs.Serialization.TraceOf.FlowBridge
