/-
Copyright (c) 2025 NASA Jet Propulsion Laboratory. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.Document
public import L4YAML.Proofs.Serialization.TokenEvents
public import L4YAML.Proofs.Production.StructureProduction
public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Output.EmitterScannability.FilteredGrowth

/-!
# S3 slice (2): the document-marker bridge (capstone 7.7, item 462)

The scanner's `scanDocumentStart` / `scanDocumentEnd` / `scanDirective` arms land on the
surface relations `TraceOf/Document.lean` annotates (`SCDirectivesEnd`, `SCDocumentEnd`,
`ScannedDirective` — `SLDirective` once the line tail is read), and the tokens each arm
pushes read, through `TokenEvents.goOut`, as exactly the event list the annotation
carries: `---` is `beginDocument` followed by the pending `%TAG` handles as `declareTag`
in directive order; `...` is `endDocument`; a directive emits nothing and leaves
`declaredHandle` of its span pending — `TLDirective`'s payload, from the scanner's handle.
-/

namespace L4YAML.Proofs.Serialization.TraceOf.DocBridge

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.TokenEvents
open L4YAML.Proofs.Serialization.TraceOf
open L4YAML.Proofs.StructureProduction L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCorrectness (advanceN_preserves_tokens skipWhitespace_preserves_tokens
  skipToEndOfLine_preserves_tokens)
open L4YAML.Proofs.EmitterScannability (scanYamlDirective_new_token_eq scanTagDirective_new_token_eq)

/-- `unwindIndentsLoop` appends `blockEnd`s and nothing else. -/
lemma unwindIndentsLoop_tokens_append (col : Int) : ∀ (fuel : Nat) (s : ScannerState),
    ∃ ends : List (Positioned YamlToken),
      (unwindIndentsLoop s col fuel).tokens.toList = s.tokens.toList ++ ends ∧
      ∀ t ∈ ends, t.val = .blockEnd := by
  intro fuel
  induction fuel with
  | zero => intro s; exact ⟨[], by simp [unwindIndentsLoop], by simp⟩
  | succ f ih =>
    intro s
    unfold unwindIndentsLoop
    split
    · obtain ⟨ends, hM, hall⟩ := ih _
      refine ⟨{ pos := s.currentPos, val := .blockEnd } :: ends, ?_, ?_⟩
      · rw [hM]; simp [ScannerState.emit]
      · intro t ht; simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · rfl
        · exact hall t ht
    · exact ⟨[], by simp, by simp⟩

lemma unwindIndents_tokens_append (s : ScannerState) (col : Int) :
    ∃ ends : List (Positioned YamlToken),
      (unwindIndents s col).tokens.toList = s.tokens.toList ++ ends ∧
      ∀ t ∈ ends, t.val = .blockEnd :=
  unwindIndentsLoop_tokens_append col _ s

/-- The tokens `scanDocumentStart` pushes: the unwound `blockEnd`s, then `documentStart`. -/
lemma scanDocumentStart_tokens (sc : ScannerState) :
    ∃ (ends : List (Positioned YamlToken)) (ds : Positioned YamlToken),
      (scanDocumentStart sc).tokens.toList = sc.tokens.toList ++ ends ++ [ds] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ ds.val = .documentStart := by
  obtain ⟨ends, hends, hall⟩ := unwindIndents_tokens_append sc (-1)
  refine ⟨ends, { pos := (unwindIndents sc (-1)).currentPos, val := .documentStart }, ?_, hall, rfl⟩
  simp only [scanDocumentStart, advanceN_preserves_tokens, ScannerState.emit]
  (simp [hends] <;> rfl)

/-- The tokens `scanDocumentEnd` pushes when it accepts: the unwound `blockEnd`s, then
`documentEnd`. -/
lemma scanDocumentEnd_tokens (sc s' : ScannerState) (hok : scanDocumentEnd sc = .ok s') :
    ∃ (ends : List (Positioned YamlToken)) (de : Positioned YamlToken),
      s'.tokens.toList = sc.tokens.toList ++ ends ++ [de] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ de.val = .documentEnd := by
  obtain ⟨ends, hends, hall⟩ := unwindIndents_tokens_append sc (-1)
  refine ⟨ends, { pos := (unwindIndents sc (-1)).currentPos, val := .documentEnd }, ?_, hall, rfl⟩
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · exact absurd hok (by simp)
  · have hres : ∀ r, (.ok r : Except ScanError ScannerState) = .ok s' → r = s' :=
      fun r h => Except.ok.inj h
    split at hok
    · have := hres _ hok; subst this
      simp only [advanceN_preserves_tokens, ScannerState.emit]; (simp [hends] <;> rfl)
    · have := hres _ hok; subst this
      simp only [advanceN_preserves_tokens, ScannerState.emit]; (simp [hends] <;> rfl)
    · split at hok
      · have := hres _ hok; subst this
        simp only [advanceN_preserves_tokens, ScannerState.emit]; (simp [hends] <;> rfl)
      · exact absurd hok (by simp)

/-- What the marker's tokens say to `goOut`: `---` is `beginDocument` then the pending
handles, in directive order, and clears them. -/
lemma goOut_marker_start (ends : List (Positioned YamlToken)) (ds : Positioned YamlToken)
    (hends : ∀ t ∈ ends, t.val = .blockEnd) (hds : ds.val = .documentStart) (p : List String) :
    goOut (ends ++ [ds]) p = (.beginDocument :: p.reverse.map .declareTag, []) := by
  rw [goOut_blockEnds ends hends, goOut_documentStart ds hds]; simp

/-- `...` is `endDocument`; the pending handles are untouched. -/
lemma goOut_marker_end (ends : List (Positioned YamlToken)) (de : Positioned YamlToken)
    (hends : ∀ t ∈ ends, t.val = .blockEnd) (hde : de.val = .documentEnd) (p : List String) :
    goOut (ends ++ [de]) p = ([.endDocument], p) := by
  rw [goOut_blockEnds ends hends, goOut_documentEnd de hde]; simp

/-- **`---`**: the scanner's document start is `[203] c-directives-end` on its span, and the
tokens it pushes read `beginDocument :: declareTag*` of the pending handles. -/
lemma scanDocumentStart_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (rest : List Char) (hchars : sp.chars = '-' :: '-' :: '-' :: rest)
    (hcol : sp.col = 0) :
    ∃ (sp' : SurfPos) (ends : List (Positioned YamlToken)) (ds : Positioned YamlToken),
      SCDirectivesEnd sp sp' ∧ ScannerSurfCorr (scanDocumentStart sc) sp' ∧
      (scanDocumentStart sc).tokens.toList = sc.tokens.toList ++ ends ++ [ds] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ ds.val = .documentStart ∧
      ∀ p, goOut (ends ++ [ds]) p = (.beginDocument :: p.reverse.map .declareTag, []) := by
  obtain ⟨sp', hprod, hcorr'⟩ := scanDocumentStart_prod sc sp hcorr rest hchars hcol
  obtain ⟨ends, ds, htoks, hends, hds⟩ := scanDocumentStart_tokens sc
  exact ⟨sp', ends, ds, hprod, hcorr', htoks, hends, hds, goOut_marker_start ends ds hends hds⟩

/-- **`...`**: the scanner's document end is `[204] c-document-end` on its span, and the
tokens it pushes read `[endDocument]`, the pending handles untouched. -/
lemma scanDocumentEnd_trace (sc : ScannerState) (sp : SurfPos)
    (hcorr : ScannerSurfCorr sc sp)
    (rest : List Char) (hchars : sp.chars = '.' :: '.' :: '.' :: rest)
    (hcol : sp.col = 0)
    (s' : ScannerState) (hok : scanDocumentEnd sc = .ok s') :
    ∃ (sp' : SurfPos) (ends : List (Positioned YamlToken)) (de : Positioned YamlToken),
      SCDocumentEnd sp sp' ∧ ScannerSurfCorr s' sp' ∧
      s'.tokens.toList = sc.tokens.toList ++ ends ++ [de] ∧
      (∀ t ∈ ends, t.val = .blockEnd) ∧ de.val = .documentEnd ∧
      ∀ p, goOut (ends ++ [de]) p = ([.endDocument], p) := by
  obtain ⟨sp', hprod, hcorr'⟩ := scanDocumentEnd_prod sc sp hcorr rest hchars hcol s' hok
  obtain ⟨ends, de, htoks, hends, hde⟩ := scanDocumentEnd_tokens sc s' hok
  exact ⟨sp', ends, de, hprod, hcorr', htoks, hends, hde, goOut_marker_end ends de hends hde⟩

end L4YAML.Proofs.Serialization.TraceOf.DocBridge
