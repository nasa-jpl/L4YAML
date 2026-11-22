/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Proofs.Serialization.TraceOf.Node

/-!
# Event-annotated documents and stream (EVENTSOF-CONCEPT §10)

Hand-written twins of `Surface/Document.lean`'s productions.  Two orderings
are fixed here rather than read off the text: a document's `beginDocument`
precedes the `declareTag`s of the `%TAG` directives that textually precede its
`---` (`RuntimeScopes.documentEvents`), and `...` is `endDocument`.
`SLYamlStream.scannerDrop` has no twin: the annotated stream is the intended
grammar, so `scan ok → TLYamlStream …` (S3) is available only once Row 12
retires the drop.
-/

namespace L4YAML.Proofs.Serialization.TraceOf

@[expose] public section

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.EventsOf (declaredHandle)

/-- Annotated `[82] l-directive`: a `%TAG` with a named handle declares it. -/
def TLDirective : TRel :=
  fun s s' ev => SLDirective s s' ∧ ev = (declaredHandle (span s s')).toList.map .declareTag

/-- Annotated `[207] l-bare-document`. -/
inductive TLBareDocument : TRel where
  | mk (s s' : SurfPos) (ev : List Event) :
      TBlockNode 0 .blockIn s s' ev →
      TLBareDocument s s' ev

/-- The part of `[208] l-explicit-document` after `---`. -/
def TLExplicitBody : TRel :=
  TAlt TLBareDocument (TSeq (Lift SENode) (Lift SSLComments))

/-- Annotated `[208] l-explicit-document`: `---` opens the document. -/
inductive TLExplicitDocument : TRel where
  | withContent (s s₁ s' : SurfPos) (ev : List Event) :
      SCDirectivesEnd s s₁ →
      TLExplicitBody s₁ s' ev →
      TLExplicitDocument s s' (.beginDocument :: ev)

/-- Annotated `[209] l-directive-document`: the directives' declarations are
emitted after the `beginDocument` of the document they belong to. -/
inductive TLDirectiveDocument : TRel where
  | mk (s s₁ s₂ s' : SurfPos) (evDirs ev : List Event) :
      TPlus TLDirective s s₁ evDirs →
      SCDirectivesEnd s₁ s₂ →
      TLExplicitBody s₂ s' ev →
      TLDirectiveDocument s s' (.beginDocument :: evDirs ++ ev)

/-- Annotated `[210] l-any-document`. -/
inductive TLAnyDocument : TRel where
  | directive (s s' : SurfPos) (ev : List Event) : TLDirectiveDocument s s' ev → TLAnyDocument s s' ev
  | explicit (s s' : SurfPos) (ev : List Event) : TLExplicitDocument s s' ev → TLAnyDocument s s' ev
  | bare (s s' : SurfPos) (ev : List Event) : TLBareDocument s s' ev → TLAnyDocument s s' ev

/-- Annotated `[205] l-document-suffix`: `...` ends the document. -/
inductive TLDocumentSuffix : TRel where
  | mk (s s₁ s' : SurfPos) :
      SCDocumentEnd s s₁ → SSLComments s₁ s' →
      TLDocumentSuffix s s' [.endDocument]

/-- Annotated `[211] l-yaml-stream` — the three grammar constructors of
`SLYamlStream`, without `scannerDrop`. -/
inductive TLYamlStream : TRel where
  | single (s s₁ s₂ s' : SurfPos) (e₁ e₂ : List Event) :
      GStar SLDocumentPrefix s s₁ →
      TOpt TLAnyDocument s₁ s₂ e₁ →
      TStar TLDocumentSuffix s₂ s' e₂ →
      TLYamlStream s s' (e₁ ++ e₂)
  | suffixContinue (s s₁ s₂ s₃ s₄ s' : SurfPos) (e₀ e₁ e₂ e₃ : List Event) :
      TLYamlStream s s₁ e₀ →
      TPlus TLDocumentSuffix s₁ s₂ e₁ →
      GStar SLDocumentPrefix s₂ s₃ →
      TOpt TLAnyDocument s₃ s₄ e₂ →
      TStar TLDocumentSuffix s₄ s' e₃ →
      TLYamlStream s s' (e₀ ++ e₁ ++ e₂ ++ e₃)
  | implicitContinue (s s₁ s₂ s₃ s' : SurfPos) (e₀ e₁ e₂ : List Event) :
      TLYamlStream s s₁ e₀ →
      GStar SLDocumentPrefix s₁ s₂ →
      TOpt TLAnyDocument s₂ s₃ e₁ →
      TStar TLDocumentSuffix s₃ s' e₂ →
      TLYamlStream s s' (e₀ ++ e₁ ++ e₂)

/-- The serialization trace of a whole input, by the annotated grammar. -/
def TraceOf (input : String) (ev : List Event) : Prop :=
  ∃ col, TLYamlStream ⟨input.toList, 0⟩ ⟨[], col⟩ ev

/-- The capstone's second conjunct, grammar-side (replaces
`SerializationWellFormedInput` on the proof path; see §10). -/
def TraceWellFormed (input : String) : Prop :=
  ∀ ev, TraceOf input ev → SerializationWellFormed ev

/-- Rule 2, smallest instance: the empty stream has the empty trace. -/
lemma traceOf_empty : TraceOf "" [] :=
  ⟨0, .single _ _ _ _ [] [] (.nil _) (.none _) (.nil _)⟩

end

end L4YAML.Proofs.Serialization.TraceOf
