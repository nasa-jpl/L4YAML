/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Surface.Document
public import L4YAML.Proofs.Serialization.EventsOf

public meta import L4YAML.Proofs.Serialization.EventsOf
public meta import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Event-annotated grammar — combinators and leaves (EVENTSOF-CONCEPT §10)

`TraceOf/Node.lean` (generated) is the copy of `Surface/Node.lean`'s mutual
block with one more index, the trace.  This file supplies what the copy refers
to: the annotated combinators (`TSeq`, `TOpt`, …, mirroring `GSeq`, `GOpt`, …),
`Lift` for the productions that carry no event, and the leaves where events
arise — tag and anchor properties, and aliases.  A leaf's events are a
*function of the span of that one lexeme* (`tagEvents`, `anchorEvents`,
`aliasEvents`), never of a wider text: the `s-separate` between two properties
may hold a comment, and a verbatim URI may hold anything, so the whole
`c-ns-properties` span is not scanned (review of the first cut).  Leaf traces
are unique by construction; uniqueness of the whole is the grammar's business.
-/

namespace L4YAML.Proofs.Serialization.TraceOf

@[expose] public section

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.EventsOf (handleOf isTagCharBool)
open L4YAML.Proofs.Serialization.SourceEvents (isAnchorCharBool)

abbrev TRel := SurfPos → SurfPos → List Event → Prop

/-- A production without events, as an annotated relation. -/
def Lift (P : SurfPos → SurfPos → Prop) : TRel := fun s s' ev => P s s' ∧ ev = []

inductive TSeq (P Q : TRel) : TRel where
  | mk (s₁ s₂ s₃ : SurfPos) (e₁ e₂ : List Event) :
      P s₁ s₂ e₁ → Q s₂ s₃ e₂ → TSeq P Q s₁ s₃ (e₁ ++ e₂)

inductive TSeq3 (P Q R : TRel) : TRel where
  | mk (s₁ s₂ s₃ s₄ : SurfPos) (e₁ e₂ e₃ : List Event) :
      P s₁ s₂ e₁ → Q s₂ s₃ e₂ → R s₃ s₄ e₃ → TSeq3 P Q R s₁ s₄ (e₁ ++ e₂ ++ e₃)

inductive TAlt (P Q : TRel) : TRel where
  | left (s s' : SurfPos) (e : List Event) : P s s' e → TAlt P Q s s' e
  | right (s s' : SurfPos) (e : List Event) : Q s s' e → TAlt P Q s s' e

inductive TStar (P : TRel) : TRel where
  | nil (s : SurfPos) : TStar P s s []
  | cons (s₁ s₂ s₃ : SurfPos) (e₁ e₂ : List Event) :
      P s₁ s₂ e₁ → TStar P s₂ s₃ e₂ → TStar P s₁ s₃ (e₁ ++ e₂)

inductive TPlus (P : TRel) : TRel where
  | mk (s₁ s₂ s₃ : SurfPos) (e₁ e₂ : List Event) :
      P s₁ s₂ e₁ → TStar P s₂ s₃ e₂ → TPlus P s₁ s₃ (e₁ ++ e₂)

inductive TOpt (P : TRel) : TRel where
  | none (s : SurfPos) : TOpt P s s []
  | some (s s' : SurfPos) (e : List Event) : P s s' e → TOpt P s s' e

/-- The characters a derivation from `s` to `s'` consumed. -/
def span (s s' : SurfPos) : List Char := s.chars.take (s.chars.length - s'.chars.length)

/-- Events of a tag lexeme: a verbatim `!<…>` names no handle (§6 Q4); a
shorthand or non-specific tag uses its handle. Applied to the exact span of one
`SCNsTagProperty`, never to a wider text. -/
def tagEvents (chars : List Char) : List Event :=
  if chars.take 2 = ['!', '<'] then [] else [.useTag (handleOf chars)]

/-- Events of an anchor lexeme `&name`. -/
def anchorEvents : List Char → List Event
  | '&' :: cs => [.defineAnchor (String.ofList (cs.takeWhile isAnchorCharBool))]
  | _ => []

/-- Events of a `c-ns-alias-node` span. -/
def aliasEvents : List Char → List Event
  | '*' :: cs => [.useAlias (String.ofList (cs.takeWhile isAnchorCharBool))]
  | _ => []

#guard tagEvents "!t".toList = [.useTag "!"]
#guard tagEvents "!!str".toList = [.useTag "!!"]
#guard tagEvents "!e!x".toList = [.useTag "!e!"]
#guard tagEvents "!<tag:a,b!h!>".toList = []
#guard anchorEvents "&a".toList = [.defineAnchor "a"]
#guard aliasEvents "*a".toList = [.useAlias "a"]

/-- Annotated `[97] c-ns-tag-property`: the surface relation, trace read off
its own span. -/
def TCNsTagProperty : TRel :=
  fun s s' ev => SCNsTagProperty s s' ∧ ev = tagEvents (span s s')

/-- Annotated `[101] c-ns-anchor-property`. -/
def TCNsAnchorProperty : TRel :=
  fun s s' ev => SCNsAnchorProperty s s' ∧ ev = anchorEvents (span s s')

/-- Annotated `[96] c-ns-properties`, constructor for constructor: each event
comes from the span of its own property premise, so the `s-separate` between
them (which may hold a comment) contributes nothing. -/
inductive TCNsProperties (n : Nat) (c : YamlContext) : TRel where
  | tagFirst (s s₁ s' : SurfPos) (e₁ e₂ : List Event) :
      TCNsTagProperty s s₁ e₁ →
      TOpt (TSeq (Lift (SSeparate n c)) TCNsAnchorProperty) s₁ s' e₂ →
      TCNsProperties n c s s' (e₁ ++ e₂)
  | anchorFirst (s s₁ s' : SurfPos) (e₁ e₂ : List Event) :
      TCNsAnchorProperty s s₁ e₁ →
      TOpt (TSeq (Lift (SSeparate n c)) TCNsTagProperty) s₁ s' e₂ →
      TCNsProperties n c s s' (e₁ ++ e₂)

/-- Annotated `[104] c-ns-alias-node`. -/
def TCNsAliasNode : TRel :=
  fun s s' ev => SCNsAliasNode s s' ∧ ev = aliasEvents (span s s')

end

end L4YAML.Proofs.Serialization.TraceOf
