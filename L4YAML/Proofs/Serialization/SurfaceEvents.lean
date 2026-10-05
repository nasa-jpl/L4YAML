/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Surface.Node
import L4YAML.Proofs.Serialization.SerializationWellFormed
import L4YAML.Proofs.Serialization.CommitTrace
import L4YAML.Proofs.Serialization.SourceEvents

/-!
# Surface-derivation semantic event witnesses

This module attaches serialization events to actual L4YAML surface
derivations, rather than scanning indicator-looking characters globally.

The key design point is structural: aliases and properties are witnessed only
where the grammar says they are nodes/properties. Quoted scalar text, comments,
and block scalar contents therefore cannot become semantic events merely by
containing '*', '&', or '!'.

Anchor commitment is represented separately from lexical property discovery:
an anchor property yields a pending anchor name; current L4YAML commits it at node completion, while YAML 1.2.2
commits it before content. Both policies are explicit in CommitTrace.
-/

namespace L4YAML.Proofs.Serialization.SurfaceEvents

open L4YAML
open L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.CommitTrace

/-- A surface alias derivation carries a semantic alias-use event. -/
def AliasEventWitness (s s' : SurfPos) (name : String) : Prop :=
  SCNsAliasNode s s' ∧
  ∃ tail : List Char,
    s.chars = '*' :: (name.toList ++ tail) ∧
    s'.chars = tail

/-- A surface anchor property carries a *pending* anchor name.  Its conversion to a defineAnchor event depends on the selected trace policy. -/
def PendingAnchorWitness (s s' : SurfPos) (name : String) : Prop :=
  SCNsAnchorProperty s s' ∧
  ∃ tail : List Char,
    s.chars = '&' :: (name.toList ++ tail) ∧
    s'.chars = tail

/-- A named surface tag property carries a custom handle use. -/
def NamedTagEventWitness (s s' : SurfPos) (handle : String) : Prop :=
  SCNsTagProperty s s' ∧
  ∃ body suffix tail : List Char,
    body ≠ [] ∧
    handle = "!" ++ String.ofList body ++ "!" ∧
    s.chars = '!' :: (body ++ '!' :: (suffix ++ tail)) ∧
    s'.chars = tail

lemma alias_surface_has_event
    (c : Char) (cs tail : List Char) (col : Nat)
    (hc : L4YAML.Proofs.Serialization.SourceEvents.isAnchorCharBool c = true)
    (hcs : ∀ d ∈ cs,
      L4YAML.Proofs.Serialization.SourceEvents.isAnchorCharBool d = true) :
    AliasEventWitness
      ⟨'*' :: ((c :: cs) ++ tail), col⟩
      ⟨tail, col + 1 + (c :: cs).length⟩
      (String.ofList (c :: cs)) := by
  constructor
  · exact L4YAML.Proofs.Serialization.SourceEvents.alias_use_surface c cs tail col hc hcs
  · refine ⟨tail, ?_, rfl⟩
    simp

lemma anchor_surface_has_pending
    (c : Char) (cs tail : List Char) (col : Nat)
    (hc : L4YAML.Proofs.Serialization.SourceEvents.isAnchorCharBool c = true)
    (hcs : ∀ d ∈ cs,
      L4YAML.Proofs.Serialization.SourceEvents.isAnchorCharBool d = true) :
    PendingAnchorWitness
      ⟨'&' :: ((c :: cs) ++ tail), col⟩
      ⟨tail, col + 1 + (c :: cs).length⟩
      (String.ofList (c :: cs)) := by
  constructor
  · exact L4YAML.Proofs.Serialization.SourceEvents.anchor_definition_surface c cs tail col hc hcs
  · refine ⟨tail, ?_, rfl⟩
    simp

/-- Current L4YAML policy, awaiting the open recursive-alias repair. -/
def l4yamlCommitPendingAnchor (pending : Option String) (contentEvents : List Event) :
    List Event :=
  match pending with
  | none => contentEvents
  | some name => contentEvents ++ [.defineAnchor name]

/-- YAML 1.2.2 policy: commit the anchor before node content. -/
def yamlCommitAnchor (anchor : Option String) (contentEvents : List Event) : List Event :=
  match anchor with
  | none => contentEvents
  | some name => .defineAnchor name :: contentEvents

lemma yaml_anchor_authorizes_inner_alias (name : String) :
    SerializationWellFormed (yamlCommitAnchor (some name) [.useAlias name]) := by
  simp [yamlCommitAnchor, SerializationWellFormed, WellFormedFrom, AliasAllowed]

lemma commit_pending_anchor_some (name : String) (events : List Event) :
    l4yamlCommitPendingAnchor (some name) events =
      events ++ [.defineAnchor name] := rfl

lemma commit_pending_anchor_none (events : List Event) :
    l4yamlCommitPendingAnchor none events = events := rfl

/-- The structured commitment operation reproduces the semantic skeleton's
anchored-node order exactly. -/
lemma commit_pending_matches_commitNode
    (name : String) (content : CommitNode) :
    l4yamlCommitPendingAnchor (some name) (l4yamlNodeEvents content) =
      l4yamlNodeEvents (.anchored name content) := by
  rfl

/-- Consequently an alias in the content cannot see the enclosing pending
anchor. -/
lemma current_l4yaml_pending_anchor_does_not_authorize_inner_alias (name : String) :
    ¬ SerializationWellFormed
      (l4yamlCommitPendingAnchor (some name) [.useAlias name]) := by
  simp [l4yamlCommitPendingAnchor, SerializationWellFormed, WellFormedFrom, AliasAllowed]

end L4YAML.Proofs.Serialization.SurfaceEvents

#print axioms L4YAML.Proofs.Serialization.SurfaceEvents.alias_surface_has_event
#print axioms L4YAML.Proofs.Serialization.SurfaceEvents.anchor_surface_has_pending
#print axioms L4YAML.Proofs.Serialization.SurfaceEvents.commit_pending_matches_commitNode
#print axioms L4YAML.Proofs.Serialization.SurfaceEvents.current_l4yaml_pending_anchor_does_not_authorize_inner_alias

#print axioms L4YAML.Proofs.Serialization.SurfaceEvents.yaml_anchor_authorizes_inner_alias
