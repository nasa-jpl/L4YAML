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
an anchor property yields a pending anchor name; a containing node may commit
that name only at the node-completion boundary described by CommitTrace.
-/

namespace L4YAMLSerializationSurfaceEvents

open L4YAML
open L4YAML.Surface
open L4YAMLSerializationWellFormed
open L4YAMLSerializationCommitTrace

/-- A surface alias derivation carries a semantic alias-use event. -/
def AliasEventWitness (s s' : SurfPos) (name : String) : Prop :=
  SCNsAliasNode s s' ∧
  ∃ tail : List Char,
    s.chars = '*' :: (name.toList ++ tail) ∧
    s'.chars = tail

/-- A surface anchor property carries a *pending* anchor name.  It is not yet
a defineAnchor event: commitment belongs to the enclosing node completion. -/
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
    (hc : L4YAMLSerializationSourceEvents.isAnchorCharBool c = true)
    (hcs : ∀ d ∈ cs,
      L4YAMLSerializationSourceEvents.isAnchorCharBool d = true) :
    AliasEventWitness
      ⟨'*' :: ((c :: cs) ++ tail), col⟩
      ⟨tail, col + 1 + (c :: cs).length⟩
      (String.ofList (c :: cs)) := by
  constructor
  · exact L4YAMLSerializationSourceEvents.alias_use_surface c cs tail col hc hcs
  · refine ⟨tail, ?_, rfl⟩
    simp

lemma anchor_surface_has_pending
    (c : Char) (cs tail : List Char) (col : Nat)
    (hc : L4YAMLSerializationSourceEvents.isAnchorCharBool c = true)
    (hcs : ∀ d ∈ cs,
      L4YAMLSerializationSourceEvents.isAnchorCharBool d = true) :
    PendingAnchorWitness
      ⟨'&' :: ((c :: cs) ++ tail), col⟩
      ⟨tail, col + 1 + (c :: cs).length⟩
      (String.ofList (c :: cs)) := by
  constructor
  · exact L4YAMLSerializationSourceEvents.anchor_definition_surface c cs tail col hc hcs
  · refine ⟨tail, ?_, rfl⟩
    simp

/-- Committing a pending anchor after a content trace appends the definition,
never prepends it. -/
def commitPendingAnchor (pending : Option String) (contentEvents : List Event) :
    List Event :=
  match pending with
  | none => contentEvents
  | some name => contentEvents ++ [.defineAnchor name]

lemma commit_pending_anchor_some (name : String) (events : List Event) :
    commitPendingAnchor (some name) events =
      events ++ [.defineAnchor name] := rfl

lemma commit_pending_anchor_none (events : List Event) :
    commitPendingAnchor none events = events := rfl

/-- The structured commitment operation reproduces the semantic skeleton's
anchored-node order exactly. -/
lemma commit_pending_matches_commitNode
    (name : String) (content : CommitNode) :
    commitPendingAnchor (some name) (nodeEvents content) =
      nodeEvents (.anchored name content) := by
  rfl

/-- Consequently an alias in the content cannot see the enclosing pending
anchor. -/
lemma pending_anchor_does_not_authorize_inner_alias (name : String) :
    ¬ SerializationWellFormed
      (commitPendingAnchor (some name) [.useAlias name]) := by
  simp [commitPendingAnchor, SerializationWellFormed, WellFormedFrom, AliasAllowed]

end L4YAMLSerializationSurfaceEvents

#print axioms L4YAMLSerializationSurfaceEvents.alias_surface_has_event
#print axioms L4YAMLSerializationSurfaceEvents.anchor_surface_has_pending
#print axioms L4YAMLSerializationSurfaceEvents.commit_pending_matches_commitNode
#print axioms L4YAMLSerializationSurfaceEvents.pending_anchor_does_not_authorize_inner_alias
