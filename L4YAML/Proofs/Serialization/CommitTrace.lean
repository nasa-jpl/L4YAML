/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Commitment-ordered serialization traces

The event-state checker is shared by two explicitly named trace policies:
`yamlNodeEvents` commits an anchor before its content (YAML 1.2.2), while
`l4yamlNodeEvents` commits it after content (current L4YAML runtime).

`CommitNode` is deliberately only the smallest witness language needed to
separate those two anchor-order policies. It is not a complete YAML syntax or
event model: mappings, tags, directives, and document scope are represented in
the adjacent source, surface, and runtime-scope modules.

Only the latter describes current parser finalization. A future runtime repair
must update the runtime bridges and guards, not silently relabel that trace.
Open repair: https://github.com/nasa-jpl/L4YAML/pull/1#issuecomment-5984913868

-/
namespace L4YAML.Proofs.Serialization.CommitTrace

open L4YAML.Proofs.Serialization.SerializationWellFormed

inductive CommitNode where
  | atom
  | alias (name : String)
  | seq (children : List CommitNode)
  | anchored (name : String) (content : CommitNode)
  deriving Repr

mutual
  def l4yamlNodeEvents : CommitNode → List Event
    | .atom => []
    | .alias name => [.useAlias name]
    | .seq children => l4yamlNodesEvents children
    | .anchored name content => l4yamlNodeEvents content ++ [.defineAnchor name]

  def l4yamlNodesEvents : List CommitNode → List Event
    | [] => []
    | node :: rest => l4yamlNodeEvents node ++ l4yamlNodesEvents rest
end

/-! YAML 1.2.2: the anchor-bearing node-start event precedes descendants. -/
mutual
  def yamlNodeEvents : CommitNode → List Event
    | .atom => []
    | .alias name => [.useAlias name]
    | .seq children => yamlNodesEvents children
    | .anchored name content => .defineAnchor name :: yamlNodeEvents content

  def yamlNodesEvents : List CommitNode → List Event
    | [] => []
    | node :: rest => yamlNodeEvents node ++ yamlNodesEvents rest
end

lemma yaml_anchor_commit_first (name : String) (content : CommitNode) :
    yamlNodeEvents (.anchored name content) =
      .defineAnchor name :: yamlNodeEvents content := rfl

lemma yaml_enclosing_anchor_self_reference_allowed (name : String) :
    SerializationWellFormed (yamlNodeEvents (.anchored name (.alias name))) := by
  simp [yamlNodeEvents, SerializationWellFormed, WellFormedFrom, AliasAllowed]

lemma yaml_current_l4yaml_anchor_separator (name : String) :
    checkFrom {} (yamlNodeEvents (.anchored name (.alias name))) ≠
      checkFrom {} (l4yamlNodeEvents (.anchored name (.alias name))) := by
  simp [yamlNodeEvents, l4yamlNodeEvents, checkFrom, AliasAllowed]

lemma l4yamlNodeEvents_anchor_commit_last (name : String) (content : CommitNode) :
    l4yamlNodeEvents (.anchored name content) =
      l4yamlNodeEvents content ++ [.defineAnchor name] := rfl

lemma l4yamlNodesEvents_cons (node : CommitNode) (rest : List CommitNode) :
    l4yamlNodesEvents (node :: rest) = l4yamlNodeEvents node ++ l4yamlNodesEvents rest := rfl

lemma current_l4yaml_enclosing_anchor_self_reference_rejected (name : String) :
    ¬ SerializationWellFormed (l4yamlNodeEvents (.anchored name (.alias name))) := by
  simp [l4yamlNodeEvents, SerializationWellFormed, WellFormedFrom, AliasAllowed]

lemma later_sibling_alias_allowed (name : String) :
    SerializationWellFormed
      (l4yamlNodesEvents [.anchored name .atom, .alias name]) := by
  simp [l4yamlNodesEvents, l4yamlNodeEvents, SerializationWellFormed, WellFormedFrom, AliasAllowed]

lemma current_l4yaml_node_boundary_separator (name : String) :
    checkFrom {} (l4yamlNodeEvents (.anchored name (.alias name))) ≠
      checkFrom {} (l4yamlNodesEvents [.anchored name .atom, .alias name]) := by
  simp [l4yamlNodesEvents, l4yamlNodeEvents, checkFrom, AliasAllowed]

lemma anchored_then_rest_events
    (name : String) (content : CommitNode) (rest : List CommitNode) :
    l4yamlNodesEvents (.anchored name content :: rest) =
      l4yamlNodeEvents content ++ [.defineAnchor name] ++ l4yamlNodesEvents rest := by
  simp [l4yamlNodesEvents, l4yamlNodeEvents, List.append_assoc]

lemma empty_anchor_then_alias (name : String) :
    l4yamlNodesEvents [.anchored name .atom, .alias name] =
      [.defineAnchor name, .useAlias name] := by
  rfl

end L4YAML.Proofs.Serialization.CommitTrace

#print axioms L4YAML.Proofs.Serialization.CommitTrace.current_l4yaml_enclosing_anchor_self_reference_rejected
#print axioms L4YAML.Proofs.Serialization.CommitTrace.later_sibling_alias_allowed
#print axioms L4YAML.Proofs.Serialization.CommitTrace.current_l4yaml_node_boundary_separator
#print axioms L4YAML.Proofs.Serialization.CommitTrace.anchored_then_rest_events

#print axioms L4YAML.Proofs.Serialization.CommitTrace.yaml_enclosing_anchor_self_reference_allowed
#print axioms L4YAML.Proofs.Serialization.CommitTrace.yaml_current_l4yaml_anchor_separator
