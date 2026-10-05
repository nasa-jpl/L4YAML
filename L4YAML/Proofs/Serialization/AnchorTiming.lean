/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Anchor commitment timing

YAML 1.2.2 §§3.2.1.3, 3.2.2.2, and 7.1 admit self-descendant nodes:
`&x [*x]` has an anchor-bearing sequence-start event before its alias.
YAML anchor commitment therefore precedes the node's content.

Current L4YAML differs: its scanner registers `&x` immediately, but its token
parser registers a collection anchor only after the content has completed.
The current load pipeline consequently rejects the self-reference.

Both event orderings below are independent algebraic traces. The separator
names the observable mismatch that the open runtime repair must remove; it
is not a claim that YAML requires rejection. See the maintainer's repair note:
https://github.com/nasa-jpl/L4YAML/pull/1#issuecomment-5984913868

-/
namespace L4YAML.Proofs.Serialization.AnchorTiming

open L4YAML.Proofs.Serialization.SerializationWellFormed

/-- A self-reference encountered before its enclosing anchor is committed is
not well formed under the current L4YAML completion-order trace. -/
lemma self_reference_before_commit_rejected
    (name : String) :
    ¬ SerializationWellFormed [.useAlias name, .defineAnchor name] := by
  simp [SerializationWellFormed, WellFormedFrom, AliasAllowed]

/-- Once an anchored node has completed and its anchor is committed, a later
alias use is well-formed. -/
lemma later_alias_after_commit_allowed
    (name : String) :
    SerializationWellFormed [.defineAnchor name, .useAlias name] := by
  simp [SerializationWellFormed, WellFormedFrom, AliasAllowed]

/-- The two orderings are observably different.  This is the current runtime/spec mismatch, not a normative YAML restriction. -/
lemma anchor_commit_order_separator
    (name : String) :
    checkFrom {} [.defineAnchor name, .useAlias name] ≠
      checkFrom {} [.useAlias name, .defineAnchor name] := by
  simp [checkFrom, AliasAllowed]

end L4YAML.Proofs.Serialization.AnchorTiming

#print axioms L4YAML.Proofs.Serialization.AnchorTiming.self_reference_before_commit_rejected
#print axioms L4YAML.Proofs.Serialization.AnchorTiming.anchor_commit_order_separator
