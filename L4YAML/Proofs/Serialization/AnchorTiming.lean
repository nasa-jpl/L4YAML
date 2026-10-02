import L4YAML.Proofs.Serialization.SerializationWellFormed

/-!
# Anchor commitment timing

The runtime census exposed a distinction that a raw source-order event stream
would miss:

  &x [*x]

The scanner accepts it because `definedAnchors` is extended as soon as the
`&x` property is scanned.  The load pipeline rejects it because the token
parser does not add `x` to its anchor environment until the anchored node has
finished parsing.

Therefore the independent serialization semantics must interpret
`Event.defineAnchor` as **anchor commitment at node completion**, not as the
lexical appearance of `&name`.

This file pins that distinction algebraically, without executing L4YAML.
-/

namespace L4YAMLSerializationAnchorTiming

open L4YAMLSerializationWellFormed

/-- A self-reference encountered before its enclosing anchor is committed is
not serialization-well-formed. -/
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

/-- The two orderings are observably different.  Hence source position of the
`&name` marker is insufficient state for the load-level contract; node
completion is a necessary distinction. -/
lemma anchor_commit_order_separator
    (name : String) :
    checkFrom {} [.defineAnchor name, .useAlias name] ≠
      checkFrom {} [.useAlias name, .defineAnchor name] := by
  simp [checkFrom, AliasAllowed]

end L4YAMLSerializationAnchorTiming

#print axioms L4YAMLSerializationAnchorTiming.self_reference_before_commit_rejected
#print axioms L4YAMLSerializationAnchorTiming.anchor_commit_order_separator
