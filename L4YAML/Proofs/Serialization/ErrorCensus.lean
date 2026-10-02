import L4YAML.Token.Token

/-!
# L4YAML rejection-boundary census

This classifies every current structured ScanError constructor by the layer of
the corrected load contract.

The purpose is adversarial: do not assume anchor/alias ordering and tag-handle
declarations exhaust SerializationWellFormed. Enumerate the executable
rejection vocabulary and force every constructor into an explicit layer.

Only two current constructors are classified as stateful serialization
environment failures: undefinedAlias and undeclaredTagHandle. Resource/API
guards are separated from language rejection rather than smuggled into either
surface syntax or SerializationWellFormed.
-/

namespace L4YAMLSerializationErrorCensus

open L4YAML

inductive RejectionLayer where
  | surface
  | serialization
  | resourceOrAPI
  deriving Repr, DecidableEq

def rejectionLayer : ScanError → RejectionLayer
  | .undefinedAlias .. => .serialization
  | .undeclaredTagHandle .. => .serialization
  | .fuelExhausted .. => .resourceOrAPI
  | .nestingDepthExceeded .. => .resourceOrAPI
  | .multipleDocuments .. => .resourceOrAPI
  | _ => .surface

def isSerializationError (e : ScanError) : Prop :=
  rejectionLayer e = .serialization

theorem serialization_error_iff (e : ScanError) :
    isSerializationError e ↔
      (∃ name line col, e = .undefinedAlias name line col) ∨
      (∃ handle line col, e = .undeclaredTagHandle handle line col) := by
  cases e <;> simp [isSerializationError, rejectionLayer]

theorem undefinedAlias_is_serialization (name : String) (line col : Nat) :
    isSerializationError (.undefinedAlias name line col) := by
  simp [isSerializationError, rejectionLayer]

theorem undeclaredTagHandle_is_serialization (handle : String) (line col : Nat) :
    isSerializationError (.undeclaredTagHandle handle line col) := by
  simp [isSerializationError, rejectionLayer]

theorem resource_guards_not_serialization :
    (∀ line col, ¬ isSerializationError (.fuelExhausted line col)) ∧
    (∀ line, ¬ isSerializationError (.nestingDepthExceeded line)) ∧
    (∀ count, ¬ isSerializationError (.multipleDocuments count)) := by
  simp [isSerializationError, rejectionLayer]

end L4YAMLSerializationErrorCensus

#print axioms L4YAMLSerializationErrorCensus.serialization_error_iff
#print axioms L4YAMLSerializationErrorCensus.resource_guards_not_serialization
