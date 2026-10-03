import L4YAML.Proofs.Serialization.SerializationWellFormed
import L4YAML.Proofs.Serialization.SourceEvents
import L4YAML.Proofs.Serialization.RuntimeScopes
import L4YAML.Proofs.Serialization.AnchorTiming
import L4YAML.Proofs.Serialization.CommitTrace
import L4YAML.Proofs.Serialization.SurfaceEvents
import L4YAML.Proofs.Serialization.AnchorRuntime
import L4YAML.Proofs.Serialization.ErrorCensus
import L4YAML.Proofs.Serialization.Census

/-!
# Stateful serialization semantics

Independent event semantics and proofs relating alias and tag-handle decisions
to the corresponding scanner and parser guards. This module is separate from
the proposed full surface/load completeness capstone.
-/
