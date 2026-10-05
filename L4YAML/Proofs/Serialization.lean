/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Serialization.SerializationWellFormed
import L4YAML.Proofs.Serialization.SourceEvents
import L4YAML.Proofs.Serialization.RuntimeScopes
import L4YAML.Proofs.Serialization.AnchorTiming
import L4YAML.Proofs.Serialization.CommitTrace
import L4YAML.Proofs.Serialization.SurfaceEvents
import L4YAML.Proofs.Serialization.AnchorRuntime
import L4YAML.Proofs.Serialization.ErrorCensus
import L4YAML.Proofs.Serialization.Census
import L4YAML.Proofs.Serialization.ExecutableBoundary

/-!
# Stateful serialization semantics

Independent event semantics and proofs relating alias and tag-handle decisions
to the corresponding scanner and parser guards. The package also includes the
exact scanner-plus-token-parser acceptance factorization selected for the load
capstone. The independent whole-input event traversal remains separate from
the surface-language work.
-/
