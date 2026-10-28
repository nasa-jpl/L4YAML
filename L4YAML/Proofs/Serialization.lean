/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Serialization.SerializationWellFormed
public import L4YAML.Proofs.Serialization.SourceEvents
public import L4YAML.Proofs.Serialization.RuntimeScopes
public import L4YAML.Proofs.Serialization.AnchorTiming
public import L4YAML.Proofs.Serialization.CommitTrace
public import L4YAML.Proofs.Serialization.SurfaceEvents
public import L4YAML.Proofs.Serialization.AnchorRuntime
public import L4YAML.Proofs.Serialization.ErrorCensus
public import L4YAML.Proofs.Serialization.Census
public import L4YAML.Proofs.Serialization.ExecutableBoundary
public import L4YAML.Proofs.Serialization.EventsOf
public import L4YAML.Proofs.Serialization.RefLex
import L4YAML.Proofs.Serialization.TokenEvents
import L4YAML.Proofs.Serialization.ParseCheckFrom
import L4YAML.Proofs.Serialization.TraceOf.Document
import L4YAML.Proofs.Serialization.TraceOf.UniqueFlow

@[expose] public section Blanket

/-!
# Stateful serialization semantics

Independent event semantics and proofs relating alias and tag-handle decisions
to the corresponding scanner and parser guards. The package also includes the
exact scanner-plus-token-parser acceptance factorization selected for the load
capstone. The independent whole-input event traversal remains separate from
the surface-language work.
-/

end Blanket
