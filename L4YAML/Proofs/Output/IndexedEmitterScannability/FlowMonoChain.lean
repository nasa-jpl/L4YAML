/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Basic
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Preserve.Step
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Preserve.DpInv
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Preserve.Helpers
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Maintenance.FlowDispatch
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Maintenance.Pipeline
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Invariant
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Detail
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.Preflow
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.FlowClose
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.Endpoint

/-! # `IndexedEmitterScannability.FlowMonoChain` — re-export shim

The `FlowMonoChain` machinery is split across `FlowMonoChain/Basic.lean`
(§1 `FlowMonoChainIx` inductive + §2 `SimpleKeyAboveFloorIx` predicate
and its maintenance through `scanNextTokenIx`) and one file per
sub-session of `.flowmono.preserve` under `FlowMonoChain/Preserve/`.
Importing this module pulls in everything; importing the sub-files
directly is also fine. The original namespace
`L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain` is preserved.

See `FlowMonoChain/Basic.lean` for the section-by-section map.
-/
