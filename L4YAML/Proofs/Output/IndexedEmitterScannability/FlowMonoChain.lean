/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Basic
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Preserve.Step
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Preserve.DpInv
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Preserve.Helpers
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Maintenance.FlowDispatch
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Maintenance.Pipeline
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.FlowStackChainIx
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Invariant
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Detail
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.Preflow
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.FlowClose
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.Endpoint
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.FlowSeqOpen
public import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.FlowScalar

@[expose] public section Blanket

/-! # `IndexedEmitterScannability.FlowMonoChain` — re-export shim

The `FlowMonoChain` machinery is split across `FlowMonoChain/Basic.lean`
(§1 `FlowMonoChainIx` inductive + §2 `SimpleKeyAboveFloorIx` predicate
and its maintenance through `scanNextTokenIx`) and one file per
sub-session of `.flowmono.preserve` under `FlowMonoChain/Preserve/`.
Importing this module pulls in everything; importing the sub-files
directly is also fine. The original namespace
`L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain` is preserved.

The `Sync/Scenarios/` subtree holds the per-character `scanNextTokenIx`
scenario chains (`.flowmono.sync.scenarios`: `Preflow`, `FlowClose`,
`Endpoint`), extended by the `.emitscans.flowpair` SS2 prerequisites
`FlowSeqOpen` (`[` opener) and `FlowScalar` (double-quoted scalar).

See `FlowMonoChain/Basic.lean` for the section-by-section map.
-/

end Blanket
