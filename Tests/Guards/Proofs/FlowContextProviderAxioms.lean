module

public import L4YAML.Proofs.Output.EmitterScannability

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Seq/map context providers audit alike

`SeqInteriorSeparators.lean` once recorded a seq/map asymmetry at the axiom layer: the map context
pair `mapWholeStreamWellTyped`/`mapFoldTotal_of_context` inherited `sorryAx` through
`scanFiltered_emitMap_nonempty_structure`, whose `ParseEntryFlowMapOk` conjunct discharged the
`FlowSubrangesOk` residual with an inline `sorry`, while the seq pair had shed its twin by
relocating it to `parseStream_emitSequence`.  The map residual has since moved out the same way,
to `parseStream_emitMapping`, so both pairs — and both structure lemmas — audit
`[propext, Classical.choice, Quot.sound]`.  These pins keep that module's status note honest: a
delegated proof can be sorry-free and still ride `sorryAx` through a dependency, so the profile is
checked by `#print axioms`, not by a grep. -/

namespace Tests.Guards.FlowContextProviderAxioms

open L4YAML.Proofs.EmitterScannability

/-- info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_emitSeq_nonempty_structure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_emitSeq_nonempty_structure

/-- info: 'L4YAML.Proofs.EmitterScannability.scanFiltered_emitMap_nonempty_structure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_emitMap_nonempty_structure

/-- info: 'L4YAML.Proofs.EmitterScannability.seqWholeStreamWellTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seqWholeStreamWellTyped

/-- info: 'L4YAML.Proofs.EmitterScannability.seqFoldTotal_of_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seqFoldTotal_of_context

/-- info: 'L4YAML.Proofs.EmitterScannability.mapWholeStreamWellTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mapWholeStreamWellTyped

/-- info: 'L4YAML.Proofs.EmitterScannability.mapFoldTotal_of_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mapFoldTotal_of_context

end Tests.Guards.FlowContextProviderAxioms

end Blanket
