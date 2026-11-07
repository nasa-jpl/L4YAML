module

public import L4YAML.Proofs.Scanner.FlowSync

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Axiom census: S3 obligation (β2a), flow-stack synchrony over the scanner loop

Capstone 7.7 `parse_iff_grammar`, stream S3.  `FlowSync` over `scanNextToken` /
`scanLoopFull`, indents frozen in flow, `skipToContent` keeps `simpleKeyAllowed`.
Standard axioms only, no `native_decide`, on every declaration. -/

namespace Tests.Guards.FlowSyncAxioms

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_mk'' does not depend on any axioms -/
#guard_msgs in
#print axioms FlowSync_mk'

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync.emit' does not depend on any axioms -/
#guard_msgs in
#print axioms FlowSync.emit

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync.consumeBOM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync.consumeBOM

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync.unwindIndents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync.unwindIndents

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.preprocess_preserves_flowLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preprocess_preserves_flowLevel

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_preprocess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_preprocess

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_dispatchStructural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_dispatchStructural

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_dispatchBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_dispatchBlock

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_dispatchContent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_dispatchContent

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_flowSequenceStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_flowSequenceStart

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_flowMappingStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_flowMappingStart

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_flowSequenceEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_flowSequenceEnd

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_flowMappingEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_flowMappingEnd

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_dispatchFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_dispatchFlow

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_scanNextToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_scanNextToken

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.FlowSync_scanLoopFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlowSync_scanLoopFull

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.dispatchStructural_indents_of_inFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dispatchStructural_indents_of_inFlow

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.scanNextToken_indents_of_inFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scanNextToken_indents_of_inFlow

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.skipToContentLoop_simpleKeyAllowed_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms skipToContentLoop_simpleKeyAllowed_mono

open L4YAML.Proofs.FlowSync in
/-- info: 'L4YAML.Proofs.FlowSync.skipToContent_simpleKeyAllowed_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms skipToContent_simpleKeyAllowed_mono

end Tests.Guards.FlowSyncAxioms
