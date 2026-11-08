module

public import L4YAML.Proofs.Serialization.ScannerShape

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Axiom census: S3 obligation (b) `DirectivesClosed` on scanner output

Capstone 7.7 `parse_iff_grammar`, stream S3.  `scanFiltered_DirectivesClosed`
discharges the `DirectivesClosed ts` premise of `parseStream_ok_checkFrom` for
real scanner output.  Standard axioms only, no `native_decide`, on every
declaration of the chain. -/

namespace Tests.Guards.ScannerShapeAxioms

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_DirectivesClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_DirectivesClosed

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_parseStream_ok_checkFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_parseStream_ok_checkFrom

open L4YAML.Proofs.DirectiveRuns in
/-- info: 'L4YAML.Proofs.DirectiveRuns.scanFiltered_closedList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_closedList

open L4YAML.Proofs.DirectiveRuns in
/-- info: 'L4YAML.Proofs.DirectiveRuns.scan_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms scan_closed

open L4YAML.Proofs.DirectiveRuns in
/-- info: 'L4YAML.Proofs.DirectiveRuns.DirInv_scanLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms DirInv_scanLoop

open L4YAML.Proofs.DirectiveRuns in
/-- info: 'L4YAML.Proofs.DirectiveRuns.DirInv_scanNextToken' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms DirInv_scanNextToken

open L4YAML.Proofs.DirectiveRuns in
/-- info: 'L4YAML.Proofs.DirectiveRuns.dirRun_false_closed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms dirRun_false_closed

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scan_toks_streamEnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scan_toks_streamEnd

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_toks_streamEnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_toks_streamEnd

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_streamEnd_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_streamEnd_last

open L4YAML.Proofs.DirectiveRuns in
/-- info: 'L4YAML.Proofs.DirectiveRuns.scan_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms scan_inv

open L4YAML.Proofs.DirectiveRuns in
/-- info: 'L4YAML.Proofs.DirectiveRuns.DirInv_scanLoop_streamEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms DirInv_scanLoop_streamEnd

open L4YAML.Proofs.DirectiveRuns in
/-- info: 'L4YAML.Proofs.DirectiveRuns.scan_streamEnd_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms scan_streamEnd_unique

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_toks_streamEnd_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_toks_streamEnd_unique

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_streamEnd_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_streamEnd_index

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.go_append_streamEnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms go_append_streamEnd

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.tokenEvents_dropLast_streamEnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms tokenEvents_dropLast_streamEnd

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_parseStream_ok_checkFrom_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_parseStream_ok_checkFrom_full

/-! S3 (β2b): the scanner excludes `LoopDead`'s index-1 and after-`...` shapes; `DeadResidue` is what
    remains (the `.afterDocument` shape (γ), or a `.comment` token). -/

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.liveF_dead_contra' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms liveF_dead_contra

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.LoopDead_scanFiltered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LoopDead_scanFiltered

/-! S3 (d): the loop's no-progress exit tied to where it can sit (`StopShape`, `LoopStuck`); the refined
    `parseStreamLoop_cf` / `parseStream_ok_checkFrom` and the wrappers above carry it. -/

open L4YAML.Proofs.Serialization.ParseCheckFrom in
/-- info: 'L4YAML.Proofs.Serialization.ParseCheckFrom.LoopDead_of_initial' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LoopDead_of_initial

open L4YAML.Proofs.Serialization.ParseCheckFrom in
/-- info: 'L4YAML.Proofs.Serialization.ParseCheckFrom.StopShape_after_documentEnd' does not depend on any axioms
-/
#guard_msgs in
#print axioms StopShape_after_documentEnd

open L4YAML.Proofs.Serialization.ParseCheckFrom in
/-- info: 'L4YAML.Proofs.Serialization.ParseCheckFrom.StopShape_afterDocument' does not depend on any axioms
-/
#guard_msgs in
#print axioms StopShape_afterDocument

open L4YAML.Proofs.Serialization.ParseCheckFrom in
/-- info: 'L4YAML.Proofs.Serialization.ParseCheckFrom.stop_mono' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms stop_mono

open L4YAML.Proofs.Serialization.ParseCheckFrom in
/-- info: 'L4YAML.Proofs.Serialization.ParseCheckFrom.stop_mono'' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms stop_mono'

open L4YAML.Proofs.Serialization.ParseCheckFrom in
/-- info: 'L4YAML.Proofs.Serialization.ParseCheckFrom.parseStreamLoop_cf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms parseStreamLoop_cf

open L4YAML.Proofs.Serialization.ParseCheckFrom in
/-- info: 'L4YAML.Proofs.Serialization.ParseCheckFrom.parseStream_ok_checkFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms parseStream_ok_checkFrom


open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.tagOk_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tagOk_shaped

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_TagUsesShaped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_TagUsesShaped

end Tests.Guards.ScannerShapeAxioms

end Blanket
