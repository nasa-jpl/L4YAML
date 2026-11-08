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

/-! Scanner-shape facts on the parser's view (β2b, (γ1)); their consumer, the discharge of the loop's
    no-progress exit (`LoopDead_scanFiltered`, `DeadResidue`), is retired since (γ2α) made that exit an
    error. -/

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.liveF_dead_contra' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms liveF_dead_contra

open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_bal_tok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_bal_tok

/-! S5(→): the stream loop stops at `.streamEnd` or the end of the array; the no-progress exit is an
    error ((γ2α)), so `parseStreamLoop_cf` / `parseStream_ok_checkFrom` carry no third stop shape. -/

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


open L4YAML.Proofs.Serialization.ScannerShape in
/-- info: 'L4YAML.Proofs.Serialization.ScannerShape.scanFiltered_noComment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms scanFiltered_noComment

end Tests.Guards.ScannerShapeAxioms

end Blanket
