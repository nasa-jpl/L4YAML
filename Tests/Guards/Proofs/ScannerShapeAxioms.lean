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

end Tests.Guards.ScannerShapeAxioms

end Blanket
