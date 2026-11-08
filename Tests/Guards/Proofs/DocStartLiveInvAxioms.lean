module

public import L4YAML.Proofs.Scanner.DocStartLiveInv

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Axiom census: S3 obligation (β2b), the document-start liveness carrier over `scanLoop`

Capstone 7.7 `parse_iff_grammar`, stream S3.  `DocStartLiveInv` carries `LiveInv` (head, `Shape`,
depth/boundary coupling, simple-key slot and stack clauses) over every `scanNextToken` arm and
`scanLoop`, from the initial state (with or without a BOM), and lands `Shape` on raw `scan`
output and `LiveF` on `scanFiltered` output.  Standard axioms only, no `native_decide`. -/

namespace Tests.Guards.DocStartLiveInvAxioms

open L4YAML.Proofs.DocStartLiveInv in
/-- info: 'L4YAML.Proofs.DocStartLiveInv.LiveInv_scanNextToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LiveInv_scanNextToken

open L4YAML.Proofs.DocStartLiveInv in
/-- info: 'L4YAML.Proofs.DocStartLiveInv.LiveInv_scanLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LiveInv_scanLoop

open L4YAML.Proofs.DocStartLiveInv in
/-- info: 'L4YAML.Proofs.DocStartLiveInv.LiveInv_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LiveInv_init

open L4YAML.Proofs.DocStartLiveInv in
/-- info: 'L4YAML.Proofs.DocStartLiveInv.scan_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_shape

open L4YAML.Proofs.DocStartLiveInv in
/-- info: 'L4YAML.Proofs.DocStartLiveInv.scanFiltered_liveF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scanFiltered_liveF

end Tests.Guards.DocStartLiveInvAxioms

end Blanket
