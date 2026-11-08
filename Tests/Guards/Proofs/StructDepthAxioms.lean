module

public import L4YAML.Proofs.Scanner.StructDepth

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Axiom census: (γ1), the structural-depth carrier over `scanLoop`

Capstone 7.7 `parse_iff_grammar`, composition residue (γ).  `StructDepth` carries `DInv` (depth
bound, `Bal`, simple-key slot/stack clauses, placeholder slots, slot ordering) over every
`scanNextToken` arm and `scanLoop`, from the initial state (with or without a BOM), and lands
`Bal` on raw `scan` output and on `scanFiltered` output.  Standard axioms only, no
`native_decide`. -/

namespace Tests.Guards.StructDepthAxioms

open L4YAML.Proofs.StructDepth in
/-- info: 'L4YAML.Proofs.StructDepth.DInv_scanNextToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DInv_scanNextToken

open L4YAML.Proofs.StructDepth in
/-- info: 'L4YAML.Proofs.StructDepth.DInv_scanLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DInv_scanLoop

open L4YAML.Proofs.StructDepth in
/-- info: 'L4YAML.Proofs.StructDepth.DInv_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DInv_init

open L4YAML.Proofs.StructDepth in
/-- info: 'L4YAML.Proofs.StructDepth.scan_bal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_bal

open L4YAML.Proofs.StructDepth in
/-- info: 'L4YAML.Proofs.StructDepth.scanFiltered_bal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scanFiltered_bal

end Tests.Guards.StructDepthAxioms

end Blanket
