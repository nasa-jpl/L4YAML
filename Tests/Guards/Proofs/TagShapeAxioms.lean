module

public import L4YAML.Proofs.Scanner.TagShape

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Axiom census: S3 obligation (a), every scanner-emitted `.tag` has a shaped handle

Capstone 7.7 `parse_iff_grammar`, stream S3.  `TagShape` carries `TagInv` (every token of `vals s`
is `tagOk`) over every `scanNextToken` arm through `TagExt` and over `scanLoop`, from the initial
state, and lands `tagOk` on every token of raw `scan` and filtered `scanFiltered` output.
Standard axioms only, no `native_decide`. -/

namespace Tests.Guards.TagShapeAxioms

open L4YAML.Proofs.TagShape in
/-- info: 'L4YAML.Proofs.TagShape.wordChar_alnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wordChar_alnum

open L4YAML.Proofs.TagShape in
/-- info: 'L4YAML.Proofs.TagShape.shaped_named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shaped_named

open L4YAML.Proofs.TagShape in
/-- info: 'L4YAML.Proofs.TagShape.collectTagHandleLoop_chars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms collectTagHandleLoop_chars

open L4YAML.Proofs.TagShape in
/-- info: 'L4YAML.Proofs.TagShape.scanTag_pushTag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scanTag_pushTag

open L4YAML.Proofs.TagShape in
/-- info: 'L4YAML.Proofs.TagShape.TagExt_scanNextToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TagExt_scanNextToken

open L4YAML.Proofs.TagShape in
/-- info: 'L4YAML.Proofs.TagShape.TagInv_scanLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TagInv_scanLoop

open L4YAML.Proofs.TagShape in
/-- info: 'L4YAML.Proofs.TagShape.TagInv_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TagInv_init

open L4YAML.Proofs.TagShape in
/-- info: 'L4YAML.Proofs.TagShape.scan_emitOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scan_emitOk

open L4YAML.Proofs.TagShape in
/-- info: 'L4YAML.Proofs.TagShape.scanFiltered_emitOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scanFiltered_emitOk

end Tests.Guards.TagShapeAxioms

end Blanket
