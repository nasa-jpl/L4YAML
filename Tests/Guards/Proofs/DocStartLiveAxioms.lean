module

public import L4YAML.Proofs.Scanner.DocStartLive

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Axiom census: S3 obligation (β), the document-start liveness carrier (list level)

Capstone 7.7 `parse_iff_grammar`, stream S3.  `DocStartLive` states the raw-list
shape `Shape` (no dead real token right after a boundary, through placeholders),
the filtered-list property `LiveF`, and the bridge `LiveF_of_Shape` through the
placeholder filter.  Standard axioms only, no `native_decide`, on every
declaration. -/

namespace Tests.Guards.DocStartLiveAxioms

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.lastReal_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lastReal_snoc

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.lastReal_append_ph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lastReal_append_ph

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.Shape_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shape_snoc

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.Shape_append_ph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shape_append_ph

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.filter_getLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms filter_getLast

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.LiveF_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LiveF_snoc

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.LiveF_of_Shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LiveF_of_Shape

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.lastReal_append_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lastReal_append_cases

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.Shape_append_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shape_append_live

open L4YAML.Proofs.DocStartLive in
/-- info: 'L4YAML.Proofs.DocStartLive.Bnd_lastReal_append_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bnd_lastReal_append_live

end Tests.Guards.DocStartLiveAxioms
