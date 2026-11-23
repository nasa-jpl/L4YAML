module

public import L4YAML.CapstoneAttr
public meta import L4YAML.CapstoneAttr
public meta import Lean.Elab.GuardMsgs

public section

/-!
Negative controls for the actual capstone admission command. Every deliberately
unsupported declaration is confined to `withoutModifyingEnv`: no test axiom or
tagged test theorem survives in this module's exported environment.

These controls catch admitting a custom assumption because it is private or has
a native-looking name. The positive controls exercise ordinary kernel proofs
and the real `native_decide` elaborator, not a hand-written imitation.
-/

open Lean Elab Command

private meta def gateMustReject (decls : Array Syntax) : CommandElabM Unit :=
  withoutModifyingEnv do
    for stx in decls do elabCommand stx
    if (← get).messages.hasErrors then
      throwError "could not elaborate an axiom-gate fixture"
    let savedMessages := (← get).messages
    modify fun s => { s with messages := {} }
    let msgs ← Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages
      (← `(command| #assert_capstone_axioms))
    modify fun s => { s with messages := savedMessages }
    let mut rejected := false
    for msg in msgs.toList do
      if msg.severity == .error &&
          (← msg.data.toString).contains "depends on non-allowed axioms" then
        rejected := true
    unless rejected do
      throwError "capstone gate did not reject a deliberately unsupported axiom"

run_cmd gateMustReject #[
  ← `(command| private axiom boolAssumption : (false : Bool) = true),
  ← `(command| @[capstone] theorem boolClaim : (false : Bool) = true := boolAssumption)]

run_cmd gateMustReject #[
  ← `(command| private axiom privateAssumption : False),
  ← `(command| @[capstone] theorem privateClaim : False := privateAssumption)]

run_cmd gateMustReject #[
  ← `(command| axiom publicAssumption : False),
  ← `(command| @[capstone] theorem publicClaim : False := publicAssumption)]

run_cmd gateMustReject #[
  ← `(command| private axiom forged._native.native_decide.ax_1 : (false : Bool) = true),
  ← `(command| @[capstone] theorem forgedClaim : (false : Bool) = true :=
    forged._native.native_decide.ax_1)]

-- The Boolean result is reflexive, but its input term carries an independent
-- custom assumption. Checking the Boolean shape/value alone would admit it.
run_cmd gateMustReject #[
  ← `(command| axiom falsePremise : False),
  ← `(command| def proofDependent (_h : False) : Bool := true),
  ← `(command| private axiom dependent._native.native_decide.ax_1 :
    proofDependent falsePremise = true),
  ← `(command| @[capstone] theorem dependentClaim : proofDependent falsePremise = true :=
    dependent._native.native_decide.ax_1)]

run_cmd withoutModifyingEnv do
  elabCommand (← `(command| @[capstone] theorem propextControl (p q : Prop)
    (h : p ↔ q) : p = q := propext h))
  elabCommand (← `(command| @[capstone] theorem choiceControl : True :=
    Classical.choice (show Nonempty True from ⟨True.intro⟩)))
  elabCommand (← `(command| @[capstone] theorem quotientControl :
    Quot.mk (fun (_ _ : Unit) => True) () = Quot.mk (fun (_ _ : Unit) => True) () :=
    Quot.sound True.intro))
  elabCommand (← `(command| @[capstone] theorem kernelControl : 3 + 4 = 7 := rfl))
  elabCommand (← `(command| @[capstone] theorem nativeControl :
    (List.range 40).length = 40 := by native_decide))
  -- Opacity forces the native replay fallback rather than kernel reduction.
  elabCommand (← `(command| opaque opaqueTrue : Bool := true))
  elabCommand (← `(command| @[capstone] theorem nativeOpaqueControl :
    opaqueTrue = true := by native_decide))
  -- Admission validates the claim, not a name-based story about its origin.
  elabCommand (← `(command| private axiom independentlyTrue : (true : Bool) = true))
  elabCommand (← `(command| @[capstone] theorem replayedTrueControl :
    (true : Bool) = true := independentlyTrue))
  elabCommand (← `(command| #assert_capstone_axioms))

-- A previous successful replay cannot authorize a later false claim.
run_cmd gateMustReject #[
  ← `(command| private axiom independentlyTrue : (false : Bool) = true),
  ← `(command| @[capstone] theorem replayedFalseControl : (false : Bool) = true :=
    independentlyTrue)]

run_cmd do
  unless (L4YAML.capstoneDecls (← getEnv)).isEmpty do
    throwError "axiom-gate controls leaked a tagged fixture into the module"

end
