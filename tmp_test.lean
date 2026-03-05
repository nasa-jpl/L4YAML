import Lean4Yaml.Scanner

open Lean4Yaml.Scanner

-- Can we unfold skipToContentLoop?
theorem test_unfold (s : ScannerState) :
    skipToContentLoop s 0 = .ok s := by
  unfold skipToContentLoop
  rfl

-- Can we do induction on fuel?
theorem test_induction (s : ScannerState) (s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.tokens = s.tokens := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h
    rw [h]
  | succ fuel' IH =>
    sorry

#check @test_unfold
#check @test_induction
