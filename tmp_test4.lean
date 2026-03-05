import Lean4Yaml.Scanner

open Lean4Yaml.Scanner

-- Test: what does the goal look like after unfold in succ case?
set_option maxHeartbeats 800000 in
theorem test_goal (s : ScannerState) (s' : ScannerState) (fuel' : Nat)
    (IH : ∀ (s : ScannerState), skipToContentLoop s fuel' = Except.ok s' → s'.tokens = s.tokens)
    (h : skipToContentLoop s (fuel' + 1) = .ok s') :
    s'.tokens = s.tokens := by
  unfold skipToContentLoop at h
  -- Just print what the first split looks like
  split at h
  · -- needIndentCheck = true path
    trace_state
    sorry
  · -- needIndentCheck = false path
    trace_state
    sorry
