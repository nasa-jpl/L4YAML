import Lean4Yaml.Scanner
open Lean4Yaml.Scanner

-- Try: unfold + dsimp to beta-reduce join points, then split at top level
set_option maxHeartbeats 4000000 in
theorem test_beta (s : ScannerState) (s' : ScannerState) (fuel' : Nat)
    (IH : ∀ (s : ScannerState), skipToContentLoop s fuel' = Except.ok s' → s'.tokens = s.tokens)
    (h : skipToContentLoop s (fuel' + 1) = .ok s') :
    s'.tokens = s.tokens := by
  unfold skipToContentLoop at h
  -- Try dsimp to beta-reduce the have-bindings
  dsimp only [] at h
  -- See the shape now
  trace_state
  sorry
