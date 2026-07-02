/-!
# Reflection 431 — a window's Dyck floor already encodes the non-emptiness gate

Self-contained (core Lean, no `L4YAML` import) toy of the R431 step.

Context.  R430's assembler `flowBodyContentDeepSeq_of_window_producers` took, as an explicit hypothesis,
the non-degeneracy gate `h_head_ne : tokens[lo] ≠ .flowSequenceEnd` (the window head is not the closing
bracket).  That looked like a fresh emission residual to source.  It is not.

The finding.  The gate is a FREE consequence of an invariant the consumer ALREADY threads — the window's
Dyck floor `∀ i ∈ [lo, hi], flowBracketBalance tokens lo i ≥ 0`.  A closing bracket has bracket-delta
`-1`, so the one-step floor `flowBracketBalance tokens lo (lo+1) ≥ 0` is VIOLATED if the head is a close.
In other words the non-emptiness of a body window (`tokens[lo] ≠ ]`) is ENCODED in its floor: an empty
`[]` window has a close-head, but its floor dips to `-1` at the very first step, so it is not a
`FlowBodyWindow` at all.  Don't thread the gate — read it off the floor.

Reusable rule: when an assembler asks for a "non-emptiness" or "head/edge is well-shaped" gate, check
whether the consumer's already-threaded MONOTONE invariant (a Dyck floor / balance lower bound) forbids
the bad edge case.  The degenerate configuration fails the floor at its first step, so the floor IS the
non-emptiness witness — the gate is not an independent fact.

The toy below: `delta` (open `+1`, close `-1`, neutral `0`), the prefix balance `bal`, and a `Floor`
predicate.  `head_ne_close_of_floor` derives `head ≠ close` from the floor; a `#guard` exhibits the
close-headed window that the floor rejects (`bal [close] 1 = -1 < 0`).
-/

namespace Tests.Reflections.FloorEncodesNonemptiness

set_option autoImplicit false

/-- Toy bracket-delta: open `1 ↦ +1`, close `2 ↦ -1`, everything else neutral (mirror of
    `flowBracketDelta`; the seq close `.flowSequenceEnd` is the `2` here, delta `-1`). -/
def delta : Nat → Int
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- Prefix balance of the first `k` tokens (mirror of `flowBracketBalance tokens lo (lo+k)`). -/
def bal (toks : List Nat) (k : Nat) : Int := ((toks.take k).map delta).sum

/-- The Dyck floor — every prefix balance is `≥ 0` (mirror of `FlowBodyWindow.dyck`). -/
def Floor (toks : List Nat) : Prop := ∀ i, i ≤ toks.length → bal toks i ≥ 0

/-- **The head is never the close — FREE from the floor.**  The one-step balance after the head is
    `delta head`; the floor forces it `≥ 0`; the close has delta `-1`, contradiction.  Toy of
    `flowBodyWindow_head_ne_close` (the Dyck-floor consequence R430's `h_head_ne` actually was). -/
theorem head_ne_close_of_floor (head : Nat) (t : List Nat) (h_floor : Floor (head :: t)) :
    head ≠ 2 := by
  intro h_close
  have hf := h_floor 1 (Nat.succ_le_succ (Nat.zero_le _))
  have hbal : bal (head :: t) 1 = delta head := by simp [bal]
  rw [hbal, h_close] at hf
  -- hf : delta 2 ≥ 0, i.e. (-1 : Int) ≥ 0
  rw [show delta 2 = -1 from rfl] at hf
  omega

-- **NEGATIVE / the rejected window** — a close-headed window violates the floor at its FIRST step:
-- `bal [close] 1 = delta 2 = -1 < 0`.  So a `Floor` window CANNOT have a close head — the gate
-- `head ≠ close` is not an independent fact, it is the floor refusing the empty/degenerate case.
#guard (bal [2] 1 == (-1 : Int))
#guard decide (bal [2] 1 < 0)
-- and a genuine (non-empty, open-headed) window passes the one-step floor:
#guard decide (bal [1, 2] 1 ≥ 0)      -- delta 1 = +1 ≥ 0

end Tests.Reflections.FloorEncodesNonemptiness
