/-!
# Reflection 435 — probe the GOAL itself for falsity, not just the intermediate obligation

Self-contained (core Lean, no `L4YAML` import) toy of the R435 finding.

Context.  R389–R434 built ~45 rounds of producer machinery toward an intermediate `h_seq_rec` (a
per-window `RecSeqBody` universal), which feeds the sorry GOAL `FlowSubrangesOk tokens` (the parser
contract).  R433 probed the INTERMEDIATE and found its 7-guard shape unsatisfiable (a cross-matched false
window).  R435 probes the GOAL — and finds it ALSO false.

The finding.  `FlowSubrangesOk`'s DEFINITION (`ParserGrammableBase`) quantifies `∀ lo hi, (five
bracket-shape guards, NO interior floor) → SeqBodyProps tokens lo hi`, and `SeqBodyProps.content_start`
forces `lo < hi → isFlowContentStart tokens[lo]`.  On `[[],[a]]` the cross-matched window `[3, 7)`
satisfies all five guards but `tokens[3] = .flowSequenceEnd` (the first element's close), so
`content_start` demands `isFlowContentStart .flowSequenceEnd` — FALSE.  So `FlowSubrangesOk tokens` is
false, the sorry goal is unachievable AS STATED, and NO producer machinery can close it.

Reusable rule: when a long producer effort fails to compose toward a goal, machine-check the GOAL ITSELF
on a concrete input — not just the intermediate sub-obligations you have been building.  A guard missing
from the GOAL's DEFINITION makes the goal false on real inputs; the fix is at the definition (add the
guard) and its consumer (re-prove it to query only the now-restricted windows), never the producer.  Probe
the goal early and often, not only the producer's residuals.

The toy below: a GOAL whose definition quantifies over a too-weak guard, machine-checked FALSE on a
concrete witness — the mirror of `flowSubrangesOk_false_window`.
-/

namespace Tests.Reflections.ProbeTheGoal

set_option autoImplicit false

/-- A GOAL definition that quantifies over a too-weak guard (`toks[k]! = 1`, "is an opener") with NO
    floor-like restriction — the mirror of `FlowSubrangesOk.seq`/`SeqBodyProps` quantifying over
    bracket-shape windows with no interior Dyck floor.  It demands "every opener is followed by content `2`". -/
def Goal (toks : List Nat) : Prop :=
  ∀ k, k + 1 < toks.length → toks[k]! = 1 → toks[k + 1]! = 2

/-- A concrete input where the GOAL is FALSE: an opener `1` at position 0 whose successor is `9`, not `2`
    (the toy of the cross-matched window whose head fails `content_start`). -/
def witness : List Nat := [1, 9, 2]

#guard witness[0]! == 1     -- the guard premise holds (position 0 is an "opener")
#guard witness[1]! == 9     -- but the GOAL would demand this be `2`

/-- **The GOAL is false** — machine-checked, the mirror of `flowSubrangesOk_false_window`.  A producer
    that establishes some intermediate could never close this; the goal's own definition is too weak. -/
theorem goal_false : ¬ Goal witness := by
  intro h
  have hc := h 0 (by decide) (by decide)
  exact absurd hc (by decide)

/-- The FIX direction (at the DEFINITION, not the producer): a goal that ADDS a guard excluding the bad
    case (here `toks[k+1]! ≠ 9`, the toy of the interior Dyck floor) holds vacuously on the witness — the
    only opener's successor is `9`, which the new guard gates out. -/
def GoalFixed (toks : List Nat) : Prop :=
  ∀ k, k + 1 < toks.length → toks[k]! = 1 → toks[k + 1]! ≠ 9 → toks[k + 1]! = 2

theorem goalFixed_holds_on_witness : GoalFixed witness := by
  intro k _ h1 hne
  have hk : k = 0 ∨ k = 1 := by
    have : k + 1 < 3 := by simpa [witness] using ‹k + 1 < witness.length›
    omega
  rcases hk with rfl | rfl
  · exact absurd (by decide : witness[0 + 1]! = 9) hne
  · exact absurd h1 (by decide)

end Tests.Reflections.ProbeTheGoal
