/-!
# Reflection 433 — endpoint+balance bracket guards admit cross-matched false windows

Self-contained (core Lean, no `L4YAML` import) toy of the R433 finding.

Context.  The flat per-window provider (`windowFacts`) and the consumer's `h_seq_rec` both quantify over
every window `[lo, hi)` gated by SEVEN bracket-shape facts: `2 ≤ lo`, `lo < hi`, `hi ≤ size-2`,
`hi < size`, `tokens[hi] = .flowSequenceEnd`, `flowBracketBalance lo hi = 0`, and
`tokens[lo-1] = .flowSequenceStart`.  The plan was to "supply the Dyck floor `h_win_dyck` once from
whole-stream well-bracketedness" — treating it as a restriction of a global fact.

The finding.  Those seven guards do NOT pin a MATCHED bracket pair, so the universal is UNSATISFIABLE.
`tokens[lo-1]` and `tokens[hi]` can close DIFFERENT brackets, with `balance lo hi = 0` holding only by
COINCIDENCE across a separator.  Machine-checked (R433, `seqWindowFacts_false_window`): `[[],[a]]` scans to
`streamStart, [, [, ], `,`, [, a, ], ], streamEnd`; the window `[3, 7)` satisfies all seven guards
(`tokens[2] = [`, `tokens[7] = ]`, `balance 3 7 = 0`) yet `balance 3 4 = -1` (its head is the FIRST
element's CLOSE `]`), so the Dyck floor underflows and `FlowBodyWindow` is FALSE.

The fix.  `h_win_dyck` is NOT a global-restriction primitive — it is the GUARD that DEFINES a genuine
window.  Add the Dyck floor `∀ i ∈ [lo, hi], balance lo i ≥ 0` as an extra guard: it EXCLUDES every
cross-matched false window and makes the floor a trivial pass-through.  This is the end-free-gate family —
an endpoint + total-balance gate underdetermines the matched pair; the interior floor is the discriminator.

The toy below models the body `[][a]` (`[ ] , [ a ]`) and exhibits the cross-matched window `[1, 5)`:
endpoint + total-balance guards hold, but the floor underflows at the first step — and the Floor guard
rejects it.
-/

namespace Tests.Reflections.BracketGuardsAdmitCrossMatched

set_option autoImplicit false

/-- Toy bracket-delta: open `1 ↦ +1`, close `2 ↦ -1`, separator/content neutral. -/
def delta : Nat → Int
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- Balance over `[a, b)` (mirror of `flowBracketBalance tokens a b`). -/
def bal (toks : List Nat) (a b : Nat) : Int := (((toks.take b).drop a).map delta).sum

/-- The body of `[[],[a]]`: `[ ] , [ a ]` — an empty seq, a separator, then a singleton seq.
    Indices: 0=`[` 1=`]` 2=`,` 3=`[` 4=`a` 5=`]`. -/
def toks : List Nat := [1, 2, 3, 1, 4, 2]

/-! ## The cross-matched window `[1, 5)` — endpoint + total balance hold, floor underflows. -/

-- `tokens[lo-1]` is an opener and `tokens[hi]` is a closer and the window balances to `0`:
#guard toks[0]! == 1            -- toks[lo-1] = `[`
#guard toks[5]! == 2            -- toks[hi]   = `]`
#guard (bal toks 1 5 == 0)      -- the window balances
-- yet the floor underflows at the very first step (the window head `toks[1]` is a CLOSE):
#guard (bal toks 1 2 == -1)     -- balance dips below 0 ⇒ NOT a matched-pair interior

/-- **Endpoint + total-balance do NOT imply the floor** — the four facts coexist, so the seven-guard
    universal cannot derive `FlowBodyWindow`'s Dyck floor. -/
theorem guards_dont_imply_floor :
    toks[0]! = 1 ∧ toks[5]! = 2 ∧ bal toks 1 5 = 0 ∧ bal toks 1 2 = -1 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

/-- The Dyck floor over `[lo, hi)` (mirror of `FlowBodyWindow.dyck`). -/
def Floor (toks : List Nat) (lo hi : Nat) : Prop := ∀ i, lo ≤ i → i ≤ hi → bal toks lo i ≥ 0

/-- **The fix: the Floor guard REJECTS the cross-matched false window.**  So adding the floor as an extra
    guard excludes `[1, 5)` (and every cross-matched window), restoring satisfiability. -/
theorem false_window_fails_floor : ¬ Floor toks 1 5 := by
  intro hF
  have hd := hF 2 (by omega) (by omega)   -- bal toks 1 2 ≥ 0
  exact absurd hd (by decide)             -- but bal toks 1 2 = -1

end Tests.Reflections.BracketGuardsAdmitCrossMatched
