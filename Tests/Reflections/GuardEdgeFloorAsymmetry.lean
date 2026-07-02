/-
# Reflection 288 — two edges of one guard need different invariant strengths

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflection 288 (and the within-one-recursion instance noted in memory
`ref-converse-forward-invariant-asymmetry`, extending `ref-guard-threading-skeleton-before-grammar`).

**The principle.** Reflection 287 named the per-window `step`'s grammar-free *guard-threading
skeleton*: concretize the recursion combinator's abstract guard `G` and prove it PRESERVED across each
recursion edge before any head-shape content. R288 completes the skeleton with the DESCEND edge and
records its lesson: **the same guard field — here the `dyck` prefix-nonnegativity — does NOT need the
same invariant strength on every edge.**

  * **ADVANCE** (the tail `[m+1, hi)` after a depth-`0` separator) re-bases onto a *balanced* prefix
    (`bal lo (m+1) = 0`), so `bal (m+1) i = bal lo i`, and the tail `dyck ≥ 0` falls straight out of the
    OUTER `dyck ≥ 0`. No extra strength.
  * **DESCEND** (the interior `[k+1, j)` of a matched bracket) sits a level DOWN — the opener pushes the
    running balance to `1` (`bal lo (k+1) = 1`), so `bal (k+1) i = bal lo i − 1`, and the interior
    `dyck ≥ 0` holds IFF `bal lo i ≥ 1` — the strictly-stronger matched-bracket FLOOR, NOT the outer
    `≥ 0`. That floor must be SUPPLIED by the position locator (the forward scan that found the closer);
    it cannot be recovered from the guard's own outer `dyck`.

This is [[ref-converse-forward-invariant-asymmetry]] instanced *inside a single recursion*: two
transports of one guard, the descend edge demanding a strictly stronger invariant than the advance edge.

**What this demo asserts (fails the build if it ever drifts):**
  * POSITIVE — `advance_dyck` derives the tail `dyck` from JUST the outer `dyck ≥ 0` (a balanced
    prefix), while `descend_dyck` needs the FLOOR `≥ 1`; on a real matched bracket (`fNest = "[ [ ] ]"`)
    the floor holds and the interior `dyck` follows.
  * NEGATIVE — outer `dyck ≥ 0` is genuinely INSUFFICIENT for the descend conclusion: on
    `fFlat = "[ ] [ ]"` the outer `dyck` holds everywhere, yet the re-based interior balance
    `bal fFlat 1 2 = −1` dips below `0` — because the FLOOR fails there (`bal fFlat 0 2 = 0`, not `≥ 1`).
    So you cannot reuse the advance edge's weaker hypothesis on the descend edge.
-/

namespace Tests.Reflections.GuardEdgeFloorAsymmetry

/-! ## The toy balance — `bal f a b` is the running depth change from `a` to `b`

`f i` is the cumulative bracket depth after `i` tokens (the toy of `flowBracketBalance tokens 0 i`),
and `bal f a b = f b − f a` is the depth change over `[a, b)` (the toy of `flowBracketBalance a b`),
so re-basing across a split point is just subtraction — exactly the algebra of `flowBracketBalance`. -/
def bal (f : Nat → Int) (a b : Nat) : Int := f b - f a

/-- `"[ [ ] ]"` — deltas `[+1, +1, −1, −1]`; cumulative depth `0,1,2,1,0`. The outer `[` at position `0`
    is matched by `]` at position `3`; its interior `[1, 3)` is a real nested bracket. -/
def fNest : Nat → Int
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 1 | _ => 0

/-- `"[ ] [ ]"` — deltas `[+1, −1, +1, −1]`; cumulative depth `0,1,0,1,0`. The `[` at `0` is matched at
    position `1`, so `[1, 3)` is NOT a matched interior — the balance returns to `0` at position `2`
    *inside* it. This is the negative witness: balanced-and-outer-dyck does not imply floored. -/
def fFlat : Nat → Int
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1 | _ => 0

/-! ## The two abstract preservation lemmas — same `dyck` field, different strengths

Both are pure re-basing algebra (`omega` over the opaque atoms `f i`, `f lo`, `f (m+1)`/`f (k+1)`); the
difference is entirely in the HYPOTHESIS each needs. -/

/-- **ADVANCE `dyck`** — the tail re-bases onto a *balanced* prefix (`bal lo (m+1) = 0`), so the tail
    `dyck ≥ 0` follows from the OUTER `dyck ≥ 0` alone. The toy of `flowBodyWindow_advance`'s `dyck`
    field. -/
theorem advance_dyck (f : Nat → Int) (lo m : Nat)
    (h_pre : bal f lo (m + 1) = 0)
    (h_outer : ∀ i, bal f lo i ≥ 0) :
    ∀ i, bal f (m + 1) i ≥ 0 := by
  intro i
  have hb := h_outer i
  unfold bal at h_pre hb ⊢
  omega

/-- **DESCEND `dyck`** — the interior sits a level down (`bal lo (k+1) = 1`), so the interior
    `dyck ≥ 0` needs the strictly-stronger FLOOR `bal lo i ≥ 1`, NOT the outer `≥ 0`. The toy of
    `flowBodyWindow_descend`'s `dyck` field; the floor is what `flowBracketBalance_matching_close`
    threads through its forward scan. -/
theorem descend_dyck (f : Nat → Int) (lo k : Nat)
    (h_off : bal f lo (k + 1) = 1)
    (h_floor : ∀ i, bal f lo i ≥ 1) :
    ∀ i, bal f (k + 1) i ≥ 0 := by
  intro i
  have hf := h_floor i
  unfold bal at h_off hf ⊢
  omega

/-! ## Positives — a real matched bracket: the floor holds, so the descend `dyck` does too -/

-- POSITIVE: the opener pushes the running balance to `1` (the descend offset), and the matched-bracket
-- FLOOR `≥ 1` holds across the interior `(0, 3]` of `fNest`.
theorem nest_offset : bal fNest 0 1 = 1 := by decide
theorem nest_floor : bal fNest 0 1 ≥ 1 ∧ bal fNest 0 2 ≥ 1 ∧ bal fNest 0 3 ≥ 1 := by decide
-- POSITIVE: hence the re-based interior `dyck ≥ 0` holds across `[1, 3]` (what `descend_dyck` delivers).
theorem nest_interior_dyck :
    bal fNest 1 1 ≥ 0 ∧ bal fNest 1 2 ≥ 0 ∧ bal fNest 1 3 ≥ 0 := by decide

/-! ## Negatives — outer `dyck ≥ 0` is genuinely insufficient for the descend edge -/

-- NEGATIVE: on `fFlat` the OUTER `dyck ≥ 0` holds at every position `[0, 4]`...
theorem flat_outer_dyck :
    bal fFlat 0 0 ≥ 0 ∧ bal fFlat 0 1 ≥ 0 ∧ bal fFlat 0 2 ≥ 0 ∧
      bal fFlat 0 3 ≥ 0 ∧ bal fFlat 0 4 ≥ 0 := by decide
-- ...yet the re-based interior balance DIPS BELOW 0 — so `descend_dyck`'s CONCLUSION is false here,
-- proving the advance edge's weaker hypothesis (outer dyck) cannot be reused on the descend edge.
theorem flat_interior_dips : bal fFlat 1 2 = -1 := by decide
-- ...and the reason is precisely that the FLOOR fails: `bal fFlat 0 2 = 0`, not `≥ 1`.
theorem flat_floor_fails : ¬ (bal fFlat 0 2 ≥ 1) := by decide

-- The negative as a direct refutation: the descend conclusion `∀ i, bal fFlat 1 i ≥ 0` is FALSE
-- (witnessed at `i = 2`), so no proof of it can be had from the outer-dyck-only hypothesis.
theorem not_flat_interior_dyck : ¬ (∀ i, bal fFlat 1 i ≥ 0) :=
  fun h => absurd (h 2) (by decide)

/-! ## Both edges strictly narrow the window — the combinator's width metric decreases either way -/

-- ADVANCE `[2, 6)` and DESCEND `[3, 5)` both have width `< 4` (the outer `[2, 6)` width). -/
#guard (6 - 3) < (6 - 2)        -- ADVANCE narrows (origin moves up)
#guard (5 - 3) < (6 - 2)        -- DESCEND narrows (both ends move in)

end Tests.Reflections.GuardEdgeFloorAsymmetry
