/-!
# Reflection 314 — a located matching-close's containment bound is a TWO-FLOOR RELAY: a single underflow witness at `close+1`, refuted by whichever of two ADJACENT-domain floors tiles it

Self-contained (core Lean) toy of the forward-CLOSE brick `(i'-b-locator-glue-close)`.

The real situation: a seq descent locates an enclosing opener `p` and its matching close `j`
(`balance (p+1) j = 0`, the close token has delta `-1`).  The consumer needs the located close to
CONTAIN the gated window `[a, b)` — i.e. `a ≤ j` AND `b ≤ j` — so it can hand `hiS = j` to the
enclosing-facts provider.  These two bounds are NOT returned by the matching-close locator (it only
gives `j < hi`); they come from the consumer's OWN floors, via one underflow witness.

**The mechanism.** The close at `j` underflows the next step for ANY base `β ≤ j`:
`balance β (j+1) = balance β j + delta_j = balance β j − 1`.  The span the bound must reach,
`[p+1, b]`, is tiled by two SEPARATELY-SOURCED floors:

* the **locator floor** over `[p+1, a]`  (the backward locator's output), and
* the **gate floor** over `[a, b]`  (R313's gate conjunct).

You do NOT need one unified floor over the whole span — two adjacent floors that TILE it suffice, and
you case-split on which domain `close+1` falls into:

* `a ≤ j` — else `j+1 ≤ a`, so `j+1` is in the locator-floor domain, and
  `balance (p+1)(j+1) = 0 − 1 = −1 < 0` contradicts the floor.
* `b ≤ j` — else `j+1 ≤ b`; having `a ≤ j` (⇒ `a ≤ j+1`), `j+1` is in the gate-floor domain, and
  `balance a (j+1) = 0 − 1 = −1 < 0` contradicts the floor (`balance a j = 0` by composition).

The first bound is the GUARD that lets the second floor's lower edge (`a ≤ j+1`) hold — the relay is
ordered.  This is the general mechanism behind R313's "the floor discharges `b ≤ hiS` for free".
-/

namespace Tests.Reflections.TwoFloorRelayCloseBound

set_option autoImplicit false

/-- **The TWO-FLOOR RELAY (proven, the transferable nugget).**  `bal` is any running balance
    satisfying additivity (`compose`) and the close-underflow step at `j` (`step_underflow`).  Given
    the located close `j` (`h_inner : bal (p+1) j = 0`), the re-seated window start
    (`h_body : bal (p+1) a = 0`), and two floors tiling `[p+1, b]`, the close CONTAINS `[a, b)`:
    `a ≤ j ∧ b ≤ j`.  No unified floor — adjacent floors + a case-split on where `close+1` lands. -/
theorem located_close_bounds
    (bal : Nat → Nat → Int)
    (compose : ∀ x y z, x ≤ y → y ≤ z → bal x z = bal x y + bal y z)
    (p a b j : Nat) (hp_j : p < j) (hp_a : p + 1 ≤ a)
    (step_underflow : ∀ β, β ≤ j → bal β (j + 1) = bal β j - 1)
    (h_inner : bal (p + 1) j = 0)
    (h_body : bal (p + 1) a = 0)
    (loc_floor : ∀ i, p + 1 ≤ i → i ≤ a → 0 ≤ bal (p + 1) i)
    (gate_floor : ∀ i, a ≤ i → i ≤ b → 0 ≤ bal a i) :
    a ≤ j ∧ b ≤ j := by
  -- (1) `a ≤ j` — the locator floor at `j+1` refutes `j < a`.
  have h_a_j : a ≤ j := by
    rcases Nat.lt_or_ge j a with h | h
    · have hf := loc_floor (j + 1) (by omega) (by omega)
      rw [step_underflow (p + 1) (by omega), h_inner] at hf; omega
    · exact h
  refine ⟨h_a_j, ?_⟩
  -- (2) `bal a j = 0` by composition over `[p+1, a, j]`.
  have h_aj : bal a j = 0 := by
    have hc := compose (p + 1) a j (by omega) h_a_j
    rw [h_inner, h_body] at hc; omega
  -- (3) `b ≤ j` — the GATE floor at `j+1` refutes `j < b` (using `a ≤ j` ⇒ `a ≤ j+1`).
  rcases Nat.lt_or_ge j b with h | h
  · have hf := gate_floor (j + 1) (by omega) (by omega)
    rw [step_underflow a h_a_j, h_aj] at hf; omega
  · exact h

-- ════════════════════ a concrete witness: `[[1], [2]]`'s bracket skeleton ════════════════════
-- Toy alphabet: op (+1), cl (-1), ct (content, 0).
inductive Tok | op | cl | ct deriving DecidableEq, Inhabited

def d : Tok → Int | .op => 1 | .cl => -1 | .ct => 0

def bal (L : List Tok) (a b : Nat) : Int :=
  ((L.drop a).take (b - a)).foldl (fun s t => s + d t) 0

/-- `op op ct cl op ct cl cl` — 0:op(outer) 1:op(first inner) 2:ct 3:cl 4:op(second inner) 5:ct
    6:cl 7:cl(outer).  The first inner seq: opener `p = 1`, body `[2,3)`, matching close `j = 3`. -/
def W : List Tok := [.op, .op, .ct, .cl, .op, .ct, .cl, .cl]

-- ════════════════════ POSITIVE — the located close `j = 3` CONTAINS the genuine window [2,3) ════
#guard bal W 2 3 == 0            -- balance (p+1) j = bal 2 3 = 0  (the inner body balances)
#guard bal W 1 4 == 0            -- balance lo (j+1) = 0  ⇒  j = 3 is the matching close of p = 1
#guard d W[3]! == -1             -- the close token has delta -1
#guard bal W 2 4 == -1           -- balance (p+1) (j+1) = -1  (the close+1 underflow witness)
-- for the genuine gated window [a,b) = [2,3):  a = 2 ≤ j = 3  ∧  b = 3 ≤ j = 3
#guard decide (2 ≤ 3) && decide (3 ≤ 3)

-- ════════════════════ NEGATIVE — the GATE floor is necessary (cross-sibling window) ════════════
-- The cross-sibling window [2,6) is balanced (passes a floor-blind gate) but DIPS below 0 crossing
-- the close at 3, so the gate floor over [2,6] FAILS — and indeed its end 6 > j = 3 (bound violated):
#guard bal W 2 6 == 0            -- balanced
#guard bal W 2 4 == -1           -- ... yet dips: gate floor over [2,6] fails at i = 4
#guard decide (6 > 3)            -- so `b ≤ j` would be FALSE — the gate floor is what excludes it

end Tests.Reflections.TwoFloorRelayCloseBound
