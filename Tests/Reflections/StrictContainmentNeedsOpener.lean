/-
Reflection 368 — a self-contained toy of "STRICT close-containment needs the START opener".

A two-floor relay closes only the NON-strict `b ≤ c`; the strict `b < c` (the inner close does not
coincide with the enclosing interior's OWN end `c`) needs a THIRD input the relay is head-BLIND to —
the inner window's opener at `a-1`.  The enclosing gate constrains the interior balance + floor and the
mark at `a`, but NOT the token at `a-1`, so it admits a MID-ENTRY-SUFFIX window (start one-past a
separator) whose close reaches the enclosing end.  No project deps — an `Int`-balance toy of
`seqTarget_close_lt_interiorEnd` (`SeqInteriorSeparators.lean`, R368).

DUAL-EDGE (R371): the SAME window-absolute opener field discriminates BOTH edges of a two-edged
recursion walk.  DESCEND reads it forward (close-containment `win_hi`, `strict_containment` below);
ADVANCE reads it backward (start-exclusion `win_lo`, `advance_winlo_exclusion` below) — a boundary whose
`a-1` is a depth-`0` separator has `bal (a-1) a = 0`, contradicting the opener's `1`.  Both edges ask the
one question: real bracket boundary, or flat separator?
-/

namespace Tests.Reflections.StrictContainmentNeedsOpener

set_option autoImplicit false

/-! ## POSITIVE — the strict relay, abstract over any balance with a composition law. -/

/-- The strict containment, proved with the opener hypothesis `h_open : bal (a-1) a = 1`.  This is the
    faithful abstract form of `seqTarget_close_lt_interiorEnd`: assume `c ≤ b`; the gate floor at `c`
    composed through the balanced enclosing interior forces `bal (off+1) a = 0` (the spurious `a` sits
    at the interior TOP level); then the opener composes to `bal (off+1) (a-1) = -1`, contradicting the
    enclosing Dyck floor at `a-1`.  Only the enclosing balance + Dyck floor + the inner gate floor + the
    opener are used. -/
theorem strict_containment
    (bal : Nat → Nat → Int)
    (compose : ∀ lo mid hi, lo ≤ mid → mid ≤ hi → bal lo hi = bal lo mid + bal mid hi)
    (a b off c : Nat)
    (h_off_a : off + 2 ≤ a)
    (h_a_c : a ≤ c)
    (h_int_bal : bal (off + 1) c = 0)
    (h_int_floor : ∀ i, off + 1 ≤ i → i ≤ c → bal (off + 1) i ≥ 0)
    (h_open : bal (a - 1) a = 1)
    (_h_gate_bal : bal a b = 0)
    (h_gate_floor : ∀ i, a ≤ i → i ≤ b → bal a i ≥ 0) :
    b < c := by
  rcases Nat.lt_or_ge b c with h_lt | h_ge
  · exact h_lt
  · exfalso
    have h_ac : bal a c ≥ 0 := h_gate_floor c h_a_c h_ge
    have h_comp : bal (off + 1) c = bal (off + 1) a + bal a c :=
      compose (off + 1) a c (by omega) h_a_c
    have h_int_a : bal (off + 1) a ≥ 0 := h_int_floor a (by omega) h_a_c
    have h0 : bal (off + 1) a = 0 := by rw [h_int_bal] at h_comp; omega
    have h_comp2 : bal (off + 1) a = bal (off + 1) (a - 1) + bal (a - 1) a :=
      compose (off + 1) (a - 1) a (by omega) (by omega)
    have h_int_a1 : bal (off + 1) (a - 1) ≥ 0 := h_int_floor (a - 1) (by omega) (by omega)
    rw [h_open, h0] at h_comp2
    omega

/-! ## NEGATIVE — a concrete enclosing interior `x , [y]` where the relay alone admits `b = c`. -/

/-- Per-position bracket deltas of `[ x , [ y ] ]`: position 0 is the enclosing opener (+1), the interior
    `[1,6)` is `x(0) , (0) [ (+1) y(0) ] (-1)`, balanced.  `c = 6` is the interior's right end. -/
def D : List Int := [1, 0, 0, 1, 0, -1]

/-- Window balance = sum of the per-position deltas over `[lo, hi)`. -/
def bal (lo hi : Nat) : Int := ((D.drop lo).take (hi - lo)).sum

-- The enclosing interior `[1, 6)` is balanced (`off + 1 = 1`, `c = 6`).
#guard bal 1 6 == 0

/-! ### The SPURIOUS mid-suffix window: `a = 3` (one PAST the separator `,` at position 2).
    It passes the gate yet its close is the enclosing end `b = c = 6` — `win_hi` (`b < c`) is FALSE. -/

-- gate balance 0 over `[3, 6)`:
#guard bal 3 6 == 0
-- gate Dyck floor `≥ 0` at every point of `[3, 6]`:
#guard (decide (bal 3 3 ≥ 0) && decide (bal 3 4 ≥ 0) && decide (bal 3 5 ≥ 0) && decide (bal 3 6 ≥ 0))
-- so the relay admits `b = c = 6` — the close coincides with the enclosing interior's OWN end.
#guard bal 3 6 == 0 && decide ((6 : Nat) = 6)
-- BUT the opener at `a-1 = 2` is the separator `,` (delta 0), NOT a `[` (delta 1):
#guard bal 2 3 == 0
#guard (bal 2 3 == 1) == false   -- the opener hypothesis FAILS for the spurious window

/-! ### A GENUINE entry window: `a = 4` (one past the real opener `[` at position 3). -/

-- gate balance 0 over `[4, 5)`, and the opener at `a-1 = 3` IS a `[` (delta 1):
#guard bal 4 5 == 0
#guard bal 3 4 == 1              -- opener present
#guard decide ((5 : Nat) < 6)    -- so `b = 5 < c = 6` — strict containment holds, as the lemma proves

/-! ## DUAL-EDGE (R371) — the SAME opener excludes the ADVANCE-arm separator-headed boundary. -/

/-- The ADVANCE arm's `win_lo` exclusion, abstractly: the recursion-walk arm admits the boundary
    `a = m + 1` (target start one PAST the consumed entry, with the separator at `m`), but the SAME
    window-absolute opener `h_open : bal (a-1) a = 1` that `strict_containment` reads for `win_hi`
    EXCLUDES it here — at `a = m+1`, `a-1 = m` is the depth-`0` separator (`bal m (m+1) = 0`),
    contradicting the opener's `1`.  This lifts the arm's weak `m < a` to the guard's `m + 1 < a`
    (no separator-headed start).  Opener read at the OTHER walking edge: start-exclusion, not
    close-containment. -/
theorem advance_winlo_exclusion
    (bal : Nat → Nat → Int) (a m : Nat)
    (h_boundary : a = m + 1)
    (h_sep : bal m (m + 1) = 0)
    (h_open : bal (a - 1) a = 1) : False := by
  subst h_boundary
  rw [Nat.add_sub_cancel] at h_open
  omega

-- Concrete witness on the SAME `D = [ x , [ y ] ]`: at the boundary `a = 3` (`m = 2`), `a-1 = 2` is the
-- separator `,` with `bal 2 3 = 0` ≠ the opener's `1` — so the separator-headed start is excluded.
#guard bal 2 3 == 0 && (bal 2 3 == 1) == false

end Tests.Reflections.StrictContainmentNeedsOpener
