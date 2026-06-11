/-
Reflection 370 — an additive carrier field's per-arm cost is set by the arm's ROLE and the field's
KEYING, not by the fact that it is "additive".

A recursion-threaded guard carries a WINDOW-ABSOLUTE field (keyed on the fixed target `[a, b]`) and a
WALKING-KEYED field (keyed on the moving origin `[off, H)`).  Adding such a field:
  * leaves READ-ONLY arms (project fields, return the deliverable) untouched — they never supply it;
  * is a verbatim pass-through at CONSTRUCTING arms for the window-absolute field;
  * but must be RE-ESTABLISHED at CONSTRUCTING arms for the walking-keyed field — its proposition at
    the child window differs from the parent's, so `g.field` does not typecheck.

The "additive ⇒ every landed arm ignores it" intuition is correct for read-only arms but WRONG for a
constructing arm holding a walking-keyed field.  No project deps — a Nat-window toy of the R370
`SeqLocateGuard.window` extension (`SeqInteriorSeparators.lean`).
-/

namespace Tests.Reflections.AdditiveFieldCostByKeying

set_option autoImplicit false

/-! ## The toy guard: one WINDOW-ABSOLUTE field, one WALKING-KEYED field. -/

/-- A recursion-threaded guard over a fixed target `[a, b]` and a walking window `[off, H)`. -/
structure Guard (a b off H : Nat) : Prop where
  /-- WINDOW-ABSOLUTE: keyed on the fixed `a`/`b` only — invariant across the walk. -/
  abs : a ≤ b
  /-- WALKING-KEYED: keyed on the moving `off`/`H` — its statement changes every recursion move. -/
  walk : off + 2 ≤ H

/-! ## POSITIVE — the constructing (DESCEND) arm: abs passes through, walk is re-established. -/

/-- The DESCEND move re-bases `off → off + 1` (the target stays fixed, `H` unchanged).  The
    window-absolute `abs` is supplied VERBATIM by `g.abs`; the walking-keyed `walk` is NOT — the
    descended obligation `off + 1 + 2 ≤ H` is strictly stronger than the parent's `off + 2 ≤ H`, so it
    must be RE-ESTABLISHED from a fresh fact (`h_room`, the arm's own transport input). -/
theorem descend (a b off H : Nat) (g : Guard a b off H) (h_room : off + 3 ≤ H) :
    Guard a b (off + 1) H :=
  { abs := g.abs           -- window-absolute: pass-through, costs nothing
    walk := by omega }      -- walking-keyed: re-established (needs h_room; g.walk alone insufficient)

/-- The READ-ONLY (LEAF) arm: it projects a field and returns the deliverable, never constructing a
    guard — so adding ANY field leaves it untouched.  (`abs` here stands for the returned `Q`.) -/
theorem read (a b off H : Nat) (g : Guard a b off H) : a ≤ b := g.abs

/-- The parent walking field does NOT imply the descended one — a separating witness, so a verbatim
    `walk := g.walk` pass-through cannot typecheck.  At `off = 0, H = 2` the parent `walk` (`off+2 ≤ H`)
    holds yet the descended `walk` (`off+3 ≤ H`) fails. -/
theorem walk_not_passed_through : ∃ off H : Nat, (off + 2 ≤ H) ∧ ¬ (off + 3 ≤ H) :=
  ⟨0, 2, by omega, by omega⟩

/-! ## NEGATIVE / POSITIVE witnesses, concretely (`#guard`-backed). -/

-- The separating witness `off = 0, H = 2`: parent `walk` holds, descended `walk` fails —
-- re-establishment is mandatory, `g.walk` alone is insufficient.
#guard decide (0 + 2 ≤ 2) && !(decide (0 + 3 ≤ 2))
-- With one more unit of room (`h_room : off+3 ≤ H`, here `H = 3`) the descended `walk` is recovered.
#guard decide (0 + 3 ≤ 3)
-- The window-absolute field has no such gap: `a ≤ b` is the SAME proposition at every walking origin,
-- so it passes through verbatim (witness: holds at `a = 1, b = 4` regardless of `off`/`H`).
#guard decide (1 ≤ 4)

end Tests.Reflections.AdditiveFieldCostByKeying
