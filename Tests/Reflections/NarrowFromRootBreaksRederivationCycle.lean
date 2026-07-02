/-!
# Reflection 318 — re-deriving a subset-restriction carrier per recursion-window is CIRCULAR; seed it once at the root from the FLAT producer and narrow down

Self-contained (core Lean) toy of the seq carrier root seed `seqRoot_seqInteriorSeparators` and the
de-risk that corrected R317.

The real situation: the seq `windowWidth_strongRecOn` step at each window `[lo,hi)` needs the
separator carrier `SeqInteriorSeparators tokens lo hi` (it supplies the `bodySucc`/`noTrailingSep`
facts `flowBodyContent_of_deep` cannot project).  R317 planned to RE-DERIVE the carrier per window
via a dispatcher needing that window's own `SafeBodyUnit` — but at a descended window the only
`SafeBodyUnit` source is `RecSeqBody.toSafeBodyUnit` of that window's own `RecSeqBody`, which is the
very output the step is PRODUCING.  Circular.

The fix: the carrier is a SUBSET RESTRICTION (`SeqInteriorSeparators_narrow`), so establish it ONCE
at the root from the FLAT (non-recursive) producer `seqRoot_safeBodyUnit` and narrow to every
sub-window.  The flat root producer does not depend on the recursion, so it breaks the cycle; the
per-window helper (`RecSeqBody.toSafeBodyUnit`, the circular edge) is then DROPPED as unneeded.

This file proves the transferable nugget (the narrow edge + narrow-from-root) and EXHIBITS the cycle
computationally: the flat-seeded recursion carries genuine per-window data, while the
re-derive-from-output recursion is window-BLIND (it injects no real data — the cycle's only base is a
default).
-/

namespace Tests.Reflections.NarrowFromRootBreaksRederivationCycle

set_option autoImplicit false

-- ════════════════════ The PROVEN nugget — subset restriction + narrow-from-root ════════════════
-- A toy window-absolute fact and the carrier that quantifies it over every sub-window of `[lo,hi)`.
def Q (a b : Nat) : Prop := a ≤ b

/-- The carrier: `Q` on every sub-window.  Its body is `lo`/`hi`-free except via the domain bounds —
    exactly the shape of `SeqInteriorSeparators` — so it RESTRICTS to sub-windows. -/
def C (lo hi : Nat) : Prop := ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → Q a b

/-- **The narrow edge (subset restriction).**  The toy of `SeqInteriorSeparators_narrow`: the
    quantifier body is reused verbatim, only the domain shrinks — a two-`Nat.le_trans` proof. -/
theorem C_narrow {lo hi lo' hi' : Nat} (h1 : lo ≤ lo') (h2 : hi' ≤ hi) (h : C lo hi) : C lo' hi' :=
  fun a b ha hab hb => h a b (Nat.le_trans h1 ha) hab (Nat.le_trans hb h2)

/-- **Narrow-from-root.**  The toy of "establish once at the root `[0,N]`, narrow to every
    sub-window": one root instance covers every `[lo,hi)` with `hi ≤ N`. -/
theorem C_all_of_root {N : Nat} (h : C 0 N) : ∀ lo hi, hi ≤ N → C lo hi :=
  fun _lo _hi hN => C_narrow (Nat.zero_le _) hN h

/-- **The FLAT root seed** — established DIRECTLY, with NO recursion (here `Q a b = a ≤ b` is
    immediate from the window hypothesis).  This independence is what breaks the cycle: the toy of
    `seqRoot_safeBodyUnit` feeding the dispatcher at the root. -/
theorem flat_root (N : Nat) : C 0 N := fun _a _b _ hab _ => hab

-- ════════════════════ POSITIVE — narrow-from-root covers every sub-window ═══════════════════════
-- The root seed at `[0,5]` covers a nested sub-window `[2,4)` for free (the de-risk coverage claim:
-- the window lies WITHIN the root span, so narrow reaches it).
example : C 2 4 := C_all_of_root (flat_root 5) 2 4 (by decide)

-- ════════════════════ The CYCLE, computationally — flat root vs re-derive-from-output ═══════════
-- Model the recursion step as PRODUCING the deliverable value at a window FROM the carrier value
-- there (`P w := step (C w)`): the step READS the carrier, exactly as `recseqentry_window_dispatch`
-- reads `FlowBodyContent`.
def step (cAtW : Nat) : Nat := cAtW + 1

-- The FLAT carrier value: computed directly from the window `w` (no recursion). The acyclic source.
def flatC (w : Nat) : Nat := w

-- POSITIVE path — deliverable from the FLAT carrier: terminates, and carries the genuine per-window
-- value (window-AWARE).
def pFromFlat (w : Nat) : Nat := step (flatC w)
#guard pFromFlat 3 == 4
#guard pFromFlat 7 == 8        -- window-aware: the flat seed injects the real per-window datum

-- The CIRCULAR alternative — re-derive the carrier from the deliverable (`extract`, the toy of
-- `RecSeqBody.toSafeBodyUnit`): `C w := extract (P w)`, but `P w := step (C w)`. The two are mutually
-- defined with NO independent base. Fuel exposes the missing base: the only seed is the fuel-0
-- DEFAULT, never a real value.
def extract (pAtW : Nat) : Nat := pAtW - 1
def pCirc : Nat → Nat → Nat
  | 0,        _ => 0                          -- out of fuel: a default, NOT a genuine base
  | fuel + 1, w => step (extract (pCirc fuel w))   -- C w := extract (P w); P w := step (C w) — the cycle

-- NEGATIVE: the circular re-derivation is window-BLIND — it injects no real data, so it yields the
-- same value regardless of `w` (and never the genuine `pFromFlat` answer), no matter the fuel. Only
-- the flat root seed carries the per-window datum.
#guard pCirc 100 3 == 1
#guard pCirc 100 7 == 1        -- same as for w = 3: the cycle carries NO window information
#guard !(pCirc 100 3 == pFromFlat 3)   -- circular ≠ genuine: re-derivation reconstructs nothing real

end Tests.Reflections.NarrowFromRootBreaksRederivationCycle
