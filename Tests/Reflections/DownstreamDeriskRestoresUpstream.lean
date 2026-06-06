/-!
# Reflection 311 — a downstream consumer's de-risk can FALSIFY a deliberately-narrowed UPSTREAM deliverable: when a minimal pair shows the dropped conjunct is the discriminator AND it is independent of the producer's other outputs, restore it in the PRODUCER, not the consumer

Self-contained (core Lean) toy of the moment a SECOND consumer re-opened the backward
opener locator (`flowBracketBalance_backward_open_locate`) that R309 had sized DOWN.

R309 ([[BackwardLocatorMirrorsForward]]) sized the locator's deliverable to its only consumer
then (the rebase assembler reads only `loS = p+1`, `loS ≤ a`, `bal (p+1) a = 0`) and DROPPED the
Dyck FLOOR, noting it "would separate" spurious from true openers but the consumer did not need it.
R311 is the sequel: the NEXT consumer — the opener-TYPE brick (`seqOpenerType_of_located_and_gate`,
"the located opener is a `[`") — DOES need it, and a minimal pair shows the bare deliverable is
INSUFFICIENT, so the floor must be RESTORED in the producer.

Tokens are abstracted to a delta stream `d : Nat → Int` (each delta in `{-1, 0, 1}`) with an opener
TYPE `ty : Nat → Bool` (meaningful when `d i = 1`: `true` = seq `[`, `false` = map `{`).  `bal d a b`
is the running balance over `[a, b)`, defined by cumulative sums so composition is free.

**Correction 1 (NEGATIVE, `#guard`-backed — the bare existential cannot pin the TYPE).** The toy
of `[{}, ["9"]]`: deltas `[1, 1, -1, 0, 1, 0]` = `[ { } , [ 9`, types `[true, false, _, _, true, _]`.
At the window start `a = 5` BOTH `p = 4` (the true innermost `[`, `ty = true`) AND `p = 1` (a spurious
`{`, `ty = false`, body `} , [` over `[2,5)` nets `-1 + 0 + 1 = 0`) satisfy the locator's three BARE
facts (`p < a`, `d p = 1`, `bal (p+1) a = 0`).  Crucially they DISAGREE on the type, so no consumer
reading only the bare existential can conclude `ty p = true` — the brick is FALSE on the bare
deliverable.  The FLOOR separates them: `bal 5 5 = 0 ≥ 0` for `p = 4`, but `bal 2 3 = -1 < 0` for
`p = 1`.  (This sharpens R309's `[ ] [` pair, where both spurious and true openers had the SAME type;
here they differ, which is exactly why the *type* brick — not the rebase — forces the floor back.)

**Correction 2 (POSITIVE `floor_unique` — the floor pins innermost-ness, hence the type).** Adding
the floor `∀ i ∈ [p+1, a], bal (p+1) i ≥ 0` to the deliverable makes the located opener UNIQUE: any
two floored witnesses `p, q < a` coincide.  Proof is pure balance composition — if `p < q` then
`bal (p+1) (q+1) = bal (p+1) a − bal (q+1) a = 0`, yet `bal (p+1) (q+1) = bal (p+1) q + d q =
bal (p+1) q + 1`, and `p`'s floor gives `bal (p+1) q ≥ 0`, so `0 = (≥0) + 1` — absurd.  Uniqueness
means the gate's innermost type IS `ty p`: the floor is the discriminator, and it is INDEPENDENT of
the three bare facts (the minimal pair satisfies them all yet only `p = 4` is floored), so it cannot
be re-derived at the consume site — it must be DELIVERED by the producer (the locator's construction
is the only source of innermost-ness).  This is the DUAL of R309's size-DOWN: a deliverable is sized
to the UNION of consumers, and a new consumer's de-risk can size it back UP.
-/

namespace Tests.Reflections.DownstreamDeriskRestoresUpstream

set_option autoImplicit false

/-- Cumulative balance: the sum of deltas over `[0, n)`. -/
def cum (d : Nat → Int) : Nat → Int
  | 0     => 0
  | n + 1 => cum d n + d n

/-- The running balance over `[a, b)`, as a difference of cumulative sums — composition for free. -/
def bal (d : Nat → Int) (a b : Nat) : Int := cum d b - cum d a

/-- **Composition is free** (no ordering hypotheses): `bal a c = bal a b + bal b c`. -/
theorem bal_comp (d : Nat → Int) (a b c : Nat) : bal d a c = bal d a b + bal d b c := by
  unfold bal; omega

/-- **One step**: `bal a (a+1) = d a`. -/
theorem bal_single (d : Nat → Int) (a : Nat) : bal d a (a + 1) = d a := by
  have h : cum d (a + 1) = cum d a + d a := rfl
  unfold bal; omega

/-! ## POSITIVE — the floor pins the located opener to a UNIQUE position (hence a unique type). -/

/-- **The floor makes the located opener UNIQUE** (toy of why the R311 floor pins the opener TYPE).
    Two floored witnesses `p, q < a` — each an opener (`d = 1`) whose body reaches `a` at top level
    (`bal (·+1) a = 0`) AND whose interior floor stays `≥ 0` — must coincide.  The proof is the
    balance-composition contradiction; the floor (`hp_floor`/`hq_floor`) is what forbids a second,
    enclosing opener of possibly-different type from also qualifying. -/
theorem floor_unique (d : Nat → Int) (a p q : Nat)
    (hp_lt : p < a) (hq_lt : q < a)
    (hq_d : d q = 1) (hp_d : d p = 1)
    (hp_bal : bal d (p + 1) a = 0) (hq_bal : bal d (q + 1) a = 0)
    (hp_floor : ∀ i, p + 1 ≤ i → i ≤ a → bal d (p + 1) i ≥ 0)
    (hq_floor : ∀ i, q + 1 ≤ i → i ≤ a → bal d (q + 1) i ≥ 0) :
    p = q := by
  rcases Nat.lt_trichotomy p q with h | h | h
  · exfalso
    have h1 : bal d (p + 1) (q + 1) = 0 := by
      have hc := bal_comp d (p + 1) (q + 1) a
      rw [hp_bal, hq_bal] at hc; omega
    have h2 : bal d (p + 1) (q + 1) = bal d (p + 1) q + d q := by
      rw [bal_comp d (p + 1) q (q + 1), bal_single d q]
    have hf := hp_floor q (by omega) (by omega)
    omega
  · exact h
  · exfalso
    have h1 : bal d (q + 1) (p + 1) = 0 := by
      have hc := bal_comp d (q + 1) (p + 1) a
      rw [hp_bal, hq_bal] at hc; omega
    have h2 : bal d (q + 1) (p + 1) = bal d (q + 1) p + d p := by
      rw [bal_comp d (q + 1) p (p + 1), bal_single d p]
    have hf := hq_floor p (by omega) (by omega)
    omega

/-! ## NEGATIVE — the minimal pair: the bare existential admits two openers of DIFFERENT type. -/

/-- Deltas of `[{}, ["9"]]`'s interior: `[ { } , [ 9` = `[1, 1, -1, 0, 1, 0]`. -/
def dList : List Int := [1, 1, -1, 0, 1, 0]
def d (i : Nat) : Int := dList.getD i 0

/-- Opener types: `[` → `true`, `{` → `false` (only meaningful where `d i = 1`: positions 0,1,4). -/
def tyList : List Bool := [true, false, false, false, true, false]
def ty (i : Nat) : Bool := tyList.getD i false

-- the window start is `a = 5` (the body level of the inner `[` at position 4).
-- BOTH candidates satisfy the locator's three BARE facts:
#guard d 4 == 1 && bal d 5 5 == 0          -- p = 4 (true innermost `[`)  ✓ bare
#guard d 1 == 1 && bal d 2 5 == 0          -- p = 1 (spurious `{`)         ✓ bare
-- ... yet they DISAGREE on the opener type, so the bare existential cannot pin `ty p`:
#guard ty 4 == true                        -- the true innermost is a seq `[`
#guard ty 1 == false                       -- the spurious witness is a map `{`
#guard !(ty 1 == ty 4)                     -- the two bare witnesses have DIFFERENT types
-- the FLOOR separates them — restoring it in the producer is what pins the type:
#guard decide (bal d 5 5 ≥ 0)              -- p = 4 floor holds (single point)
#guard bal d 2 3 == -1                     -- p = 1 floor VIOLATED at i = 3 (just past the `}`)
#guard !decide (bal d 2 3 ≥ 0)

end Tests.Reflections.DownstreamDeriskRestoresUpstream
