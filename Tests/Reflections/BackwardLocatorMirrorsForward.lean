/-!
# Reflection 309 — a backward locator mirrored from a forward one needs NO standalone backward-matching-open primitive, and its DELIVERABLE is sized to the consumer's reads (drop the floor)

Self-contained (core Lean) toy of the pure-balance backward enclosing-opener locator that landed
`flowBracketBalance_backward_open_locate`.

Tokens are abstracted to a delta stream `d : Nat → Int` (each delta in `{-1, 0, 1}`); `bal d n` is the
running balance from `0` to `n`.  "balance `loS` to `a` = 0" becomes `bal d loS = bal d a`.

**Correction 1 (POSITIVE `backwardLocate`).** The backward locator is proved by `Nat.strongRecOn` on
`a`, casing the last delta `d (a-1)` into opener / neutral / closer.  The closer case does NOT need a
standalone "backward matching-open" primitive (the mirror of a forward matching-close scan): the IH at
`a-1` recovers the closer's own matching opener `p'`, and a one-line `pairSkip` (toy of
`flowBracketBalance_bracket_pair_skip`) jumps the matched block (`bal d a = bal d p'`), after which the
IH at `p'` walks outward.  The recursion structure IS the backward matching-open.

**Correction 2 (NEGATIVE, `#guard`-backed).** The deliverable is `∃ p, p < a ∧ d p = 1 ∧
bal d (p+1) = bal d a` — exactly what the consumer (`Located` / the FROM-LOCATED assembler) reads
(`loS := p+1`, `loS ≤ a`, `bal d loS = bal d a`).  No Dyck FLOOR conclusion is included, even though the
real forward lemma carries a symmetric floor.  The `#guard`s show the floor is strictly MORE than the
consumer needs: on `[ ] [` the pruned existential is satisfied by both the true innermost opener and a
SPURIOUS outer opener whose floor dips negative — the floor would separate them, but the consumer needs
neither innermost-ness nor the floor, only `bal d loS = bal d a`.  Dropping the floor ≈ halves the proof
and loses nothing the assembler consumes.
-/

namespace Tests.Reflections.BackwardLocatorMirrorsForward

set_option autoImplicit false

/-- Running balance from `0` to `n` of a delta stream. -/
def bal (d : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => bal d n + d n

/-- The one-step recurrence (definitional). -/
theorem step (d : Nat → Int) (n : Nat) : bal d (n + 1) = bal d n + d n := rfl

/-! ## POSITIVE — the backward locator: strong induction, closer case via `pairSkip` (no standalone
    backward-matching-open primitive). -/

/-- **The backward enclosing-opener locator** (toy `flowBracketBalance_backward_open_locate`).  If at
    least one bracket is open at `a` (`bal d a ≥ 1`), there is an innermost opener `p < a` with
    `d p = 1` and `bal d (p+1) = bal d a` ("balance `p+1` to `a` = 0").  Deltas are pinned to
    `{-1,0,1}` by `hd`.  The closer case reuses the IH (= the closer's matching opener) + `pairSkip`;
    NO separate backward matching-open lemma is authored. -/
theorem backwardLocate (d : Nat → Int) (hd : ∀ i, -1 ≤ d i ∧ d i ≤ 1) (a : Nat)
    (h : bal d a ≥ 1) : ∃ p, p < a ∧ d p = 1 ∧ bal d (p + 1) = bal d a := by
  revert h
  induction a using Nat.strongRecOn with
  | ind a IH =>
    intro h
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have h0 : bal d 0 = 0 := rfl
      omega
    have hrec : bal d a = bal d (a - 1) + d (a - 1) := by
      have := step d (a - 1); rwa [show a - 1 + 1 = a from by omega] at this
    rcases hd (a - 1) with ⟨hge, hle⟩
    by_cases hd1 : d (a - 1) = 1
    · -- opener: `a - 1` is the innermost opener.
      exact ⟨a - 1, by omega, hd1, by rw [show a - 1 + 1 = a from by omega]⟩
    · by_cases hd0 : d (a - 1) = 0
      · -- neutral: the innermost opener at `a - 1` still encloses `a`.
        have hprev : bal d (a - 1) ≥ 1 := by omega
        obtain ⟨p, hp_lt, hp1, hpb⟩ := IH (a - 1) (by omega) hprev
        exact ⟨p, by omega, hp1, by rw [hpb]; omega⟩
      · -- closer: the IH at `a-1` IS the matching opener; `pairSkip` jumps the block.
        have hneg : d (a - 1) = -1 := by omega
        have hprev : bal d (a - 1) ≥ 1 := by omega
        obtain ⟨p', hp'_lt, hp'1, hp'b⟩ := IH (a - 1) (by omega) hprev
        -- pairSkip: `bal d a = bal d p'` (the matched pair `(p', a-1)` is depth-transparent).
        have hskip : bal d a = bal d p' := by
          rw [step d p', hp'1] at hp'b
          rw [hrec, hneg]; omega
        have hp'pos : bal d p' ≥ 1 := by omega
        obtain ⟨p, hp_lt, hp1, hpb⟩ := IH p' (by omega) hp'pos
        exact ⟨p, by omega, hp1, by rw [hpb, hskip]⟩

/-! ## The consumer reads ONLY `loS ≤ a` and `bal d loS = bal d a` (no floor). -/

/-- The FROM-LOCATED deliverable the assembler consumes (toy `seqEnclosingFacts_provider_of_located`
    inputs): a located body start `loS` with `loS ≤ a` and `bal d loS = bal d a`.  No floor field. -/
structure Located (d : Nat → Int) (a : Nat) where
  loS : Nat
  loS_le : loS ≤ a
  bal0 : bal d loS = bal d a

/-- The locator's PRUNED output assembles a `Located` in one line — the floor is never needed. -/
theorem locatorAssembles (d : Nat → Int) (hd : ∀ i, -1 ≤ d i ∧ d i ≤ 1) (a : Nat)
    (h : bal d a ≥ 1) : Nonempty (Located d a) := by
  obtain ⟨p, hp_lt, _hp1, hpb⟩ := backwardLocate d hd a h
  exact ⟨{ loS := p + 1, loS_le := hp_lt, bal0 := hpb }⟩

/-! ## NEGATIVE — the floor is strictly more than the consumer needs. -/

/-- Concrete deltas for `[ ] [` : index 0 = `+1`, 1 = `-1`, 2 = `+1`. -/
def dd : Nat → Int := fun i => [1, -1, 1].getD i 0

/-- The floor predicate (balance from `loS` never dips below `0` up to `a`) — the conclusion the real
    forward lemma carries and the backward locator DROPS. -/
def floorOK (d : Nat → Int) (loS a : Nat) : Bool :=
  (List.range (a + 1)).all (fun i => if loS ≤ i then decide (bal d i - bal d loS ≥ 0) else true)

-- one bracket is open at a = 3:
#guard bal dd 3 == 1
-- the PRUNED existential `d p = 1 ∧ bal d (p+1) = bal d a` is satisfied by BOTH openers:
#guard dd 2 == 1 && bal dd (2 + 1) == bal dd 3   -- innermost p = 2 (loS = 3)
#guard dd 0 == 1 && bal dd (0 + 1) == bal dd 3   -- SPURIOUS outer p = 0 (loS = 1), both bal = 1
-- the FLOOR separates them — but the consumer reads neither it nor innermost-ness:
#guard floorOK dd 3 3 == true                    -- innermost loS = 3: floor holds
#guard floorOK dd 1 3 == false                   -- spurious loS = 1: balance dips to -1 at i = 2

end Tests.Reflections.BackwardLocatorMirrorsForward
