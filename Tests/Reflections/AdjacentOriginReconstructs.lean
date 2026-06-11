namespace Tests.Reflections.AdjacentOriginReconstructs

set_option autoImplicit false

/-! ## A type-blind cumulative-balance model (toy of `flowBracketBalance`) -/

/-- Sum of the per-position deltas `δ` over the `n` positions `[lo, lo+n)` — a recursive cumulative
    sum so the single-token STEP unfolds definitionally. -/
def balFrom (δ : Nat → Int) (lo : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => δ lo + balFrom δ (lo + 1) n

/-- Cumulative balance over `[lo, hi)` (toy of `flowBracketBalance tokens lo hi`). -/
def bal (δ : Nat → Int) (lo hi : Nat) : Int := balFrom δ lo (hi - lo)

/-- A segment of all-`0` deltas contributes `0` (used to discharge the concrete interior floor). -/
theorem balFrom_zero (δ : Nat → Int) (lo n : Nat) (h : ∀ k, lo ≤ k → δ k = 0) :
    balFrom δ lo n = 0 := by
  induction n generalizing lo with
  | zero => rfl
  | succ m ih =>
    rw [balFrom, h lo (Nat.le_refl lo), ih (lo + 1) (fun k hk => h k (by omega))]
    omega

/-- **The single-token compose step** — `bal lo i = δ lo + bal (lo+1) i` for `lo < i` (toy of
    `flowBracketBalance_compose` at the adjacent origins `lo`, `lo+1`, the one identity the
    reconstruction folds through). -/
theorem bal_step (δ : Nat → Int) (lo i : Nat) (h : lo < i) :
    bal δ lo i = δ lo + bal δ (lo + 1) i := by
  unfold bal
  have h1 : i - lo = (i - (lo + 1)) + 1 := by omega
  rw [h1]
  rfl

/-! ## POSITIVE — the lower-origin `≥ 1` floor RECONSTRUCTS from the `≥ 0` interior floor + opener pin -/

/-- The guard carries the INTERIOR floor at origin `lo+1` (`≥ 0`) and pins the boundary token's delta
    (`δ lo = 1`, the opener `[`).  The consumer's ENCLOSURE floor at the ADJACENT lower origin `lo`
    (`≥ 1`) is NOT a separate carried field — it reconstructs by `bal_step` across the pinned opener:
    `bal lo i = δ lo + bal (lo+1) i = 1 + (≥ 0) ≥ 1`.  (Toy of `nestedSeq_recseqentry_locate_leaf_typed`
    deriving the LEAF seam's `h_floor` from `SeqTypedInterior`'s interior floor.) -/
theorem floor_lo_from_floor_hi (δ : Nat → Int) (lo hi : Nat)
    (h_open : δ lo = 1)
    (h_floor_hi : ∀ i, lo + 1 ≤ i → i ≤ hi → bal δ (lo + 1) i ≥ 0) :
    ∀ i, lo < i → i ≤ hi → bal δ lo i ≥ 1 := by
  intro i hi1 hi2
  rw [bal_step δ lo i hi1, h_open]
  have h0 : bal δ (lo + 1) i ≥ 0 := h_floor_hi i (by omega) hi2
  omega

-- A concrete window: opener at `lo = 2` (δ = 1), balance-neutral atoms after (δ = 0).
def δopen : Nat → Int := fun k => if k = 2 then 1 else 0

#guard bal δopen 2 3 == 1        -- bal lo (lo+1) reads the opener: ≥ 1
#guard bal δopen 2 5 == 1        -- the whole window stays ≥ 1 (enclosure floor, origin lo = 2)
#guard bal δopen 3 5 == 0        -- the interior is balance-0 at origin lo+1 = 3 (interior floor ≥ 0)

/-- The reconstruction FIRES on the concrete window: the `≥ 1` enclosure floor lands from the interior
    `≥ 0` floor + the opener pin, with NO separate lower-origin field. -/
example : ∀ i, 2 < i → i ≤ 5 → bal δopen 2 i ≥ 1 :=
  floor_lo_from_floor_hi δopen 2 5 (by decide) (by
    intro i _ _
    have hz : bal δopen (2 + 1) i = 0 :=
      balFrom_zero δopen (2 + 1) (i - (2 + 1)) (fun k hk => by
        show (if k = 2 then (1 : Int) else 0) = 0
        rw [if_neg (by omega)])
    rw [hz]; decide)

/-! ## NEGATIVE — the reconstruction is LOAD-BEARING on the boundary-token pin -/

-- WITHOUT the opener pin: a delta-`0` token at `lo` (an atom, not `[`).  The interior floor still holds
-- (`≥ 0`), but the `≥ 1` enclosure floor FAILS — `bal lo (lo+1) = 0`.
def δflat : Nat → Int := fun _ => 0

#guard bal δflat 3 5 == 0        -- interior floor ≥ 0 STILL holds (origin lo+1 = 3)…
#guard bal δflat 2 3 == 0        -- …but bal lo (lo+1) = 0, so the ≥ 1 floor is FALSE.

/-- Without `δ lo = 1`, the lower-origin `≥ 1` floor does NOT hold — even though the interior floor
    does.  So when the boundary token's delta is NOT pinned by the guard (a non-adjacent or unpinned
    origin), the lower-origin fact IS a genuine debt, not a free reconstruction. -/
example : ¬ (∀ i, 2 < i → i ≤ 5 → bal δflat 2 i ≥ 1) := fun h =>
  absurd (h 3 (by decide) (by decide)) (by decide)

end Tests.Reflections.AdjacentOriginReconstructs
