/-!
# Reflection 377 — one position-DELTA discriminator refutes a FAMILY of adjacent boundaries; the
standalone boundary-exclusion brick is the sibling arm's INLINE refutation lifted and made delta-generic

Self-contained core-Lean toy of L4YAML BRICK C-ii (`nestedSeq_recseqentry_locate_cons_boundary`).

A bottom-up locator's recursion dispatch (`move_trichotomy off L a`, pure length `omega`) is exhaustive
only given several `a ≠ <boundary>` preconditions: the post-close cut `a ≠ off + L` (C-ii itself) and
the post-separator cut `a ≠ off + L + 1` (the sibling ADVANCE arm's INLINE `h_ne_boundary`).  BOTH are
refuted by ONE field — `opener`: the token at `a - 1` has delta `+1`.  Any candidate `a = m + 1` whose
token at `m` has delta `≠ 1` dies the SAME way; the two boundaries differ ONLY in that delta
(separator δ = 0, close δ = −1).  So the standalone brick is the sibling's inline refutation LIFTED and
made delta-generic — one proof, the boundary token's delta a parameter.

Tokens are abstracted to a delta stream `d : Nat → Int`; the single-token balance over `[i, i+1)` is
just `d i`, so the "opener at `a - 1`" fact is `d (a - 1) = 1`.

**Probe-outcome nuance.**  C-ii is gated by the same mandatory probe-before-producing as its sibling
C-i ([[DownstreamDeriskRestoresUpstream]], R376), but the two diverged.  C-i's probe KILLED the stated
discriminator (the window-absolute fields could not exclude the empty-seq target → a strengthened field
had to be restored).  C-ii's probe instead CORRECTED the spec's GEOMETRY (the queued spec said `a - 1`
is the separator; it is actually the head entry's CLOSE — the separator sits AT `a`) while CONFIRMING
the discriminator (`opener` still refutes, because the close delta is also `≠ 1`).  A geometric mislabel
is INDEPENDENT of whether the discriminator is sound — probe both.
-/

namespace Tests.Reflections.DeltaGenericBoundaryFamily

set_option autoImplicit false

/-- **The DELTA-GENERIC boundary-exclusion brick (the C-ii core).**  If the target start `a` has an
    OPENER at its predecessor (`d (a - 1) = 1`, δ = +1), then `a` is never ONE PAST any token whose
    delta is `≠ 1`.  ONE proof; the boundary token's delta enters only through `h_tok`. -/
theorem boundary_excluded (d : Nat → Int) (a m : Nat)
    (h_opener : d (a - 1) = 1)
    (h_tok : d m ≠ 1) :
    a ≠ m + 1 := by
  intro h_a
  subst h_a
  have h2 : m + 1 - 1 = m := by omega
  rw [h2] at h_opener
  exact h_tok h_opener

/-! ## POSITIVE — two adjacent boundaries, SAME brick, only the delta differs. -/

-- A concrete window tail: the head entry's CLOSE `]` at index 5 (δ = −1), the SEPARATOR `,` at index 6
-- (δ = 0).  In locator coordinates the close sits at `off + L - 1 = 5`, so `off + L = 6` (the
-- post-close cut, = the separator index) and `off + L + 1 = 7` (the post-separator cut).
def dW : Nat → Int := fun i => if i = 5 then -1 else if i = 6 then 0 else 0

/-- The C-ii boundary: `a ≠ off + L` (= 6), refuted by the CLOSE delta (−1). -/
theorem post_close_excluded (a : Nat) (h_op : dW (a - 1) = 1) : a ≠ 6 :=
  boundary_excluded dW a 5 h_op (by decide)

/-- The sibling ADVANCE arm's boundary: `a ≠ off + L + 1` (= 7), refuted by the SEPARATOR delta (0).
    Same `boundary_excluded`, only the delta lemma instance differs. -/
theorem post_separator_excluded (a : Nat) (h_op : dW (a - 1) = 1) : a ≠ 7 :=
  boundary_excluded dW a 6 h_op (by decide)

#guard dW 5 == -1                                    -- close delta
#guard dW 6 == 0                                     -- separator delta
#guard !decide (dW 5 == 1) && !decide (dW 6 == 1)    -- neither is an opener ⇒ both boundaries die

/-! ## Probe-outcome nuance — the spec's GEOMETRY was mislabeled, yet the discriminator stays SOUND. -/

/-- The queued C-ii spec said "at the boundary `a = off + L`, the predecessor `a - 1` is the SEPARATOR".
    The real layout REFUTES that geometry: at `a = 6` (= off + L, the separator INDEX) the predecessor
    `a - 1 = 5` is the CLOSE (δ = −1), and the separator sits AT `a = 6` (δ = 0), not before it. -/
theorem geometry_mislabeled : dW (6 - 1) ≠ 0 ∧ dW 6 = 0 := by
  refine ⟨?_, by decide⟩
  show dW 5 ≠ 0
  decide

/-- …yet the discriminator (`opener`, δ = +1) STILL refutes, because the close's δ = −1 is also `≠ 1`.
    A geometric mislabel is independent of whether the discriminator is sound (contrast C-i, where the
    probe killed the discriminator). -/
theorem discriminator_still_sound (a : Nat) (h_op : dW (a - 1) = 1) : a ≠ 6 :=
  post_close_excluded a h_op

#guard !decide (dW 5 == 1)    -- the discriminator survives the geometry correction

end Tests.Reflections.DeltaGenericBoundaryFamily
