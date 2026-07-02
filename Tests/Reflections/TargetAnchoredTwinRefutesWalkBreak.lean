/-
Reflection 374 — a "the walk breaks invariant I" refutation must contradict I anchored at the
FIXED TARGET, never the WALKING-keyed copy re-based.  Re-basing fails BY CONSTRUCTION: the structural
feature that fires the refutation is exactly what makes I false at the moved position, so the walking
copy re-based to that position IS the very `¬` the refuter outputs.  Trap: a sibling guard field can
be the SAME predicate yet the wrong ANCHOR, so it LOOKS derivable.

Real instance: `seqPathAllSeq_map_descend_excluded` (R374, BRICK B-i, SeqInteriorSeparators.lean).  The
spine-walk carries `domain : SeqPathAllSeq tokens off` (walking-keyed).  The map-head DESCEND branch is
refuted by `seqPathAllSeq_map_frame_persists tokens off (a-1) : ¬ SeqPathAllSeq tokens (a-1)`.  The
positive `SeqPathAllSeq tokens (a-1)` to contradict it is NOT `domain` re-based (the map between off and
a-1 is exactly what breaks all-seq), but a NEW window-absolute target-anchored twin `h_path`.

Self-contained `Nat`-list toy.  Invariant `AllEven` ("every element even"); a "bad token" `7` (odd)
breaks it — the analogue of a `.flowMappingStart` breaking the all-seq path.  POSITIVE: refute with a
TARGET-anchored hypothesis.  NEGATIVE (commented): try to source the positive by re-basing the WALKING
copy across the bad token — unprovable, and a `#guard` exhibits a state where the walking copy holds but
the target copy is false.
-/

namespace Tests.Reflections.TargetAnchoredTwinRefutesWalkBreak

set_option autoImplicit false

/-- The invariant `I`: every element of the prefix is even (the toy of `SeqPathAllSeq`: "every frame on
    the typed stack is a seq"). -/
def AllEven (l : List Nat) : Prop := l.all (fun n => n % 2 == 0) = true

/-! ## The refuter — the toy of `seqPathAllSeq_map_frame_persists`.

    Appending a "bad" (odd) token breaks `AllEven`: the moved position `l ++ [bad]` falls OUT of the
    invariant.  This is the `¬ I(moved-position)` the refutation consumes. -/
theorem allEven_bad_breaks (l : List Nat) (bad : Nat) (h_bad : (bad % 2 == 0) = false) :
    ¬ AllEven (l ++ [bad]) := by
  intro h
  unfold AllEven at h
  rw [List.all_append] at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  rw [h_bad] at h
  simp at h

/-! ## POSITIVE — refute the vacuous branch via the TARGET-anchored twin.

    The positive `AllEven target` is supplied as a hypothesis (the window-absolute `h_path`), NOT derived
    from the walking copy.  This is exactly `seqPathAllSeq_map_descend_excluded`'s shape. -/
theorem refute_via_target (walk : List Nat) (bad : Nat)
    (h_bad : (bad % 2 == 0) = false)
    (h_target : AllEven (walk ++ [bad])) :     -- the target-anchored twin, true for the real input
    False :=
  allEven_bad_breaks walk bad h_bad h_target

/-! ## NEGATIVE — re-basing the WALKING copy across the bad token cannot source the positive.

    The walking copy `AllEven walk` says nothing about the bad token appended past it; re-basing it to
    the moved position `walk ++ [bad]` is precisely `AllEven (walk ++ [bad])`, which `allEven_bad_breaks`
    refutes.  So the would-be derivation is the refuter's own `¬`-target — unprovable:

    theorem refute_via_walk_BAD (walk : List Nat) (bad : Nat)
        (h_bad : (bad % 2 == 0) = false)
        (h_walk : AllEven walk) :                -- the WALKING copy — same predicate, wrong anchor
        False :=
      allEven_bad_breaks walk bad h_bad (by
        -- GOAL: AllEven (walk ++ [bad]).  `h_walk : AllEven walk` does NOT give this — the appended
        -- `bad` is odd, so the re-based fact is false.  No term inhabits this; the case is genuinely
        -- vacuous only relative to the TARGET twin, never the walking one.
        sorry)
-/

/-! ## Concrete witnesses (`#guard`-backed): the walking copy holds while the target copy is FALSE. -/

-- walk = [2, 4] is all-even (the walking copy holds)…
#guard ([2, 4] : List Nat).all (fun n => n % 2 == 0) == true
-- …yet walk ++ [7] is NOT all-even (the target copy, re-based across the bad token, is false):
-- the walking twin cannot supply the positive the refutation needs.
#guard (([2, 4] ++ [7] : List Nat)).all (fun n => n % 2 == 0) == false
-- 7 is the "bad token" (odd) — the analogue of `.flowMappingStart` breaking the all-seq path.
#guard (7 % 2 == 0) == false

end Tests.Reflections.TargetAnchoredTwinRefutesWalkBreak
