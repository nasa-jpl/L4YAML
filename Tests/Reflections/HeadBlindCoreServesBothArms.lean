/-
Reflection 373 — when a dispatch splits on a HEAD SHAPE and one shape DELIVERS while the opposite
shape REFUTES, both branches often need the SAME window-internal fact.  That fact is typically already
proven INLINE inside the delivery arm, keyed on the delivery head — but its derivation never READS the
head type (the head only gates WHICH arm fires, not the interior's numeric balance).  Extract it
HEAD-BLIND and both branches consume it: the de-risk's "load-bearing gap" was a fact trapped inline,
closed by EXTRACTION, not by authoring new infra.

Real instance: `recseqentry_head_interior_floor_tokens` (R373, SeqInteriorSeparators.lean).  The
nested-seq locator's DESCEND arm (seq head, `.flowSequenceStart`) delivers; the dispatch's MAP head
(`.flowMappingStart`) whose interior contains the target is VACUOUS, refuted by
`seqPathAllSeq_map_frame_persists` — which needs the map interior's Dyck FLOOR.  That floor is exactly
the seq-DESCEND arm's interior floor.  Its interior slice is recovered by a HEAD-BLIND positional bridge
(`nestedSeq_recseqentry_locate_descend`, needing only the `op :: (interior ++ [cl])` prefix shape, NOT
the opener type), then the balance/floor are type-blind by construction (they count brackets, not types).
So one extraction serves BOTH head shapes.

Self-contained `Nat`-list toy.  POSITIVE: the head-blind interior recovery, reused VERBATIM by a
`0`-headed ("seq", delivery) consumer AND a `1`-headed ("map", refutation) consumer.  NEGATIVE: a
head-SPECIALIZED version pins the head, so the dual branch cannot reuse it (shown commented).
-/

namespace Tests.Reflections.HeadBlindCoreServesBothArms

set_option autoImplicit false

/-! ## POSITIVE — the head-blind core. -/

/-- The head-blind interior recovery: from `body = (op :: (interior ++ [cl])) ++ rest`, the slice
    `(body.drop 1).take interior.length = interior`.  The signature does NOT mention `op`'s value —
    the recovery is keyed on the PREFIX SHAPE alone (the toy of
    `nestedSeq_recseqentry_locate_descend`, whose interior slice reads the layout, not the opener type). -/
theorem interior_slice_headBlind
    (body interior rest : List Nat) (op cl : Nat)
    (h : body = (op :: (interior ++ [cl])) ++ rest) :
    (body.drop 1).take interior.length = interior := by
  subst h
  -- `(op :: X) ++ rest = op :: (X ++ rest)`, so `.drop 1 = (interior ++ [cl]) ++ rest`, and the
  -- `interior`-length prefix of `interior ++ ([cl] ++ rest)` is `interior` (simp's `take`/`append` set).
  simp [List.cons_append, List.append_assoc]

/-! ## POSITIVE — the DELIVERY branch (head = 0, the "seq" shape) reuses the head-blind core. -/

/-- A `0`-headed ("seq") consumer — the DESCEND-delivery analogue — calls the head-blind lemma with
    `op := 0`. -/
theorem deliver_seq (body interior rest : List Nat) (cl : Nat)
    (h : body = (0 :: (interior ++ [cl])) ++ rest) :
    (body.drop 1).take interior.length = interior :=
  interior_slice_headBlind body interior rest 0 cl h

/-! ## POSITIVE — the REFUTATION branch (head = 1, the "map" shape) reuses the SAME core. -/

/-- A `1`-headed ("map") consumer — the dual VACUOUS-refutation analogue — calls the SAME head-blind
    lemma with `op := 1`.  This is the whole point: the opposite head shape gets the identical interior
    fact for free, because the lemma never read the head. -/
theorem refute_map (body interior rest : List Nat) (cl : Nat)
    (h : body = (1 :: (interior ++ [cl])) ++ rest) :
    (body.drop 1).take interior.length = interior :=
  interior_slice_headBlind body interior rest 1 cl h

/-! ## NEGATIVE — a head-SPECIALIZED version traps the fact (shown commented).

    Baking the head into the signature (here `op` pinned to `0`) makes the lemma unusable by the
    `1`-headed dual branch — `refute_map` could not call it, so the gap would look like "needs new
    infra" when in fact the fact is identical and only the spurious head-pin blocks reuse:

    theorem interior_slice_BAD
        (body interior rest : List Nat) (cl : Nat)
        (h : body = (0 :: (interior ++ [cl])) ++ rest) :   -- ← head pinned to 0
        (body.drop 1).take interior.length = interior := by
      subst h; simp [List.cons_append, List.append_assoc]
    -- refute_map (op = 1) CANNOT reuse interior_slice_BAD: the head-type is in the hypothesis shape.
-/

/-! ## Concrete witnesses (`#guard`-backed). -/

-- The interior recovery on a concrete decomposition: body = [9] ++ ([2,3] ++ [7]) ++ [4,5],
-- i.e. op=9, interior=[2,3], cl=7, rest=[4,5].  drop 1 then take 2 = [2,3].
#guard (([9, 2, 3, 7, 4, 5] : List Nat).drop 1).take 2 == [2, 3]
-- Same recovery with a DIFFERENT head (op=1) — the recovery is head-value-independent.
#guard (([1, 2, 3, 7, 4, 5] : List Nat).drop 1).take 2 == [2, 3]
-- The take length IS interior.length (genuine, not an identity): a wrong length over/under-shoots.
#guard (([9, 2, 3, 7, 4, 5] : List Nat).drop 1).take 3 == [2, 3, 7]

end Tests.Reflections.HeadBlindCoreServesBothArms
