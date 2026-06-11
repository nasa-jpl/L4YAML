/-!
# Reflections 359 & 361 — a recursion's branch ARMS are NOT uniform in difficulty; AUDIT each arm before authoring the skeleton, COMPOSE the landed-brick arms' SEAMS first (each its own green increment), and defer the new-infra arm. A seam is SERIAL (A's output → B's input, R359) or PARALLEL (two independent facts about the same descended state, fused; R361)

Self-contained (core Lean, no `L4YAML` import) toy model of the move found while authoring the
emission-spine-walk wrapper `nestedSeq_recseqentry_locate`.

A `Nat.strongRecOn` recursion dispatches into several arms (LEAF / DESCEND / ADVANCE). The narration
treats the skeleton as "pure plumbing once the bricks land", but the arms are HETEROGENEOUS: LEAF and
ADVANCE are compose-only (backed by landed bricks), while DESCEND hides a sub-case (a map head can't be
descended through and must be REFUTED) that needs infra which does NOT exist. So the full recursion is
not a safe single increment — it stalls on the new-infra arm under the IRON RULE.

The move: COMPOSE the landed bricks of an EASY arm into a single standalone arm-callable. The genuine
NEW content is the inter-brick SEAM — brick A's OUTPUT shape reshaped into brick B's INPUT shape (here
the close-pin window identity `(take H).drop off).take L = ...` reshaped into the leaf brick's prefix
decomposition `body = ... ++ rest` via `List.take_append_drop`). That reshape is unproven slice algebra,
exactly what the recursion's leaf case would otherwise discharge INLINE, tangled with dispatch + measure.
Landing it standalone gets the seam green in isolation; the leaf case becomes a one-line brick call. The
new-infra arm (the DESCEND map-head refutation) becomes the next named increment, sharply isolated.

This toy mirrors the structure faithfully: `producer` (brick A, the close-pin analogue) returns a
take-equality (shape A); `consumer` (brick B, the leaf-brick analogue) wants a prefix DECOMPOSITION
(shape B); `seam` reshapes A→B via `List.take_append_drop` (the new content); `leaf_arm` is the composed
standalone callable. The `hard_arm` is the new-infra arm: classifying a head as seq-vs-map needs an
EXTERNAL witness the compose-only bricks cannot supply, so it stays a HYPOTHESIS — the skeleton's deferred
obligation. The `#guard`s show the composed leaf-arm computes and the seam reshape is the real work; the
negative is that the hard arm cannot be discharged from the producer/consumer data alone.
-/

namespace Tests.Reflections.ComposeArmSeamBeforeSkeleton

set_option autoImplicit false

/-! ## The two LANDED bricks — `producer` (shape A out) and `consumer` (shape B in) -/

/-- **Brick A — the "producer"** (close-pin analogue).  From a located window it returns a
    take-equality in SHAPE A (`ws.take pre.length = pre`) plus a length pin.  This is the close pin's
    `(op :: (interior ++ [cl])) = ((take H).drop off).take L` + `b + 1 = off + L`. -/
theorem producer (ws : List Nat) (k : Nat) (pre : List Nat)
    (h_take : ws.take k = pre) (h_k : k = pre.length) :
    ws.take pre.length = pre ∧ k = pre.length :=
  ⟨h_k ▸ h_take, h_k⟩

/-- **Brick B — the "consumer"** (leaf-brick analogue).  It wants its input in SHAPE B: a prefix
    DECOMPOSITION `ws = pre ++ rest`.  Then the deliverable (`pre` is a prefix of `ws`) falls out. -/
theorem consumer (ws pre rest : List Nat) (h_prefix : ws = pre ++ rest) :
    ∃ r, ws = pre ++ r := ⟨rest, h_prefix⟩

/-! ## The SEAM — the genuine NEW content: reshape A (take-equality) into B (append-decomposition) -/

/-- **The seam** — `nestedSeq_recseqentry_locate_leaf_full`'s intricate core.  Reshapes the producer's
    take-equality (shape A) into the consumer's append decomposition (shape B) via
    `List.take_append_drop` (`rest := ws.drop pre.length`).  This is the close-pin→leaf-brick slice
    algebra, unproven before composing — and what the recursion's leaf case would discharge inline. -/
theorem seam (ws pre : List Nat) (h_take : ws.take pre.length = pre) :
    ws = pre ++ ws.drop pre.length := by
  have hsplit := List.take_append_drop pre.length ws
  rw [h_take] at hsplit
  exact hsplit.symm

/-! ## The COMPOSED leaf arm — one standalone callable, landed BEFORE any skeleton -/

/-- **The composed LEAF arm** — `producer` ▸ `seam` ▸ `consumer`, the single callable the recursion's
    leaf case invokes.  Landed green and standalone, de-risking the seam BEFORE the skeleton threads it
    through `cases`/dispatch/measure.  Mirrors `nestedSeq_recseqentry_locate_leaf_full`. -/
theorem leaf_arm (ws : List Nat) (k : Nat) (pre : List Nat)
    (h_take : ws.take k = pre) (h_k : k = pre.length) :
    ∃ r, ws = pre ++ r := by
  obtain ⟨h_take', _⟩ := producer ws k pre h_take h_k
  exact consumer ws pre (ws.drop pre.length) (seam ws pre h_take')

/-! ## R361 — a seam comes in TWO shapes: the LEAF seam above was SERIAL (A's output → B's input);
    the DESCEND seam is PARALLEL (two bricks each producing an INDEPENDENT fact about the same
    descended state, fused as a conjunction).  Fuse only the NON-mechanical facts; delegate the rest. -/

/-- **Parallel brick 1 — the structural slice invariant** (`nestedSeq_recseqentry_locate_descend`
    analogue, drop-algebra).  Re-bases the descended window one step: `(xs.drop off).drop 1 =
    xs.drop (off+1)`.  Independent of the domain brick. -/
theorem brick_slice (xs : List Nat) (off : Nat) :
    (xs.drop off).drop 1 = xs.drop (off + 1) := by
  rw [List.drop_drop]

/-- **Parallel brick 2 — the stack-fold domain** (`seqPathAllSeq_descend` analogue).  Pushing a `true`
    frame onto an all-`true` stack keeps it all-`true`.  Independent of the slice brick — it reads the
    domain, not the slice. -/
theorem brick_domain (s : List Bool) (h_all : s.all (· == true) = true) :
    (true :: s).all (· == true) = true := by
  rw [List.all_cons, h_all]; rfl

/-- **The composed seq-head DESCEND seam** — `nestedSeq_recseqentry_locate_descend_step` analogue.  A
    PARALLEL fusion: `brick_slice` and `brick_domain` do NOT feed each other; each produces an INDEPENDENT
    fact about the descended state `(off+1, true :: s)`, fused as a conjunction.  The mechanical residue
    (the fit `off+1 ≤ off+1`, a `Nat.le_refl`, the skeleton's own `omega`) is DELEGATED — the seam returns
    ONLY the two non-mechanical facts the skeleton's DESCEND arm cannot reconstruct itself. -/
theorem parallel_seam (xs : List Nat) (off : Nat) (s : List Bool)
    (h_all : s.all (· == true) = true) :
    ((xs.drop off).drop 1 = xs.drop (off + 1)) ∧ (true :: s).all (· == true) = true :=
  ⟨brick_slice xs off, brick_domain s h_all⟩

/-! ## The NEW-INFRA arm — needs an EXTERNAL witness the compose-only bricks cannot supply -/

/-- A head is a seq or a map (the `RecSeqEntry.seq` / `RecSeqEntry.map` dispatch). -/
inductive Head | seq | map
  deriving DecidableEq

/-- **The hard arm** — the DESCEND map-head refutation analogue.  NOT compose-only: classifying the head
    as a seq needs the EXTERNAL fact `h_no_map` (the window's seq-enclosure, a not-yet-existing
    map-frame-persists argument in the real proof), which the producer/consumer/seam data cannot supply.
    So it stays a HYPOTHESIS — the skeleton's deferred obligation, isolated as the next increment. -/
theorem hard_arm (h : Head) (h_no_map : h ≠ Head.map) : h = Head.seq := by
  cases h with
  | seq => rfl
  | map => exact absurd rfl h_no_map

/-! ## The composed leaf-arm computes; the seam reshape is the real work; the hard arm is isolated -/

-- the producer's SHAPE A fact on a concrete witness (`ws = [1,2,3,4]`, `pre = [1,2]`, `k = 2`):
#guard (([1, 2, 3, 4] : List Nat).take 2) == [1, 2]
-- the SEAM reshape — SHAPE A becomes SHAPE B (`ws = pre ++ drop`), the new content:
#guard ([1, 2, 3, 4] : List Nat) == [1, 2] ++ ([1, 2, 3, 4] : List Nat).drop 2
-- ...which is exactly `List.take_append_drop` at the pin point:
#guard ((([1, 2, 3, 4] : List Nat).take 2) ++ (([1, 2, 3, 4] : List Nat).drop 2)) == [1, 2, 3, 4]
-- the NEW-INFRA arm needs an external witness — `seq ≠ map` is decidable but the WITNESS is not
-- recoverable from the producer/consumer data (it is the deferred obligation):
#guard decide (Head.seq ≠ Head.map)
-- R361 PARALLEL seam — the two bricks produce INDEPENDENT facts about the descended state:
-- (1) the slice re-bases (`drop_drop`), (2) the all-`true` domain survives the `true` push:
#guard (([10, 20, 30, 40] : List Nat).drop 1).drop 1 == ([10, 20, 30, 40] : List Nat).drop 2
#guard ((true :: [true, true]).all (· == true)) == true
-- NEGATIVE — a `false` push (a map head) does NOT survive (the domain brick would not fire):
#guard ((false :: [true, true]).all (· == true)) == false

/-! ## Concrete witnesses -/

-- the composed leaf arm applies, producing the deliverable from shape-A inputs:
example : ∃ r, ([1, 2, 3, 4] : List Nat) = [1, 2] ++ r :=
  leaf_arm [1, 2, 3, 4] 2 [1, 2] (by decide) (by decide)
-- the seam reshape stands alone (the genuine new content):
example : ([1, 2, 3, 4] : List Nat) = [1, 2] ++ ([1, 2, 3, 4] : List Nat).drop 2 :=
  seam [1, 2, 3, 4] [1, 2] (by decide)
-- the hard arm fires only WITH the external witness — the deferred obligation:
example : Head.seq = Head.seq := hard_arm Head.seq (by decide)
-- the R361 parallel seam fuses the two independent facts about the descended state:
example : ((([10, 20, 30, 40] : List Nat).drop 1).drop 1 = ([10, 20, 30, 40] : List Nat).drop 2)
    ∧ (true :: [true, true]).all (· == true) = true :=
  parallel_seam [10, 20, 30, 40] 1 [true, true] (by decide)

end Tests.Reflections.ComposeArmSeamBeforeSkeleton
