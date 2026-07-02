/-
# Reflection 537 — a recursion-driver's abstract `locate` hole is the first-entry DISPATCH's richer
existential RE-PACKED; the three bricks are WIRED, no new proof, and the planned "sole surviving brick"
already existed

Self-contained companion to `recbody_locate_seq_carrier`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the SEQ half of the two `locate`
holes the carrier-specialised driver `recbody_joint_navigator_driver_carrier` (R534) takes as inputs.

The point this file isolates — **a width-recursion driver leaves an abstract per-window `locate` hole
whose deliverable is a LEAN existential (located boundary `m` + balance + marker + the sub-block
deliverable).  The concrete first-entry DISPATCH that fills it returns a RICHER existential over the SAME
witness — it additionally carries an interior-MINIMALITY conjunct the driver never reads, and orders the
balance/marker conjuncts the other way.  Filling the hole is therefore pure WIRING capped by a RE-PACK:
feed the dispatch its content source and its induction hypothesis, then destructure its rich existential,
DROP the surplus conjunct, and re-tuple into the hole's order.**  No new lemma is proved at the hole.

Two findings the real brick embodies:

1. **The "sole surviving brick" was already landed.**  The plan named a per-window non-deep content
   source (the guard carries only the DEEP content) as the last missing piece.  It turned out a sibling
   lemma already produced exactly it from the threaded root carrier narrowed to the window — so the
   residual was an IMPORT, not a derivation.  GREP the named brick before building it.

2. **The hole is the dispatch RE-PACKED.**  A first-entry dispatch's deliverable is strictly RICHER than
   a recursion driver's `locate` hole (it pins the located boundary's minimality for ITS own induction;
   the driver only needs the boundary + balance + sub-block).  Destructure, drop the surplus, reorder —
   the witness flows straight through.

What this file does:
* `DispatchOut` — the toy of `recseqentry_window_dispatch_seq`'s 6-conjunct deliverable (bounds, balance,
  marker, a surplus MINIMALITY conjunct, the sub-block), an existential over the located `m`.
* `LocateHole` — the toy of the driver's `locate_seq` hole: the SAME existential MINUS minimality, with
  balance/marker SWAPPED — strictly leaner.
* `holeOfDispatch` — the RE-PACK (the audited move): destructure the rich existential, drop minimality,
  re-tuple into the hole's order.
* `locateOfBricks` — the full WIRING: the three abstract bricks (`contentSource` = the already-landed
  per-window content source, `ihAdapter` = the joint-oracle→axis-IH adapter R535/R536, `dispatch` = the
  first-entry dispatch) composed and capped by `holeOfDispatch` — the shape of `recbody_locate_seq_carrier`.
* toy instances RUN `locateOfBricks` end-to-end to a closed `LocateHole` value.
-/

namespace LocateHoleIsDispatchRepacked

set_option autoImplicit false

/-! ## The two existentials — the dispatch's RICH deliverable vs the driver's LEAN hole. -/

/-- Toy of `recseqentry_window_dispatch_seq`'s deliverable: an existential over the located boundary `m`
    with SIX conjuncts — `lo < m`, `m ≤ hi`, the depth-`0` balance, the marker disjunct, an interior
    MINIMALITY clause (no earlier boundary), and the sub-block deliverable.  The minimality conjunct is
    what the dispatch needs for ITS own first-entry induction and the driver does NOT read. -/
def DispatchOut (lo hi : Nat) (Bal Marker Min Entry : Nat → Prop) : Prop :=
  ∃ m, lo < m ∧ m ≤ hi ∧ Bal m ∧ Marker m ∧ Min m ∧ Entry m

/-- Toy of the driver's `locate_seq` hole: the SAME existential, but LEANER — the minimality conjunct is
    dropped and balance/marker are in the opposite order.  This is exactly the gap between
    `recseqentry_window_dispatch_seq`'s output and `recbody_joint_navigator_driver_carrier`'s `locate`
    argument. -/
def LocateHole (lo hi : Nat) (Bal Marker Entry : Nat → Prop) : Prop :=
  ∃ m, lo < m ∧ m ≤ hi ∧ Marker m ∧ Bal m ∧ Entry m

/-! ## The re-pack — drop the surplus conjunct, reorder, re-tuple. -/

/-- **The RE-PACK (the audited move).**  The dispatch's richer existential projects to the driver's
    leaner hole over the SAME witness `m`: destructure all six conjuncts, discard the minimality one
    (`_h_min`), and re-tuple with marker before balance.  No reasoning — pure structural re-projection,
    so it depends on no axioms.  In the real brick this is the closing
    `exact ⟨m, h_lo_m, h_m_hi, h_marker, h_bal_m, h_entry⟩`. -/
theorem holeOfDispatch {lo hi : Nat} {Bal Marker Min Entry : Nat → Prop}
    (d : DispatchOut lo hi Bal Marker Min Entry) : LocateHole lo hi Bal Marker Entry := by
  obtain ⟨m, h_lo, h_hi, h_bal, h_mark, _h_min, h_entry⟩ := d
  exact ⟨m, h_lo, h_hi, h_mark, h_bal, h_entry⟩

/-! ## The full wiring — three landed bricks, capped by the re-pack. -/

/-- **The `locate` as pure WIRING.**  The three bricks are abstract here, faithful to the real shapes'
    SKELETON: `contentSource` produces the per-window content from the carrier (the already-landed brick,
    `seqWindow_flowBodyContent_seq_general`); `ihAdapter` produces the axis-only induction hypothesis
    from the joint oracle (R535/R536, `recbody_joint_oracle_seq_ih`); `dispatch` is the first-entry
    dispatch consuming both and returning the RICH existential (R527).  The `locate` is their
    composition, capped by `holeOfDispatch` — NO new obligation is discharged at the hole.  This is the
    shape of `recbody_locate_seq_carrier`. -/
theorem locateOfBricks {lo hi : Nat}
    {Carrier Win Oracle Content IH : Prop} {Bal Marker Min Entry : Nat → Prop}
    (contentSource : Carrier → Win → Content)
    (ihAdapter : Oracle → IH)
    (dispatch : Win → Content → IH → DispatchOut lo hi Bal Marker Min Entry)
    (h_carrier : Carrier) (h_win : Win) (h_oracle : Oracle) :
    LocateHole lo hi Bal Marker Entry :=
  holeOfDispatch (dispatch h_win (contentSource h_carrier h_win) (ihAdapter h_oracle))

/-! ## Toy instances: the wiring RUNS end-to-end. -/

/-- Toy per-window predicates over the located witness `m`, kept DISTINCT so the re-pack's reorder is
    visible (balance and marker are not the same proposition). -/
def Bal0 (m : Nat) : Prop := m = m
def Marker0 (m : Nat) : Prop := m = 5 ∨ True
def Min0 (_ : Nat) : Prop := True
def Entry0 (m : Nat) : Prop := m ≤ 5

/-- The three bricks at toy types (each `True`), and the dispatch returning the rich existential at the
    boundary `m = 5` of the window `[0, 5)`. -/
def toyContent : True → True → True := fun _ _ => trivial
def toyIh : True → True := fun _ => trivial
def toyDispatch : True → True → True → DispatchOut 0 5 Bal0 Marker0 Min0 Entry0 :=
  fun _ _ _ => ⟨5, Nat.zero_lt_succ _, Nat.le_refl 5, rfl, Or.inl rfl, trivial, Nat.le_refl 5⟩

/-- The wiring RUN: feed the three toy bricks to `locateOfBricks`, obtaining the leaner `LocateHole`
    end-to-end.  Elaborates to a closed value — the dispatch's rich output really does re-pack into the
    driver's hole. -/
example : LocateHole 0 5 Bal0 Marker0 Entry0 :=
  locateOfBricks toyContent toyIh toyDispatch trivial trivial trivial

/-- The re-pack in isolation also runs: hand `holeOfDispatch` the rich existential directly. -/
example : LocateHole 0 5 Bal0 Marker0 Entry0 :=
  holeOfDispatch (toyDispatch trivial trivial trivial)

end LocateHoleIsDispatchRepacked

/-- info: 'LocateHoleIsDispatchRepacked.holeOfDispatch' does not depend on any axioms -/
#guard_msgs in
#print axioms LocateHoleIsDispatchRepacked.holeOfDispatch

/-- info: 'LocateHoleIsDispatchRepacked.locateOfBricks' does not depend on any axioms -/
#guard_msgs in
#print axioms LocateHoleIsDispatchRepacked.locateOfBricks
