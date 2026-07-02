/-!
# Reflection 360 — a flagged "needs-new-infra" REFUTATION arm is often a PINNING sibling's MIRROR: flip the type-discriminator bit, relax the pin-hypothesis to a floor

Self-contained (core Lean, no `L4YAML` import) toy model of the move found while authoring the
DESCEND map-head refutation `seqPathAllSeq_map_frame_persists` that the R359 arm-audit had deferred
as "needs new infra".

It was NOT new infra. The lemma is a near-twin of an EXISTING sibling, `seqOpenerType_of_located_and_gate`,
which PINS the located opener's type (`tokens[p] = .flowSequenceStart`, the head is a seq `[`). Both read
the SAME substrate `btFold_frame_inv` (a floored fold from a base whose bottom frame is `bit :: base`
returns `m ++ (bit :: base)` — the bottom frame survives). The refutation is the sibling's MIRROR with two
parametric edits:
  1. FLIP the type-discriminator bit: the sibling pins the pushed bit to `true` (a `[`); the refutation
     reads the same decomposition with the bit `false` (a `{`) and concludes the OPPOSITE membership —
     a `false` survives, so the stack is not all-`true`.
  2. RELAX the pin-hypothesis: pinning needs the EXACT body balance (forces the surviving prefix `m = []`,
     so the head is read directly); refuting needs only the FLOOR (the frame is never popped; `m` may be
     nonempty, sitting harmlessly above the surviving `false`). So the refutation DROPS the sibling's
     tightest hypothesis.

This toy mirrors the structure faithfully: `FrameInv` is the shared substrate (the `S = m ++ (bit :: base)`
decomposition `btFold_frame_inv` delivers); `pin` is the sibling (bit `true` + the exact-balance witness
`m = []` ⟹ head pinned to `true`); `refute` is the mirror (bit `false`, NO exact hypothesis ⟹ a surviving
`false` ⟹ not all-`true`). The `#guard`s show the pin's all-`true` stack, the mirror's surviving `false`,
and the NEGATIVE: without the frame surviving (an empty stack — the floor violated, the frame popped) the
refutation's conclusion fails (`[].all = true`), so the floor is load-bearing.
-/

namespace Tests.Reflections.RefuteArmMirrorsPinningSibling

set_option autoImplicit false

/-! ## The SHARED SUBSTRATE — a frame-inverse decomposition (`btFold_frame_inv` analogue) -/

/-- **The shared substrate.**  A floored fold over an interior, started from a base stack whose bottom
    frame is `bit :: base`, returns a stack of the form `m ++ (bit :: base)`: the bottom frame SURVIVES
    (the floor never pops it), `m` is the surviving prefix above it.  This is exactly what
    `btFold_frame_inv` delivers; BOTH the pinning sibling and the refuting mirror read it. -/
def FrameInv (S : List Bool) (bit : Bool) (base : List Bool) : Prop :=
  ∃ m, S = m ++ (bit :: base)

/-! ## The PINNING sibling — `seqOpenerType_of_located_and_gate` analogue -/

/-- **The pinning sibling.**  With the pushed bit `true` (a seq `[`) AND the EXACT-balance witness that
    the surviving prefix is empty (`m = []` — the sibling's `flowBracketBalance = 0` forcing the head),
    the stack head is pinned to `true`.  This is the EXACT-hypothesis consumer of `FrameInv`. -/
theorem pin (S base : List Bool) (h : FrameInv S true base)
    (h_exact : ∀ m, S = m ++ (true :: base) → m = []) :
    S.head? = some true := by
  obtain ⟨m, hm⟩ := h
  rw [h_exact m hm, List.nil_append] at hm
  rw [hm]; rfl

/-! ## The REFUTING mirror — `seqPathAllSeq_map_frame_persists` analogue -/

/-- **The refuting mirror.**  SAME substrate `FrameInv`, but (1) the bit is FLIPPED to `false` (a map `{`)
    and (2) the exact-balance hypothesis is DROPPED — only the floor remains, so the surviving prefix `m`
    may be nonempty.  The surviving `false` makes the stack not all-`true`.  Refuting needs strictly LESS
    than pinning: no `m = []`, just the frame's survival. -/
theorem refute (S base : List Bool) (h : FrameInv S false base) :
    (S.all (· == true)) = false := by
  obtain ⟨m, hm⟩ := h
  rw [hm, List.all_append]
  simp [List.all_cons]

/-! ## The pin pins; the mirror refutes (with a nonempty `m`); the floor is load-bearing -/

-- the PIN's stack (`m = []`, bit `true`) is all-`true`, head pinned:
#guard (([true] : List Bool).all (· == true)) == true
#guard ([true] : List Bool).head? == some true
-- the MIRROR's stack carries a surviving `false` even with a NONEMPTY prefix `m = [true, true]`
-- (`S = [true,true] ++ (false :: []) = [true,true,false]`) — relaxing the pin loses nothing:
#guard (([true, true, false] : List Bool).all (· == true)) == false
-- NEGATIVE — the floor is load-bearing: if the frame were POPPED (an empty stack, floor violated), the
-- refutation's conclusion FAILS (`[].all = true`), so the surviving frame (FrameInv) is essential:
#guard (([] : List Bool).all (· == true)) == true

/-! ## Concrete witnesses -/

-- the pinning sibling fires WITH the exact-balance witness `m = []`:
example : ([true] : List Bool).head? = some true :=
  pin [true] [] ⟨[], rfl⟩ (fun m hm => by
    cases m with
    | nil => rfl
    | cons a t => simp at hm)
-- the refuting mirror fires WITHOUT any exact hypothesis — only the flipped bit + a surviving frame,
-- here with a NONEMPTY surviving prefix `m = [true, true]`:
example : (([true, true, false] : List Bool).all (· == true)) = false :=
  refute [true, true, false] [] ⟨[true, true], rfl⟩

end Tests.Reflections.RefuteArmMirrorsPinningSibling
