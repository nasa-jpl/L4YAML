/-!
# Reflection 475 — a width-gated IH over an inner CONTAINED frame is dischargeable from the
# OUTER joint width IH, and the per-step ASSEMBLE that does it ISOLATES the locator while
# SIDESTEPPING the SafeBodyUnit ↔ carrier ↔ recursion circularity.

Self-contained (core Lean, no `L4YAML` import) toy recording the brick R475 landed:
`seqWidthEnc_of_enclosingLocate_and_recIH`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the per-step ASSEMBLE the
eventual body-width joint induction invokes to discharge `seqLocalCarrier_of_widthEnc`'s `h_widthEnc`
hypothesis at one body window `[lo, hi)`.

**The shape of the problem.**  `h_widthEnc`'s deliverable, for each gated window `[a, b)` whose
enclosing opener is `p`, is the ENCLOSING-WINDOW facts of a frame `[p, hiE)` PLUS a width-gated
`RecSeqBody` IH for the sub-windows of THAT frame — gated by the FRAME width `hi' - lo' < hiE - p`.
The joint induction's own IH, by contrast, is gated by the BODY width `hi' - lo' < hi - lo`.  The two
gates differ, so the inner IH is not literally the outer IH — yet it is dischargeable from it.

**The bridge — frame containment.**  The locator delivers the frame INSIDE the body: `lo ≤ p` and
`hiE ≤ hi`.  Those two containments give `hiE - p ≤ hi - lo`, so the inner gate IMPLIES the outer one
(`hi' - lo' < hiE - p ≤ hi - lo`).  The same two containments lift the inner quantifier's bounds
`p ≤ lo'` / `hi' ≤ hiE` to the outer IH's `lo ≤ lo'` / `hi' ≤ hi`.  All three obligations are pure
`omega` from the four facts `{h_width, lo ≤ p, hiE ≤ hi, p ≤ lo', hi' ≤ hiE}`.  So the per-step
assemble is: obtain the contained frame from the locator, then discharge the inner IH by `recIH` under
the three `omega` bridges.

**Why this is the RIGHT half to land first.**  The full joint induction must also build, at each
window, the `SafeBodyUnit` the carrier needs — and that is circular (carrier needs `SafeBodyUnit`,
`SafeBodyUnit` comes from `RecSeqBody.toSafeBodyUnit`, `RecSeqBody` needs the carrier), broken only by
the width well-ordering.  This assemble touches NONE of that: it composes the locator and the recursion
IH into the `h_widthEnc` shape, proving the width arithmetic and isolating the LOCATOR as the single
residual.  Carrier construction (which needs the `SafeBodyUnit`) is the SEPARATE
`seqLocalCarrier_of_widthEnc` step.

This toy reproduces the three reusable facts.
-/

namespace ContainedFrameIHFromOuterIH

set_option autoImplicit false

/-- **The structural heart — an inner-frame width-gated IH FROM the outer body IH.**  `RecBody` stands
    for `RecSeqBody ((take hi').drop lo')`; `WindowFacts` for the bundle
    `FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed ∧ tokens[·] = close`.  Given only the two
    containments `lo ≤ p` and `hiE ≤ hi`, the FRAME-width-gated IH over `[p, hiE)` is discharged by the
    BODY-width-gated IH over `[lo, hi)`: the three `omega`s ARE the width bridge. -/
theorem inner_frame_IH_from_outer_IH
    (RecBody WindowFacts : Nat → Nat → Prop)
    (lo hi p hiE : Nat)
    (h_lo_p : lo ≤ p) (h_hiE_hi : hiE ≤ hi)
    (recIH : ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
        WindowFacts lo' hi' → RecBody lo' hi') :
    ∀ lo' hi', hi' - lo' < hiE - p → p ≤ lo' → hi' ≤ hiE →
        WindowFacts lo' hi' → RecBody lo' hi' := by
  intro lo' hi' h_width h_p_lo' h_hi'_hiE h_wf
  exact recIH lo' hi' (by omega) (by omega) (by omega) h_wf

/-- **The full per-step ASSEMBLE in miniature** — mirrors `seqWidthEnc_of_enclosingLocate_and_recIH`.
    `enclosingLocate` is the LOCATE residual (returns a CONTAINED frame `[p, hiE)` with `lo ≤ p`,
    `hiE ≤ hi`); `recIH` is the joint BODY-width IH.  The assemble produces the `∃`-frame deliverable
    whose inner IH is FRAME-gated, discharged exactly as `inner_frame_IH_from_outer_IH`.  No
    `SafeBodyUnit`/carrier is referenced — this is the half of the joint induction that sidesteps the
    circularity. -/
theorem assemble
    (RecBody WindowFacts Frame : Nat → Nat → Prop)
    (lo hi : Nat)
    (enclosingLocate : ∀ a, lo ≤ a → a ≤ hi →
        ∃ p hiE, lo ≤ p ∧ a ≤ hiE ∧ hiE ≤ hi ∧ Frame p hiE)
    (recIH : ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
        WindowFacts lo' hi' → RecBody lo' hi') :
    ∀ a, lo ≤ a → a ≤ hi →
      ∃ p hiE, a ≤ hiE ∧ Frame p hiE ∧
        (∀ lo' hi', hi' - lo' < hiE - p → p ≤ lo' → hi' ≤ hiE →
          WindowFacts lo' hi' → RecBody lo' hi') := by
  intro a ha hb
  obtain ⟨p, hiE, h_lo_p, h_a_hiE, h_hiE_hi, h_frame⟩ := enclosingLocate a ha hb
  refine ⟨p, hiE, h_a_hiE, h_frame, ?_⟩
  intro lo' hi' h_width h_p_lo' h_hi'_hiE h_wf
  exact recIH lo' hi' (by omega) (by omega) (by omega) h_wf

/-- **The containment is LOAD-BEARING — without it the bridge is FALSE.**  Drop `lo ≤ p` / `hiE ≤ hi`
    and pick a frame WIDER than the body (`hiE - p > hi - lo`): then the inner gate no longer implies
    the outer gate, so `recIH` cannot be applied.  Concretely `lo=0, hi=1, p=0, hiE=10, lo'=0, hi'=5`:
    `5 < 10 - 0` holds but `5 < 1 - 0` does not.  This is why the locator must deliver a CONTAINED
    frame — the two containments are not bookkeeping, they are what makes the descent well-founded. -/
theorem bridge_needs_containment :
    ¬ (∀ lo hi p hiE lo' hi' : Nat,
        hi' - lo' < hiE - p → hi' - lo' < hi - lo) := by
  intro h
  exact absurd (h 0 1 0 10 0 5 (by omega)) (by omega)

/-- CONCRETE, non-vacuous — the assemble runs end-to-end on a contained frame (`p = 0`, `hiE = 10`
    inside the body `[0, 10)`), mirroring the `#guard`-backed satisfiability de-risk of the real
    locator. -/
example :
    ∀ a, (0 : Nat) ≤ a → a ≤ 10 →
      ∃ p hiE, a ≤ hiE ∧ True ∧
        (∀ lo' hi', hi' - lo' < hiE - p → p ≤ lo' → hi' ≤ hiE → True → True) :=
  assemble (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) 0 10
    (fun a _ hb => ⟨0, 10, by omega, hb, Nat.le_refl 10, trivial⟩)
    (fun _ _ _ _ _ _ => trivial)

end ContainedFrameIHFromOuterIH
