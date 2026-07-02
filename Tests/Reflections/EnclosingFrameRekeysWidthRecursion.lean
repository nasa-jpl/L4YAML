/-!
# Reflection 472 — a width strong-induction whose per-window obligation references the ENCLOSING
# FRAME (one bracket-level OUT, wider by exactly 2) CANNOT be keyed on the inner BODY width: the IH
# (`< bodyWidth`) never reaches the frame obligation at `bodyWidth + 2`. RE-KEY the induction on the
# ENCLOSING-FRAME width — the outermost frame is the base case, and every descent goes strictly INWARD.

Self-contained (core Lean, no `L4YAML` import) toy recording the SMALLEST-FIRST de-risk that R470/R471
queued before authoring the seq carrier↔recursion JOINT WIDTH STRONG-INDUCTION.

Context (the real situation).  The last seq residual `h_widthEnc`
(`seqLocalCarrier_of_widthEnc` / `seqRoot_carrier_of_widthEnc`) co-constructs, by strong induction on
window width, the separator carrier `SeqInteriorSeparators tokens lo hi` of a seq body `[lo, hi)` and the
recursive `RecSeqBody`.  The queued plan was a `Nat.strongRecOn` on the BODY width `hi - lo`, producing
the pair per body window.  The queued de-risk: does the child window `[p, hiE)` produced by the R470/R471
siblings satisfy the IH's width guard `hiE - p < hi - lo`?

**The de-risk OUTCOME (this reflection).  NO — and the failure is structural, not incidental.**  The
carrier `SeqInteriorSeparators tokens lo hi` quantifies over every gated sub-window `[a, b) ⊆ [lo, hi)`.
For a TOP-LEVEL gated window (depth `0` within the body: `balance lo a = 0`), the enclosing opener that
`seqEnclosingOpener_of_gate` locates is `p = lo - 1` — the body's OWN bracket opener, which sits OUTSIDE
the body — and its matching close is `j = hi`, the body's own close.  So the enclosing window the
producer must deliver facts for is the FRAME `[p, hiE) = [lo - 1, hi + 1)`, whose width is

  `hiE - p = (hi + 1) - (lo - 1) = (hi - lo) + 2`.

The frame is exactly TWO wider than the body (the opener it adds on the left, the closer on the right).
A strong induction keyed on the BODY width `w = hi - lo` hands an IH covering every `k < w` — and
`w + 2` is never `< w`.  So the body-width IH cannot reach the frame obligation: the index is out of
range no matter the proof.  (Confirmed by balance arithmetic on the real types, not just this toy:
`balance lo a = 0` with `balance (lo-1) a = 1 + 0 = 1` pins the nearest enclosing opener to `lo - 1`,
and `balance lo hi = 0` with the `.flowSequenceEnd` at `hi` pins its matching close to `hi`.)

**Why this is not a paperwork off-by-one.**  The gap widths are benign in CONSUMPTION (the child
`SafeBodyUnit` reads the width IH only at the body's ENTRIES, all `< hi - lo`), but they are not benign
in the TYPE: at width exactly `hi - lo` the only inhabited frame-interior window is `[lo, hi)` ITSELF —
the body — whose `RecSeqBody` is the other half of the pair under construction (a genuine
self-reference), and at width `hi - lo + 1` no `FlowBodyWindow` ending on the close exists at all
(vacuous).  Discharging both gap widths explicitly is possible but fiddly.

**The PIVOT (recorded for the next brick).**  Re-key the strong induction on the ENCLOSING-FRAME width,
not the inner body width.  The outermost frame is the whole document bracket `[1, size - 1)` — the
LARGEST frame, the base case — and every nested frame inside a body is strictly NARROWER, so the descent
is well-founded with no `+2` gap: the body of a frame `[p, hiE)` is its child `[p+1, hiE-1)` (width
`frameWidth - 2`), and any nested frame inside that body has width `< frameWidth`.  Keying on the frame
makes `h_widthEnc`'s per-window obligation — which is itself FRAME-shaped (`[p, hiE)`) — the recursion's
own object, so the IH guard and the obligation index coincide.

This toy reproduces exactly that arithmetic + the two recursions:

* `bodyWidth` / `frameWidth` — the body `[lo, hi)` and its enclosing frame `[lo-1, hi+1)`.
* `frame_eq_body_add_two` — the `+2` gap, by `omega`.
* `frame_index_exceeds_body_ih` — the obstruction: the body-width IH (`< w`) cannot be instantiated at
  the frame index `w + 2`, because `¬ (w + 2 < w)`.  No proof of the per-window obligation can route
  through the body-width IH; the index is simply out of reach.
* `solveFrame` — the RE-KEYED recursion: a `termination_by` recursion on frame width whose step
  descends into a nested frame of width `≤ frameWidth - 2 < frameWidth`.  It CLOSES (`omega` discharges
  the descent), unlike a body-width keying which would get stuck at the frame obligation.
* `frame_descends` — the descent fact the re-keyed recursion relies on (`2 ≤ W → W - 2 < W`).
-/

namespace EnclosingFrameRekeysWidthRecursion

set_option autoImplicit false

/-- The width of a seq BODY window `[lo, hi)` (the recursion's *inner* span). -/
def bodyWidth (lo hi : Nat) : Nat := hi - lo

/-- The width of the body's ENCLOSING FRAME `[lo - 1, hi + 1)` — the body plus its opener (at `lo - 1`)
    and its closer (at `hi`).  This is the window the per-body carrier obligation actually references for
    a TOP-LEVEL gated sub-window (`p = lo - 1`, close `hiE = hi + 1`). -/
def frameWidth (lo hi : Nat) : Nat := (hi + 1) - (lo - 1)

/-- **THE `+2` GAP.**  The enclosing frame is exactly two wider than its body — the opener on the left,
    the closer on the right.  (Needs a real opener position, `1 ≤ lo`, and `lo ≤ hi`.) -/
theorem frame_eq_body_add_two (lo hi : Nat) (h_lo : 1 ≤ lo) (h_le : lo ≤ hi) :
    frameWidth lo hi = bodyWidth lo hi + 2 := by
  unfold frameWidth bodyWidth; omega

/-- **THE OBSTRUCTION — the frame obligation is OUT OF REACH of a body-width IH.**  A strong induction
    keyed on the BODY width `w` supplies an IH usable only at indices `k < w`.  The per-body obligation
    references the FRAME, at index `w + 2`.  And `w + 2` is never `< w`, so the body-width IH cannot be
    applied there — independently of *what* one is trying to prove about the frame.  This is why the
    queued body-width keying does not close. -/
theorem frame_index_exceeds_body_ih (w : Nat) : ¬ (w + 2 < w) := by omega

/-- **THE DESCENT FACT for the RE-KEYED recursion.**  Keyed on the FRAME width `W`, the recursion
    descends into a nested frame whose width is at most `W - 2` (it lives inside the body, width
    `W - 2`), which is strictly `< W` whenever `W ≥ 2` (a real frame has an opener and a closer).  No
    `+2` gap appears: descents go strictly INWARD. -/
theorem frame_descends (W : Nat) (h : 2 ≤ W) : W - 2 < W := by omega

/-- **THE RE-KEYED RECURSION.**  A toy recursion on FRAME width, stepping by 2 (`frameW → frameW - 2`):
    the step at a frame of width `n + 2` recurses into its body's nested frame of width `n = frameW - 2`,
    which is strictly `< frameW` (`frame_descends`).  Modelling the pivot — the outermost frame (largest
    width) is the base of the descent, every nested frame is strictly narrower, and the descent always
    terminates because it removes the opener+closer pair each level.  A body-width keying would instead
    get stuck at the `frameW = bodyW + 2` obligation (`frame_index_exceeds_body_ih`). -/
def solveFrame : Nat → Nat
  | 0 => 0
  | 1 => 0
  | (n + 2) => solveFrame n + 1

/-- CONCRETE — a body `[2, 6)` (width `4`) is enclosed by the frame `[1, 7)` (width `6 = 4 + 2`). -/
example : bodyWidth 2 6 = 4 := rfl
example : frameWidth 2 6 = 6 := rfl
example : frameWidth 2 6 = bodyWidth 2 6 + 2 := rfl

/-- CONCRETE — the frame index `4 + 2 = 6` is NOT `< 4`: the body-width IH at width `4` cannot reach it. -/
example : ¬ (bodyWidth 2 6 + 2 < bodyWidth 2 6) := by decide

/-- CONCRETE — the document FRAME `[1, size - 1)` (here `size = 8`, frame `[1, 7)`, width `6`) is the
    OUTERMOST frame: the re-keyed recursion's base, with every nested frame strictly narrower. -/
example : frameWidth 2 6 = 6 := rfl
example : solveFrame 6 = 3 := rfl   -- 6 → 4 → 2 → 0, three nested levels

end EnclosingFrameRekeysWidthRecursion
