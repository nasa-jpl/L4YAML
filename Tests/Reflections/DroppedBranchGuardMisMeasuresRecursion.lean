/-!
# Reflection 473 — a width-recursion producer that DROPS the BRANCH-GUARD selecting its own
# sub-case MIS-DIAGNOSES its recursion MEASURE.  The dropped guard, restored, BOTH excludes the
# out-of-range (boundary) instance AND keeps the natural (body-width) measure — so the apparent need
# to re-key the recursion was an artifact of reading the WRONG branch.

Self-contained (core Lean, no `L4YAML` import) toy recording the de-risk that **CORRECTS Reflection
472**.  R472 concluded the seq carrier↔recursion joint induction could not be keyed on the BODY width
`hi - lo` and had to be re-keyed on the ENCLOSING-FRAME width, because a gated sub-window's enclosing
opener was found at `p = lo - 1` (the body's own bracket opener, OUTSIDE the body), making the
obligation reference the FRAME `[lo-1, hi+1)` of width `(hi-lo) + 2`, beyond a body-width IH.

**The de-risk OUTCOME (this reflection).  R472 read the WRONG branch.**  The carrier dispatcher
`seqInteriorSeparators_of_safebody_and_descent` CASE-SPLITS every gated sub-window `[a,b) ⊆ [lo,hi)`
on `flowBracketBalance tokens lo a = 0`:

* the **`then` branch** (`balance lo a = 0`, a TOP-LEVEL window at depth `0` of the body) is handled
  by `seqEnclosingFacts_provider_of_located` *directly from the flat root `SafeBodyUnit`* (`h_safe`),
  with `loS = lo, hiS = hi` — the WHOLE body, NO descent, NO nested `FlowBodyWindow`.  THIS is the
  `p = lo - 1` (= document opener `[`) case R472 analysed;
* the **`else` branch** (`balance lo a ≠ 0`, a STRICTLY NESTED window) is the only branch handled by
  `desc` / `h_widthEnc`.

So `h_widthEnc` is invoked ONLY when `balance lo a ≠ 0`.  Under that guard the located enclosing opener
`p` (from `flowBracketBalance_backward_open_locate`, satisfying `balance (p+1) a = 0`) CANNOT be
`lo - 1`: if `p + 1 = lo` then `balance (p+1) a = balance lo a ≠ 0`, contradicting the locator's
`balance (p+1) a = 0`.  Hence `lo ≤ p`, the enclosing frame `[p, hiE)` is CONTAINED in the body
(`lo ≤ p`, `hiE ≤ hi`), its width `hiE - p ≤ hi - lo` — never `+2` — and a body-width IH (`< hi - lo`)
covers the deliverable's frame IH (`< hiE - p ≤ hi - lo`) with **no gap** (the `<` is strict, so even
the equality case `p = lo, hiE = hi` is covered).

**The real bug is a DROPPED GUARD, not the measure.**  `h_widthEnc`'s signature quantifies over
`a b p` WITHOUT the `flowBracketBalance tokens lo a ≠ 0` hypothesis — even though the `desc` branch
binds it (`_hbal`) and has it in scope at the call site, it is not passed.  As stated, `h_widthEnc`
would have to hold for the `p = lo - 1` instance too, which demands `FlowBodyWindow tokens 1 hiE` —
UNINHABITABLE, since `FlowBodyWindow.lo_ge : 2 ≤ lo` and `.hi_le : hi ≤ size - 2` exclude the document
bracket.  This is the producer-guarded-quantifier trap: undischargeable yet type-checks.  The fix is
to thread the guard (`balance lo a ≠ 0`) into `h_widthEnc`, NOT to re-key the recursion.

This toy reproduces exactly that:

* `BodyWin` / `boundary_frame_uninhabitable` — the window guard's `2 ≤ lo` lower bound makes the
  document-boundary frame `[1, …)` uninhabitable (`FlowBodyWindow.lo_ge` analog).
* `guard_excludes_document_opener` — the DROPPED branch-guard, restored: `bal lo a ≠ 0` together with
  the locator's `bal (p+1) a = 0` forces `p + 1 ≠ lo`, i.e. `p ≠ lo - 1`.  Pure logic, any `bal`.
* `located_opener_ge_lo` — `p ≠ lo - 1` plus the locator's own containment `lo - 1 ≤ p` gives `lo ≤ p`.
* `frame_le_body` — under `lo ≤ p`, `hiE ≤ hi` the frame is CONTAINED: `hiE - p ≤ hi - lo` (contrast
  R472's `bodyWidth + 2`).
* `body_ih_covers_frame_ih` — the body-width IH covers the frame IH with NO GAP (contrast R472's
  `¬ (w + 2 < w)`); the `<` is strict so the equality case is covered too.
* `r472_thenBranch_frameWidth` / `r472_thenBranch_is_plus_two` — the `+2` frame R472 measured is the
  `then`-branch (`p = lo - 1`) geometry, the case `desc` NEVER sees.
-/

namespace DroppedBranchGuardMisMeasuresRecursion

set_option autoImplicit false

/-- The window guard's structural lower bound (the `FlowBodyWindow.lo_ge : 2 ≤ lo` analog): a body
    window must start at `≥ 2`, so the document-boundary frame `[1, …)` cannot inhabit it. -/
structure BodyWin (lo hi : Nat) : Prop where
  lo_ge : 2 ≤ lo
  lo_lt_hi : lo < hi

/-- **The document-boundary frame is UNINHABITABLE.**  `FlowBodyWindow tokens 1 hiE` cannot exist —
    `lo_ge` demands `2 ≤ 1`.  This is why `h_widthEnc`'s unguarded `p = lo - 1` (= 1 at the root)
    instance is undischargeable: it asks for exactly this. -/
theorem boundary_frame_uninhabitable (hi : Nat) : ¬ BodyWin 1 hi :=
  fun h => absurd h.lo_ge (by omega)

/-- **THE DROPPED BRANCH-GUARD, RESTORED — it excludes the document opener.**  `h_widthEnc` is reached
    ONLY in the `else` branch, where `desc` carries `bal lo a ≠ 0` (`_hbal`).  The backward locator
    gives `bal (p+1) a = 0`.  If `p + 1 = lo` the two are the SAME expression — contradiction.  So the
    located enclosing opener is never `lo - 1` (the body's own / document bracket opener).  Pure logic,
    holds for ANY balance function `bal`. -/
theorem guard_excludes_document_opener
    (bal : Nat → Nat → Int) (lo a p : Nat)
    (h_guard : bal lo a ≠ 0)
    (h_loc : bal (p + 1) a = 0) :
    p + 1 ≠ lo := by
  intro h; rw [h] at h_loc; exact h_guard h_loc

/-- The located opener sits inside the body: `p ≠ lo - 1` (the restored guard) plus the locator's own
    containment `lo - 1 ≤ p` (it never scans before the enclosing bracket) gives `lo ≤ p`. -/
theorem located_opener_ge_lo (lo p : Nat) (h_lo : 1 ≤ lo)
    (h_ne : p + 1 ≠ lo) (h_ge : lo - 1 ≤ p) : lo ≤ p := by omega

/-- The width of the seq BODY window `[lo, hi)` — the recursion's natural measure. -/
def bodyWidth (lo hi : Nat) : Nat := hi - lo

/-- The width of the located enclosing frame `[p, hiE)`. -/
def frameWidth (p hiE : Nat) : Nat := hiE - p

/-- **THE FRAME IS CONTAINED — width `≤`, not `+2`.**  Under the restored guard (`lo ≤ p` from
    `located_opener_ge_lo`) and the close-bound `hiE ≤ hi`, the frame `[p, hiE) ⊆ [lo, hi)`, so its
    width never exceeds the body's.  Contrast R472's `frameWidth = bodyWidth + 2`. -/
theorem frame_le_body (lo hi p hiE : Nat) (h_p : lo ≤ p) (h_hiE : hiE ≤ hi) :
    frameWidth p hiE ≤ bodyWidth lo hi := by
  unfold frameWidth bodyWidth; omega

/-- **THE BODY-WIDTH IH COVERS THE FRAME IH — NO GAP.**  The joint induction keyed on the BODY width
    `hi - lo` hands an IH usable at every `hi' - lo' < hi - lo`.  `h_widthEnc`'s deliverable IH needs
    coverage of `hi' - lo' < frameWidth p hiE`, and `frameWidth p hiE ≤ bodyWidth lo hi`
    (`frame_le_body`), so the body-width IH covers it.  The `<` is STRICT, so even the equality case
    `p = lo, hiE = hi` (frame = body) is covered.  Contrast R472's obstruction `¬ (w + 2 < w)`: the
    measure that fails for a `+2` frame SUCCEEDS for a contained frame. -/
theorem body_ih_covers_frame_ih (lo hi p hiE lo' hi' : Nat)
    (h_p : lo ≤ p) (h_hiE : hiE ≤ hi)
    (h_need : hi' - lo' < frameWidth p hiE) :
    hi' - lo' < bodyWidth lo hi := by
  have h := frame_le_body lo hi p hiE h_p h_hiE
  omega

/-- The frame R472 measured — the `then`-branch geometry `p = lo - 1`, `hiE = hi + 1`. -/
def r472_thenBranch_frameWidth (lo hi : Nat) : Nat := frameWidth (lo - 1) (hi + 1)

/-- **R472's `+2` frame is the `then`-branch (top-level window) case `desc` NEVER sees.**  For a
    top-level gated window the enclosing opener IS `lo - 1` and the close `hi`, giving the frame
    `[lo-1, hi+1)` of width `bodyWidth + 2` — but that window is the `then` branch, handled directly
    from `h_safe`, never reaching `h_widthEnc`. -/
theorem r472_thenBranch_is_plus_two (lo hi : Nat) (h_lo : 1 ≤ lo) (h_le : lo ≤ hi) :
    r472_thenBranch_frameWidth lo hi = bodyWidth lo hi + 2 := by
  unfold r472_thenBranch_frameWidth frameWidth bodyWidth; omega

/-- CONCRETE — the document-boundary frame `[1, 7)` is uninhabitable. -/
example : ¬ BodyWin 1 7 := boundary_frame_uninhabitable 7

/-- CONCRETE — a body `[2, 6)` (width `4`) whose nested gated window has enclosing frame `[3, 5)`
    (`p = 3 ≥ lo = 2`, width `2 ≤ 4`): the frame is CONTAINED, body-width keying applies. -/
example : bodyWidth 2 6 = 4 := rfl
example : frameWidth 3 5 = 2 := rfl
example : frameWidth 3 5 ≤ bodyWidth 2 6 := by decide

/-- CONCRETE — the body-width IH (`< 4`) covers the frame IH (`< 2`): any `hi' - lo' < 2` is `< 4`. -/
example : (1 : Nat) < frameWidth 3 5 → (1 : Nat) < bodyWidth 2 6 := by decide

/-- CONCRETE — R472's `then`-branch frame `[1, 7)` is `+2` (width `6 = 4 + 2`): the case `desc` skips. -/
example : r472_thenBranch_frameWidth 2 6 = 6 := rfl
example : r472_thenBranch_frameWidth 2 6 = bodyWidth 2 6 + 2 := rfl

end DroppedBranchGuardMisMeasuresRecursion
