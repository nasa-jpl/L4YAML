/-!
# Reflection 343 — a context-free IH adapter cannot thread a context-dependent carrier fact; the carrier-free knot

Self-contained (core Lean, no `L4YAML` import) toy model of the PROBE outcome behind the carrier-free
`seqWindowRecSeqBody` (`(i'-b-B2c-desc-fixpoint-assembly)`).

R342 produced the per-window `FlowBodyContent` SOURCE carrier-free (`seqRoot_flowBodyContent` root seed +
the two landed edges `flowBodyContent_descend` / `flowBodyContent_advance`).  The next move was to ASSEMBLE
the `windowWidth_strongRecOn` `RecSeqBody` producer with `FlowBodyContent` THREADED as a `G`-conjunct
instead of looked up from the ambient carrier — the device that breaks the carrier↔recursion circularity
(R318/R340) once and for all.

The mandated probe asked: does the IH adapter admit a CLEAN ordering (build each child `FlowBodyContent`
from the descend/advance edge BEFORE invoking `ih`), or is there a TRUE CO-RECURSIVE KNOT?  **It is the
latter.**  Two facts collide:

* The recursion's IH reaches the descend recursion only through the dispatch's `h_ih`, a *context-free*
  universal `∀ lo' hi', hi'-lo' < hi-lo → (cheap guards) → RecSeqBody`.  Threading `FlowBodyContent` as a
  guard conjunct forces the adapter that builds `h_ih` from the step's `ih` to materialise
  `FlowBodyContent tokens lo' hi'` for an ARBITRARY sub-window `lo' hi'` — but the only carrier-free
  sources (descend/advance) need the enclosing/preceding window context the *context-free* adapter does
  not have.
* `recseqentry_window_dispatch` consumes the current window's full `FlowBodyContent` (`headContentStart`,
  `bodySucc`, both bracket oracles), while `FlowBodyContent W` is obtainable carrier-free only from
  `RecSeqBody W`'s own `SafeBodyUnit` (R296: the separator facts have no balance-free form).  So
  `Content W ⟸ Rec W ⟸ dispatch ⟸ Content W` — a *same-window* cycle the width recursion cannot break,
  and `P := Rec ∧ Content` does NOT untie it (the dispatch still needs the same window's `Content` as
  input).

The carrier was precisely the device that broke the knot — a GLOBAL oracle answering `Content` at any
window WITHOUT recursion.  Removing it reinstates the cycle.  The toy below models exactly this:

* `Content` is sourced from `Rec` at the SAME window (`content_of_rec`, toy of
  `SafeBodyUnit`-of-`RecSeqBody` ▸ `flowBodyContent_of_deep`);
* the dispatch needs the current window's `Content` PLUS a *context-free* `Rec`-IH over smaller windows
  (`dispatch`, toy of `recseqentry_window_dispatch`).

POSITIVE (`rec_via_carrier`): with the GLOBAL carrier `∀ w, Content w` the producer closes — the carrier
answers `Content` at every window without recursion.

NEGATIVE (`rec_guarded_needs_carrier` + `content_of_rec`): threading `Content` through the recursion guard
buys NOTHING — to call the guarded IH `∀ w', w' < w → Content w' → Rec w'` the step must inject
`Content w'` at every recursive call, and the only carrier-free source `content_of_rec` needs `Rec w'` (the
output), so the step must take the WHOLE carrier `∀ w, Content w` as an undischarged hypothesis — exactly
the carrier route, no progress.  The cycle is `Content w ⟵ Rec w ⟵ dispatch ⟵ Content w`.

RESOLUTION (`rec_resolved` + `content_resolved`): the knot cuts only by making the dispatch
`Content`-FREE — reconstruct its three first-entry/head facts (`headContentStart`, `bodySucc`,
oracle-facts) carrier-free from the deep guard + boundary context ([[ref-prefix-gate-reconstructed-from-boundary]]).
Then the `Rec` producer closes with NO carrier and NO `Content` threading, and `Content` of any window
drops out as a pure downstream COROLLARY of its produced `Rec`.
-/

namespace Tests.Reflections.ContextFreeAdapterKnot

set_option autoImplicit false

/-! ## The abstract dependency structure (the two propositions and the two structural lemmas)

`Rec`/`Content` are opaque (the toy isolates the DEPENDENCY GRAPH, not the bracket content): `Rec w` is
"the width-`w` window resolves to a recursive body" (toy `RecSeqBody`), `Content w` is "its separator
facts hold" (toy `FlowBodyContent`).  The two lemmas are the load-bearing edges:

* `content_of_rec` — `Content W` follows from `Rec W` at the SAME window (toy: `SafeBodyUnit`-of-`RecSeqBody`
  ▸ separator facts).  This is the same-window edge that, with the dispatch, closes the cycle.
* `dispatch` — to produce `Rec W` the dispatch needs the CURRENT window's `Content W` plus a *context-free*
  `Rec`-IH over strictly-smaller windows (toy `recseqentry_window_dispatch` + `recseqbody_window_assemble`).
-/

/-! ## POSITIVE — the carrier route closes (the GLOBAL oracle answers `Content` without recursion) -/

/-- **The carrier route** (toy of the carrier-dependent `seqWindowRecSeqBody`).  Given the GLOBAL carrier
    `∀ w, Content w` — an external oracle, NOT produced by this recursion — the producer closes by strong
    recursion: at each window the carrier supplies the dispatch's `Content w`, the IH supplies the smaller
    windows.  No knot, because the carrier never recurses. -/
theorem rec_via_carrier (Rec Content : Nat → Prop)
    (dispatch : ∀ w, Content w → (∀ w', w' < w → Rec w') → Rec w)
    (carrier : ∀ w, Content w) : ∀ w, Rec w := fun w =>
  Nat.strongRecOn w (fun w ih => dispatch w (carrier w) ih)

/-! ## NEGATIVE — threading `Content` through the guard buys nothing; the same-window cycle

To remove the carrier we thread `Content` as the recursion's guard, so the IH becomes
`∀ w', w' < w → Content w' → Rec w'`.  But the step's adapter is *context-free* in `w'` — to invoke that
IH it must supply `Content w'` for arbitrary smaller `w'`, and there is no carrier-free source: the only
one (`content_of_rec`) needs `Rec w'`, the very output.  So the guarded producer can be written ONLY by
injecting the whole carrier at each call — reconstructing the carrier it set out to eliminate. -/

/-- **The guarded recursion is STUCK at the adapter**: producing `∀ w, Content w → Rec w` (the guarded
    form) requires injecting `carrier w'` at each recursive call, because the context-free IH adapter
    `fun w' hw' => ih w' hw' ?` has no other way to discharge the threaded `Content w'` premise.  The
    `carrier` hypothesis is the undischarged debt — identical to `rec_via_carrier`, so the guard buys
    nothing.  (Without `carrier`, the `?` is unfillable: that unfillability IS the knot.) -/
theorem rec_guarded_needs_carrier (Rec Content : Nat → Prop)
    (dispatch : ∀ w, Content w → (∀ w', w' < w → Rec w') → Rec w)
    (carrier : ∀ w, Content w) : ∀ w, Content w → Rec w := fun w =>
  Nat.strongRecOn w (fun w ih _hc => dispatch w (carrier w) (fun w' hw' => ih w' hw' (carrier w')))

/-- **The same-window cycle** (toy of R296 + the dispatch's `Content` input).  `Content w` is sourced from
    `Rec w` at the SAME window — so combined with `dispatch` (which needs `Content w` to produce `Rec w`)
    the dependency is `Content w ⟵ Rec w ⟵ dispatch ⟵ Content w`, a cycle at a SINGLE window that
    well-founded width recursion (which only delivers strictly-smaller windows) cannot break. -/
theorem content_same_window (Rec Content : Nat → Prop)
    (content_of_rec : ∀ w, Rec w → Content w) (w : Nat) (h : Rec w) : Content w :=
  content_of_rec w h

/-! ## RESOLUTION — a `Content`-FREE dispatch cuts the knot; `Content` becomes a corollary

The knot cuts only by removing `Content` from the dispatch's INPUT.  Its three uses (`headContentStart`,
`bodySucc`, the bracket oracles) are all FIRST-ENTRY/head facts; reconstructing them carrier-free from the
deep guard + boundary context makes the dispatch `Content`-free.  Then the producer closes with NO carrier,
and `Content` of any window is a pure downstream corollary of its produced `Rec`. -/

/-- **The resolved producer** (the pivot): with a `Content`-FREE dispatch the `Rec` producer closes by
    plain strong recursion — no carrier, no `Content` threading, no knot. -/
theorem rec_resolved (Rec : Nat → Prop)
    (dispatch_cf : ∀ w, (∀ w', w' < w → Rec w') → Rec w) : ∀ w, Rec w := fun w =>
  Nat.strongRecOn w (fun w ih => dispatch_cf w ih)

/-- **`Content` as a downstream corollary**: once `Rec` is produced carrier-free, `Content` of every window
    drops out by `content_of_rec` — the same-window edge that was a CYCLE under the input-dispatch is a
    one-way DERIVATION under the `Content`-free dispatch. -/
theorem content_resolved (Rec Content : Nat → Prop)
    (content_of_rec : ∀ w, Rec w → Content w)
    (dispatch_cf : ∀ w, (∀ w', w' < w → Rec w') → Rec w) : ∀ w, Content w :=
  fun w => content_of_rec w (rec_resolved Rec dispatch_cf w)

/-! ## A concrete model — smoke tests that every route is inhabited (and the metric decreases)

Instantiate `Rec`/`Content` as the always-true predicate with trivial edges, confirming each producer
above is a total function of the width.  (The toy's content is the DEPENDENCY GRAPH above; these guards
just witness that the resolved and carrier routes both deliver.) -/

/-- The trivial concrete model: every window resolves, every window's content holds. -/
abbrev RecT : Nat → Prop := fun _ => True
abbrev ContentT : Nat → Prop := fun _ => True

theorem contentT_of_recT : ∀ w, RecT w → ContentT w := fun _ _ => trivial
theorem dispatchT : ∀ w, ContentT w → (∀ w', w' < w → RecT w') → RecT w := fun _ _ _ => trivial
theorem dispatchT_cf : ∀ w, (∀ w', w' < w → RecT w') → RecT w := fun _ _ => trivial
theorem carrierT : ∀ w, ContentT w := fun _ => trivial

example : RecT 5 := rec_via_carrier RecT ContentT dispatchT carrierT 5
example : RecT 5 := rec_resolved RecT dispatchT_cf 5
example : ContentT 7 := content_resolved RecT ContentT contentT_of_recT dispatchT_cf 7

#guard (decide (RecT 5))          -- the resolved producer delivers at width 5
#guard (decide (ContentT 7))      -- the corollary delivers at width 7
#guard (3 < 5)                    -- the width metric the IH strictly decreases

end Tests.Reflections.ContextFreeAdapterKnot
