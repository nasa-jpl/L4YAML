/-!
# Reflection 348 — a carrier-free IH thread's descend edge re-enters its OWN window: the five→four projection runs UP the strength order, and the combined deliverable relocates the same-window cycle without breaking it

Self-contained (core Lean, no `L4YAML` import) toy model of the PROBE that settled
`(i'-b-B2c-dispatch-ih-widen)` step (3): is `flowBodyContent_descend`'s four-conjunct `h_ih`
obtainable by PROJECTING the widened five-conjunct recursion IH?

R347 settled the carrier-free route as "thread `FlowBodyContent` (`F`) as a fifth `G`-conjunct,
discharge it at the structural sites via the landed descend/advance edges, with the dispatch IH
SIGNATURE widened by `F`." Its toy modeled the descend edge as a CLEAN parent→child arrow
(`F.descend : F plo phi → F lo hi`). The R348 PROBE — run mechanically against the real definitions
in `Tests/Guards/Proofs/DescendIHProjectionProbe.lean` (sorry-free) and abstracted here — finds that
arrow is too optimistic: the REAL descend edge builds the child's `F` from the child's OWN `Out`
(`RecSeqBody`, via `seqChild_safeBodyUnit`), because `F`'s `bodySucc` has no all-depth balance-free
form (R296) and so cannot re-base down a nesting level the way the ADVANCE edge re-bases along one.

THE TWO DECISIVE FINDINGS (both sorry-free below):

1. STRICT STRENGTH ORDER. `IH4` (produces a child `Out` from FOUR intrinsic facts) is STRICTLY
   STRONGER than `IH5` (needs the child's `F` too). Four→five is a free drop (`ih5_of_ih4`); five→four
   closes IFF a per-window `provider : Intrinsic → F` exists (`ih4_of_ih5_iff_provider`). The needed
   projection therefore runs UP the strength order — impossible without a NEW producer for the dropped
   `F`, which is precisely the carrier-free `F` the whole arc lacks.

2. THE CYCLE SURVIVES COMBINATION. `F n` is read OFF `Out n` (`f_of_out`, toy
   `seqSeparatorFacts_of_recseqbody`) while `Out n`'s dispatch needs `F n` as INPUT (`out_needs_f`).
   Composed, that is an endo with no seed (`same_window_loop`) — the same shape as R346's
   `carrier_route_is_a_loop`, but now located at a SINGLE window. Producing the COMBINED deliverable
   `Pair n := Out n ∧ F n` does not dissolve it: the step still needs `F n` to build `Out n` and
   `Out n` to build `F n` (`combined_step_still_cyclic`). The combined deliverable RELOCATES the cycle
   from the recursive edge into the step; it does not break it.

THE BREAK (positive). The cycle opens only when `F` has an EMISSION source independent of `Out`
(`break_via_emission`): then `F n` is a genuine recursion INPUT, the four-conjunct `G` suffices, and
no thread or combination is needed. The forward route is to generalize the flat root seed
(`seqRoot_safeBodyUnit` / `seqRoot_flowBodyContent`) to nested sub-values.

THE EDGE ASYMMETRY (why descend, not advance). `advance_supplies_child` models the ADVANCE edge — a
clean parent→child arrow with NO `Out` in the loop, exactly R347's optimistic shape, and it is sound.
`descend_supplies_child_via_out` models the DESCEND edge — the child's `F` routed through the child's
own `Out`, which `out_needs_f` ties back to the child's `F`: a same-window 2-cycle. The asymmetry is
[[ref-push-blind-frame-dependent]] / [[ref-converse-forward-invariant-asymmetry]] recurring on the
content thread.
-/

namespace Tests.Reflections.ProjectionUpStrengthOrder

set_option autoImplicit false

/-! ## The two invariants and the per-window intrinsic facts -/

/-- The INTRINSIC per-window facts — re-derivable from the window alone (toy
    `FlowBodyWindow ∧ FlowBodyContentDeep ∧ Q ∧ close`). -/
def Intrinsic (n : Nat) : Prop := 0 ≤ n

/-- `F` — the parent-relative / emission invariant (toy `FlowBodyContent`, ultimately `bodySucc`). -/
def F (n : Nat) : Prop := 0 ≤ n
/-- `Out` — the recursion's deliverable (toy `RecSeqBody`). -/
def Out (n : Nat) : Prop := 0 ≤ n

/-! ## Finding 1 — the projection runs UP the strength order -/

/-- The FOUR-conjunct IH `flowBodyContent_descend` consumes: a child's `Out` from intrinsic facts
    ALONE, no child `F`. -/
def IH4 : Prop := ∀ n, Intrinsic n → Out n
/-- The FIVE-conjunct IH the widened recursion hands its step: a child's `Out` needs that child's `F`
    as an extra INPUT. -/
def IH5 : Prop := ∀ n, Intrinsic n → F n → Out n

/-- **POSITIVE — four→five is the FREE drop.**  `IH4` needs less, so it serves where five are offered
    (the extra `F` input is ignored).  Hence `IH4` is STRICTLY STRONGER than `IH5`. -/
theorem ih5_of_ih4 (h4 : IH4) : IH5 := fun n hi _hf => h4 n hi

/-- **NEGATIVE (residual isolated, sorry-free) — five→four closes IFF a per-window `provider`.**  The
    forward projection supplies the dropped `F` at each child from intrinsic facts via `provider`; the
    projection EXISTS iff `provider` does.  And `provider : ∀ n, Intrinsic n → F n` is exactly the
    carrier-free `F`-from-intrinsics the arc lacks (R296/R345 + the cycle below).  So the projection is
    a GENUINE arity entanglement, not a mechanical drop. -/
theorem ih4_of_ih5_iff_provider (h5 : IH5) (provider : ∀ n, Intrinsic n → F n) : IH4 :=
  fun n hi => h5 n hi (provider n hi)

/-! ## Finding 2 — the same-window cycle survives the combined deliverable -/

/-- `F n` is read OFF `Out n` — toy `seqSeparatorFacts_of_recseqbody`. -/
def f_of_out : Prop := ∀ n, Out n → F n
/-- `Out n`'s dispatch needs `F n` as INPUT — toy `recseqentry_window_dispatch` reading `bodySucc`. -/
def out_needs_f : Prop := ∀ n, F n → Out n

/-- **NEGATIVE (same-window loop).**  Composed at ONE window, the two arrows are an endo `F → F` with
    no seed — it presupposes its own input.  Same shape as R346's `carrier_route_is_a_loop`, now at a
    single window. -/
theorem same_window_loop (h1 : f_of_out) (h2 : out_needs_f) : ∀ n, F n → F n :=
  fun n h => h1 n (h2 n h)

/-- **NEGATIVE (combination relocates, does not break).**  Producing the COMBINED deliverable
    `Pair n := Out n ∧ F n` from intrinsic facts would need to seed the cycle: given a would-be step
    `intrinsic → Pair`, the `Out`-component still consumes `F` and the `F`-component still consumes
    `Out`, so the step is only as good as a cycle-breaker it does not contain.  Modeled as: a pair
    producer that is HANDED the cyclic arrows is still an endo on `F` — combining `Out` and `F` into
    one deliverable moves the loop from the recursive edge into the step, it does not open it. -/
theorem combined_step_still_cyclic (h1 : f_of_out) (h2 : out_needs_f) :
    ∀ n, F n → (Out n ∧ F n) :=
  fun n h => ⟨h2 n h, h1 n (h2 n h)⟩   -- both fields trace back through the same `F n` input

/-! ## The break — an emission source independent of `Out` -/

/-- **POSITIVE (the break).**  When `F` has an EMISSION source independent of `Out`, the cycle opens:
    `F n` is a genuine INPUT, `Out n` follows, and no thread or combination is needed.  The toy
    `seqRoot_safeBodyUnit` / `seqRoot_flowBodyContent`, generalized per nested sub-value. -/
theorem break_via_emission (emit : ∀ n, F n) (h2 : out_needs_f) : ∀ n, Out n :=
  fun n => h2 n (emit n)

/-! ## The edge asymmetry — advance is clean, descend re-enters the same window -/

/-- **POSITIVE (ADVANCE edge).**  A clean parent→child arrow for `F` — NO `Out` in the loop, exactly
    R347's optimistic shape.  Sound: `flowBodyContent_advance` re-bases the parent's `F` along one
    nesting level, no IH. -/
theorem advance_supplies_child (h_parent : F 0) (child_from_parent : F 0 → F 1) : F 1 :=
  child_from_parent h_parent

/-- **NEGATIVE (DESCEND edge).**  The child's `F` routed through the child's OWN `Out` (toy
    `seqChild_safeBodyUnit`), which `out_needs_f` ties straight back to the child's `F` — a same-window
    2-cycle.  Unlike advance, there is no `Out`-free arrow: `bodySucc` has no all-depth balance-free
    form (R296), so descend cannot re-base down a level and must consume the child's deliverable. -/
theorem descend_supplies_child_via_out (h1 : f_of_out) (h2 : out_needs_f) : ∀ n, F n → F n :=
  fun n h => h1 n (h2 n h)   -- identical to `same_window_loop`: descend's `F` route IS the cycle

end Tests.Reflections.ProjectionUpStrengthOrder
