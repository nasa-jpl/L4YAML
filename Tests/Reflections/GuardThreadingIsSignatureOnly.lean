/-!
# Reflection 474 — repairing the producer-guarded-quantifier trap is a SIGNATURE-ONLY edit
# while the deferred hypothesis is VERIFIED-BUT-UNCONSUMED: the dropped guard is ALREADY bound
# at the dispatcher's branch, so threading it costs exactly (one signature conjunct) + (one
# already-in-scope argument), touches no consumer, and flips the hypothesis from UNSATISFIABLE
# to satisfiable with NO proof-body change.  Caught later — once a supplier exists — the same
# fix is expensive: the supplier inherits the previously-impossible obligation.

Self-contained (core Lean, no `L4YAML` import) toy recording the EDIT that R473 queued and this
turn LANDED.  R473 diagnosed the seq `h_widthEnc` residual
(`seqLocalCarrier_of_widthEnc` / `seqRoot_carrier_of_widthEnc`,
`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`) as the
producer-guarded-quantifier trap ([[ref-producer-guarded-quantifier]]): the deferred per-window
hypothesis `h_widthEnc` quantified over every gated `[a,b)` WITHOUT the dispatcher's branch guard
`flowBracketBalance tokens lo a ≠ 0`, so — as stated — it had to hold for the document-boundary
opener `p = lo - 1` too, demanding the UNINHABITABLE `FlowBodyWindow tokens 1 hiE`
(`FlowBodyWindow.lo_ge : 2 ≤ lo`).

**The fix (this reflection).**  Thread the guard.  The dispatcher
`seqInteriorSeparators_of_safebody_and_descent` case-splits each gated `[a,b)` on
`flowBracketBalance tokens lo a = 0`; only the `else` branch (`balance lo a ≠ 0`) calls
`h_widthEnc`, and that branch ALREADY BINDS the guard as `_hbal` (it is `desc`'s 4th argument).
So the repair was:
  1. insert `flowBracketBalance tokens lo a ≠ 0 →` into `h_widthEnc`'s signature (and the root
     instance `seqRoot_carrier_of_widthEnc`, `lo := 2`), and
  2. pass the in-scope `_hbal` at the one call site (line 2647).
No proof-body restructuring; the lemma is verified-but-unconsumed so NO consumer breaks; the build
stays green and the frontier sorry count unchanged at 4.  With the guard present, every instance
of `h_widthEnc` now has `lo ≤ p` (the guard excludes `p = lo - 1`, R473), so the deliverable's
enclosing frame `[p, hiE) ⊆ [lo, hi)` is CONTAINED and the eventual joint induction can supply it.

**The reusable point — the trap's REPAIR cost is asymmetric in time.**
* WHILE verified-but-unconsumed: the guard the hypothesis needs is the very binding the call site
  already has in scope (a dispatcher branch carries it).  Threading it is mechanical — rename a
  dropped binder into the signature — and provably nothing downstream can break, because nothing
  supplies the hypothesis yet.  This is the cheapest moment to fix the trap.
* ONCE a supplier exists: the supplier inherits the now-stated obligation — which, before the fix,
  was secretly impossible (it had to inhabit the deliverable at the boundary instance).  Fixing the
  trap then means re-proving that the supplier only ever hits guarded instances, i.e. doing the
  satisfiability work the unguarded statement hid.

This toy reproduces exactly that asymmetry:

* `Deliv` / boundary uninhabitability — the deliverable inhabited only at `2 ≤ a`
  (`FlowBodyWindow.lo_ge` analog), so the boundary index `1` cannot inhabit it.
* `provU_unsatisfiable` — the UNGUARDED deferred hypothesis (`∀ a, 1 ≤ a → Deliv a`) is
  unsatisfiable: instantiated at `a = 1` it demands `Deliv 1`, i.e. `2 ≤ 1`.  Yet it type-checks
  as a hypothesis — the trap.
* `provG_satisfiable` — the GUARDED hypothesis (`∀ a, 1 ≤ a → a ≠ 1 → Deliv a`) is a CLOSED TERM:
  `1 ≤ a` and `a ≠ 1` give `2 ≤ a`.  The guard is precisely what makes it dischargeable.
* `dispatch` — the dispatcher case-splits on the decidable `a = 1`; the `else` branch BINDS
  `h : a ≠ 1` and feeds it to the guarded provider, modelling `_hbal` being in scope at the
  `h_widthEnc` call.  The guarded argument is free — already bound.
* `cost_is_one_in_scope_argument` — the only delta between the unguarded and guarded provider call
  is the single in-scope `h : a ≠ 1`; everything else is identical.
-/

namespace GuardThreadingIsSignatureOnly

set_option autoImplicit false

/-- The per-index deliverable a deferred provider must inhabit.  Inhabited only at `2 ≤ a` — the
    `FlowBodyWindow.lo_ge : 2 ≤ lo` analog: a body window opens at index `≥ 2`, so the
    document-boundary index `1` (the `p = lo - 1` opener) cannot inhabit it. -/
structure Deliv (a : Nat) : Prop where
  ge2 : 2 ≤ a

/-- The dispatcher's domain bound on every index it visits (the `lo ≤ a` analog): at least the
    document opener position `1`. -/
def Domain (a : Nat) : Prop := 1 ≤ a

/-- **THE UNGUARDED DEFERRED HYPOTHESIS IS UNSATISFIABLE.**  Quantified over every in-domain `a`
    WITHOUT the dispatcher's branch guard, it must hold at the boundary index `a = 1`, where
    `Deliv 1` demands `2 ≤ 1`.  It type-checks fine as a *hypothesis* — that is the
    producer-guarded-quantifier trap ([[ref-producer-guarded-quantifier]]): undischargeable yet
    well-typed. -/
theorem provU_unsatisfiable : ¬ (∀ a, Domain a → Deliv a) := by
  intro h
  exact absurd (h 1 (by unfold Domain; omega)).ge2 (by omega)

/-- **THE GUARDED HYPOTHESIS IS SATISFIABLE — the guard is the whole fix.**  Threading the
    dispatcher's branch guard `a ≠ 1` into the signature makes the provider a CLOSED TERM:
    `Domain a` (`1 ≤ a`) and `a ≠ 1` give `2 ≤ a` by `omega`.  Contrast `provU_unsatisfiable`:
    same deliverable, same domain, only the guard added — and now it is inhabited. -/
theorem provG_satisfiable : ∀ a, Domain a → a ≠ 1 → Deliv a :=
  fun _ h1 hne => ⟨by unfold Domain at h1; omega⟩

/-- The dispatcher's per-index outcome: at the boundary it is the flat-root branch (`a = 1`,
    the `seqEnclosingFacts_provider_of_located`-from-`h_safe` analog); elsewhere it is the
    provider's deliverable (the `desc`/`h_widthEnc` branch). -/
def Outcome (a : Nat) : Type := PSum (a = 1) (Deliv a)

/-- **THE GUARD IS ALREADY IN SCOPE AT THE PROVIDER CALL — threading it is FREE.**  The
    dispatcher case-splits on the decidable `a = 1`: the `then` branch is the flat-root handler
    (`PSum.inl`), the `else` branch BINDS `h : a ≠ 1` and calls the guarded provider.  So the
    provider's extra argument is satisfied by a binding the dispatcher already has — the repair is
    (one signature conjunct) + (one already-bound argument), no proof-body restructuring.  This
    mirrors `seqLocalCarrier_of_widthEnc`, whose `else`-branch binds `_hbal` and now passes it to
    `h_widthEnc`. -/
def dispatch (provG : ∀ a, Domain a → a ≠ 1 → Deliv a) :
    ∀ a, Domain a → Outcome a :=
  fun a h1 =>
    if h : a = 1 then
      PSum.inl h
    else
      PSum.inr (provG a h1 h)

/-- **THE COST, MADE EXPLICIT — one in-scope argument.**  The guarded dispatcher runs end-to-end
    using only the satisfiable provider; the unguarded analog could never be applied
    (`provU_unsatisfiable`).  The delta between them is exactly the single in-scope `h : a ≠ 1`
    threaded into the provider call.  Hence the trap is FREE to repair while the hypothesis is
    verified-but-unconsumed, and expensive once a supplier inherits the impossible obligation. -/
theorem cost_is_one_in_scope_argument :
    (∀ a, Domain a → a ≠ 1 → Deliv a) ∧ ¬ (∀ a, Domain a → Deliv a) :=
  ⟨provG_satisfiable, provU_unsatisfiable⟩

/-- CONCRETE — at the boundary index `1` the dispatcher takes the flat-root branch (`PSum.inl`),
    never touching the provider; `Deliv 1` is never demanded. -/
example : dispatch provG_satisfiable 1 (by unfold Domain; omega) = PSum.inl rfl := rfl

/-- CONCRETE — at a non-boundary index `3` the dispatcher takes the provider branch, and the
    guarded provider discharges it. -/
example : ∃ d : Deliv 3, dispatch provG_satisfiable 3 (by unfold Domain; omega) = PSum.inr d :=
  ⟨_, rfl⟩

/-- CONCRETE — the deliverable really is uninhabitable at the boundary, which is why the unguarded
    hypothesis could never be supplied. -/
example : ¬ Deliv 1 := fun d => absurd d.ge2 (by omega)

end GuardThreadingIsSignatureOnly
