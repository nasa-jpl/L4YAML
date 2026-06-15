/-!
# Reflection 439 — adding a GUARD (antecedent) to a shared field is the DUAL of adding a conclusion
# conjunct: it ripples to CONSUMERS, not producers — and a guard that FIXES an over-strong contract
# breaks the counterexample lemma that proved it over-strong (which IS the proof the fix worked).

Self-contained (core Lean, no `L4YAML` import) toy of the R439 finding — STEP C of the Dyck-floor
exposure.

Context.  R435 proved the parser contract `FlowSubrangesOk tokens` was itself FALSE on real emitted
output: its `.seq` field quantified over every window `[lo, hi)` with FIVE bracket-shape guards (endpoint
tokens + total balance) and NO interior floor, so a CROSS-MATCHED window (one whose guards paired the
wrong opener/closer) satisfied all five, the field fired, and `SeqBodyProps.content_start` then forced a
false `isFlowContentStart .flowSequenceEnd`.  The counterexample lemma `flowSubrangesOk_false_window`
proved `¬ FlowSubrangesOk tokens` from exactly that window.

R437/R438 (the SIBLING finding, `DelegationTreeCollapsesFieldRipple`) exposed the Dyck floor as a new
CONJUNCT on the field's CONCLUSION (`SeqBodyProps.bracket_seq` now also OUTPUTS the floor).  That
refinement rippled to PRODUCERS — every constructor must SUPPLY the conjunct — and collapsed to the
assembler root by delegation topology.

R439 (this step, STEP C) is the DUAL move: it adds the floor as a new HYPOTHESIS — an ANTECEDENT / guard —
on the fields `FlowSubrangesOk.seq`/`.map`.  Two findings:

* **Opposite ripple direction.**  A new ANTECEDENT is bind-IGNORE-free for the PRODUCER (an extra
  hypothesis only makes the field EASIER to build — the producer binds it `_` and proves the conclusion
  exactly as before; `flowSubrangesOk_of_locators.seq`/`.map` each gained one `_h_floor` binder and ZERO
  proof content) but a SUPPLY-DEBT for every CONSUMER (each `.seq`/`.map` query must now PROVIDE the
  guard).  This is the mirror of the conclusion-conjunct, which ripples to producers.  WHERE a field
  refinement ripples is set by WHICH SIDE OF THE ARROW it lands on: conclusion → producers,
  antecedent → consumers.

  The consumer cost is itself STRUCTURED by the recursion (`flow_parser_ok_of_structure`): at each DESCEND
  site the floor is READ OFF the just-located bracket field (the producer already established it there —
  the self-propagating floor), so the only genuinely-new supply is at the ROOT entry, threaded through the
  span-induction motive and discharged by the top-level caller from a real global Dyck (`h_dyck`).

* **A guard that fixes an over-strong contract breaks its own counterexample — and that break IS the
  proof.**  The floor guard EXCLUDES exactly the cross-matched window `flowSubrangesOk_false_window` used
  as its witness.  So after STEP C that lemma no longer compiles: its `.seq` application can no longer
  supply the (false) floor.  The break is not a regression — it is the machine-checked evidence that the
  floor repaired the unsatisfiability.  Repurpose, don't delete: INVERT the conclusion from `¬ Contract`
  to `¬ Guard(witness)`, reusing the SAME decision facts.  The witness flips role from "breaks the
  contract" to "excluded by the guard" (`flowSubrangesOk_seq_floor_rejects_crossMatched_window`).

The toy models both findings: the field as a guarded universal, the producer absorbing the new guard for
free, the unfloored producer hypothesis still unsatisfiable (previewing STEP D), the consumer paying the
debt, the counterexample inverting, and — PART 4 — the dual conclusion-conjunct direction.
-/

namespace Tests.Reflections.GuardFixBreaksItsCounterexample

set_option autoImplicit false

/-! ## The shared field's per-window deliverable, and the guards. -/

/-- The per-window deliverable the field concludes.  Its `content` sub-fact is FALSE on the bad window
    (`w = 5`): the toy of `SeqBodyProps.content_start` forcing `isFlowContentStart .flowSequenceEnd` on a
    cross-matched window. -/
structure Body (w : Nat) : Prop where
  content : w < 3

/-- The OLD guard — too weak: `Balanced 5` holds, so the bad window passes.  (Toy of the five
    endpoint+balance bracket guards with NO interior floor.)  `abbrev` so `decide` sees through it. -/
abbrev Balanced (w : Nat) : Prop := w % 5 = 0

/-- The NEW guard STEP C adds: the Dyck FLOOR.  It EXCLUDES the bad window (`Floor 5` is false) and is
    exactly what `Body` needs. -/
abbrev Floor (w : Nat) : Prop := w < 3

/-- An opaque per-window "locator" the producer builds `Body` from — the toy of `SeqLocated`. -/
abbrev Located (w : Nat) : Prop := w < 3

/-! ## PART 1 — the OLD (un-floored) contract is FALSE: the counterexample. -/

/-- The contract before STEP C: `∀ w, Balanced w → Body w`, no floor.  The bad window `w = 5` satisfies
    `Balanced` but not `Body`, so the contract is FALSE.  (Toy of `flowSubrangesOk_false_window`, the
    `¬ FlowSubrangesOk tokens` this lemma USED to prove.) -/
theorem oldContract_false : ¬ (∀ w, Balanced w → Body w) := by
  intro h
  exact absurd (h 5 (by decide)).content (by decide)

/-! ## PART 2 — the guard fixes the contract; the producer absorbs it for FREE. -/

/-- **The producer absorbs the new guard for FREE.**  Given the UNFLOORED locator hypothesis `hLoc`
    (keyed on the OLD guard, exactly like `flowSubrangesOk_of_locators`'s `h_seq`) and a `build`, the
    FLOORED contract is the SAME chain with one IGNORED binder `_hfloor`.  Zero new proof content — the
    bind-ignore each of `flowSubrangesOk_of_locators.{seq,map}` pays in STEP C. -/
theorem mkFlooredContract
    (hLoc : ∀ w, Balanced w → Located w) (build : ∀ w, Located w → Body w) :
    ∀ w, Balanced w → Floor w → Body w :=
  fun w hbal _hfloor => build w (hLoc w hbal)

/-- The producer's UNFLOORED locator hypothesis is itself unsatisfiable — the bad window `5` passes
    `Balanced` but has no `Located`.  This is WHY STEP D must ALSO floor the producer hypotheses
    (`h_seq_rec`/`h_map_rec`): `mkFlooredContract` typechecks (verified) but its `hLoc` cannot be
    discharged until the floor narrows ITS domain too. -/
theorem unflooredLocator_unsatisfiable : ¬ (∀ w, Balanced w → Located w) := by
  intro h
  exact absurd (h 5 (by decide)) (by decide)

/-- The floored contract is genuinely PROVABLE (satisfiable) — the floor repaired the unsatisfiability
    `oldContract_false` exhibited.  Built directly from the floor; the bad window never reaches here. -/
theorem newContract_holds : ∀ w, Balanced w → Floor w → Body w :=
  fun _w _hbal hfloor => ⟨hfloor⟩

/-! ## PART 3 — the consumer pays the supply-debt; the counterexample inverts. -/

/-- **The consumer pays the supply-debt.**  Instantiating the floored contract requires PROVIDING the
    floor at every query — the cost `flow_parser_ok_of_structure` pays (`hsub.seq … h_floor`).  At a
    genuine window the floor holds, so it can be supplied. -/
theorem consume (C : ∀ w, Balanced w → Floor w → Body w) (w : Nat)
    (hbal : Balanced w) (hfloor : Floor w) : Body w :=
  C w hbal hfloor

/-- **The counterexample INVERTS.**  `oldContract_false` used the bad window `5` to refute the
    UN-floored contract.  After STEP C the SAME witness refutes the FLOOR — `Floor 5` is false — so the
    window is EXCLUDED, the contract is satisfiable, and `oldContract_false`'s route is severed.  Same
    witness, dual role.  (Toy of `flowSubrangesOk_seq_floor_rejects_crossMatched_window`: the cross-matched
    window passes the boundary guards yet fails the floor.) -/
theorem floorRejectsBadWindow : Balanced 5 ∧ ¬ Floor 5 :=
  ⟨by decide, by decide⟩

/-! ## PART 4 — the DUAL direction (R437/R438): a CONCLUSION conjunct ripples to the PRODUCER.

`Body'` adds the floor as an OUTPUT (an extra CONCLUSION conjunct) instead of a guard.  Now the PRODUCER
must SUPPLY it (`build'` returns the richer structure) while every CONSUMER gets it for FREE (projects it
out).  Opposite side of the arrow ⇒ opposite side pays — the R437/R438 collapse vs. the R439 supply-debt
are the two halves of one duality. -/

/-- `Body` with the floor moved to the CONCLUSION as an extra conjunct `extra`. -/
structure Body' (w : Nat) : Prop where
  content : w < 3
  extra : w < 3

/-- Producer of the conclusion-enriched field PAYS: `build'` must now establish BOTH conjuncts. -/
theorem mkContract'
    (hLoc : ∀ w, Balanced w → Located w) (build' : ∀ w, Located w → Body' w) :
    ∀ w, Balanced w → Floor w → Body' w :=
  fun w hbal _hfloor => build' w (hLoc w hbal)

/-- Consumer of the conclusion-enriched field gets the new conjunct for FREE — just projects it. -/
theorem consume' (C : ∀ w, Balanced w → Floor w → Body' w) (w : Nat)
    (hbal : Balanced w) (hfloor : Floor w) : w < 3 :=
  (C w hbal hfloor).extra

/-! ## The point, machine-checked. -/

/-- The old contract is false (counterexample), the new one holds (fix), and the witness flips role. -/
example : (¬ (∀ w, Balanced w → Body w)) ∧ (∀ w, Balanced w → Floor w → Body w) :=
  ⟨oldContract_false, newContract_holds⟩
/-- The cross-matched witness `5` passes the old guard yet fails the floor — excluded, as designed. -/
example : Balanced 5 ∧ ¬ Floor 5 := floorRejectsBadWindow

end Tests.Reflections.GuardFixBreaksItsCounterexample
