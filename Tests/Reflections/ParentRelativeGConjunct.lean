/-!
# Reflection 347 — a PARENT-RELATIVE recursion-guard conjunct rides the recursion's structural SITES, not the uniform IH adapter; widen the IH SIGNATURE, discharge at the descend/advance sites where the parent–child relation is in scope

Self-contained (core Lean, no `L4YAML` import) toy model of the PROBE that settled the live route
for the seq `RecSeqBody` fixpoint (`(i'-b-B2c-ih-recseqbody-step)`), the brick R346 handed forward.

R346 refuted the "narrow the emission root carrier" plan and pointed at two candidate carrier-free
routes for the step's per-window `FlowBodyContent`: (A) read its separator facts off the window's OWN
recursive output via `seqSeparatorFacts_of_recseqbody`, or (B) thread `FlowBodyContent` as an extra
recursion-guard (`G`) conjunct, seeded at the root from emission and propagated by the two landed
edges `flowBodyContent_descend`/`_advance`. The R347 PROBE picks (B) and discovers the precise reason
(A) is off the critical path AND the precise obstruction (B) must clear — neither of which is a
missing lemma.

THE DECISIVE FINDING. The new invariant `F` (here `FlowBodyContent`, ultimately its `bodySucc` field)
has a propagation edge that CONSUMES THE PARENT–CHILD RELATION: the descend edge builds the child's
`F` from the PARENT's `F` plus the descent opener (`flowBodyContent_descend` takes the parent
`h_content` + the opener/close/floor relation). A parent-relative conjunct therefore CANNOT be
re-established in the recursion's UNIFORM IH ADAPTER — that adapter sees only the child window's
INTRINSIC facts (`FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed ∧ close`), never how the child
descends from its parent. This is the [[ref-context-free-adapter-knot]] / R343 knot, now RESOLVED
rather than merely diagnosed: the four conjuncts already in `G` are themselves supplied not in the
adapter but at the recursion's STRUCTURAL CALL SITES (the seq oracle's descend call, the assembler's
advance call), where the parent–child relation IS in scope; the adapter just FORWARDS pre-established
facts. So the fix is to WIDEN the dispatch's IH SIGNATURE by the `F` conjunct and discharge it at
those same two sites via the LANDED edges. The adapter still just forwards.

Why route (A) is off the critical path. Reading `F` off the window's OWN recursive output is a
SAME-WINDOW CYCLE for the producing window (the output is the step's deliverable, not an input) and
REDUNDANT for child windows (the descend edge already builds the child `F` from the parent's). So
`seqSeparatorFacts_of_recseqbody` — the lemma R346's next-step title named — is NOT the route; the
three threaded `FlowBodyContent` edges (root `seqRoot_flowBodyContent`, descend
`flowBodyContent_descend`, advance `flowBodyContent_advance`, all landed) are.

Why the conjunct is NECESSARY (not avoidable). At a nested window the step needs its OWN `bodySucc`,
whose only carrier-free source is the parent's `F` via the descend edge — which needs the parent
relation, in scope only if `F` is threaded parent→child. A four-conjunct recursion at a nested window
knows only its own intrinsic facts, so it cannot manufacture its own `F`; hence the carrier was
introduced, and hence going carrier-free FORCES threading `F` as the fifth conjunct.

The toy below abstracts: `F`, an invariant whose only producers are a ROOT seed (no parent) and a
DESCEND edge (needs the parent); the structural-site supplier (POSITIVE, typechecks); the
uniform-adapter impossibility made positive as an inversion (`F` at a nested window CARRIES evidence
of a parent, so intrinsic-only data can never conjure it); and the same-window-cycle endo-map
(NEGATIVE, echoing R346's `carrier_route_is_a_loop`).
-/

namespace Tests.Reflections.ParentRelativeGConjunct

set_option autoImplicit false

/-! ## The intrinsic per-window facts (the existing four-conjunct `G`) and the parent-relative `F` -/

/-- The INTRINSIC per-window facts — re-derivable from the child window ALONE (toy
    `FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed ∧ close`).  The uniform IH adapter has exactly
    this and nothing more. -/
def Intrinsic (lo hi : Nat) : Prop := lo ≤ hi

/-- The PARENT-RELATIVE invariant `F` (toy `FlowBodyContent`, ultimately its `bodySucc` field).  Its
    ONLY producers are the ROOT seed (no parent) and the DESCEND edge (which needs the parent window
    plus a descent relation).  At a non-root window `F` can ONLY come from `descend`. -/
inductive F : Nat → Nat → Prop
  /-- ROOT seed: `F` at the root window (`lo = 0`), from an external EMISSION fact — no parent needed
      (toy `seqRoot_flowBodyContent`, off `seqRoot_safeBodyUnit`, recursion-independent). -/
  | root (hi : Nat) : F 0 hi
  /-- DESCEND edge: the child's `F` from the PARENT's `F` plus the descent relation `plo < lo` (toy
      `flowBodyContent_descend`, which takes the parent `h_content` + the opener/close/floor). -/
  | descend (plo phi lo hi : Nat) : plo < lo → F plo phi → F lo hi

/-! ## POSITIVE — `F` rides the structural SITES (root seed + descend supply where the parent is in scope) -/

/-- **POSITIVE (root seed).**  At the root window the emission fact seeds `F` with no parent — the
    [[ref-universal-producer-root-seed-first]] base. -/
theorem F_root_seed (hi : Nat) : F 0 hi := F.root hi

/-- **POSITIVE (structural-site supply).**  At a DESCEND site — where the parent window `(plo, phi)`
    and the descent relation `plo < lo` ARE in scope — the child's `F` is supplied directly.  This is
    the site the recursion's consumers (seq oracle descend / assembler advance) occupy; the conjunct
    is discharged HERE, not in the adapter. -/
theorem F_supply_at_descend (plo phi lo hi : Nat) (hrel : plo < lo) (hpar : F plo phi) : F lo hi :=
  F.descend plo phi lo hi hrel hpar

/-! ## NEGATIVE — the uniform IH adapter cannot re-establish a parent-relative conjunct -/

/-- **NEGATIVE (uniform-adapter impossibility, made positive).**  A uniform IH adapter receives ONLY a
    child window and its INTRINSIC fact — never a parent.  It can never manufacture `F lo hi` at a
    nested window, because any such `F` CARRIES a strictly-smaller parent (inversion): the only
    constructor that fires at `lo > 0` is `descend`, which demands a parent.  So no function
    `Intrinsic lo hi → F lo hi` exists for nested `lo`; `F` must be SUPPLIED at the structural site
    (above), not re-derived in the adapter.

    (The would-be adapter `fun (lo hi : Nat) (_ : Intrinsic lo hi) => (?? : F lo hi)` does not
    typecheck for `lo > 0` — there is no parent in scope to feed `F.descend`.  This inversion is the
    positive witness of that gap.) -/
theorem F_nonroot_carries_parent {lo hi : Nat} (h_pos : 0 < lo) (hF : F lo hi) :
    ∃ plo phi, plo < lo ∧ F plo phi := by
  cases hF with
  | root hi => exact absurd rfl (Nat.ne_of_gt h_pos)
  | descend plo phi lo hi hrel hpar => exact ⟨plo, phi, hrel, hpar⟩

/-! ## NEGATIVE — reading `F` off the window's OWN output is a same-window cycle (echoes R346) -/

/-- The step CONSUMES `F` to produce its output (toy: the output packages the very `F` the dispatch
    needed at the first entry). -/
def Out (lo hi : Nat) : Prop := F lo hi

/-- The step needs `F` as INPUT to produce `Out` (toy `recseqentry_window_dispatch`, which reads
    `h_content.bodySucc`). -/
theorem step_consumes_F {lo hi : Nat} (h : F lo hi) : Out lo hi := h

/-- Reading `F` back off the output (toy `seqSeparatorFacts_of_recseqbody`, route (A)). -/
theorem read_F_off_output {lo hi : Nat} (h : Out lo hi) : F lo hi := h

/-- **NEGATIVE (same-window cycle).**  Route (A) at the CURRENT window, fully composed, is an ENDO-map
    `F → F` with no base case — it presupposes its own input.  Reading the per-window fact off the
    window's OWN recursive output cannot SEED the window whose output is still being produced; it only
    relocates the dependency.  (Contrast `F_root_seed`, which produces `F` outright, and
    `F_supply_at_descend`, which produces a CHILD's `F` from a strictly-smaller-width parent.)  Same
    shape as R346's `carrier_route_is_a_loop`: an endo with no seed. -/
theorem own_output_is_a_loop {lo hi : Nat} (h : F lo hi) : F lo hi :=
  read_F_off_output (step_consumes_F h)

end Tests.Reflections.ParentRelativeGConjunct
