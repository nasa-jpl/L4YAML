/-!
# Reflection 308 — factor the descent into a FROM-LOCATED assembler before authoring it; the locator's DIRECTION is the residual's true shape

Self-contained (core Lean) toy of the producer-side factoring that landed
`seqEnclosingFacts_provider_of_located` (and made `seqEnclosingFacts_provider_root` its corollary).

The real situation: a universal producer `∀ window, Gate window → Deliverable window`, already split
into a ROOT seed + a DESCENT (`ref-root-seed-discriminator-not-from-gate`).  Before authoring the
descent, FACTOR it: lift the locator's eventual output — a located enclosing window `e` plus its
deliverable witness — as hypotheses into a FROM-LOCATED assembler that discharges the existential in
ONE line.  Then:

* the ROOT seed becomes a COROLLARY — the assembler at the fixed root witness with the
  infra-supplied deliverable (`ref-parametric-assembler-extraction`);
* the DESCENT becomes "produce the located enclosing + its deliverable for non-root windows" — the
  isolated locator residual, the trivial assemble removed.

The de-risk probe then reveals the locator's DIRECTION, which is the residual's true shape: a producer
quantified BOTTOM-UP over interior windows (`∀ interior, ∃ enclosing`) needs an INNER→OUTER locator,
which the established TOP-DOWN (outer→inner) recursion machinery does NOT provide.  So the residual is
genuinely NEW infrastructure (a backward enclosing/last-crossing scan), not a reuse of the descend
oracle — recognising the direction-mismatch prevents trying to discharge the descent top-down.

POSITIVE — the assembler is satisfiable on a nested window (the located enclosing exists, all
preconditions hold).  NEGATIVE — the root witness is wrong for a nested window (so the descent is
genuine), AND the top-down descent operation goes the OPPOSITE direction from the bottom-up locator
the producer needs (it strictly deepens; at the deepest interior it has no target, yet an enclosing
still exists).
-/

namespace Tests.Reflections.FromLocatedAssemblerDirection

set_option autoImplicit false

/-- A toy "window": `depth` = bracket-depth from the root origin, `seqTyped` = the gate condition
    (true at ANY depth, as the real `SeqTypedInterior` is). -/
structure Win where
  depth : Nat
  seqTyped : Bool
deriving DecidableEq

/-- The universal producer's GATE (toy `SeqTypedInterior`). -/
def Gate (w : Win) : Prop := w.seqTyped = true

/-- The per-window DELIVERABLE (toy of the `∃ loS hiS, … ∧ SafeBodyUnit …` existential): a located
    enclosing seq window `e` at whose level the window sits (`w.depth = e.depth`, toy of the re-seated
    `flowBracketBalance tokens loS a = 0`). -/
def Deliverable (w : Win) : Prop := ∃ e : Win, e.seqTyped = true ∧ w.depth = e.depth

/-- **The FROM-LOCATED assembler** (toy `seqEnclosingFacts_provider_of_located`) — lift the located
    enclosing `e` + its witness as hypotheses; the deliverable is ONE line.  No locate analysis: that
    is the isolated residual. -/
theorem assemble (w e : Win) (h_seq : e.seqTyped = true) (h_reseat : w.depth = e.depth) :
    Deliverable w := ⟨e, h_seq, h_reseat⟩

/-! ## ROOT seed = the assembler at the fixed root witness (a COROLLARY). -/

/-- The root window/body (toy outer seq `[2, size-2)`), infra-supplied. -/
def rootWin : Win := ⟨0, true⟩
theorem rootInfra : rootWin.seqTyped = true := rfl

/-- **The ROOT seed is now a corollary of the assembler** (toy `seqEnclosingFacts_provider_root`
    rewritten as `seqEnclosingFacts_provider_of_located … (seqRoot_safeBodyUnit …)`). -/
theorem rootSeed (w : Win) (h : w.depth = 0) : Deliverable w :=
  assemble w rootWin rootInfra h

example : Deliverable rootWin := rootSeed rootWin rfl

/-! ## POSITIVE — the assembler is satisfiable on a NESTED window (the descent's residual output). -/

/-- A nested gated window (toy `[3,6)` with `flowBracketBalance 2 3 = 1`). -/
def nestedWin : Win := ⟨2, true⟩
/-- Its located enclosing seq body, at the same level (toy inner seq `[3,6)`). -/
def nestedEncl : Win := ⟨2, true⟩

theorem nested_gated : Gate nestedWin := rfl
example : Deliverable nestedWin := assemble nestedWin nestedEncl rfl rfl

/-! ## NEGATIVE (1) — the ROOT witness is wrong for a nested window, so the descent is genuine. -/

/-- The root body is at depth `0`; the nested window at depth `2`; the re-seating `w.depth = root.depth`
    fails — the root seed is INAPPLICABLE to the nested window, exactly the
    `ref-root-seed-discriminator-not-from-gate` gap. -/
theorem root_wrong_for_nested : ¬ (nestedWin.depth = rootWin.depth) := by decide

/-! ## NEGATIVE (2) — the locator's DIRECTION: the producer needs INNER→OUTER, the machinery is OUTER→INNER. -/

/-- The toy outer / inner seq bodies of a nested `[[ … ]]`. -/
def outerBody : Win := ⟨0, true⟩
def innerBody : Win := ⟨1, true⟩

/-- **BOTTOM-UP** — what the producer NEEDS: given an interior window, its enclosing BODY (same level).
    This is the inner→outer locator, the descent's residual. -/
def locateEnclosing : Win → Option Win
  | ⟨0, _⟩ => some outerBody
  | ⟨1, _⟩ => some innerBody
  | _      => none

/-- **TOP-DOWN** — what the existing recursion machinery PROVIDES: given an enclosing body, descend to
    its strictly-deeper child (outer→inner). -/
def descendChild : Win → Option Win
  | ⟨0, _⟩ => some innerBody
  | _      => none

-- top-down STRICTLY DEEPENS (0 → 1):
#guard (descendChild outerBody).map (·.depth) == some 1
-- bottom-up does NOT deepen (a depth-1 window's enclosing body is at depth 1):
#guard (locateEnclosing innerBody).map (·.depth) == some 1
-- the deepest interior has an enclosing (bottom-up succeeds) but NO descent target (top-down fails):
-- the top-down operation returns `none` exactly where the producer must return a witness ⇒ the
-- residual is new inner→outer infrastructure, not a reuse of the outer→inner descend.
#guard descendChild innerBody == none
#guard locateEnclosing innerBody != none

end Tests.Reflections.FromLocatedAssemblerDirection
