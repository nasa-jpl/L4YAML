/-!
# Reflection 307 — the ROOT seed of a universal-over-gated-windows producer carries a DISCRIMINATOR the gate cannot supply

Self-contained (core Lean) toy of `(i'-b-locator)`'s base case `seqEnclosingFacts_provider_root`.

The real situation: a universal producer `∀ window, Gate window → Deliverable window` (here the
enclosing-facts `provider`, gated by `SeqTypedInterior`) is split into a ROOT seed + a DESCENT
(per `ref-universal-producer-root-seed-first`).  At the root (the outer seq `[2, size-2)`) the
deliverable is supplied directly by infra (`seqRoot_safeBodyUnit` ∘ the enclosing-facts bundle).

The non-obvious part: the root seed does NOT consume the universal's `Gate`.  The gate is satisfied
by seq-typed windows at *any* nesting depth — including the descent's own targets — so it cannot tell
a root-level window from a nested one.  The root seed instead carries the **top-level discriminator**
`flowBracketBalance tokens 2 a = 0` (the window starts at the outer seq's depth), which is strictly
STRONGER than the gate and NOT derivable from it.  That is correct, not a defect: the discriminator
is the SAME quantity the descent re-establishes per level (each `descend` re-seats the origin to the
located child opener) — the root seed receives it as a hypothesis; the descent produces it from the
located bracket.

Toy: a `Win` carries `bal` (balance from the outer origin; `0` ⇒ at the root level) and `seqTyped`
(the gate condition, true at any depth).  `Deliverable w` = an enclosing seq-typed window at whose
level `w` sits (`w.bal = encl.bal`, the re-seated discriminator).  `descentStep` takes the LOCATED
enclosing as a hypothesis (in reality recovered by `recseqentry_seqbracket_oracle`); `rootSeed` is
exactly `descentStep` specialised to the outer window, with the discriminator `AtRoot` plugged into
the re-seat slot — making the shared discriminator literal.

NEGATIVE — the gate does NOT supply the discriminator: a nested gated window `⟨2, true⟩` satisfies
`Gate` but not `AtRoot`, and the OUTER window is the wrong enclosing for it (`w.bal = 0` fails); so
the nested case is INAPPLICABLE to the root seed and genuinely needs the descent's located enclosing.
-/

namespace Tests.Reflections.RootSeedDiscriminatorNotFromGate

set_option autoImplicit false

/-- A toy "window": `bal` = bracket-balance from the OUTER origin (`0` ⇒ at the outer/root level),
    `seqTyped` = the universal producer's GATE condition (true at ANY depth). -/
structure Win where
  bal : Nat
  seqTyped : Bool

/-- The universal producer's GATE (toy `SeqTypedInterior`) — satisfied by seq-typed windows at ANY
    depth, so it cannot discriminate root-level windows from nested ones. -/
def Gate (w : Win) : Prop := w.seqTyped = true

/-- The ROOT discriminator (toy `flowBracketBalance tokens 2 a = 0`) — the window starts at the OUTER
    seq's depth.  Strictly STRONGER than `Gate`; NOT derivable from it. -/
def AtRoot (w : Win) : Prop := w.bal = 0

/-- The per-window DELIVERABLE (toy of the three enclosing facts at `⟨loS, hiS⟩`): an enclosing
    seq-typed window `encl` at whose level `w` sits (`w.bal = encl.bal`, the re-seated discriminator
    `flowBracketBalance tokens loS a = 0`). -/
def Deliverable (w : Win) : Prop := ∃ encl : Win, encl.seqTyped = true ∧ w.bal = encl.bal

/-- The outer seq window (toy `[2, size-2)`), supplied directly by infra. -/
def outerWin : Win := ⟨0, true⟩

/-- INFRA at the root (toy `seqRoot_safeBodyUnit` ∘ `seqEnclosingFacts_of_windowed_safebodyunit`):
    the outer window is seq-typed, delivered directly with no recursion. -/
theorem rootInfra : outerWin.seqTyped = true := rfl

/-- **The DESCENT step** (toy of the inductive locator) — given the LOCATED enclosing window `encl`
    (in reality recovered by `recseqentry_seqbracket_oracle`) that is seq-typed and at whose level the
    window sits, the deliverable holds.  The descent does NOT invent `encl`; it receives the located
    bracket and its re-seated discriminator `h_reseat`. -/
theorem descentStep (w encl : Win) (h_seq : encl.seqTyped = true) (h_reseat : w.bal = encl.bal) :
    Deliverable w := ⟨encl, h_seq, h_reseat⟩

/-- **The ROOT seed** (toy `seqEnclosingFacts_provider_root`) — `descentStep` specialised to the outer
    window, with the discriminator `AtRoot` plugged into the re-seat slot.  It takes the discriminator
    `hr`, NOT the gate: the gate cannot supply it.  The shared discriminator is literal — `rootSeed`
    IS `descentStep … outerWin … hr`. -/
theorem rootSeed (w : Win) (hr : AtRoot w) : Deliverable w :=
  descentStep w outerWin rootInfra hr

/-! ## POSITIVE — a root-level gated window: the seed packages the infra-delivered outer enclosing. -/

def rootWin : Win := ⟨0, true⟩

theorem gate_root : Gate rootWin := rfl
theorem atRoot_root : AtRoot rootWin := rfl

example : Deliverable rootWin := rootSeed rootWin atRoot_root

-- the discriminator holds at the root level:
#guard rootWin.bal == 0

/-! ## NEGATIVE — the gate does NOT supply the discriminator. -/

/-- A nested gated window: seq-typed (so `Gate` holds) but two brackets deep. -/
def nestedWin : Win := ⟨2, true⟩

theorem gate_nested : Gate nestedWin := rfl

/-- The gate holds yet the discriminator fails — `Gate` cannot tell root-level from nested. -/
theorem not_atRoot_nested : ¬ AtRoot nestedWin := by unfold AtRoot; decide

-- the gate is satisfied (true) but the discriminator is not (bal ≠ 0):
#guard nestedWin.seqTyped == true
#guard nestedWin.bal != 0

/-- The OUTER window is the WRONG enclosing for the nested window: the re-seating `w.bal = outer.bal`
    (`= 0`) fails.  So the root seed is INAPPLICABLE here (its `AtRoot` premise is unsatisfiable) and
    the nested case genuinely needs the descent's LOCATED enclosing at level `2`. -/
theorem outer_wrong_for_nested : ¬ (nestedWin.bal = outerWin.bal) := by decide

/-- The descent supplies the same deliverable for the nested window via a DIFFERENT, located enclosing
    at the window's own level (the re-seated discriminator `2 = 2`) — not the outer window. -/
example : Deliverable nestedWin := descentStep nestedWin ⟨2, true⟩ rfl rfl

end Tests.Reflections.RootSeedDiscriminatorNotFromGate
