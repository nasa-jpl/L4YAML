/-!
# Reflection 385 — a recursion's ROOT SEED derives SHAPE and defers VALUE; 'not the descent's debt'
does NOT mean 'derive it inline'

Self-contained core-Lean toy of L4YAML BRICK D's root seed (`nestedSeq_recseqentry_locate_root_seed`):
how to draw the derive-vs-hypothesis line when packaging the base-case guard a `Nat.strongRecOn` driver
consumes.

The prior root-seed reflection (`ref-root-seed-discriminator-not-from-gate`) says the TARGET-relative
discriminators are hypotheses = the descent's DEBT.  The trap is its converse: that everything NOT debt
is the seed's own to derive.  It is not.  The right line is:

* DERIVE inline only **positional SHAPE** fields (here `shape`, an `omega`) and fields with a **landed
  flat producer** you call in one line (here `produced`, via `flatProducer` — the `recBody :=
  seqRoot_recseqbody …` analog).
* take as a HYPOTHESIS **everything that needs fresh value reasoning** — and that splits into TWO kinds:
  the **DEBT** (`debt`, target-relative, the consumer's precondition, the descent already threads it) and
  the **DEFERRED-STRUCTURAL** (`frame`, an OUTER-FRAME value-fact, emission-derivable but only via a
  SEPARATE brick — so a NEW owed obligation, NOT target-debt yet STILL a hypothesis).

POSITIVE: `rootSeed` — near-ZERO proof content (one `omega`, one producer call, two hypotheses).
NEGATIVE / de-risk: `frame_independent_of_shape` — `frame` is independent of the window shape AND has no
producer, so it MUST be a hypothesis even though it is not target-debt; `produced_has_producer` shows the
contrast (a value-fact WITH a producer is derived inline).
-/

namespace Tests.Reflections.RootSeedDerivesShapeDefersValue

set_option autoImplicit false

-- value-level predicates (NOT derivable from the window's positional shape)
def EmissionInput (r : Nat) : Prop := r = 6     -- the "h_scan"-style input the flat producer consumes
def Produced (r : Nat) : Prop := r % 2 = 0       -- ~ recBody: a value-fact WITH a landed flat producer
def FrameFact (r : Nat) : Prop := r % 2 = 0      -- ~ domain/window: outer-frame value, NO producer yet
def TargetFact (t : Nat) : Prop := t % 3 = 0     -- ~ typed/close/…: target value, consumer precondition

/-- The landed FLAT-root producer (mirrors `seqRoot_recseqbody`): turns the emission input into the
    value-fact in ONE line.  Its EXISTENCE is what lets the root seed DERIVE `produced` inline. -/
theorem flatProducer (r : Nat) (h : EmissionInput r) : Produced r := by
  unfold EmissionInput Produced at *; omega

/-- The recursion's per-window GUARD, at root `r`, fixed target `t`, walking window `w`. -/
structure Guard (r t w : Nat) : Prop where
  shape    : w + 2 ≤ r        -- SHAPE: positional, a function of the window alone
  produced : Produced r       -- VALUE with a landed flat producer → DERIVED inline
  frame    : FrameFact r      -- VALUE, OUTER-FRAME, no producer yet → DEFERRED-STRUCTURAL hypothesis
  debt     : TargetFact t     -- VALUE, TARGET-relative → DEBT hypothesis

/-! ## POSITIVE — the root seed at the outer window `w = 2`: derive SHAPE + the PRODUCED value, defer
the rest.  Near-ZERO proof content: one `omega` for shape, one producer call, two hypotheses. -/

theorem rootSeed (r t : Nat)
    (h_emission : EmissionInput r)     -- feeds the flat producer (the "h_scan")
    (h_frame : FrameFact r)            -- DEFERRED-STRUCTURAL: a separate emission brick will supply this
    (h_debt : TargetFact t)            -- DEBT: the consumer/locator supplies this as a precondition
    (h_r : 4 ≤ r) :                    -- the root window is positionally well-formed
    Guard r t 2 :=
  ⟨by omega, flatProducer r h_emission, h_frame, h_debt⟩

/-- The DESCENT threads `produced`/`frame`/`debt` (value-facts pass: same `r`, same `t`) and re-derives
    SHAPE for the shrunk window — confirming the DEBT's discharge is DONE in the step, not owed. -/
theorem descend {r t w : Nat} (g : Guard r t w) (w' : Nat) (h : w' + 2 ≤ r) : Guard r t w' :=
  ⟨h, g.produced, g.frame, g.debt⟩

/-! ## NEGATIVE / de-risk — why FRAME (and DEBT) MUST be hypotheses, while PRODUCED need not.

The point the prior root-seed memory omits: `frame` is an OUTER-FRAME value-fact, NOT target-debt, yet
it is STILL a hypothesis — because (a) it is independent of the window's shape, and (b) unlike
`produced`, it has NO landed producer to call inline.  'Not target-debt' does NOT mean 'derive it'. -/

/-- `frame` is genuinely independent of the positional SHAPE: a shape-satisfying `r` can fail it.  So a
    root seed CANNOT derive it from shape — it is a hypothesis (a deferred emission brick). -/
theorem frame_independent_of_shape : ∃ r, (2 + 2 ≤ r) ∧ ¬ FrameFact r :=
  ⟨5, by omega, by unfold FrameFact; decide⟩

/-- Same independence for the target DEBT — the contrasting hypothesis kind (consumer precondition). -/
theorem debt_independent_of_shape : ∃ t, (2 + 2 ≤ t) ∧ ¬ TargetFact t :=
  ⟨4, by omega, by unfold TargetFact; decide⟩

/-- The asymmetry that pins the line: `produced` is a value-fact too, but it HAS a flat producer, so the
    root seed derives it inline (no hypothesis).  `frame` has none ⇒ hypothesis.  The derive/hypothesis
    split is 'landed-producer-or-positional' vs 'needs-value-reasoning-with-no-producer'. -/
theorem produced_has_producer (r : Nat) (h : EmissionInput r) : Produced r := flatProducer r h

end Tests.Reflections.RootSeedDerivesShapeDefersValue
