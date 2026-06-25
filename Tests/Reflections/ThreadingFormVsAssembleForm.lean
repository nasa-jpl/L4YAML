/-! # Reflection 522 — threading form vs assemble form (the map `after_fe` carrier asymmetry)

The L4YAML carrier-free recursion threads a per-window *content guard* and, separately, an *assembler*
projects per-window facts into a structured bundle (`MapBodyProps`).  This demo pins the reflection that
landed `mapWindow_mapBodyProps_general` (R522, `SeqInteriorSeparators.lean`):

* **A per-window separator-successor fact has TWO non-interconvertible shapes.**
  - the **THREADING form** — *conditional* (`,` whose successor is NOT content ⟹ the successor is a
    key).  This is what the recursion's *advance* edge re-establishes step-by-step
    (`FlowBodyContentDeepMap.feKey`): the `¬ content` premise is exactly what lets the advance fire
    without proving the content-exclusion, because the driver SUPPLIES the next head directly.
  - the **ASSEMBLE form** — *unconditional* (`,` ⟹ the successor is a key, full stop).  This is what a
    one-shot assembler demands (`MapBodyProps.after_fe`, M2).

  The threading form does NOT imply the assemble form: deriving the unconditional fact from the
  conditional one would require proving the `¬ content` premise FOR FREE — the very content-exclusion the
  threading form took as a hypothesis.  We witness this with a concrete `seqLike` stream where the
  threading form holds *vacuously* (its `¬ content` premise fails exactly where the assemble form would
  have to fire) yet the assemble form is FALSE.

* **A parallel carrier may internalize the assemble form on one axis but omit it on the other.**  The
  SEQ carrier `SeqInteriorSeparators` bundles the unconditional separator-successor fact
  (`noTrailingSepFact`), so the seq bridge self-sources it.  The MAP carrier `MapInteriorSeparators`
  bundles only the six adjacency facts (`MapGrammarFacts`) — it OMITS the comma→key fact — so the map
  bridge `mapWindow_mapBodyProps_general` must take `after_fe` as a SUPPLIED hypothesis (the recorded
  seq/map carrier asymmetry, here pinned to its exact entry point).  We model both bridges: the seq one
  reads the fact off the carrier; the map one takes it as an argument.

Self-contained core Lean (no imports).  `demo` is the non-implication `threading ⊬ assemble`; it carries
`[propext, Quot.sound]` (the `Quot.sound` from the `DecidableEq Tok` derivation) — no `Classical.choice`
and crucially no `sorryAx`.
-/

namespace ThreadingFormVsAssembleForm

set_option autoImplicit false

/-- Toy token alphabet: `.scalar` is the only "content" token; `.sep` is the depth-`0` `.flowEntry`. -/
inductive Tok where
  | scalar | key | sep | close
deriving DecidableEq

/-- Content tokens (Bool for clean decidability): only a scalar (the toy of `isFlowContentStart`). -/
def isContent : Tok → Bool
  | .scalar => true
  | _ => false

/-- **THREADING form** (toy of `FlowBodyContentDeepMap.feKey`): a `.sep` whose successor is NOT content
    is followed by a `.key`.  Conditional — the `¬ content` premise is what the recursion's advance edge
    relies on (it never proves it; the driver supplies the next head). -/
def FeThreading (f : Nat → Tok) (n : Nat) : Prop :=
  ∀ k, k < n → f k = .sep → isContent (f (k + 1)) = false → f (k + 1) = .key

/-- **ASSEMBLE form** (toy of `MapBodyProps.after_fe`, M2): a `.sep` is *unconditionally* followed by a
    `.key`.  This is what the one-shot assembler `mapBodyProps_assemble` demands. -/
def AfterFe (f : Nat → Tok) (n : Nat) : Prop :=
  ∀ k, k < n → f k = .sep → f (k + 1) = .key

/-- A SEQ-style stream: after the `.sep` (a comma in a *seq* body) comes CONTENT, not a key. -/
def seqLike : Nat → Tok
  | 0 => .sep | 1 => .scalar | _ => .close

/-- The THREADING form holds on `seqLike` — VACUOUSLY: its `¬ content` premise is false exactly at the
    one separator (`isContent (seqLike 1) = isContent .scalar = true`), so it promises nothing there. -/
theorem seqLike_threading : FeThreading seqLike 1 := by
  intro k hk hsep hnc
  have hk0 : k = 0 := by omega
  subst hk0
  exact absurd hnc (by decide)

/-- Yet the ASSEMBLE form FAILS on `seqLike`: it would demand `seqLike 1 = .key`, but `seqLike 1` is a
    `.scalar`.  So the threading form does NOT carry the assemble form. -/
theorem seqLike_not_afterFe : ¬ AfterFe seqLike 1 := by
  intro h
  exact absurd (h 0 (by omega) (by decide)) (by decide)

/-- **The kernel — threading ⊬ assemble**, witnessed at one stream.  The conditional separator-successor
    fact cannot be promoted to the unconditional one without re-proving its own `¬ content` premise. -/
theorem threading_not_implies_afterFe :
    ¬ (∀ f n, FeThreading f n → AfterFe f n) := fun h =>
  seqLike_not_afterFe (h seqLike 1 seqLike_threading)

/-- A toy "body props" bundle the assembler builds: a head fact plus the *unconditional* separator fact.
    (Toy of `MapBodyProps`'s `key_start` + `after_fe`.) -/
structure BodyProps (f : Nat → Tok) (n : Nat) : Prop where
  headKey : f 0 = .key
  afterFe : AfterFe f n

/-- **The MAP bridge** (toy of `mapWindow_mapBodyProps_general`): the carrier OMITS the comma→key fact,
    so the assemble form `after_fe` is a SUPPLIED hypothesis. -/
theorem mapBridge (f : Nat → Tok) (n : Nat)
    (h_head : f 0 = .key) (h_after : AfterFe f n) : BodyProps f n :=
  ⟨h_head, h_after⟩

/-- A SEQ-style carrier that INTERNALIZES the unconditional separator fact (toy of how
    `SeqInteriorSeparators` bundles `noTrailingSepFact`). -/
def SeqCarrier (f : Nat → Tok) (n : Nat) : Prop := f 0 = .key ∧ AfterFe f n

/-- **The SEQ bridge** (toy of `seqWindow_flowBodyContent_seq_general`): the carrier already carries the
    assemble form, so the bridge SELF-SOURCES it — no supplied hypothesis.  Same target `BodyProps` as
    the map bridge; only WHERE `after_fe` comes from differs (carrier here, argument there). -/
theorem seqBridge (f : Nat → Tok) (n : Nat) (h : SeqCarrier f n) : BodyProps f n :=
  ⟨h.1, h.2⟩

/-- **The demo deliverable**: the non-implication that forces the asymmetry — because the threading form
    cannot produce the assemble form, the map carrier (which omits it) must defer it to the driver. -/
theorem demo : ¬ (∀ f n, FeThreading f n → AfterFe f n) := threading_not_implies_afterFe

end ThreadingFormVsAssembleForm

-- Axiom audit (machine-checked: `#guard_msgs` pins the profile and fails the build if it drifts).
-- `[propext, Quot.sound]` — the `Quot.sound` comes from the `DecidableEq Tok` derivation; no
-- `Classical.choice`, and crucially no `sorryAx` (the real `mapWindow_mapBodyProps_general` carries
-- `[propext, Classical.choice, Quot.sound]` from `mapBodyProps_assemble`'s typed locators, still
-- `sorryAx`-free — it never touches the tainted `scanFiltered_emitMap_nonempty_structure`).
/-- info: 'ThreadingFormVsAssembleForm.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThreadingFormVsAssembleForm.demo
