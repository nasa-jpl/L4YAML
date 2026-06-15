/-!
# Reflection 441 — docking a producer by currying an ALREADY-PROVEN composition brick discharges the
# producer's CONCLUSION de-risk for free (import the proof), but RELOCATES the unsatisfiability risk
# onto every residual HYPOTHESIS the dock threads.  Each threaded primitive must be independently
# PROBED for truth — else you rebuild the same vacuous-by-false-hypothesis trap one layer up.

Self-contained (core Lean, no `L4YAML` import) toy of the R441 finding — STEP D continued: DOCK the
floored seq `h_seq_rec` producer, the payoff of R440's conduit flooring.

Context.  R440 made `flowSubrangesOk_of_window_producers`'s `h_seq_rec` slot textually identical to the
floored producer `seqRec_of_carrier_and_windowFacts_seq`'s conclusion.  R441 DOCKS that producer: it
consumes a root carrier + a `windowFacts` provider, and the provider is assembled by CURRYING the proven
R432 brick `seqWindowFacts_of_emit_and_primitives` (which derives `FlowBodyWindow ∧ FlowBodyContentDeepSeq
∧ SeqEnclosed` from the window guards + emit context + a per-window fold-totality `h_fold_pre`).

Findings:

* **Dock-by-import discharges the CONCLUSION de-risk for free.**  The producer's `windowFacts` hypothesis
  is satisfiable BY CONSTRUCTION: its three output facts are a theorem (`seqWindowFacts_of_emit_and_primitives`
  is already proven), DERIVED from the guards, not owed.  No fresh witness is needed for the conclusion —
  importing the proof IS the satisfiability check.  (Contrast a conclusion INDEPENDENT of the guards: there
  a witness probe would be mandatory.)

* **But the dock RELOCATES the unsatisfiability risk onto the threaded HYPOTHESES.**  Currying the proven
  brick leaves residual hypotheses (here a per-window fold-totality `h_fold_total`).  A `lemma H → C` with
  unsatisfiable `H` type-checks yet is vacuous — exactly the R433 trap (the un-floored window universal was
  unsatisfiable on real output) one layer up.  So docking does NOT eliminate the unsat risk; it moves it
  from the conclusion to the threaded primitives.

* **Probe each threaded primitive for truth.**  The window guards and the interior `WellTyped` are bracket
  facts available at the consume site; the one primitive whose truth is not self-evident is the fold-totality.
  Probe it.  The strong move: prove the GENERAL `∀ m` form (not a single prefix) by routing through a
  whole-stream fact (`tfold (some 0) wholeStream = some 0`, the `WellTyped` analog) + a prefix lemma
  (`tfold_prefix_some`, the `WellTyped_prefix_some` analog).  That both confirms the thread is non-vacuous
  AND NAMES the future discharge route (a whole-stream WellTyped fact, fed through the prefix lemma).

The transferable rule: when you DOCK a producer by currying a proven composition brick, the producer's
conclusion satisfiability is free (import), but each residual hypothesis you thread inherits the
unsatisfiability risk — probe each for truth before you rely on the dock, and prefer a probe that proves
the general form via a whole-stream → per-prefix lemma (it doubles as the discharge route's signpost).

The toy models the proven brick (`assembled`, conclusion derived from guard + fold-totality), the producer
(`producer`, root carrier + windowFacts → deliverable via a real `.2` projection), the dock (`docked`,
producer ∘ providerOfContext), the RELOCATION trap (a fold-totality stated where it is FALSE —
`badStream` underflows — makes `∀ w, FoldPre badStream w` false, so a careless thread is vacuous), and the
real case (`goodStream` is whole-stream-OK ⇒ every prefix folds to some, the general `∀ w` form proven
mechanically).
-/

namespace Tests.Reflections.DockImportsConclusionProbesThreadedHyps

set_option autoImplicit false

/-! ## PART 0 — a toy bracket-fold (`btFold` analog) and its prefix-some lemma (`WellTyped_prefix_some`).

`tfold` runs a depth counter across a list of deltas (`+1` open, `-1` close, else no-op), returning
`none` the moment a close underflows depth `0` — the toy of `btFold`'s `none`-absorbing underflow. -/

/-- One fold step: `+1` pushes, `-1` pops (underflow ⇒ `none`), anything else is the identity. -/
def tstep (n : Nat) (d : Int) : Option Nat :=
  if d = 1 then some (n + 1)
  else if d = -1 then (match n with | 0 => none | k + 1 => some k)
  else some n

/-- Fold the depth across a delta list; `none` is absorbing via `bind`. -/
def tfold (s0 : Option Nat) (l : List Int) : Option Nat :=
  l.foldl (fun acc d => acc.bind (fun n => tstep n d)) s0

/-- `tfold` over a concatenation threads the intermediate stack (the `btFold_append` analog). -/
theorem tfold_append (a b : List Int) (s0 : Option Nat) :
    tfold s0 (a ++ b) = tfold (tfold s0 a) b := by
  simp [tfold, List.foldl_append]

/-- `none` is absorbing — once underflowed, the fold stays `none` (the `btFold_none` analog). -/
theorem tfold_none (b : List Int) : tfold none b = none := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    simp only [tfold, List.foldl_cons] at ih ⊢
    exact ih

/-- **A prefix of a whole-stream-OK fold never underflows** — it folds to `some` (the
    `WellTyped_prefix_some` analog: `none` is absorbing, so an underflowing prefix would force the whole
    fold to `none ≠ some 0`).  This is the lemma that turns a WHOLE-stream fact into fold-totality at
    EVERY prefix. -/
theorem tfold_prefix_some (a b : List Int) (h : tfold (some 0) (a ++ b) = some 0) :
    ∃ s, tfold (some 0) a = some s := by
  rw [tfold_append] at h
  cases ha : tfold (some 0) a with
  | none => rw [ha, tfold_none] at h; exact absurd h (by simp)
  | some s => exact ⟨s, rfl⟩

/-! ## PART 1 — the per-window pieces and the ALREADY-PROVEN composition brick.

`Guard` is the window-shape guard, `FoldPre` the per-window fold-totality PRIMITIVE (the threaded
residual), `Triple` the DERIVED conclusion (the `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ SeqEnclosed`
analog — here a fold-witness bundled with a numeric bound).  `assembled` is the proven brick: its
conclusion is DERIVED from the guard + the in-scope bound + the threaded `FoldPre`. -/

/-- The window-shape guard (toy of the eight bracket/floor guards). -/
abbrev Guard (w : Nat) : Prop := w % 2 = 0

/-- The per-window fold-totality primitive (toy of `h_fold_pre`): the prefix folds to `some`. -/
abbrev FoldPre (s : List Int) (w : Nat) : Prop := ∃ k, tfold (some 0) (s.take w) = some k

/-- The derived conclusion (toy of the three `windowFacts` facts): the fold-witness AND a numeric bound. -/
abbrev Triple (s : List Int) (w : Nat) : Prop := FoldPre s w ∧ w ≤ 4

/-- **The proven composition brick** (toy of `seqWindowFacts_of_emit_and_primitives`).  Its conclusion is
    DERIVED: the bound from the guard + the in-scope shape bound, the fold-witness from the threaded
    `FoldPre`.  `hf` is genuinely CONSUMED (it supplies `Triple`'s first conjunct) — modelling that
    `h_fold_pre` is real content the brick needs, not decoration. -/
theorem assembled (s : List Int) (w : Nat)
    (hg : Guard w) (hbound : w < 6) (hf : FoldPre s w) : Triple s w :=
  ⟨hf, by simp only [Guard] at hg; omega⟩

/-! ## PART 2 — the producer (toy of `seqRec_of_carrier_and_windowFacts_seq`).

It consumes a ROOT CARRIER (orthogonal to the windowFacts dock) + a `windowFacts` provider, and yields the
DELIVERABLE through a real `.2` projection (the `seqWindowRecSeqBody_seq` coercion analog). -/

/-- The root carrier (toy of `SeqInteriorSeparators` — a separate residual, orthogonal to windowFacts). -/
abbrev RootCarrier : Prop := True

/-- The deliverable (toy of `RecSeqBody`) — strictly WEAKER than `Triple`, so the producer coerces by `.2`. -/
abbrev Deliverable (w : Nat) : Prop := w ≤ 4

/-- The producer: root carrier + windowFacts provider → deliverable.  The `.2` is a genuine (non-`id`)
    projection that drops `Triple`'s fold-witness. -/
theorem producer (s : List Int) (_rc : RootCarrier)
    (windowFacts : ∀ w, Guard w → w < 6 → Triple s w) :
    ∀ w, Guard w → w < 6 → Deliverable w :=
  fun w hg hb => (windowFacts w hg hb).2

/-! ## PART 3 — THE DOCK: curry the proven brick with a threaded fold-totality, plug into the producer. -/

/-- The windowFacts provider, ASSEMBLED by currying the proven `assembled` with a per-window fold-totality
    supplier (toy of `seqWindowFacts_provider_of_context`).  The conclusion is imported from `assembled` —
    no fresh witness. -/
theorem providerOfContext (s : List Int) (h_fold_total : ∀ w, FoldPre s w) :
    ∀ w, Guard w → w < 6 → Triple s w :=
  fun w hg hb => assembled s w hg hb (h_fold_total w)

/-- **The dock** (toy of `seqHRec_of_root_and_context`): `producer ∘ providerOfContext`.  The conclusion is
    FREE (imported via `assembled`); the residual is the root carrier + the threaded `h_fold_total`. -/
theorem docked (s : List Int) (rc : RootCarrier) (h_fold_total : ∀ w, FoldPre s w) :
    ∀ w, Guard w → w < 6 → Deliverable w :=
  producer s rc (providerOfContext s h_fold_total)

/-! ## PART 4 — the de-risk the dock RELOCATES onto the threaded hyp: probe `h_fold_total`'s truth.

The dock did not remove the unsatisfiability risk — it moved it to `h_fold_total`.  A careless thread (a
fold-totality stated where it is FALSE) makes the whole dock vacuous: the R433 trap one layer up. -/

/-- A stream that UNDERFLOWS: `[+1, -1, -1]` pops below depth `0` at prefix `3`. -/
def badStream : List Int := [1, -1, -1]

/-- **The RELOCATION trap**, machine-checked: a GENERAL `∀ w, FoldPre badStream w` is FALSE (prefix `3`
    underflows to `none`).  Threading THIS as `h_fold_total` would type-check yet leave `docked` vacuous —
    the exact R433 failure (an unsatisfiable threaded hypothesis), now one layer up at the dock. -/
theorem foldTotal_false_on_badStream : ¬ (∀ w, FoldPre badStream w) := by
  intro h
  obtain ⟨k, hk⟩ := h 3
  have hbad : tfold (some 0) (badStream.take 3) = none := by decide
  rw [hbad] at hk
  exact absurd hk (by simp)

/-- A WELL-bracketed stream: `[+1, +1, -1, -1]` folds whole to `some 0`. -/
def goodStream : List Int := [1, 1, -1, -1]

/-- The WHOLE-stream fact (toy of `WellTyped tokens.toList`): the full fold returns to depth `0`. -/
theorem goodStream_wholeOk : tfold (some 0) goodStream = some 0 := by decide

/-- **The probe, in its strong GENERAL form**: from the whole-stream fact, EVERY prefix folds to some — via
    `tfold_prefix_some` (the `WellTyped_prefix_some` analog).  This both confirms the thread is non-vacuous
    AND names the discharge route: a whole-stream-OK fact fed through the prefix lemma. -/
theorem foldTotal_true_on_goodStream : ∀ w, FoldPre goodStream w := by
  intro w
  exact tfold_prefix_some (goodStream.take w) (goodStream.drop w)
    (by rw [List.take_append_drop]; exact goodStream_wholeOk)

/-! ## The point, machine-checked. -/

/-- A false thread is vacuous (the relocated unsat risk); the real dock holds once the threaded
    fold-totality is PROVED true.  Half-fix → whole-fix is exactly probing the threaded primitive. -/
example :
    (¬ (∀ w, FoldPre badStream w)) ∧
    (∀ w, Guard w → w < 6 → Deliverable w) :=
  ⟨foldTotal_false_on_badStream, docked goodStream trivial foldTotal_true_on_goodStream⟩

end Tests.Reflections.DockImportsConclusionProbesThreadedHyps
