module


@[expose] public section Blanket

/-!
# Reflection 612 — an unclosable case arm has three destinations

A case analysis over an implementation step hands you one goal per arm. When an
arm will not close, the goal is in exactly one of three places, and they are
**not distinguishable by staring at the goal** — every one of them looks like
"refute this arm":

1. **Refutable, but the fact lives in the CALLER.** The step alone permits the
   arm; the caller's post-check rejects it. Hoist the fact into the lemma's
   statement as a hypothesis — the caller already has it, so the cost is one
   argument, not a proof.
2. **Refutable, but the fact lives in a THREADED INVARIANT.** Some earlier step
   established a state relation that kills the arm. Thread it (folding it into
   an existing guarded conjunct beats adding a tuple slot).
3. **Not refutable at all — the arm really fires.** The implementation accepts
   input the specification has no production for. This is a DEFECT, not proof
   work, and no amount of vocabulary will close it.

Destination 3 is the cheapest to *test* and the most expensive to *discover
late*: one runtime probe on a concrete input separates it from 1 and 2 in
seconds, whereas finding it by failing to prove the arm costs however long you
spend building frame vocabulary first. **So probe before you thread.**

The toy below is the smallest faithful model of L4YAML's `accum_step_*` family:
`scan` is the step, `scanAll` the caller loop, `prodB` the grammar. All three
destinations occur, and `dead_arm_and_live_arm_look_alike` is the crux — two
refutations of the *same shape* in the same case tree, one true and one false.

L4YAML instances (Fix A β.3, 2026-08-06):
* destination 1 — the EOF site: `scanLoop`'s `unterminatedFlowCollection`
  post-check is what rules out an open flow at end of input.
* destination 2 — the structural site: `allowDirectives` is cleared before any
  flow can open, so `scanDirective` cannot fire inside one.
* destination 3 — the content site (DOCS item 9c): the scanner accepts a block
  scalar inside a flow collection (`[a, |…]` scans clean), but `SFlowContent`
  has no literal/folded production. The sorry was never closable.

`lake build Tests.Reflections.UnclosableArmThreeDestinations`
-/

namespace UnclosableArmThreeDestinations

/-- Token alphabet. `pct` opens a directive, `bar` opens a block scalar. -/
inductive Tok where
  | atom
  | comma
  | bar
  | pct
  deriving DecidableEq, Repr

/-- Scanner state: `depth` = flow nesting, `fresh` = "a directive is still legal here". -/
structure St where
  depth : Nat
  fresh : Bool
  deriving DecidableEq, Repr

/-- The implementation's one step. Note `bar` is accepted at **any** depth. -/
def scan (s : St) (t : Tok) : Option St :=
  match t with
  | .pct   => if s.fresh then some { s with fresh := false } else none
  | .comma => if 1 ≤ s.depth then some { s with fresh := false } else none
  | .atom  => some { s with fresh := false }
  | .bar   => some { s with fresh := false }

/-- The caller loop. Its `[]` arm is the post-check — an open flow at end of
input is rejected *here*, nowhere else. -/
def scanAll : St → List Tok → Option St
  | s, []      => if s.depth = 0 then some s else none
  | s, t :: ts => (scan s t).bind (fun s' => scanAll s' ts)

/-- The specification: which tokens have a grammar production at a given depth.
Inside a flow only `atom` and `comma` are producible — there is **no** production
for a block scalar. -/
def prodB : Nat → Tok → Bool
  | 0,     .pct   => true
  | 0,     .atom  => true
  | 0,     .bar   => true
  | 0,     .comma => false
  | _ + 1, .atom  => true
  | _ + 1, .comma => true
  | _ + 1, .bar   => false
  | _ + 1, .pct   => false

abbrev Prod (d : Nat) (t : Tok) : Prop := prodB d t = true

/-! ## Destination 1 — the fact lives in the caller

The arm to refute is "the loop ended with a flow still open". No per-step lemma
can supply it: a single step is perfectly happy to leave the depth nonzero. The
fact is *created* by the caller's post-check, so it must be hoisted. -/

/-- The caller's post-check is the whole content of the fact. -/
theorem caller_supplies_depth :
    ∀ (ts : List Tok) (s s' : St), scanAll s ts = some s' → s'.depth = 0 := by
  intro ts
  induction ts with
  | nil =>
    intro s s' h
    simp only [scanAll] at h
    split at h
    · rename_i hd
      simp only [Option.some.injEq] at h
      subst h
      exact hd
    · simp at h
  | cons t ts ih =>
    intro s s' h
    simp only [scanAll] at h
    cases hs : scan s t with
    | none => rw [hs] at h; simp at h
    | some s1 => rw [hs] at h; exact ih s1 s' h

/-- …and the step ALONE cannot: it happily leaves the depth nonzero. Any attempt
to prove the arm locally is doomed; the hypothesis has to come in from outside. -/
theorem step_alone_cannot_bound_depth :
    ∃ s s' : St, scan s .comma = some s' ∧ s'.depth ≠ 0 := by
  refine ⟨{ depth := 1, fresh := false }, { depth := 1, fresh := false }, ?_, ?_⟩ <;> decide

/-! ## Destination 2 — the fact lives in a threaded invariant

The arm to refute is "a directive fired inside a flow". Nothing in the step's
own hypotheses forbids it; what forbids it is a flag cleared by every earlier
step. Thread the flag and the arm dies in one line. -/

/-- The invariant's advance edge: every accepted step clears `fresh`. -/
theorem scan_clears_fresh {s s' : St} {t : Tok} (h : scan s t = some s') : s'.fresh = false := by
  cases t <;> simp only [scan] at h <;>
    first
      | (split at h <;> simp_all)
      | simp_all
  all_goals (subst h; rfl)

/-- The refutation, *given* the threaded fact. -/
theorem pct_dead_when_stale {s : St} (h : s.fresh = false) : scan s .pct = none := by
  simp [scan, h]

/-- The invariant is load-bearing, not decoration: drop it and the arm fires. -/
theorem pct_fires_when_fresh :
    scan { depth := 0, fresh := true } .pct = some { depth := 0, fresh := false } := by decide

/-- The whole destination-2 closure. The arm is dead not because of anything in
this lemma, but because of a fact established one step earlier. -/
theorem no_pct_after_any_step {s s₁ : St} {t : Tok} (h : scan s t = some s₁) :
    scan s₁ .pct = none :=
  pct_dead_when_stale (scan_clears_fresh h)

/-! ## Destination 3 — there is no fact, the implementation is wrong

The arm to refute is "a block scalar appeared inside a flow". It is not
refutable: the implementation accepts it and the grammar has no production for
it. The obligation is FALSE, so the sorry was never closable — what the case
analysis found is a bug. -/

/-! **THE PROBE.** Two guards, no vocabulary, run before any proof work. -/
#guard (scan { depth := 1, fresh := false } .bar).isSome
#guard ! prodB 1 .bar

theorem impl_accepts_bar_in_flow :
    scan { depth := 1, fresh := false } .bar = some { depth := 1, fresh := false } := by decide

theorem spec_has_no_production_for_bar_in_flow : ¬ Prod 1 .bar := by decide

/-- The obligation the case analysis handed you is **false**. No hypothesis
hoisted from the caller and no invariant threaded through the loop can close it,
because the statement it would prove is not true. -/
theorem step_sound_in_flow_is_false :
    ¬ (∀ (s : St) (t : Tok), 1 ≤ s.depth → (scan s t).isSome → Prod s.depth t) := by
  intro h
  exact spec_has_no_production_for_bar_in_flow
    (h { depth := 1, fresh := false } .bar (by decide) (by decide))

/-! ## The crux — destinations 2 and 3 are indistinguishable in the goal -/

/-- Two refutations of the **same shape**, sitting in the same case tree: "this
arm cannot fire". The first is true and closes by threading a fact. The second is
false and closes by nothing. The goals do not say which is which. -/
theorem dead_arm_and_live_arm_look_alike :
    (∀ s : St, s.fresh = false → scan s .pct = none)
    ∧ ¬ (∀ s : St, 1 ≤ s.depth → scan s .bar = none) := by
  refine ⟨fun _ h => pct_dead_when_stale h, ?_⟩
  intro h
  have hbar := h { depth := 1, fresh := false } (by decide)
  rw [impl_accepts_bar_in_flow] at hbar
  simp at hbar

/-! ## Probing as a table sweep

The probe generalizes: cross the implementation against the specification over a
small grid of states and tokens. This is the check that costs seconds and would
have found L4YAML item 9c before any frame vocabulary was written for the arm. -/

/-- The implementation accepts what the grammar cannot produce. -/
def diverges (d : Nat) (t : Tok) : Bool :=
  (scan { depth := d, fresh := false } t).isSome && ! prodB d t

#guard diverges 1 .bar
#guard ! diverges 1 .atom
#guard ! diverges 1 .comma
#guard ! diverges 1 .pct
#guard ! diverges 0 .atom
#guard ! diverges 0 .bar
#guard ! diverges 0 .comma

/-! The sweep localizes the defect: over depths 0–2 exactly the two in-flow `bar`
cells diverge. A small nonempty answer is a bug report; an empty sweep sends you
back to destinations 1 and 2 with confidence. -/
#guard (([0, 1, 2].flatMap fun d => [Tok.atom, .comma, .bar, .pct].map fun t => (d, t)).filter
          (fun p => diverges p.1 p.2)).length = 2

/-! ## Axiom audit

The two destination-3 facts — that the implementation accepts the input and that
the obligation is therefore false — are **axiom-free**. A bug report should not
rest on anything. -/

/-- info: 'UnclosableArmThreeDestinations.caller_supplies_depth' depends on axioms: [propext] -/
#guard_msgs in
#print axioms caller_supplies_depth

/--
info: 'UnclosableArmThreeDestinations.step_alone_cannot_bound_depth' does not depend on any axioms
-/
#guard_msgs in
#print axioms step_alone_cannot_bound_depth

/-- info: 'UnclosableArmThreeDestinations.no_pct_after_any_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms no_pct_after_any_step

/--
info: 'UnclosableArmThreeDestinations.step_sound_in_flow_is_false' does not depend on any axioms
-/
#guard_msgs in
#print axioms step_sound_in_flow_is_false

/--
info: 'UnclosableArmThreeDestinations.dead_arm_and_live_arm_look_alike' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms dead_arm_and_live_arm_look_alike

end UnclosableArmThreeDestinations

end Blanket
