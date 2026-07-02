/-!
# Reflection 447 — a producer reused to break a circularity that routes through a SPINE-walking
# navigator inherits the spine's WHOLE-PATH invariant as a gate.  That gate constrains the ANCESTOR
# stack; the consumer's guard only asserts the window's OWN enclosing frame (vacuous over ancestors).
# So the gate is NOT derivable from the guard — it must be THREADED through the consuming recursion
# (a descend edge that pushes the own frame onto the ancestor stack), seeded vacuously at the root.

Self-contained (core Lean, no `L4YAML` import) toy of the R447 finding — STEP D continued: resolving the
within-window carrier↔recursion circularity by sourcing the per-window `SafeBodyUnit` (`h_safe`)
carrier-free from emission.

Context.  The carrier `seqLocalCarrier_of_widthEnc tokens lo hi h_hi h_safe h_widthEnc` (R446) needs
`h_safe : SafeBodyUnit ((take hi).drop lo)`, and the body producer needs the carrier — so `h_safe` must
be sourced INDEPENDENTLY of the carrier, from emission.  The R446 Next step queued "find/build the
per-nested-value emission-flat `SafeBodyUnit` producer".  Reading the landed code, it ALREADY exists:
`nestedSeq_safeBodyUnit_of_locator`.  But it routes through the forward locator
`nestedSeq_recseqentry_locate`, which walks an all-seq bracket SPINE down to the stored entry — so it
carries the locator's `h_path : SeqPathAllSeq tokens (lo - 1)`: EVERY ancestor bracket frame is `[`-typed.

The crux.  `btStep` pushes the TOP at the list HEAD (`.flowSequenceStart ↦ true :: s`,
`.flowMappingStart ↦ false :: s`), and a seq window's stack at `lo` is `true :: p`, where `true` is the
window's OWN opener `[` and `p = btFold (take (lo-1))` is its ANCESTOR stack.  The joint-induction guard's
`SeqEnclosed tokens lo` reads the head `(true :: p).head? = some true` — the OWN frame, which is `true`
for EVERY seq window regardless of `p`.  So the guard is VACUOUS over the ancestors.  The locator's gate
`SeqPathAllSeq tokens (lo-1)` reads `allSeq p` — the whole ANCESTOR stack all-`[` and nonempty.  A seq
reached through a map (`[{a:[b]}]`'s `[b]`) has `p = [false, true]` (a map's `false` deeper): the OWN
frame is still `[` (guard holds) but `allSeq p` FAILS.  That is the counterexample: the gate is not a
projection of the guard, so it must be THREADED.

The thread.  Descending into a child seq, the child's ancestor stack is `true :: p` (the current window's
own `[` becomes the child's nearest ancestor).  `allSeq (true :: p)` holds iff `p` is all-`[` — INCLUDING
the empty `p`.  So the threadable invariant is `allTrue p` (all-`[`, possibly empty), strictly weaker than
the gate `allSeq p = allTrue p ∧ p ≠ []`: the root window itself fails the gate (empty ancestor stack,
`SeqPathAllSeq tokens 1` fails) — sourcing its `h_safe` from the flat `seqRoot_safeBodyUnit` (a
root-vs-nested dispatch) — yet it SEEDS the thread (`allTrue []` vacuously), so every nested window the
recursion descends into satisfies the gate.  The seq recursion only ever descends `[`→`[`, so the thread
never meets a `false`.

The reusable rule.  When the producer you reuse to break a circularity routes through a navigator that
walks a TYPED SPINE, it inherits the spine's WHOLE-PATH invariant as a hypothesis.  Your consumer's guard
typically asserts only the window's OWN enclosing frame — vacuous over the ancestor path the spine gate
constrains.  So the gate is NOT a projection of the guard; thread it through the recursion via a descend
edge (push the own frame onto the ancestor stack), seeded at the root by the invariant's vacuous (empty)
case even though the root itself fails the gate.  Confirm necessity with a MINIMAL PAIR sharing the OWN
frame but differing on the ancestor path (a thing-under-a-different-thing).

This toy models the ancestor stack as `p : List Bool` (`true` = `[`/seq frame, `false` = `{`/map frame):

* `ownFrame_vacuous_over_ancestors` — the guard `SeqEnclosed` (`(true :: p).head? = some true`) holds for
  EVERY seq window, regardless of `p`: it gives no information about the ancestor path.
* `minimal_pair_own_frame_agrees_path_differs` — `[true]` (all-seq) vs `[false, true]` (map-nested) have
  the SAME own frame (`true :: ·` is a seq window for both) but DIFFER on `allSeq` ⇒ the gate is not
  derivable from the guard.
* `allSeq_descend_push` — the descend edge: `allTrue p → allSeq (true :: p)` (the child's ancestor stack);
  threadable even from the empty root, where `allTrue [] = true`.
* `root_fails_gate_seeds_thread` — the root: `¬ allSeq []` (fed flat) yet `allTrue []` (seeds the thread).

All sorry-free, axiom-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.TopFrameGuardVsSpineGate

/-! ## The ancestor bracket stack and the two invariants. -/

/-- The ANCESTOR bracket stack at a seq window — `btFold (take (lo-1))`, EXCLUDING the window's own `[`.
    `true` = seq frame `[`, `false` = map frame `{`; TOP at the HEAD. -/
abbrev Stack := List Bool

/-- The threadable invariant — every ancestor frame is `[` (ALLOWING the empty stack, vacuously true). -/
def allTrue (p : Stack) : Prop := p.all (· == true) = true

/-- The spine gate — `SeqPathAllSeq tokens (lo-1)`: every ancestor frame is `[` AND the stack is nonempty.
    Strictly stronger than `allTrue` (the empty root fails it). -/
def allSeq (p : Stack) : Prop := p ≠ [] ∧ allTrue p

/-! ## The guard is vacuous over the ancestors; the gate is not derivable from it. -/

/-- **The guard `SeqEnclosed` is vacuous over the ancestor path.**  For EVERY seq window the stack at `lo`
    is `true :: p` (the own opener `[`), so `SeqEnclosed tokens lo = (true :: p).head? = some true` holds
    regardless of the ancestors `p`.  The guard tells you nothing about `p`. -/
theorem ownFrame_vacuous_over_ancestors (p : Stack) : (true :: p).head? = some true := rfl

/-- **The minimal pair: SAME own frame, DIFFERENT ancestor path.**  `[true]` (a genuine all-seq window)
    and `[false, true]` (a seq reached through a map — `[{a:[b]}]`'s `[b]`) are BOTH valid seq windows
    (own frame `[`, `ownFrame_vacuous_over_ancestors`), yet `allSeq [true]` holds and `allSeq [false, true]`
    FAILS (the map's `false`).  So the guard cannot decide the gate: it must be threaded. -/
theorem minimal_pair_own_frame_agrees_path_differs :
    ((true :: ([true] : Stack)).head? = some true ∧ (true :: ([false, true] : Stack)).head? = some true)
    ∧ allSeq [true]                                  -- all-seq window: gate holds
    ∧ ¬ allSeq [false, true] := by                   -- map-nested window: gate FAILS
  refine ⟨⟨rfl, rfl⟩, ⟨by simp, by simp [allTrue]⟩, ?_⟩
  rintro ⟨_, hall⟩
  simp [allTrue] at hall

/-! ## The descend edge and the root seed. -/

/-- **The descend edge — push the own frame onto the ancestor stack.**  When the seq recursion descends
    through a located `[` opener, the child window's ancestor stack is `true :: p` (the current window's
    own `[`).  If the ancestor path is all-`[` (`allTrue p`, possibly EMPTY), the child satisfies the gate
    `allSeq (true :: p)`.  This is the edge threading `SeqPathAllSeq` through the seq recursion (which only
    descends `[`→`[`).  (The real edge is a btFold-push composition over a balanced sub-range; this models
    its essential content — the head push.) -/
theorem allSeq_descend_push {p : Stack} (h : allTrue p) : allSeq (true :: p) := by
  refine ⟨by simp, ?_⟩
  simpa [allTrue] using h

/-- **The gate implies the threadable invariant** — so a nested window (which satisfies the gate) seeds
    the thread for ITS children: `allSeq p → allTrue p → allSeq (true :: p)`. -/
theorem allSeq_imp_allTrue {p : Stack} (h : allSeq p) : allTrue p := h.2

/-- **The root fails the gate but seeds the thread.**  The root window's ancestor stack is empty
    (`SeqPathAllSeq tokens 1` fails — nothing before the outer `[`), so the root is NOT served by the
    spine navigator; it sources `h_safe` from the flat `seqRoot_safeBodyUnit` (root-vs-nested dispatch).
    Yet `allTrue []` holds vacuously, so the root's CHILDREN satisfy the gate via `allSeq_descend_push`. -/
theorem root_fails_gate_seeds_thread : ¬ allSeq [] ∧ allTrue [] := by
  refine ⟨?_, by simp [allTrue]⟩
  rintro ⟨hne, _⟩; exact hne rfl

/-- The finding in one proposition: the guard is vacuous over ancestors, the gate is strictly stronger
    (the minimal pair), the thread survives the descend push from an all-`[` ancestor path, and the empty
    root fails the gate (fed flat) yet seeds the thread. -/
theorem r447_finding :
    (∀ p : Stack, (true :: p).head? = some true)             -- guard vacuous over ancestors
    ∧ (allSeq [true] ∧ ¬ allSeq [false, true])               -- gate distinguishes; not derivable
    ∧ (∀ p : Stack, allTrue p → allSeq (true :: p))          -- descend edge: thread is sound
    ∧ (¬ allSeq [] ∧ allTrue []) :=                          -- root fails gate but seeds thread
  ⟨ownFrame_vacuous_over_ancestors,
   ⟨(minimal_pair_own_frame_agrees_path_differs).2.1,
    (minimal_pair_own_frame_agrees_path_differs).2.2⟩,
   fun _ => allSeq_descend_push,
   root_fails_gate_seeds_thread⟩

end Tests.Reflections.TopFrameGuardVsSpineGate
