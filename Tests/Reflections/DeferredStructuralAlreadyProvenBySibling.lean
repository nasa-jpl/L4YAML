/-!
# Reflection 386 — a root seed's DEFERRED-STRUCTURAL hypothesis is often ALREADY proven by a sibling
whole-structure lemma serving a DIFFERENT consumer; the only gap is a per-item-predicate coercion.

Self-contained core-Lean toy of L4YAML R386 (`seqRoot_flowBodyWindow` / `seqRoot_seqPathAllSeq`):
R385's root seed named `domain`/`window` DEFERRED-STRUCTURAL — "a NEW owed brick, nothing produces them
yet."  R386 refines that: nothing produces them *under your consumer's per-item predicate*, but a SIBLING
consumer's whole-structure lemma already proves the SAME facts *under a weaker per-item predicate*.  So
the move is: SEARCH the sibling consumers first; the gap is usually a strong→weak per-item coercion
([[ref-coerce-to-weaker-reuse-wrapper]]), and the feared brick was already a theorem
([[ref-metric-bridge-is-composition]]).

Mapping to L4YAML: `WeakItem` ~ `EmitScansInFlowBlock`; `StrongItem` ~ `EmitScansInFlowRecEntry` (the
nested locator's per-item predicate, +`RecSeqEntry`); `siblingStructure` ~
`scanFiltered_emitSeq_nonempty_structure` (proves `Balanced` ~ the `FlowBodyWindow` content, en route to
its OWN `OwnGoal` ~ `FlowSubrangesOk`); `deferredProducer` ~ `seqRoot_flowBodyWindow`.

POSITIVE: `deferredProducer` — derives the deferred fact in ONE line (coerce strong→weak, call sibling,
project).  Near-zero content; not a new induction.
NEGATIVE / de-risk: `coercion_is_necessary` — `StrongItem` is genuinely stronger than `WeakItem`, so you
CANNOT pass it to the sibling directly; the coercion is a real (if trivial) step.  `would_be_a_new_brick`
shows the from-scratch alternative (a full induction the sibling already ran) the reuse AVOIDS.
-/

namespace Tests.Reflections.DeferredStructuralAlreadyProvenBySibling

set_option autoImplicit false

/-- The WEAK per-item predicate the SIBLING whole-structure lemma consumes. -/
structure WeakItem (n : Nat) : Prop where
  even : n % 2 = 0

/-- The STRONG per-item predicate OUR (nested-locator) consumer threads: same `even`, plus an EXTRA
    conjunct `div4` (the recursive-deliverable analog `RecSeqEntry`). -/
structure StrongItem (n : Nat) : Prop where
  even : n % 2 = 0
  div4 : n % 4 = 0

/-- **The per-item coercion** (`emitScansInFlowBlock_of_flowRecEntry` analog): drop the extra conjunct,
    strong → weak.  Trivial, but a REAL step — the predicates are genuinely distinct (see below). -/
theorem weakItem_of_strong (n : Nat) (h : StrongItem n) : WeakItem n := ⟨h.even⟩

/-- The deferred-structural fact OUR producer needs (the `FlowBodyWindow` content analog). -/
def Balanced (ns : List Nat) : Prop := ns.all (· % 2 == 0) = true

/-- The SIBLING consumer's OWN goal (the `FlowSubrangesOk` analog) — we don't care about it, but the
    sibling lemma proves it alongside `Balanced` from the same weak per-item predicate. -/
def OwnGoal (ns : List Nat) : Prop := ns.length % 1 = 0

/-- **The SIBLING whole-structure lemma** (`scanFiltered_emitSeq_nonempty_structure` analog): from the
    WEAK per-item predicate it proves a BUNDLE — `Balanced` (the fact we need) AND its OWN `OwnGoal` — in
    ONE induction over the structure.  The `Balanced` half is proven HERE, for the sibling's sake; our
    producer will just project it. -/
theorem siblingStructure (ns : List Nat) (h : ∀ n ∈ ns, WeakItem n) :
    Balanced ns ∧ OwnGoal ns := by
  refine ⟨?_, ?_⟩
  · unfold Balanced
    rw [List.all_eq_true]
    intro n hn
    have he := (h n hn).even
    simp only [beq_iff_eq, he]
  · unfold OwnGoal; exact Nat.mod_one _

/-! ## POSITIVE — the deferred-structural producer is a ONE-LINER: coerce, call the sibling, project.
Not a new substantial brick — the feared deferred fact was already a theorem (the sibling proved it). -/

theorem deferredProducer (ns : List Nat) (h_strong : ∀ n ∈ ns, StrongItem n) :
    Balanced ns :=
  (siblingStructure ns (fun n hn => weakItem_of_strong n (h_strong n hn))).1

/-! ## NEGATIVE / de-risk — why the coercion is a REAL step, and what the reuse AVOIDS. -/

/-- `StrongItem` is genuinely STRONGER than `WeakItem`: `n = 2` is `WeakItem` but not `StrongItem`.  So
    `∀ n ∈ ns, StrongItem n` is NOT the sibling's hypothesis `∀ n ∈ ns, WeakItem n` — you MUST coerce
    (the predicates differ; you can't pass strong where weak is wanted without `weakItem_of_strong`). -/
theorem coercion_is_necessary : ∃ n, WeakItem n ∧ ¬ StrongItem n :=
  ⟨2, ⟨by decide⟩, fun h => by have := h.div4; omega⟩

/-- What the reuse AVOIDS: proving `Balanced` from scratch re-runs the SAME induction the sibling already
    ran.  `deferredProducer` does NONE of this — it projects the sibling's first conjunct.  (Here the
    from-scratch proof is short; in L4YAML it is the whole `scanFiltered_emitSeq_nonempty_structure`
    chain replay — exactly the substantial brick the "deferred ⇒ new owed brick" estimate feared.) -/
theorem would_be_a_new_brick (ns : List Nat) (h : ∀ n ∈ ns, WeakItem n) : Balanced ns := by
  unfold Balanced
  rw [List.all_eq_true]
  intro n hn
  have he := (h n hn).even
  simp only [beq_iff_eq, he]

-- concrete checks: the deferred fact is a plain computation on real data
#guard ([2, 4, 6] : List Nat).all (· % 2 == 0)
#guard ! ([2, 3] : List Nat).all (· % 2 == 0)

end Tests.Reflections.DeferredStructuralAlreadyProvenBySibling
