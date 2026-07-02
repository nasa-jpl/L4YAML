/-!
# Reflection 432 — source a multi-field provider's later field from an earlier field's output

Self-contained (core Lean, no `L4YAML` import) toy of the R432 step.

Context.  A flat per-window provider produces a conjunction `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧
SeqEnclosed`.  The naive way to build it is to source each conjunct independently from the shared
hypotheses, so the provider's residual is the SUM of every conjunct's primitives.

The finding.  Build a LATER field from an EARLIER field's OUTPUT, not just from the shared hypotheses.
R432's `seqWindowFacts_of_emit_and_primitives` produces the `FlowBodyWindow` field first (R390), then feeds
that very `FlowBodyWindow` to R431's `flowBodyContentDeepSeq_of_emit_and_window` to produce the
deep-content field — because the deep field's non-emptiness gate is a consequence of the window's Dyck
floor (R431).  So the combined residual is the UNION of the conjuncts' primitives, not the sum: the floor
primitive does DOUBLE DUTY — it is `FlowBodyWindow.dyck` AND the source of the deep field's head
non-emptiness.

Reusable rule: before sourcing each conjunct of a provider independently, check whether a later conjunct
is implied by (or cheaply derivable from) an earlier conjunct already produced.  A field's invariant (a
floor, a balance, a typing) often discharges a sibling field's precondition, collapsing the provider's
residual to the shared primitives.

The toy below contrasts a NAIVE provider (residual = two independent facts) with a SMART provider whose
second field is derived from the first (residual = one fact, the floor, doing double duty).
-/

namespace Tests.Reflections.ProviderFieldFromSiblingOutput

set_option autoImplicit false

/-- Toy bracket-delta: open `+1`, close `-1`, neutral `0`. -/
def delta : Nat → Int
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- Prefix balance of the first `k` tokens. -/
def bal (toks : List Nat) (k : Nat) : Int := ((toks.take k).map delta).sum

/-- Field A's invariant — the Dyck floor (mirror of `FlowBodyWindow.dyck`). -/
def Floor (toks : List Nat) : Prop := ∀ i, i ≤ toks.length → bal toks i ≥ 0

/-- **Field A's invariant implies field C's precondition** — the head is not the close, FROM the floor
    (mirror of `flowBodyWindow_head_ne_close`: the deep field's non-emptiness comes from the window's
    floor, R431). -/
theorem headNeClose_of_floor (head : Nat) (t : List Nat) (h : Floor (head :: t)) : head ≠ 2 := by
  intro h_close
  have hf := h 1 (Nat.succ_le_succ (Nat.zero_le _))
  have hbal : bal (head :: t) 1 = delta head := by simp [bal]
  rw [hbal, h_close, show delta 2 = -1 from rfl] at hf
  omega

/-- **NAIVE provider** — both fields sourced independently, so the residual is the SUM of their
    primitives: it demands BOTH `Floor` AND the non-emptiness `head ≠ 2` as separate hypotheses. -/
theorem provider_naive (head : Nat) (t : List Nat)
    (hA : Floor (head :: t)) (hC : head ≠ 2) :
    Floor (head :: t) ∧ head ≠ 2 :=
  ⟨hA, hC⟩

/-- **SMART provider** — the second field is derived from the FIRST field's output, so the residual is the
    UNION: ONLY `Floor` is demanded, and it does DOUBLE DUTY (field A's invariant + field C's source).
    Toy of `seqWindowFacts_of_emit_and_primitives` (the deep field fed the produced `FlowBodyWindow`). -/
theorem provider_smart (head : Nat) (t : List Nat)
    (hA : Floor (head :: t)) :
    Floor (head :: t) ∧ head ≠ 2 :=
  ⟨hA, headNeClose_of_floor head t hA⟩

-- The floor genuinely implies the non-emptiness: a close-headed window fails the floor at step 1
-- (`bal [close] 1 = -1 < 0`), so the SMART provider's single primitive really does cover both fields.
#guard decide (bal [2] 1 < 0)         -- close-headed ⇒ floor violated
#guard decide (bal [1, 2] 1 ≥ 0)      -- open-headed  ⇒ floor satisfied

end Tests.Reflections.ProviderFieldFromSiblingOutput
