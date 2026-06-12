/-!
# Reflection 393 — FIX a root-false all-depth guard by ADDING the window-absolute excluding premise.

Self-contained core-Lean toy of L4YAML R393, the FIX that follows R392's refutation
([[ref-restriction-hides-root-falsity]]).  An all-depth guard field `opener k → content (k+1)` was found
FALSE at the ROOT (its `opener 3` is an empty-bracket-style opener whose successor is a `close`, not
content — exactly `FlowBodyContentDeep.openerContentStart` failing at `{` / `[]`).  The WRONG fix is to
weaken it to a depth-0 / context-keyed field (that loses the trivial restriction edges and re-introduces
re-basing, [[ref-non-restriction-residual-root-seed]]).  The RIGHT fix — modelled here — KEEPS the field
all-depth and ADDS the WINDOW-ABSOLUTE premise (`close (k+1) = false`, i.e. `tokens[k+1] ≠ ]`) that excludes
exactly the false region.

Three things the toy makes precise:
* The premise is the fact the OLD field was UNSOUNDLY SELF-DERIVING (`premise_is_self_derived`): where the
  old field held it implied `close (k+1) = false` (non-emptiness).  Re-scoping converts that self-derived
  proof into an ASSUMED precondition — the consumer's DEBT ([[ref-guarded-universal-fold-relocates-guard]]).
* The premise is WINDOW-ABSOLUTE, so the restriction edge threads it VERBATIM (`restrict_threads_premise`) —
  re-scoping costs ZERO edge work ([[ref-window-absolute-gate-subset-restriction]]).
* The re-scoped root is established by a NON-vacuous positive witness (`newGuard_nonvacuous`): at `opener 0`
  the premise HOLDS and the conclusion FIRES, the satisfiability anchor
  ([[ref-probe-provider-satisfiable-before-assembler]]) — not a vacuous "premise never holds" pass.

Mapping to L4YAML: `opener`/`close`/`content` ~ "position is a `[` opener" / "next token is `]`" / "next
token is content-start"; `OldGuard` ~ `FlowBodyContentDeep.openerContentStart` (root-FALSE); `NewGuard` ~
`FlowBodyContentDeepSeq.openerContentStart` (root-TRUE); `newGuard_nonvacuous` ~
`flowBodyContentDeepSeq_root_holds_nested_scalar` on `[[a]]`; `restrict_threads_premise` ~
`flowBodyContentDeepSeq_descend`/`_advance`.

POSITIVE: `newGuard_holds` / `newGuard_nonvacuous` (re-scoped root TRUE, non-vacuously);
`restrict_threads_premise` (edge threads the premise verbatim); `consumer_supplies_premise` (the consumer
discharges the debt).
NEGATIVE: `oldGuard_false` (the un-premised root is FALSE, R392); `premise_is_self_derived` (the added
premise is exactly what the false field had been silently proving).
-/

namespace Tests.Reflections.RescopeByExcludingPremise

set_option autoImplicit false

/-! ## Toy positions. `opener 0` is a real opener (→ content at 1); `opener 3` is an empty-bracket-style
opener whose successor (position 4) is a `close`, NOT content — the all-depth field over-reaches here. -/

def opener : Nat → Bool | 0 => true | 3 => true | _ => false
/-- position 4 is a "close" (the empty-bracket end). -/
def close : Nat → Bool | 4 => true | _ => false
/-- content-start test: every position except the close at 4 (content and close are mutually exclusive). -/
def content (k : Nat) : Bool := !(close k)

/-- OLD all-depth field (= `FlowBodyContentDeep.openerContentStart`): every opener → next is content. -/
def OldGuard : Prop := ∀ k, opener k = true → content (k + 1) = true

/-- NEW re-scoped field (= `FlowBodyContentDeepSeq.openerContentStart`): opener AND next-not-a-close → next
    is content (the `≠ ]` premise added). -/
def NewGuard : Prop := ∀ k, opener k = true → close (k + 1) = false → content (k + 1) = true

/-- **NEGATIVE — the OLD root is FALSE** (R392): `opener 3` is followed by the close at 4, not content. -/
theorem oldGuard_false : ¬ OldGuard :=
  fun h => absurd (h 3 (by decide)) (by decide)

/-- **POSITIVE — the NEW (re-scoped) root is TRUE.**  The `close (k+1) = false` premise directly delivers
    content (a `[` that isn't `]` is followed by content by well-formedness). -/
theorem newGuard_holds : NewGuard := by
  intro k _ho hclose
  simp [content, hclose]

/-- **POSITIVE — NON-vacuous:** at `opener 0` the premise HOLDS and the conclusion FIRES (the satisfiability
    anchor — not a vacuous "premise never holds" pass). -/
theorem newGuard_nonvacuous : opener 0 = true ∧ close 1 = false ∧ content 1 = true := by decide

/-- **NEGATIVE — the added premise is the fact the OLD field was UNSOUNDLY SELF-DERIVING.**  Where the old
    field held (content at an opener), it implied `close (k+1) = false` (non-emptiness) — exactly the premise
    the re-scoping now makes EXPLICIT and the consumer must supply. -/
theorem premise_is_self_derived (k : Nat) (h : content (k + 1) = true) : close (k + 1) = false := by
  unfold content at h
  cases hc : close (k + 1) with
  | false => rfl
  | true => rw [hc] at h; simp at h

/-- **POSITIVE — the restriction edge threads the added premise VERBATIM** (window-absolute): narrowing the
    universal to `[a, ∞)` passes `close (k+1) = false` straight through, zero edge work. -/
theorem restrict_threads_premise (h : NewGuard) (a : Nat) :
    ∀ k, a ≤ k → opener k = true → close (k + 1) = false → content (k + 1) = true :=
  fun k _ ho hc => h k ho hc

/-- **POSITIVE — the consumer's DEBT discharged.**  Using the NEW guard at `opener 0` requires SUPPLYING the
    premise (here `close 1 = false`) that, in L4YAML, the dispatch's empty-vs-non-empty case-split produces. -/
theorem consumer_supplies_premise : content 1 = true :=
  newGuard_holds 0 (by decide) (by decide)

#guard opener 3 == true
#guard content 4 == false      -- the OLD root fails HERE (opener 3 → close 4, not content)
#guard close 1 == false        -- the premise holds at opener 0 (non-empty) ...
#guard content 1 == true       -- ... so the NEW guard's conclusion fires (non-vacuous)

end Tests.Reflections.RescopeByExcludingPremise
