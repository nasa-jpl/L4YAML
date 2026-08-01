/-!
# Reflection -- two FALSE-PROGRESS signals in proof engineering

Surfaced by the R447 workstream (2026-07-01).  Demonstrates concretely why "no `sorry` warning" and
"reduced to a weaker type" can both LIE about progress.

See [[feedback_illusory_sorry_free_delegation]] and [[feedback_vestigial_reduction_produce_not_type]].

## Trap 1 -- the illusory "sorry-free" wrapper

Lean's `declaration uses 'sorry'` warning fires ONLY on the declaration whose proof term
SYNTACTICALLY contains `sorryAx`.  A theorem that merely CALLS a sorry-containing lemma gets NO
warning -- its term references the lemma as a constant, not its unfolded body -- yet `#print axioms`
unfolds transitively and still reports `sorryAx`.  So a delegating wrapper LOOKS proven (no warning)
but is NOT.  Judge "landed" by the axiom profile, never by the sorry keyword / warning.
-/

namespace IllusorySorryFree

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- A genuinely-unproven obligation: a literal `sorry`.  Lean WARNS "declaration uses `sorry`"
    (captured by the surrounding `#guard_msgs` so the indexed build stays warning-clean —
    the warning existing is the point). -/
theorem hard_obligation : True ∧ True := by
  sorry

/-- A wrapper that only CALLS `hard_obligation`.  Its own body has NO `sorry` token, so Lean emits
    NO "declaration uses 'sorry'" warning on THIS line -- it LOOKS sorry-free / landed. -/
theorem looks_sorry_free : True :=
  hard_obligation.2

-- ...but `#print axioms` tells the truth: the wrapper transitively carries `sorryAx`.  This is the
-- trap: splitting `f := g h_sorry` into a "sorry-free f" + "sorry g" moves the sorry and manufactures
-- a misleading proven-looking wrapper, without changing the axiom profile of anything downstream.

/-- info: 'IllusorySorryFree.looks_sorry_free' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms looks_sorry_free

/-! ## Trap 2 -- the vestigial reduction (type-strength ≠ production-cost)

A combinator that "reduces producing hard `X` to producing easier `Y`" adds value ONLY if `Y` is
genuinely cheaper to PRODUCE at the leaf.  If the only way to produce `Y` is to project it off `X`
(`Y := projectYfromX (produceX ...)`), then the reduction is VESTIGIAL: `Y` is weaker as a TYPE but
not cheaper to PRODUCE -- it re-derives `X`.  Below, `produce_Y` bottoms out at `produce_X`, so the
`X ← recursion over Y` combinator would add a layer without removing the hard part. -/

/-- Stand-in "hard deliverable" X (per window). -/
def X (n : Nat) : Prop := n = n
/-- Stand-in "weaker deliverable" Y, a PROJECTION of X (weaker type, same production bottleneck). -/
def Y (_n : Nat) : Prop := True

/-- Producing X (the real work -- here trivial, but imagine a navigator/locate). -/
theorem produce_X (n : Nat) : X n := rfl

/-- Producing Y "cheaply"?  No -- its only source projects off `produce_X`.  So a combinator
    `X ← (fun n => Y n)` gains nothing: `Y` shares `X`'s bottleneck (`produce_X`). -/
theorem produce_Y (n : Nat) : Y n :=
  (fun _ => trivial) (produce_X n)

end IllusorySorryFree
