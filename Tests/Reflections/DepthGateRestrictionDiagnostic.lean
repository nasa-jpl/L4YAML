/-!
# Reflection 390 — the DEPTH-GATING of the in-scope global facts is the diagnostic for which conjuncts
of a per-window provider RESTRICT now vs which OWE a deep characterization.

Self-contained core-Lean toy of L4YAML R390.  Continuing the seq frontier, R389 reduced `h_seq_rec` to
a per-window provider `∀ lo hi, <seq guards> → FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed`.  The
queued (a) DE-RISK asked: is the global content-start fact at the sorry site ALL-DEPTH or DEPTH-0 only?
Reading the in-scope facts settled it — `h_content0` is the depth-`0` HEAD and `h_fe_pattern` is gated on
`flowBracketBalance tokens 2 k = 0` (top-level separators only).  But `FlowBodyContentDeep`'s
`openerContentStart`/`feContentStart` quantify over EVERY `k ∈ [lo, hi)` with NO balance gate.  An
all-depth universal is provably NOT a restriction of a depth-`0`-gated fact, so the content conjunct owes
a genuine deep characterization (emitter induction), while the bracket + enclosure conjuncts — whose
universals carry the same gate, or are pure subrange transports — assemble now.

The transferable diagnostic: for each conjunct that is a universal `∀ k, guards → body`, COMPARE its
guards to the in-scope fact's.  If the in-scope fact carries a depth-`0` gate (`balance ... = 0`) and the
conjunct's universal carries the SAME gate, it RESTRICTS (bound the quantifier).  If the conjunct is
ALL-DEPTH (no balance gate), it does NOT restrict — it owes a deep fact.  Mechanical test: grep the
in-scope fact for a `balance ... = 0` premise.

Mapping to L4YAML: `Q` ~ "the token after position k is a content-start head"; `Gate0` ~ the depth-`0`
balance gate; `inScope_depth0` ~ `h_fe_pattern`; `conjA_restricts` ~ the depth-`0` conjunct restricting;
`conjB_not_from_depth0` ~ the all-depth `FlowBodyContentDeep` field NOT following from the depth-`0`
facts; `deepFact` ~ the owed deep characterization that does discharge it.

POSITIVE: `conjA_restricts` — the depth-`0`-keyed conjunct is the in-scope fact with its window bounds
dropped; `allDepth_from_deep` — the all-depth conjunct DOES hold, but only from the deep fact.
NEGATIVE: `conjB_not_from_depth0` — `Q` satisfies the gated in-scope fact yet fails the ungated
all-depth conjunct; `separating_witness` — the ungated position `k = 1` the depth-`0` fact can't reach.

Sharpens [[ref-incomplete-projection-still-factors]] and [[ref-non-restriction-residual-root-seed]].
-/

namespace Tests.Reflections.DepthGateRestrictionDiagnostic

set_option autoImplicit false

/-- A position predicate: "the token after position `k` is a content-start head". -/
def Q (k : Nat) : Prop := k % 4 = 1
/-- The DEPTH-`0` gate the in-scope global fact carries (models `flowBracketBalance 2 k = 0`). -/
def Gate0 (k : Nat) : Prop := k % 4 = 0

/-- The in-scope GLOBAL fact, DEPTH-`0` GATED: content guaranteed only AFTER a gated position
    (models `h_fe_pattern`, whose `flowBracketBalance tokens 2 k = 0` premise restricts it to the
    top level). -/
theorem inScope_depth0 : ∀ k, Gate0 k → Q (k + 1) := by
  intro k h; unfold Gate0 at h; unfold Q; omega

/-- **POSITIVE — the depth-`0`-keyed conjunct RESTRICTS.**  A window-bounded conjunct whose universal
    carries the SAME gate is just the in-scope fact with its domain narrowed: drop the window bounds and
    apply.  (In L4YAML: the bracket/enclosure conjuncts, restrictions of global invariants.) -/
theorem conjA_restricts (lo hi : Nat) : ∀ k, lo ≤ k → k < hi → Gate0 k → Q (k + 1) :=
  fun k _ _ hg => inScope_depth0 k hg

/-- **NEGATIVE — the ALL-DEPTH conjunct is NOT a restriction of the depth-`0` fact.**  `Q` satisfies the
    gated fact (`inScope_depth0`) yet FAILS the ungated all-depth conjunct: at the ungated `k = 1`,
    `Q 2` is false.  No amount of bounding the depth-`0` fact yields `∀ k, Q (k+1)`.  (In L4YAML:
    `FlowBodyContentDeep` cannot come from the depth-`0` content facts.) -/
theorem conjB_not_from_depth0 : ¬ (∀ k, Q (k + 1)) := by
  intro h; have h2 := h 1; unfold Q at h2; omega

/-- The separating witness: `k = 1` is UNGATED (`Gate0 1` false) and `Q 2` is false — the all-depth
    quantifier reaches it, the depth-`0` fact does not.  Its existence is what forces the deep
    characterization. -/
theorem separating_witness : ¬ Gate0 1 ∧ ¬ Q 2 := by
  unfold Gate0 Q; exact ⟨by decide, by decide⟩

/-- The owed DEEP characterization (modelled as the genuinely all-positions fact). -/
def Qdeep (_ : Nat) : Prop := True
/-- **POSITIVE — the all-depth conjunct DOES hold, but only from the DEEP fact.**  The lesson: the
    all-depth conjunct is true in reality, just not derivable from the in-scope depth-`0` fact — it owes
    the deep characterization, the lone named residual. -/
theorem allDepth_from_deep : ∀ k, Qdeep (k + 1) := fun _ => trivial

#guard !(1 % 4 == 0)                  -- k = 1 is ungated (Gate0 1 false)
#guard !(2 % 4 == 1)                  -- Q 2 false: the all-depth conjunct fails where the gate can't reach
#guard (0 % 4 == 0) && (1 % 4 == 1)   -- the gated fact holds at k = 0: Gate0 0 ∧ Q 1

end Tests.Reflections.DepthGateRestrictionDiagnostic
