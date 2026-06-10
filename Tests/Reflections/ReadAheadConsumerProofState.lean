/-!
# Reflection 352 — read-ahead the CONSUMER chain to de-alarm a terse downstream step-list: proof-STATE, not prose, sets the pace

Self-contained (core Lean, no `L4YAML` import) toy model of the de-risk that read-ahead steps (3)–(6)
below the two `FlowSubrangesOk tokens := sorry` sites before grinding the mechanical locator bricks.

THE SETTING.  A dependency map lists the steps below a frontier `sorry` as terse one-liners ("drive X …
thread Y … wire Z").  A one-liner is INDISTINGUISHABLE between three states: (i) a feared obligation that
is ALREADY PROVEN (discharged sessions ago, forgotten), (ii) trivial plumbing of proven pieces, and (iii)
a whole PARALLEL effort duplicating what you just built.  Only the actual `theorem … := by` vs `:= sorry`
tells them apart — so READ THE PROOF-STATE off source, not the plan's prose.

THE FINDING — A SURVEY THAT CHECKS THE `def` MISSES THE `theorem` AND OVER-ALARMS.  A first-pass survey
reported a property as "definition only, no proof."  But a PRODUCER theorem had proved it.  The survey
looked at the `def` (the property's STATEMENT) and never grepped for its producer (`: T := by`, `→ T`,
`_of_…`).  Checking the producer inverts the verdict: the chain is SHALLOWER than feared, gated on one
descent function, the rest proven composition.

THE TRANSFERABLE RULE.  A consumer-chain step is a proof-state question, not a prose one.  Before pacing a
per-brick grind down a deep chain: read-ahead the consumers; for each named symbol grep for a PRODUCER, not
the `def`; classify each step as proven / plumbing / parallel-effort from SOURCE; treat any multi-agent
survey as a lead and confirm against source.  Payoff is a PACING decision — no wall behind the mechanical
bricks licenses BATCHING them.

Complements [[ref-probe-deferred-universal-before-producing]] (probe a PRODUCER target before proving it;
this probes a CONSUMER chain before PACING toward it) and pairs with
[[ref-leaf-production-is-prefix-slice]] (the mechanical bricks this de-risk cleared the runway for).
-/

namespace Tests.Reflections.ReadAheadConsumerProofState

set_option autoImplicit false

/-! ## A consumer-chain step has a PROOF-STATE, invisible in the plan's one-liner -/

/-- The three states a terse "step (N) follows" one-liner can be in.  The plan's prose cannot tell them
    apart; only the source's `theorem … := by` vs `:= sorry` can. -/
inductive StepState where
  | alreadyProven   -- a feared obligation discharged sessions ago (look for its PRODUCER theorem)
  | trivialPlumbing -- pure composition of proven pieces
  | parallelEffort  -- a whole mirror side duplicating completed work
  | openFunnel      -- the genuine single remaining obligation
deriving DecidableEq

/-- What the PLAN's prose exposes about a step: just that "a step follows" — a single bit, blind to state. -/
def planSeesState (_s : StepState) : Bool := true

/-- **NEGATIVE — the plan's prose underdetermines the proof-state.**  Every step looks identical in the
    map ("a step follows"), so `planSeesState` is constant `true` across all four states — it certifies
    nothing about which obligations are paid.  Pacing off prose is pacing blind. -/
theorem plan_prose_is_state_blind : ∀ s : StepState, planSeesState s = true := by
  intro s; rfl

/-! ## The de-risk: a SURVEY that checks the `def` over-alarms; checking the PRODUCER inverts the verdict -/

/-- A property's STATEMENT exists (the `def T`). -/
def definitionExists : Bool := true

/-- Whether a PRODUCER theorem (`: T := by`, `→ T`, `_of_…`) is found for the property. -/
def producerFound : Bool := true  -- the real `emit_scans_in_flow_rec_entry` at NonemptyStructure.lean:2418

/-- A survey that concludes "unproven" from the DEFINITION alone — it never looked for the producer. -/
def surveyVerdict_fromDefOnly : Bool := false  -- "definition only, no proof" — WRONG

/-- The SOURCE verdict: proven iff a producer theorem is found, regardless of the `def` existing. -/
def sourceVerdict_fromProducer : Bool := producerFound

/-- **NEGATIVE — a definition existing says NOTHING about whether the property is proven.**  The survey
    read `definitionExists = true` and a missing-proof shape and reported `false`; but the producer was
    there.  So the survey's verdict and the source's verdict DISAGREE — the survey over-alarmed. -/
theorem survey_overalarms_vs_source :
    surveyVerdict_fromDefOnly = false ∧ sourceVerdict_fromProducer = true := by
  exact ⟨rfl, rfl⟩

/-- **POSITIVE — grepping for the PRODUCER, not the `def`, yields the correct verdict.**  The source
    verdict ignores `definitionExists` entirely and reads off `producerFound`. -/
theorem source_verdict_reads_producer_not_def :
    sourceVerdict_fromProducer = producerFound := by rfl

/-! ## The payoff is a PACING decision: no wall behind the bricks ⇒ batch them -/

/-- After de-risk, each downstream step's resolved state. -/
def resolvedChain : List StepState :=
  [.alreadyProven, .trivialPlumbing, .parallelEffort, .openFunnel]

/-- "A wall" = a downstream step that is itself a NEW deep open obligation (not the one known funnel). -/
def isHiddenWall : StepState → Bool
  | .openFunnel => false      -- the funnel is KNOWN, not hidden
  | .alreadyProven => false
  | .trivialPlumbing => false
  | .parallelEffort => false  -- substantial, but already built — not a wall

/-- **POSITIVE — the de-risk confirms NO hidden wall behind the mechanical bricks.**  Every resolved step
    is proven / plumbing / already-built / the known funnel — none is a new deep surprise.  This is the
    licence to BATCH the mechanical bricks instead of grinding one-per-session. -/
theorem no_hidden_wall : ∀ s ∈ resolvedChain, isHiddenWall s = false := by
  intro s _; cases s <;> rfl

end Tests.Reflections.ReadAheadConsumerProofState
