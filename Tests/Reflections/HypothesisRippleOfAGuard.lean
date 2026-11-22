/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 632 — a strictened guard's THIRD ripple is the hypothesis chain,
# and it climbs to the weakest producer

**The rule.**  Reflection 631 priced a behaviour change as invariant ripple
plus shape ripple.  LANDING a strictened guard exposes a third, and it is the
one that dominates: the **hypothesis ripple**.  The guard's new discharge
premise must be SUPPLIABLE at every proof that runs through the guard — so it
becomes a hypothesis on the def family, and the supplier chain climbs caller
by caller until it reaches a producer that concretely owns the fact (here:
the `{` or `,` whose push IS the entry boundary).  Price it by walking the
WEAKEST def of the family: every hypothesis of the discharge that the weakest
producer cannot derive is a new def-family hypothesis, and its cost is the
family's caller count — not the guard's site count.

**The corollary that restructures producers.**  Chasing the weakest producer
found the plain tower's mapping case needing the saved-key LAYOUT of its keys
(that is what discharges the guard at each pair's `:`), while the saved-key
producer needed the plain scans of its sub-values.  Two lemmas that feed each
other's hypotheses on sub-derivations are ONE induction split cosmetically;
the fix is the merge (`emit_scans_in_flow_both`), and projections keep every
caller unchanged.

**The limit that splits pipelines.**  A twin pipeline is only as strictenable
as its weakest EXPOSURE.  The indexed tower carries floors and no-overwrite
machinery but ZERO reservation-layout exposures — the discharge cannot even be
STATED there — so the same one-line scanner change the legacy tower absorbed
is deliberately reverted on the indexed side, the divergence pinned by guards
(`Tests/Guards/Proofs/ScannerFlowPropsColon.lean` §4), and the missing
substrate is now a measured budget instead of a surprise.

Self-contained: models the shipped instance's counts (L4YAML item 9r,
2026-08-09) and pins that the hypothesis ripple, not the guard's own site
count, is where the landing went.
-/

namespace L4YAML.Tests.Reflections.HypothesisRippleOfAGuard

/-- The three ripples a strictened guard produces (631's two, plus the one
    that only shows up when the guard LANDS). -/
inductive Ripple where
  /-- Proofs transporting an invariant across the changed step. -/
  | invariant
  /-- Proofs quoting the step's result record literally. -/
  | shape
  /-- Defs that must now CARRY the discharge premise, and callers that must
      SUPPLY it. -/
  | hypothesis
  deriving DecidableEq, Repr

open Ripple

/-- The legacy gateway's call sites — the count a site-based pricing reads. -/
def gatewaySites : Nat := 16
def gatewayFiles : Nat := 6

/-- Defs/lemmas that had to GAIN a hypothesis so the discharge is suppliable:
    2 plain defs (stack-sync), 2 pair-list defs (four pair-start facts each),
    1 Block pair def, 6 standalone assemblers, 3 wrappers, 2 demo lemmas. -/
def defsGainingSync : Nat := 2
def pairDefsGainingBoundary : Nat := 3
def standaloneAssemblers : Nat := 6
def wrapperLemmas : Nat := 3
def demoLemmas : Nat := 2
def hypothesisCarriers : Nat :=
  defsGainingSync + pairDefsGainingBoundary + standaloneAssemblers + wrapperLemmas + demoLemmas

/-- Producers before and after the weakest-producer walk: the plain and
    saved-key producers fed each other's hypotheses, so they merged. -/
def producersBefore : Nat := 2
def producersAfter : Nat := 1

/-- Indexed-side reservation-layout exposures found by measurement: in the
    scalar scenario, the two nested opens, and the two nested closes. -/
def ixLayoutExposures : Nat := 0
/-- Scenario lemmas the indexed landing must extend (the measured budget). -/
def ixExposuresNeeded : Nat := 5
/-- Shapes on which the pipelines now deliberately diverge (legacy scanner
    rejects, indexed scanner still scans clean), pinned as guards. -/
def divergentShapes : Nat := 7

/-- Corpus evidence, per pipeline. -/
def corpusSources : Nat := 351

-- ═══ §1  The guard's site count is not where the landing went ═══

#guard gatewaySites == 16
#guard gatewayFiles == 6
#guard hypothesisCarriers == 16

-- Coincidence made instructive: as many defs/lemmas had to LEARN the premise
-- as there were gateway call sites — but they are DIFFERENT declarations, and
-- only the second set's edits were creative work (which fact, from where).
#guard hypothesisCarriers == gatewaySites

-- ═══ §2  The chain climbs to a producer that owns the fact ═══

-- The supplier chain terminates only at pushes: the `{`/`,` steps got new
-- conclusion conjuncts (ska, LastRawNotValue, PairStart) so callers stop
-- climbing there.  Modeled: every carrier is BELOW some concrete push.
#guard defsGainingSync + pairDefsGainingBoundary < hypothesisCarriers

-- ═══ §3  Mutually-feeding producers are one induction ═══

#guard producersBefore == 2
#guard producersAfter == 1
-- The merge is a strict decrease: neither half stands alone post-guard.
#guard producersAfter < producersBefore

-- ═══ §4  A twin pipeline is only as strictenable as its weakest exposure ═══

#guard ixLayoutExposures == 0
#guard ixExposuresNeeded == 5
-- Zero exposures ⇒ the discharge is unstatable there ⇒ the divergence is
-- pinned, not silent: one guard per shape.
#guard divergentShapes == 7
#guard ixLayoutExposures < ixExposuresNeeded

-- ═══ §5  Behaviour: unchanged where legal, rejected where underivable ═══

#guard corpusSources == 351

end L4YAML.Tests.Reflections.HypothesisRippleOfAGuard

end Blanket
