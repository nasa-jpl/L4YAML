import Tests.Guards.Proofs.DeadDeclarationRoster

/-!
# The dead-declaration census — the pins (DOCS items 476 / 477)

`lake run dead-census -- --check` (`Scripts/Main/DeadCensus.lean`, classifier
`Scripts/Dead/Census.lean`) recomputes, off the built environment of `L4YAML` + `Tests.Guards` +
`Tests.AdversarialInstantiation` + `Tests.Reflections`, every user-named library declaration no
`@[capstone]` / `@[export]` root reaches, splits it into (A) campaign in progress, (C) API by
convention, (D) Rule 2 / instrument-only and (B) the roster, and compares two pins:

* `expectedDeadCensus` — the one-line summary (counts); `--write` rewrites it.
* `expectedDeadRoster` (`DeadDeclarationRoster.lean`) — class (B) as a SET of fully-qualified
  names, shrink-only: a name entering it is a declaration reached by nothing — Rule 1's finding;
  a name leaving it was deleted or reached by a capstone.

The guard below ties the two: the roster's line count is the `B-roster=` the summary names, so
neither can be edited without the other.
-/

namespace L4YAML.Tests.Guards.DeadDeclarationCensus

-- 2026-11-12 (item 486, S3 slice (4) PR 1): population 14,226 → 14,236 (+9 lemmas, +1 def: `TraceOf/ContentBridge`), all ten in
-- (A) `Proofs.Serialization` (1,298 → 1,308) — no capstone chain reaches the twins until their caller lands; roster 3,536 unmoved.
-- 2026-11-12 (item 487, the K caller): population 14236 → 14243 (+7: `ContentLead` and its two constructors,
-- `tailOf_preprocess_eq`, `contentLead_of_interior`, `content_prop_tail_kept`, `accum_step_content_traceK`), thm +4,
-- unreached +7 and (A) 1308 → 1315 — the K caller has no capstone-path reader yet (the 2c fold is item 488's);
-- the (B) roster 3,536 unmoved, (C)/(D) unmoved.
-- 2026-11-14 (item 490, the ∀-floor fold): population 14,279 → 14,289 (+10: ContentBridge §10's nine lemmas and
-- `accum_step_content_pairK`), unreached +10 and (A) 1,351 → 1,361 — the fold is read by no root until the 2c fold
-- (`scan_trace`) composes it; the (B) roster 3,536 unmoved, (C)/(D) unmoved.
-- 2026-11-15 (item 506 rebased over items 505/508/510): the deletion's −87 (class (A)) recomposed over the base —
-- population 14,302 → 14,215, unreached 6,577 → 6,490, (A) 1,361 → 1,274; the roster 3,534 and (D) 277 are the
-- base's (item 505's `StreamAccum.seqEntryTail_cons` entered the roster unpinned on the base; the owner's call),
-- cluster-roots 1,460 → 1,461 (one roster name's cluster root recomputed after the module deletion).
-- 2026-11-15 (item 513, closeNestedColon, rebased over item 512's +1 reached): population 14,216 → 14,220 (+4: FlowWalk §6d's `closeNestedSeqColon` /
--- `closeNestedMapColon` / `closeNestedSeqPropsColon` / `closeNestedMapPropsColon`), unreached +4 and (A) 1,274 → 1,278 —
--- the nested close's `:` twin is read by no root until price (3)'s fold (`accum_step_flow_pairK`) consumes it; the (B)
--- roster 3,534, (C)/(D) and cluster-roots unmoved.
-- 2026-11-15 (item 517): +3 class (A) — `kmBit` / `kmBit_iff` (FlowWalk §8) and `content_km_transport_any`
-- (ContentBridge), reached only by `accum_step_flow_trace` / `accum_step_content_pairK` until the fold; roster unmoved.
-- 2026-11-15 (item 519): population +1 = `RegisterWitness.MarkedColsIn.mem`; `FlowBaseRoutes.vslot` LEFT the roster (3,534 → 3,533) — the projection is read at the four flow closes now; unreached −1.
-- 2026-11-15 (item 520): +7 class (A) composed over item 519's re-pin — `accum_step_flow_pairK` / `accum_step_flow_trace_uniform` / `dispatchFlow_km_faces` / `gapRead_onT_uniform` / `ColonKeyCase` (ContentBridge §10), `TFlowStackB.km_size` / `TFlowOpenStack.km_size` (FlowWalk) are reached by no root until (2c); cluster-roots 1,460 → 1,459 — unmoved by this item on item 518's tree and by item 519 on its own, −1 on the composed tree (an interaction of the two items' unreached sets; cause not read); roster unmoved.
-- 2026-11-17 (item 520, review round 2): population 14,231 → 14,229 (`flowOpen_stamp` / `flowOpen_marker` deleted); unreached
-- +23 → roster 3,533 → 3,556, cluster-roots 1,459 → 1,476 — the `implicitValueLine` / `docStartLine` PRESERVATION chain that
-- only fed `KmSound`'s stamp transport is now reached by nothing; re-pinned as read, the names listed in item 520 for the
-- owner's ruling (delete or keep), as item 505's `seqEntryTail_cons` was.
-- 2026-11-17 (item 522): population 14,229 → 14,237 (+8: ContentBridge §12's seven and `scanValue_km_transport`), unreached
-- +7 class (A) 1,288 → 1,295 — the key fold is reached by no root until the 2c fold `scan_trace` consumes it (`scanValue_km_transport`
-- is reached, by `accum_step_block`); roster 3,556 and cluster-roots unmoved.
-- 2026-11-17 (item 524, the deletion): the 23 `implicitValueLine` / `docStartLine` preservation lemmas item 520 listed for the
-- owner's ruling deleted on his word — roster 3,556 → 3,533, population −23, unreached −23; class (A) and cluster-roots read below.
-- 2026-11-18 (item 526, α): population 14,214 → 14,229 (thm +13), unreached 6,510 → 6,525, A-campaign 1,295 → 1,310 —
-- `TSLYamlStream` (structure, two projections) and the eleven DocBridge §α lemmas, reached by no root until the fold
-- spends them (class (A), as items 520 / 522); B-roster unmoved.
-- 2026-11-18 (item 527, β PR 1): population 14,229 → 14,242 (thm +8), unreached 6,525 → 6,538, A-campaign 1,310 → 1,323 —
-- `TPendingNode` (type + four constructors) and StreamBridge's eight lemmas, reached by no root until the fold spends
-- them (class (A), as items 520 / 522 / 526); B-roster unmoved.
-- 2026-11-19 (item 528, β PR 2): population 14,242 → 14,249 (thm +2), unreached 6,538 → 6,545, A-campaign 1,323 → 1,330 —
-- the five content-park constructors, `SSLComments_to_GStar_prefix` and the steps split by source park (five lemmas, were
-- three), reached by no root until the fold spends them (class (A)); B-roster unmoved.
-- 2026-11-19 (#302 integrated over item 526 and #349, base 4f31fef): full Lean 4.35.0
-- build 1,573/1,573; native `dead-census -- --check` measured population
-- 14,304 → 14,309, thm 10,247 → 10,249, def 2,701 → 2,702, unreached
-- 6,505 → 6,534 and A-campaign 1,281 → 1,310. The owner S3 development
-- changed the cluster-root count 1,460 → 1,459; capstone:27, blueprint:223,
-- C-api:1,414, D-test-only:277 and B-roster:3,533 are unchanged. The pin is
-- read on the merged tree, not summed from the two parents.
-- 2026-11-20 (#302 against upstream b9e0a5b, S3 Items 527-528 and Python #299):
-- The pin below is a compositional candidate from disjoint declarations, not a
-- measured exact-tree census. Run native `dead-census -- --write` and `--check`
-- on this source before upgrading the candidate to a warranted qualification.
def expectedDeadCensus : String :=
  "population=14329 thm=10259 def=2702 roots=capstone:27+export:37+blueprint:223(unresolved=5) unreached=6554 thm=4622 A-campaign=1330 C-api=1414 D-test-only=277 B-roster=3533 thm=3172 cluster-roots=1459"

/-- `B-roster=N` out of the summary. -/
def rosterCount (summary : String) : Option Nat := do
  let after ← (summary.splitOn "B-roster=")[1]?
  ((after.splitOn " ")[0]?).bind String.toNat?

def rosterLines : Nat :=
  ((DeadDeclarationRoster.expectedDeadRoster.splitOn "\n").filter (· ≠ "")).length

#eval do
  let some n := rosterCount expectedDeadCensus | throw (IO.userError "DeadDeclarationCensus: expectedDeadCensus names no B-roster count")
  if n != rosterLines then
    throw (IO.userError s!"DeadDeclarationCensus: the summary says B-roster={n} but DeadDeclarationRoster.lean holds {rosterLines} names — run `lake run dead-census -- --write`")

end L4YAML.Tests.Guards.DeadDeclarationCensus
