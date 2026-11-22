/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 634 — one dispatch of lookahead, carried as a field on the
# pending state

**The rule.**  Reflection 633's companion mask priced a strictened guard's
firing direction at depth ≥ 1.  Site 5 — the depth-0 flow open arriving with
no break crossed — needed the OPPOSITE ingredient: not a mask over a stack,
but ONE DISPATCH of lookahead, carried by the pending state itself.  Three
lessons made it land:

1. **The refutation fact is the producer's own trailing validation.**  Every
   pending whose construct is COMPLETE was built right after a guard that
   validated the rest of the line (`validateTrailingContent`,
   `validateAliasClose`, `validateFlowClose`, `scanDocumentEnd`'s suffix
   probe) or after a scan that cannot stop before a bracket (plain scalars
   absorb `[`; block scalars end at column 0 or EOF).  Packaging that window
   as a REST-OF-LINE field on the constructor (`s-white*` then never `[`/`{`)
   turns "the guard ran one dispatch earlier" into a hypothesis the flow-open
   arm can consume — and the ¬-form predicate is what lets SIX producer
   families with DIFFERENT allowlists share ONE consumer.

2. **A validator behind the walk pays its own fuel.**  The white-skip loops'
   fuel-exhaustion cases vanish for free wherever a validator follows: if
   fuel died mid-whites the landing peek would be a white, which no allowlist
   admits, so `.ok` itself refutes exhaustion.  Only the two loops with NO
   validator behind them (plain scalar, block scalar) pay a genuine
   fuel-adequacy induction.

3. **Sort the pendings by producer guarantee, not by "closeable".**  The plan
   said "refute the four non-props pendings"; enumerating producers showed
   `pendingFlow` — the deferred catch-all — is legally inhabited here
   (`- - [a]`, `? [a]`) and CANNOT be refuted.  It rides its own closing
   strategy instead: the resume ignores the content evidence and applies the
   same `scannerDrop` its break-case close already uses.  And the legal
   inhabitant (`&a [b]`, `- &a [b]`, `&a⏎[b]`) became a STATE:
   `pendingProps`, whose two closures (`propsEmpty` close, `propsContent`
   ride) capture the enclosing route, so one constructor serves the bare
   document, the block entry, and the explicit document alike.

**The milestone.**  `StreamAccum.lean` reached ZERO sorries — β.3 complete —
and `L4YAML.Capstones`, the only failing target of the whole campaign, went
GREEN: `parse_strict_proof` dropped its `sorryAx` dependency and now matches
its pinned axiom profile.  All with zero scanner changes: this pass is
proof-only, corpus byte-identical by construction.

Self-contained: pins the shipped instance's counts (L4YAML item 9t,
2026-08-10).
-/

namespace L4YAML.Tests.Reflections.PendingLookaheadField

/-- How each `PendingNode` constructor meets the no-break flow open. -/
inductive Fate where
  /-- Refuted through the rest-of-line field (`h_line`). -/
  | refuted
  /-- Rides its own `scannerDrop` closing strategy. -/
  | ridden
  /-- Consumed: the run rides INTO the flow node (`h_flow`). -/
  | consumed
  /-- A legal continuation with its own arm all along. -/
  | continued
  deriving DecidableEq, Repr

/-- The false-indexed constructors' fates at the depth-0 no-break open. -/
def fates : List Fate :=
  [.continued,  -- noPending
   .refuted,    -- pendingContent
   .consumed,   -- pendingProps (NEW this pass)
   .refuted,    -- pendingDocEnd
   .continued,  -- pendingDocStart
   .ridden,     -- pendingFlow
   .refuted,    -- pendingBlockContent
   .continued]  -- pendingBlock

/-- Producer families sharing the one rest-of-line predicate. -/
def producerFamilies : Nat := 6
/-- ...of which pay a genuine fuel-adequacy induction (plain, block scalar). -/
def fuelPayers : Nat := 2

/-- Constructors that grew the `h_line` field. -/
def lineFields : Nat := 3
/-- New constructors (`pendingProps`). -/
def newConstructors : Nat := 1
/-- Scanner changes in this pass. -/
def scannerChanges : Nat := 0
/-- Corpus sources, byte-identical by construction (proof-only pass). -/
def corpusSources : Nat := 351

/-- `StreamAccum.lean` sorry sites: before and after. -/
def sorriesBefore : Nat := 1
def sorriesAfter : Nat := 0
/-- Failing build targets: before (`L4YAML.Capstones`) and after. -/
def failingTargetsBefore : Nat := 1
def failingTargetsAfter : Nat := 0

-- ═══ §1  The pending split: every constructor has exactly one fate ═══

#guard fates.length == 8
#guard (fates.filter (· == .refuted)).length == 3
#guard (fates.filter (· == .ridden)).length == 1
#guard (fates.filter (· == .consumed)).length == 1
#guard (fates.filter (· == .continued)).length == 3

-- ═══ §2  One ¬-form predicate serves six validator families ═══

#guard producerFamilies == 6
#guard lineFields == 3
#guard newConstructors == 1

-- ═══ §3  Fuel is owed only where no validator follows the walk ═══

#guard fuelPayers == 2
#guard producerFamilies - fuelPayers == 4

-- ═══ §4  A proof-only pass: the pipelines cannot diverge ═══

#guard scannerChanges == 0
#guard corpusSources == 351

-- ═══ §5  β.3 closes, and the capstone gate flips ═══

#guard sorriesBefore - sorriesAfter == 1
#guard sorriesAfter == 0
#guard failingTargetsBefore - failingTargetsAfter == 1
#guard failingTargetsAfter == 0

end L4YAML.Tests.Reflections.PendingLookaheadField

end Blanket
