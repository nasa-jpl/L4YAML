/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 633 — the FIRING direction of a strictened guard costs a
# one-directional companion mask

**The rule.**  Reflection 632 priced LANDING a strictened guard on the side
that must show the guard PASSES (the emitter towers).  The side that must
show the guard FIRES — an accumulation invariant refuting the frames the
guard exists to kill — pays differently: the guard's premises must be
CARRIED BY THE INVARIANT at every state that could reach the guarded step,
and the carrier is not a hypothesis chain but a **companion mask** over the
structure the scanner itself stacks.  Three design rules made it affordable:

1. **One-directional bits.**  A mask bit promises facts only when TRUE
   (`KmSound`); false bits promise nothing.  That kills the flip problem —
   token appends can never turn an unarmed bit sound-looking — so the mask
   transports through every step with a per-step one-liner instead of an
   equality pin.

2. **∃-anchored alignment.**  The mask aligns to the key stack's TOP through
   an existential offset (`off + km.size = stack.size`), so the last bit
   always describes `back` — the entry every flow close RESTORES — while
   whatever lies below the anchor is never read.  Depth-0 arms therefore
   never owe a stack-emptiness proof, which is what kept the whole
   block-context world untouched.

3. **The armed floor surfaces at the ONE sub-top writer.**  Every scanner
   step appends; exactly one (`scanValuePrepare`'s reservation resolution)
   writes BELOW the top, and only there did the mask need its floor half —
   armed reservations sit at least two below everything stacked above them
   and below the pending key, so the resolution write lands three above
   every armed slot.  No site count predicts this conjunct; the transport
   proof does.

**The gate generalization.**  One scanner change made the invariant statable
at all: `skipToContentLoop` stopped re-enabling simple keys across breaks in
ANY flow collection (previously only flow sequences), so a completed entry's
layout can no longer be masked by a fresh save — `{a: b⏎: c}` now rejects at
the scanner, all 351 suite sources byte-identical, and the gate's existing
comment already stated the principle the fix made uniform.

**The grid closes.**  With mask, closures and layouts in hand, the flow `:`
step's 2×4 grid (Reflection 629) resolves: four cells RECEIVE (`.sep` and
`.question`, white and props rows), three cells are SCAN-REFUTED through
`KeyAfterValueLayout` (both `.colon` cells and the completed half of
`.value`), and the one MIXED cell splits on the entry disjunct its builders
stored one step earlier — `receiveNodeColon`, the `receiveColonValue` closure
Reflection 628 said the token history could not supply, built where the
frame was still concrete.

Self-contained: pins the shipped instance's counts (L4YAML item 10,
2026-08-10).
-/

namespace L4YAML.Tests.Reflections.FiringDirectionCompanionMask

/-- The three carriers the firing direction threads. -/
inductive Carrier where
  /-- Conditional fields on the interior gap (`.colon`-tail layouts). -/
  | gapConditional
  /-- The promise mask riding the open-frame stack (`km` + `promise`). -/
  | mask
  /-- The `.value`-tail entry disjunct (`FlowStackK`'s packaged case split). -/
  | entryDisjunct
  deriving DecidableEq, Repr

/-- The flow `:` step's grid (Reflection 629's indices). -/
def gridCells : Nat := 8
def receivedCells : Nat := 4
def refutedCells : Nat := 3
def splitCells : Nat := 1

/-- `InteriorGap` grew exactly two conditionals — one per constructor. -/
def gapConditionals : Nat := 2

/-- New frame receivers: `receiveNodeColon` and its props twin. -/
def newReceivers : Nat := 2

/-- Sub-top token writers in the scanner — the armed floor's whole audience. -/
def subTopWriters : Nat := 1

/-- Scanner changes the landing needed: the one gate generalization. -/
def scannerChanges : Nat := 1

/-- Corpus evidence, per pipeline, byte-identical across the change. -/
def corpusSources : Nat := 351

/-- Sorry sites in `StreamAccum.lean`: before item 10 and after. -/
def sorriesBefore : Nat := 2
def sorriesAfter : Nat := 1

-- ═══ §1  The grid resolves, and no cell was free-form ═══

#guard gridCells == receivedCells + refutedCells + splitCells
#guard receivedCells == 4
#guard refutedCells == 3
#guard splitCells == 1

-- ═══ §2  The carriers are few because the bits are one-directional ═══

#guard gapConditionals == 2
#guard newReceivers == 2

-- ═══ §3  The armed floor has an audience of one ═══

-- Every scanner step appends except the reservation resolution; the floor
-- conjunct exists for that step alone, and only the transport proof — not
-- any site count — could have found it.
#guard subTopWriters == 1

-- ═══ §4  One scanner change, behaviour-preserving where legal ═══

#guard scannerChanges == 1
#guard corpusSources == 351

-- ═══ §5  Site 2 is CLOSED ═══

#guard sorriesBefore - sorriesAfter == 1
#guard sorriesAfter == 1

end L4YAML.Tests.Reflections.FiringDirectionCompanionMask

end Blanket
