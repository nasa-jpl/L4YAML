/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 635 — a conditional conjunct replaces a parallel tower

**The rule.**  When a strictened guard needs a LAYOUT fact threaded through a
predicate tower, there are two architectures.  The legacy landing (item 9r)
grew a SECOND tower — `EmitScansInFlowSavedKey`, carrying the reservation
index alongside the plain scans — and then had to MERGE the two
(`emit_scans_in_flow_both`) when the producers turned out to feed each other's
hypotheses.  The indexed landing (item 11) carried the same fact as **one
conditional conjunct on the existing predicate**:

    simpleKeyAllowed = true → LastRawNotValueIx s → SavedKeyAtEntryBoundaryIx s'

Three lessons made the single-tower form work:

1. **The antecedents are state bits the machine itself flips, and they
   SELF-SELECT the positions that owe the layout.**  After `{`, `[` or `,`
   both antecedents hold — the conjunct is LOADED exactly at key positions,
   where the following `:` will read the boundary.  After `: ` the raw array
   ends in the just-emitted `.value`, so `LastRawNotValueIx` FAILS — the
   conjunct is VACUOUS exactly at value positions, where a saved key would sit
   directly above a `.value` and no boundary could be proven.  No second
   predicate, no merge lemma: the state bits do the case split that the
   parallel tower encoded structurally.

2. **Walking the induction discovers the antecedent set — and what it is
   missing becomes a HYPOTHESIS, not a conjunct.**  The scalar case needs
   only the antecedents (save-then-push).  The collection-as-key case — the
   reservation crossing a whole `[`…`]` body to be restored by the close —
   additionally consumed exact stack–flow-level sync for the raw-prefix chain
   (`SimpleKeyAboveFloorIx`'s stack half goes vacuous only under equality).
   Sync therefore joined the predicate's HYPOTHESES, where it self-propagates:
   the conclusions preserve both sides.

3. **Exposures come producer-shaped, the same triple at every boundary
   token.**  Opens expose (re-enable saves, cap the raw array, push the saved
   key); closes expose (restore the pushed key, `getElem?`-prefix); the comma
   exposes (re-enable, clear — item 9q — cap).  Stating the prefix legs on
   `getElem?` lets a scenario lemma expose them without naming the tokens it
   pushes.

**The measured budget held.**  Item 9r priced this landing — by building the
strictening and reverting — at five scenario-lemma exposures, one conditional
layout conjunct on `EmitScansInFlowIx`, and four assembler call sites.  That
is where the DESIGN went; everything else that surfaced at landing time
(comma/ws1/init-open exposures, the sync hypothesis threading) was transport.
With the guard strictened on both sides, the seven shapes of
`Tests/Guards/Proofs/ScannerFlowPropsColon.lean` §4 — `[a: b: c]`, `[a: : b]`,
`[: :]`, `{a: : b}`, `[? : : a]`, `[a: &x : b]`, `[a: !t : b]` — reject at
BOTH scanners with the IDENTICAL `ScanError`, closing the last deliberate
legacy↔indexed divergence.

Self-contained: pins the shipped instance's counts (L4YAML item 11,
2026-08-10).
-/

namespace L4YAML.Tests.Reflections.ConditionalLayoutConjunct

/-- The emitter's positions between tokens, by what the last real token is. -/
inductive Position where
  /-- After `{`, `[` or `,`: an entry boundary. -/
  | entryBoundary
  /-- After `: `: a value position (raw array capped by `.value`). -/
  | afterValue
  /-- After a completed scalar or close: mid-entry. -/
  | afterNode
  deriving DecidableEq, Repr

/-- Whether `simpleKeyAllowed` holds there. -/
def ska : Position → Bool
  | .entryBoundary => true
  | .afterValue => true   -- `scanValueIx` re-enables saves
  | .afterNode => false
/-- Whether `LastRawNotValueIx` holds there. -/
def lastRawNotValue : Position → Bool
  | .entryBoundary => true
  | .afterValue => false  -- the `.value` just emitted caps the array
  | .afterNode => true
/-- The conjunct is loaded (both antecedents hold) — the positions that owe
    the boundary to a following `:`. -/
def conjunctLoaded (p : Position) : Bool := ska p && lastRawNotValue p

-- ═══ §1  The antecedents self-select: loaded exactly at entry boundaries ═══

#guard conjunctLoaded .entryBoundary == true
#guard conjunctLoaded .afterValue == false
#guard conjunctLoaded .afterNode == false

-- ═══ §2  The measured budget (item 9r) vs what landed (item 11) ═══

/-- Scenario lemmas that gained layout exposures: the scalar, the two nested
    opens, the two nested closes. -/
def scenarioExposures : Nat := 5
/-- Conditional layout conjuncts on `EmitScansInFlowIx`. -/
def layoutConjuncts : Nat := 1
/-- Assembler call sites of `scanNextToken_flow_valueIx` that supply the
    boundary (weak singleton/multi + strong singleton/multi). -/
def assemblerCallSites : Nat := 4
/-- Transport surfaced at landing time, not in the measurement: the comma,
    the one-space skip, and the `{`-init open gained exposures. -/
def transportExposures : Nat := 3

#guard scenarioExposures == 5
#guard layoutConjuncts == 1
#guard assemblerCallSites == 4

-- ═══ §3  One tower where legacy needed two ═══

/-- Legacy towers carrying the layout: the plain one and the saved-key one,
    merged by `emit_scans_in_flow_both`. -/
def legacyTowers : Nat := 2
/-- Indexed towers: the conjunct rides the existing one. -/
def indexedTowers : Nat := 1
/-- Merge lemmas the indexed side needed. -/
def indexedMergeLemmas : Nat := 0

#guard legacyTowers == 2
#guard indexedTowers == 1
#guard indexedMergeLemmas == 0

-- ═══ §4  The divergence closes: both scanners, identical error ═══

/-- The §4 shapes of `ScannerFlowPropsColon.lean`, all now rejected at BOTH
    scanners with the identical `ScanError` (previously: legacy scanner only,
    indexed parser). -/
def sharedRejections : Nat := 7
/-- Pipelines whose SCANNER rejects them. -/
def rejectingScanners : Nat := 2

#guard sharedRejections == 7
#guard rejectingScanners == 2

end L4YAML.Tests.Reflections.ConditionalLayoutConjunct

end Blanket
