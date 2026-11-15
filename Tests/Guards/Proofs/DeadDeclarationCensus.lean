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
-- 2026-11-15 (#302 merge at ccc50f2d): +10 declarations are the three proof lemmas
-- `compactMapTail_append`, `ResumeFrames.one_of_route`, `markedCols_le_of_top`, plus
-- `KeyArm` and its six constructors (Row 12 / S3).  `MarkedColsIn.of_markedCols_nil`
-- is newly reached by the Row 12 proof, hence unreached −1 and B-roster thm −1;
-- the roster already dropped that name.  Pinned to CI run #43678091841's
-- measured summary on the exact merged source; no classifier or proof weakened.
def expectedDeadCensus : String :=
  "population=14379 thm=10314 def=2707 roots=capstone:27+export:37+blueprint:223(unresolved=5) unreached=6585 thm=4658 A-campaign=1361 C-api=1414 D-test-only=275 B-roster=3535 thm=3172 cluster-roots=1460"

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
