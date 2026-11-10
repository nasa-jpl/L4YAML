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

def expectedDeadCensus : String :=
  "population=14256 thm=10245 def=2678 roots=capstone:26+export:37 unreached=7230 thm=5242 A-campaign=1298 C-api=1442 D-test-only=298 B-roster=4192 thm=3796 cluster-roots=1605"

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
