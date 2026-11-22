/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 646 — a branch the runtime cannot take is not a case you owe; count a deferral's domain over REACHABLE inputs, and refute the rest from the dispatcher itself

**The rule.**  A proof's case split is chosen by the prover; the branches the
code can actually take are chosen by the code.  When the split is finer than
the dispatch — a classical `by_cases` on a character, a `cases` on a
constructor the producers never build — the extra branches are PHANTOMS.  Route
them to an escape hatch and they enter its stated domain as if they were input,
which is how a deferral comes to claim more than it owes.  The fix is one lemma
read off the dispatcher (`some` result ⇒ the character is one of the three it
tests), applied at every phantom site at once.

**And it sharpens the honest measure.**  [[CoverageNotCallSites]] said to report
the DOMAIN rather than the call-site count.  That is right, but the domain must
be counted over inputs that can REACH the escape: refuting a phantom drops the
domain and the sites together — merge's signature exactly — while composing no
new input at all.  So `merge` and `refute` are indistinguishable in both of
R645's measures and differ in the only thing that matters.  A third measure is
needed, and it is the one the campaign actually cares about: how many families
the parser accepts that the accumulation still cannot compose.

Concretely (L4YAML): four block-dispatch lemmas split `by_cases hc : c = '-'`
and then `by_cases hcv : c = ':' ∨ c = '?'`, sending the last branch to
`block_dispatch_deferred`.  But `scanNextToken_dispatchBlockIndicators` opens
each of its three arms with its own literal test and falls through to `none`
otherwise, so a `.ok (some s')` result NAMES the character: no fourth block
indicator exists.  `dispatchBlockIndicators_indicator_of_some` is that reading;
`block_indicator_exhausted` is the three-way contradiction the four sites use.
Sites 18 → 14, and the family they represented was never input.

§1 is the model: a dispatcher, a finer split, and the phantom branch.  §2 is the
reachability refutation and why it closes every site at once.  §3 is the
measurement — the three edit kinds R645 separates, plus `refute`, which its two
measures cannot tell from `merge`.  §4 the shipped counts.

Self-contained: the dispatcher and its split, the exhaustiveness reading, the
four-way measurement, and the counts.
-/

namespace L4YAML.Tests.Reflections.PhantomBranchNotADeferral

/-! ## §1  A dispatcher, and a split finer than it

  The runtime tests three literals and falls through; the proof splits the
  whole character type. -/

/-- Stand-in for the scanned character. -/
abbrev Ch := Nat

/-- `-`, `:`, `?` — the three block indicators. -/
def dash : Ch := 0
def colon : Ch := 1
def question : Ch := 2

/-- The dispatcher: fires only on its own three literals, `none` otherwise —
    the shape of `scanNextToken_dispatchBlockIndicators`, whose three arms each
    open with `c == '-'` / `c == '?'` / `c == ':'`. -/
def dispatch (c : Ch) : Option Ch :=
  if c = dash then some c
  else if c = question then some c
  else if c = colon then some c
  else none

/-- **The reading.**  A `some` result names its character.  This is the whole
    content of the refutation: it is a fact about the CODE, available without
    any grammar, any invariant, or any new production. -/
theorem indicator_of_some {c c' : Ch} (h : dispatch c = some c') :
    c = dash ∨ c = question ∨ c = colon := by
  unfold dispatch at h
  by_cases hd : c = dash
  · exact Or.inl hd
  · by_cases hq : c = question
    · exact Or.inr (Or.inl hq)
    · by_cases hv : c = colon
      · exact Or.inr (Or.inr hv)
      · simp [hd, hq, hv] at h

/-- The four block-dispatch lemmas' shared contradiction: with `-` and the two
    mapping indicators taken, nothing is left. -/
theorem exhausted {c c' : Ch} (h : dispatch c = some c')
    (hdash : ¬ c = dash) (hmap : ¬ (c = colon ∨ c = question)) : False := by
  rcases indicator_of_some h with h | h | h
  · exact hdash h
  · exact hmap (Or.inr h)
  · exact hmap (Or.inl h)

/-! ## §2  One lemma, every site

  The split is per-lemma; the refutation is not.  Each of the four sites
  discharges with the same term, so the cost is one lemma and four one-line
  arms — the opposite of the per-site work an arm would have needed. -/

/-- The phantom branch, as the four lemmas reach it. -/
def phantomBranch (c c' : Ch) (h : dispatch c = some c')
    (hdash : ¬ c = dash) (hmap : ¬ (c = colon ∨ c = question)) : Empty :=
  (exhausted h hdash hmap).elim

/-- And there is nothing to build there: the branch has no inhabitant to
    produce, because it has no input to produce it for. -/
theorem phantom_is_empty (c c' : Ch) (h : dispatch c = some c')
    (hdash : ¬ c = dash) (hmap : ¬ (c = colon ∨ c = question)) :
    ∀ P : Prop, P :=
  fun _ => (exhausted h hdash hmap).elim

/-! ## §3  The measurement R645 could not make

  [[CoverageNotCallSites]] models an escape hatch by its domain (which inputs
  it still owns) and its sites (how often it is written).  Refuting a phantom
  moves BOTH down — the same signature as a merge — while composing nothing.
  So the honest measure has to be the reachable domain. -/

/-- Input families, and whether the dispatcher can actually deliver them. -/
structure Family where
  /-- Identifier. -/
  id : Nat
  /-- Can a real input reach the escape through this branch? -/
  reachable : Bool
  deriving DecidableEq

/-- Whites before the indicator — an indented block collection. -/
def indented : Family := ⟨0, true⟩
/-- A mid-line park that crosses no break. -/
def residue : Family := ⟨1, true⟩
/-- `pendingBlockContent` at a nonzero entry indent. -/
def nonzeroIndent : Family := ⟨2, true⟩
/-- A character that is not a block indicator — the phantom. -/
def notAnIndicator : Family := ⟨3, false⟩
/-- `noPending` parked at a column other than 0 — real, and item 21 folded it
    into `residue` by gating on the landing instead of the park. -/
def parkedOffColumn : Family := ⟨4, true⟩

/-- The escape hatch under all three measures at once. -/
structure Escape where
  /-- Everything the branch structure sends here. -/
  domain : List Family
  /-- How many times it is written. -/
  sites : Nat
  deriving DecidableEq

/-- What it still owes: the families a real input can reach. -/
def reachableDomain (e : Escape) : List Family := e.domain.filter (·.reachable)

def start : Escape := ⟨[indented, residue, nonzeroIndent, notAnIndicator, parkedOffColumn], 18⟩

/-- **Refute** — prove the branch unreachable.  Domain down, sites down. -/
def refute (e : Escape) : Escape :=
  ⟨e.domain.filter (· != notAnIndicator), e.sites - 4⟩

/-- **Fold** — re-gate so a real family is handled by an existing arm's route
    (item 21's landing gate: `parkedOffColumn` merges into `residue`).  One
    family leaves; the sites are unchanged, the deferral simply reached
    through a different branch. -/
def fold (e : Escape) : Escape :=
  ⟨e.domain.filter (· != parkedOffColumn), e.sites⟩

/-- **Compose** — build the arm.  A REACHABLE family leaves. -/
def compose (e : Escape) : Escape :=
  ⟨e.domain.filter (· != indented), e.sites - 8⟩

def afterRefute : Escape := refute start
def afterFold : Escape := fold afterRefute

#guard start.sites == 18
#guard afterRefute.sites == 14
#guard afterFold.sites == 14

/-- **The phantom inflated both of R645's measures.**  Removing it looks
    exactly like progress under either one. -/
theorem refute_looks_like_progress :
    afterRefute.domain.length < start.domain.length ∧
    afterRefute.sites < start.sites := by decide

/-- **…and composed nothing.**  Under the reachable-domain measure it is a
    no-op: the parser never sent an input down that branch. -/
theorem refute_composed_nothing :
    (reachableDomain afterRefute).length = (reachableDomain start).length := by decide

/-- Whereas building the arm does move it. -/
theorem compose_moves_the_real_measure :
    (reachableDomain (compose afterFold)).length <
      (reachableDomain afterFold).length := by decide

/-- Folding a real family into an existing route moves the real measure too,
    and leaves the site count alone — the third signature, distinct from both
    `refute` (sites fall, reachable domain flat) and `compose` (both fall). -/
theorem fold_moves_it_without_moving_sites :
    (reachableDomain afterFold).length < (reachableDomain afterRefute).length ∧
    afterFold.sites = afterRefute.sites := by decide

/-- The four edit kinds are pairwise distinguishable only under the reachable
    measure: `refute` and a merge agree on domain-length AND on sites. -/
theorem stated_domain_cannot_separate_them :
    (afterRefute.domain.length < start.domain.length ∧
      afterRefute.sites < start.sites) ∧
    ((compose afterFold).domain.length < afterFold.domain.length ∧
      (compose afterFold).sites < afterFold.sites) := by decide

/-- The reachable measure separates them. -/
theorem reachable_domain_separates_them :
    (reachableDomain afterRefute).length = (reachableDomain start).length ∧
    (reachableDomain (compose afterFold)).length < (reachableDomain afterFold).length := by
  decide

/-! ## §4  The shipped counts (item 21, 2026-08-11) -/

/-- New lemmas: the dispatcher reading and its three-way contradiction. -/
def newLemmas : Nat := 2
/-- Phantom sites discharged by them. -/
def phantomSites : Nat := 4
/-- Deferral call sites before… -/
def sitesBefore : Nat := 18
/-- …after the refutation… -/
def sitesAfterRefute : Nat := 14
/-- …and after the landing gate, which moves a family without moving the count. -/
def sitesAfterFold : Nat := 14
/-- Reachable families the deferral owned before item 21. -/
def reachableFamiliesBefore : Nat := 4
/-- …and after: `parkedOffColumn` folded into the residue. -/
def reachableFamiliesAfter : Nat := 3
/-- Grammar constructors added. -/
def newGrammarConstructors : Nat := 0
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0

#guard newLemmas == 2
#guard phantomSites == 4
#guard sitesBefore - phantomSites == sitesAfterRefute
#guard sitesAfterFold == sitesAfterRefute
#guard reachableFamiliesBefore == reachableFamiliesAfter + 1
#guard newGrammarConstructors == 0
#guard runtimeEdits == 0

end L4YAML.Tests.Reflections.PhantomBranchNotADeferral

end Blanket
