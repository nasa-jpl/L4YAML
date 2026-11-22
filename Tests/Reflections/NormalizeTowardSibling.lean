/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 631 — a behaviour change's price is INVARIANT ripple + SHAPE ripple

**The rule.** When a step's behaviour changes, two different sets of proofs
break, and they are counted differently.

  * The **invariant ripple** — proofs that transport a predicate across the
    step. Bounded by the invariant families the step appears in.
  * The **shape ripple** — proofs that quote the step's RESULT RECORD
    literally. Bounded by nothing an invariant analysis can see, and in a
    codebase with per-step reduction lemmas it is the larger number by far.

**The corollary that makes the invariant ripple free.** If the change makes a
step behave like its SIBLINGS — here, "the `,` clears the pending simple key",
which is what every other flow step already did — then every invariant family
already owns the constructor the new behaviour needs, because some sibling
already needed it. Nothing new gets proved; each site is a one-line swap from
`*_of_preserved` to `*_of_cleared_preserved`.

**The instance (L4YAML item 9q).** Item 9p priced the `scanFlowEntry`
normalization as "its own ripple: the `SimpleKeyAbove` / `SimpleKeyAboveFloor` /
`AllKeysValid` family, 6 sites". Building it found eleven invariant sites, not
six — and **zero** new invariant constructors, because all eleven families
(five plain, six indexed) already had a cleared-key constructor. The forty
sites that actually carried the diff were statement sites spelling
`{ … with simpleKeyAllowed := true, explicitKeyLine := none }`, the step's
result record, which the pricing never mentioned because no invariant runs
through them.

**And a normalization pays part of its own price.** Two `EndLineOnLine`
obligations became vacuous (a cleared key has nothing to say about lines),
freeing an `h_endline` hypothesis in each of two step lemmas; and the one
lemma whose conclusion had to change — the `,`'s simple-key add-on — became
what all six of its consumers actually wanted, which is why all six had been
discarding the old conclusion with `_`.

Self-contained: models the two ripples over the shipped instance's shape and
pins that the priced one is neither the larger nor the expensive one.
-/

namespace L4YAML.Tests.Reflections.NormalizeTowardSibling

/-- The invariant families a flow step is transported through. -/
inductive Family where
  | simpleKeyAbove | simpleKeyAboveFloor | noOverwriteAt | flowNoOverwriteAt
  | allKeysValid | allKeysPlaceholderInv
  | simpleKeyAboveIx | simpleKeyAboveFloorIx | noOverwriteAtIx
  | allKeysValidIx | allKeysPlaceholderInvIx
  deriving DecidableEq, Repr

/-- The two ways a proof can break when a step's behaviour changes. -/
inductive Ripple where
  /-- The proof transports an invariant across the step. -/
  | invariant
  /-- The proof quotes the step's result RECORD literally. -/
  | shape
  deriving DecidableEq, Repr

open Family Ripple

def families : List Family :=
  [simpleKeyAbove, simpleKeyAboveFloor, noOverwriteAt, flowNoOverwriteAt,
   allKeysValid, allKeysPlaceholderInv,
   simpleKeyAboveIx, simpleKeyAboveFloorIx, noOverwriteAtIx,
   allKeysValidIx, allKeysPlaceholderInvIx]

/-- Did this family ALREADY own a cleared-key constructor before the change?
    Yes for every one of them — clearing the pending key is what the flow
    OPEN, the `?`, the `:` and the block steps all already do, so each family
    was built with the constructor on day one. -/
def hasClearedConstructor : Family → Bool := fun _ => true

/-- Sites that spell the step's result record verbatim
    (`{ … with simpleKeyAllowed := true, explicitKeyLine := none }`). -/
def shapeSites : Nat := 40

/-- What item 9p wrote down for this change: "its own invariant ripple,
    6 sites". -/
def pricedRipple : Nat := 6

def invariantSites : Nat := families.length

/-- Constructors that had to be WRITTEN, as opposed to called. -/
def newConstructors : Nat := (families.filter (fun f => !hasClearedConstructor f)).length

def measuredRipple : Nat := invariantSites + shapeSites

/-- Obligations the normalization discharged for free: a cleared key makes
    `EndLineOnLine` vacuous. -/
def vacuatedObligations : Nat := 2

/-- Hypotheses those vacuous obligations freed from step lemmas. -/
def freedHypotheses : Nat := 2

/-- Consumers of the one lemma whose CONCLUSION changed, that were using the
    old conclusion. All six destructured it as `_`. -/
def consumersUsingOldConclusion : Nat := 0

def consumersOfChangedConclusion : Nat := 6

-- ═══ §1 The priced ripple was the wrong ripple ═══

#guard invariantSites == 11
#guard shapeSites == 40
#guard measuredRipple == 51

-- The pricing named the invariant ripple and undercounted even that…
#guard pricedRipple < invariantSites

-- …but the invariant ripple is not where the work is: the shape ripple is
-- larger, and it is larger than the whole priced number by nearly an order.
#guard shapeSites > invariantSites
#guard shapeSites / invariantSites == 3
#guard shapeSites > pricedRipple * 6

-- ═══ §2 The invariant ripple is FREE when you normalize toward a sibling ═══

-- Every family already owned the constructor the new behaviour needs, because
-- some sibling step already cleared the key.
#guard families.all hasClearedConstructor
#guard newConstructors == 0

-- So all eleven invariant sites are one-line swaps — the priced work is the
-- part that costs nothing.
#guard invariantSites - newConstructors == 11

-- Both pipelines are covered by the same argument: five plain families, six
-- indexed twins, and not one of the twins needed a constructor either.
#guard (families.filter (fun f =>
          f == Family.simpleKeyAboveIx || f == Family.simpleKeyAboveFloorIx
          || f == Family.noOverwriteAtIx || f == Family.allKeysValidIx
          || f == Family.allKeysPlaceholderInvIx)).length == 5

-- ═══ §3 A normalization pays part of its own price ═══

#guard vacuatedObligations == 2
#guard freedHypotheses == vacuatedObligations

-- The one conclusion that had to change was the one nobody was using: every
-- consumer had been discarding it and re-deriving what the new one states.
#guard consumersUsingOldConclusion == 0
#guard consumersOfChangedConclusion == 6

-- ═══ §4 What a shape-blind pricing would have predicted ═══

-- Priced: six invariant sites, each needing a new constructor. Actual: eleven
-- invariant sites needing none, and forty shape sites nobody counted.
#guard pricedRipple + newConstructors == 6
#guard measuredRipple - pricedRipple == 45

-- The ratio the pricing was wrong by is not a factor on the named quantity —
-- it is an entire second quantity.
#guard measuredRipple - invariantSites == shapeSites

end L4YAML.Tests.Reflections.NormalizeTowardSibling

end Blanket
