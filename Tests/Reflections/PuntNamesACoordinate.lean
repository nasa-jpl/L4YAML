/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 654 — an optional field's punt names a COORDINATE, not a difficulty: re-measure the producer where the runtime pushes

**The rule.**  [[OptionalFieldBuysDomain]] says to carry a new invariant
obligation as `P ∨ True`, so a producer that cannot establish it hands `True`
back instead of opening a new escape route.  That leaves a record: every `True`
is a producer you did not reach.  When you come back for one, do not start by
trying to make its case *harder-but-provable* — read WHY it punted.  If the
reason was that the runtime measures at a different coordinate than your lemma
names, the repair is to restate the producer's lemma AT the coordinate the
runtime uses.  Nothing about the runtime moves; the lemma stops naming the
wrong column.

**Why that is a repair and not a generalization.**  Both lemmas describe the
same push.  What changes is which of the state's coordinates the hypothesis is
stated about — and a hypothesis about the used coordinate is dischargeable by
the producer that pushes there, while a hypothesis about an unused one is not,
at any strength.  So the punt was never evidence that the case was hard; it was
evidence that the question had been asked in the wrong units
([[DifferentQuestionNotAHarderCase]], one layer down: there a case was not an
instance of the question, here it was not an instance of the MEASUREMENT).

**Where the new hypothesis comes from — check both sides first.**  A repair
like this costs machinery only if the coordinate is genuinely absent.  Usually
it is not: in a correspondence proof the same quantity is often already carried
on BOTH sides under different names, and what is missing is the equation
between them.  Then the item is one conjunct — and, by
[[OptionalFieldBuysDomain]] again, that conjunct should itself be optional, so
the producers that cannot supply it keep the coverage they already had.

**The check that keeps you honest.**  Confirm the new lemma does not RETIRE the
old one.  Re-measuring trades domain: it reaches the producers that push at the
new coordinate and loses the ones that have no such coordinate to offer.  If
the two lemmas' domains are incomparable, keep both as siblings (the choice
[[DifferentQuestionNotAHarderCase]]'s item made) rather than deleting a working
lemma to make the story tidier.

Concretely (L4YAML): item 27 measured `scanValuePrepare`'s block-mapping push at
the `:`'s own column, which is the resolved key's only when the save was fresh,
so item 15's `  a: |` handed `True`.  Item 28 measures the same push at
`s.simpleKey.pos.col` — the column it actually uses — and the missing
hypothesis was already present on both sides of the correspondence: as
`[63] s-indent(k)` on the surface (`ImplicitKeyPack`'s own index since item 25)
and as the saved key's column on the scanner.  One optional conjunct couples
them; the alias and property-headed keys hand `True` and keep item 17's
coverage.

§1 is punt-as-coordinate.  §2 is siblings, not replacement.  §3 is the quantity
already on both sides.  §4 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.PuntNamesACoordinate

/-! ## §1  The punt named a coordinate

One runtime push, two lemmas about it.  The push is a fixed function of the
state — the item cannot and does not touch it.  What the item chooses is which
coordinate the hypothesis is stated about. -/

/-- Where the `:`'s saved key came from, as far as the push is concerned. -/
inductive Save where
  /-- Saved at the indicator itself — `[189]`'s empty-key entry (item 13). -/
  | fresh
  /-- Inherited from a key scanned earlier on the line — item 15's `a: v`. -/
  | inherited
  /-- No key at all: the `:` opens the mapping at its own column. -/
  | keyless
  deriving DecidableEq, Repr

/-- All of them. -/
def saves : List Save := [.fresh, .inherited, .keyless]

/-- Whether there is a key for the push to resolve. -/
def hasKey : Save → Bool
  | .fresh => true
  | .inherited => true
  | .keyless => false

/-- The two coordinates the state carries. -/
structure St where
  /-- The indicator's own column. -/
  col : Nat
  /-- The column of the key the `:` resolves. -/
  keyCol : Nat
  deriving Repr

/-- **The runtime.**  `scanValuePrepare` pushes at the RESOLVED KEY when there
    is one, and at the indicator when there is not.  This function is what both
    lemmas below are about; neither item changed a line of it. -/
def pushedAt (v : Save) (s : St) : Nat := if hasKey v then s.keyCol else s.col

/-- A save is FRESH exactly when the two coordinates coincide. -/
def Fresh (s : St) : Prop := s.keyCol = s.col

/-- **Item 27's floor**, stated at the INDICATOR's column.  It needs the two
    coordinates to coincide wherever a key exists — which is freshness. -/
theorem floor_at_indicator {n : Nat} {v : Save} {s : St}
    (h_coord : hasKey v = true → Fresh s) (h : n ≤ s.col) : n ≤ pushedAt v s := by
  unfold pushedAt
  cases hv : hasKey v with
  | false => simpa [hv] using h
  | true =>
    have := h_coord hv
    unfold Fresh at this
    simp only [this]
    exact h

/-- **Item 28's floor**, stated at the KEY's column.  Same push, no freshness
    hypothesis: it asks only that a key exist for the push to resolve. -/
theorem floor_at_key {n : Nat} {v : Save} {s : St}
    (h_coord : hasKey v = true) (h : n ≤ s.keyCol) : n ≤ pushedAt v s := by
  unfold pushedAt; simp only [h_coord, ite_true]; exact h

/-- The case item 27 punted is reachable — by the SAME push, once the lemma
    names the coordinate the push uses. -/
theorem inherited_is_reachable (n : Nat) (s : St) (h : n ≤ s.keyCol) :
    n ≤ pushedAt .inherited s := floor_at_key rfl h

/-- And the coordinate really was the whole obstruction: at an inherited save no
    strengthening of the indicator-column hypothesis can work, because the
    indicator's column bounds nothing the push produced. -/
theorem inherited_unreachable_from_the_indicator :
    ¬ (∀ (n : Nat) (s : St), n ≤ s.col → n ≤ pushedAt .inherited s) := by
  intro h
  exact absurd (h 3 ⟨3, 1⟩ (Nat.le_refl 3)) (by decide)

/-! ## §2  Siblings, not a replacement

Re-measuring TRADES domain.  The key-column lemma reaches the inherited save and
loses the keyless `:`, whose state has no key column to be measured at — so the
two lemmas' domains are incomparable and both stay. -/

/-- The saves item 27's lemma discharges. -/
def coveredByIndicator : Save → Bool
  | .fresh => true
  | .inherited => false
  | .keyless => true

/-- The saves item 28's lemma discharges. -/
def coveredByKey : Save → Bool
  | .fresh => true
  | .inherited => true
  | .keyless => false

/-- Neither domain contains the other. -/
theorem neither_subsumes :
    (∃ v, coveredByIndicator v = true ∧ coveredByKey v = false) ∧
    (∃ v, coveredByKey v = true ∧ coveredByIndicator v = false) :=
  ⟨⟨.keyless, rfl, rfl⟩, ⟨.inherited, rfl, rfl⟩⟩

/-- Kept together they cover everything, which is the reason to keep both. -/
theorem together_they_are_total (v : Save) :
    coveredByIndicator v || coveredByKey v := by cases v <;> rfl

/-- The keyless `:` is what the new lemma cannot even be asked about: its
    hypothesis is the one thing that state does not have. -/
theorem key_lemma_cannot_be_asked : hasKey .keyless = false := rfl

/-- …so the old lemma is still load-bearing for it. -/
theorem indicator_lemma_still_needed (n : Nat) (s : St) (h : n ≤ s.col) :
    n ≤ pushedAt .keyless s :=
  floor_at_indicator (fun hv => absurd hv (by decide)) h

/-! ## §3  The quantity was already on both sides

The new hypothesis cost one conjunct because it was not new information — the
index was already measured on the surface side and already recorded on the
scanner side.  What the item added is the EQUATION. -/

/-- The surface side's measurement: `[63] s-indent(k)` between a column-0
    landing and the key.  Carried by the pack since item 25. -/
def surfaceIndex (landCol keyCol : Nat) : Nat := keyCol - landCol

/-- The scanner side's: the column the key was saved at.  Carried by the state
    since long before either item. -/
def scannerKeyCol (s : St) : Nat := s.keyCol

/-- Both sides had it all along, at a column-0 landing. -/
theorem both_sides_already_had_it (keyCol : Nat) :
    surfaceIndex 0 keyCol = scannerKeyCol ⟨0, keyCol⟩ := by
  simp [surfaceIndex, scannerKeyCol]

/-- With the equation the consumer's bound is one rewrite — no coupling
    argument, no new machinery, and in particular nothing that the escape has to
    absorb when it is unavailable. -/
theorem equation_closes_the_bound {n : Nat} {s : St}
    (h_eq : scannerKeyCol s = n) : n ≤ pushedAt .inherited s := by
  unfold pushedAt scannerKeyCol at *
  simp only [hasKey, ite_true]
  exact Nat.le_of_eq h_eq.symm

/-- And it is carried OPTIONALLY for the same reason the floor is: a producer
    whose key sits somewhere else — a property-headed key, an alias key — hands
    `True` and keeps the coverage it already had ([[OptionalFieldBuysDomain]]). -/
def Coupled (s : St) (n : Nat) : Prop := scannerKeyCol s = n ∨ True

theorem coupling_punt_is_free (s : St) (n : Nat) : Coupled s n := Or.inr trivial

theorem coupling_punt_does_not_decide :
    ¬ (∀ (s : St) (n : Nat), Coupled s n → scannerKeyCol s = n) := by
  intro h
  exact absurd (h ⟨0, 1⟩ 5 (Or.inr trivial)) (by decide)

/-! ## §4  What item 28 shipped -/

/-- Grammar files edited. -/
def grammarEdits : Nat := 0
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0
/-- New conjuncts on `ImplicitKeyPack`: one, optional. -/
def newPackConjuncts : Nat := 1
/-- Pack producers that discharge it: the plain and the two quoted heads. -/
def packProducersDischarging : Nat := 3
/-- Pack producers that hand `True`: the alias head and the props pack. -/
def packProducersPunting : Nat := 2
/-- Producers of the re-indexed pendings that discharge the FLOOR, before item
    28 — `-`, `?`, the empty-key `:` ([[OptionalFieldBuysDomain]] §1 measured
    this at 3 of 4). -/
def floorProducersBefore : Nat := 3
/-- …and after: the implicit-key `:` joins them. -/
def floorProducersAfter : Nat := 4
/-- New satellite lemmas in `PreprocessIndentStable`. -/
def newSatelliteLemmas : Nat := 3
/-- Floor lemmas RETIRED by the re-measurement — none, by §2. -/
def lemmasRetired : Nat := 0
/-- Escape call sites before. -/
def escapeSitesBefore : Nat := 14
/-- …and after: unchanged, which is the design claim and not an accident. -/
def escapeSitesAfter : Nat := 14
/-- Opaque `scannerDrop` sites: unchanged. -/
def dropSites : Nat := 4

theorem shipped :
    grammarEdits = 0 ∧ runtimeEdits = 0 ∧ newPackConjuncts = 1 ∧
    packProducersDischarging = 3 ∧ packProducersPunting = 2 ∧
    floorProducersBefore = 3 ∧ floorProducersAfter = 4 ∧
    newSatelliteLemmas = 3 ∧ lemmasRetired = 0 ∧
    escapeSitesAfter = escapeSitesBefore ∧ dropSites = 4 := by
  decide

end L4YAML.Tests.Reflections.PuntNamesACoordinate

end Blanket
