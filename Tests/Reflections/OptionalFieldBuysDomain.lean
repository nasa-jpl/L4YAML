/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 653 — carry a new invariant obligation as an OPTIONAL field, so partial coverage costs domain instead of call sites

**The rule.**  When [[SideConditionNeedsItsQuantity]] has told you which quantity
an invariant must start carrying, you still have to decide what SHAPE to carry
it in.  Carry it as a REQUIRED field and every producer of that constructor
owes it on the spot: the ones that can measure it are fine, and the ones that
cannot must route their case to the escape — a route that did not exist before,
authored by your own edit.  Carry it as `P ∨ True` and a producer that cannot
measure hands `True` back; the consumer's route to the escape is the one it
already had, and what moves is the DOMAIN.

**Why that is the right default here.**  The campaign's progress metric is the
escape's call-site count together with what each site is true of
([[CoverageNotCallSites]]).  A required field inflates the first while leaving
the second alone — the same inflation [[WideningIsAnOccurrenceQuestion]] §4
warns about for `by_cases`, one layer up: there it was several questions failing
into one hatch, here it is several producers failing into one.  The optional
field gets exactly the same coverage as the required one, because a producer
that cannot measure could not have composed its case either way.  It just does
not charge you a site for saying so.

**The tell that you will need it.**  A family that is symmetric in the GRAMMAR
need not be symmetric in the runtime.  Before committing to a required field,
check for each producer which coordinate the runtime actually uses: if any
member of the family pushes at someone else's coordinate rather than its own,
that member cannot discharge the field from local information, and the field has
to be optional or the item has to grow by whatever coupling would supply it.

Concretely (L4YAML): item 26 left `n ≤ d` owed, where `d` is the indent a block
scalar's body was collected at.  Item 27 pays it by carrying
`IndentFloor sc n = (sc.needIndentCheck = false ∧ n ≤ minContentIndentOf sc)` on
`pendingBlock` / `pendingMapValue` / `pendingProps` and transporting it across
preprocessing (`skipToContent` never writes `indents`; only the armed
`unwindIndents` does, and the arming flag is what the break-free branch already
rules out).  `-` pushes `[183]`'s indent at its own column and `?` pushes
`[187]`'s at its own, so both discharge the field; `:` pushes at the RESOLVED
KEY's column, which is its own exactly when the save was fresh — so `  : |`
discharges and `  a: |` does not, and it hands `True`.

§1 is required-versus-optional.  §2 is the transport and why `True` is
absorbing.  §3 is the asymmetric family.  §4 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.OptionalFieldBuysDomain

/-! ## §1  A required field charges a call site; an optional one does not

The measurement is the same in both designs, and so is the set of producers that
can take it.  What differs is what happens to the ones that cannot. -/

/-- The four producers of the re-indexed pendings. -/
inductive Producer where
  /-- `-` — `[183] l+block-sequence`, pushes at the indicator's own column. -/
  | dash
  /-- `?` — `[187] l+block-mapping`, likewise. -/
  | key
  /-- `:` opening `[189]`'s empty-key entry — pushes at the FRESH saved key,
      which sits at the indicator itself. -/
  | value
  /-- `:` resolving item 15's implicit key — pushes at the KEY's column. -/
  | implicitKey
  deriving DecidableEq, Repr

/-- All of them. -/
def producers : List Producer := [.dash, .key, .value, .implicitKey]

/-- Whether the producer can take the measurement from what it holds locally. -/
def measures : Producer → Bool
  | .dash => true
  | .key => true
  | .value => true
  | .implicitKey => false

/-- The escape's call sites BEFORE the item: one per consumer family, whatever
    the producers do. -/
def baseSites : Nat := 14

/-- **Required field**: a producer that cannot establish it has nowhere to go
    but the escape, so it authors a new call site. -/
def sitesRequired : Nat :=
  baseSites + (producers.filter (fun p => !measures p)).length

/-- **Optional field** (`P ∨ True`): the same producer hands `True` back and the
    consumer keeps the single route it already had. -/
def sitesOptional : Nat := baseSites

/-- The coverage — the producers whose cases now compose — is IDENTICAL under
    the two designs, because a producer that cannot measure could not have
    composed its case either way. -/
def covered : List Producer := producers.filter measures

/-- So the required field buys nothing and costs a site. -/
theorem optional_costs_no_site :
    sitesOptional = baseSites ∧ sitesRequired = baseSites + 1 ∧
    covered = [.dash, .key, .value] := by
  decide

/-- Stated as the comparison that matters: same domain, strictly fewer sites. -/
theorem same_domain_fewer_sites :
    covered.length = covered.length ∧ sitesOptional < sitesRequired := by
  decide

/-! ## §2  The transport, and why `True` is absorbing

The field is read one step later than it is written, so it has to survive the
step.  It does, on the branch where the step changed nothing the measurement
depends on — and a pending that never had the measurement still has none, which
is what makes the optional shape composable rather than a special case at every
re-park. -/

/-- The measurement: an index at or below a bound. -/
def Floor (n bound : Nat) : Prop := n ≤ bound

/-- What a pending carries. -/
def Carried (n bound : Nat) : Prop := Floor n bound ∨ True

/-- A producer that measured. -/
theorem carried_of_measured {n bound : Nat} (h : n ≤ bound) : Carried n bound :=
  Or.inl h

/-- A producer that did not.  Note there is nothing to prove — which is the
    point: the cost of NOT measuring is zero, not a new branch. -/
theorem carried_of_punt (n bound : Nat) : Carried n bound := Or.inr trivial

/-- **Transport**: a step that leaves the bound alone carries the measurement,
    and carries the absence of one just as happily. -/
theorem carried_transport {n bound bound' : Nat}
    (h : Carried n bound) (heq : bound = bound') : Carried n bound' := by
  rcases h with hle | _
  · exact Or.inl (heq ▸ hle)
  · exact Or.inr trivial

/-- The consumer asks ONCE and composes when the measurement is there — one
    `Nat.le_trans`, no case analysis of its own. -/
theorem consumes_on_measured {n bound target : Nat}
    (hle : n ≤ bound) (hb : bound ≤ target) : n ≤ target :=
  Nat.le_trans hle hb

/-- `True` really is information-free: handing it costs a producer nothing… -/
theorem punt_is_free (n bound : Nat) : Carried n bound := Or.inr trivial

/-- …and gives the consumer nothing, so the case falls to the deferral that was
    already there.  That is the whole trade, and it is why the optional field
    cannot be mistaken for a proof: `Carried` is inhabited at every index. -/
theorem punt_does_not_decide : ¬ (∀ n bound : Nat, Carried n bound → n ≤ bound) := by
  intro h
  exact absurd (h 5 3 (Or.inr trivial)) (by decide)

/-! ## §3  Symmetric in the grammar, asymmetric in the runtime

`-`, `?` and `:` are three block indicators that open block collections at an
index the grammar treats uniformly.  The runtime does not: two of them push
their collection's indent at their OWN column and the third pushes at the column
of the key it is resolving.  That is the whole reason the field has to be
optional rather than required. -/

/-- The scanner state the push reads. -/
structure St where
  /-- The indicator's own column. -/
  col : Nat
  /-- The column of the saved implicit key. -/
  keyCol : Nat
  /-- Whether the save was fresh — i.e. taken at the indicator itself. -/
  fresh : Bool
  deriving Repr

/-- Where each producer pushes its block-collection indent. -/
def pushedAt : Producer → St → Nat
  | .dash, s => s.col
  | .key, s => s.col
  | .value, s => if s.fresh then s.col else s.keyCol
  | .implicitKey, s => s.keyCol

/-- The entry index the ACCUMULATOR parked, measured off the line start. -/
def parkedIndex : Producer → St → Nat
  | .dash, s => s.col
  | .key, s => s.col
  | .value, s => s.col
  | .implicitKey, s => s.keyCol

/-- Two of the three push at the index the accumulator parked, unconditionally. -/
theorem dash_and_key_push_at_their_own (s : St) :
    pushedAt .dash s = parkedIndex .dash s ∧ pushedAt .key s = parkedIndex .key s :=
  ⟨rfl, rfl⟩

/-- The `:` does too — but only on the fresh save, which is exactly the shape
    `[189]`'s empty-key entry has. -/
theorem value_pushes_at_its_own_iff_fresh (s : St) (h : s.fresh = true) :
    pushedAt .value s = parkedIndex .value s := by
  simp [pushedAt, parkedIndex, h]

/-- And on an inherited save it does not — the parked index is the KEY's, a
    column the accumulator never carried.  This is the counterexample that
    forces the field to be optional. -/
theorem inherited_save_breaks_the_symmetry :
    pushedAt .value ⟨3, 1, false⟩ ≠ parkedIndex .value ⟨3, 1, false⟩ := by decide

/-- The implicit-key producer is not a harder instance of the same question, it
    is the OTHER coordinate throughout — which is why item 27 leaves it and does
    not merely fail on it. -/
theorem implicit_key_is_a_different_coordinate (s : St) :
    pushedAt .implicitKey s = s.keyCol ∧ parkedIndex .implicitKey s = s.keyCol :=
  ⟨rfl, rfl⟩

/-- The grammar, meanwhile, cannot see the difference: all four open a block
    collection at the parked index. -/
def opensAt (p : Producer) (s : St) : Nat := parkedIndex p s

/-- …so no reading of the productions would have flagged the asymmetry. -/
theorem grammar_is_blind (s : St) : ∀ p, opensAt p s = parkedIndex p s :=
  fun _ => rfl

/-! ## §4  What item 27 shipped -/

/-- Grammar files edited.  None — this is a scanner/invariant coupling. -/
def grammarEdits : Nat := 0
/-- Runtime files edited. -/
def runtimeEdits : Nat := 0
/-- New pending FIELDS: one, optional, on three constructors. -/
def newFields : Nat := 1
/-- Constructors that gained it. -/
def constructorsTouched : Nat := 3
/-- Producers that discharge it (`-`, `?`, the fresh `:`) — see §3. -/
def producersDischarging : Nat := 3
/-- Producers that hand `True` (the implicit-key `:`). -/
def producersPunting : Nat := 1
/-- Escape call sites before. -/
def escapeSitesBefore : Nat := 14
/-- …and after: UNCHANGED, which is the design claim of §1 and not an accident. -/
def escapeSitesAfter : Nat := 14
/-- Opaque `scannerDrop` sites: unchanged. -/
def dropSites : Nat := 4
/-- `PendingNode` constructors that CARRY the missing quantity, before —
    Reflection 652 measured this at zero and called it the whole item. -/
def constructorsCarryingBefore : Nat := 0
/-- …and after: `pendingBlock`, `pendingMapValue`, `pendingProps`. -/
def constructorsCarryingAfter : Nat := 3

theorem shipped :
    grammarEdits = 0 ∧ runtimeEdits = 0 ∧ newFields = 1 ∧
    constructorsTouched = 3 ∧ producersDischarging = 3 ∧ producersPunting = 1 ∧
    escapeSitesAfter = escapeSitesBefore ∧ dropSites = 4 ∧
    constructorsCarryingBefore = 0 ∧ constructorsCarryingAfter = 3 := by
  decide

end L4YAML.Tests.Reflections.OptionalFieldBuysDomain

end Blanket
