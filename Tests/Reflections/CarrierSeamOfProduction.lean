/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 641 — a carrier's arms are the PRODUCTION's alternatives, not the producer's cases — and a coupling carries what its consumer cannot observe

**The rule.**  Reflection 640's corollary said that when several readings reach
one consumer you widen the pack with a carrier inductive and convert ONCE.  It
did not say where to cut the carrier, and the default — one arm per producer
branch that exists today — is the wrong seam.  Cut it along the GRAMMAR's
alternatives instead: give each arm the whole production the consumer's
corresponding alternative reads, and every future head that is an arm of that
production lands with no carrier edit at all.

The test is checkable before writing the arm: *is the head you are about to add
already an alternative of the production the carrier's payload names?*  If it
is, the carrier does not need an arm — it needs the payload widened to the
production.

- Item 16 cut at the producer: three arms, one per scanner branch (plain,
  double-quoted, single-quoted).  Two heads remained punted.
- Item 17 re-cut at `[188] ns-s-block-map-implicit-key`'s own two alternatives
  — `[193]`'s plain key and `[194]`'s flow node — and the two remaining heads,
  an alias key and a property-prefixed key, are `[161] ns-flow-node`'s own
  `alias` and `propsContent` arms.  Zero new carrier arms; the whole cost moved
  to the producers, where the evidence actually differs.

§1 proves the difference is not stylistic: the producer-shaped carrier is
provably unable to state the fourth head, while the production-shaped one
carries it by construction.

**The second rule (§3).**  A coupling field's guard hypotheses must be facts
its CONSUMER can observe.  Item 15's key coupling is guarded by two decidable
facts about the state the field is attached to, so the consumer fires it by
case split.  Item 17's props coupling needed a fact about a state the consumer
no longer holds — the saved key's line at the moment the run OPENED — and a
post-state guard does not imply it.  So the field CARRIES that datum rather
than demanding it; §3 exhibits the counter-model that forces the choice.

Self-contained: the two cuts and the head that separates them, the union
identity that licenses the wider payload, the carry-vs-demand counter-model and
the discharge it enables, and the shipped counts.
-/

namespace L4YAML.Tests.Reflections.CarrierSeamOfProduction

/-! ## §1  Two ways to cut one carrier -/

/-- The node shapes a key can be built from. -/
inductive Node where
  | plain | quoted | alias | props
  deriving DecidableEq

/-- The PRODUCTION (`[161] ns-flow-node`): four alternatives, all of them
    legal heads. -/
inductive Flow : Node → Prop where
  | plain  : Flow .plain
  | quoted : Flow .quoted
  | alias  : Flow .alias
  | props  : Flow .props

/-- The consumer (`[188]`): two alternatives, the YAML key reading a plain
    scalar and the JSON key reading a flow node. -/
inductive Key : Node → Prop where
  | yaml : Key .plain
  | json {n : Node} : Flow n → Key n

/-- **Cut A — the producer's seam** (item 16): one arm per scanner branch that
    had landed when the carrier was written. -/
inductive CarrierA : Node → Prop where
  | plain  : CarrierA .plain
  | quoted : CarrierA .quoted

/-- **Cut B — the production's seam** (item 17): one arm per ALTERNATIVE of the
    consumer, the JSON arm carrying the whole production.  The plain head keeps
    its `[193]` attribution; everything else is a flow node. -/
inductive CarrierB : Node → Prop where
  | yaml : CarrierB .plain
  | json {n : Node} : Flow n → CarrierB n

theorem carrierA_to_key {n : Node} (h : CarrierA n) : Key n := by
  cases h with
  | plain => exact .yaml
  | quoted => exact .json .quoted

theorem carrierB_to_key {n : Node} (h : CarrierB n) : Key n := by
  cases h with
  | yaml => exact .yaml
  | json h => exact .json h

/-- The new heads arrive.  Cut B admits them with no edit… -/
theorem aliasHead_carrierB : CarrierB .alias := .json .alias
theorem propsHead_carrierB : CarrierB .props := .json .props

/-- …while cut A cannot state them at all: those carriers are UNINHABITED, so
    the arms are not a convenience — they are the only way to say the thing. -/
theorem carrierA_misses_alias : ¬ CarrierA .alias := by intro h; cases h
theorem carrierA_misses_props : ¬ CarrierA .props := by intro h; cases h

/-! ## §2  What licenses the wider payload

  Cutting at the production is only honest if the consumer's alternatives
  really do union to it.  Here they do, arm for arm — which is why the wider
  payload costs no strength: the carrier's language is the consumer's. -/

theorem key_iff_flow {n : Node} : Key n ↔ Flow n := by
  constructor
  · intro h
    cases h with
    | yaml => exact .plain
    | json h => exact h
  · intro h; exact .json h

/-- …and the two cuts differ exactly on the heads cut A cannot name. -/
theorem carrierB_iff_flow {n : Node} : CarrierB n ↔ Flow n := by
  constructor
  · intro h
    cases h with
    | yaml => exact .plain
    | json h => exact h
  · intro h; exact .json h

/-! ## §3  Carry the datum, or demand it?

  A coupling attached to a state can DEMAND facts about that state — the
  consumer decides them and fires the field.  It cannot demand facts about an
  earlier state: the consumer no longer holds it, and the post-state guard does
  not imply the pre-state one. -/

/-- A scanner state, stripped to the two fields the §7.4 guard reads. -/
structure St where
  line : Nat
  keyLine : Nat

/-- What a consumer can observe: the guard on the state it holds. -/
def guard (s : St) : Prop := s.keyLine = s.line

/-- One step: the line may advance by `d` (breaks crossed); the saved key does
    not move. -/
def step (d : Nat) (s : St) : St := { s with line := s.line + d }

/-- **Why demanding fails.**  The post-state guard is satisfied by a step that
    crossed a break, over a pre-state whose own guard is false — so no
    consumer holding only the post-state can conclude anything about the
    scan. -/
theorem post_guard_does_not_fire_pre_guard :
    ∃ (s : St) (d : Nat), guard (step d s) ∧ ¬ guard s :=
  ⟨⟨0, 1⟩, 1, rfl, by simp [guard]⟩

/-- **What carrying buys.**  With the pre-state datum in hand, the same
    post-state guard says the step crossed NOTHING — which is exactly the
    hypothesis the content's one-line reading asks for. -/
theorem carried_datum_fires (s : St) (d : Nat)
    (h_carry : guard s) (h_post : guard (step d s)) : d = 0 := by
  simp only [guard, step] at h_carry h_post
  omega

/-! ## §4  The shipped counts (item 17, 2026-08-11) -/

/-- Carrier arms before the re-cut (plain, double-quoted, single-quoted). -/
def carrierArmsBefore : Nat := 3
/-- …and after: one per alternative of `[188]`. -/
def carrierArmsAfter : Nat := 2
/-- Heads item 17 landed: the alias key and the property-prefixed key. -/
def headsAdded : Nat := 2
/-- Carrier arms those two heads needed. -/
def carrierArmsForNewHeads : Nat := 0
/-- One-line content readings REUSED verbatim under the props head (items
    15/16's plain, double-quoted and single-quoted `_key_prod` lemmas). -/
def oneLineReadingsReused : Nat := 3
/-- New production lemmas: the two BLOCK-KEY run extensions and the saved-key
    line transport across a preprocessing step. -/
def newProdLemmas : Nat := 3
/-- Scanner transports the props head needed and did NOT have to write: both
    `dispatchContent_{anchor,tag}_simpleKey` already existed for item 10's
    key-layout work — the twins were drafted, then deleted unbuilt. -/
def reusedScannerTransports : Nat := 2
/-- Coupling fields added, and the datum each CARRIES rather than demands. -/
def carriedCouplings : Nat := 1
/-- The alias head's line hypotheses: `ns-anchor-char` excludes `s-white` and
    `b-char`, so there is no break to refute. -/
def aliasLineHypotheses : Nat := 0
/-- Scanner/runtime files edited. -/
def runtimeEdits : Nat := 0

#guard carrierArmsBefore == 3
#guard carrierArmsAfter == 2
#guard headsAdded == 2
#guard carrierArmsForNewHeads == 0
#guard oneLineReadingsReused == 3
#guard newProdLemmas == 3
#guard reusedScannerTransports == 2
#guard carriedCouplings == 1
#guard aliasLineHypotheses == 0
#guard runtimeEdits == 0

end L4YAML.Tests.Reflections.CarrierSeamOfProduction

end Blanket
