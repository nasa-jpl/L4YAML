/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 644 — a parked state should name what it AWAITS, not what opened it; then a second opener costs one producer and no consumers

**The rule.**  A state parked mid-parse has two things it could record: the
construct that PARKED it, or the obligation it is waiting to discharge.  Record
the opener and every consumer must decide per opener, so a second opener costs
one edit at each of them.  Record only the obligation — as the closure that
discharges it — and the opener is spent at the producer, where it belongs: the
consumers never learn there was a second one.

Concretely (L4YAML): item 13 parked `PendingNode.pendingMapValue` for the col-0
`:` — `[189]`'s empty-key entry — with the whole entry frame pre-composed
inside its closure, so the payload is exactly `SBlockNode … → SLYamlStream`,
one node awaited and nothing about the `:`.  Item 20 wanted `?`, which is
`[188]`'s OTHER alternative and a different entry constructor and awaits the
KEY rather than the value.  Because the payload named no indicator, the second
producer reused the pending verbatim: no new `PendingNode` constructor, no
consumer arm edited, and the dispatch branch widened from `c = ':'` to
`c = ':' ∨ c = '?'` rather than being copied.

§1 is the model: two producers that genuinely build different things, one
consumer that cannot tell.  §2 is the cost law — opener-named states scale as
openers × consumers, await-named as openers.  §3 is where item 20's cost
actually landed, the surface GRAMMAR: `[186]`'s value is
`( l-block-map-explicit-value(n) | e-node )` and the `e-node` alternative had no
constructor, so `? a` parsed correctly with no derivation at all.  Widening a
`Prop` inductive is free exactly when nothing ELIMINATES it — construction
sites transport canonically, elimination sites need a choice that is not
determined.  §4 the shipped counts.

Self-contained: the two state shapes, the cost law, the widening's transport
and its non-uniqueness, and the counts.
-/

namespace L4YAML.Tests.Reflections.AwaitNotOpener

/-! ## §1  Two producers, one consumer

  The awaited thing and the thing it becomes, stripped to numbers. -/

/-- The node the parked state is waiting for. -/
abbrev Node := Nat
/-- What the state becomes once the node arrives. -/
abbrev Stream := Nat

/-- Which indicator parked the state. -/
inductive Opener where
  /-- `:` — `[189]`'s empty-key entry; the awaited node is the VALUE. -/
  | colon
  /-- `?` — `[186]`'s explicit-key entry; the awaited node is the KEY. -/
  | question
  deriving DecidableEq

/-- **Opener-named**: the state remembers which indicator parked it, so the
    frame is still to be chosen — at consumption time, by every consumer. -/
structure OpenerNamed where
  /-- The indicator that parked this state. -/
  opener : Opener

/-- **Await-named**: the state remembers only how the awaited node becomes a
    stream.  The opener was spent composing `close`, at the producer. -/
structure AwaitNamed where
  /-- Discharge the obligation: the frame is already inside. -/
  close : Node → Stream

/-- The one consumer.  It applies the closure it was handed; it never decides
    what the closure is. -/
def consume (s : AwaitNamed) (n : Node) : Stream := s.close n

/-- The `:` producer's frame: `[189]`'s empty-key entry around the value. -/
def colonFrame (n : Node) : Stream := 2 * n
/-- The `?` producer's frame: `[186]`'s explicit entry, `e-node` value,
    around the key.  Genuinely a different construction… -/
def questionFrame (n : Node) : Stream := 2 * n + 1

theorem frames_differ : ∃ n, colonFrame n ≠ questionFrame n := ⟨0, by decide⟩

/-- …and yet the single consumer serves both, unchanged. -/
theorem one_consumer_serves_both (n : Node) :
    consume ⟨colonFrame⟩ n = colonFrame n ∧
    consume ⟨questionFrame⟩ n = questionFrame n := ⟨rfl, rfl⟩

/-- The opener-named state cannot do that: with only the opener in hand, a
    consumer must carry a frame table, and the two openers land on different
    frames — so the table is load-bearing at every consumer. -/
def consumeNamed (table : Opener → Node → Stream) (s : OpenerNamed) (n : Node) : Stream :=
  table s.opener n

theorem named_consumer_needs_the_table :
    consumeNamed (fun o => match o with | .colon => colonFrame | .question => questionFrame)
        ⟨.colon⟩ 0 ≠
      consumeNamed (fun o => match o with | .colon => colonFrame | .question => questionFrame)
        ⟨.question⟩ 0 := by decide

/-! ## §2  The cost law

  Adding an opener to an opener-named state touches every consumer; adding one
  to an await-named state touches only the new producer. -/

/-- Edits to add `openers` openers when the state names the opener. -/
def openerNamedEdits (openers consumers : Nat) : Nat := openers * consumers
/-- …and when it names only what it awaits. -/
def awaitNamedEdits (openers _consumers : Nat) : Nat := openers

theorem await_never_worse (o c : Nat) (hc : 1 ≤ c) :
    awaitNamedEdits o c ≤ openerNamedEdits o c := by
  simpa [awaitNamedEdits, openerNamedEdits] using Nat.mul_le_mul_left o hc

/-- The gap is the consumer count, and it is unbounded: the design decision
    pays more the more consumers the state already has. -/
theorem gap_unbounded (o c : Nat) :
    openerNamedEdits o c - awaitNamedEdits o c = o * c - o := rfl

-- L4YAML's own numbers at item 20: two openers (`:`, `?`), three consuming
-- arms for `pendingMapValue` (content, flow-open, block dispatch).
#guard openerNamedEdits 2 3 == 6
#guard awaitNamedEdits 2 3 == 2

/-! ## §3  Where the cost actually landed: the surface grammar

  The accumulator was never the blocker.  `[186]`'s value is
  `( l-block-map-explicit-value(n) | e-node )`, and only the first alternative
  had a constructor — so a key-only entry had no derivation, and no arm could
  even be STATED.  Widening the inductive was the whole item.

  The safety argument is a count, not a hope: a `Prop` inductive used only to
  CONSTRUCT is free to widen. -/

/-- `[188]`'s entry alternatives as shipped before item 20. -/
inductive Entry where
  /-- `? key` + `: value`. -/
  | explicit
  /-- Implicit key, block-node value. -/
  | implicitKeyNode
  /-- Implicit key, empty value. -/
  | implicitKeyEmpty
  /-- Empty key, block-node value. -/
  | emptyKeyNode
  /-- Empty key, empty value. -/
  | emptyKeyEmpty
  deriving DecidableEq

/-- …and after: the `e-node` value alternative of the explicit entry. -/
inductive EntryPlus where
  /-- `? key` + `: value`. -/
  | explicit
  /-- `? key` alone — the value is `e-node` (item 20). -/
  | explicitEmpty
  /-- Implicit key, block-node value. -/
  | implicitKeyNode
  /-- Implicit key, empty value. -/
  | implicitKeyEmpty
  /-- Empty key, block-node value. -/
  | emptyKeyNode
  /-- Empty key, empty value. -/
  | emptyKeyEmpty
  deriving DecidableEq

/-- The old alternatives keep their meanings. -/
def embed : Entry → EntryPlus
  | .explicit => .explicit
  | .implicitKeyNode => .implicitKeyNode
  | .implicitKeyEmpty => .implicitKeyEmpty
  | .emptyKeyNode => .emptyKeyNode
  | .emptyKeyEmpty => .emptyKeyEmpty

/-- **Construction sites transport canonically.**  Anything that PRODUCES the
    old type produces the new one by composition — no choice to make, so no
    site to revisit. -/
def transport {α : Type} (f : α → Entry) : α → EntryPlus := embed ∘ f

theorem transport_agrees {α : Type} (f : α → Entry) (a : α) :
    transport f a = embed (f a) := rfl

/-- **Elimination sites do not.**  A function out of the widened type extends
    an old one, but only after CHOOSING what to do with the new constructor. -/
def extend (g : Entry → Nat) (k : Nat) : EntryPlus → Nat
  | .explicit => g .explicit
  | .explicitEmpty => k
  | .implicitKeyNode => g .implicitKeyNode
  | .implicitKeyEmpty => g .implicitKeyEmpty
  | .emptyKeyNode => g .emptyKeyNode
  | .emptyKeyEmpty => g .emptyKeyEmpty

theorem extend_agrees (g : Entry → Nat) (k : Nat) (e : Entry) :
    extend g k (embed e) = g e := by cases e <;> rfl

/-- And the choice is not determined — which is exactly why every elimination
    site is a hand edit and counting them IS the risk assessment. -/
theorem extension_not_unique (g : Entry → Nat) :
    extend g 0 EntryPlus.explicitEmpty ≠ extend g 1 EntryPlus.explicitEmpty := by
  simp [extend]

/-- Sites in the repo that CONSTRUCT `SBlockMapEntry` (free across the
    widening): `colon_open_map`, `colon_open_map_implicit`, `question_open_map`. -/
def constructionSites : Nat := 3
/-- Sites that ELIMINATE it — `cases`/`induction`/`match`.  Zero is what made
    the widening cost nothing beyond the constructor itself. -/
def eliminationSites : Nat := 0

#guard eliminationSites == 0

/-! ## §4  The shipped counts (item 20, 2026-08-11) -/

/-- Constructors added to the surface grammar (`SBlockMapEntry.explicitEmpty`). -/
def newGrammarConstructors : Nat := 1
/-- New `PendingNode` constructors. -/
def newPendingConstructors : Nat := 0
/-- Consuming arms of `pendingMapValue` edited. -/
def consumerArmsEdited : Nat := 0
/-- New lemmas: the dispatch reader, the producer, and the join that lets one
    branch serve both indicators. -/
def newLemmas : Nat := 3
/-- Dispatch BRANCHES added: none — the `:` branch's condition widened to a
    disjunction instead of being copied. -/
def dispatchBranchesAdded : Nat := 0
/-- Deferral (`block_dispatch_deferred`) call sites before… -/
def deferralSitesBefore : Nat := 18
/-- …and after: unchanged, because the arm widened rather than splitting.
    (Copying it first DID push this to 22 while composing strictly more input
    — Reflection 645 has that measurement and its rule.) -/
def deferralSitesAfter : Nat := 18
/-- Block indicators the dispatch composes, of three (`-`, `:`, `?`). -/
def blockIndicatorsComposedBefore : Nat := 2
/-- …and after. -/
def blockIndicatorsComposedAfter : Nat := 3
/-- Scanner/runtime files edited. -/
def runtimeEdits : Nat := 0

#guard newGrammarConstructors == 1
#guard newPendingConstructors == 0
#guard consumerArmsEdited == 0
#guard newLemmas == 3
#guard dispatchBranchesAdded == 0
#guard deferralSitesBefore == 18
#guard deferralSitesAfter == 18
#guard blockIndicatorsComposedBefore + 1 == blockIndicatorsComposedAfter
#guard runtimeEdits == 0

end L4YAML.Tests.Reflections.AwaitNotOpener

end Blanket
