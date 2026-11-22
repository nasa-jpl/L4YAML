/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 637 — type the twin's closure as the original's; convert at its one producer

**The rule.**  A new parked obligation whose closure has the SAME SHAPE as an
existing constructor's should state it at the existing machinery's type — even
when its own grammar slot asks for a different index — and pay the conversion
ONCE, at the producer's capture site, where the grammar constructor is
actually applied.  Every consumer arm then becomes the existing constructor's
VERBATIM clone, because consumers never see the difference.

The shipped instance (L4YAML item 13): the first block-MAPPING pending.
`[189] c-l-block-map-implicit-value` wants its value node at `.blockOut`;
every consumer in the accumulation — content dispatch, flow open, block
scalar, SSL close — composes nodes at `.blockIn`.  Stating
`pendingMapValue.h_close` at `.blockOut` would have forked all four consumer
arms into context-converting variants.  Stating it at `.blockIn` and
converting at the ONE producer (`SBlockNode_blockIn_to_blockOut`, inert at
n = 0: `seq-spaces(0, BLOCK-OUT)` truncates to 0, separators and properties
re-label by definitional equality plus one constructor rebuild) made the
close/flow-open arms byte-for-byte clones and the content arm a near-clone.

**The fields you do NOT add.**  The sequence twin (`pendingBlock`) carries a
SECOND closure — the entries-level snoc — so sibling `- b` entries extend one
derivation.  The mapping twin omits it: sibling `: b` entries close the map
and re-open through `[211]`'s admitted bare-document continuation
(`implicitContinue`), so the entries-level fidelity is NOT load-bearing for
language membership — the op-tree-witness rule one level up.  One closure,
no new invariant conjuncts, and the structural/EOF/flow steps consumed the
new constructor through `close_with_ssl` without an edit.

Self-contained: a miniature two-context grammar with an inert conversion at
depth 0, plus the shipped instance's counts (item 13, 2026-08-10).
-/

namespace L4YAML.Tests.Reflections.TwinClosureTypedAsTheOriginal

/-- Two contexts whose difference is a depth adjustment. -/
inductive Ctx where
  | inCtx | outCtx
  deriving DecidableEq, Repr

/-- The depth a context imposes: `outCtx` steps down — the mini `seqSpaces`. -/
def spaces (n : Nat) : Ctx → Nat
  | .inCtx => n
  | .outCtx => n - 1

/-- At depth 0 the adjustment truncates: the contexts are inert. -/
example : spaces 0 .outCtx = spaces 0 .inCtx := rfl

/-- A miniature node, indexed by depth and context; the recursive field
    reads the context only through `spaces`. -/
inductive MiniNode : Nat → Ctx → Prop where
  | leaf (n : Nat) (c : Ctx) : MiniNode n c
  | nest (n : Nat) (c : Ctx) : MiniNode (spaces n c) .inCtx → MiniNode n c

/-- The conversion, sound exactly where the context is inert (n = 0):
    one cases-rebuild, every field transported by definitional equality. -/
theorem convert : MiniNode 0 .inCtx → MiniNode 0 .outCtx
  | .leaf _ _ => .leaf 0 .outCtx
  | .nest _ _ h => .nest 0 .outCtx h

/-- A consumer composes nodes at `.inCtx` — the machinery's home context. -/
theorem consumerComposes (n : Nat) : MiniNode n .inCtx := .leaf n .inCtx

/-- The producer's capture: the grammar slot wants `.outCtx`, so the
    conversion happens HERE — the pending's closure still TAKES `.inCtx`,
    which is why the consumer above feeds it unchanged. -/
def producerCapture (close : MiniNode 0 .outCtx → Prop)
    (h : MiniNode 0 .inCtx) : Prop :=
  close (convert h)

example : producerCapture (fun _ => True) (consumerComposes 0) = True := rfl

-- ═══ §1  The carrier's price (item 13's shipped counts) ═══

/-- Consumer arms that are the seq twin's VERBATIM clones (`close_with_ssl`,
    flow-open, block-scalar path of the content arm). -/
def verbatimConsumerArms : Nat := 3
/-- Consumer arms with a real difference (the content arm's flow case parks
    stream-level `pendingContent` — no entries snoc to thread). -/
def adaptedConsumerArms : Nat := 1
/-- Producer call sites, all riding ONE shared helper (`colon_open_map`). -/
def producerSites : Nat := 4
/-- Conversion call sites — the producer's capture, nowhere else. -/
def conversionSites : Nat := 1
/-- Steps that consumed the new constructor with NO edit (structural, EOF,
    flow at depth > 0) — they read pendings only through `close_with_ssl`. -/
def zeroEditConsumingSteps : Nat := 3

#guard verbatimConsumerArms == 3
#guard adaptedConsumerArms == 1
#guard producerSites == 4
#guard conversionSites == 1
#guard zeroEditConsumingSteps == 3

-- ═══ §2  The fields not added ═══

/-- `pendingBlock`'s closures (node-level + entries-level snoc). -/
def seqTwinClosures : Nat := 2
/-- `pendingMapValue`'s closures — the snoc is not load-bearing: siblings
    ride the stream grammar's admitted bare-document continuation. -/
def mapTwinClosures : Nat := 1
/-- New invariant conjuncts threaded for the new state. -/
def newInvariantConjuncts : Nat := 0

#guard seqTwinClosures == 2
#guard mapTwinClosures == 1
#guard newInvariantConjuncts == 0

-- ═══ §3  What the arm covers vs. defers ═══

/-- The col-0 `:` dispatch outcomes (item 13). -/
inductive ColonOutcome where
  | composes   -- `: v`, `:`, `: [a]`, `: |`, `: &a v`, `---⏎: v`, `: a⏎: b`
  | deferred   -- `a: b` (implicit key, col ≠ 0), `?` explicit key, indented ` : v`
  deriving DecidableEq, Repr

def outcomeOf (col0 : Bool) (whitespaceBefore : Bool) : ColonOutcome :=
  if col0 && !whitespaceBefore then .composes else .deferred

#guard outcomeOf true false == .composes
#guard outcomeOf false false == .deferred   -- `a: b` — the implicit-key pass
#guard outcomeOf true true == .deferred     -- ` : v` — the indent machinery

end L4YAML.Tests.Reflections.TwinClosureTypedAsTheOriginal

end Blanket
