/-!
# Reflection 497 — the seq ROOT CARRIER `_seq` twin is the producer/consumer MEET, and a thin-instance
twin is the CHEAPEST link in a guard re-thread (zero proof body — one parent-name swap + the forwarded
residual's guard re-key).

Self-contained (core Lean, no `L4YAML` import) toy recording the structure step surfaced while landing
`seqRoot_carrier_of_widthEnc_seq` — the `FlowBodyContentDeepSeq`-keyed twin of
`seqRoot_carrier_of_widthEnc`, the thin `lo := 2`, `hi := tokens.size - 2` instance of the now-re-keyed
window-parametric `seqLocalCarrier_of_widthEnc_seq` (R496).

**The setup.**  The `_seq` re-thread (R488→R496) re-keyed the whole seq consumer chain off the root-FALSE
strong content guard `FlowBodyContentDeep` onto its root-TRUE weaker twin `FlowBodyContentDeepSeq`.  The
PRODUCER side (`seqWidthEnc_of_enclosingLocate_and_recIH_seq`, R492→R493) delivers an `h_widthEnc`
residual whose enclosing-window + IH facts are keyed on `FlowBodyContentDeepSeq`.  The window-parametric
CONSUMER carrier was re-keyed to match in R496.  THIS brick is the thin ROOT instance of that carrier.

**The find — the root seed is the MEET, and a thin instance is the cheapest possible re-key.**  Two
points, one brick.

1. **The MEET.**  The whole re-thread existed to reconcile a TYPE MISMATCH at exactly this interface:
   the producer hands an `h_widthEnc` keyed on the weak guard, but the OLD root carrier
   `seqRoot_carrier_of_widthEnc` demanded one keyed on the strong (root-FALSE) guard — so the producer's
   deliverable could NOT plug into the consumer's hypothesis slot.  This twin re-keys the consumer's
   hypothesis to the weak guard, and the producer's deliverable type and the consumer's hypothesis type
   now COINCIDE.  The re-thread's PURPOSE was this reconciliation; the root seed is where the two types
   meet and the producer plugs straight in.  And the reconciliation was NECESSARY, not cosmetic: the
   strong-keyed root residual is UNSATISFIABLE (the strong guard is FALSE at the root), so the old
   consumer's hypothesis could never have been supplied at all.

2. **A thin instance is the cheapest link in a re-thread — it has no proof BODY.**  Unlike the
   window-parametric carrier (R496) or the descent provider (R495), the root carrier carries NO proof
   logic: its body is a SINGLE application of the window-parametric parent at the root window.  So its
   `_seq` cost is the degenerate floor of [[LiftRekeysByGuardKeyedChildNames]] (R493) /
   [[TransportingLemmaTwinZeroBodyEdits]] (R492): exactly ONE guard-keyed parent swap and the guard
   re-key of the FORWARDED residual hypothesis it passes through verbatim.  The guard-NEUTRAL
   instantiation arguments (the width bound, the flat root `SafeBodyUnit`) transport byte-identical.

Below, `localCarrier` is the guard-polymorphic window carrier (the R496 stand-in — it consumes a
`WidthEnc G` residual and never reads the guard conjunct, it only transports it).  `rootCarrier_strong`
and `rootCarrier_seq` are its two thin root instances; `rootCarrier_seq` is THE BRICK — the strong
instance with the parent's guard argument swapped `StrongG ↦ WeakG` and the forwarded residual re-keyed
`WidthEnc StrongG ↦ WidthEnc WeakG`, zero body otherwise.  `producer` delivers the `WeakG`-keyed
residual; `meet` plugs it straight into `rootCarrier_seq`.  `strong_root_residual_unsatisfiable` shows
the OLD strong consumer's hypothesis was a dead end (the strong guard fails at the root sub-window),
which is WHY the re-thread re-keyed the consumer rather than the producer.

Axiom note: `producer`/`meet`/`strong_root_residual_unsatisfiable` are axiom-FREE (`[]` — `decide` over
the concrete root, no `omega`); strictly LIGHTER than the real lemma's `[propext, Classical.choice,
Quot.sound]`.  As in R496 the real lemma's `Classical.choice` is INHERITED from the deeper locator
machinery the window-parametric parent transports, not from this thin instance's own (absent) logic —
the root seed adds neither a branch, a `have`, nor an axiom over its parent.
-/

namespace ThinInstanceTwinIsProducerConsumerMeet

set_option autoImplicit false

/-! ### The two content guards, the carrier deliverable, and the guard-keyed residual. -/

/-- STRONG content guard (toy `FlowBodyContentDeep`): FALSE at the root sub-window `0`. -/
abbrev StrongG (n : Nat) : Prop := 1 ≤ n
/-- WEAK seq content guard (toy `FlowBodyContentDeepSeq`): TRUE everywhere, including the root. -/
abbrev WeakG (_n : Nat) : Prop := True

/-- The leaf-packaged per-window fact (toy `SafeBodyUnit` content). -/
abbrev Packaged (n : Nat) : Prop := 0 < n
/-- The carrier deliverable (toy `SeqInteriorSeparators tokens lo hi`). -/
abbrev Goal (n : Nat) : Prop := ∀ k, k + 1 < n → Packaged n

/-- The width-recursion residual `h_widthEnc`, KEYED on a content guard `G`.  The guard sits in the
    FIRST conjunct (toy: the enclosing-window `FlowBodyContent*` fact, evaluated at the root sub-window
    `0`); the second conjunct is the packaged content the carrier actually consumes.  The guard `G`
    appears in BOTH the producer's deliverable type and the consumer's hypothesis type, so the two must
    MATCH for the producer to plug in. -/
def WidthEnc (G : Nat → Prop) (n : Nat) : Prop := G 0 ∧ (∀ k, k + 1 < n → Packaged n)

/-- The window-local plumbing the carrier carries (toy `h_safe`) — guard-NEUTRAL, transported verbatim. -/
abbrev Safe (_n : Nat) : Prop := True

/-! ### The window-parametric carrier (R496 stand-in) — guard-polymorphic, transports the guard. -/

/-- The window-parametric carrier: consumes a `WidthEnc G` residual and produces `Goal`, reading ONLY
    the packaged conjunct — it never inspects the guard `G`, it merely carries it.  (Toy
    `seqLocalCarrier_of_widthEnc{,_seq}`: the guard is transported, not consumed.) -/
theorem localCarrier (G : Nat → Prop) (n : Nat) (_h_safe : Safe n) (h : WidthEnc G n) : Goal n :=
  fun k hk => h.2 k hk

/-! ### The ROOT SEED — thin instances at a fixed root, and the `_seq` twin (R497, THE BRICK). -/

/-- The concrete root window (toy `lo := 2`, `hi := tokens.size - 2`). -/
abbrev root : Nat := 3

/-- STRONG root carrier (toy `seqRoot_carrier_of_widthEnc`): the thin `n := root` instance of
    `localCarrier` at the STRONG guard.  Its body is a SINGLE parent application — no proof logic.  (Its
    hypothesis is a DEAD END; see `strong_root_residual_unsatisfiable` below.) -/
theorem rootCarrier_strong (h : WidthEnc StrongG root) : Goal root :=
  localCarrier StrongG root trivial h

/-- **THE BRICK** (toy `seqRoot_carrier_of_widthEnc_seq`, R497).  The `_seq` root carrier: the SAME thin
    instance, with ONE guard-keyed name swap (the parent's guard argument `StrongG ↦ WeakG`) and the
    forwarded residual `h`'s guard re-keyed `WidthEnc StrongG ↦ WidthEnc WeakG`.  Zero proof body beyond
    the single parent application; the guard-neutral `Safe`/`trivial` transports verbatim.  (That this
    typechecks as a one-line delegation, identical to `rootCarrier_strong` but for the guard name, IS
    the proof that a thin instance is the degenerate floor of the lift re-key.) -/
theorem rootCarrier_seq (h : WidthEnc WeakG root) : Goal root :=
  localCarrier WeakG root trivial h

/-! ### The MEET — the producer's re-keyed deliverable plugs straight into the `_seq` root carrier. -/

/-- The PRODUCER side delivers a `WeakG`-keyed residual (toy `seqWidthEnc_..._seq`, R492→R493): the
    guard conjunct `WeakG 0` holds (`trivial`), the packaged conjunct holds at the concrete root. -/
theorem producer : WidthEnc WeakG root :=
  ⟨trivial, fun _ _ => by decide⟩

/-- **The MEET** — the producer's `WeakG`-keyed deliverable plugs DIRECTLY into the `_seq` root
    carrier's hypothesis slot, because the re-thread made the two guard types COINCIDE.  This single
    application term is the whole payoff of the chain re-thread: producer-out ⟶ consumer-in, no
    adapter. -/
theorem meet : Goal root := rootCarrier_seq producer

/-- **Why the re-thread was NECESSARY, not cosmetic** — the OLD strong consumer's hypothesis is a DEAD
    END: `WidthEnc StrongG root` is UNSATISFIABLE because the strong guard is FALSE at the root
    sub-window `0` (`StrongG 0 = 1 ≤ 0`).  So the producer could never have supplied the strong-keyed
    residual; re-keying the CONSUMER to the weak guard (this whole re-thread) is the only way the two
    meet.  (Mirrors `FlowBodyContentDeep` being root-FALSE while `FlowBodyContentDeepSeq` is root-TRUE,
    [[RootSeedNeedsRootTrueGuard]] R488.) -/
theorem strong_root_residual_unsatisfiable : ¬ WidthEnc StrongG root :=
  fun h => absurd (h.1 : (1 : Nat) ≤ 0) (by decide)

/-- The `_seq` root carrier on the producer's witness, end to end. -/
example : Goal root := rootCarrier_seq producer

end ThinInstanceTwinIsProducerConsumerMeet
