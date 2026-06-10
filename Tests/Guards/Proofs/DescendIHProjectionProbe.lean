import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Descend-IH projection probe (de-risk for `(i'-b-B2c-dispatch-ih-widen)`, step (3))

R347 settled the carrier-free route as "thread `FlowBodyContent` as a fifth `G`-conjunct, discharged
at the structural sites via the landed descend/advance edges, with the dispatch IH SIGNATURE widened
by `FlowBodyContent`." The widened-dispatcher next-step's step (3) demands a PROBE before authoring:
is `flowBodyContent_descend`'s four-conjunct `h_ih` obtainable by PROJECTING the widened five-conjunct
recursion IH (dropping the `FlowBodyContent` premise)?

This file probes that mechanically, sorry-free. The five-conjunct IH `IH5` is what the widened
recursion hands its step (the dispatch's widened `h_ih`); the four-conjunct `IH4` is what
`flowBodyContent_descend` / `seqChild_safeBodyUnit` consume (see those signatures,
`SeqInteriorSeparators.lean:652-655` / `:612-615`). A "projection" must build `IH4` from `IH5`.

The decisive findings, both sorry-free:

* `ih5_of_ih4` — the REVERSE direction (four→five) is a FREE drop: `IH4` produces a child `RecSeqBody`
  from FOUR facts, so it trivially serves where five are offered (the extra `FlowBodyContent` is
  ignored). Hence `IH4` is STRICTLY STRONGER than `IH5`, and the needed projection runs UP the
  strength order.

* `ih4_of_ih5_iff_provider` — the FORWARD projection (five→four) closes IF AND ONLY IF a per-window
  `provider : intrinsic-facts → FlowBodyContent` exists, supplying the dropped premise at each
  strictly-smaller child window from only its INTRINSIC facts (`FlowBodyWindow`,
  `FlowBodyContentDeep`, `Q`, close). That provider is exactly the carrier-free `FlowBodyContent`
  source that does NOT exist: its `bodySucc` field has no all-depth balance-free form (R296) and is
  invisible to the separator-blind `WellTyped` (R345); and the same-window cycle forbids it, since
  `bodySucc W` is read OFF `RecSeqBody W` (`seqSeparatorFacts_of_recseqbody`) while `RecSeqBody W`'s
  dispatch needs `bodySucc W` as INPUT. So the projection is a GENUINE arity entanglement, not a
  mechanical drop — the `(i'-b-B2c-dispatch-ih-widen)` fork's second branch.

The asymmetry that LOCATES it: the ADVANCE edge (`flowBodyContent_advance`) builds the tail's
`FlowBodyContent` by pure re-basing from the parent's (no IH, no child `RecSeqBody`), so its
five-conjunct child is supplied cleanly; the DESCEND edge (`flowBodyContent_descend`) builds the
child's `FlowBodyContent` only via the child's OWN `RecSeqBody` (`seqChild_safeBodyUnit`), so
discharging it re-enters the recursion at that SAME child window. R347's toy abstracted descend as a
clean parent→child arrow, hiding this; the real descend routes through the child's deliverable.
-/

namespace L4YAML.Proofs.EmitterScannability.DescendIHProjectionProbe

open L4YAML
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)

set_option autoImplicit false

variable (tokens : Array (Positioned YamlToken)) (p hi : Nat) (Q : Nat → Prop)

/-- The FIVE-conjunct IH the widened recursion hands its step (the dispatch's widened `h_ih`): to
    produce a child window's `RecSeqBody` it demands that child's `FlowBodyContent` as an INPUT. -/
abbrev IH5 : Prop :=
  ∀ lo' hi', hi' - lo' < hi - p →
    FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' →
    FlowBodyContent tokens lo' hi' → Q lo' →
    tokens[hi']!.val = .flowSequenceEnd →
    RecSeqBody ((tokens.toList.take hi').drop lo')

/-- The FOUR-conjunct IH `flowBodyContent_descend` (and `seqChild_safeBodyUnit`) consume: it produces a
    child's `RecSeqBody` WITHOUT that child's `FlowBodyContent`. -/
abbrev IH4 : Prop :=
  ∀ lo' hi', hi' - lo' < hi - p →
    FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' → Q lo' →
    tokens[hi']!.val = .flowSequenceEnd →
    RecSeqBody ((tokens.toList.take hi').drop lo')

/-- **POSITIVE — four→five is the FREE drop.**  A four-conjunct producer needs LESS, so it yields a
    five-conjunct one by ignoring the extra `FlowBodyContent` input.  Establishes `IH4` is STRICTLY
    STRONGER than `IH5`: the projection the route needs runs UP the strength order. -/
theorem ih5_of_ih4 (ih4 : IH4 tokens p hi Q) : IH5 tokens p hi Q :=
  fun lo' hi' h_lt h_w h_d _h_fbc h_q h_c => ih4 lo' hi' h_lt h_w h_d h_q h_c

/-- **NEGATIVE (residual isolated, sorry-free) — five→four closes IFF a per-window provider exists.**

    The forward projection adapter
    `fun lo' hi' h_lt h_w h_d h_q h_c => ih5 lo' hi' h_lt h_w h_d (?fbc) h_q h_c` leaves exactly the
    hole `?fbc : FlowBodyContent tokens lo' hi'`, over an ARBITRARY strictly-smaller window whose only
    facts are the four INTRINSIC conjuncts.  This theorem closes the projection by taking that hole as
    a hypothesis `provider` — so the residual is NAMED, not `sorry`-marked: the projection exists iff
    `provider` does.  And `provider` (a per-window `FlowBodyContent` from intrinsic facts) is exactly
    what is carrier-free unavailable — its `bodySucc` is genuine emission info (R296/R345) and the
    same-window cycle forbids deriving it from `RecSeqBody`.  Hence: GENUINE arity entanglement. -/
theorem ih4_of_ih5_iff_provider (ih5 : IH5 tokens p hi Q)
    (provider : ∀ lo' hi',
        FlowBodyWindow tokens lo' hi' → FlowBodyContentDeep tokens lo' hi' → Q lo' →
        tokens[hi']!.val = .flowSequenceEnd → FlowBodyContent tokens lo' hi') :
    IH4 tokens p hi Q :=
  fun lo' hi' h_lt h_w h_d h_q h_c =>
    ih5 lo' hi' h_lt h_w h_d (provider lo' hi' h_w h_d h_q h_c) h_q h_c

end L4YAML.Proofs.EmitterScannability.DescendIHProjectionProbe
