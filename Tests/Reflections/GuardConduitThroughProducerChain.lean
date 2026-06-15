/-!
# Reflection 440 — a consumer-boundary guard is only HALF a fix: it must be CONDUITED back
# through the producer-hypothesis chain to the LEAF producer slot, where a pre-built floored
# producer can finally discharge it.  On a FLAT (boundary-anchoring, non-recursive) chain the
# guard rides VERBATIM as a matched antecedent-pair — zero proof content.

Self-contained (core Lean, no `L4YAML` import) toy of the R440 finding — STEP D of the Dyck-floor
exposure, the producer-side completion of R439's consumer-side STEP C.

Context.  R439 (STEP C) installed the interior Dyck floor as a GUARD on the CONSUMER-facing contract
field `FlowSubrangesOk.{seq,map}`.  That made the CONTRACT satisfiable (the cross-matched window is now
fenced out — `flowSubrangesOk_seq_floor_rejects_crossMatched_window`).  But it left the PRODUCER-side
hypothesis chain that SUPPLIES that contract STILL unsatisfiable: `flowSubrangesOk_of_window_producers`'s
`h_seq_rec` (via `seqLocator_of_window_recseqbody`, fed into `flowSubrangesOk_of_locators`) quantified over
every bracket-guarded window with NO floor — so it would be asked for a `RecSeqBody` at the cross-matched
window that has none.  The lemma chain TYPE-CHECKED but was vacuous: conditional on an unsatisfiable
hypothesis.

R440 (STEP D) propagates the SAME guard BACKWARD through that chain to the LEAF producer slot.  Findings:

* **The chain is a CONDUIT of dual-role links.**  Each intermediate lemma is simultaneously a CONSUMER
  (its conclusion SUPPLIES the layer above) and a PRODUCER (its hypothesis is SUPPLIED by the layer
  below).  So a guard added to the TOP contract field must be threaded as a MATCHED ANTECEDENT-PAIR at
  every link: one antecedent on the CONCLUSION (so the layer above can hand the guard down) AND one on the
  HYPOTHESIS (so the link can hand it to the layer below).  The body just `intro`s the conclusion's guard
  binder and forwards it verbatim to the hypothesis call.

* **On a FLAT chain the guard rides VERBATIM.**  The locator chain is a boundary-anchoring COMPOSITION,
  not a recursion that re-bases the window onto a descended origin.  So the floor is window-keyed
  IDENTICALLY `(∀ i, lo ≤ i → i ≤ hi → balance lo i ≥ 0)` at every link — `lo`/`hi` never shift — and the
  thread is pure plumbing with ZERO proof content.  (Contrast R439's CONSUMER side, which WAS a recursion:
  there the guard had to be READ OFF the just-descended field at each step and only the ROOT was genuinely
  new.  Flat conduit ⇒ verbatim ride; recursion ⇒ read-off-descend + root-seed.)

* **The conduit DOCKS two independently-built floored shapes.**  The leaf producer
  `seqRec_of_carrier_and_windowFacts_seq` was built FLOORED ahead of time (R434) — its conclusion already
  carried the floor antecedent.  The contract was floored LATER (R439).  Neither end moved; STEP D only
  aligned the conduit between them.  After STEP D the `h_seq_rec` slot is TEXTUALLY IDENTICAL to the
  producer's conclusion, so the producer plugs straight in.

* **Frontier-NEUTRAL, but real.**  STEP D discharges no `sorry`; it retypes the producer's owed contract
  to EXACTLY the shape an existing lemma delivers — the "retype IS the progress" move
  (`ref_reduction_by_import`).

The transferable rule: a guard added at the consumer contract to fix unsatisfiability is only half the
repair.  The producer-hypothesis chain stays vacuous until the SAME guard is conduited back to the LEAF
producer hypothesis.  Thread it as a matched antecedent-pair through every dual-role link; on a flat chain
it rides verbatim.  Check the docking: the leaf slot should become textually identical to the pre-built
floored producer's conclusion.

The toy models the 3-link conduit (`producer → locator → assembler`), the verbatim floor ride (every link
keys `Floor` on the SAME `w`), the deliverable transforming while the guard does not, the dock (the
floored producer plugs straight in), and the BEFORE state (the unfloored producer hypothesis is
unsatisfiable, so the unfloored chain is vacuous).
-/

namespace Tests.Reflections.GuardConduitThroughProducerChain

set_option autoImplicit false

/-! ## The guard and the per-link deliverables.

The GUARD (`Floor`) rides the conduit untouched.  The DELIVERABLE transforms at each link
(`RecBody → Located → Body`) — distinct predicates with real (non-`id`) coercions — yet the floor is
keyed on the SAME window `w` everywhere: the flat-chain verbatim ride. -/

/-- The OLD bracket guards — too weak: `Balanced 5` holds, so the cross-matched window passes. -/
abbrev Balanced (w : Nat) : Prop := w % 5 = 0

/-- The Dyck FLOOR guard STEP C/D adds.  It EXCLUDES the bad window (`Floor 5` is false).  This single
    predicate rides every conduit link verbatim. -/
abbrev Floor (w : Nat) : Prop := w < 3

/-- The LEAF producer's deliverable (toy of `RecSeqBody`). -/
abbrev RecBody (w : Nat) : Prop := w < 3

/-- The intermediate locator's deliverable (toy of `SeqLocated`) — a DISTINCT predicate, derived from
    `RecBody` by a real coercion. -/
abbrev Located (w : Nat) : Prop := w ≤ 2

/-- The top contract field's deliverable (toy of `SeqBodyProps`). -/
abbrev Body (w : Nat) : Prop := w < 3

/-- The deliverable TRANSFORMS up the chain (`RecBody → Located`) — a genuine, non-`id` coercion. -/
theorem recBodyToLocated {w : Nat} (h : RecBody w) : Located w := Nat.lt_succ_iff.mp h
/-- `Located → Body` — the second genuine coercion. -/
theorem locatedToBody {w : Nat} (h : Located w) : Body w := Nat.lt_succ_of_le h

/-! ## PART 1 — the LEAF producer, built FLOORED ahead of time (the R434 analog).

`seqRec_of_carrier_and_windowFacts_seq` already carried the floor antecedent before STEP D.  Here the
floor is exactly what the leaf CONSUMES to build its deliverable: the bad window never reaches it. -/

/-- The leaf producer.  It CONSUMES the floor (`hfloor`) to build `RecBody`.  Built floored — its shape
    is the target the conduit will dock to. -/
theorem recProducer : ∀ w, Balanced w → Floor w → RecBody w :=
  fun _w _hbal hfloor => hfloor

/-! ## PART 2 — the conduit links: each is BOTH consumer and producer, threading a matched pair.

Each link's TYPE carries the floor on BOTH its hypothesis (`Floor w →` inside the `h_*` argument) AND its
conclusion (the outer `Floor w →`).  Its body RECEIVES the conclusion's floor and FORWARDS it verbatim to
the hypothesis.  Drop EITHER antecedent and the conduit breaks — the matched pair is the conduit
invariant. -/

/-- **Conduit link 1 — the locator** (toy of `seqLocator_of_window_recseqbody`).  Consumes a floored
    `RecBody` producer, produces a floored `Located` conclusion.  Receives `hfloor`, forwards it verbatim
    (SAME `w` — the flat-chain verbatim ride), then coerces the deliverable. -/
theorem locator (h_rec : ∀ w, Balanced w → Floor w → RecBody w) :
    ∀ w, Balanced w → Floor w → Located w :=
  fun w hbal hfloor => recBodyToLocated (h_rec w hbal hfloor)

/-- **Conduit link 2 — the assembler** (toy of `flowSubrangesOk_of_locators`, which is BOTH a consumer of
    `h_seq` and the producer of the contract field).  Before STEP D its lambda RECEIVED the contract
    field's floor but DROPPED it (`_h_floor`) because `h_loc` was unfloored; STEP D makes `h_loc` floored,
    so the lambda now FORWARDS the floor it receives.  Same verbatim ride. -/
theorem assembler (h_loc : ∀ w, Balanced w → Floor w → Located w) :
    ∀ w, Balanced w → Floor w → Body w :=
  fun w hbal hfloor => locatedToBody (h_loc w hbal hfloor)

/-! ## PART 3 — the composition (toy of `flowSubrangesOk_of_window_producers`) and the DOCK. -/

/-- The whole producer chain folded to one lemma keyed only on the LEAF producer hypothesis.  The floor
    threads through both links untouched. -/
theorem ofProducers (h_rec : ∀ w, Balanced w → Floor w → RecBody w) :
    ∀ w, Balanced w → Floor w → Body w :=
  assembler (locator h_rec)

/-- **The dock.**  Because STEP D made the `h_rec` slot TEXTUALLY IDENTICAL to `recProducer`'s type, the
    pre-built floored producer plugs straight in — no coercion, no adapter.  This is the payoff of the
    conduit: two independently-built floored shapes (contract end + producer end) meet exactly. -/
theorem docked : ∀ w, Balanced w → Floor w → Body w :=
  ofProducers recProducer

/-! ## PART 4 — the BEFORE state: the unfloored chain is vacuous (conditional on an unsatisfiable hyp).

Before STEP D the producer hypothesis was unfloored — and on real output it is UNSATISFIABLE: the bad
window `5` passes `Balanced` but has no `RecBody`.  So the unfloored chain type-checked yet could never be
instantiated.  Flooring (STEP D) narrows the producer's domain so the cross-matched window is excluded and
the real floored producer discharges it. -/

/-- The UNFLOORED producer hypothesis is unsatisfiable — the cross-matched witness `5` passes `Balanced`
    but `RecBody 5` is false.  This is WHY a consumer-only floor (STEP C) is half a fix: the producer
    chain stays vacuous until the floor reaches THIS hypothesis. -/
theorem unflooredRec_unsatisfiable : ¬ (∀ w, Balanced w → RecBody w) := by
  intro h
  exact absurd (h 5 (by decide)) (by decide)

/-- The FLOORED producer hypothesis IS satisfiable — `recProducer` discharges it.  The floor narrowed the
    domain so the bad window never reaches the producer. -/
theorem flooredRec_satisfiable : ∀ w, Balanced w → Floor w → RecBody w := recProducer

/-! ## The point, machine-checked. -/

/-- Unfloored producer hypothesis: unsatisfiable (chain vacuous).  Floored: the producer docks and the
    contract holds.  Half-fix → whole-fix is exactly the floor reaching the leaf slot. -/
example :
    (¬ (∀ w, Balanced w → RecBody w)) ∧
    (∀ w, Balanced w → Floor w → Body w) :=
  ⟨unflooredRec_unsatisfiable, docked⟩

end Tests.Reflections.GuardConduitThroughProducerChain
