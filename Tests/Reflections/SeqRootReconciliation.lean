/-! # Reflection 512 — fold the whole discharged seq chain into the contract consumer, collapsing
        the seq half of the frontier obligation to ONE hard residual (the root carrier)

R415 (`seqWindowRecSeqBody_seq_general`) + the R432–R441 emit/fold-totality chain already close the
seq navigator end-to-end *given the root carrier* `SeqInteriorSeparators tokens 2 (size-2)`.  R512
(`flowSubrangesOk_of_seqRoot_and_map_producers`) is the critical-path RECONCILIATION: it composes the
contract consumer `flowSubrangesOk_of_window_producers` with `seqHRec_of_root_and_emit` in its
`h_seq_rec` slot (a direct substitution — R440 made the two universals textually identical), so the
SEQ half of the frontier obligation `FlowSubrangesOk tokens` collapses to **the single hypothesis
`h_root_carrier`** plus emit context already in scope at the sorry site.  This is
[[ref-fold-consumer-chain-to-producer-contract]] applied at the contract level.

Two findings the brick pins:

* **Where the genuine work lives.**  After the fold, `h_root_carrier` is the ONLY seq-side hypothesis
  left — so the sole open seq residual is the root carrier (= `seqRoot_seqInteriorSeparators` fed its
  `desc` descent provider, the hard B2 brick).  The map side stays as its seven RAW per-window
  producers (`h_map_rec` + six grammar facts): the seq axis is one carrier away from done, the map
  axis still owes its whole producer family — a recorded seq/map ASYMMETRY.
* **The driver line is OFF the critical path.**  The width-recursion DRIVER
  `recseqbody_navigator_driver` (R510) and its extracted `recseqbody_seq_descend_tail` (R511) are a
  *parallel* modular re-derivation of R415's inlined per-window `step`.  Correct, but redundant:
  building `locate` + re-typing the driver would re-prove what R415 already delivers.  Because
  `RecSeqBody`-at-a-window is a `Prop`, the driver-route witness and the carrier-route witness are the
  SAME proof up to proof-irrelevance, so the driver adds nothing once the carrier route closes it.

This demo (self-contained core Lean, no imports) models the reconciliation over a tiny token toy:

* `Carrier` is the single hard residual (here: a balanced-bracket-count stand-in for
  `SeqInteriorSeparators tokens 2 (size-2)`); `Emit` is the context available at the consume site.
* `windowFacts_of_carrier` (toy R432) → `seqProducer_of_windowFacts` (toy R415) is the discharged seq
  chain; `seqProducer_of_carrier_and_emit` (toy `seqHRec_of_root_and_emit`) folds it.
* `contract_of_producers` (toy `flowSubrangesOk_of_window_producers`) needs BOTH a `SeqProducer` and a
  RAW `MapProducer`; `contract_of_carrier_and_map` (toy R512) collapses the seq half so the `Contract`
  follows from `Carrier ∧ Emit ∧ MapProducer` — the seq side is now a single carrier hypothesis.
* `seqProducer_via_driver` + `driver_route_redundant` model the off-path finding: a SECOND route to the
  SAME `SeqProducer` Prop, proven equal to the carrier route by `rfl` (proof irrelevance) — i.e. the
  driver re-derives an already-closed obligation.
* `run` exhibits a concrete `Contract sample` through the reconciliation.

Axioms: `demo` and `run` depend on NONE (the real `flowSubrangesOk_of_seqRoot_and_map_producers`
carries `[propext, Classical.choice, Quot.sound]`, inherited from the recursion/`WellTyped` plumbing;
the toy sheds it).
-/

namespace SeqRootReconciliation

/-- Toy token alphabet: `1` = open bracket, `2` = close bracket, `0` = separator. -/
abbrev Toks := List Nat
def OPEN : Nat := 1
def SEP : Nat := 0
def CLOSE : Nat := 2

/-- **The single HARD residual.**  Toy mirror of `SeqInteriorSeparators tokens 2 (size-2)` — the seq
    root carrier, fed in the real proof by the `desc` descent provider (`seqEnclosingOpener_of_gate`
    LOCATE + `seqDescent_provider_of_gate` ASSEMBLE).  Here a balanced-bracket-count stand-in. -/
structure Carrier (t : Toks) : Prop where
  balanced : t.count OPEN = t.count CLOSE

/-- Emit context available at the consume site (real: `h_scan`/`h_ne`/`h_wt_outer`/boundary tokens). -/
structure Emit (t : Toks) : Prop where
  nonempty : t ≠ []

/-- The per-window intermediate (real: `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ SeqEnclosed`). -/
structure WindowFacts (t : Toks) : Prop where
  fromCarrier : t.count OPEN = t.count CLOSE
  fromEmit : t ≠ []

/-- The seq deliverable the contract needs at every window (real: `h_seq_rec`, i.e. `RecSeqBody`). -/
structure SeqProducer (t : Toks) : Prop where
  facts : WindowFacts t

/-- The map deliverable, left RAW (real: `h_map_rec` + the six map-grammar facts — NOT yet reduced). -/
structure MapProducer (t : Toks) : Prop where
  raw : True

/-- The frontier obligation (real: `FlowSubrangesOk tokens` at `NonemptyStructure.lean:11208`). -/
structure Contract (t : Toks) : Prop where
  seq : SeqProducer t
  map : MapProducer t

/-- Toy R432 — the window facts from the carrier + emit context. -/
def windowFacts_of_carrier (t : Toks) (hc : Carrier t) (he : Emit t) : WindowFacts t :=
  ⟨hc.balanced, he.nonempty⟩

/-- Toy R415 (`seqWindowRecSeqBody_seq_general`) — the seq deliverable from the window facts. -/
def seqProducer_of_windowFacts (t : Toks) (hw : WindowFacts t) : SeqProducer t := ⟨hw⟩

/-- Toy `seqHRec_of_root_and_emit` — FOLD the discharged seq chain: the seq deliverable now follows
    from the carrier + emit alone. -/
def seqProducer_of_carrier_and_emit (t : Toks) (hc : Carrier t) (he : Emit t) : SeqProducer t :=
  seqProducer_of_windowFacts t (windowFacts_of_carrier t hc he)

/-- Toy `flowSubrangesOk_of_window_producers` — the contract consumer, needing BOTH producers. -/
def contract_of_producers (t : Toks) (hs : SeqProducer t) (hm : MapProducer t) : Contract t := ⟨hs, hm⟩

/-- **Toy R512** (`flowSubrangesOk_of_seqRoot_and_map_producers`) — the RECONCILIATION.  The contract
    collapses to `Carrier ∧ Emit ∧ MapProducer`: the whole seq half is now the single carrier
    hypothesis, the map side still raw. -/
def contract_of_carrier_and_map (t : Toks) (hc : Carrier t) (he : Emit t) (hm : MapProducer t) :
    Contract t :=
  contract_of_producers t (seqProducer_of_carrier_and_emit t hc he) hm

/-- The width-recursion DRIVER's obligations (toy R510 `locate` + R511 `descend_tail`). -/
structure DriverObligations (t : Toks) : Prop where
  locate : t ≠ []
  descendTail : t.count OPEN = t.count CLOSE

/-- A SECOND route to the SAME `SeqProducer`, via the driver decomposition (toy R510/R511). -/
def seqProducer_via_driver (t : Toks) (hd : DriverObligations t) : SeqProducer t :=
  ⟨⟨hd.descendTail, hd.locate⟩⟩

/-- **The off-path finding.**  `SeqProducer t` is a `Prop`, so the carrier route and the driver route
    produce the SAME proof up to proof-irrelevance — the driver re-derives an already-closed
    obligation and adds nothing once the carrier route exists. -/
theorem driver_route_redundant (t : Toks) (hc : Carrier t) (he : Emit t) (hd : DriverObligations t) :
    seqProducer_of_carrier_and_emit t hc he = seqProducer_via_driver t hd :=
  rfl

/-- A concrete well-formed toy stream `[ , ]` (counts: one OPEN, one CLOSE). -/
def sample : Toks := [OPEN, SEP, CLOSE]

theorem sample_carrier : Carrier sample := ⟨by decide⟩
theorem sample_emit : Emit sample := ⟨by decide⟩
theorem sample_map : MapProducer sample := ⟨trivial⟩

/-- A RUN: the contract through the reconciliation, seq half collapsed to the carrier. -/
theorem run : Contract sample :=
  contract_of_carrier_and_map sample sample_carrier sample_emit sample_map

/-- The demo deliverable: the contract follows from `Carrier ∧ Emit ∧ MapProducer` (seq half folded to
    one residual), and the driver route is provably the SAME proof as the carrier route (off-path). -/
theorem demo :
    Contract sample
    ∧ (∀ (hc : Carrier sample) (he : Emit sample) (hd : DriverObligations sample),
        seqProducer_of_carrier_and_emit sample hc he = seqProducer_via_driver sample hd) :=
  ⟨run, fun hc he hd => driver_route_redundant sample hc he hd⟩

end SeqRootReconciliation
