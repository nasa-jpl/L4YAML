/-!
# Reflection 387 — a conjunctive / multi-axis universal consumer cannot be discharged by a
single-axis producer, no matter how complete that axis's chain; recursion makes the "obviously
single-axis" object's orthogonal conjunct NON-vacuous.

Self-contained core-Lean toy of L4YAML R387.  Wiring the now-hypothesis-free nested-seq locator
(`nestedSeq_recseqentry_locate`, R386) toward the seq frontier sorry, the CONSUME plan asked: *can the
seq sorry (`NonemptyStructure.lean:7502`, goal `FlowSubrangesOk tokens`) close on the seq locator ALONE
before building the map side?*  The answer is STRUCTURAL: `FlowSubrangesOk` is a CONJUNCTION of two
orthogonal universals — `seq : ∀ lo hi, … → SeqBodyProps …` and `map : ∀ lo hi, … → MapBodyProps …`.
A producer serving only the SEQ axis cannot discharge the conjunction however complete its (multi-stage)
chain is — the map conjunct is an INDEPENDENT obligation.  And the misleading intuition — "the object is
a top-level SEQUENCE, so the map axis is vacuous" — is FALSE: recursion mixes the axes (a seq can nest a
mapping, `[{a: b}]`), so the map conjunct is non-vacuous and `h_map_rec` is owed regardless.

Mapping to L4YAML: `BothOk` ~ `FlowSubrangesOk`; `SeqHalf`/`MapHalf` ~ its `seq`/`map` universals;
`seqProducer` ~ the seq locator→carrier→`RecSeqBody` chain (`nestedSeq_safeBodyUnit_of_locator`, R387,
the first hop); the missing `MapHalf` ~ the owed map mirror (`RecMapBody` axis).

POSITIVE: `bothOk_needs_both` — the conjunctive consumer is dischargeable only with BOTH producers.
NEGATIVE: `seqHalf_alone_insufficient` — the seq half alone does NOT imply `BothOk` (a witness passing
`SeqHalf` but failing `MapHalf`); `mapHalf_nonvacuous` — the orthogonal conjunct is non-vacuous on the
very witness the seq producer handles, so no completeness of the seq chain can reach it.

The transferable rule: when asked "can deliverable X close sorry S alone?", DECOMPOSE S's consumer into
its independent conjuncts/axes FIRST; if S = (P_seq ∧ P_map) and X serves only one axis, the answer is
NO by the consumer's STRUCTURE, not the producer's completeness — and don't assume the orthogonal axis is
vacuous just because the object's top-level type is single-axis.  Sibling of
[[ref-entry-boundary-input-shape-split]] (whether a BRICK mirrors seq/map) at the CONSUMER-gating layer.
-/

namespace Tests.Reflections.ConjunctiveConsumerGatesOnOrthogonalAxis

set_option autoImplicit false

/-- The "seq axis" per-item universal — all elements even. -/
def SeqHalf (ns : List Nat) : Prop := ∀ n ∈ ns, n % 2 = 0

/-- The "map axis" per-item universal — all elements divisible by 3.  ORTHOGONAL to `SeqHalf`. -/
def MapHalf (ns : List Nat) : Prop := ∀ n ∈ ns, n % 3 = 0

/-- The frontier consumer is a CONJUNCTION of the two orthogonal universals
    (mirrors `FlowSubrangesOk = seq-universal ∧ map-universal`). -/
structure BothOk (ns : List Nat) : Prop where
  seq : SeqHalf ns
  map : MapHalf ns

/-- A SINGLE-AXIS producer: I can build the seq half (here from a div-6 premise — a stand-in for the
    multi-stage seq locator → carrier → `RecSeqBody` chain). -/
theorem seqProducer (ns : List Nat) (h : ∀ n ∈ ns, n % 6 = 0) : SeqHalf ns :=
  fun n hn => by have := h n hn; omega

/-- **POSITIVE.** `BothOk` is dischargeable only with BOTH producers; supplying the seq half is half
    the contract.  The conjunctive consumer gates on EVERY conjunct, not the "main" one. -/
theorem bothOk_needs_both (ns : List Nat)
    (h_seq : SeqHalf ns) (h_map : MapHalf ns) : BothOk ns := ⟨h_seq, h_map⟩

/-- **NEGATIVE.** The seq half ALONE does not imply `BothOk`: `[2]` satisfies `SeqHalf` (all even) but
    fails `MapHalf` (2 is not divisible by 3), so `BothOk` fails.  The orthogonal conjunct is an
    INDEPENDENT obligation — no completeness of the seq chain can discharge it. -/
theorem seqHalf_alone_insufficient : ∃ ns, SeqHalf ns ∧ ¬ BothOk ns :=
  ⟨[2], fun n hn => by simp only [List.mem_singleton] at hn; omega,
    fun h => by have := h.map 2 (by simp); omega⟩

/-- **The "main axis looks total" trap, concretely.**  Even when the object's top-level type is
    single-axis (a top-level SEQUENCE), recursion MIXES the axes: a seq can nest a map (`[{a: b}]`),
    so the orthogonal `MapHalf` conjunct is NON-VACUOUS.  `[2]` is "all even" yet `MapHalf` fails. -/
theorem mapHalf_nonvacuous : ¬ MapHalf [2] := fun h => by have := h 2 (by simp); omega

/-- The seq witness IS available (the seq producer fires) — but that is not the gate. -/
theorem seqHalf_holds : SeqHalf [2] := fun n hn => by simp only [List.mem_singleton] at hn; omega

#guard 2 % 2 == 0      -- seq axis holds on the witness
#guard !(2 % 3 == 0)   -- map axis fails on the same witness ⇒ the conjunction is gated by the map axis

/-! ## R411 — an axis-UNIFORM intermediate collapses the split to ONE deliverable fed from two sources

Once the orthogonal split is FORCED, the per-axis producer cost is not automatically "doubled at every
stage."  If a predicate on the critical path is AXIS-UNIFORM — one shape that fires on BOTH axes — the two
conjuncts collapse to ONE per-window deliverable, and the per-axis residual shrinks to JUST the SOURCE
wiring.  Toy of L4YAML R411: `GlobalAdj` ~ the axis-uniform `GlobalFlowSeqOpenerAdj`; `seqSource`/`mapSource`
~ `seqGlobalFlowSeqOpenerAdj_of_emit`/`mapGlobalFlowSeqOpenerAdj_of_emit`; `windowAdj_of_global` ~
`flowSeqOpenerAdj_window_of_global`; `seqWindowAdj`/`mapWindowAdj` ~ the two window providers.  But
uniformity must be CERTIFIED, not assumed (the R395 cross-axis firing probe): a NON-uniform intermediate
cannot be produced from one of the axes, so the "shared" provider would be vacuous there. -/

/-- The axis-UNIFORM global predicate (stand-in for `GlobalFlowSeqOpenerAdj`): "every element div-5".
    ONE shape — it does NOT mention seq vs map. -/
def GlobalAdj (full : List Nat) : Prop := ∀ n ∈ full, n % 5 = 0

/-- SEQ emit source producing the uniform global fact (stand-in for `seqGlobalFlowSeqOpenerAdj_of_emit`). -/
theorem seqSource (full : List Nat) (h : ∀ n ∈ full, n % 10 = 0) : GlobalAdj full :=
  fun n hn => by have := h n hn; omega

/-- MAP emit source producing the SAME uniform global fact (stand-in for `mapGlobalFlowSeqOpenerAdj_of_emit`). -/
theorem mapSource (full : List Nat) (h : ∀ n ∈ full, n % 15 = 0) : GlobalAdj full :=
  fun n hn => by have := h n hn; omega

/-- ONE restriction lemma: the global fact restricts to any sub-window (stand-in for
    `flowSeqOpenerAdj_window_of_global`). -/
theorem windowAdj_of_global (full window : List Nat)
    (h : GlobalAdj full) (h_sub : ∀ n ∈ window, n ∈ full) : ∀ n ∈ window, n % 5 = 0 :=
  fun n hn => h n (h_sub n hn)

/-- **POSITIVE (R411).** The two per-window providers are IDENTICAL except for the source call — the
    split's downstream cost is paid ONCE at the source, not per stage. -/
theorem seqWindowAdj (full window : List Nat) (h : ∀ n ∈ full, n % 10 = 0)
    (h_sub : ∀ n ∈ window, n ∈ full) : ∀ n ∈ window, n % 5 = 0 :=
  windowAdj_of_global full window (seqSource full h) h_sub

theorem mapWindowAdj (full window : List Nat) (h : ∀ n ∈ full, n % 15 = 0)
    (h_sub : ∀ n ∈ window, n ∈ full) : ∀ n ∈ window, n % 5 = 0 :=
  windowAdj_of_global full window (mapSource full h) h_sub

/-- A NON-uniform intermediate (the SEQ source's own premise "div-10"). -/
def BadGlobal (full : List Nat) : Prop := ∀ n ∈ full, n % 10 = 0

/-- **NEGATIVE (R411).** Uniformity must be CERTIFIED.  `BadGlobal` cannot be produced from the MAP axis:
    `15` is div-15 (the map source's premise holds) yet not div-10 (BadGlobal fails), so a provider keyed
    on `BadGlobal` would be vacuous / unprovable on the map axis — exactly why the uniform predicate's
    cross-axis firing had to be probed before sharing it. -/
theorem badGlobal_not_axis_uniform : ∃ n, n % 15 = 0 ∧ ¬ (n % 10 = 0) :=
  ⟨15, by decide, by decide⟩

#guard 10 % 5 == 0 && 15 % 5 == 0   -- both sources' premises imply the uniform predicate
#guard 15 % 15 == 0 && !(15 % 10 == 0)  -- but a NON-uniform intermediate breaks on the map axis

end Tests.Reflections.ConjunctiveConsumerGatesOnOrthogonalAxis
