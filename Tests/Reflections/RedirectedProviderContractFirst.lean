/-!
# Reflection 395 — a redirected heavy producer: name the contract, land the trivial restriction, probe satisfiable with the OLD route's counterexample.

Self-contained core-Lean toy of L4YAML R395, the first increment after R394 redirected the root-seed
opener-field producer.  R394 ([[ref-all-depth-overreach-source-globally]]) PROVED the planned route a
dead end: the all-depth opener field reaches `.flowSequenceStart` openers strictly inside flow-MAP
interiors, where the seq-axis recursive deliverable `RecSeqBody` bottoms out at `WellBracketed` — so the
field is NOT projectable from that single axis, even though it is TRUE there.  The fix is to source the
fact GLOBALLY (by value-induction on the emitter, uniform across axes).  That producer is heavy /
multi-session; the IRON RULE wants one green increment.

The disciplined first increment on the new route is a 3-part DE-RISK, not the producer:

1. **NAME the contract** (`GlobalAdj`) — the exact global predicate the producer must establish, as a
   `def`, so the consumer can cite it before it is proven.
2. **LAND the consume-side bridge** (`windowField_of_global`) — the window-relative field shape restricts
   from the global predicate in ONE `omega` bound step (the payoff of keeping the field all-depth: the
   restriction edge is pure subset narrowing, no re-basing).  This isolates the residual to EXACTLY the
   heavy producer.
3. **PROBE the contract satisfiable** — and choose the witness = the OLD route's COUNTEREXAMPLE
   (`crossWitness`, the cross-axis list whose map-interior opener broke the seq route).  The body fires
   NON-VACUOUSLY at BOTH a seq-spine opener (`i = 0`) and a map-interior opener (`i = 3`).  DOUBLE DUTY:
   `recBody_underdetermines` re-confirms the OLD route's failure on the same shape, while
   `globalAdj_crossWitness` confirms the NEW route reaches exactly where the old one couldn't — pinning
   the cross-axis UNIFORMITY the single-axis deliverable lacked.

POSITIVE: `windowField_of_global` (the trivial restriction lands); `globalAdj_crossWitness` (the contract
holds fully on the cross-axis witness); `crossWitness_fires_seq_spine` / `crossWitness_fires_map_interior`
(non-vacuous firing at both axes).
NEGATIVE: `recBody_underdetermines` (the single-axis deliverable does NOT entail the global contract —
it accepts `badWitness`, whose map-interior opener `i = 1` is followed by `mcls` ≠ content-start).

Mapping to L4YAML: `GlobalAdj` ~ `GlobalFlowSeqOpenerAdj`; `windowField_of_global` ~
`flowSeqOpenerAdj_window_of_global`; `crossWitness` ~ the scan of `[{a: [b]}]` (openers `k = 1` spine,
`k = 6` map interior); `globalAdj_crossWitness` / the two firing lemmas ~
`globalFlowSeqOpenerAdj_fires_cross_axis`; `RecBody.mapEntry` ~ `RecSeqEntry.map` (`WellBracketed`-only);
`recBody_underdetermines` ~ `flowBodyContentDeepSeq_opener_reaches_map_interior` (R394).
-/

namespace Tests.Reflections.RedirectedProviderContractFirst

set_option autoImplicit false

inductive Tok | opn | cls | mopn | mcls | content
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A content-start token (= `isFlowContentStart`): content, or a sequence/mapping opener. -/
def isContentStart (t : Tok) : Prop := t = .content ∨ t = .opn ∨ t = .mopn

/-- **(1) NAME the contract** (= `GlobalFlowSeqOpenerAdj`): over the WHOLE list, every `opn` with a
    non-`cls` successor is followed by a content-start.  `List.range`-bounded so it is `decide`-able. -/
def GlobalAdj (l : List Tok) : Prop :=
  ∀ i ∈ List.range l.length, i + 1 < l.length →
    l[i]! = .opn → l[i+1]! ≠ .cls → isContentStart l[i+1]!

/-- The window-relative field (= the `openerContentStart` shape over `[lo, hi)`). -/
def WindowField (l : List Tok) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i + 1 < hi → l[i]! = .opn → l[i+1]! ≠ .cls → isContentStart l[i+1]!

/-- **(2) LAND the trivial restriction** (= `flowSeqOpenerAdj_window_of_global`).  The window field
    follows from the global contract by ONE `omega` bound step — the all-depth field's payoff. -/
theorem windowField_of_global {l : List Tok} {lo hi : Nat}
    (h : GlobalAdj l) (h_hi : hi ≤ l.length) : WindowField l lo hi := by
  intro i _ hihi ho hne
  exact h i (List.mem_range.mpr (by omega)) (by omega) ho hne

/-- The OLD route deliverable (= `RecSeqBody`): recurses through `opn`-interiors (`seqEntry`) but BOTTOMS
    OUT at a weak `True` substrate for `mopn`-interiors (`mapEntry`) — exactly `RecSeqEntry.map`. -/
inductive RecBody : List Tok → Prop where
  | scalarEntry : RecBody [.content]
  | seqEntry (interior : List Tok) (h : RecBody interior) :
      RecBody (.opn :: interior ++ [.cls])
  | mapEntry (interior : List Tok) (h : True) :
      RecBody (.mopn :: interior ++ [.mcls])

/-- Same map-entry SHAPE as a real witness, but its interior opener (`i = 1`) is followed by `mcls`
    (not content-start, not `cls`) — violating the contract. -/
def badWitness : List Tok := [.mopn, .opn, .mcls, .mcls]

theorem recBody_badWitness : RecBody badWitness := RecBody.mapEntry [.opn, .mcls] trivial

theorem globalAdj_badWitness_false : ¬ GlobalAdj badWitness := by
  unfold GlobalAdj isContentStart badWitness; decide

/-- **NEGATIVE — the single-axis deliverable does NOT entail the contract.**  `RecBody` accepts
    `badWitness` (its `mapEntry` is blind to the interior) yet `GlobalAdj badWitness` is FALSE — so there
    is no projection `RecBody l → GlobalAdj l`.  This is the dead end that forced the redirect. -/
theorem recBody_underdetermines : ¬ ∀ l, RecBody l → GlobalAdj l := fun h =>
  globalAdj_badWitness_false (h badWitness recBody_badWitness)

/-- **(3) PROBE satisfiable with the OLD route's COUNTEREXAMPLE.**  `crossWitness` has an `opn` at the
    seq spine (`i = 0`) AND one strictly inside the map interior (`i = 3`, between `mopn`@1 and `mcls`@6).
    The contract holds FULLY on it. -/
def crossWitness : List Tok := [.opn, .mopn, .content, .opn, .content, .cls, .mcls, .cls]

theorem globalAdj_crossWitness : GlobalAdj crossWitness := by
  unfold GlobalAdj isContentStart crossWitness; decide

/-- **POSITIVE — fires NON-VACUOUSLY at the seq-spine opener (`i = 0`).**  Successor `mopn` is a
    content-start (the map disjunct). -/
theorem crossWitness_fires_seq_spine :
    crossWitness[0]! = .opn ∧ crossWitness[1]! ≠ .cls ∧ isContentStart crossWitness[1]! := by
  refine ⟨by decide, by decide, ?_⟩
  unfold isContentStart crossWitness; decide

/-- **POSITIVE — fires NON-VACUOUSLY at the map-INTERIOR opener (`i = 3`).**  This is the position the
    single-axis `RecBody` cannot witness; the global contract reaches it.  Successor `content`. -/
theorem crossWitness_fires_map_interior :
    crossWitness[3]! = .opn ∧ crossWitness[4]! ≠ .cls ∧ isContentStart crossWitness[4]! := by
  refine ⟨by decide, by decide, ?_⟩
  unfold isContentStart crossWitness; decide

#guard crossWitness.length == 8
#guard crossWitness[0]! == Tok.opn      -- seq-spine opener
#guard crossWitness[3]! == Tok.opn      -- map-interior opener (inside mopn..mcls)
#guard badWitness[1]! == Tok.opn        -- same-shape map entry's interior opener ...
#guard badWitness[2]! == Tok.mcls       -- ... followed by mcls (not content-start, not cls): violated

end Tests.Reflections.RedirectedProviderContractFirst
