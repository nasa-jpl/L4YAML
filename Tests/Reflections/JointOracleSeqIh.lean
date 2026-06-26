/-
# Reflection 535 — adapting a JOINT oracle to an axis-specific IH: reconstruct the joint guard for the
sub-window and project one side, the off-axis conditional made vacuous by marker exclusivity

Self-contained companion to `recbody_joint_oracle_seq_ih`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the first concrete brick of the
two `locate`s the carrier-specialised driver `recbody_joint_navigator_driver_carrier` (R534) still takes
as inputs.

The point this file isolates — **a width-recursion driver hands its per-window step a JOINT oracle:
at every strictly-narrower sub-window it delivers BOTH deliverables, keyed on the window's close marker
(`seqEnd → SeqBody` AND `mapEnd → MapBody`).  But the concrete first-entry dispatch consumes a
SEQ-ONLY induction hypothesis that wants a bare `SeqBody` from loose window facts plus an enclosure
predicate.**  The adapter between the two is pure guard RECONSTRUCTION + one-side PROJECTION: the
dispatch hands over the loose pieces (`Win`, `DeepSeq`, `EncSeq`, the seq close, the span/bounds), the
adapter FOLDS them back into the joint guard the oracle wants, calls the oracle, and projects the seq
deliverable out of the returned pair.  The crux is the OFF-axis conditional inside the guard
(`mapEnd → DeepMap ∧ EncMap`): its premise `mark hi' = .mapEnd` contradicts the seq close
`mark hi' = .seqEnd`, so MARKER EXCLUSIVITY collapses it to a vacuous case — no map fact is ever needed
to build the guard in the seq branch.

This is the SEQ half of the cross-deliverable knot.  A carrier-only seq producer
(`seqWindowRecSeqBody_seq_general`) delivers `SeqBody` for nested windows but only on the all-seq PATH
(it cannot speak for a `{`-enclosed frame); drawing the IH from the JOINT oracle instead lifts that
restriction, because the oracle delivers both bodies at EVERY narrower window regardless of enclosing
bracket type.

What this file does:
* `Marker` — a two-constructor close marker (`seqEnd`/`mapEnd`) with `DecidableEq`, so the off-axis
  conditional is refuted by `decide` exactly as the real proof refutes `.flowSequenceEnd = .flowMappingEnd`.
* `JointGuard` — the toy of `RecBodyJointGuard`: bounds ∧ window ∧ a seq conditional ∧ a map conditional
  ∧ the close disjunction, parametric in the predicates.
* `seqIhOfOracle` — the adapter (the audited artifact): joint oracle → seq-only IH, by guard
  reconstruction + `.1` projection, the map conditional vacuous.
* `mapIhOfOracle` — the SYMMETRIC twin (R536): joint oracle → map-only IH, by the SAME guard
  reconstruction + `.2` projection, the SEQ conditional now the vacuous one.  Both halves let each
  dispatch branch (`[`-nested seq, `{`-nested map) draw a path-general IH from the one joint oracle.
* `reconstructGuard` — the guard reconstruction in ISOLATION (one sub-window, no oracle), the move's
  core: fold the loose pieces into the guard, the off-axis conditional discharged by marker exclusivity.
* toy instances RUN end-to-end through BOTH `seqIhOfOracle` and `mapIhOfOracle`.
-/

namespace JointOracleSeqIh

set_option autoImplicit false

/-- A two-constructor close marker — the toy of the flow close tokens `.flowSequenceEnd`/`.flowMappingEnd`.
    `DecidableEq` is what lets the off-axis guard conditional be refuted by `decide`. -/
inductive Marker
  | seqEnd
  | mapEnd
deriving DecidableEq

/-! ## The joint guard — bounds ∧ window ∧ seq-conditional ∧ map-conditional ∧ close-disjunction. -/

/-- Toy of `RecBodyJointGuard tokens lo0 hi0 lo hi`.  The two conditionals carry the axis-specific
    deep-content + enclosure facts, gated on the window's close marker; the final disjunction asserts the
    close IS one of the two markers.  Parametric in the close-marker function `mark` and the predicates. -/
def JointGuard (mark : Nat → Marker)
    (Win DeepSeq DeepMap : Nat → Nat → Prop) (EncSeq EncMap : Nat → Prop)
    (lo0 hi0 lo hi : Nat) : Prop :=
  lo0 ≤ lo ∧ hi ≤ hi0 ∧ Win lo hi ∧
    (mark hi = .seqEnd → DeepSeq lo hi ∧ EncSeq lo) ∧
    (mark hi = .mapEnd → DeepMap lo hi ∧ EncMap lo) ∧
    (mark hi = .seqEnd ∨ mark hi = .mapEnd)

/-! ## The adapter — joint oracle → seq-only IH, by guard reconstruction + projection. -/

/-- **The joint-oracle → seq-IH adapter.**  Given the JOINT `oracle` (at every narrower window it
    returns `(seqEnd → SeqBody) ∧ (mapEnd → MapBody)`) and the two outer bounds, produce the SEQ-ONLY
    induction hypothesis the first-entry dispatch wants: from the loose pieces `Win lo' hi'`,
    `DeepSeq lo' hi'`, `EncSeq lo'`, a seq close `mark hi' = .seqEnd`, and the span/bounds, deliver
    `SeqBody lo' hi'`.

    The proof FOLDS the loose pieces back into the `JointGuard` the oracle demands, then projects `.1`
    applied to the seq close.  The two outer bounds compose by `omega`; the window is verbatim; the seq
    conditional is `fun _ => ⟨h_deep, h_enc⟩` (we are in the seq-close case); the MAP conditional is
    VACUOUS — its premise `mark hi' = .mapEnd` contradicts the seq close, so marker exclusivity
    (`decide` on `Marker.seqEnd = .mapEnd`) discharges it without any map fact; the disjunct is `Or.inl`
    the seq close. -/
theorem seqIhOfOracle (mark : Nat → Marker)
    (Win DeepSeq DeepMap SeqBody MapBody : Nat → Nat → Prop) (EncSeq EncMap : Nat → Prop)
    (lo0 hi0 lo hi : Nat) (h_lo0_lo : lo0 ≤ lo) (h_hi_hi0 : hi ≤ hi0)
    (oracle : ∀ lo' hi', hi' - lo' < hi - lo →
        JointGuard mark Win DeepSeq DeepMap EncSeq EncMap lo0 hi0 lo' hi' →
        (mark hi' = .seqEnd → SeqBody lo' hi') ∧ (mark hi' = .mapEnd → MapBody lo' hi')) :
    ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
      Win lo' hi' → DeepSeq lo' hi' → EncSeq lo' → mark hi' = .seqEnd → SeqBody lo' hi' := by
  intro lo' hi' h_span h_lo_lo' h_hi'_hi h_win h_deep h_enc h_seqEnd
  refine (oracle lo' hi' h_span ?_).1 h_seqEnd
  -- fold the loose pieces back into the joint guard; the map conditional is vacuous.
  refine ⟨by omega, by omega, h_win, fun _ => ⟨h_deep, h_enc⟩, fun h_mapEnd => ?_, Or.inl h_seqEnd⟩
  rw [h_seqEnd] at h_mapEnd
  exact absurd h_mapEnd (by decide)

/-- **The SYMMETRIC twin — joint oracle → MAP-only IH.**  Same adapter, opposite axis: from the loose
    pieces `Win lo' hi'`, `DeepMap lo' hi'`, `EncMap lo'`, a MAP close `mark hi' = .mapEnd`, and the
    span/bounds, deliver `MapBody lo' hi'`.  The proof folds the SAME joint guard and projects `.2`
    applied to the map close; this time the SEQ conditional is the vacuous one — its premise
    `mark hi' = .seqEnd` contradicts the map close, refuted by `decide` on `Marker.mapEnd = .seqEnd`; the
    map conditional is `fun _ => ⟨h_deep, h_enc⟩`; the disjunct is `Or.inr` the map close.  The real
    `recbody_joint_oracle_map_ih` is this verbatim, both halves auditing the minimal `[propext,
    Quot.sound]`. -/
theorem mapIhOfOracle (mark : Nat → Marker)
    (Win DeepSeq DeepMap SeqBody MapBody : Nat → Nat → Prop) (EncSeq EncMap : Nat → Prop)
    (lo0 hi0 lo hi : Nat) (h_lo0_lo : lo0 ≤ lo) (h_hi_hi0 : hi ≤ hi0)
    (oracle : ∀ lo' hi', hi' - lo' < hi - lo →
        JointGuard mark Win DeepSeq DeepMap EncSeq EncMap lo0 hi0 lo' hi' →
        (mark hi' = .seqEnd → SeqBody lo' hi') ∧ (mark hi' = .mapEnd → MapBody lo' hi')) :
    ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi →
      Win lo' hi' → DeepMap lo' hi' → EncMap lo' → mark hi' = .mapEnd → MapBody lo' hi' := by
  intro lo' hi' h_span h_lo_lo' h_hi'_hi h_win h_deep h_enc h_mapEnd
  refine (oracle lo' hi' h_span ?_).2 h_mapEnd
  -- fold the loose pieces back into the joint guard; the seq conditional is now the vacuous one.
  refine ⟨by omega, by omega, h_win, fun h_seqEnd => ?_, fun _ => ⟨h_deep, h_enc⟩, Or.inr h_mapEnd⟩
  rw [h_mapEnd] at h_seqEnd
  exact absurd h_seqEnd (by decide)

/-! ## The guard reconstruction in ISOLATION — one sub-window, no oracle. -/

/-- **Folding the loose pieces into the joint guard at a single window** (no oracle, no recursion).
    Isolates exactly the move `seqIhOfOracle` performs: the dispatch's loose facts become a
    `JointGuard`, the OFF-axis (map) conditional discharged by marker exclusivity — `h_seqEnd` and a
    hypothetical `h_mapEnd` would force `Marker.seqEnd = .mapEnd`, refuted by `decide`. -/
theorem reconstructGuard (mark : Nat → Marker)
    (Win DeepSeq DeepMap : Nat → Nat → Prop) (EncSeq EncMap : Nat → Prop)
    (lo0 hi0 lo' hi' : Nat) (h_lo0_lo' : lo0 ≤ lo') (h_hi'_hi0 : hi' ≤ hi0)
    (h_win : Win lo' hi') (h_deep : DeepSeq lo' hi') (h_enc : EncSeq lo')
    (h_seqEnd : mark hi' = .seqEnd) :
    JointGuard mark Win DeepSeq DeepMap EncSeq EncMap lo0 hi0 lo' hi' :=
  ⟨h_lo0_lo', h_hi'_hi0, h_win, fun _ => ⟨h_deep, h_enc⟩,
    fun h_mapEnd => absurd (h_seqEnd.symm.trans h_mapEnd) (by decide), Or.inl h_seqEnd⟩

/-! ## Toy instance: the adapter RUNS end-to-end. -/

/-- Every window closes with a seq marker; predicates trivial. -/
def markToy (_ : Nat) : Marker := .seqEnd
def R2 (_ _ : Nat) : Prop := True
def R1 (_ : Nat) : Prop := True

/-- The toy joint oracle over the outer window `[0, 3)`: ignores the guard, returns both arms trivially. -/
theorem oracleToy : ∀ lo' hi', hi' - lo' < 3 - 0 →
    JointGuard markToy R2 R2 R2 R1 R1 0 3 lo' hi' →
    (markToy hi' = .seqEnd → R2 lo' hi') ∧ (markToy hi' = .mapEnd → R2 lo' hi') :=
  fun _ _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩

/-- The adapter RUN: the seq-IH drawn from `oracleToy`, instantiated at the sub-window `[1, 2)` of the
    outer `[0, 3)`, delivering `R2 1 2`.  Elaborates to a closed value. -/
example : R2 1 2 :=
  seqIhOfOracle markToy R2 R2 R2 R2 R2 R1 R1 0 3 0 3 (Nat.le_refl 0) (Nat.le_refl 3) oracleToy
    1 2 (by omega) (by omega) (by omega) trivial trivial trivial rfl

/-- Every window closes with a MAP marker; predicates trivial — the map-side toy oracle. -/
def markMapToy (_ : Nat) : Marker := .mapEnd

theorem oracleMapToy : ∀ lo' hi', hi' - lo' < 3 - 0 →
    JointGuard markMapToy R2 R2 R2 R1 R1 0 3 lo' hi' →
    (markMapToy hi' = .seqEnd → R2 lo' hi') ∧ (markMapToy hi' = .mapEnd → R2 lo' hi') :=
  fun _ _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩

/-- The MAP twin RUN: the map-IH drawn from `oracleMapToy`, at the sub-window `[1, 2)` of `[0, 3)`,
    delivering `R2 1 2`.  Elaborates to a closed value — the symmetric brick runs end-to-end too. -/
example : R2 1 2 :=
  mapIhOfOracle markMapToy R2 R2 R2 R2 R2 R1 R1 0 3 0 3 (Nat.le_refl 0) (Nat.le_refl 3) oracleMapToy
    1 2 (by omega) (by omega) (by omega) trivial trivial trivial rfl

end JointOracleSeqIh

/-- info: 'JointOracleSeqIh.seqIhOfOracle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms JointOracleSeqIh.seqIhOfOracle

/-- info: 'JointOracleSeqIh.mapIhOfOracle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms JointOracleSeqIh.mapIhOfOracle
