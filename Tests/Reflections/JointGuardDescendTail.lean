/-
# Reflection 533 — folding the JOINT navigator guard: pack the reproducible window facts into one named
`G`, so the carrier-fed descend's output IS `G (m+1) hi` and the only non-pass-through is the suffix
frame LOWER bound, re-established by arithmetic

Self-contained companion to `RecBodyJointGuard` + `recbody_joint_guard_descend_tail`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the guard-fold half of the
joint-driver re-type (brick (2) piece (i)).

The point this file isolates — **a width-recursion driver runs `windowWidth_strongRecOn` over an abstract
guard `G`, and its `descend_tail` slot demands `G lo hi → … → G (m+1) hi`.**  The carrier-fed descend
(R532) already advances the UNPACKED window facts (window, the two close-gated deep/enclosure halves,
the close disjunction) to the suffix `[m+1, hi)`.  Folding those facts — PLUS the frame bounds
`lo0 ≤ lo ∧ hi ≤ hi0` that witness the per-window carrier narrowing — into one named conjunction `G` is
all it takes to retype that edge into the driver's slot shape: project `G lo hi`, call the carrier edge,
re-pack as `G (m+1) hi`.  The ONLY conjunct that is not a verbatim pass-through is the suffix frame
lower bound `lo0 ≤ m+1`, re-established by `omega` from `lo0 ≤ lo` and `lo < m`; the upper bound
`hi ≤ hi0` is shared with the window's close `hi` and carries unchanged.

What stays OUTSIDE `G` is the part the recursion cannot reproduce per-window from `G` alone: the two
fixed-at-root carriers, the map-deferred fact `M2`, and the marker balance `Bal`.  Those remain explicit
inputs to the descend — exactly the plumbing the driver must still thread.  So the fold sorts every
fact into "reproducible ⇒ inside `G`" vs "irreproducible ⇒ named outer input".

This file models the carrier-fed descend as one abstract edge, defines the folded guard `Guard`, proves
the exact descend-at-guard lemma the real one performs, then instantiates at toy types and runs both
close branches end-to-end (input guard → descended suffix guard).
-/

namespace JointGuardDescendTail

set_option autoImplicit false

/-- The window close token — the gate discriminator (toy stand-in for `YamlToken`'s
    `.flowSequenceEnd` / `.flowMappingEnd`). -/
inductive Close where
  | seqEnd
  | mapEnd
  | scalar
  deriving DecidableEq

/-! ## The folded guard — the reproducible window facts + frame bounds, as one named conjunction. -/

/-- **The folded JOINT navigator guard.**  Parametric in the close map and the window/deep/enclosure
    guards.  Bundles the per-window facts the recursion REPRODUCES: the frame bounds `lo0 ≤ lo ∧ hi ≤ hi0`
    (the carrier-narrowing witnesses), the window `Win`, the two close-gated deep+enclosure halves, and
    the close disjunction.  This is `G : Nat → Nat → Prop` once `lo0`/`hi0` are fixed — the predicate
    `windowWidth_strongRecOn` descends along. -/
def Guard (close : Nat → Close) (Win DeepS DeepM : Nat → Nat → Prop) (EncS EncM : Nat → Prop)
    (lo0 hi0 lo hi : Nat) : Prop :=
  lo0 ≤ lo ∧ hi ≤ hi0
    ∧ Win lo hi
    ∧ (close hi = .seqEnd → DeepS lo hi ∧ EncS lo)
    ∧ (close hi = .mapEnd → DeepM lo hi ∧ EncM lo)
    ∧ (close hi = .seqEnd ∨ close hi = .mapEnd)

/-! ## The descend-at-guard — lift the carrier edge from unpacked halves to the packed `Guard`. -/

/-- **The descend-tail at the folded guard.**  Parametric in the close map, the guard predicates, the two
    fixed outer carriers `CarrierS`/`CarrierM`, the deferred map fact `M2`, the marker balance `Bal`, the
    separator `Sep`, and ONE abstract edge:

    * `carrierEdge` — the carrier-fed concrete descend (R532 analog): given the window, the two
      close-gated deep/enclosure HALVES, the close disjunction, the two carriers, `M2`, the frame bounds
      and the marker facts, it advances those halves to the suffix `[m+1, hi)`.  (This already has the
      content debt discharged — it asks for carriers, not content packs.)

    The lemma projects `Guard lo0 hi0 lo hi` to its six conjuncts, feeds the window/halves/close + the
    outer inputs into `carrierEdge`, and re-packs the result as `Guard lo0 hi0 (m+1) hi`.  The ONLY
    non-pass-through conjunct is the suffix frame lower bound `lo0 ≤ m+1`, re-established by `omega`. -/
theorem guard_descend_tail
    (close : Nat → Close)
    (Win DeepS DeepM CarrierS CarrierM M2 Bal : Nat → Nat → Prop)
    (EncS EncM Sep : Nat → Prop)
    (carrierEdge : ∀ lo0 hi0 lo hi m, Win lo hi →
        (close hi = .seqEnd → DeepS lo hi ∧ EncS lo) →
        (close hi = .mapEnd → DeepM lo hi ∧ EncM lo) →
        (close hi = .seqEnd ∨ close hi = .mapEnd) →
        CarrierS lo0 hi0 → CarrierM lo0 hi0 → M2 lo hi → lo0 ≤ lo → hi ≤ hi0 →
        lo < m → m < hi → Bal lo m → Sep m →
        Win (m + 1) hi
          ∧ (close hi = .seqEnd → DeepS (m + 1) hi ∧ EncS (m + 1))
          ∧ (close hi = .mapEnd → DeepM (m + 1) hi ∧ EncM (m + 1))
          ∧ (close hi = .seqEnd ∨ close hi = .mapEnd))
    (lo0 hi0 lo hi m : Nat)
    (h_seq_carrier : CarrierS lo0 hi0)
    (h_map_carrier : CarrierM lo0 hi0)
    (h_m2 : M2 lo hi)
    (h_g : Guard close Win DeepS DeepM EncS EncM lo0 hi0 lo hi)
    (h_lo_m : lo < m) (h_m_hi : m < hi)
    (h_bal_m : Bal lo m) (h_sep : Sep m) :
    Guard close Win DeepS DeepM EncS EncM lo0 hi0 (m + 1) hi := by
  unfold Guard at h_g ⊢
  obtain ⟨h_lo0, h_hi0, h_win, h_seq_guard, h_map_guard, h_close⟩ := h_g
  obtain ⟨h_win', h_seq_guard', h_map_guard', h_close'⟩ :=
    carrierEdge lo0 hi0 lo hi m h_win h_seq_guard h_map_guard h_close
      h_seq_carrier h_map_carrier h_m2 h_lo0 h_hi0 h_lo_m h_m_hi h_bal_m h_sep
  exact ⟨by omega, h_hi0, h_win', h_seq_guard', h_map_guard', h_close'⟩

/-! ## Toy instance: concrete close map, trivial guards, the abstract carrier edge discharged. -/

/-- A toy stream: position `3` is a seq close, `4` is a map close. -/
def close : Nat → Close
  | 3 => .seqEnd
  | 4 => .mapEnd
  | _ => .scalar

/-- All window/carrier guards are the monotone predicate `lo ≤ hi`; the leaf markers are `True`. -/
def W (lo hi : Nat) : Prop := lo ≤ hi
def Dp (_ _ : Nat) : Prop := True
def Car (_ _ : Nat) : Prop := True
def B (_ _ : Nat) : Prop := True
def En (_ : Nat) : Prop := True
def Sp (_ : Nat) : Prop := True
def M2t (_ _ : Nat) : Prop := True

/-- The toy carrier-fed descend edge (R532 analog): from `m < hi` the suffix window `(m+1) ≤ hi` holds;
    the deep/enclosure halves and close disjunction pass through trivially. -/
theorem edgeToy : ∀ lo0 hi0 lo hi m, W lo hi →
    (close hi = .seqEnd → Dp lo hi ∧ En lo) →
    (close hi = .mapEnd → Dp lo hi ∧ En lo) →
    (close hi = .seqEnd ∨ close hi = .mapEnd) →
    Car lo0 hi0 → Car lo0 hi0 → M2t lo hi → lo0 ≤ lo → hi ≤ hi0 →
    lo < m → m < hi → B lo m → Sp m →
    W (m + 1) hi
      ∧ (close hi = .seqEnd → Dp (m + 1) hi ∧ En (m + 1))
      ∧ (close hi = .mapEnd → Dp (m + 1) hi ∧ En (m + 1))
      ∧ (close hi = .seqEnd ∨ close hi = .mapEnd) := by
  intro _ _ _ _ m _ _ _ h_close _ _ _ _ _ _ h_m_hi _ _
  exact ⟨by unfold W; omega, fun _ => ⟨trivial, trivial⟩, fun _ => ⟨trivial, trivial⟩, h_close⟩

/-- The descend-at-guard at the toy types — one carrier-fed descend serving BOTH close tokens, lifted to
    the folded `Guard`. -/
theorem toyGuardDescend : ∀ lo0 hi0 lo hi m,
    Car lo0 hi0 → Car lo0 hi0 → M2t lo hi →
    Guard close W Dp Dp En En lo0 hi0 lo hi →
    lo < m → m < hi → B lo m → Sp m →
    Guard close W Dp Dp En En lo0 hi0 (m + 1) hi :=
  fun lo0 hi0 lo hi m h_sc h_mc h_m2 h_g h_lo_m h_m_hi h_bal h_sep =>
    guard_descend_tail close W Dp Dp Car Car M2t B En En Sp edgeToy
      lo0 hi0 lo hi m h_sc h_mc h_m2 h_g h_lo_m h_m_hi h_bal h_sep

/-! ## Both branches run: input guard at `[0, hi)` → descended suffix guard at `[m+1, hi)`. -/

/-- The SEQ descend: `hi = 3` selects `close 3 = .seqEnd`; from the guard at `[0,3)` past separator
    `m = 2`, the guard at the suffix `[3,3)` is produced. -/
example : Guard close W Dp Dp En En 0 3 3 3 :=
  toyGuardDescend 0 3 0 3 2 trivial trivial trivial
    ⟨by omega, by omega, by unfold W; omega,
      fun _ => ⟨trivial, trivial⟩, fun h => by simp [close] at h, Or.inl rfl⟩
    (by omega) (by omega) trivial trivial

/-- The MAP descend: `hi = 4` selects `close 4 = .mapEnd`; from the guard at `[0,4)` past separator
    `m = 3`, the guard at the suffix `[4,4)` is produced. -/
example : Guard close W Dp Dp En En 0 4 4 4 :=
  toyGuardDescend 0 4 0 4 3 trivial trivial trivial
    ⟨by omega, by omega, by unfold W; omega,
      fun h => by simp [close] at h, fun _ => ⟨trivial, trivial⟩, Or.inr rfl⟩
    (by omega) (by omega) trivial trivial

/-- The punchline for the axiom audit: the descend-at-guard specialised to the toy types — the full
    fold-and-lift (project the guard, call the carrier edge, re-pack), no `sorry`. -/
theorem demo : ∀ lo0 hi0 lo hi m,
    Car lo0 hi0 → Car lo0 hi0 → M2t lo hi →
    Guard close W Dp Dp En En lo0 hi0 lo hi →
    lo < m → m < hi → B lo m → Sp m →
    Guard close W Dp Dp En En lo0 hi0 (m + 1) hi := toyGuardDescend

end JointGuardDescendTail

/-- info: 'JointGuardDescendTail.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms JointGuardDescendTail.demo
