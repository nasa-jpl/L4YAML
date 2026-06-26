/-
# Reflection 530 — the JOINT descend-tail: two collection-specific guard advances folded into ONE
descend by close-token dispatch, with the carrier debts exposed as explicit inputs

Self-contained companion to `recbody_joint_descend_tail`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the `descend_tail` companion
of the joint navigator driver `recbody_joint_navigator_driver` (Reflection 529).

A width-recursion navigator's `descend_tail` narrows the per-window guard from `[lo, hi)` to the
suffix `[m+1, hi)` past a depth-`0` separator.  The seq and map navigators each had their own edge
(`recseqbody_seq_descend_tail` / `recmapbody_map_descend_tail`), each producing one collection's
guard.  The JOINT driver runs at a close-token-dispatched conjunctive deliverable, so it needs ONE
`descend_tail` that advances WHICHEVER guard the window's close token selects.

The resolution: dispatch the descend on the window close token.  `rcases` the close disjunction; in
each branch unpack the matching content pack, call the matching single edge, and reassemble the
conjunctive guard.  Two structural points this file isolates:

* **Reproduced vs consumed.**  The descend REPRODUCES the shared window guard + the close-dispatched
  deep-content/enclosure pair — those advance.  But each single edge also CONSUMES a top-down content
  provider (`FlowBodyContent` / `MapBodyProps`) and the located separator's depth-`0` balance, which
  the recursion cannot thread top-down and cannot reproduce at the suffix.  Those appear as EXPLICIT
  hypotheses (here `PackS`/`PackM` and `h_lo_m`/`h_m_hi`), the visible carrier debt.

* **Vacuous off-branch.**  The conjunctive goal carries BOTH close-keyed implications.  In the seq
  branch the map implication's premise (`close hi = mapEnd`) contradicts `close hi = seqEnd`, so it is
  discharged for ANY goal by discriminator disjointness (`by decide` on the constructor equality), and
  symmetrically.

This file models the discriminator as a two-valued close token and the guards as abstract predicates,
proves the exact dual-branch dispatch of the real edge, then instantiates and runs both branches.
-/

namespace JointDescendTailDispatch

set_option autoImplicit false

/-- The window close token — the dispatch discriminator (toy stand-in for `YamlToken`'s
    `.flowSequenceEnd` / `.flowMappingEnd`). -/
inductive Close where
  | seqEnd
  | mapEnd
  | scalar
  deriving DecidableEq

/-! ## The abstract joint descend — one descend, two close-keyed halves. -/

/-- **The joint descend-tail dispatcher.**  Parametric in the close-token map `close`, the shared
    window guard `Win`, the two deep-content guards `DeepS`/`DeepM`, the two enclosure guards
    `EncS`/`EncM`, the two consumed-but-not-reproduced content packs `PackS`/`PackM`, and the two
    collection-specific advance edges.  Given the shared window guard, the close disjunction, and the
    close-gated content packs, it produces the conjunctive guard at the suffix `[m+1, hi)`.

    This is the exact shape of `recbody_joint_descend_tail`: the reproduced conjuncts (`Win` + the two
    close-keyed deep/enclosure implications + the close disjunction) advance via the matching edge; the
    off-branch implication is discharged vacuously by `Close` disjointness. -/
theorem joint_descend_dispatch
    (close : Nat → Close)
    (Win DeepS DeepM : Nat → Nat → Prop)
    (EncS EncM : Nat → Prop)
    (PackS PackM : Nat → Nat → Prop)
    (advanceS : ∀ lo hi m, Win lo hi → DeepS lo hi → EncS lo → PackS lo hi →
        close hi = .seqEnd → lo < m → m < hi →
        Win (m + 1) hi ∧ DeepS (m + 1) hi ∧ EncS (m + 1))
    (advanceM : ∀ lo hi m, Win lo hi → DeepM lo hi → EncM lo → PackM lo hi →
        close hi = .mapEnd → lo < m → m < hi →
        Win (m + 1) hi ∧ DeepM (m + 1) hi ∧ EncM (m + 1))
    (lo hi m : Nat)
    (h_win : Win lo hi)
    (h_close : close hi = .seqEnd ∨ close hi = .mapEnd)
    (h_seq_pack : close hi = .seqEnd → DeepS lo hi ∧ EncS lo ∧ PackS lo hi)
    (h_map_pack : close hi = .mapEnd → DeepM lo hi ∧ EncM lo ∧ PackM lo hi)
    (h_lo_m : lo < m) (h_m_hi : m < hi) :
    Win (m + 1) hi
      ∧ (close hi = .seqEnd → DeepS (m + 1) hi ∧ EncS (m + 1))
      ∧ (close hi = .mapEnd → DeepM (m + 1) hi ∧ EncM (m + 1))
      ∧ (close hi = .seqEnd ∨ close hi = .mapEnd) := by
  rcases h_close with h_s | h_m
  · obtain ⟨h_deep, h_enc, h_pack⟩ := h_seq_pack h_s
    obtain ⟨h_win', h_deep', h_enc'⟩ := advanceS lo hi m h_win h_deep h_enc h_pack h_s h_lo_m h_m_hi
    exact ⟨h_win', fun _ => ⟨h_deep', h_enc'⟩,
      fun h_m => absurd (h_m.symm.trans h_s) (by decide), Or.inl h_s⟩
  · obtain ⟨h_deep, h_enc, h_pack⟩ := h_map_pack h_m
    obtain ⟨h_win', h_deep', h_enc'⟩ := advanceM lo hi m h_win h_deep h_enc h_pack h_m h_lo_m h_m_hi
    exact ⟨h_win', fun h_s => absurd (h_s.symm.trans h_m) (by decide),
      fun _ => ⟨h_deep', h_enc'⟩, Or.inr h_m⟩

/-! ## Toy instance: a concrete close-token map and trivial guards, exercising both branches. -/

/-- A toy stream: positions `0,1,2` are scalars, `3` is a seq close, `4` is a map close.  Drives the
    dispatch onto each branch by varying `hi`. -/
def close : Nat → Close
  | 3 => .seqEnd
  | 4 => .mapEnd
  | _ => .scalar

/-- All guards are the trivial monotone window predicate `lo ≤ hi`, so both advance edges are provable
    (the real edge re-establishes `m + 1 < hi` from the window's CONTENT — a no-trailing-separator
    argument — which this toy abstracts away; it exercises the DISPATCH and the vacuous off-branch, not
    the guards' content). -/
def W (lo hi : Nat) : Prop := lo ≤ hi
def Pk (_ _ : Nat) : Prop := True
def E (_ : Nat) : Prop := True

theorem advW : ∀ lo hi m, W lo hi → W lo hi → E lo → Pk lo hi →
    close hi = .seqEnd → lo < m → m < hi → W (m + 1) hi ∧ W (m + 1) hi ∧ E (m + 1) :=
  fun _ hi m _ _ _ _ _ _ h => ⟨by unfold W; omega, by unfold W; omega, trivial⟩

theorem advM : ∀ lo hi m, W lo hi → W lo hi → E lo → Pk lo hi →
    close hi = .mapEnd → lo < m → m < hi → W (m + 1) hi ∧ W (m + 1) hi ∧ E (m + 1) :=
  fun _ hi m _ _ _ _ _ _ h => ⟨by unfold W; omega, by unfold W; omega, trivial⟩

/-- The dispatcher at the toy types — one descend serving BOTH close tokens. -/
theorem toyDescend : ∀ lo hi m, W lo hi →
    (close hi = .seqEnd ∨ close hi = .mapEnd) →
    (close hi = .seqEnd → W lo hi ∧ E lo ∧ Pk lo hi) →
    (close hi = .mapEnd → W lo hi ∧ E lo ∧ Pk lo hi) →
    lo < m → m < hi →
    W (m + 1) hi
      ∧ (close hi = .seqEnd → W (m + 1) hi ∧ E (m + 1))
      ∧ (close hi = .mapEnd → W (m + 1) hi ∧ E (m + 1))
      ∧ (close hi = .seqEnd ∨ close hi = .mapEnd) :=
  fun lo hi m h_win h_close h_sp h_mp h1 h2 =>
    joint_descend_dispatch close W W W E E Pk Pk advW advM lo hi m h_win h_close h_sp h_mp h1 h2

/-! ## Both branches run. -/

/-- The SEQ branch: `hi = 3` selects `close 3 = .seqEnd`; the seq advance fires (`m = 1`, so the suffix
    starts at `m + 1 = 2`), the map implication is discharged vacuously. -/
example : W 2 3 ∧ (close 3 = .seqEnd → W 2 3 ∧ E 2) ∧ (close 3 = .mapEnd → W 2 3 ∧ E 2)
    ∧ (close 3 = .seqEnd ∨ close 3 = .mapEnd) :=
  toyDescend 0 3 1 (by unfold W; omega) (Or.inl rfl)
    (fun _ => ⟨by unfold W; omega, trivial, trivial⟩)
    (fun h => by simp [close] at h)
    (by omega) (by omega)

/-- The MAP branch: `hi = 4` selects `close 4 = .mapEnd`; the map advance fires (suffix at `m + 1 = 2`),
    the seq implication is discharged vacuously. -/
example : W 2 4 ∧ (close 4 = .seqEnd → W 2 4 ∧ E 2) ∧ (close 4 = .mapEnd → W 2 4 ∧ E 2)
    ∧ (close 4 = .seqEnd ∨ close 4 = .mapEnd) :=
  toyDescend 0 4 1 (by unfold W; omega) (Or.inr rfl)
    (fun h => by simp [close] at h)
    (fun _ => ⟨by unfold W; omega, trivial, trivial⟩)
    (by omega) (by omega)

/-- The punchline for the axiom audit: the joint descend dispatcher specialised to the toy types — the
    full dual-branch dispatch with vacuous off-branch, no `sorry`. -/
theorem demo : ∀ lo hi m, W lo hi →
    (close hi = .seqEnd ∨ close hi = .mapEnd) →
    (close hi = .seqEnd → W lo hi ∧ E lo ∧ Pk lo hi) →
    (close hi = .mapEnd → W lo hi ∧ E lo ∧ Pk lo hi) →
    lo < m → m < hi →
    W (m + 1) hi
      ∧ (close hi = .seqEnd → W (m + 1) hi ∧ E (m + 1))
      ∧ (close hi = .mapEnd → W (m + 1) hi ∧ E (m + 1))
      ∧ (close hi = .seqEnd ∨ close hi = .mapEnd) := toyDescend

end JointDescendTailDispatch

/-- info: 'JointDescendTailDispatch.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms JointDescendTailDispatch.demo
