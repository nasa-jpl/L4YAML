/-
# Reflection 529 — the JOINT navigator driver: one width-recursion, a close-token-dispatched
deliverable, resolving the cross-deliverable IH knot

Self-contained companion to `recbody_joint_navigator_driver`
(`L4YAML/Proofs/Output/EmitterScannability/NonemptyStructure.lean`), the brick that unifies the two
single drivers `recseqbody_navigator_driver` / `recmapbody_navigator_driver` (Reflections 510 / 528).

Each single driver runs the width-recursion at a deliverable `P` fixed to ONE collection (`RecSeqBody`
or `RecMapBody`), so its width-oracle delivers only that one shape.  But the real recursion is
**cross-deliverable**: a map pair's key/value sub-block is one entry, and an entry whose node is a
nested *sequence* needs `RecSeqBody` while one whose node is a nested *map* needs `RecMapBody`.  A
single-collection oracle cannot supply the other shape — that is the knot.

The resolution: run ONE width-recursion at a **close-token-dispatched JOINT deliverable**

    P lo hi := (closeA hi → BodyA lo hi) ∧ (closeB hi → BodyB lo hi)

The window's close bracket selects which body it is; the conjunction carries BOTH implications, so the
oracle delivers whichever body a narrower window needs.  Each per-window step dispatches on the actual
close token, locates the first item with the matching `locate`, folds it with the matching assembler,
and draws the tail from the SAME joint oracle projected by the SAME close token.  The two single drivers
are then literally the `.1` and `.2` PROJECTIONS of this one.

This file proves the abstract `joint_navigator_driver` once — the exact dual-half stitch of the real
brick — exhibits the two single drivers as projections, instantiates at two DISTINCT body-type pairs,
and shows the cross-deliverable draw concretely: from inside the A-half a `BodyB` for a sub-window is
reachable off the joint oracle's `.2`.
-/

namespace JointNavigatorDriverCrossDeliverable

set_option autoImplicit false

/-! ## The abstract width-recursion combinator (verbatim `windowWidth_strongRecOn`). -/

/-- Strong induction on window WIDTH `hi - lo` over an abstract guard `G`. -/
theorem windowWidth_strongRecOn {P : Nat → Nat → Prop} (G : Nat → Nat → Prop)
    (step : ∀ lo hi, G lo hi →
      (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → P lo' hi') →
      P lo hi) :
    ∀ lo hi, G lo hi → P lo hi := by
  have key : ∀ n : Nat, ∀ lo hi : Nat, hi - lo ≤ n → G lo hi → P lo hi := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro lo hi h_span h_g
      exact step lo hi h_g (fun lo' hi' h_lt h_g' =>
        IH (hi' - lo') (by omega) lo' hi' (Nat.le_refl _) h_g')
  intro lo hi h_g
  exact key (hi - lo) lo hi (Nat.le_refl _) h_g

/-! ## The joint driver — one recursion, a close-keyed conjunctive deliverable. -/

/-- **The joint navigator driver.**  Parametric in the guard `G`, the two close classifiers
    `closeA`/`closeB` (each indexed by the window's close position `hi`), the two item deliverables
    `ItemA`/`ItemB`, the two body deliverables `BodyA`/`BodyB`, the separator `sep`, the two assemblers,
    the two `locate`s, and the shared `descend_tail`.  It runs ONE `windowWidth_strongRecOn` at the
    JOINT deliverable `(closeA hi → BodyA lo hi) ∧ (closeB hi → BodyB lo hi)`, dispatching each
    per-window step on the actual close token and folding with the matching assembler; the tail is drawn
    from the same joint oracle and projected by the same close token.

    The body is the two single-driver bodies run side by side under one `refine ⟨…, …⟩` — the verbatim
    stitch of `recseqbody_navigator_driver` / `recmapbody_navigator_driver`, now sharing a single
    recursion and a single oracle that delivers BOTH collection shapes. -/
theorem joint_navigator_driver
    (G : Nat → Nat → Prop) (closeA closeB : Nat → Prop)
    (ItemA ItemB BodyA BodyB : Nat → Nat → Prop) (sep : Nat → Prop)
    (assembleA : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ sep m) →
        ItemA lo m → (m < hi → BodyA (m + 1) hi) → BodyA lo hi)
    (assembleB : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ sep m) →
        ItemB lo m → (m < hi → BodyB (m + 1) hi) → BodyB lo hi)
    (locateA : ∀ lo hi, G lo hi → closeA hi →
        (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' →
          (closeA hi' → BodyA lo' hi') ∧ (closeB hi' → BodyB lo' hi')) →
        ∃ m, lo < m ∧ m ≤ hi ∧ (m = hi ∨ sep m) ∧ ItemA lo m)
    (locateB : ∀ lo hi, G lo hi → closeB hi →
        (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' →
          (closeA hi' → BodyA lo' hi') ∧ (closeB hi' → BodyB lo' hi')) →
        ∃ m, lo < m ∧ m ≤ hi ∧ (m = hi ∨ sep m) ∧ ItemB lo m)
    (descend_tail : ∀ lo hi m, G lo hi → lo < m → m < hi → sep m → G (m + 1) hi) :
    ∀ lo hi, G lo hi →
      (closeA hi → BodyA lo hi) ∧ (closeB hi → BodyB lo hi) := by
  refine windowWidth_strongRecOn G (fun lo hi h_g oracle => ?_)
  refine ⟨fun h_a => ?_, fun h_b => ?_⟩
  · obtain ⟨m, h_lo_m, h_m_hi, h_marker, h_item⟩ := locateA lo hi h_g h_a oracle
    refine assembleA lo m hi h_lo_m h_m_hi h_marker h_item (fun h_lt => ?_)
    have h_sep : sep m := h_marker.resolve_left (by omega)
    exact (oracle (m + 1) hi (by omega) (descend_tail lo hi m h_g h_lo_m h_lt h_sep)).1 h_a
  · obtain ⟨m, h_lo_m, h_m_hi, h_marker, h_item⟩ := locateB lo hi h_g h_b oracle
    refine assembleB lo m hi h_lo_m h_m_hi h_marker h_item (fun h_lt => ?_)
    have h_sep : sep m := h_marker.resolve_left (by omega)
    exact (oracle (m + 1) hi (by omega) (descend_tail lo hi m h_g h_lo_m h_lt h_sep)).2 h_b

/-! ## Toy instance: two DISTINCT body types selected by parity of the close position. -/

inductive SeqEntry : Nat → Nat → Prop where | mk (lo hi : Nat) : lo < hi → SeqEntry lo hi
inductive SeqBody  : Nat → Nat → Prop where | mk (lo hi : Nat) : lo < hi → SeqBody lo hi
inductive MapPair  : Nat → Nat → Prop where | mk (lo hi : Nat) : lo < hi → MapPair lo hi
inductive MapBody  : Nat → Nat → Prop where | mk (lo hi : Nat) : lo < hi → MapBody lo hi

/-- Shared model: a window is valid when non-empty, with no interior separators (every window is a
    single item, terminating at once).  `closeA`/`closeB` are the two close classifiers — kept as
    distinct one-arg predicates so the conjunctive deliverable genuinely has two independently-keyed
    halves (the dispatch knob).  Here both are inhabited so each projection runs. -/
def G (lo hi : Nat) : Prop := lo < hi
def sep (_ : Nat) : Prop := False
def closeA (_ : Nat) : Prop := True
def closeB (_ : Nat) : Prop := True

theorem assembleSeq : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ sep m) →
    SeqEntry lo m → (m < hi → SeqBody (m + 1) hi) → SeqBody lo hi :=
  fun lo m hi h1 h2 _ _ _ => SeqBody.mk lo hi (by omega)

theorem assembleMap : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ sep m) →
    MapPair lo m → (m < hi → MapBody (m + 1) hi) → MapBody lo hi :=
  fun lo m hi h1 h2 _ _ _ => MapBody.mk lo hi (by omega)

theorem locateSeq : ∀ lo hi, G lo hi → closeA hi →
    (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' →
      (closeA hi' → SeqBody lo' hi') ∧ (closeB hi' → MapBody lo' hi')) →
    ∃ m, lo < m ∧ m ≤ hi ∧ (m = hi ∨ sep m) ∧ SeqEntry lo m :=
  fun lo hi h_g _ _ => ⟨hi, h_g, Nat.le_refl _, Or.inl rfl, SeqEntry.mk lo hi h_g⟩

theorem locateMap : ∀ lo hi, G lo hi → closeB hi →
    (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' →
      (closeA hi' → SeqBody lo' hi') ∧ (closeB hi' → MapBody lo' hi')) →
    ∃ m, lo < m ∧ m ≤ hi ∧ (m = hi ∨ sep m) ∧ MapPair lo m :=
  fun lo hi h_g _ _ => ⟨hi, h_g, Nat.le_refl _, Or.inl rfl, MapPair.mk lo hi h_g⟩

theorem descend_tail : ∀ lo hi m, G lo hi → lo < m → m < hi → sep m → G (m + 1) hi :=
  fun _ _ _ _ _ _ h_sep => h_sep.elim

/-- **The joint driver at the toy types** — one recursion producing the conjunctive deliverable. -/
theorem jointNav : ∀ lo hi, G lo hi →
    (closeA hi → SeqBody lo hi) ∧ (closeB hi → MapBody lo hi) :=
  joint_navigator_driver G closeA closeB SeqEntry MapPair SeqBody MapBody sep
    assembleSeq assembleMap locateSeq locateMap descend_tail

/-! ## Both single drivers are PROJECTIONS of the one joint driver. -/

/-- The seq body producer — the `.1` projection (windows that close as `closeA`). -/
theorem seqDriver : ∀ lo hi, G lo hi → closeA hi → SeqBody lo hi :=
  fun lo hi h_g => (jointNav lo hi h_g).1

/-- The map body producer — the `.2` projection (windows that close as `closeB`). -/
theorem mapDriver : ∀ lo hi, G lo hi → closeB hi → MapBody lo hi :=
  fun lo hi h_g => (jointNav lo hi h_g).2

/-! ## The cross-deliverable draw, concretely. -/

/-- The point of the conjunctive oracle: while PRODUCING a `SeqBody`, the OTHER body `MapBody` for a
    narrower window is reachable off the joint oracle's `.2`.  This is the draw a single-collection
    oracle cannot make — here exhibited as a closed term over an arbitrary joint oracle. -/
theorem cross_draw_reachable
    (oracle : ∀ lo' hi', G lo' hi' → (closeA hi' → SeqBody lo' hi') ∧ (closeB hi' → MapBody lo' hi'))
    (lo' hi' : Nat) (h_g' : G lo' hi') (h_b : closeB hi') : MapBody lo' hi' :=
  (oracle lo' hi' h_g').2 h_b

/-! ## Concrete runs. -/

example : SeqBody 0 5 := seqDriver 0 5 (by unfold G; omega) True.intro
example : MapBody 0 5 := mapDriver 0 5 (by unfold G; omega) True.intro

/-- The punchline term for the axiom audit: the seq body producer built entirely from the abstract
    joint stitch plus the toy locate/descend/assemble — no `sorry`, no classical choice. -/
theorem demo : ∀ lo hi, G lo hi → closeA hi → SeqBody lo hi := seqDriver

end JointNavigatorDriverCrossDeliverable

/-- info: 'JointNavigatorDriverCrossDeliverable.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms JointNavigatorDriverCrossDeliverable.demo
