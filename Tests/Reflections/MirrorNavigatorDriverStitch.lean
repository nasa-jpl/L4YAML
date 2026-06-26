/-
# Reflection 528 — the navigator-driver STITCH reduces a body-recursion to two obligations,
making the second collection axis a verbatim mirror

Self-contained companion to `recmapbody_navigator_driver`
(`L4YAML/Proofs/Output/EmitterScannability/NonemptyStructure.lean`), the map mirror of
`recseqbody_navigator_driver`.

A body-recursion navigator over windows `[lo, hi)` has three moving parts that are already proven
separately: a width-recursion combinator (strong induction on `hi - lo`), a window ASSEMBLER that, given
the first item plus the recursion's tail oracle, folds them into the whole-window deliverable, and the
per-window analytical work (locate the first item, descend the guard past its trailing separator).  The
*driver* is the **stitch** that wires the three together — and the reflection is that once stitched, the
entire navigator reduces to exactly **two abstract obligations**:

* `locate` — find the first item's extent `m`, its marker (`m = hi` or a separator at `m`), and the
  single-item deliverable `Item lo m`;
* `descend_tail` — descend the guard `G` from `[lo, hi)` to the suffix `[m+1, hi)` past the separator.

Everything else — the strong-recursion plumbing, the marker-disjunct collapse, the ADVANCE/TERMINATE
selection — is collection-agnostic.  The body/entry deliverable TYPES (and their assembler) are the
*sole* collection-specific knobs, so the parallel axis (map, given seq) is a verbatim mirror: a one-line
specialization of the same abstract driver.

This file proves the abstract `navigator_driver` once — the exact marker-disjunct + strong-rec stitch of
both real drivers — then instantiates it at two DISTINCT deliverable-type triples (`SeqEntry`/`SeqBody`
and `MapPair`/`MapBody`) to exhibit the mirror, and runs each on a concrete single-item window.
-/

namespace MirrorNavigatorDriverStitch

set_option autoImplicit false

/-! ## The abstract width-recursion combinator (verbatim `windowWidth_strongRecOn`). -/

/-- Strong induction on window WIDTH `hi - lo` over an abstract guard `G`: the per-window step gets an
    oracle for every strictly-narrower sub-window.  The reusable plumbing both real drivers pivot on. -/
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

/-! ## The driver STITCH — abstract in the deliverable types. -/

/-- **The navigator driver.**  Parametric in the guard `G`, the per-entry deliverable `Item`, the body
    deliverable `Body`, the separator predicate `sep`, and the `assemble` selector — and the analytical
    `locate` / `descend_tail`.  The body is the verbatim stitch of `recseqbody_navigator_driver` and
    `recmapbody_navigator_driver`: refine through the width combinator, locate the first item, hand the
    located pair to the assembler, and on ADVANCE (`m < hi`) feed the oracle the descended guard.

    The marker-disjunct collapse (`resolve_left (by omega)`) is the same on both axes; the ONLY
    collection-specific data is `Item`/`Body`/`assemble`.  So the second axis is this same theorem at a
    different type triple — the mirror is a specialization, not a re-proof. -/
theorem navigator_driver
    (G Item Body : Nat → Nat → Prop) (sep : Nat → Prop)
    (assemble : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ sep m) →
        Item lo m → (m < hi → Body (m + 1) hi) → Body lo hi)
    (locate : ∀ lo hi, G lo hi →
        (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → Body lo' hi') →
        ∃ m, lo < m ∧ m ≤ hi ∧ (m = hi ∨ sep m) ∧ Item lo m)
    (descend_tail : ∀ lo hi m, G lo hi → lo < m → m < hi → sep m → G (m + 1) hi) :
    ∀ lo hi, G lo hi → Body lo hi := by
  refine windowWidth_strongRecOn G (fun lo hi h_g oracle => ?_)
  obtain ⟨m, h_lo_m, h_m_hi, h_marker, h_item⟩ := locate lo hi h_g oracle
  refine assemble lo m hi h_lo_m h_m_hi h_marker h_item (fun h_lt => ?_)
  have h_sep : sep m := h_marker.resolve_left (by omega)
  exact oracle (m + 1) hi (by omega) (descend_tail lo hi m h_g h_lo_m h_lt h_sep)

/-! ## The mirror: two DISTINCT deliverable types, one driver. -/

/-- Toy seq-side deliverables — a single entry and a body, kept as distinct one-field wrappers so the
    two axes have genuinely different types (the mirror's sole knob). -/
inductive SeqEntry : Nat → Nat → Prop where | mk (lo hi : Nat) : lo < hi → SeqEntry lo hi
inductive SeqBody  : Nat → Nat → Prop where | mk (lo hi : Nat) : lo < hi → SeqBody lo hi

/-- Toy map-side deliverables — the parallel pair/body, structurally identical, nominally distinct. -/
inductive MapPair : Nat → Nat → Prop where | mk (lo hi : Nat) : lo < hi → MapPair lo hi
inductive MapBody : Nat → Nat → Prop where | mk (lo hi : Nat) : lo < hi → MapBody lo hi

/-- Shared model: a window is valid when non-empty (`lo < hi`), and there are no interior separators
    (`sep := fun _ => False`) — so every window is a single item and the navigator TERMINATEs at once.
    This isolates the stitch shape from the separator analysis (covered by Reflection 527). -/
def G (lo hi : Nat) : Prop := lo < hi
def sep (_ : Nat) : Prop := False

/-- `locate` for the seq axis: the first (and only) item is the whole window, ending at `m = hi`. -/
theorem locate_seq : ∀ lo hi, G lo hi →
    (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → SeqBody lo' hi') →
    ∃ m, lo < m ∧ m ≤ hi ∧ (m = hi ∨ sep m) ∧ SeqEntry lo m :=
  fun lo hi h_g _ => ⟨hi, h_g, Nat.le_refl _, Or.inl rfl, SeqEntry.mk lo hi h_g⟩

/-- `locate` for the map axis: same shape, `MapPair` for `SeqEntry`. -/
theorem locate_map : ∀ lo hi, G lo hi →
    (∀ lo' hi', hi' - lo' < hi - lo → G lo' hi' → MapBody lo' hi') →
    ∃ m, lo < m ∧ m ≤ hi ∧ (m = hi ∨ sep m) ∧ MapPair lo m :=
  fun lo hi h_g _ => ⟨hi, h_g, Nat.le_refl _, Or.inl rfl, MapPair.mk lo hi h_g⟩

/-- `descend_tail` is shared and vacuous here: there are no separators, so the `sep m` premise is
    `False`.  (In the real drivers this is the genuine guard-threading brick — collection-agnostic
    because the separator token `.flowEntry` is the same for both kinds.) -/
theorem descend_tail : ∀ lo hi m, G lo hi → lo < m → m < hi → sep m → G (m + 1) hi :=
  fun _ _ _ _ _ _ h_sep => h_sep.elim

theorem assemble_seq : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ sep m) →
    SeqEntry lo m → (m < hi → SeqBody (m + 1) hi) → SeqBody lo hi :=
  fun lo m hi h1 h2 _ _ _ => SeqBody.mk lo hi (by omega)

theorem assemble_map : ∀ lo m hi, lo < m → m ≤ hi → (m = hi ∨ sep m) →
    MapPair lo m → (m < hi → MapBody (m + 1) hi) → MapBody lo hi :=
  fun lo m hi h1 h2 _ _ _ => MapBody.mk lo hi (by omega)

/-- **Seq navigator** — the abstract driver at the seq type triple.  One line. -/
theorem seqNav : ∀ lo hi, G lo hi → SeqBody lo hi :=
  navigator_driver G SeqEntry SeqBody sep assemble_seq locate_seq descend_tail

/-- **Map navigator** — the SAME driver at the map type triple.  The mirror is a pure swap of
    `MapPair`/`MapBody`/`assemble_map`/`locate_map` for their seq counterparts; `G`, `sep`,
    `descend_tail`, and the entire driver proof are shared. -/
theorem mapNav : ∀ lo hi, G lo hi → MapBody lo hi :=
  navigator_driver G MapPair MapBody sep assemble_map locate_map descend_tail

/-! ## Concrete runs. -/

example : SeqBody 0 5 := seqNav 0 5 (by unfold G; omega)
example : MapBody 0 5 := mapNav 0 5 (by unfold G; omega)

/-- The punchline term for the axiom audit: the seq navigator built entirely from the abstract stitch
    plus the toy locate/descend/assemble — no `sorry`, no classical choice. -/
theorem demo : ∀ lo hi, G lo hi → SeqBody lo hi := seqNav

end MirrorNavigatorDriverStitch

/-- info: 'MirrorNavigatorDriverStitch.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MirrorNavigatorDriverStitch.demo
