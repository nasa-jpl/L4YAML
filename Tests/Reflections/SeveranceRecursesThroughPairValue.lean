/-!
# Reflection 460 — the token-indistinguishable map severance is NOT eliminated by bridging to the
# severance-free `RecMapEntry`/`RecMapBody`; it RE-SURFACES one level deeper, at every `RecMapPair`'s
# bare-`RecSeqEntry` VALUE field.  So the recursive map navigator faces the undischargeable flat-`.map`
# `cases` at every map-value-that-is-itself-a-map — the recursion must be threaded by the producer at
# EACH value, not just at the located top entry; the fix is a parallel family whose value field carries
# the recursion.

Self-contained (core Lean, no `L4YAML` import) toy executing the PROBE that STEP D step 5 front-loads.

R459 found the seq→map severance and resolved the *top* entry by bridging a located map `RecSeqEntry`
into the severance-free `RecMapEntry` (`RecSeqEntry.toRecMapEntry`), whose own descent
`RecMapEntry.map_interior` is debt-free.  Step 5 plans the recursive map NAVIGATOR over `RecMapBody`.
PROBING where a map-value-that-is-itself-a-map is reached (the `MapPathLocatorMoveProbe` M3
`[{a:{x:[b]}}]` DESCEND-VALUE step) shows it arrives as the **bare value field** of a `RecMapPair`:

    RecMapBody  →  RecMapPair.mk … (h_ve : RecSeqEntry block_v) …  →  block_v a bare RecSeqEntry

`RecMapEntry`/`RecMapBody` is severance-free only at the entry / body / pair-LIST spine.  Its pairs
(`RecMapPair`) store the value (and key) as a **bare `RecSeqEntry`** — exactly the type with the flat
`.map` / recursive `.mapRec` token-indistinguishability R459 isolated.  So to recurse into a value that
is itself a map, the navigator must `cases` that bare `RecSeqEntry`, hitting the undischargeable flat
`.map` branch again.  **The severance is recursive: it bites at every map-value-that-is-a-map boundary,
not just the located top entry the R459 bridge cleaned.**  A navigator descending `RecMapBody` therefore
cannot recurse into nested-map values from the deliverable alone — the per-value recursive body is the
producer's debt at every level.

The toy mirrors it with a 5-token alphabet and a `Entry`/`Pair`/`MBody` mutual group (`Pair`'s value is a
bare `Entry`, `Entry` carries the flat `mapFlat` severance), a severance-free `MEntry` (entry-level descent
clean), and a PARALLEL deep family `DEntry`/`DPair`/`DBody` whose `DPair` value is a `DEntry` *without* the
flat severance:

* `MEntry.map_interior` — entry-level descent is DEBT-FREE (the R459 "severance-free" claim, at the entry).
* `Pair.value` — descending a pair yields its value as a BARE `Entry` (where the severance lives).
* `pair_value_severance_is_real` — a `Pair` whose value is a flat `mapFlat` exists, yet its inner `MBody`
  is provably not recoverable: the severance R459 found at the top entry recurs INSIDE a `MBody`.
* `DPair.value_map_descent` — in the parallel family the value field is a severance-free `DEntry`, so a
  map-valued pair descends into its inner `DBody` with NO producer debt — the fix.
* `deep_value_descent_clean_no_debt` — a concrete depth-2 nested map `{k:{k:a}}` whose value boundary
  descends with no debt at either level (the descent the `Entry`/`Pair` family cannot do unthreaded).
* `toDEntry` — the producer bridge: it threads the DEEP body (`DBody`, not the flat severance) into the
  value field; the recursion comes from the producer at every value.
* `severance_recurses_through_pair_value` — the finding in one proposition.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.SeveranceRecursesThroughPairValue

/-- Toy alphabet: `a` content, `mop`/`mcl` map brackets, `k` the `.key` marker, `fe` the `.flowEntry`
    pair separator. -/
inductive Tok where
  | a | mop | mcl | k | fe
deriving DecidableEq

/-- Append-singleton injectivity (core Lean, the same lemma the real descents use). -/
theorem append_singleton_inj {a b : List Tok} {x y : Tok}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hr
  injection hr with hxy har
  exact ⟨List.reverse_inj.mp har, hxy⟩

/-- The WEAK bracket fact the flat severance stores (mirror `WellBracketed`): trivially true of ANY
    interior — which is exactly what lets the flat `.map` carry a non-`MBody` interior. -/
def WB (_l : List Tok) : Prop := True

/-! ## The severance-prone family — mirror `RecSeqEntry` / `RecMapPair` / `RecMapBody`.

`Entry` carries BOTH a flat severance (`mapFlat`, stores only `WB`) and the recursive `mapRec` (stores
`MBody`) — token-indistinguishable, same `mop :: interior ++ [mcl]`.  Crucially `Pair`'s VALUE field is a
**bare `Entry`** (mirror `RecMapPair`'s `h_ve : RecSeqEntry block_v`), so the severance recurs at the
value boundary.  `MBody` is the pair-list spine (`single`/`cons`). -/
mutual
  inductive Entry : List Tok → Prop where
    | scalar : Entry [Tok.a]
    | mapFlat (interior : List Tok) (hwb : WB interior) :
        Entry (Tok.mop :: (interior ++ [Tok.mcl]))
    | mapRec (interior : List Tok) (hwb : WB interior) (h : MBody interior) :
        Entry (Tok.mop :: (interior ++ [Tok.mcl]))
  inductive Pair : List Tok → Prop where
    | mk (val : List Tok) (h_v : Entry val) : Pair (Tok.k :: val)
  inductive MBody : List Tok → Prop where
    | single (p : List Tok) (h_p : Pair p) : MBody p
    | cons (p rest : List Tok) (h_p : Pair p) (h_rest : MBody rest) :
        MBody (p ++ Tok.fe :: rest)
end

/-- The severance-free recursive map entry (mirror `RecMapEntry`): only `mapEmpty` and a `map` that
    STORES `MBody`.  No flat constructor ⇒ its own entry-level descent is debt-free. -/
inductive MEntry : List Tok → Prop where
  | mapEmpty : MEntry (Tok.mop :: ([] ++ [Tok.mcl]))
  | map (interior : List Tok) (h : MBody interior) :
      MEntry (Tok.mop :: (interior ++ [Tok.mcl]))

/-- **`MEntry` descent — DEBT-FREE at the ENTRY level** (mirror `RecMapEntry.map_interior`).  This is
    the R459 "severance-free" property — but it is *shallow*: it cleans the located top entry only. -/
theorem MEntry.map_interior {e interior : List Tok}
    (h : MEntry e) (h_eq : e = Tok.mop :: (interior ++ [Tok.mcl])) :
    MBody interior ∨ interior = [] := by
  cases h with
  | mapEmpty =>
      right; injection h_eq with _h1 h2; simp only [List.nil_append] at h2
      exact (append_singleton_inj h2.symm).1
  | map interior' h =>
      left; injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h

/-- **Descending a pair yields its value as a BARE `Entry`** (mirror reading `RecMapPair`'s
    `h_ve : RecSeqEntry block_v`).  `Pair` has the single `mk` constructor, so this is a clean `cases` —
    but what it hands back is a bare `Entry`, where the flat/recursive severance lives. -/
theorem Pair.value {p val : List Tok} (h : Pair p) (h_eq : p = Tok.k :: val) : Entry val := by
  cases h with
  | mk val' h_v => injection h_eq with _h1 h2; exact h2 ▸ h_v

/-- Every `Pair` begins with the `.key` marker. -/
theorem Pair.head?_key {p : List Tok} (h : Pair p) : p.head? = some Tok.k := by
  cases h with | mk val h_v => rfl

/-- Every `MBody` begins with the `.key` marker (structural, both spine constructors). -/
theorem MBody.head?_key : {l : List Tok} → MBody l → l.head? = some Tok.k
  | _, .single p h_p => Pair.head?_key h_p
  | _, .cons p rest h_p h_rest => by
      have hp := Pair.head?_key h_p
      cases p with
      | nil => simp at hp
      | cons hd tl =>
          simp only [List.cons_append, List.head?_cons] at hp ⊢
          exact hp

/-- `[mcl]` (a flat `mapFlat`'s interior) is provably not an `MBody`: an `MBody` starts with `.key`. -/
theorem not_mbody_mcl : ¬ MBody [Tok.mcl] := fun h => absurd (MBody.head?_key h) (by decide)

/-- **The severance RECURSES — the gap is real one level deeper.**  A `Pair` whose VALUE is a flat
    `mapFlat` entry (interior `[mcl]`, trivially `WB`) exists, yet that interior is provably NOT a
    recoverable `MBody`.  So the navigator, after the R459 bridge cleaned the top entry and descended to
    this `MBody`, reaches a value that is itself a map and CANNOT recover its inner body from the bare
    `Entry` — the exact severance R459 found, now INSIDE a `RecMapBody`.  (On the emit feed the producer
    builds `mapRec` for non-empty map values; this off-feed inhabitant exists only because `Pair`'s value
    type admits the severance — which is why the navigator cannot rule it out from the bare type.) -/
theorem pair_value_severance_is_real :
    Pair (Tok.k :: (Tok.mop :: ([Tok.mcl] ++ [Tok.mcl])))
    ∧ ¬ (MBody [Tok.mcl] ∨ [Tok.mcl] = []) := by
  refine ⟨Pair.mk _ (Entry.mapFlat [Tok.mcl] trivial), ?_⟩
  rintro (hb | he)
  · exact not_mbody_mcl hb
  · simp at he

/-! ## The fix — a PARALLEL deep family whose VALUE field carries the recursion (severance-free).

`DEntry` has no flat constructor (`scalar`/`mapEmpty`/`map`-with-`DBody` only), and `DPair`'s value is a
`DEntry` — so descending a map-valued pair into its inner body is a plain `cases`, NO producer debt.  This
is the structural shape the recursive map navigator needs end-to-end: the producer threads `toDEntry` at
every map value (not just the top entry), so the navigator only ever descends severance-free types. -/
mutual
  inductive DEntry : List Tok → Prop where
    | scalar : DEntry [Tok.a]
    | mapEmpty : DEntry (Tok.mop :: ([] ++ [Tok.mcl]))
    | map (interior : List Tok) (h : DBody interior) :
        DEntry (Tok.mop :: (interior ++ [Tok.mcl]))
  inductive DPair : List Tok → Prop where
    | mk (val : List Tok) (h_v : DEntry val) : DPair (Tok.k :: val)
  inductive DBody : List Tok → Prop where
    | single (p : List Tok) (h_p : DPair p) : DBody p
    | cons (p rest : List Tok) (h_p : DPair p) (h_rest : DBody rest) :
        DBody (p ++ Tok.fe :: rest)
end

/-- `DEntry` entry-level descent — debt-free (no flat severance to block it). -/
theorem DEntry.map_interior {e interior : List Tok}
    (h : DEntry e) (h_eq : e = Tok.mop :: (interior ++ [Tok.mcl])) :
    DBody interior ∨ interior = [] := by
  cases h with
  | scalar => injection h_eq with h1 _h2; exact absurd h1 (by decide)
  | mapEmpty =>
      right; injection h_eq with _h1 h2; simp only [List.nil_append] at h2
      exact (append_singleton_inj h2.symm).1
  | map interior' h =>
      left; injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h

/-- Descend a `DPair` to its value `DEntry` (clean `cases`). -/
theorem DPair.value {p val : List Tok} (h : DPair p) (h_eq : p = Tok.k :: val) : DEntry val := by
  cases h with
  | mk val' h_v => injection h_eq with _h1 h2; exact h2 ▸ h_v

/-- **The value boundary descends with NO debt in the deep family.**  A map-valued `DPair`'s value is a
    severance-free `DEntry`, so descending into its inner `DBody` is `DPair.value` then the debt-free
    `DEntry.map_interior` — the navigator recurses into a nested-map value WITHOUT any producer debt.
    This is exactly what the severance-prone `Pair`/`Entry` family cannot do (`pair_value_severance_is_real`):
    there the value is a bare `Entry` whose inner body must be threaded from the producer at this level. -/
theorem DPair.value_map_descent {p val interior : List Tok}
    (h : DPair p) (h_eq : p = Tok.k :: val) (h_val : val = Tok.mop :: (interior ++ [Tok.mcl])) :
    DBody interior ∨ interior = [] :=
  DEntry.map_interior (DPair.value h h_eq) h_val

/-- **Depth-2 nested map `{ k : { k : a } }`, descended through both value boundaries with NO debt.**
    The outer map's body head pair's value is itself a map; the inner map's body head pair's value is the
    scalar.  Both value-boundary descents are debt-free (`DEntry`/`DPair` carry no flat severance), so the
    navigator reaches the innermost body recursing through severance-free types only. -/
theorem deep_value_descent_clean_no_debt :
    -- the constructed depth-2 outer entry inhabits the deep family ...
    DEntry (Tok.mop :: ([Tok.k, Tok.mop, Tok.k, Tok.a, Tok.mcl] ++ [Tok.mcl]))
    -- ... its body's head pair (value = the inner map) descends with no debt ...
    ∧ (DBody [Tok.k, Tok.a] ∨ ([Tok.k, Tok.a] : List Tok) = [])
    -- ... and the inner map's body's head pair (value = scalar) bottoms out cleanly.
    ∧ DBody [Tok.k, Tok.a] := by
  -- inner: pair `k :: scalar`, body `[k, a]`.
  have h_inner_pair : DPair [Tok.k, Tok.a] := DPair.mk [Tok.a] DEntry.scalar
  have h_inner_body : DBody [Tok.k, Tok.a] := DBody.single _ h_inner_pair
  -- level-1 value: the inner map `{ k : a }`.
  have h_lvl1 : DEntry (Tok.mop :: ([Tok.k, Tok.a] ++ [Tok.mcl])) :=
    DEntry.map _ h_inner_body
  -- level-1 pair `k :: (inner map)`, its body, then the outer map `{ k : { k : a } }`.
  have h_pair2 : DPair [Tok.k, Tok.mop, Tok.k, Tok.a, Tok.mcl] := DPair.mk _ h_lvl1
  have h_body2 : DBody [Tok.k, Tok.mop, Tok.k, Tok.a, Tok.mcl] := DBody.single _ h_pair2
  refine ⟨DEntry.map _ h_body2, ?_, h_inner_body⟩
  -- the outer body's head pair's value (`= the inner map`) descends with NO debt:
  exact DPair.value_map_descent h_pair2 rfl rfl

/-- **The producer bridge threads the DEEP body** (mirror `RecSeqEntry.toRecMapEntry`, but with the body
    now a recursive `DBody`, not the flat `WB`).  Given a bare map-headed `Entry` and the producer's
    *deep* body debt `h_deep` (the recursion the producer holds at build time), package into the
    severance-free `DEntry` the navigator descends.  `h` (the bare entry) is carried, never destructured —
    the recursion comes from the producer, threaded through the type at THIS value, not recovered from the
    bare `Entry`.  At a nested map value the producer applies this again, recursively. -/
theorem toDEntry {e interior : List Tok}
    (_h : Entry e) (h_eq : e = Tok.mop :: (interior ++ [Tok.mcl]))
    (h_deep : DBody interior ∨ interior = []) :
    DEntry e := by
  subst h_eq
  cases h_deep with
  | inl hb => exact DEntry.map interior hb
  | inr he => subst he; exact DEntry.mapEmpty

/-- **The finding in one proposition.**  (1) the entry-level descent of the severance-free `MEntry` is
    debt-free (R459's claim — but only at the located top entry); (2) yet a `Pair`'s VALUE is a bare
    `Entry`, which RE-INTRODUCES the flat severance one level deeper, with an unremovable gap; (3) the fix
    is a parallel family whose value field is a severance-free `DEntry`, descending a map-valued pair with
    NO debt.  Sharpens `[[ref-token-indistinguishable-severance-threads-recursion-from-producer]]`: the
    bridge to `RecMapEntry` does not eliminate the severance, it relocates it to every pair value — so the
    recursion must be producer-threaded at EACH map value, via a value field that carries it. -/
theorem severance_recurses_through_pair_value :
    (∀ e interior, MEntry e → e = Tok.mop :: (interior ++ [Tok.mcl]) → MBody interior ∨ interior = [])
    ∧ (Pair (Tok.k :: (Tok.mop :: ([Tok.mcl] ++ [Tok.mcl]))) ∧ ¬ (MBody [Tok.mcl] ∨ [Tok.mcl] = []))
    ∧ (∀ p val interior, DPair p → p = Tok.k :: val → val = Tok.mop :: (interior ++ [Tok.mcl]) →
        DBody interior ∨ interior = []) :=
  ⟨fun _e _i h h_eq => MEntry.map_interior h h_eq,
   pair_value_severance_is_real,
   fun _p _v _i h h1 h2 => DPair.value_map_descent h h1 h2⟩

end Tests.Reflections.SeveranceRecursesThroughPairValue
