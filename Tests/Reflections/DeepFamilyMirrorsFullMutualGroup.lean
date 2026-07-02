/-!
# Reflection 461 — the severance-free deep family that resolves a recursive token-indistinguishable
# severance must mirror the FULL mutual group of the recursion (BOTH the seq and map axes), not just
# the one axis where the severance was first seen — because the navigator recursion is MUTUAL
# (a map value can be a seq, a seq entry can be a map, to any depth) — and per
# `[[ref-recursive-deliverable-project-to-flat-first]]` its FIRST brick is the deep→flat PROJECTION.

Self-contained (core Lean, no `L4YAML` import) toy executing the SHAPE PROBE that STEP D step 6
front-loads: decide whether the deep-map family is **(a)** a NEW four-inductive mutual group, or **(b)**
a thinner family reusing the map-only `RecMapEntry` for the pair value/key.

R460 (`SeveranceRecursesThroughPairValue`) found the token-indistinguishable map severance RECURSES:
`RecMapPair.mk` stores the value/key as a **bare `RecSeqEntry`**, so a map-value-that-is-a-map re-hits the
flat-`.map` `cases`.  Its fix sketch (`DEntry`/`DPair`/`DBody`) was MAP-ONLY.  This round settles the
shape and lands the projection:

* **(a) over (b).**  `value_can_be_nonmap` — a map pair's value can be a SCALAR (or a SEQ), so the value
  field must be a *universal* severance-free entry; the map-only `RecMapEntry` (mapEmpty/map only) cannot
  type it.  So (b) is rejected: the deep family needs its own universal entry type.

* **The recursion is MUTUAL — the seq axis is severed too.**  `seq_of_map_severance_is_real` — a flat
  `FSeqBody` whose head entry is a flat `mapFlat` has an unrecoverable inner `FMapBody`: the EXISTING seq
  navigator over `RecSeqBody` (whose `.single`/`.cons` store bare `RecSeqEntry` entries) re-hits the
  flat-`.map` severance at a seq-of-map (the M3 `[{a:{x:[b]}}]` shape: `[` → `{` → `{` → `[`).  So the
  deep family's SEQ bodies must be deep too — one four-inductive mutual group covering both axes, NOT a
  map-only family bolted onto the flat `RecSeqBody`.

* **The PROJECTION is the first brick.**  `DEntry.toFlat`/`DSeqBody.toFlat`/`DMapPair.toFlat`/
  `DMapBody.toFlat` (a mutual theorem block) project the deep family onto the flat one: a deep `map` lands
  in flat `mapRec` (RECURSION PRESERVED — flat consumers reading `mapRec`'s body still get it), a deep
  `mapEmpty` lands in flat `mapFlat []` (the producer's degenerate-`{}` dispatch, R458).  Authoring the
  projection FIRST (`[[ref-recursive-deliverable-project-to-flat-first]]`) both validates the family shape
  (it must project) and keeps existing flat consumers firing.

* `deep_descends_both_axes_clean` — a depth-3 `[ { k : [ a ] } ]` (seq → map → seq) inhabits the deep
  family, projects to the flat family, AND descends through the seq, map, and inner-seq boundaries with NO
  producer debt (the descent the flat family cannot do unthreaded on either axis).

* `toDEntry` — the producer bridge threading the deep body at a value (mirror `RecSeqEntry.toRecMapEntry`,
  generalized: the recursion comes from the producer at every value/key, on either axis).

* `deep_family_mirrors_full_mutual_group` — the finding in one proposition.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.DeepFamilyMirrorsFullMutualGroup

/-- Toy alphabet: `a` content, `sop`/`scl` seq brackets, `mop`/`mcl` map brackets, `k` the `.key`
    marker, `fe` the `.flowEntry` separator (both for seq entries and map pairs, as in the real types). -/
inductive Tok where
  | a | sop | scl | mop | mcl | k | fe
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
    interior — which is exactly what lets the flat `.map` carry a non-`FMapBody` interior. -/
def WB (_l : List Tok) : Prop := True

/-! ## The severance-prone FLAT family — mirror the merged 4-inductive group
    `RecSeqBody`/`RecSeqEntry`/`RecMapPair`/`RecMapBody`.

`FEntry` is the UNIVERSAL entry: scalar / seq (stores `FSeqBody` — no severance) / map.  The map case has
BOTH a flat severance (`mapFlat`, stores only `WB`) and the recursive `mapRec` (stores `FMapBody`) —
token-indistinguishable, same `mop :: interior ++ [mcl]`.  Crucially BOTH the seq body's entries
(`FSeqBody`'s `h_e : FEntry e`, mirror `RecSeqBody`) AND the map pair's value (`FMapPair`'s
`h_v : FEntry val`, mirror `RecMapPair`'s `h_ve : RecSeqEntry block_v`) are **bare `FEntry`** — so the
severance recurs on BOTH axes. -/
mutual
  inductive FEntry : List Tok → Prop where
    | scalar : FEntry [Tok.a]
    | seqEmpty : FEntry (Tok.sop :: ([] ++ [Tok.scl]))
    | seq (interior : List Tok) (h : FSeqBody interior) :
        FEntry (Tok.sop :: (interior ++ [Tok.scl]))
    | mapFlat (interior : List Tok) (hwb : WB interior) :
        FEntry (Tok.mop :: (interior ++ [Tok.mcl]))
    | mapRec (interior : List Tok) (h : FMapBody interior) :
        FEntry (Tok.mop :: (interior ++ [Tok.mcl]))
  inductive FSeqBody : List Tok → Prop where
    | single (e : List Tok) (h_e : FEntry e) : FSeqBody e
    | cons (e rest : List Tok) (h_e : FEntry e) (h_rest : FSeqBody rest) :
        FSeqBody (e ++ Tok.fe :: rest)
  inductive FMapPair : List Tok → Prop where
    | mk (val : List Tok) (h_v : FEntry val) : FMapPair (Tok.k :: val)
  inductive FMapBody : List Tok → Prop where
    | single (p : List Tok) (h_p : FMapPair p) : FMapBody p
    | cons (p rest : List Tok) (h_p : FMapPair p) (h_rest : FMapBody rest) :
        FMapBody (p ++ Tok.fe :: rest)
end

/-! ## The DEEP family — the SHAPE DECISION: option (a), a NEW four-inductive mutual group.

`DEntry` is the UNIVERSAL severance-free entry: scalar / seqEmpty / seq (`DSeqBody`) / mapEmpty / map
(`DMapBody`).  **No flat `mapFlat` constructor** — the map case always carries its `DMapBody`.  Both axes
recurse through the deep family: `DSeqBody`'s entries are `DEntry`, `DMapPair`'s value is `DEntry`.  So the
navigator only ever descends severance-free types, on BOTH the seq and map axes, to any depth. -/
mutual
  inductive DEntry : List Tok → Prop where
    | scalar : DEntry [Tok.a]
    | seqEmpty : DEntry (Tok.sop :: ([] ++ [Tok.scl]))
    | seq (interior : List Tok) (h : DSeqBody interior) :
        DEntry (Tok.sop :: (interior ++ [Tok.scl]))
    | mapEmpty : DEntry (Tok.mop :: ([] ++ [Tok.mcl]))
    | map (interior : List Tok) (h : DMapBody interior) :
        DEntry (Tok.mop :: (interior ++ [Tok.mcl]))
  inductive DSeqBody : List Tok → Prop where
    | single (e : List Tok) (h_e : DEntry e) : DSeqBody e
    | cons (e rest : List Tok) (h_e : DEntry e) (h_rest : DSeqBody rest) :
        DSeqBody (e ++ Tok.fe :: rest)
  inductive DMapPair : List Tok → Prop where
    | mk (val : List Tok) (h_v : DEntry val) : DMapPair (Tok.k :: val)
  inductive DMapBody : List Tok → Prop where
    | single (p : List Tok) (h_p : DMapPair p) : DMapBody p
    | cons (p rest : List Tok) (h_p : DMapPair p) (h_rest : DMapBody rest) :
        DMapBody (p ++ Tok.fe :: rest)
end

/-! ## (a) over (b): the value field must be a UNIVERSAL entry, not the map-only `RecMapEntry`. -/

/-- **The pair value can be a NON-map** (a scalar here; equally a seq).  So the deep family's pair value
    field must be a *universal* severance-free entry (`DEntry`) — the map-only `RecMapEntry`
    (`mapEmpty`/`map` only) could not type this value.  This rejects shape (b) ("reuse `RecMapEntry` for
    the value/key directly"): a `RecMapPair`-of-`RecMapEntry` cannot represent a scalar- or seq-valued
    pair, which the emit feed produces freely. -/
theorem value_can_be_nonmap :
    DMapPair (Tok.k :: [Tok.a]) ∧ ([Tok.a] : List Tok).head? ≠ some Tok.mop :=
  ⟨DMapPair.mk [Tok.a] DEntry.scalar, by decide⟩

/-! ## The deep→flat PROJECTION — the FIRST brick (`[[ref-recursive-deliverable-project-to-flat-first]]`).

A mutual theorem block mirroring the mutual inductive structure.  The deep `map` projects to the flat
`mapRec` (recursion PRESERVED), the deep `mapEmpty` to the flat `mapFlat []` (the producer's degenerate
`{}` dispatch, R458 — the flat `mapFlat` is reached only where the no-`nil` `FMapBody` structurally cannot
represent the empty body).  So every existing flat consumer (the `RecMapBody.toSafeBody` /
`RecSeqEntry.toEntrySafe` analogues) still fires on the projected output. -/
mutual
  theorem DEntry.toFlat : {l : List Tok} → DEntry l → FEntry l
    | _, .scalar => FEntry.scalar
    | _, .seqEmpty => FEntry.seqEmpty
    | _, .seq interior h => FEntry.seq interior (DSeqBody.toFlat h)
    | _, .mapEmpty => FEntry.mapFlat [] trivial
    | _, .map interior h => FEntry.mapRec interior (DMapBody.toFlat h)
  theorem DSeqBody.toFlat : {l : List Tok} → DSeqBody l → FSeqBody l
    | _, .single e h_e => FSeqBody.single e (DEntry.toFlat h_e)
    | _, .cons e rest h_e h_rest => FSeqBody.cons e rest (DEntry.toFlat h_e) (DSeqBody.toFlat h_rest)
  theorem DMapPair.toFlat : {l : List Tok} → DMapPair l → FMapPair l
    | _, .mk val h_v => FMapPair.mk val (DEntry.toFlat h_v)
  theorem DMapBody.toFlat : {l : List Tok} → DMapBody l → FMapBody l
    | _, .single p h_p => FMapBody.single p (DMapPair.toFlat h_p)
    | _, .cons p rest h_p h_rest => FMapBody.cons p rest (DMapPair.toFlat h_p) (DMapBody.toFlat h_rest)
end

/-! ## The recursion is MUTUAL — the seq axis is severed too (the sharpening of the map-only framing). -/

/-- Every `FMapBody` begins with the `.key` marker (structural, both spine constructors) — used to refute
    that a flat `mapFlat`'s interior could be an `FMapBody`. -/
theorem FMapBody.head?_key : {l : List Tok} → FMapBody l → l.head? = some Tok.k
  | _, .single _ h_p => by cases h_p with | mk val h_v => rfl
  | _, .cons p _ h_p _ => by
      cases h_p with
      | mk val h_v =>
          simp only [List.cons_append, List.head?_cons]

/-- `[mcl]` (a flat `mapFlat`'s interior) is provably not an `FMapBody`: an `FMapBody` starts with `.key`. -/
theorem not_fmapbody_mcl : ¬ FMapBody [Tok.mcl] := fun h => absurd (FMapBody.head?_key h) (by decide)

/-- **The severance recurses through the SEQ axis too.**  A flat `FSeqBody` whose single entry is a flat
    `mapFlat` (interior `[mcl]`, trivially `WB`) exists, yet that interior is provably NOT a recoverable
    `FMapBody`.  This is the M3 `[{a:{x:[b]}}]` shape: descending a SEQ body reaches a map-valued entry as
    a bare `FEntry`, re-hitting the flat-`.map` severance — so the EXISTING seq navigator over `RecSeqBody`
    cannot descend a seq-of-map.  Hence the deep family must make the SEQ bodies deep too: one mutual group
    covering both axes, not a map-only family bolted onto the flat `RecSeqBody`. -/
theorem seq_of_map_severance_is_real :
    FSeqBody [Tok.mop, Tok.mcl, Tok.mcl]
    ∧ ¬ (FMapBody [Tok.mcl] ∨ [Tok.mcl] = []) := by
  refine ⟨?_, ?_⟩
  · -- the seq's single entry is a flat `mapFlat` with interior `[mcl]`.
    have h_entry : FEntry (Tok.mop :: ([Tok.mcl] ++ [Tok.mcl])) := FEntry.mapFlat [Tok.mcl] trivial
    exact FSeqBody.single _ h_entry
  · rintro (hb | he)
    · exact not_fmapbody_mcl hb
    · simp at he

/-! ## The deep family descends BOTH axes with NO producer debt. -/

/-- `DEntry` entry-level descent on the MAP axis — debt-free (no flat severance to block it). -/
theorem DEntry.map_interior {e interior : List Tok}
    (h : DEntry e) (h_eq : e = Tok.mop :: (interior ++ [Tok.mcl])) :
    DMapBody interior ∨ interior = [] := by
  cases h with
  | scalar => injection h_eq with h1 _h2; exact absurd h1 (by decide)
  | seqEmpty => injection h_eq with h1 _h2; exact absurd h1 (by decide)
  | seq interior' h => injection h_eq with h1 _h2; exact absurd h1 (by decide)
  | mapEmpty =>
      right; injection h_eq with _h1 h2; simp only [List.nil_append] at h2
      exact (append_singleton_inj h2.symm).1
  | map interior' h =>
      left; injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h

/-- `DEntry` entry-level descent on the SEQ axis — debt-free (the seq side never had a severance, but the
    deep family keeps it clean uniformly). -/
theorem DEntry.seq_interior {e interior : List Tok}
    (h : DEntry e) (h_eq : e = Tok.sop :: (interior ++ [Tok.scl])) :
    DSeqBody interior ∨ interior = [] := by
  cases h with
  | scalar => injection h_eq with h1 _h2; exact absurd h1 (by decide)
  | seqEmpty =>
      right; injection h_eq with _h1 h2; simp only [List.nil_append] at h2
      exact (append_singleton_inj h2.symm).1
  | seq interior' h =>
      left; injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h
  | mapEmpty => injection h_eq with h1 _h2; exact absurd h1 (by decide)
  | map interior' h => injection h_eq with h1 _h2; exact absurd h1 (by decide)

/-- Descend a `DMapPair` to its value `DEntry` (clean `cases`, severance-free). -/
theorem DMapPair.value {p val : List Tok} (h : DMapPair p) (h_eq : p = Tok.k :: val) : DEntry val := by
  cases h with
  | mk val' h_v => injection h_eq with _h1 h2; exact h2 ▸ h_v

/-- **A depth-3 `[ { k : [ a ] } ]` (seq → map → seq) inhabits the deep family, PROJECTS to the flat
    family, AND descends through all three boundaries with NO producer debt.**  This is the M3-shaped
    mutual nesting the flat family cannot descend unthreaded on EITHER axis: the outer seq's entry is a map
    (seq-of-map severance) and the map's value is a seq.  In the deep family every boundary is a plain,
    debt-free `cases`; the projection lands the map level in flat `mapRec` (recursion preserved). -/
theorem deep_descends_both_axes_clean :
    -- the depth-3 outer seq entry `[ { k : [ a ] } ]` inhabits the deep family ...
    DEntry (Tok.sop :: ([Tok.mop, Tok.k, Tok.sop, Tok.a, Tok.scl, Tok.mcl] ++ [Tok.scl]))
    -- ... and projects to the FLAT family (so flat consumers still fire) ...
    ∧ FEntry (Tok.sop :: ([Tok.mop, Tok.k, Tok.sop, Tok.a, Tok.scl, Tok.mcl] ++ [Tok.scl]))
    -- ... its outer seq body descends to the inner map body with NO debt ...
    ∧ (DMapBody [Tok.k, Tok.sop, Tok.a, Tok.scl] ∨ ([Tok.k, Tok.sop, Tok.a, Tok.scl] : List Tok) = [])
    -- ... and the map pair's value seq descends to its scalar body with NO debt.
    ∧ (DSeqBody [Tok.a] ∨ ([Tok.a] : List Tok) = []) := by
  -- innermost: the value seq `[ a ]`.
  have h_inner_body : DSeqBody [Tok.a] := DSeqBody.single _ DEntry.scalar
  have h_val_seq : DEntry (Tok.sop :: ([Tok.a] ++ [Tok.scl])) := DEntry.seq _ h_inner_body
  -- the map pair `k : [ a ]`, its body, then the map `{ k : [ a ] }`.
  have h_pair : DMapPair (Tok.k :: (Tok.sop :: ([Tok.a] ++ [Tok.scl]))) := DMapPair.mk _ h_val_seq
  have h_map_body : DMapBody [Tok.k, Tok.sop, Tok.a, Tok.scl] := DMapBody.single _ h_pair
  have h_map : DEntry (Tok.mop :: ([Tok.k, Tok.sop, Tok.a, Tok.scl] ++ [Tok.mcl])) := DEntry.map _ h_map_body
  -- the outer seq body `[ { k : [ a ] } ]` and its entry.
  have h_outer_body : DSeqBody [Tok.mop, Tok.k, Tok.sop, Tok.a, Tok.scl, Tok.mcl] := DSeqBody.single _ h_map
  have h_outer : DEntry (Tok.sop :: ([Tok.mop, Tok.k, Tok.sop, Tok.a, Tok.scl, Tok.mcl] ++ [Tok.scl])) :=
    DEntry.seq _ h_outer_body
  refine ⟨h_outer, DEntry.toFlat h_outer, ?_, ?_⟩
  · -- the map entry's interior descends with NO debt:
    exact DEntry.map_interior h_map rfl
  · -- the value seq's interior descends with NO debt:
    exact DEntry.seq_interior (DMapPair.value h_pair rfl) rfl

/-- **The producer bridge threads the DEEP body at a value** (mirror `RecSeqEntry.toRecMapEntry`,
    generalized: the body is now a recursive `DMapBody`, and the producer applies this at EVERY map
    value/key, never recovering the recursion from the bare flat `FEntry`).  `_h` (the bare entry) is
    carried, never destructured — the recursion comes from the producer's deep body debt `h_deep`. -/
theorem toDEntry {e interior : List Tok}
    (_h : FEntry e) (h_eq : e = Tok.mop :: (interior ++ [Tok.mcl]))
    (h_deep : DMapBody interior ∨ interior = []) :
    DEntry e := by
  subst h_eq
  cases h_deep with
  | inl hb => exact DEntry.map interior hb
  | inr he => subst he; exact DEntry.mapEmpty

/-- **The finding in one proposition.**  (1) the deep family PROJECTS to the flat family on every axis
    (`DEntry.toFlat`), so existing flat consumers still fire; (2) the value field must be a UNIVERSAL
    entry — a pair value can be a non-map (`value_can_be_nonmap`), rejecting shape (b)'s map-only
    `RecMapEntry`; (3) the recursion is MUTUAL — a seq-of-map is severed in the flat family
    (`seq_of_map_severance_is_real`), so the deep family must cover the seq axis too; (4) the deep family
    descends both axes with NO producer debt (`deep_descends_both_axes_clean`).  Decision: shape (a), a
    NEW four-inductive mutual group covering both axes, severance-free.  Sharpens
    `[[ref-severance-recurses-through-pair-value]]` (the parallel family must mirror the FULL mutual group,
    not just the axis where the severance was first seen) via
    `[[ref-recursive-deliverable-project-to-flat-first]]` (author the deep→flat projection first). -/
theorem deep_family_mirrors_full_mutual_group :
    (∀ l, DEntry l → FEntry l)
    ∧ (DMapPair (Tok.k :: [Tok.a]) ∧ ([Tok.a] : List Tok).head? ≠ some Tok.mop)
    ∧ (FSeqBody [Tok.mop, Tok.mcl, Tok.mcl] ∧ ¬ (FMapBody [Tok.mcl] ∨ [Tok.mcl] = []))
    ∧ (∀ e interior, DEntry e → e = Tok.mop :: (interior ++ [Tok.mcl]) → DMapBody interior ∨ interior = [])
    ∧ (∀ e interior, DEntry e → e = Tok.sop :: (interior ++ [Tok.scl]) → DSeqBody interior ∨ interior = []) :=
  ⟨fun _l h => DEntry.toFlat h,
   value_can_be_nonmap,
   seq_of_map_severance_is_real,
   fun _e _i h h_eq => DEntry.map_interior h h_eq,
   fun _e _i h h_eq => DEntry.seq_interior h h_eq⟩

end Tests.Reflections.DeepFamilyMirrorsFullMutualGroup
