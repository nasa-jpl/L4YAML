/-!
# Additive parallel type over shared edit — runnable demonstration

A self-contained (core Lean, no `L4YAML` import) illustration of the proof-engineering principle
documented in `Blueprint/08-initiative-4-intrinsic-foundations.md`, **Reflection 242**: when you
mirror a *family* of consumer joints and a joint demands a richer *deliverable* than the symmetric
side ever built, that is the signal to land the deferred refinement NOW — as a **new additive
parallel type** aimed straight at the existing consumer, never as a structural edit to the shared
type.  And a second, smaller lesson: a *dedicated* (monomorphic) type **internalizes** a guard the
*polymorphic* type needed supplied externally.

**The real instance.**  The seq side built two consumer joints off its recursive deliverable: a
back-half (R236) and a front-end (R237 `seqBodyProps_of_located_entry`), the latter extracting a
`RecSeqBody` from a *located* `RecSeqEntry` via `RecSeqEntry.seq_interior`.  Mirroring the front-end
to the map side needs a `RecMapBody` from a located map entry — but `RecSeqEntry.map` was
deliberately built to bottom out at `WellBracketed` (its fully-recursive interior flagged "a later
refinement").  So **no existing entry type carries the recursion the map front-end needs**: completing
the *family* forced the deferred refinement.  The decision (R242): do **not** edit the pervasively-used
`RecSeqEntry` (it would drag in a four-way `mutual`); define an **additive** `RecMapEntry` depending
only on the already-defined `RecMapBody`, with a guard-free split `RecMapEntry.map_interior`, and the
joint `mapBodyProps_of_located_entry` routes it to the existing back-half.

This toy mirrors every moving part:

* `PolyEntry` is the toy `RecSeqEntry` — polymorphic over `scalar` / `seqE` / `mapE`.  Its `seqE`
  carries the RECURSIVE `SeqBody`, but `mapE` **bottoms out** at the non-recursive `Flat` substrate
  (toy `WellBracketed`), exactly as `RecSeqEntry.map` does.
* `PolyEntry.seq_split` (toy `seq_interior`) **needs an external opener guard** `op = .sOpen` to
  select the seq branch and rule out the others.
* `PolyEntry.map_split` (toy `map_interior`) yields only `Flat` — never the recursion.  **This is why
  the front-end joint cannot use the polymorphic type.**
* `MapEntry` is the toy `RecMapEntry` — an **additive** type (zero edits to `PolyEntry`) carrying the
  recursive `MapBody`, with `mapEmpty` for the `{}` body that the no-`nil` `MapBody` cannot represent.
* `MapEntry.split` needs **no guard** — every constructor is a map, so the opener is internalized.
* `mapProps_of_located` is the front-end joint: it routes the split to the back-half / empty leaf.

The crux contrast is `poly_map_only_flat` vs `dedicated_map_gives_body` below: at the *same* located
map window, the polymorphic type yields only `Flat`, the dedicated type yields `MapBody`.

Run it: open in the IDE (the `#eval`s render in the infoview) or
`lake build Tests.Reflections.AdditiveParallelType` (the `#guard`s fail the build if any expectation
is wrong).
-/

namespace AdditiveParallelType

/-- Toy tokens: sequence brackets `[`/`]`, mapping brackets `{`/`}`, and a content `atom`. -/
inductive Tok | sOpen | sClose | mOpen | mClose | atom
  deriving DecidableEq, Repr

/-- Append-singleton injectivity (core Lean, no Mathlib): the toy of `append_singleton_inj`, used to
    read a bracket entry's interior off the constructor index. -/
theorem append_singleton_inj {a b : List Tok} {x y : Tok}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hr
  injection hr with hxy har
  exact ⟨List.reverse_inj.mp har, hxy⟩

/-! ## The recursive deliverables — both have NO `nil` constructor.

`SeqBody`/`MapBody` are the toys of `RecSeqBody`/`RecMapBody`: a body is a single atom or a nested
bracket entry whose interior is itself a body.  Neither has a `nil` constructor — so an empty body
`[]`/`{}` is NOT one, which is exactly why the descent split must carry an `interior = []` disjunct
(the R233 producer-contract split). -/

/-- Toy `RecSeqBody` (recursive). -/
inductive SeqBody : List Tok → Prop where
  | one (t : Tok) (h : t = .atom) : SeqBody [t]
  | nest (interior : List Tok) (h : SeqBody interior) :
      SeqBody (.sOpen :: (interior ++ [.sClose]))

/-- Toy `RecMapBody` (recursive) — the structure the map front-end joint needs. -/
inductive MapBody : List Tok → Prop where
  | one (t : Tok) (h : t = .atom) : MapBody [t]
  | nest (interior : List Tok) (h : MapBody interior) :
      MapBody (.mOpen :: (interior ++ [.mClose]))

/-- The non-recursive FLAT substrate — toy of `WellBracketed`, here trivial.  The point is not its
    content but that it is **non-recursive**: it cannot regenerate a body's structure, so an entry
    that bottoms out here can never hand back a `MapBody`. -/
abbrev Flat (_interior : List Tok) : Prop := True

/-! ## The polymorphic entry — the toy `RecSeqEntry`, whose `mapE` BOTTOMS OUT.

`seqE` carries the recursive `SeqBody`, but `mapE` carries only the non-recursive `Flat` — mirroring
`RecSeqEntry.map` stopping at `WellBracketed`.  This is the shared, pervasively-used type we must NOT
edit. -/

/-- Toy `RecSeqEntry`: polymorphic over scalar / nested seq (recursive) / nested map (bottomed out). -/
inductive PolyEntry : List Tok → Prop where
  | scalar (t : Tok) (h : t = .atom) : PolyEntry [t]
  | seqE (interior : List Tok) (h_rec : SeqBody interior) :
      PolyEntry (.sOpen :: (interior ++ [.sClose]))
  | mapE (interior : List Tok) (h_flat : Flat interior) :   -- NO recursion — only the flat substrate
      PolyEntry (.mOpen :: (interior ++ [.mClose]))

/-- **Seq split needs the external opener guard** (toy `RecSeqEntry.seq_interior`).  Because
    `PolyEntry` ranges over scalar/seq/map, the guard `op = .sOpen` is what selects the seq branch and
    rules out the others; without it the lemma could not fire. -/
theorem PolyEntry.seq_split {e interior : List Tok} {op cl : Tok}
    (h : PolyEntry e) (h_eq : e = op :: (interior ++ [cl])) (h_op : op = .sOpen) :
    SeqBody interior ∨ interior = [] := by
  cases h with
  | scalar t ht => injection h_eq with _h1 h2; simp at h2
  | seqE interior' h_rec =>
      left
      injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h_rec
  | mapE interior' h_flat =>
      exfalso
      injection h_eq with h1 _h2
      exact absurd (h1.trans h_op) (by decide)

/-- **Map split off the polymorphic type yields ONLY the flat substrate** (toy
    `RecSeqEntry.map_interior`).  `mapE` bottomed out, so a located map entry of `PolyEntry` can hand
    back `Flat`, never `MapBody`.  **This is precisely why the map front-end joint cannot use
    `PolyEntry`** — it needs `MapBody`, which lives only in the additive `MapEntry` below. -/
theorem PolyEntry.map_split {e interior : List Tok} {op cl : Tok}
    (h : PolyEntry e) (h_eq : e = op :: (interior ++ [cl])) (h_op : op = .mOpen) :
    Flat interior ∨ interior = [] := by
  cases h with
  | scalar t ht => injection h_eq with _h1 h2; simp at h2
  | seqE interior' h_rec =>
      exfalso
      injection h_eq with h1 _h2
      exact absurd (h1.trans h_op) (by decide)
  | mapE _ _ =>
      -- The flat substrate is all there is — `mapE` bottomed out, so nothing recursive to extract.
      exact Or.inl trivial

/-- **A pre-existing consumer of `PolyEntry`** (toy of `RecSeqEntry.toEntrySafe`/`toWellBracketed`).
    It still type-checks unchanged: adding `MapEntry` below was ADDITIVE — zero edits to `PolyEntry`
    or its API, so nothing it supports can regress. -/
theorem PolyEntry.nonempty {e : List Tok} (h : PolyEntry e) : e ≠ [] := by
  cases h <;> simp

/-! ## The ADDITIVE parallel type — the toy `RecMapEntry`.

`MapEntry` carries the recursive `MapBody` the polymorphic `mapE` lacked.  It depends only on the
already-defined `MapBody` — no `mutual`, no edit to `PolyEntry` — so it cannot regress anything, and
it is born aimed at the existing back-half consumer.  `mapEmpty` is the `{}` witness (`MapBody` has no
`nil`). -/

/-- Toy `RecMapEntry`: the dedicated, monomorphic, RECURSIVE map entry. -/
inductive MapEntry : List Tok → Prop where
  | mapEmpty : MapEntry [.mOpen, .mClose]
  | mapRec (interior : List Tok) (h_rec : MapBody interior) :
      MapEntry (.mOpen :: (interior ++ [.mClose]))

/-- **Map split needs NO guard** (toy `RecMapEntry.map_interior`).  Every `MapEntry` constructor is a
    mapping, so the opener `.mOpen` is INTERNALIZED — the lemma needs no external `h_op`, unlike the
    polymorphic `PolyEntry.seq_split`.  The `interior = []` disjunct is the `{}` body the no-`nil`
    `MapBody` cannot represent (R233 producer-contract split). -/
theorem MapEntry.split {e interior : List Tok} {op cl : Tok}
    (h : MapEntry e) (h_eq : e = op :: (interior ++ [cl])) :
    MapBody interior ∨ interior = [] := by
  cases h with
  | mapEmpty =>
      right
      injection h_eq with _h1 h2
      exact (append_singleton_inj h2.symm).1
  | mapRec interior' h_rec =>
      left
      injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h_rec

/-! ## The front-end joint — routes the split to back-half / empty leaf. -/

/-- Toy downstream target (`MapBodyProps`): the non-empty recursive structure feeds the "back half",
    the empty body is the vacuous leaf. -/
inductive MapProps : List Tok → Prop where
  | backHalf (interior : List Tok) (h : MapBody interior) :
      MapProps (.mOpen :: (interior ++ [.mClose]))
  | emptyLeaf : MapProps [.mOpen, .mClose]

/-- **The map front-end consumer joint** (toy `mapBodyProps_of_located_entry`).  Consumes a located
    `MapEntry` (the opener-window) and routes its single-level split: the non-empty disjunct to the
    back half, the empty disjunct to the vacuous leaf.  No opener guard is threaded — `MapEntry`
    internalized it. -/
theorem mapProps_of_located (interior : List Tok)
    (h : MapEntry (.mOpen :: (interior ++ [.mClose]))) :
    MapProps (.mOpen :: (interior ++ [.mClose])) := by
  rcases MapEntry.split h rfl with h_rec | h_empty
  · exact MapProps.backHalf interior h_rec
  · subst h_empty; exact MapProps.emptyLeaf

/-! ## The crux contrast — same located map window, two yields. -/

/-- At a located map window, the POLYMORPHIC type yields only `Flat` (no recursion). -/
theorem poly_map_only_flat : Flat [Tok.atom] ∨ [Tok.atom] = [] :=
  PolyEntry.map_split (PolyEntry.mapE [Tok.atom] trivial) rfl rfl

/-- At the SAME located map window, the DEDICATED type yields `MapBody` — the recursion the front-end
    joint needs.  The whole reason `MapEntry` had to exist. -/
theorem dedicated_map_gives_body : MapBody [Tok.atom] ∨ [Tok.atom] = [] :=
  MapEntry.split (MapEntry.mapRec [Tok.atom] (MapBody.one .atom rfl)) rfl

/-- `MapBody` has no `nil` constructor — an empty body cannot be one, so the `interior = []` disjunct
    (and `MapEntry.mapEmpty`) is what represents it. -/
theorem not_MapBody_nil : ¬ MapBody ([] : List Tok) := by
  intro h; cases h

/-! ## Witnesses. -/

/-- A non-empty map body `{ a }`. -/
def goodMap : List Tok := [.mOpen, .atom, .mClose]

/-- The empty map body `{}` — represented by `mapEmpty`, not `MapBody`. -/
def emptyMap : List Tok := [.mOpen, .mClose]

theorem goodMap_entry : MapEntry goodMap := MapEntry.mapRec [Tok.atom] (MapBody.one .atom rfl)
theorem emptyMap_entry : MapEntry emptyMap := MapEntry.mapEmpty

/-- End-to-end: the front-end joint turns the located non-empty entry into the back-half target. -/
theorem goodMap_props : MapProps goodMap := mapProps_of_located [Tok.atom] goodMap_entry

/-- End-to-end: the located empty entry routes to the vacuous leaf. -/
theorem emptyMap_props : MapProps emptyMap := mapProps_of_located [] emptyMap_entry

/-! ### `#eval` — the contrast made visible. -/

/-- info: "PolyEntry @ map window  -> Flat substrate only (bottomed out); seq_split needs an EXTERNAL opener guard" -/
#guard_msgs in
#eval "PolyEntry @ map window  -> Flat substrate only (bottomed out); seq_split needs an EXTERNAL opener guard"

/-- info: "MapEntry  @ map window  -> MapBody recursion (additive type); split needs NO guard (opener internalized)" -/
#guard_msgs in
#eval "MapEntry  @ map window  -> MapBody recursion (additive type); split needs NO guard (opener internalized)"

/-! ### `#guard` — the decidable facts. -/

#guard  decide (Tok.mOpen ≠ Tok.sOpen)   -- the opener guard the polymorphic split needs is a real choice
#guard  decide (goodMap = [Tok.mOpen, Tok.atom, Tok.mClose])
#guard  decide (emptyMap = [Tok.mOpen, Tok.mClose])

end AdditiveParallelType
