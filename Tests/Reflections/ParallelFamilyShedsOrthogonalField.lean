/-!
# Reflection 462 — porting a verified-but-unconsumed PARALLEL family to the main lib should SHED any
# flat-type field that is ORTHOGONAL to the family's purpose and re-derivable from the field the family
# DOES carry, RE-MATERIALIZING it on projection — keeping the parallel family a MINIMAL carrier and
# LIGHTENING the future producer's contract.

Self-contained (core Lean, no `L4YAML` import) toy executing STEP D step 7's design decision: when the
R461 SHAPE PROBE's deep family (`[[ref-deep-family-mirrors-full-mutual-group]]`) is AUTHORED in the main
lib, the flat recursive constructors (`RecSeqEntry.seq`/`.mapRec`) ALSO store a `WellBracketed interior`
field — should the deep family store it too (a verbatim mirror), or SHED it?

**The decision: SHED it.**  The flat family stores the orthogonal field because its SEVERED constructor
(the flat `.map`, recursion-cut) has no recursive body to derive it from; the recursive constructor
inherits the stored-field convention to mirror.  The deep family REPLACES the severed constructor with a
recursion-carrying one — so the orthogonal field is now REDUNDANT (re-derivable from the body the family
carries, via the EXISTING flat extractor).  Shedding it keeps the deep family a minimal recursion carrier
AND lightens the future producer: it threads only the recursion, never the orthogonal field, which
materializes only at the flat-projection boundary.

This toy mirrors the real port exactly:

* `B` — the orthogonal, body-derivable field (here "non-empty", mirror `WellBracketed`).
* `FEntry.wrapRec` stores BOTH `hB : B interior` AND the recursive `h : FBody interior` (mirror the real
  `RecSeqEntry.seq`/`.mapRec`); the severed `FEntry.wrapFlat` stores ONLY `hB` (mirror the flat `.map`).
* `DEntry.wrap` stores ONLY the recursive body — `B` is SHED.
* `DEntry.toFlat` re-materializes `B` via the FLAT extractor `FBody.toB` applied to the PROJECTED body —
  exactly as the real `RecEntryDeep.toFlat` supplies `WellBracketed` from
  `RecSeqBody.toWellBracketed`/`RecMapBody.toWellBracketed (… .toFlat …)`.  (The `wrap` arm calls
  `DBody.toFlat` twice — once for the body, once feeding the extractor — validating that the real
  double-call compiles under structural recursion.)
* `deep_producer_needs_no_B` vs `flat_producer_needs_B` — the contrast: the deep recursive constructor
  takes no `B`, the flat one does.
* `parallel_family_sheds_orthogonal_field` — the finding in one proposition.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.ParallelFamilyShedsOrthogonalField

/-- Toy alphabet: `a` content, `op`/`cl` brackets, `fe` the entry separator. -/
inductive Tok where
  | a | op | cl | fe
deriving DecidableEq

/-- The ORTHOGONAL, body-derivable field the flat family stores (mirror `WellBracketed`): here
    "non-empty".  Orthogonal to the recursion (a balance/structural invariant of the token list), yet
    derivable from any recursive body — which is exactly why the deep family can SHED it. -/
def B (l : List Tok) : Prop := l ≠ []

/-! ## Flat family — the recursive constructor stores BOTH the body AND the orthogonal `B`
    (mirror `RecSeqEntry.seq`/`.mapRec` storing `h_wb : WellBracketed` + `h_rec`); the SEVERED
    `wrapFlat` stores ONLY `B` (mirror the flat `.map` — it has no body to derive `B` from, so it MUST
    store it). -/
mutual
  inductive FEntry : List Tok → Prop where
    | leaf : FEntry [Tok.a]
    | wrapFlat (interior : List Tok) (hB : B interior) :
        FEntry (Tok.op :: (interior ++ [Tok.cl]))
    | wrapRec (interior : List Tok) (hB : B interior) (h : FBody interior) :
        FEntry (Tok.op :: (interior ++ [Tok.cl]))
  inductive FBody : List Tok → Prop where
    | single (e : List Tok) (h_e : FEntry e) : FBody e
    | cons (e rest : List Tok) (h_e : FEntry e) (h_rest : FBody rest) :
        FBody (e ++ Tok.fe :: rest)
end

/-! ## Deep family — the recursive constructor stores ONLY the body; the orthogonal `B` is SHED.
    There is no severed `wrapFlat`: every entry carries its recursive body, so `B` is always derivable. -/
mutual
  inductive DEntry : List Tok → Prop where
    | leaf : DEntry [Tok.a]
    | wrap (interior : List Tok) (h : DBody interior) :
        DEntry (Tok.op :: (interior ++ [Tok.cl]))
  inductive DBody : List Tok → Prop where
    | single (e : List Tok) (h_e : DEntry e) : DBody e
    | cons (e rest : List Tok) (h_e : DEntry e) (h_rest : DBody rest) :
        DBody (e ++ Tok.fe :: rest)
end

/-! ## The FLAT extractor for the orthogonal field — what the projection re-materializes `B` through
    (mirror the existing `RecSeqBody.toWellBracketed`/`RecMapBody.toWellBracketed`). -/

/-- Every `FEntry` is non-empty (each constructor's index is `[a]` or `op :: …`). -/
theorem FEntry.ne_nil : {e : List Tok} → FEntry e → e ≠ []
  | _, .leaf => by simp
  | _, .wrapFlat _ _ => by simp
  | _, .wrapRec _ _ _ => by simp

/-- A flat `FBody` is non-empty — i.e. `B` holds of it.  This is the flat extractor the deep→flat
    projection applies to the PROJECTED body to re-materialize the shed `B` (mirror
    `RecSeqBody.toWellBracketed`). -/
theorem FBody.toB {l : List Tok} (h : FBody l) : B l := by
  cases h with
  | single e h_e => exact FEntry.ne_nil h_e
  | cons e rest h_e h_rest => show e ++ Tok.fe :: rest ≠ []; cases e <;> simp

/-! ## The deep→flat PROJECTION — re-materializes the shed `B` from the projected body. -/

mutual
  /-- The deep `wrap` projects to the flat `wrapRec`, SUPPLYING the orthogonal `B` from the FLAT
      extractor `FBody.toB` applied to the projected body `DBody.toFlat h` — never stored in the deep
      family.  The arm calls `DBody.toFlat h` twice (once for the body, once feeding the extractor),
      mirroring the real `RecEntryDeep.toFlat`'s `seq`/`mapRec` arms and validating that the double
      recursive call compiles under structural recursion. -/
  theorem DEntry.toFlat : {e : List Tok} → DEntry e → FEntry e
    | _, .leaf => FEntry.leaf
    | _, .wrap interior h =>
        FEntry.wrapRec interior (FBody.toB (DBody.toFlat h)) (DBody.toFlat h)
  theorem DBody.toFlat : {l : List Tok} → DBody l → FBody l
    | _, .single e h_e => FBody.single e (DEntry.toFlat h_e)
    | _, .cons e rest h_e h_rest => FBody.cons e rest (DEntry.toFlat h_e) (DBody.toFlat h_rest)
end

/-! ## The contrast — the deep producer needs no `B`, the flat one does. -/

/-- **The deep producer needs NO `B`.**  Building a deep `wrap` requires only the recursive body — the
    orthogonal `B` is never threaded.  (Mirror: the future producer of `RecEntryDeep` threads only the
    recursion, never `WellBracketed`.) -/
theorem deep_producer_needs_no_B (interior : List Tok) (h : DBody interior) :
    DEntry (Tok.op :: (interior ++ [Tok.cl])) := DEntry.wrap interior h

/-- **The flat producer DOES need `B`.**  Building the flat recursive `wrapRec` requires supplying the
    orthogonal `B interior` alongside the body — the field the deep family sheds. -/
theorem flat_producer_needs_B (interior : List Tok) (hB : B interior) (h : FBody interior) :
    FEntry (Tok.op :: (interior ++ [Tok.cl])) := FEntry.wrapRec interior hB h

/-- A concrete `{ a }`-shaped deep entry inhabits the deep family (with no `B` supplied), PROJECTS to the
    flat family, and the projection re-materializes `B` from the projected body. -/
theorem deep_wrap_projects_and_rederives_B :
    DEntry (Tok.op :: ([Tok.a] ++ [Tok.cl]))
    ∧ FEntry (Tok.op :: ([Tok.a] ++ [Tok.cl]))
    ∧ B [Tok.a] := by
  have hbody : DBody [Tok.a] := DBody.single _ DEntry.leaf
  have hdeep : DEntry (Tok.op :: ([Tok.a] ++ [Tok.cl])) := DEntry.wrap _ hbody
  exact ⟨hdeep, DEntry.toFlat hdeep, FBody.toB (DBody.toFlat hbody)⟩

/-- **The finding in one proposition.**  (1) the deep family PROJECTS to the flat family
    (`DEntry.toFlat`); (2) the deep recursive constructor needs NO `B` (`deep_producer_needs_no_B`),
    while the flat one does (`flat_producer_needs_B`); (3) `B` is re-derivable from the deep body (via
    the projection + the FLAT extractor `FBody.toB`), which is exactly why shedding it loses nothing.
    Porting the verified-but-unconsumed parallel family to the main lib SHEDS the orthogonal,
    body-derivable field, keeping the family a minimal recursion carrier and lightening the future
    producer's contract.  Sharpens `[[ref-deep-family-mirrors-full-mutual-group]]` (which fixed the
    family SHAPE) with the field-level porting refinement, via
    `[[ref-recursive-deliverable-project-to-flat-first]]` (the projection re-materializes the shed field)
    and `[[ref-additive-parallel-type-over-shared-edit]]` (a minimal additive carrier, the flat type's
    stored field untouched). -/
theorem parallel_family_sheds_orthogonal_field :
    (∀ l, DEntry l → FEntry l)
    ∧ (∀ interior, DBody interior → DEntry (Tok.op :: (interior ++ [Tok.cl])))
    ∧ (∀ interior, B interior → FBody interior → FEntry (Tok.op :: (interior ++ [Tok.cl])))
    ∧ (∀ l, DBody l → B l) :=
  ⟨fun _l h => DEntry.toFlat h,
   fun interior h => DEntry.wrap interior h,
   fun interior hB h => FEntry.wrapRec interior hB h,
   fun _l h => FBody.toB (DBody.toFlat h)⟩

end Tests.Reflections.ParallelFamilyShedsOrthogonalField
