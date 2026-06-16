/-!
# Reflection 454 — adding a constructor whose FIELD TYPE lives in a downstream, originally
# NON-mutual group of the same recursive family silently FORCES the two groups to MERGE into one
# `mutual` block.  The merge is safe by an ordering argument; the per-matcher cost is as predicted.

Self-contained (core Lean, no `L4YAML` import) toy of the R454 finding — the EXECUTION of R453's
"separate `RecSeqEntry.mapRec` constructor" plan, which on contact with the real code revealed a cost
R453's de-risk under-priced.

Context.  R453 ([[ref-two-role-deliverable-blocks-shared-field]]) resolved the blocked
"required field on the shared `RecSeqEntry.map`" by a SEPARATE `mapRec` constructor carrying
`h_rec : RecMapBody interior`, priced as "add a constructor + one verbatim arm per matcher (~13)".

The under-priced cost.  `RecMapBody` was NOT declared with `RecSeqEntry`.  The original layering was
TWO groups, ~1500 lines apart:
  * group 1 (`mutual`): `RecSeqBody` / `RecSeqEntry`;
  * group 2 (plain, downstream): `RecMapPair` (refs `RecSeqEntry`) then `RecMapBody` (recurses on
    itself) — a ONE-DIRECTIONAL dependency `RecMapBody → RecMapPair → RecSeqEntry`, so the original
    design comment correctly said "no `mutual` block is needed".
Adding `RecSeqEntry.mapRec : … → RecMapBody interior → …` adds the back-edge
`RecSeqEntry → RecMapBody`, turning the one-directional dependency into a genuine CYCLE
`RecSeqEntry → RecMapBody → RecMapPair → RecSeqEntry`.  A cycle must be co-declared in ONE `mutual`
block — so the additive constructor silently FORCED a four-inductive mutual-group MERGE.

The two findings this toy proves:

1.  **Diagnose the merge before editing.**  When the new constructor's field type `F` is a recursive
    type whose group (transitively) references the type you're EXTENDING, the new field closes a cycle
    and the groups MUST merge.  (Here `RecMapBody`'s group already referenced `RecSeqEntry`; the new
    field added the reverse edge.)

2.  **The merge is SAFE by an ordering argument.**  Moving the downstream INDUCTIVE DECLARATIONS up
    into the target block is sound iff they reference nothing defined BETWEEN the target block and
    their old site.  `RecMapPair`/`RecMapBody`'s declarations reference only `RecSeqEntry` + token
    constructors — nothing in the 1500 intervening lines.  (Their PROJECTION theorems, which DO use
    intervening lemmas, stay at the old site; only the bare `inductive` declarations move.)  And
    moving a declaration strictly EARLIER can never break use-ordering: everything that consumed it
    sat after its old position, hence still after its new, earlier one.  Empirically: the real merge
    built green on the FIRST full build, and the structural recursions on the moved inductive
    (`RecMapBody.toSafeBody` etc.) survived — recursing on ONE inductive of a mutual family is exactly
    what the joint recursor supports.

This toy mirrors that exactly:

* `Flat`           — the coarse balance-only fact (mirror `WellBracketed`), as in R453.
* `A`              — the entry type being EXTENDED (mirror `RecSeqEntry`): `scalar` / `map` (flat) and
                     the NEW `mapRec` storing `B` — the back-edge that closes the cycle.
* `B`              — the downstream body type (mirror `RecMapBody`), recursing back through `A`.
* `B.toFlat`       — a projection on `B` that references ONLY `A` and `Flat` (the safety witness: it
                     would have type-checked at `B`'s ORIGINAL downstream site, so moving `B` up
                     breaks nothing — it needs nothing "in between").
* `merge_*`        — the merged block compiles and the cross-cycle is inhabited (depth-2 witness).

The point the toy can only DESCRIBE (a non-compiling state can't live in a green file): the
pre-merge `inductive A` (with `mapRec` referencing a not-yet-declared, separately-grouped `B`) does
NOT type-check — Lean reports an unknown identifier / forward reference.  The fix is precisely the
`mutual` block below.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.ConstructorFieldForcesMutualGroupMerge

/-- Toy token alphabet: scalar, `{`/`}` (map open/close), `.key`/`.value`.  Mirrors `YamlToken`. -/
inductive Tok where
  | sc | om | cm | k | v
deriving DecidableEq

/-- The coarse balance-only fact the flat constructor stores (mirror `WellBracketed interior`). -/
def Flat (_ : List Tok) : Prop := True

/-! ### The MERGED block — what the constructor's field type forced.

The original code had `A`'s group and `B`'s group SEPARATE (`B` referencing `A` one-directionally,
no `mutual`).  Adding `A.mapRec`, whose field `h_rec : B interior` references `B`, closes the cycle
`A → B → A`, so the two groups MUST become one `mutual` block.  Plain `/- -/`, not `/-- -/`, on
`mutual` (the Reflection-234 gotcha). -/
mutual
  /-- Mirror `RecSeqEntry`: the type being EXTENDED.  `map` is the flat (weak-role) constructor;
      `mapRec` is the NEW one storing the downstream body `B` — the edge that closed the cycle. -/
  inductive A : List Tok → Prop where
    | scalar : A [Tok.sc]
    | map (interior : List Tok) (h_flat : Flat interior) :
        A (Tok.om :: (interior ++ [Tok.cm]))
    | mapRec (interior : List Tok) (h_flat : Flat interior) (h_rec : B interior) :
        A (Tok.om :: (interior ++ [Tok.cm]))
  /-- Mirror `RecMapBody`: the DOWNSTREAM body, recursing back through `A` on its blocks.  In the
      real code this lived ~1500 lines after `A`'s group as a plain (non-`mutual`) inductive; the new
      `A.mapRec` field dragged it up into `A`'s `mutual` block. -/
  inductive B : List Tok → Prop where
    | mk (bk bv : List Tok) (hk : A bk) (hv : A bv) :
        B (Tok.k :: (bk ++ Tok.v :: bv))
end

/-! ### Safety witness — the moved declaration references nothing "in between". -/

/-- **The ordering-safety argument, made concrete.**  A projection on `B` (mirror
    `RecMapBody.toSafeBody`/`toWellBracketed`) that references ONLY `A` and `Flat` — both available at
    `A`'s ORIGINAL group site.  Because `B`'s declaration (and this structural recursion on it) need
    nothing defined in the intervening 1500 lines, moving `B`'s `inductive` up to join `A` breaks no
    use-ordering: every consumer of `B` sat after its old, downstream position — hence still after its
    new, earlier one.  (Structural recursion on `B` survives the merge: recursing on one inductive of
    a mutual family is what the joint recursor supports.) -/
theorem B.toFlat : {l : List Tok} → B l → Flat l
  | _, .mk _bk _bv _hk _hv => trivial

/-- The merge is real, not cosmetic: the cross-cycle `B → A.mapRec → B` is inhabited.  A depth-2
    witness `{ k: sc, v: { k: sc, v: sc } }`-shaped, whose outer value block is a nested `A.mapRec`
    storing the inner `B` — closing the cycle the merge exists to express.  Built bottom-up. -/
theorem cross_cycle_inhabited :
    B (Tok.k :: ([Tok.sc] ++ Tok.v ::
      (Tok.om :: ((Tok.k :: ([Tok.sc] ++ Tok.v :: [Tok.sc])) ++ [Tok.cm])))) :=
  -- inner body `{ k: sc, v: sc }`
  have inner : B (Tok.k :: ([Tok.sc] ++ Tok.v :: [Tok.sc])) :=
    B.mk [Tok.sc] [Tok.sc] A.scalar A.scalar
  -- inner value entry — `mapRec`, storing the inner body (the back-edge into `B`)
  have innerMap : A (Tok.om :: ((Tok.k :: ([Tok.sc] ++ Tok.v :: [Tok.sc])) ++ [Tok.cm])) :=
    A.mapRec _ trivial inner
  -- outer pair: key `sc`, value the nested map
  B.mk [Tok.sc] _ A.scalar innerMap

/-! ### The per-matcher cost was as R453 predicted — one verbatim arm per matcher. -/

/-- A projection BOTH map constructors satisfy (mirror the ~13 `RecSeqEntry` matchers): the new
    `mapRec` arm is a VERBATIM mirror of the `map` arm — reads the balance fact, ignores `h_rec`.
    This part of the cost held exactly as R453 priced it; the merge above was the ONLY surprise. -/
theorem A.nonempty {a : List Tok} (h : A a) : a ≠ [] := by
  cases h with
  | scalar => exact List.cons_ne_nil _ _
  | map interior _ => exact List.cons_ne_nil _ _
  | mapRec interior _ _ => exact List.cons_ne_nil _ _   -- verbatim mirror of the `map` arm

/-! ### The law, packaged. -/

/-- **The finding in one proposition.**  The cycle-closing field forces the merge (the `mutual` block
    above is the only way to inhabit `A.mapRec`'s `B`-typed field while `B` recurses back through
    `A`); the merge is safe (`B.toFlat` needs nothing "in between"); and the cross-cycle is real
    (`cross_cycle_inhabited`).  Sharpens [[ref-two-role-deliverable-blocks-shared-field]] (R453 priced
    the separate constructor but not the mutual-group MERGE its field type forces) and
    [[ref-additive-parallel-type-over-shared-edit]] (an additive constructor can have a non-additive
    structural consequence: pulling a downstream group into the block). -/
theorem cycle_field_forces_safe_merge :
    (∀ interior, Flat interior → B interior → A (Tok.om :: (interior ++ [Tok.cm])))   -- field inhabited only via the merge
    ∧ (∀ l, B l → Flat l)                                                             -- moved decl needs nothing in between
    ∧ B (Tok.k :: ([Tok.sc] ++ Tok.v ::                                              -- cross-cycle is real
        (Tok.om :: ((Tok.k :: ([Tok.sc] ++ Tok.v :: [Tok.sc])) ++ [Tok.cm])))) :=
  ⟨fun interior h hr => A.mapRec interior h hr, fun _ h => B.toFlat h, cross_cycle_inhabited⟩

end Tests.Reflections.ConstructorFieldForcesMutualGroupMerge
