/-!
# Reflection 384 — CARVE the leaf lemmas of a dispatch to the ELIMINATOR's output shape, so the
assembler is a GLUE-FREE fan-out (no `rw`/`simp`/reorder/`.symm`)

Self-contained core-Lean toy of L4YAML BRICK D's `h_step` assembly
(`nestedSeq_recseqentry_locate_hstep`): the fan-out that folds the eight pre-carved
`recseqbody_head_or_cons × cases h_e` cells into the one hypothesis `seqLocateRecDriver` consumes.

When you factor a K-way (or 2×K) dispatch into K leaf lemmas BEFORE writing the assembler, you get to
CHOOSE each leaf's hypotheses.  Choose them to be EXACTLY what the destructor hands you:

* each leaf's leading equation `h_eq : subject = <pattern>` should be the LITERAL index the constructor
  carries — when `cases h_e` eliminates an indexed family `Entry e`, it auto-reverts the hyps that
  mention the index `e` (here `h_eq : subject = e`), substitutes the constructor index, and re-intros,
  so `h_eq` re-emerges as `subject = <ctor index>`.  Carve the leaf to THAT, and `exact <leaf> … h_eq`
  needs no rewriting.  ORIENTATION counts: the splitter yields `subject = e`, so leaves take
  `subject = <pattern>`, never `<pattern> = subject` (the latter costs a `.symm` per call).
* sibling hyps that do NOT depend on the eliminated index (here CONS's `h_r`) survive `cases h_e`
  un-reverted, keep their names, and slot straight into the cell calls.

So the assembler is the INVERSE of the carve: `intro; <splitter>; cases h_e with | C flds => exact
leaf_C <ctx> h_eq <flds>` — one `exact` per cell, zero glue.  The carve is the design work; the
assembler is bookkeeping.

POSITIVE: `assemble` — glue-free, one `exact` per cell.  NEGATIVE: `assemble_with_glue` — one leaf
mis-carved (equation flipped) forces a `.symm` token at its call site.
-/

namespace Tests.Reflections.CarveLeavesToEliminatorOutput

set_option autoImplicit false

/-- A two-constructor indexed family mirroring `RecSeqEntry` (scalar / wrap). -/
inductive Entry : List Nat → Prop where
  | scalar (n : Nat) : Entry [n]
  | wrap (interior : List Nat) : Entry (0 :: (interior ++ [9]))

/-- A body is one entry (`single`) or an entry followed by a tail (`cons`) — mirrors `RecSeqBody`. -/
inductive Body : List Nat → Prop where
  | single (e : List Nat) (h_e : Entry e) : Body e
  | cons (e r : List Nat) (h_e : Entry e) (h_r : Body r) : Body (e ++ r)

/-- The HEAD-or-CONS splitter — mirrors `recseqbody_head_or_cons`.  `single`'s bare-var index keeps
    the target `l` under `cases` (the R331 gotcha), so `l = e` is `rfl` with `e := l`. -/
theorem head_or_cons {l : List Nat} (h : Body l) :
    (∃ e, Entry e ∧ l = e)
    ∨ (∃ e r, Entry e ∧ Body r ∧ l = e ++ r) := by
  cases h with
  | single _e h_e => exact Or.inl ⟨l, h_e, rfl⟩
  | cons e r h_e h_r => exact Or.inr ⟨e, r, h_e, h_r, rfl⟩

/-! ## POSITIVE — leaves carved to the destructor's OUTPUT shape, `h_eq : l = <ctor index>`.

Each leaf's `h_eq` is exactly the equation the matching `cases` arm substitutes; the CONS leaves also
take the index-independent sibling `h_r`. -/

theorem leaf_scalar_single (l : List Nat) (n : Nat) (h_eq : l = [n]) : l ≠ [] := by
  rw [h_eq]; simp
theorem leaf_wrap_single (l interior : List Nat) (h_eq : l = 0 :: (interior ++ [9])) : l ≠ [] := by
  rw [h_eq]; simp
theorem leaf_scalar_cons (l r : List Nat) (n : Nat) (_h_r : Body r) (h_eq : l = [n] ++ r) :
    l ≠ [] := by rw [h_eq]; simp
theorem leaf_wrap_cons (l r interior : List Nat) (_h_r : Body r)
    (h_eq : l = (0 :: (interior ++ [9])) ++ r) : l ≠ [] := by rw [h_eq]; simp

/-- POSITIVE — the GLUE-FREE assembler: `head_or_cons` then `cases h_e`, one `exact <leaf> … h_eq`
    per cell.  No `rw`/`simp`/reorder: each cell's `h_eq` is EXACTLY the equation `cases`'s
    index-substitution produces, and the CONS sibling `h_r` (independent of the eliminated index `e`)
    survives `cases h_e` and slots straight in.  This is the inverse of the carve. -/
theorem assemble (l : List Nat) (h : Body l) : l ≠ [] := by
  rcases head_or_cons h with ⟨e, h_e, h_eq⟩ | ⟨e, r, h_e, h_r, h_eq⟩
  · cases h_e with
    | scalar n => exact leaf_scalar_single l n h_eq
    | wrap interior => exact leaf_wrap_single l interior h_eq
  · cases h_e with
    | scalar n => exact leaf_scalar_cons l r n h_r h_eq
    | wrap interior => exact leaf_wrap_cons l r interior h_r h_eq

/-! ## NEGATIVE — a leaf carved with the equation FLIPPED forces a `.symm` glue token per call. -/

theorem leaf_scalar_single_flipped (l : List Nat) (n : Nat) (h_eq : [n] = l) : l ≠ [] := by
  rw [← h_eq]; simp

/-- NEGATIVE — the SAME assembly, but the scalar-single arm routes through the flipped leaf.  The bare
    `exact leaf_scalar_single_flipped l n h_eq` would FAIL (`h_eq : l = [n]` ≠ `[n] = l`); it compiles
    only with the `.symm` glue token.  One mis-oriented leaf ⇒ one glue token at every call site — the
    cost the carve-to-output discipline avoids (orientation is part of "the destructor's output shape":
    the splitter yields `l = e`, so leaves must take `l = <pattern>`, not `<pattern> = l`). -/
theorem assemble_with_glue (l : List Nat) (h : Body l) : l ≠ [] := by
  rcases head_or_cons h with ⟨e, h_e, h_eq⟩ | ⟨e, r, h_e, h_r, h_eq⟩
  · cases h_e with
    | scalar n => exact leaf_scalar_single_flipped l n h_eq.symm   -- ← glue: `.symm`
    | wrap interior => exact leaf_wrap_single l interior h_eq
  · cases h_e with
    | scalar n => exact leaf_scalar_cons l r n h_r h_eq
    | wrap interior => exact leaf_wrap_cons l r interior h_r h_eq

end Tests.Reflections.CarveLeavesToEliminatorOutput
