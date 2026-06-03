/-!
# Recursive deliverable, project-to-flat-first — runnable demonstration

A self-contained (core Lean, no `L4YAML` import) illustration of the proof-engineering
principle documented in `Blueprint/08-initiative-4-intrinsic-foundations.md`, Reflection 234
— the *recursive* generalization of the consumer-joint-before-producer family
(`ReductionByImport` / `ConvergentReduction` / `ParametricAssemblerExtraction`).

**The principle.** When a frontier needs "do X at every nesting level" and a *descent* must treat
sub-parts the way the consumer treats the whole, the instinct is a token-level recursion that
re-derives the consumer's FLAT invariant at each sub-part.  Check that instinct against a concrete
identity first: **does the flat invariant actually regenerate a sub-part's structure?**  Often it
does NOT — the L4YAML wall was `SafeBody → WellBracketed` is *false* (`EntrySafe` constrains the
running balance only at separator positions, so a non-separator prefix could dip negative).  A flat
deliverable is then too weak: to hand a descent a nested interior as a structured witness, that
structure must already be *recorded*, not re-derived.  So make the producer's deliverable a
**recursive** inductive — and land it safely in ONE increment, without committing to the producer or
the descent, by proving it **projects to the flat form the consumer already accepts**, using only the
non-recursive fields (so the projection is robust to later constructor tweaks and to bottoming-out a
not-yet-needed branch).

This file makes all the moving parts runnable on a toy bracket language:
* **NEGATIVE** — the flat per-entry obligation `Balanced` does NOT imply the full bracket invariant
  `WB` (`clsOpn` is `Balanced` but `¬ WB`): the toy stand-in for `SafeBody ↛ WellBracketed`, the
  reason a flat body cannot be descended into.
* **POSITIVE** — the recursive deliverable `RecBody`/`RecEntry` *records* each bracket entry's
  interior (`WB` + a recursive `RecBody`), and `RecBody.toFlatBody` projects it to the flat `FlatBody`
  a downstream lemma accepts, via only the non-recursive `WB.1` total-balance field.

Three mechanical Lean facts the real `RecSeqBody` hit, reproduced here: (1) a doc comment `/-- … -/`
cannot precede `mutual` — use a section comment `/-! … -/`; (2) a recursive occurrence cannot sit
under `Or` ("invalid nested inductive datatype 'Or'"), so the empty interior is a SEPARATE
constructor (`brkEmpty`), not `interior = [] ∨ RecBody interior`; (3) `induction` is rejected on a
mutual inductive — the projection is term-mode structural recursion.

Run it: open in the IDE (the `#eval`s render in the infoview) or
`lake build Tests.Reflections.RecursiveDeliverableProjectToFlat` (the `#guard`s fail the build if
any expectation is wrong).
-/

namespace RecursiveDeliverableProjectToFlat

/-- Toy tokens: opener `[`, closer `]`, separator `,`, leaf value `x`. -/
inductive Tok | opn | cls | sep | leaf
deriving DecidableEq, Repr

/-- Bracket delta: `+1` open, `−1` close, `0` otherwise. -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _    => 0

/-- Total bracket balance of a token list (`pbalance` in the real proof). -/
def tot (e : List Tok) : Int := (e.map delta).sum

theorem tot_append (a b : List Tok) : tot (a ++ b) = tot a + tot b := by
  simp [tot, List.map_append, List.sum_append]

theorem tot_cons (t : Tok) (l : List Tok) : tot (t :: l) = delta t + tot l := by
  simp [tot]

/-- Running balance of the first `n` tokens. -/
def bal (e : List Tok) (n : Nat) : Int := tot (e.take n)

/-! ## NEGATIVE — the flat per-entry obligation cannot regenerate bracket structure.

`Balanced` (the flat stand-in for `EntrySafe`/`SafeBody` data) asks only that an entry be balanced
overall.  `WB` (the stand-in for `WellBracketed`) asks every prefix to be `≥ 0`.  `abbrev`, not
`def`, so `decide` can synthesize the bounded-∀ `Decidable` instance. -/

/-- Flat per-entry obligation (toy `EntrySafe`/`SafeBody` data): merely balanced overall. -/
abbrev Balanced (e : List Tok) : Prop := tot e = 0

/-- Full bracket invariant (toy `WellBracketed`): balanced AND every prefix `≥ 0` (Dyck). -/
abbrev WB (e : List Tok) : Prop :=
  tot e = 0 ∧ ∀ i, i < e.length + 1 → bal e i ≥ 0

/-- The discriminating witness: `] [` — balanced overall, but the prefix after `]` is `−1`. -/
def clsOpn : List Tok := [.cls, .opn]

-- `] [` satisfies the flat obligation but NOT the full bracket invariant: `Balanced ↛ WB`.
-- This is the toy `SafeBody ↛ WellBracketed` — the reason a flat deliverable cannot be descended.
#guard  decide (Balanced clsOpn)   -- true  : tot = 0
#guard !decide (WB clsOpn)         -- false : bal 1 = -1

theorem clsOpn_Balanced : Balanced clsOpn := by decide
theorem clsOpn_not_WB : ¬ WB clsOpn := by decide

/-! ## The recursive deliverable — records each nested entry's interior structure.

`RecBody` is a body of entries separated by `,`; each `RecEntry` is a `leaf`, an EMPTY pair `[ ]`
(`brkEmpty`), or a bracket pair `[ interior ]` carrying BOTH its `WB interior` and — recursively —
the interior's own `RecBody`.  That recursive field is exactly what `Balanced`/`FlatBody` cannot
carry (the NEGATIVE above), and exactly what a descent into a nested entry needs. -/
mutual
  inductive RecBody : List Tok → Prop where
    | single (e : List Tok) (h_ne : e ≠ []) (h_e : RecEntry e) : RecBody e
    | cons (e : List Tok) (s : Tok) (rest : List Tok) (h_ne : e ≠ [])
        (h_e : RecEntry e) (h_sep : s = Tok.sep) (h_rest : RecBody rest) :
        RecBody (e ++ s :: rest)
  inductive RecEntry : List Tok → Prop where
    | leaf : RecEntry [Tok.leaf]
    | brkEmpty : RecEntry (Tok.opn :: ([] ++ [Tok.cls]))
    | brk (interior : List Tok) (h_wb : WB interior) (h_rec : RecBody interior) :
        RecEntry (Tok.opn :: (interior ++ [Tok.cls]))
end

/-! ## The flat consumer form — what a downstream lemma keyed on flatness accepts. -/

/-- The flat body form (toy `SafeBody`): entries that are merely `Balanced`, separated by `,`. -/
inductive FlatBody : List Tok → Prop where
  | single (e : List Tok) (h_ne : e ≠ []) (h_e : Balanced e) : FlatBody e
  | cons (e : List Tok) (s : Tok) (rest : List Tok) (h_ne : e ≠ [])
      (h_e : Balanced e) (h_sep : s = Tok.sep) (h_rest : FlatBody rest) :
      FlatBody (e ++ s :: rest)

/-! ## POSITIVE — the recursive deliverable projects to the flat form. -/

/-- A recursive entry is `Balanced` (the flat per-entry obligation) — via only the non-recursive
    `WB.1` total-balance field, never `h_rec`, so the projection is robust (it would still hold if
    `brk` later bottomed out at `WB` alone, as the real `map` case does). -/
theorem RecEntry.toBalanced {e : List Tok} (h : RecEntry e) : Balanced e := by
  cases h with
  | leaf => decide
  | brkEmpty => decide
  | brk interior h_wb _ =>
      show tot (Tok.opn :: (interior ++ [Tok.cls])) = 0
      rw [tot_cons, tot_append, h_wb.1]
      simp [delta, tot]

/-- **Flat projection.**  A `RecBody` is in particular the flat `FlatBody` a downstream lemma keyed
    on flatness accepts — term-mode structural recursion (`induction` is rejected on a mutual
    inductive); the recursive interiors are discarded. -/
theorem RecBody.toFlatBody : {l : List Tok} → RecBody l → FlatBody l
  | _, .single e h_ne h_e => FlatBody.single e h_ne h_e.toBalanced
  | _, .cons e s rest h_ne h_e h_sep h_rest =>
      FlatBody.cons e s rest h_ne h_e.toBalanced h_sep h_rest.toFlatBody

/-! ## A concrete nested deliverable, and its projection. -/

/-- `[ x , [ x ] ]` as a `RecBody`: an outer body of two entries (a leaf and a bracket whose interior
    `x` recurses).  The nested structure is RECORDED — readable off the constructors. -/
theorem example_nested :
    RecBody [Tok.opn, Tok.leaf, Tok.sep, Tok.opn, Tok.leaf, Tok.cls, Tok.cls] := by
  have h_inner : RecBody [Tok.leaf] := RecBody.single _ (by decide) RecEntry.leaf
  have h_brk : RecEntry [Tok.opn, Tok.leaf, Tok.cls] :=
    RecEntry.brk [Tok.leaf] (by decide) h_inner
  have h_body : RecBody [Tok.leaf, Tok.sep, Tok.opn, Tok.leaf, Tok.cls] :=
    RecBody.cons [Tok.leaf] Tok.sep [Tok.opn, Tok.leaf, Tok.cls] (by decide)
      RecEntry.leaf rfl (RecBody.single _ (by decide) h_brk)
  exact RecBody.single _ (by decide) (RecEntry.brk _ (by decide) h_body)

/-- The same recursive value projects to the flat form the consumer accepts — project-to-flat
    applied to a concrete deliverable.  The `FlatBody` keeps only the per-entry `Balanced` data;
    the nested `RecBody` that `example_nested` recorded is gone. -/
theorem example_nested_flat :
    FlatBody [Tok.opn, Tok.leaf, Tok.sep, Tok.opn, Tok.leaf, Tok.cls, Tok.cls] :=
  example_nested.toFlatBody

#guard decide (tot [Tok.opn, Tok.leaf, Tok.sep, Tok.opn, Tok.leaf, Tok.cls, Tok.cls] = 0)

end RecursiveDeliverableProjectToFlat
