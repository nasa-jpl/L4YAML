/-!
# Recursive deliverable, project-to-flat-first — runnable demonstration

A self-contained (core Lean, no `L4YAML` import) illustration of the proof-engineering
principles documented in `Blueprint/08-initiative-4-intrinsic-foundations.md`, **Reflections 234
and 235** — the *recursive* generalization of the consumer-joint-before-producer family
(`ReductionByImport` / `ConvergentReduction` / `ParametricAssemblerExtraction`), plus its DRY
continuation: the single-level descent step that CONSUMES the recursive deliverable.

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

/-! ## DRY continuation — the single-level DESCENT step (Reflection 235).

Once the recursive deliverable + flat projection exist (above), the next atom toward CONSUMING it
(the *descent-locator*: "from `RecBody (outer)`, extract a flat body at any nested sub-part") is the
irreducible **"descend one nesting level"** step.  Land it FIRST, in isolation, before the positional
bridge or the outer recursion exist, because the **single-level constructor case-split is
self-contained**: `cases` on the deliverable's `RecEntry` constructors IS the case analysis — the
wanted recursion witness falls out of one constructor (`brk`), the impossible shapes are killed by a
head/shape mismatch (`leaf`), and the empty interior is its own witness (`brkEmpty`).

**The key move: pick the step's conclusion type to BE the producer-contract split you already proved.**
`RecEntry.interior` returns `RecBody interior ∨ interior = []` — exactly the non-empty / empty
dichotomy the downstream stage already branches on (the real `lo < hi` / `lo = hi` split, Reflection
233).  So the atom plugs in with ZERO glue (`descendRoute`): the non-empty disjunct goes to the flat
consumer via `toFlatBody`, the empty disjunct stays empty for the vacuous leaf to handle. -/

/-- Append-singleton injectivity (core Lean): `a ++ [x] = b ++ [y] → a = b ∧ x = y` (via `reverse` +
    `List.reverse_inj`).  Reads a bracket entry's `interior` off the `op :: (interior ++ [cl])`
    constructor index — the toy mirror of the real `append_singleton_inj`. -/
theorem append_singleton_inj {a b : List Tok} {x y : Tok}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hr
  injection hr with hxy har
  exact ⟨List.reverse_inj.mp har, hxy⟩

/-- **Single-level descent step** (toy mirror of `RecSeqEntry.seq_interior`).  A bracket entry
    `op :: (interior ++ [cl])` recorded in the deliverable (head `op = [`) has interior EITHER a
    `RecBody` (the `brk` recursion witness, recovered structurally) OR empty (`brkEmpty`).  The
    `leaf` constructor is ruled out by the `[`-head guard `h_op` (head `leaf ≠ [`) — the toy's single
    `leaf` mismatch stands in for BOTH real rule-outs: `scalar` (ruled out by shape) and `map` (ruled
    out by head, the mechanic exercised here).  The disjunction IS the downstream split — chosen, not
    incidental. -/
theorem RecEntry.interior {e interior : List Tok} {op cl : Tok}
    (h : RecEntry e) (h_eq : e = op :: (interior ++ [cl])) (h_op : op = Tok.opn) :
    RecBody interior ∨ interior = [] := by
  cases h with
  | leaf =>
      -- `e = [leaf]`: head `leaf` clashes with the `[`-head guard (the `map`-style rule-out).
      injection h_eq with h1 _h2
      rw [h_op] at h1
      exact absurd h1 (by decide)
  | brkEmpty =>
      -- empty bracket pair `[ ]`: interior forced empty (the `lo = hi` disjunct).
      right
      injection h_eq with _h1 h2
      simp only [List.nil_append] at h2
      exact (append_singleton_inj h2.symm).1
  | brk interior' h_wb h_rec =>
      -- the recursive interior witness, transported across `interior' = interior`.
      left
      injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h_rec

/-- **POSITIVE — recover the recursion.**  Descending into a nested bracket entry `[ x ]` recovers
    its interior's `RecBody` (the left disjunct): the recursion witness, structurally recovered. -/
theorem example_descend_nonempty : RecBody [Tok.leaf] := by
  have h_brk : RecEntry [Tok.opn, Tok.leaf, Tok.cls] :=
    RecEntry.brk [Tok.leaf] (by decide) (RecBody.single _ (by decide) RecEntry.leaf)
  rcases RecEntry.interior (e := [Tok.opn, Tok.leaf, Tok.cls]) (interior := [Tok.leaf])
      (op := Tok.opn) (cl := Tok.cls) h_brk rfl rfl with h | h
  · exact h
  · exact absurd h (by decide)   -- the empty disjunct is impossible for `[ x ]`

/-- **EMPTY — route to the leaf.**  The empty bracket entry `[ ]` descends to the RIGHT disjunct
    `interior = []` — the toy `lo = hi` case, handled with no recursion witness (the vacuous
    empty-body leaf, never asked for a flat body). -/
theorem example_descend_empty : RecBody [] ∨ ([] : List Tok) = [] :=
  RecEntry.interior (e := Tok.opn :: ([] ++ [Tok.cls])) (interior := [])
    (op := Tok.opn) (cl := Tok.cls) RecEntry.brkEmpty rfl rfl

/-- **The conclusion type IS the downstream split — zero-glue routing.**  Because `RecEntry.interior`
    returns exactly the dichotomy the next stage branches on, it plugs in with no glue: `Or.imp` sends
    the non-empty disjunct through the flat projection `RecBody.toFlatBody` and leaves the empty
    disjunct untouched for the vacuous leaf.  This is the whole point of choosing the conclusion type
    to match the split rather than returning a bare `RecBody` and re-casing downstream. -/
theorem descendRoute {e interior : List Tok} {op cl : Tok}
    (h : RecEntry e) (h_eq : e = op :: (interior ++ [cl])) (h_op : op = Tok.opn) :
    FlatBody interior ∨ interior = [] :=
  (RecEntry.interior h h_eq h_op).imp RecBody.toFlatBody id

#guard decide (tot [Tok.leaf] = 0)   -- the recovered nested interior is balanced

end RecursiveDeliverableProjectToFlat
