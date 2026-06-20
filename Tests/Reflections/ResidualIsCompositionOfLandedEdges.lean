/-!
# Reflection 469 — a residual named "preserve invariant `I` across a single located edge `X`"
# can hide a FRAME-TO-REACH component: the located position is NOT adjacent to the window origin
# (sibling structure intervenes), so the edge is `EDGE_X-at-the-locator ∘ FRAME-origin→locator`.
# Both component edges are usually already landed — a SIBLING producer may already compose the very
# same two — so PROBE for the composition before authoring a "new edge".

Self-contained (core Lean, no `L4YAML` import) toy modelling the seq carrier↔recursion
co-construction's `SeqPathAllSeq` descend edge.

Context (the real situation).  `seqWindow_safeBodyUnit`'s NESTED arm (the carrier co-construction's
within-window `h_safe` source) needs `SeqPathAllSeq tokens (lo - 1)` — every enclosing frame of the
window is a flow SEQUENCE `[`.  The joint width induction, descending from a bracket body into a
CHILD bracket body, must re-establish that path fact at the child opener.  The blueprint named this
"the btFold-push preservation of `SeqPathAllSeq` across a located `[`" — i.e. a presumed NEW edge.

The de-risk found it is NOT a new edge.  Reaching the child opener `n` from the parent's path key is:
* a PUSH across the located opener `[` at `k` — `seqPathAllSeq_descend` (R337), ALREADY landed; then
* a FRAME across the earlier sibling entries `[k+1, n)` — the child opener need not be the FIRST
  entry — `seqPathAllSeq_advance` (R357), ALREADY landed.
The "single located `[`" description hid the FRAME: the located position `n` is not adjacent to `k`.
And both edges were ALREADY composed for the NAVIGATOR (`nestedSeq_recseqentry_locate_descend_step`
/ `_advance_step`) — so the joint CARRIER induction's descend edge is the SAME composition, keyed for
the carrier.  The brick `seqPathAllSeq_into_child` is the one-line fusion; no new edge owed.

This toy reproduces the STRUCTURE:

* `Tok`/`step`/`fold` — a typed bracket stack (`[` pushes `true`, `]` pops a matching `true`, `,` is
  identity), the `btStep`/`btFold` analog.
* `AllSeq pre` — the path invariant (the fold of the prefix is `some s`, nonempty, all-`true`), the
  `SeqPathAllSeq` analog.
* `allSeq_push` — THE LOCATED EDGE (crossing a `[` pushes `true`), the `seqPathAllSeq_descend` analog.
* `Balanced`/`fold_frame`/`allSeq_frame` — THE FRAME (a balanced sibling run returns the stack
  unchanged), the `WellTyped`/`seqPathAllSeq_advance` analog.
* `allSeq_into_child` — THE COMPOSITE (`allSeq_frame ∘ allSeq_push`): the residual, discharged with NO
  new edge — just the two landed edges fused.  The `seqPathAllSeq_into_child` analog.
* A NEGATIVE witnessing the FRAME is load-bearing: drop `Balanced` and an unbalanced "sibling" pops
  out of the enclosing bracket, breaking `AllSeq` — push-at-origin alone cannot reach the child opener.
-/

namespace ResidualIsCompositionOfLandedEdges

set_option autoImplicit false

/-- A minimal typed bracket alphabet: `[` (`lbrack`), `]` (`rbrack`), `,` (`comma`). -/
inductive Tok | lbrack | rbrack | comma
  deriving DecidableEq, Repr

/-- The typed bracket stack step (the `btStep` analog): `[` pushes `true`, `]` pops a matching `true`
    (else `none`), `,` is identity. -/
def step (s : List Bool) (t : Tok) : Option (List Bool) :=
  match t with
  | .lbrack => some (true :: s)
  | .rbrack => match s with | true :: s' => some s' | _ => none
  | .comma  => some s

/-- The fold from a starting stack (the `btFold` analog). -/
def fold (s0 : Option (List Bool)) (l : List Tok) : Option (List Bool) :=
  l.foldl (fun a t => a.bind (fun s => step s t)) s0

/-- The fold splits over an append (mirrors `btFold_append`). -/
theorem fold_append (s0 : Option (List Bool)) (a b : List Tok) :
    fold s0 (a ++ b) = fold (fold s0 a) b := by
  simp [fold, List.foldl_append]

/-- A `some`-started fold steps through the head (mirrors `btFold_cons_some`). -/
theorem fold_cons_some (s : List Bool) (t : Tok) (l : List Tok) :
    fold (some s) (t :: l) = fold (step s t) l := by
  simp [fold]

/-- **The PATH invariant** (toy analog of `SeqPathAllSeq tokens (prefix length)`): the prefix folds to
    a nonempty all-`true` stack — every enclosing frame is a sequence `[`. -/
def AllSeq (pre : List Tok) : Prop :=
  ∃ s, fold (some []) pre = some s ∧ s ≠ [] ∧ s.all (· == true) = true

/-- **THE LOCATED EDGE — the PUSH across a `[`** (toy analog of `seqPathAllSeq_descend`, R337).
    Crossing the opener pushes a `true`, so the stack stays nonempty and all-`true`. -/
theorem allSeq_push (pre : List Tok) (h : AllSeq pre) : AllSeq (pre ++ [Tok.lbrack]) := by
  obtain ⟨s, hf, _hne, hall⟩ := h
  refine ⟨true :: s, ?_, by simp, ?_⟩
  · rw [fold_append, hf]; rfl
  · rw [List.all_cons, hall]; rfl

/-- **Balanced (Dyck) sibling runs** — the FRAME's domain: an empty run, a separator, a complete
    bracket, or a concatenation.  The `WellTyped` analog. -/
inductive Balanced : List Tok → Prop
  | nil : Balanced []
  | comma : Balanced [Tok.comma]
  | bracket (inner : List Tok) : Balanced inner → Balanced (Tok.lbrack :: inner ++ [Tok.rbrack])
  | app (a b : List Tok) : Balanced a → Balanced b → Balanced (a ++ b)

/-- **THE FRAME — a balanced run returns the fold to the SAME stack** (toy analog of `WellTyped_frame`,
    the engine of `seqPathAllSeq_advance`, R357).  Structural induction on the Dyck word: a bracket
    pushes a `true` its matching `]` pops, leaving the stack below untouched. -/
theorem fold_frame (seg : List Tok) (h : Balanced seg) : ∀ s, fold (some s) seg = some s := by
  induction h with
  | nil => intro s; rfl
  | comma => intro s; rfl
  | bracket inner _hb ih =>
      intro s
      -- `[ :: inner ++ ]` parses as `([ :: inner) ++ [ ] ]`; push `true`, frame `inner`, pop `true`.
      rw [fold_append, fold_cons_some]
      simp only [step]
      rw [ih (true :: s)]
      rfl
  | app a b _ha _hb iha ihb =>
      intro s; rw [fold_append, iha, ihb]

/-- **THE FRAME on the path invariant** (toy analog of `seqPathAllSeq_advance`): a balanced sibling run
    appended after the path preserves `AllSeq` — the stack is literally unchanged. -/
theorem allSeq_frame (pre seg : List Tok) (h : AllSeq pre) (hbal : Balanced seg) :
    AllSeq (pre ++ seg) := by
  obtain ⟨s, hf, hne, hall⟩ := h
  exact ⟨s, by rw [fold_append, hf, fold_frame seg hbal s], hne, hall⟩

/-- **THE COMPOSITE — the residual, discharged with NO new edge** (toy analog of
    `seqPathAllSeq_into_child`).  The child opener `n` sits after the located `[` AND after earlier
    sibling entries `sibs`; so the path at `n` = `allSeq_frame` (across `sibs`) ∘ `allSeq_push`
    (across the `[`).  Two LANDED edges fused — the "single located `[`" residual is a composition. -/
theorem allSeq_into_child (pre sibs : List Tok) (h : AllSeq pre) (hbal : Balanced sibs) :
    AllSeq (pre ++ Tok.lbrack :: sibs) := by
  have hpush : AllSeq (pre ++ [Tok.lbrack]) := allSeq_push pre h
  have heq : pre ++ Tok.lbrack :: sibs = (pre ++ [Tok.lbrack]) ++ sibs := by simp
  rw [heq]
  exact allSeq_frame (pre ++ [Tok.lbrack]) sibs hpush hbal

/-- POSITIVE — the root opener alone is on the all-seq path (stack `[true]`). -/
example : AllSeq [Tok.lbrack] := ⟨[true], rfl, by simp, by decide⟩

/-- POSITIVE — the composite reaches the child opener PAST a complete sibling entry `[] ,` (the FRAME
    bridges positions 1→4 that the bare PUSH at the origin cannot).  `#guard`-checked fold value. -/
example : fold (some []) ([Tok.lbrack] ++ Tok.lbrack :: [Tok.lbrack, Tok.rbrack, Tok.comma])
    = some [true, true] := by decide

/-- POSITIVE — and that prefix is `AllSeq`, produced by the composite from `AllSeq [lbrack]` and the
    balanced sibling `[ [], ] = [lbrack, rbrack, comma]`. -/
example : AllSeq ([Tok.lbrack] ++ Tok.lbrack :: [Tok.lbrack, Tok.rbrack, Tok.comma]) :=
  allSeq_into_child [Tok.lbrack] [Tok.lbrack, Tok.rbrack, Tok.comma]
    ⟨[true], rfl, by simp, by decide⟩
    (Balanced.app [Tok.lbrack, Tok.rbrack] [Tok.comma]
      (by have := Balanced.bracket [] Balanced.nil; simpa using this)
      Balanced.comma)

/-- NEGATIVE — the FRAME's `Balanced` hypothesis is LOAD-BEARING: an UNBALANCED "sibling" `]` pops out
    of the enclosing bracket, emptying the stack, so `AllSeq` FAILS — push-at-origin alone cannot reach
    a later child opener across arbitrary intervening tokens. -/
example : ¬ AllSeq ([Tok.lbrack] ++ Tok.lbrack :: [Tok.rbrack, Tok.rbrack]) := by
  rintro ⟨s, hf, hne, _⟩
  -- fold (some []) [lbrack, lbrack, rbrack, rbrack] = some []  (empty stack), contradicting `s ≠ []`.
  have : fold (some []) ([Tok.lbrack] ++ Tok.lbrack :: [Tok.rbrack, Tok.rbrack]) = some [] := by decide
  rw [this] at hf
  exact hne (Option.some.inj hf).symm

end ResidualIsCompositionOfLandedEdges
