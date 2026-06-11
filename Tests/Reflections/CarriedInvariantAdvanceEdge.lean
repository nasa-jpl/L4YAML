/-!
# Reflection 357 — a carried domain invariant needs one preservation edge per recursion MOVE; the descend+negation pair MASKS the missing ADVANCE (frame) edge

Self-contained (core Lean, no `L4YAML` import) toy model of the gap found while authoring the
emission-spine wrapper `nestedSeq_recseqentry_locate`.

A spine-walk recursion produces a deliverable AND carries a *domain invariant* — a stack/path
predicate threaded to each recursive call that bounds where the navigator may go (the real one:
`SeqPathAllSeq tokens off`, "every enclosing bracket frame from the root to the body base is a flow
SEQUENCE `[`, none a mapping `{`").  The invariant needs one PRESERVATION edge per recursion MOVE:

* **DESCEND** — step *into* a nested structure (a head opener PUSHes onto the stack);
* **ADVANCE** — step *sideways* past a consumed sibling segment (a balanced segment FRAMEs the stack).

The trap: a prior reflection (R337) authored the DESCEND edge (`seqPathAllSeq_descend`, the seq-head
push preserves) AND its NEGATION (`seqPathAllSeq_map_push_breaks`, the map-head push breaks).  That
pair *feels* exhaustive — a converse-style asymmetry, "going down through a seq preserves, going down
through a map breaks" — but it answers only the *descend* axis.  The ADVANCE (frame) edge is a third,
ORTHOGONAL obligation the descend pair never touches.  The wrapper's next-step pointer NAMED it
(crediting R337), but R337 never proved it.

And the missing edge is the EASY one: an advance is a whole-stack FRAME, not a push.  A balanced
segment returns the bracket fold to the SAME stack, so every conjunct of the invariant (definedness,
nonemptiness, all-`true`) transports VERBATIM — the frame is BLIND to the stack's contents.  This is
even more direct than the top-only projection's advance edge (which must re-read the head the frame
preserves).  That triviality is exactly why it was overlooked: the hard descend PUSH (which
overwrites the head, needs the opener token, and whose negation is a separate proof) absorbs all the
attention; the frame edge looks too easy to be a missing obligation.

This toy mirrors the real structure: a bracket fold (`os` pushes `true`, `om` pushes `false`, `cl`
pops, `it` neutral), the stack predicate `PathAllSeq` (nonempty + all-`true`), and the three edges.
`descend_preserves` is the seq-head push; `map_break` is the negation; `advance_preserves` is the
MISSING frame edge — the analogue of the real `seqPathAllSeq_advance` (which `WellTyped_frame`
discharges in one `rw`, mirroring `seqEnclosed_advance` but DROPPING the head re-read).
-/

namespace Tests.Reflections.CarriedInvariantAdvanceEdge

set_option autoImplicit false

/-- A toy bracket token: open-seq (push `true`), open-map (push `false`), a neutral content item, or
    a close (pop).  Mirrors `.flowSequenceStart` / `.flowMappingStart` / a scalar / a close. -/
inductive Tok | os | om | it | cl
deriving DecidableEq, Repr

/-- The fold step: `os` pushes `true`, `om` pushes `false`, `cl` pops the top, `it` is neutral.
    Mirrors `btStep`. -/
def bstep (s : List Bool) : Tok → List Bool
  | .os => true :: s
  | .om => false :: s
  | .cl => s.tail
  | .it => s

/-- Fold a token list onto a starting stack.  Mirrors `btFold`. -/
def bfold (l : List Tok) (s : List Bool) : List Bool := l.foldl bstep s

@[simp] theorem bfold_append (a b : List Tok) (s : List Bool) :
    bfold (a ++ b) s = bfold b (bfold a s) := by
  simp [bfold, List.foldl_append]

@[simp] theorem bfold_singleton (t : Tok) (s : List Bool) :
    bfold [t] s = bstep s t := rfl

/-- The stack after folding a prefix from empty.  Mirrors `btFold (some []) (take n)`. -/
def stk (l : List Tok) : List Bool := bfold l []

/-- The carried domain invariant: the path stack is nonempty and all-`true`.  Mirrors
    `SeqPathAllSeq`. -/
def PathAllSeq (pre : List Tok) : Prop :=
  stk pre ≠ [] ∧ (stk pre).all (· == true) = true

/-- A segment is BALANCED if it returns the fold to whatever stack it started on (a FRAME).  Mirrors
    `WellTyped` (the segment returns the bracket fold to depth `0`). -/
def Balanced (seg : List Tok) : Prop := ∀ s, bfold seg s = s

/-! ## The three edges -/

/-- **DESCEND edge** — a `.os` head PUSHES `true`; the stack grows by one `true`, so all-`true` and
    nonemptiness are preserved.  Mirrors `seqPathAllSeq_descend` (a PUSH that overwrites the head). -/
theorem descend_preserves (pre : List Tok) (h : PathAllSeq pre) :
    PathAllSeq (pre ++ [.os]) := by
  obtain ⟨_h_ne, h_all⟩ := h
  have hs : stk (pre ++ [.os]) = true :: stk pre := by simp [stk, bstep]
  refine ⟨by rw [hs]; simp, ?_⟩
  rw [hs, List.all_cons, h_all]; rfl

/-- **The NEGATION edge** — a `.om` head PUSHES `false`, breaking all-`true`.  Mirrors
    `seqPathAllSeq_map_push_breaks`.  Together with `descend_preserves` this is the converse-style
    pair that FEELS complete but covers only the DESCEND axis. -/
theorem map_break (pre : List Tok) (_h : PathAllSeq pre) :
    ¬ PathAllSeq (pre ++ [.om]) := by
  have hs : stk (pre ++ [.om]) = false :: stk pre := by simp [stk, bstep]
  rintro ⟨_, h_all⟩
  rw [hs, List.all_cons] at h_all
  simp at h_all

/-- **ADVANCE edge (the MISSING one)** — a BALANCED segment FRAMES: the whole stack is unchanged, so
    EVERY conjunct transports VERBATIM, the frame BLIND to the stack's contents.  Mirrors
    `seqPathAllSeq_advance` (`WellTyped_frame` returns the fold to the same stack) — even more direct
    than `descend_preserves`, which grows/inspects the stack.  This is the third, orthogonal edge the
    descend+negation pair never touches. -/
theorem advance_preserves (pre seg : List Tok) (h : PathAllSeq pre) (h_bal : Balanced seg) :
    PathAllSeq (pre ++ seg) := by
  have hs : stk (pre ++ seg) = stk pre := by
    show bfold (pre ++ seg) [] = bfold pre []
    rw [bfold_append, h_bal]
  rw [PathAllSeq, hs]; exact h

/-- A balanced segment: `[os, it, cl]` (push `true`, neutral, pop → back to the start stack). -/
theorem balanced_oitc : Balanced [.os, .it, .cl] := by intro s; simp [bfold, bstep]

/-- A neutral segment is balanced. -/
theorem balanced_it : Balanced [.it] := by intro s; rfl

/-! ## The MASKING made literal — an advance segment is NOT a push

The descend edge (a push) and its negation cannot SUPPLY the advance: an advance segment returns to
the START stack rather than pushing onto it.  The frame is BLIND to the stack — it preserves even a
non-all-`true` one — whereas a descend push genuinely CHANGES the stack. -/

-- the frame preserves even a non-all-`true` stack (blind to contents)...
#guard bfold [.os, .it, .cl] [false] == [false]
-- ...and the identity stack, and a true stack — always the input verbatim:
#guard bfold [.os, .it, .cl] [] == []
#guard bfold [.os, .it, .cl] [true] == [true]
-- ...whereas a single descend PUSH genuinely changes the stack:
#guard bfold [.os] [false] == [true, false]

/-! ## Concrete witnesses -/

example : PathAllSeq [.os] := ⟨by decide, by decide⟩
-- DESCEND: push another seq opener.
example : PathAllSeq ([.os] ++ [.os]) := descend_preserves [.os] ⟨by decide, by decide⟩
-- ADVANCE: frame past a balanced sibling segment — the edge that did NOT exist.
example : PathAllSeq ([.os] ++ [.os, .it, .cl]) :=
  advance_preserves [.os] [.os, .it, .cl] ⟨by decide, by decide⟩ balanced_oitc
-- NEGATION: a map opener breaks the invariant.
example : ¬ PathAllSeq ([.os] ++ [.om]) := map_break [.os] ⟨by decide, by decide⟩

end Tests.Reflections.CarriedInvariantAdvanceEdge
