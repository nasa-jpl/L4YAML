/-!
# Reflection 294 — a threaded guard PRUNES the case tree

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`recseqentry_window_dispatch`: the per-window head-shape dispatch that the four dependency-map
revisions wrote as a FOUR-way split (scalar / empty `[ ]` / `{ … }` / `[ … ]`) is actually a
THREE-way split, because the deep content guard threaded through the recursion makes the
empty-bracket leaf unreachable.

The dispatch reads the head off a classifier (`isContentStart`) that has only THREE shapes — never
the closer.  The empty bracket `[ ]` has no shape of its own: the guard's `OpenerContentStart` field
asserts the token after an opener is content-start, so a `[`-headed window never has `]` next.  The
empty case is therefore EXCLUDED, not handled — it folds into the nested-`[ … ]` branch.

The lesson (R294): a threaded recursion guard is not only a source of premises — it PRUNES the case
tree.  A guard strengthened for one purpose (content provenance, here) can be strong enough to delete
a whole branch the deliverable's type still anticipates.  The number of structural moves that
complete a recursion is fewer than the constructor count when a threaded invariant rules a
constructor out.

* POSITIVE — `dispatch` is a TOTAL function over the THREE content-start heads (its `sclose` case is
  vacuous, `isContentStart sclose = False`); `empty_excluded` shows that under the guard a
  `sopen`-headed window never has `sclose` next.
* NEGATIVE — `not_content_start_sclose` shows the closer is not a content-start head (so the dispatch
  never classifies it); `empty_reachable_without_guard` shows the empty bracket IS a genuine fourth
  shape absent the guard — so it is the GUARD, not the token type, that prunes the branch.
-/

namespace Tests.Reflections.ThreadedGuardPrunesCaseTree

set_option autoImplicit false

/-- Toy token stream: a scalar, the two sequence brackets, and a mapping opener. -/
inductive Tok | scal | sopen | sclose | mopen
  deriving DecidableEq, Repr

/-- The head-shape classifier the dispatch reads (toy of `isFlowContentStart`).  THREE shapes — the
    closer `sclose` is NOT among them. -/
def isContentStart : Tok → Prop
  | .scal   => True
  | .sopen  => True
  | .mopen  => True
  | .sclose => False

/-- The FOUR entry shapes the deliverable's type still anticipates (toy of `recseqentry_classify`'s
    four disjuncts) — including the empty bracket the guard will prune. -/
inductive Shape | scalar | emptyBracket | nestedSeq | nestedMap
  deriving DecidableEq, Repr, BEq

/-- The deep guard's `openerContentStart` field (toy): after a `sopen` at the head, the next token is
    content-start — so it is never `sclose`, i.e. no empty bracket. -/
def OpenerContentStart (head next : Tok) : Prop :=
  head = .sopen → isContentStart next

/-! ## POSITIVE — the dispatch is total over the THREE content-start heads -/

/-- The dispatch routes a content-start head into one of THREE shapes.  The empty bracket is not among
    them — and the `sclose` case is vacuous (`isContentStart sclose` reduces to `False`). -/
def dispatch : (t : Tok) → isContentStart t → Shape
  | .scal,   _ => .scalar
  | .sopen,  _ => .nestedSeq
  | .mopen,  _ => .nestedMap
  | .sclose, h => h.elim

-- It fires on each of the three reachable heads.
#guard dispatch .scal  True.intro == Shape.scalar
#guard dispatch .sopen True.intro == Shape.nestedSeq
#guard dispatch .mopen True.intro == Shape.nestedMap

/-- Under the guard, a `sopen`-headed window never has `sclose` next — the empty-bracket entry is
    EXCLUDED, not handled.  (Mirrors how `recseqentry_seqbracket_oracle`'s interior-non-emptiness step
    derives the would-be-empty close away from the deep guard's `openerContentStart`.) -/
theorem empty_excluded (head next : Tok)
    (h_guard : OpenerContentStart head next) (h_head : head = .sopen) :
    next ≠ .sclose := by
  intro h
  have hcs : isContentStart next := h_guard h_head
  rw [h] at hcs
  exact hcs  -- `isContentStart sclose` reduces to `False`

/-! ## NEGATIVE — it is the GUARD, not the token type, that prunes the empty branch -/

/-- The closer is not a content-start head, so the dispatch never classifies it as an entry head.
    (`isContentStart sclose` reduces to `False`, and `¬ False` is `False → False`.) -/
theorem not_content_start_sclose : ¬ isContentStart .sclose :=
  fun h => h

/-- WITHOUT the guard, a `sopen`-headed window CAN have `sclose` next — the empty bracket is a genuine
    fourth shape.  So the four-way head dispatch collapses to three only BECAUSE the guard is threaded:
    the guard, not the deliverable's type, does the pruning. -/
theorem empty_reachable_without_guard :
    ∃ head next : Tok, head = .sopen ∧ next = .sclose :=
  ⟨.sopen, .sclose, rfl, rfl⟩

-- The empty bracket is a DISTINCT shape in the deliverable's type — it is excluded by the guard at
-- dispatch time, not absent from the grammar.
#guard (Shape.emptyBracket == Shape.nestedSeq) == false

end Tests.Reflections.ThreadedGuardPrunesCaseTree
