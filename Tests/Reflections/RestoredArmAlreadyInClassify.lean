/-!
# Reflection 414 — the arm a false guard suppressed is already built in the classify; restore it with `by_cases`

Self-contained (core Lean, no `L4YAML` import) toy model of the (R2) SMALLEST-FIRST de-risk behind the
`h_seq_rec` producer migration.

A de-risk concludes a producer migration "requires a redesign to HANDLE a degenerate case the now-false
guard EXCLUDED" — and budgets new handling machinery. The trap (inverted): the deliverable type and its
*classify* are built ONCE, COMPLETE — a constructor per real shape — so the excluded case ALREADY HAS an
arm; the false guard was merely SUPPRESSING it. The redesign is a `by_cases` on the degenerate-case
discriminator routing to the existing arm, and (free alignment) the discriminator is EXACTLY the premise
the re-scoped guard is keyed on.

Mirrors L4YAML R413→R414. R413 named the residual: migrate the seq-rec producer off the empty-FALSE
`FlowBodyContentDeep` onto `FlowBodyContentDeepSeq`, "NOT a signature swap because the dispatch RELIES on
the false guard to EXCLUDE the empty-bracket leaf, a REAL case, so HANDLE it." R414 found: `RecSeqEntry`
already has the `seqEmpty` constructor, `recseqentry_classify` already has the empty-sequence disjunct,
`recseqentry_seqempty_dispatch` already produces it — the redesign is `by_cases tokens[lo+1] = ]`, whose
discriminator IS `FlowBodyContentDeepSeq.openerContentStart`'s `≠ ]` key.

* `deepOld`  models the OLD producer guard: after EVERY opener, a content start. FALSE at an empty `[ ]`.
* `deepNew`  models the RE-SCOPED guard: after an opener NOT immediately closed. VACUOUS at an empty `[ ]`.
* `Entry`    models the deliverable, built COMPLETE — including `emptyE`, the arm the old guard suppressed.
* `headEmpty` is the `by_cases` discriminator; it coincides with `deepNew`'s opener keying.
-/

namespace Tests.Reflections.RestoredArmAlreadyInClassify

set_option autoImplicit false

/-- A toy token kind: an opener `[`, a closer `]`, a content `scalar`, and an entry separator `,`. -/
inductive Tok where
  | op | cl | scal | sep
  deriving DecidableEq, BEq

/-- A content start: a scalar or an opener (mirrors `isFlowContentStart`). -/
def isContentStart : Tok → Bool
  | .scal | .op => true
  | _ => false

/-- **OLD producer guard** — after EVERY opener a content start (mirrors
    `FlowBodyContentDeep.openerContentStart`). FALSE at an empty `[ ]`: the opener is followed by a
    closer, which is not content. -/
def deepOld : List Tok → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!(a == Tok.op) || isContentStart b) && deepOld (b :: rest)

/-- **RE-SCOPED guard** — after an opener that is NOT immediately closed (mirrors
    `FlowBodyContentDeepSeq.openerContentStart`, keyed on `tokens[k+1] ≠ ]`). VACUOUS at an empty `[ ]`. -/
def deepNew : List Tok → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!((a == Tok.op) && !(b == Tok.cl)) || isContentStart b) && deepNew (b :: rest)

/-- The deliverable type, built COMPLETE — one constructor per real shape, INCLUDING the empty bracket
    `emptyE` (the arm a false producer guard would suppress). -/
inductive Entry : List Tok → Prop where
  | scalarE : Entry [Tok.scal]
  | emptyE  : Entry [Tok.op, Tok.cl]
  | nestedE (x : Tok) (rest : List Tok) : Entry (Tok.op :: x :: rest ++ [Tok.cl])

/-- The `by_cases` discriminator: the window is headed by an empty bracket `[ ]`. -/
def headEmpty : List Tok → Bool
  | Tok.op :: Tok.cl :: _ => true
  | _ => false

/-- A window whose FIRST entry is an empty `[ ]` and whose second is a scalar — the empty entry is NOT
    last, so (in the real lemma) its successor is a genuine separator.  In the producer's domain. -/
def emptyThenScalar : List Tok := [Tok.op, Tok.cl, Tok.sep, Tok.scal]
/-- The empty entry itself. -/
def emptyWin : List Tok := [Tok.op, Tok.cl]

/-! ## NEGATIVE — the OLD producer guard is FALSE on the real empty-bracket window -/

theorem deepOld_excludes_empty : deepOld emptyThenScalar = false := by decide

/-! ## POSITIVE — the RE-SCOPED guard HOLDS on the SAME window (vacuous at the empty head) -/

theorem deepNew_admits_empty : deepNew emptyThenScalar = true := by decide

/-! ## POSITIVE — the excluded arm is ALREADY BUILT in the deliverable; no new infra -/

theorem empty_arm_already_built : Entry emptyWin := Entry.emptyE

/-- **The redesign — a `by_cases` on the discriminator routes the empty case to the EXISTING arm.**
    No new handler: the `headEmpty` branch hands back `Entry.emptyE`, the constructor that was there all
    along.  Models `recseqentry_window_dispatch`'s `by_cases tokens[lo+1] = ]` redesign. -/
theorem producer_routes_empty_via_bycases : Entry emptyWin := by
  by_cases h : headEmpty emptyWin
  · -- empty branch: route to the constructor the classify already exposes.
    exact Entry.emptyE
  · -- non-empty branch: unreachable for this window (the discriminator fires).
    exact absurd (by decide : headEmpty emptyWin = true) h

/-! ## The free alignment — the `by_cases` discriminator IS the re-scoped guard's opener keying

`deepNew`'s opener clause fires under `(a == op) && !(b == cl)` — exactly the NEGATION of
`headEmpty`.  So the FALSE branch of `by_cases headEmpty` is precisely where the re-scoped guard's
opener premise holds (the old non-empty path), and the TRUE branch is where it is vacuous (the empty
arm).  Guard and case-split share ONE boundary. -/

theorem guard_skips_empty_head : ((Tok.op == Tok.op) && !(Tok.cl == Tok.cl)) = false := by decide
theorem guard_fires_nonempty_head : ((Tok.op == Tok.op) && !(Tok.scal == Tok.cl)) = true := by decide
theorem discriminator_matches_empty_head : headEmpty emptyThenScalar = true := by decide

-- the old guard suppresses the real empty case …
#guard deepOld emptyThenScalar == false
-- … while the re-scoped guard admits it …
#guard deepNew emptyThenScalar == true
-- … the discriminator fires exactly at the empty head (= where the re-scoped guard is vacuous) …
#guard headEmpty emptyThenScalar
#guard ((Tok.op == Tok.op) && !(Tok.cl == Tok.cl)) == false
-- … and the non-empty head keeps the old path.
#guard ((Tok.op == Tok.op) && !(Tok.scal == Tok.cl)) == true

end Tests.Reflections.RestoredArmAlreadyInClassify
