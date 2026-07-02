/-!
# Reflection 470 — an INTERIOR-only producer cannot be COERCED UP to a BOUNDARY-INCLUSIVE window:
# author the OPENER-INCLUSIVE sibling instead (same machinery, and it SHEDS the empty-case guard).

Self-contained (core Lean, no `L4YAML` import) toy modelling the seq carrier↔recursion
co-construction's enclosing-window residual.

Context (the real situation).  The seq carrier↔recursion co-construction's last residual
(`h_widthEnc`, `SeqInteriorSeparators.lean`) must hand the enclosing opener `p`'s window to
`seqDescent_provider_of_located`, which consumes `FlowBodyWindow tokens p hiE` SOLELY to drive
`flowBracketBalance_matching_close tokens p p hiE` — a re-scan that needs `bal` to START AT the
opener `p` (`balance p hiE = 0`, opener-INCLUSIVE).  The landed descend producer
`flowBodyWindow_descend` (R285) delivers the INTERIOR `[k+1, j)` (`balance (k+1) j = 0`,
opener-EXCLUSIVE), GUARDED on non-emptiness `k+1 < j` (the empty bracket `[]`/`{}` has no interior).

The de-risk asked: do the enclosing-window facts re-base from the parent's `FlowBodyWindow`, or need
a new producer?  The answer is a SUBTLE BOTH: they re-base from the parent (same position lemma
`flowBracketBalance_matching_close` + the same `WellTyped_subrange` transporter), but NOT through
`flowBodyWindow_descend` — the interior producer threw away the opener and closer, so it cannot be
COERCED UP to the boundary-inclusive window the consumer re-scans from.  The brick
`flowBodyWindow_child_bracket` is the OPENER-INCLUSIVE sibling: it keeps the opener `[` and closer `]`,
delivering `FlowBodyWindow tokens k (j+1)` (`balance k (j+1) = 0`).  And because `[k, j+1)` is never
empty (`k < j+1`), the sibling SHEDS the R285 non-emptiness guard.

This toy reproduces the STRUCTURE:

* `bal` — a token list's running balance (`+1` opener, `-1` closer, `0` item), the
  `flowBracketBalance` analog; `bal_append` is its `flowBracketBalance_compose` analog.
* `interiorWindow I = I` — the opener-EXCLUSIVE window `flowBodyWindow_descend` delivers.
* `boundaryWindow I = (1 :: I) ++ [-1]` — the opener-INCLUSIVE window the consumer needs.
* `closeAtEnd` — THE CONSUMER: re-scans a window FROM ITS START as a single bracket (balanced, ends in
  a closer, every PROPER prefix has running balance `≥ 1`), the
  `flowBracketBalance_matching_close tokens p p hiE` analog that needs `bal` to start at the opener.
* `bal_boundaryWindow` — the sibling's `balanced` field: opener `+1`, balanced interior, closer `-1`.
* The POSITIVE/NEGATIVE pair on `I = [1,-1,1,-1]` (`[][]`, balanced but TWO sub-brackets): the consumer
  HOLDS on the boundary window, FAILS on the interior window — even though BOTH are balanced.  The
  interior window cannot be coerced up: it returns to `0` internally, so it is not a single bracket
  re-scannable from a virtual opener.
* The EMPTY case `I = []`: `interiorWindow [] = []` (the producer's degenerate case, needing a guard);
  `boundaryWindow [] = [1,-1]` is nonempty and the consumer holds — the sibling sheds the guard.
-/

namespace BoundaryInclusiveNeedsSiblingNotCoercion

set_option autoImplicit false

/-- A minimal bracket-delta token: `1` opener `[`, `-1` closer `]`, `0` content item. -/
abbrev Tok := Int

/-- The running balance of a token list (the `flowBracketBalance` analog). -/
def bal : List Tok → Int
  | [] => 0
  | x :: xs => x + bal xs

/-- `bal` is additive over append (the `flowBracketBalance_compose` analog). -/
theorem bal_append (a b : List Tok) : bal (a ++ b) = bal a + bal b := by
  induction a with
  | nil => simp [bal]
  | cons x xs ih => simp only [List.cons_append, bal, ih]; omega

/-- **THE INTERIOR WINDOW** — the opener-EXCLUSIVE `[k+1, j)` that `flowBodyWindow_descend` delivers:
    the content strictly between the opener and closer. -/
def interiorWindow (I : List Tok) : List Tok := I

/-- **THE BOUNDARY-INCLUSIVE WINDOW** — the opener-INCLUSIVE `[k, j+1)` the consumer needs: opener `1`,
    the interior `I`, then closer `-1` — the full bracket. -/
def boundaryWindow (I : List Tok) : List Tok := (1 :: I) ++ [-1]

/-- **THE CONSUMER** (the `flowBracketBalance_matching_close tokens p p hiE` analog): it re-scans a
    window FROM ITS START as a single bracket — balanced, ending in a closer, with the running balance
    `≥ 1` at every PROPER prefix (so the matching close is exactly at the END).  It NEEDS `bal` to
    start at the opener; a window that starts past the opener cannot satisfy it.  The proper-prefix
    positivity is a decidable `List.range` check, so the witnesses below close by `decide`. -/
def closeAtEnd (w : List Tok) : Prop :=
  bal w = 0 ∧ w ≠ [] ∧ w.getLast? = some (-1) ∧
    (List.range (w.length - 1)).all (fun n => decide (1 ≤ bal (w.take (n + 1)))) = true

/-- **THE SIBLING'S `balanced` FIELD — the boundary-inclusive window is balanced** (general): opener
    `+1`, balanced interior, closer `-1`.  The `flowBodyWindow_child_bracket` `balanced` field, in the
    toy: it re-bases from the interior's balance, KEEPING the opener and closer. -/
theorem bal_boundaryWindow (I : List Tok) (hI : bal I = 0) : bal (boundaryWindow I) = 0 := by
  simp only [boundaryWindow, bal_append, bal]
  omega

/-- POSITIVE — on `I = [1,-1,1,-1]` (`[][]`, balanced but TWO sub-brackets) the consumer HOLDS on the
    BOUNDARY-INCLUSIVE window `[1, 1,-1,1,-1, -1]`: the proper-prefix balances `1,2,1,2,1` are all
    `≥ 1`, and the last token is the matching closer.  The opener-inclusive window re-scans as a
    single bracket. -/
example : closeAtEnd (boundaryWindow [1, -1, 1, -1]) := by
  unfold closeAtEnd; decide

/-- NEGATIVE — the SAME interior, but the INTERIOR window `[1,-1,1,-1]` FAILS the consumer: the proper
    prefix `[1,-1]` already returns to balance `0`, so the proper-prefix positivity is violated.  The
    interior window CANNOT be coerced up to the boundary-inclusive one — it threw away the opener, so
    its balance does not present as a single bracket.  (Both windows are balanced; only the
    boundary-inclusive one satisfies the from-opener re-scan.) -/
example : ¬ closeAtEnd (interiorWindow [1, -1, 1, -1]) := by
  unfold closeAtEnd interiorWindow; decide

/-- EMPTY case — the SIBLING SHEDS the non-emptiness guard.  The INTERIOR window of an empty bracket
    is `[]` (the producer's degenerate case, which `flowBodyWindow_descend` must GUARD with `k+1 < j`);
    the BOUNDARY-INCLUSIVE window `[1,-1]` is nonempty and the consumer holds with NO guard. -/
example : interiorWindow ([] : List Tok) = [] := rfl

example : closeAtEnd (boundaryWindow ([] : List Tok)) := by
  unfold closeAtEnd; decide

end BoundaryInclusiveNeedsSiblingNotCoercion
