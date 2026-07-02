/-!
# Reflection 483 — the nested TYPED locator is a FRAME, not a re-proof
# (and the frame is cleaner than the hand-rolled depth-0 special case).

Self-contained (core Lean, no `L4YAML` import) toy recording how R483 lifted the typed matching-close
locators (`matching_close_typed_{generic,core}`,
`flowBracketBalance_matching_close_{seq,map}` in `Proofs/Output/EmitterScannability/WellBracketed.lean`)
from a depth-0 opener to a NESTED one — the typed half of the same obstruction R482 fixed at the
balance layer.

**The obstruction (shared with R482).**  `seqEnclosingOpener_of_gate` hands back the INNERMOST
enclosing opener of a gated window, which for a deeply-nested window sits at depth ≥ 1.  So the
depth-0 premise `h_k_depth : flowBracketBalance tokens lo k = 0` is genuinely FALSE, and every
depth-0-keyed locator must be generalized.  R482 generalized the BALANCE core
(`flowBracketBalance_matching_close_nested`); R483 generalizes the TYPED layer that pins the close's
*token type* (`]` for a `[`, never `}`).

**Two obstructions, two DIFFERENT repair shapes.**
* The BALANCE layer carries a scalar `Int` depth.  A scalar shifts UNIFORMLY under nesting, so the
  generalization RE-BASES: subtract the opener's own level everywhere (`0 ↦ balance lo k`,
  `1 ↦ balance lo k + 1`).  Nothing is reused — the proof is re-derived against a new baseline,
  because the global Dyck floor `≥ 0` does NOT shift-transfer (it becomes `≥ d`).  See R482.
* The TYPED layer carries a `List Bool` STACK.  A nested opener sits over a base stack `s_k` whose
  bottom `d` markers (the enclosing openers) are INERT across the positive-depth span `[k, j]`.  So
  the generalization FRAMES: the base stack `s_k` is a suffix the interior never reads.  The opener
  pushes `b :: s_k` (`step_frame`), the balanced interior folds from `b :: s_k` back to `b :: s_k`
  (`fold_frame_self`), and the close strips `s_k` off — collapsing the nested
  `step (pop b) (b :: s_k) = some s_k` to the IDENTICAL depth-0 `step (pop b) [b] = some []`.  The
  depth-0 *type reader* then applies verbatim, at any depth, with no re-proof.

The dividing line: **re-base when the carrier is a scalar difference; frame when the carrier is a
stack with an inert suffix.**  And framing the interior via "a balanced body returns to any prefix"
(`fold_frame_self`, the real `WellTyped_frame`) is CLEANER than the depth-0 proof's bespoke
bottom-preservation (`btFold_getLast?_preserved`) — the nested generalization is structurally
SIMPLER than the special case it generalizes, because framing names the abstraction the depth-0
proof open-coded.

This toy models the stack machine (`step`/`fold`), proves the two framing engines (`step_frame`,
`fold_frame`), and the punchline that the nested close is the depth-0 close framed by `s_k`.
-/

namespace NestedTypedLocatorIsAFrame

set_option autoImplicit false

/-- A toy bracket token: `push b` opens a marker `b`, `pop b` closes a matching one, `nop` is
    depth-neutral.  Models `[`/`]`/`{`/`}` (markers `true`/`false`) and scalars in the real
    `btStep`/`btFold`. -/
inductive Tok
  | push (b : Bool)
  | pop (b : Bool)
  | nop

open Tok

/-- One stack step; `none` on a pop mismatch or underflow.  Mirrors `btStep`. -/
def step : Tok → List Bool → Option (List Bool)
  | push b, s     => some (b :: s)
  | pop _, []     => none
  | pop b, x :: s => if x = b then some s else none
  | nop, s        => some s

/-- Fold the step over a token list from a starting stack.  Mirrors `btFold`. -/
def fold : List Tok → List Bool → Option (List Bool)
  | [],      s => some s
  | t :: ts, s =>
      match step t s with
      | none    => none
      | some s' => fold ts s'

theorem fold_cons_some (t : Tok) (ts : List Tok) (s s' : List Bool)
    (h : step t s = some s') : fold (t :: ts) s = fold ts s' := by
  simp only [fold, h]

theorem fold_cons_none (t : Tok) (ts : List Tok) (s : List Bool)
    (h : step t s = none) : fold (t :: ts) s = none := by
  simp only [fold, h]

/-- A matching `pop b` over `b :: s` pops the head, leaving `s`. -/
theorem step_pop_match (b : Bool) (s : List Bool) : step (pop b) (b :: s) = some s := by
  simp [step]

/-- **One step frames up.**  A step defined over `s` runs identically over `s ++ extra`, carrying the
    frame `extra` along untouched.  The toy of `btStep_frame` — the load-bearing fact that a stack's
    bottom suffix is inert.  (A `pop` never reaches into `extra` because it pops the head `x`, which
    is in `s`.) -/
theorem step_frame (t : Tok) (s extra r : List Bool) (h : step t s = some r) :
    step t (s ++ extra) = some (r ++ extra) := by
  cases t with
  | push b => simp only [step, Option.some.injEq] at h; subst h; simp [step]
  | nop => simp only [step, Option.some.injEq] at h; subst h; simp [step]
  | pop b =>
    cases s with
    | nil => simp [step] at h
    | cons x s' =>
      by_cases hx : x = b
      · subst x
        rw [List.cons_append, step_pop_match b (s' ++ extra)]
        rw [step_pop_match b s'] at h
        rw [Option.some.injEq] at h
        rw [h]
      · simp [step, hx] at h

/-- **A fold frames up.**  A fold defined over `s` (ending at `r`) runs identically over `s ++ extra`,
    ending at `r ++ extra`.  The toy of `btFold_frame`: induct on the list, framing each step. -/
theorem fold_frame (ts : List Tok) :
    ∀ (s extra r : List Bool), fold ts s = some r → fold ts (s ++ extra) = some (r ++ extra) := by
  induction ts with
  | nil =>
    intro s extra r h
    simp only [fold, Option.some.injEq] at h
    subst h
    simp only [fold]
  | cons t ts ih =>
    intro s extra r h
    cases hstep : step t s with
    | none =>
      rw [fold_cons_none t ts s hstep] at h
      exact absurd h (by simp)
    | some s' =>
      rw [fold_cons_some t ts s s' hstep] at h
      rw [fold_cons_some t ts (s ++ extra) (s' ++ extra) (step_frame t s extra s' hstep)]
      exact ih s' extra r h

/-- **A balanced body returns to ANY prefix** — the `WellTyped_frame` analogue, and the reason the
    nested interior preservation needs NO bottom-preservation re-proof.  If the body returns to `s`
    from `s` (a balanced, Dyck interior), it returns to `s ++ extra` from `s ++ extra`.  In the real
    locator this is how the interior `[k+1, j)` folds from `b :: s_k` back to `b :: s_k` — replacing
    the depth-0 proof's hand-rolled `btFold_getLast?_preserved`. -/
theorem fold_frame_self (ts : List Tok) (s extra : List Bool) (h : fold ts s = some s) :
    fold ts (s ++ extra) = some (s ++ extra) :=
  fold_frame ts s extra s h

/-- **The depth-0 close**: a `pop b` over the singleton `[b]` pops to `[]`.  This is the type
    reader's input (`btStep_pop_eq_seqEnd : step (pop true) [true] = some [] → it's a `]``). -/
theorem depth0_close (b : Bool) : step (pop b) [b] = some [] := by
  simp [step]

/-- **Punchline — the nested close IS the depth-0 close, framed by `s_k`.**  Given the depth-0 close
    fact and ANY base stack `s_k`, the nested close over `b :: s_k` pops to `s_k` purely by
    `step_frame` — the SAME proof with the frame carried along.  So the depth-0 type reader applies
    at any depth WITHOUT re-proof.  (Contrast R482: the BALANCE layer re-bases by shift because a
    scalar depth offers no inert suffix to frame.) -/
theorem nested_close_via_frame (b : Bool) (s_k : List Bool) :
    step (pop b) (b :: s_k) = some s_k := by
  have h := step_frame (pop b) [b] s_k [] (depth0_close b)
  simpa using h

/-- A concrete depth-1 nesting witness: `[ { x } ]` as `push true, push false, nop, pop false,
    pop true`.  The INNER opener `push false` fires at stack `[true]` (depth 1) — so its matching
    close `pop false` must be located by the NESTED locator, not the depth-0 one.  The whole word is
    balanced: it folds from `[]` back to `[]`. -/
def nestedWord : List Tok := [push true, push false, nop, pop false, pop true]

theorem nestedWord_balanced : fold nestedWord [] = some [] := by
  simp [nestedWord, fold, step]

/-- The inner `pop false` (the 4th token) pops the depth-1 frame `false :: [true]` back to `[true]` —
    `nested_close_via_frame` with `s_k = [true]`, exactly the depth-≥1 case the depth-0 locator
    cannot reach. -/
theorem inner_close_is_framed : step (pop false) (false :: [true]) = some [true] :=
  nested_close_via_frame false [true]

end NestedTypedLocatorIsAFrame
