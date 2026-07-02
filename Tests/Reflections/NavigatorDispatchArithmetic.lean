/-!
# Reflection 350 — a position-indexed navigator splits DECISION from CORRECTNESS: the bottom-up locator's branch dispatch is pure offset/length arithmetic, balance is demoted to the correctness side

Self-contained (core Lean, no `L4YAML` import) toy model of the PROBE that settled
`(i'-b-B2c-nested-fbc-emission-locator)`: is the emission-spine-walk LOCATOR — at an all-seq-path
interior window `[a, b)`, find the enclosing `RecSeqEntry` stored in `seqRoot_recseqbody` — **(a)** a
single offset-tracked `body.length` recursion, or **(b)** a separate balance-locate front end?

The probe found **(a)**, and the reason generalizes: a navigator over a recursive deliverable splits
into a DECISION procedure (which branch to recurse into) and a CORRECTNESS justification (why that
branch is right), and the two use DIFFERENT machinery.  The decision is the cheap part.

FINDING — THE DECISION IS LENGTH ARITHMETIC.  Walking `RecSeqBody body` with the absolute base offset
`off` of `body`, the head entry `e` occupies `[off, off+e.length-1]`, so its interior window is
`[off+1, off+e.length-1)`.  The target window start `a` selects the move by comparing `a` against
`off+1` and `off + e.length` ALONE — a trichotomy (`classifyMove`, `classify_*`, `move_exhaustive`,
`move_exclusive`, all pure `omega`): `a = off+1` → LEAF; `off+1 < a < off+e.length` → DESCEND
(off' = off+1); `off+e.length < a` → ADVANCE (off' = off+e.length+1); `a = off+e.length` is the
impossible close/separator position.  The recursive structure already STORES each entry's length, and
the offset-slice invariant `body = (take H).drop off` ties structure to absolute token positions — so
the navigator NEVER calls balance to decide.

FINDING — BALANCE IS DEMOTED TO CORRECTNESS.  R330's TOP-DOWN projection selected the entry by
`flowBracketBalance = 0` from the active base — it was given a token coordinate and had to FIND the
structural entry (`topDown_needs_balance`).  This BOTTOM-UP locator is keyed on the window `[a,b)`
itself, so the structural walk + offset arithmetic locate the entry directly
(`bottomUp_decides_by_arithmetic`); balance enters only the PROOF that the located slice equals the
target window (`Correct`, via the all-seq-path / `WellTyped` hypotheses), never the branch selector.
Importing the front end into the navigator is redundant — its extra hypothesis is dead in the dispatch
(`balance_arg_redundant`).

THE TRANSFERABLE RULE.  Before importing a locate's heavy front end (balance, search, a
matching-bracket primitive) into a navigator that descends the same structure, ask which part of the
locate is the DECISION (which child to recurse into) vs the CORRECTNESS (why).  If the recursive
deliverable stores the positional data the decision needs (entry lengths, child spans) and an
offset-slice invariant ties it to absolute coordinates, the decision is a length-arithmetic trichotomy
— pure `omega` — and the heavy front end belongs only to the correctness proof.  Probe the trichotomy
on concrete witnesses BEFORE authoring; clean classification is the (a) single-recursion answer.

Sharpens [[ref-backward-locator-mirrors-forward]] / [[ref-near-leaf-mirror-sheds-machinery]] (the
backward/bottom-up direction sheds the forward locate's machinery) and
[[ref-from-located-assembler-direction]] (the bottom-up single-step shape); the feared machinery was
already paid for by the structure's stored lengths ([[ref-metric-bridge-is-composition]]).
-/

namespace Tests.Reflections.NavigatorDispatchArithmetic

set_option autoImplicit false

/-! ## The decision: a length-arithmetic trichotomy (no balance) -/

/-- The three navigator moves. -/
inductive Move where
  | leaf | descend | advance

/-- **The branch selector** — reads ONLY `off`, `L = e.length`, `a` (length arithmetic), never
    balance.  `off + L` (the close/separator position) cannot be a valid interior start, so the gap
    between `descend` (`a < off+L`) and `advance` (`off+L < a`) is never a valid window. -/
def classifyMove (off L a : Nat) : Move :=
  if a = off + 1 then .leaf
  else if a < off + L then .descend
  else .advance

/-- A total navigator step: the move plus the new base offset.  LEAF returns the current base `off`
    as the located entry opener `lo`; DESCEND drops into the head entry's interior (`off+1`); ADVANCE
    skips the head entry and its separator (`off+L+1`). -/
def navMove (off L a : Nat) : Move × Nat :=
  match classifyMove off L a with
  | .leaf    => (.leaf, off)
  | .descend => (.descend, off + 1)
  | .advance => (.advance, off + L + 1)

theorem classify_leaf (off L a : Nat) (h : a = off + 1) : classifyMove off L a = .leaf := by
  unfold classifyMove; rw [if_pos h]

theorem classify_descend (off L a : Nat) (h1 : off + 1 < a) (h2 : a < off + L) :
    classifyMove off L a = .descend := by
  unfold classifyMove; rw [if_neg (by omega), if_pos h2]

theorem classify_advance (off L a : Nat) (hL : 1 ≤ L) (h : off + L < a) :
    classifyMove off L a = .advance := by
  unfold classifyMove; rw [if_neg (by omega), if_neg (by omega)]

/-- The trichotomy is EXHAUSTIVE on valid windows (`a` is not the impossible close/separator position
    `off+L`): every valid `a ≥ off+1` classifies as exactly one of the three moves — pure `omega`. -/
theorem move_exhaustive (off L a : Nat) (h_pos : off + 1 ≤ a) (h_ne : a ≠ off + L) :
    (a = off + 1) ∨ (off + 1 < a ∧ a < off + L) ∨ (off + L < a) := by omega

/-- The branches are mutually exclusive (no window classifies as two moves); needs only `1 ≤ L`
    (entries are nonempty).  Again pure `omega` on the same length data. -/
theorem move_exclusive (off L a : Nat) (hL : 1 ≤ L) :
    ¬ ((a = off + 1) ∧ (off + 1 < a ∧ a < off + L)) ∧
    ¬ ((a = off + 1) ∧ (off + L < a)) ∧
    ¬ ((off + 1 < a ∧ a < off + L) ∧ (off + L < a)) := by omega

/-! ## Decision vs correctness: balance is demoted to the correctness side -/

/-- A toy "balance = 0 at the entry head" fact — the heavy front end R330's TOP-DOWN projection used
    to FIND the structural entry from a bare token coordinate. -/
def Balance (_off _a : Nat) : Prop := True

/-- The CORRECTNESS obligation: the located opener `lo` EQUALS the navigator's base `off`.  Modeled as
    needing `Balance` (which entry the slice is) — the ONLY place balance enters. -/
def Correct (off a lo : Nat) : Prop := Balance off a → lo = off

/-- **TOP-DOWN locate consumes balance to DECIDE** (R330): given only a token coordinate, it must call
    `Balance` to select the entry. -/
theorem topDown_needs_balance (off a : Nat) (_hb : Balance off a) : ∃ lo, lo = off := ⟨off, rfl⟩

/-- **BOTTOM-UP locate DECIDES by arithmetic** (R350): the move is a function of `off`/`L`/`a` with no
    `Balance` argument — the deliverable's stored entry length `L` + the offset suffice. -/
theorem bottomUp_decides_by_arithmetic (off L a : Nat) :
    navMove off L a = (match classifyMove off L a with
      | .leaf => (Move.leaf, off) | .descend => (.descend, off+1) | .advance => (.advance, off+L+1)) :=
  rfl

/-- **The split, distilled.**  Deciding `leaf` at `a = off+1` is arithmetic (`classify_leaf`); the
    matching correctness `lo = off` is delivered by `Correct` FROM `Balance`.  Decision balance-free,
    correctness balance-fed — two pieces, two machineries. -/
theorem decision_then_correctness (off L a : Nat)
    (h_leaf : a = off + 1) (_hb : Balance off a) :
    classifyMove off L a = .leaf ∧ Correct off a off := by
  refine ⟨classify_leaf off L a h_leaf, ?_⟩
  intro _; rfl

/-- **NEGATIVE — importing balance into the DECISION is REDUNDANT.**  A hypothetical decider that also
    consumes `Balance` returns the very same move `classifyMove` already computes from arithmetic — the
    extra hypothesis is dead in the branch selector.  Don't import the front end into the navigator. -/
def classifyWithBalance (off L a : Nat) (_hb : Balance off a) : Move := classifyMove off L a

theorem balance_arg_redundant (off L a : Nat) (_hb : Balance off a) :
    classifyWithBalance off L a _hb = classifyMove off L a := rfl

end Tests.Reflections.NavigatorDispatchArithmetic
