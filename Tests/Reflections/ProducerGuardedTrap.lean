/-!
# The producer-guarded-quantifier trap — runnable demonstration

A self-contained (core Lean, no `L4YAML` import) illustration of the proof-engineering trap
documented in `Blueprint/08-initiative-4-intrinsic-foundations.md`, Reflection 218: a lemma that
**produces** its witness internally and then defers a premise quantified over that witness must
guard the premise with the producer's guarantee — otherwise the `∀` ranges over cases the producer
never hits, the premise is unsatisfiable, and *the build does not tell you*.

The witness stream `ts` is the body of `[["a"],"b"]` with the outer brackets stripped — `[ s ] , s` —
and the separator (index 3) is the case the locator never returns but the weak `∀` still ranges over.

Run it: open in the IDE (the `#eval`s render in the infoview) or `lake build Tests.Reflections.ProducerGuardedTrap`
(the `#guard`s fail the build if any expectation is wrong).
-/

namespace ProducerGuardedTrap

/-- Toy tokens: opener `[`, closer `]`, separator `,`, scalar `s`. -/
inductive Tok | opn | cls | sep | scal
deriving DecidableEq, Repr

/-- Bracket delta: +1 open, −1 close, 0 otherwise. -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _    => 0

/-- Running bracket balance of the first `n` tokens. -/
def bal (ts : List Tok) (n : Nat) : Int :=
  ((ts.take n).map delta).foldl (· + ·) 0

/-- Witness stream = body of `[["a"],"b"]`, outer brackets stripped: `[ s ] , s`, indices 0..4. -/
def ts : List Tok := [.opn, .scal, .cls, .sep, .scal]

/-- "A complete value is followed by a separator, or the end." Holds at the close (idx 2 → `,`) and
    the last scalar (idx 4 → end); FAILS at the separator (idx 3 → next is scalar `s`).
    `abbrev`, not `def`, so `decide` can synthesize the bounded-∀ `Decidable` instance. -/
abbrev Goal (ts : List Tok) (j : Nat) : Prop :=
  ts[j+1]? = some .sep ∨ j + 1 = ts.length

/-- The locator's guarantee about the witness it returns: `j` is a depth-0 close. -/
abbrev producerProp (ts : List Tok) (j : Nat) : Prop := delta (ts.getD j .scal) = -1
/-- The weaker, separator-blind condition the broken premise used. -/
abbrev weakCond (ts : List Tok) (j : Nat) : Prop := bal ts (j+1) = 0

/-! ## The two lemmas — both type-check; only one has a supplyable premise. -/

/-- BROKEN. Deferred premise quantified over the witness using only `weakCond`. TYPE-CHECKS — the
    body applies `h_succ` only at the produced `j`, where `weakCond j` holds. -/
theorem trap {ts : List Tok} {j : Nat} (h_jlt : j < ts.length)
    (h_loc : producerProp ts j ∧ weakCond ts j)
    (h_succ : ∀ j, j < ts.length → weakCond ts j → Goal ts j) :
    Goal ts j :=
  h_succ j h_jlt h_loc.2

/-- FIXED. Same one-line body, premise now guarded by the producer's property (`h_loc.1`). -/
theorem fixed {ts : List Tok} {j : Nat} (h_jlt : j < ts.length)
    (h_loc : producerProp ts j ∧ weakCond ts j)
    (h_succ : ∀ j, j < ts.length → producerProp ts j → weakCond ts j → Goal ts j) :
    Goal ts j :=
  h_succ j h_jlt h_loc.1 h_loc.2

/-! ## `#eval` — see the trap. Per index `j`: delta, `bal (j+1)`, weakCond?, producerProp?, Goal?. -/

/-- One row of the diagnostic table for index `j`. -/
def report (j : Nat) : String :=
  s!"j={j}  delta={delta (ts.getD j .scal)}  bal(j+1)={bal ts (j+1)}  " ++
  s!"weakCond={decide (weakCond ts j)}  producerProp={decide (producerProp ts j)}  " ++
  s!"Goal={decide (Goal ts j)}"

-- Watch index 3 (the separator): weakCond=true, producerProp=false, Goal=FALSE.
-- That row is the trap — the weak `∀` must cover it, but `Goal` is false there.
-- Index 2 (the close) is the legitimate witness: weakCond=true, producerProp=true, Goal=true.
-- `#guard_msgs` pins each rendered table as checked documentation AND keeps it out of the build
-- log: a match is swallowed silently; any drift in a row fails the build with an error.
/-- info: ["j=0  delta=1  bal(j+1)=1  weakCond=false  producerProp=false  Goal=false",
 "j=1  delta=0  bal(j+1)=1  weakCond=false  producerProp=false  Goal=false",
 "j=2  delta=-1  bal(j+1)=0  weakCond=true  producerProp=true  Goal=true",
 "j=3  delta=0  bal(j+1)=0  weakCond=true  producerProp=false  Goal=false",
 "j=4  delta=0  bal(j+1)=0  weakCond=true  producerProp=false  Goal=true"] -/
#guard_msgs in
#eval (List.range ts.length).map report

/-- info: "j=2  delta=-1  bal(j+1)=0  weakCond=true  producerProp=true  Goal=true" -/
#guard_msgs in
#eval report 2  -- the close: the legitimate witness (producerProp=true, Goal=true)

/-- info: "j=3  delta=0  bal(j+1)=0  weakCond=true  producerProp=false  Goal=false" -/
#guard_msgs in
#eval report 3  -- the separator: the trap (weakCond=true, yet Goal=false)

/-! ## `#guard` — enforce the positives and the negative. -/

-- Positive: `Goal` holds at the close (idx 2) and at the end (idx 4).
#guard decide (Goal ts 2)
#guard decide (Goal ts 4)

-- NEGATIVE: `Goal` FAILS at the separator (idx 3) — yet `weakCond` holds there.
#guard !decide (Goal ts 3)
#guard decide (weakCond ts 3)

-- The trap's `h_succ` premise is UNSATISFIABLE: the bounded `∀` is false (idx 3 breaks it).
#guard !decide (∀ j, j < ts.length → weakCond ts j → Goal ts j)

-- The fixed `h_succ` premise IS satisfiable: guarding by `producerProp` excludes the separator.
#guard decide (∀ j, j < ts.length → producerProp ts j → weakCond ts j → Goal ts j)

/-! ## The theorems at work. -/

/-- The fixed `h_succ` premise, as a real (sorry-free) proof. -/
theorem strong_premise_holds :
    ∀ j, j < ts.length → producerProp ts j → weakCond ts j → Goal ts j := by decide

/-- `fixed` produces a genuine proof of `Goal ts 2` — its premise is supplyable. -/
example : Goal ts 2 :=
  fixed (by decide) (by decide) strong_premise_holds

/-- `trap` cannot be applied here: its `h_succ` is exactly the universal that this refutes, so no
    such function exists to pass. (Contrast with `strong_premise_holds`, which does exist.) -/
theorem trap_premise_is_false :
    ¬ (∀ j, j < ts.length → weakCond ts j → Goal ts j) := by decide

/-! ## R283 refinement — the guard is forced by ANY witness-dependent residual, not the recursive one.

Reflection 283 folds the close-locators into the bracket disjuncts, deriving the matching close `j`
from the head.  Two residual facts survive past the located `j`: an **interior oracle** and the
**trailing separator**.  On the *recursive* (nested-sequence) branch both await the witness (the
interior oracle is a `RecSeqBody` from the recursion); on the *near-leaf* (nested-mapping) branch the
interior oracle is flat-decidable and suppliable inline — yet the fold STILL needs the guarded
universal.  Why: the separator is witness-dependent on BOTH branches.  The lesson sharpens the
principle above: scan ALL residual conjuncts; a single witness-dependent one forces the guard, even if
its companion is benign everywhere.  Modeled below: `interiorOk` holds at every index (the inline
near-leaf oracle), but the full residual `Resid = interiorOk ∧ Goal` still needs the guard because of
`Goal` (the separator). -/

/-- A flat interior oracle that holds at EVERY index (models the near-leaf `WellBracketed`, suppliable
    inline): the balance never goes negative.  True for all `j` of `ts`. -/
abbrev interiorOk (ts : List Tok) (j : Nat) : Prop := 0 ≤ bal ts (j+1)

/-- The full residual a bracket disjunct needs past the located close: interior oracle AND separator. -/
abbrev Resid (ts : List Tok) (j : Nat) : Prop := interiorOk ts j ∧ Goal ts j

/-- One row of the R283 table: the interior oracle, the separator `Goal`, and their conjunction. -/
def reportR283 (j : Nat) : String :=
  s!"j={j}  interiorOk={decide (interiorOk ts j)}  Goal={decide (Goal ts j)}  Resid={decide (Resid ts j)}"

-- The close (idx 2) is the legitimate witness; the separator (idx 3) is the trap. Note `interiorOk`
-- is TRUE on both rows — the residual fails at idx 3 purely because `Goal` (the separator) fails there.
/-- info: ["j=2  interiorOk=true  Goal=true  Resid=true", "j=3  interiorOk=true  Goal=false  Resid=false"] -/
#guard_msgs in
#eval [reportR283 2, reportR283 3]

/-- NEAR-LEAF TRAP. The interior oracle is suppliable inline (holds everywhere), so one is tempted to
    guard the residual loosely — but it also carries the witness-dependent separator. Unguarded `∀`
    over `weakCond` type-checks, yet its premise is unsatisfiable. -/
theorem nearLeaf_trap {ts : List Tok} {j : Nat} (h_jlt : j < ts.length)
    (h_loc : producerProp ts j ∧ weakCond ts j)
    (h_resid : ∀ j, j < ts.length → weakCond ts j → Resid ts j) :
    Resid ts j :=
  h_resid j h_jlt h_loc.2

/-- NEAR-LEAF FIXED. Same body, residual premise guarded by the producer's property — forced by the
    separator conjunct even though the interior conjunct alone would not need it. -/
theorem nearLeaf_fixed {ts : List Tok} {j : Nat} (h_jlt : j < ts.length)
    (h_loc : producerProp ts j ∧ weakCond ts j)
    (h_resid : ∀ j, j < ts.length → producerProp ts j → weakCond ts j → Resid ts j) :
    Resid ts j :=
  h_resid j h_jlt h_loc.1 h_loc.2

-- The interior oracle ALONE needs no guard — supplyable over the weak condition (holds everywhere).
#guard decide (∀ j, j < ts.length → weakCond ts j → interiorOk ts j)
-- Yet the FULL residual unguarded is FALSE — the separator (idx 3) breaks it even though interiorOk holds.
#guard !decide (∀ j, j < ts.length → weakCond ts j → Resid ts j)
-- Guarding by `producerProp` (the close-locator's output) restores supplyability — excludes the separator.
#guard decide (∀ j, j < ts.length → producerProp ts j → weakCond ts j → Resid ts j)

/-- The interior oracle alone is supplyable UNGUARDED — so the recursion is not what forces the guard. -/
theorem interior_alone_needs_no_guard :
    ∀ j, j < ts.length → weakCond ts j → interiorOk ts j := by decide

/-- The full residual unguarded is unsatisfiable — the witness-dependent SEPARATOR forces the guard. -/
theorem nearLeaf_resid_unguarded_is_false :
    ¬ (∀ j, j < ts.length → weakCond ts j → Resid ts j) := by decide

/-- The guarded residual premise IS a real (sorry-free) proof. -/
theorem nearLeaf_resid_premise_holds :
    ∀ j, j < ts.length → producerProp ts j → weakCond ts j → Resid ts j := by decide

/-- `nearLeaf_fixed` produces a genuine proof at the located close (idx 2). -/
example : Resid ts 2 := nearLeaf_fixed (by decide) (by decide) nearLeaf_resid_premise_holds

end ProducerGuardedTrap
