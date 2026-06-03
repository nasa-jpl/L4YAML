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

end ProducerGuardedTrap
