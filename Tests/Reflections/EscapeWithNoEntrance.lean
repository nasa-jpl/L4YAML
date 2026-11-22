/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 684 — an escape with no entrance

**The rule.**  An escape constructor added to an invariant (Reflection 672's
renounced state) is closed one birth site at a time by the repairs that refute
its events — and the last birth site closes SILENTLY.  What is left is a
constructor every one of whose producers consumes one of its own kind: the
transport arms still typecheck, the dispatch arms still split, the case tree
still looks inhabited, and no build says a word.  A census of construction
sites cannot settle it, because a transport site and a birth site are the same
text.  **Delete the constructor and rebuild** — the compiler is the only thing
that can distinguish a lane with an entrance from a lane without one, and a
green build after the deletion is the proof of unreachability.  Corollary: any
work item that ENRICHES such a constructor (one more field, one more coupling)
is priced against a lane no input enters.

**The instance** (item 126, correcting items 124/125).  `FlowStackB.shape` was
item 46's renounced flow stack.  Items 50/69/72/73/82/83/84 refuted the
renounce events — the flow open's under-run, the interior's under-run, the tab,
and the floor made real at every park — until every `.shape` in the file was
built from a `close` taken out of a `.shape` (`open_of_succ`'s right disjunct),
with the invariant seeded at `nil`.  The next item on the ledger was to give
that constructor a value-slot FACE.  Deleting it instead: the constructor,
`FlowStackK.collapse`, the shape continuation the five flow indicators ran on
it, nine `rcases … | h_close_sh` splits and four dead match arms come out —
289 lines net — with zero runtime edits, zero errors and zero warnings.

**A second instance, from the other direction** (item 127).  A constructor can
also reach this state without ever having had an entrance: `BlockStack`'s
`seqLevel`/`mapLevel` were written as the accumulation's mirror of the scanner's
indent stack, each carrying a `col : Int` "matching scanner's
`IndentEntry.column`", and no producer was ever written.  Deleting both raises
four errors, all of them match arms, and `nil` alone is then total.  Two things
generalize.  A constructor FIELD is even quieter than a constructor: every arm
binds it `_`, so a rename probe cannot find its readers and only deletion can.
And the reason it mattered is the corollary above read forwards — the ledger's
next item was to hang U3's frames ↔ indent-stack coupling on exactly this
carrier, because its DOCUMENTATION said it mirrored the stack.  A carrier's
docstring is a plan; its constructors are the fact.

§1 the escape with an entrance (Reflection 672's shape) — and the entrance,
executable.  §2 the repaired machine, where the entrance is gone and the
transport arm still compiles.  §3 the deletion, and why it is the measurement:
the reduced type steps the same way on everything reachable.
-/

namespace L4YAML.Tests.Reflections.EscapeWithNoEntrance

/-- The invariant: a rich reading with fuel, or the renounced state carrying
    one absorbing close (Reflection 672's `FlowStackB.shape`). -/
inductive Inv : Nat → Type where
  | rich (d : Nat) (fuel : Nat) : Inv d
  | shape (d : Nat) (close : Unit → String) : Inv d

/-- The one question asked of a state below: is it the escape? -/
def isShape {d : Nat} : Inv d → Bool
  | .rich _ _ => false
  | .shape _ _ => true

/-! ## §1  The escape WITH an entrance

The original step renounces when the reading runs out of fuel.  The entrance
is a computation, so it can be exhibited. -/

def stepOld {d : Nat} : Inv d → Inv d
  | .rich _ 0 => .shape d (fun _ => "dropped")
  | .rich _ (f + 1) => .rich d f
  | .shape _ close => .shape d close

/-- The entrance, executable: a RICH state becomes the escape. -/
example : stepOld (.rich 1 0) = .shape 1 (fun _ => "dropped") := rfl

/-- …so "no rich state reaches the escape" is FALSE of this machine.  This is
    the half a later reader must re-check rather than assume: the rule below
    is about the repaired machine, not about renounced states in general. -/
example : ¬ (∀ (s : Inv 1), isShape s = false → isShape (stepOld s) = false) :=
  fun h => by simpa [isShape, stepOld] using h (.rich 1 0) rfl

/-! ## §2  The repaired machine

The floors refute the renounce event: the reading always extends.  Nothing
else changes — the transport arm keeps its text, its type and its place in the
case tree, which is exactly why the closure goes unnoticed. -/

def step {d : Nat} : Inv d → Inv d
  | .rich _ f => .rich d (f + 1)
  -- The transport arm.  Still well-typed, still matched, never entered.
  | .shape _ close => .shape d close

/-- The machine, run for `k` steps. -/
def run {d : Nat} : Nat → Inv d → Inv d
  | 0, s => s
  | k + 1, s => run k (step s)

/-- Every producer of the escape consumes one: the step preserves "not the
    escape", so no run from a `rich` seed ever reaches it.  In the toy this is
    provable; in a 23 000-line file it is not — see §3. -/
theorem no_entrance {d : Nat} :
    ∀ (k : Nat) (s : Inv d), isShape s = false → isShape (run k s) = false := by
  intro k
  induction k with
  | zero => intro s h; exact h
  | succ k ih =>
    intro s h
    exact ih (step s) (by
      cases s with
      | rich => simp [step, isShape]
      | shape => exact absurd h (by simp [isShape]))

/-! ## §3  The deletion IS the measurement

A census of the escape's construction sites is a hypothesis: a transport site
and a birth site read the same.  What settles it is the reduced type — the
same invariant with the constructor gone — and the fact that the machine still
steps.  The erasure commutes, so nothing reachable was carried by the arm that
was removed. -/

/-- The reduced invariant. -/
inductive Inv' : Nat → Type where
  | rich (d : Nat) (fuel : Nat) : Inv' d

def step' {d : Nat} : Inv' d → Inv' d
  | .rich _ f => .rich d (f + 1)

def embed {d : Nat} : Inv' d → Inv d
  | .rich _ f => .rich d f

/-- The deletion loses nothing: the reduced machine's step is the original's,
    on everything the original can reach. -/
theorem embed_commutes {d : Nat} (s : Inv' d) : embed (step' s) = step (embed s) := by
  cases s <;> simp [embed, step', step]

/-- …and the seed is in the reduced type, which is what makes the previous
    line a statement about every run rather than about one state. -/
example : Inv' 0 := .rich 0 7

end L4YAML.Tests.Reflections.EscapeWithNoEntrance

end Blanket
