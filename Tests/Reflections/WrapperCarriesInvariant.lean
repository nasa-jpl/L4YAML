/-!
# Reflection 353 — the WRAPPER of a position-navigator is NOT among its mechanical slice bricks

Self-contained (core Lean, no `L4YAML` import) toy model of the R353 finding: a de-risk that bins a
position-indexed navigator's remaining steps as "mechanical bricks" mis-bins the WRAPPER.

THE SETTING.  A navigator over a recursive deliverable has moves: a LEAF (produces the deliverable), a
DESCEND and an ADVANCE (re-base coordinates and recurse), and a WRAPPER (the `Nat.strongRecOn` that
threads the trichotomy dispatch over all three).  A de-risk read-ahead ([[ref-read-ahead-consumer-chain-
proof-state]]) batched "descend + advance + wrapper" as mechanical bricks with "no wall."

THE FINDING.  Partition the moves by what each PRODUCES, not by step-list position.  The leaf/descend/
advance SLICE bricks re-base coordinates and produce NOTHING but a re-sliced child — mechanical,
balance-free.  The WRAPPER produces the located deliverable by threading a DOMAIN INVARIANT + a
termination measure.  The tell that the wrapper is a different object: its DESCEND arm must exclude a
SIBLING SHAPE (a map head) that SURVIVES the pure-arithmetic dispatch (its entry is long enough to make
the descend range nonempty) but is killed ONLY by the domain invariant — the arithmetic alone cannot
separate a seq head from a map head.

THE TRANSFERABLE RULE.  When a de-risk bins a navigator's remaining steps as bricks, the wrapper is not
among them; it needs its own interface-design probe before authoring.
-/

namespace Tests.Reflections.WrapperCarriesInvariant

set_option autoImplicit false

/-! ## Moves partition by what they PRODUCE -/

/-- The navigator's moves. -/
inductive Move where
  | leaf | descend | advance | wrapper
deriving DecidableEq

/-- A move is a SLICE BRICK iff it only re-bases coordinates (leaf/descend/advance). -/
def isSliceBrick : Move → Bool
  | .leaf => true | .descend => true | .advance => true | .wrapper => false

/-- A move PRODUCES the located deliverable iff it is the wrapper (the leaf produces the existential
    only WHEN the wrapper drives it to fire; standalone it re-bases like the others — here we model the
    completed deliverable as the wrapper's output). -/
def producesDeliverable : Move → Bool
  | .wrapper => true | _ => false

/-- **POSITIVE — the slice bricks produce nothing.**  Every move flagged a slice brick has
    `producesDeliverable = false`: they re-base coordinates only. -/
theorem slice_bricks_produce_nothing :
    ∀ m : Move, isSliceBrick m = true → producesDeliverable m = false := by
  intro m h; cases m <;> first | rfl | exact absurd h (by decide)

/-- **POSITIVE — the wrapper is the complement: it produces the deliverable and is NOT a slice brick.** -/
theorem wrapper_produces_and_is_not_a_brick :
    producesDeliverable .wrapper = true ∧ isSliceBrick .wrapper = false :=
  ⟨rfl, rfl⟩

/-! ## The DESCEND arm carries a domain-invariant obligation the slice bricks never touch -/

/-- The head-entry shapes the navigator's DESCEND arm can meet. -/
inductive HeadShape where
  | scalar | seqEmpty | seqNonempty | mapNonempty
deriving DecidableEq

/-- Entry token-length per shape: scalar `1`, empty seq `[]` → `2`, nonempty seq/map ≥ `4`. -/
def entryLen : HeadShape → Nat
  | .scalar => 1 | .seqEmpty => 2 | .seqNonempty => 4 | .mapNonempty => 4

/-- The trichotomy DESCENDs at `off+1 < a < off+entryLen`, a range nonempty iff `entryLen > 2`.
    This is the PURE-ARITHMETIC dispatch — blind to which constructor the head is. -/
def survivesArithmeticDispatch (h : HeadShape) : Bool := entryLen h > 2

/-- The domain invariant (`SeqPathAllSeq`): a seq head keeps the all-`true` path; a map head pushes
    `false` and breaks it.  This is what the wrapper's DESCEND arm must thread. -/
def domainAllows : HeadShape → Bool
  | .scalar => true | .seqEmpty => true | .seqNonempty => true | .mapNonempty => false

/-- **POSITIVE — scalars and empties are excluded by ARITHMETIC alone** (the slice-brick-friendly part):
    their descend range is empty, so they never reach the DESCEND arm — no invariant needed. -/
theorem scalar_empty_excluded_by_arithmetic :
    survivesArithmeticDispatch .scalar = false ∧ survivesArithmeticDispatch .seqEmpty = false :=
  ⟨rfl, rfl⟩

/-- **NEGATIVE — a MAP head SURVIVES the arithmetic dispatch.**  `entryLen .mapNonempty = 4 > 2`, so the
    pure-arithmetic trichotomy would DESCEND into it — but descending into a map interior is wrong. -/
theorem arithmetic_dispatch_admits_map :
    survivesArithmeticDispatch .mapNonempty = true := rfl

/-- **NEGATIVE — arithmetic CANNOT separate a seq head from a map head.**  Both survive the dispatch, so
    the decision procedure alone is blind to the difference — exactly why the wrapper is not a mechanical
    brick. -/
theorem arithmetic_cannot_separate_seq_from_map :
    survivesArithmeticDispatch .seqNonempty = survivesArithmeticDispatch .mapNonempty := rfl

/-- **POSITIVE — only the DOMAIN INVARIANT separates them.**  `domainAllows` distinguishes the seq head
    (`true`) from the map head (`false`); so the wrapper's DESCEND arm MUST thread the invariant to
    exclude the map head the arithmetic would wrongly take.  This obligation is what makes the wrapper the
    invariant-bearing assembly, not a slice brick. -/
theorem invariant_separates_seq_from_map :
    domainAllows .seqNonempty ≠ domainAllows .mapNonempty := by decide

end Tests.Reflections.WrapperCarriesInvariant
