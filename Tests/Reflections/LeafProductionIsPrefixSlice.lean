/-!
# Reflection 351 — the LEAF (the only deliverable-PRODUCING move of a position-navigator) is balance-FREE even on the CORRECTNESS side: its window identity is a pure prefix-slice fact; balance is confined to the non-producing interior MOVES

Self-contained (core Lean, no `L4YAML` import) toy model of the AUTHORING result that landed the leaf
of `nestedSeq_recseqentry_locate` (`(i'-b-B2c-nested-fbc-emission-locator-author)`).  R350 split a
position-indexed navigator into a DECISION (which child — arithmetic) and a CORRECTNESS (why — balance)
and demoted balance to the correctness side.  AUTHORING the leaf SHARPENS that: R350's "correctness needs
balance" is too coarse.  The leaf — the SINGLE move that produces the deliverable (descend/advance only
re-base and recurse) — has a CORRECTNESS obligation (the window identity `(take (off+e.length)).drop off
= e`) that is ITSELF balance-free: a pure `take`/`drop` prefix-slice fact, derivable from the navigator's
offset-slice invariant `body = (take H).drop off` plus "the head entry `e` is a prefix of `body`".

THE FINDING — THE LEAF'S CORRECTNESS IS A PREFIX SLICE, NOT BALANCE.  Given `(L.take H).drop off = e ++
rest` (the navigator carries this; `e` is the head entry, a prefix) and the fit bound `off + e.length ≤
H`, the window identity `(L.take (off+e.length)).drop off = e` follows by `take_take` (re-base the cut to
`H`) + `drop_take` (swap order) + `take_append_of_le_length` (read off the prefix).  No `pbalance`, no
matching-bracket, no Dyck floor.  So at the leaf BOTH halves of R350's split are cheap: the decision is
length arithmetic (`a = off+1`), and the correctness is prefix slicing.

THE FINDING — BALANCE IS CONFINED TO THE NON-PRODUCING MOVES.  The only place balance can enter the
locator is the DESCEND / ADVANCE navigation — proving the target window lies in the head entry's INTERIOR
vs in `rest` (which child).  Those moves produce NOTHING (they re-base `off` and recurse); the leaf
produces EVERYTHING.  So the deliverable-producing case is the balance-free case, and the entire balance
burden lives in the moves that only steer.  "The producing case is the easy case."

THE TRANSFERABLE RULE.  When a position-navigator over a recursive deliverable stores its children as
prefixes/segments and carries an offset-slice invariant tying structure to coordinates, AUTHOR THE LEAF
FIRST and expect its correctness (the window identity) to be PURE SLICE ALGEBRA, not the metric (balance)
the forward locate used.  If you find yourself reaching for balance to justify the leaf's output, you are
over-engineering — balance belongs to the interior MOVES (which child), never the leaf's PRODUCTION.
Probe the slice fact closes from the offset invariant + prefix BEFORE authoring (it did, axiom-clean).

Sharpens [[ref-navigator-dispatch-is-arithmetic]] (R350: locates WHERE balance enters — not even the
leaf's correctness, only the interior moves) and [[ref-near-leaf-mirror-sheds-machinery]] (the near-leaf
is the producer's SIMPLIFICATION; here the leaf sheds even the correctness-side metric).  The slice fact
is the window identity [[ref-from-located-assembler-direction]]'s assembler consumes.
-/

namespace Tests.Reflections.LeafProductionIsPrefixSlice

set_option autoImplicit false

/-! ## The leaf's correctness is a pure prefix-slice fact (no balance) -/

/-- **The head-entry slice fact** — the LEAF's whole correctness obligation, balance-free.  Given the
    navigator's offset-slice invariant `(L.take H).drop off = e ++ rest` and the fit bound
    `off + e.length ≤ H`, the head-entry window `(L.take (off+e.length)).drop off` equals the prefix `e`.
    Pure `take`/`drop` algebra; this is the real `head_entry_slice` landed in `NonemptyStructure.lean`. -/
theorem head_entry_slice {α : Type} (L : List α) (off H : Nat) (e rest : List α)
    (h_body : (L.take H).drop off = e ++ rest) (h_le : off + e.length ≤ H) :
    (L.take (off + e.length)).drop off = e := by
  have h1 : L.take (off + e.length) = (L.take H).take (off + e.length) := by
    rw [List.take_take]; congr 1; omega
  rw [h1, List.drop_take, h_body, List.take_append_of_le_length (by omega)]; simp

/-- The leaf's DECISION is length arithmetic — it fires exactly at `a = off + 1` (R350). -/
def leafFires (off a : Nat) : Prop := a = off + 1

theorem leaf_decision_is_arithmetic (off a : Nat) (h : a = off + 1) : leafFires off a := h

/-! ## The split, distilled: leaf = decision + correctness, BOTH balance-free -/

/-- A toy "needs balance" marker — the metric the FORWARD/top-down locate used. -/
def Balance (_off _a : Nat) : Prop := True

/-- **POSITIVE — the leaf's correctness needs NO balance.**  The window identity (modeled by the slice
    fact specialized to a concrete prefix) is delivered with no `Balance` hypothesis whatsoever. -/
theorem leaf_correctness_balance_free {α : Type} (L : List α) (off H : Nat) (e rest : List α)
    (h_body : (L.take H).drop off = e ++ rest) (h_le : off + e.length ≤ H) :
    (L.take (off + e.length)).drop off = e :=
  head_entry_slice L off H e rest h_body h_le

/-- **NEGATIVE — importing balance into the leaf is REDUNDANT over-engineering.**  A hypothetical leaf
    that also demanded `Balance` produces the very same window identity the slice fact already gives — the
    extra hypothesis is dead.  Don't reach for the metric to justify the leaf's output. -/
theorem leaf_with_balance_redundant {α : Type} (L : List α) (off H : Nat) (e rest : List α)
    (_hb : Balance off off)
    (h_body : (L.take H).drop off = e ++ rest) (h_le : off + e.length ≤ H) :
    (L.take (off + e.length)).drop off = e :=
  head_entry_slice L off H e rest h_body h_le

/-! ## Balance is confined to the non-producing interior moves -/

/-- The three navigator moves; only `leaf` produces the deliverable. -/
inductive Move where | leaf | descend | advance

/-- Whether a move PRODUCES the deliverable.  Only the leaf does; descend/advance re-base and recurse. -/
def produces : Move → Bool
  | .leaf => true | .descend => false | .advance => false

/-- Whether a move's justification CAN involve balance (which-child reasoning).  Only the interior moves
    (descend/advance) do; the leaf's correctness is the balance-free slice fact above. -/
def usesBalance : Move → Bool
  | .leaf => false | .descend => true | .advance => true

/-- **The confinement, distilled** — the producing move and the balance-using moves are DISJOINT: every
    move either produces the deliverable (leaf, balance-free) or only steers (descend/advance, may use
    balance), never both.  "The producing case is the easy case." -/
theorem producing_is_balance_free : ∀ m : Move, produces m = true → usesBalance m = false := by
  intro m h; cases m <;> simp_all [produces, usesBalance]

end Tests.Reflections.LeafProductionIsPrefixSlice
