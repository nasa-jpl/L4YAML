/-!
# Reflection 364 — demoting a recursion's DISPATCH from METRIC-keyed to STRUCTURE-keyed does not delete a
downstream arm's metric fact; the fact migrates from "dispatch byproduct" to "structural derivation", and
that derivation already exists as an inline block inside the metric-keyed SIBLING — lift it to a standalone
brick.

Self-contained (core Lean, no `L4YAML` import) toy model of the move found while closing the
emission-spine-walk locator's ADVANCE-arm cut fact (`nestedSeq_recseqentry_locate_advance_balance`, R364).

The locator (R350) dispatches its branches by pure LENGTH ARITHMETIC (`move_trichotomy`), "balance demoted
to the correctness side, never the decision." But its ADVANCE arm's `WellTyped` supplier (R363) consumes a
balance-`0` cut fact `flowBracketBalance tokens off (off+e.length+1) = 0`. In the metric-keyed SIBLING
`seqWindowRecSeqBody`, the analogous fact `h_bal_m1` falls out of the dispatch FOR FREE — the dispatch
LOCATES the separator `m` by `balance lo m = 0`, then adds the comma's delta-`0`. The length-arithmetic
locator makes no such balance call. Where does its cut fact come from?

R364's answer: re-source it STRUCTURALLY — the head entry is a complete balanced unit
(`RecSeqEntry e ⇒ pbalance e = 0`) and the `.flowEntry` separator has delta `0`, so `e ++ [fe]` is balanced.
And that derivation is NOT new: it is the `h_bal_sep` block already proven inline inside the metric-keyed
sibling `recseqbody_advance`. The brick is that block lifted standalone, keyed on the new recursion's frame.

This toy mirrors that faithfully. `bal` is a type-blind cumulative balance (toy of `flowBracketBalance` /
`pbalance`). `sep` is a delta-`0` separator (toy of `.flowEntry`). `EntryOk` is the structural completeness
predicate that PROJECTS to `bal e = 0` (toy of `RecSeqEntry` + `toWellBracketed`). `metricCut` is the
metric-keyed sibling: it gets `bal e = 0` from a LOCATED separator (the dispatch byproduct). `structureCut`
is the lifted brick: it gets the SAME `bal e = 0` from `EntryOk.balanced` (structure), and its downstream
body — `bal_append_sep`, the inline cut algebra — is TOKEN-IDENTICAL to `metricCut`'s. The fact migrated, it
did not vanish. The POSITIVE shows a concrete complete entry whose cut is `bal (e ++ [sep]) = 0`. The
NEGATIVE shows `EntryOk` is LOAD-BEARING (just like `RecSeqEntry`): an incomplete `e` (a lone opener,
`bal ≠ 0`) cannot build `EntryOk`, and its cut fact is genuinely FALSE — so the structural hypothesis cannot
be dropped, the metric fact must come from somewhere.
-/

namespace Tests.Reflections.DemotedDispatchMetricFromStructure

set_option autoImplicit false

/-! ## The bracket alphabet + type-blind cumulative balance -/

/-- `os`/`cs` = `[`/`]`; `sep` = a delta-`0` separator (toy of `.flowEntry`); `a` = a balance-neutral atom. -/
inductive Brak | os | cs | sep | a
  deriving DecidableEq, BEq, Repr

open Brak

/-- Type-blind balance delta — the separator and atoms are `0`, the bracket pair `±1`. -/
def delta : Brak → Int
  | os => 1 | cs => -1 | sep => 0 | a => 0

/-- Cumulative balance (toy of `flowBracketBalance` / `pbalance`). -/
def bal (l : List Brak) : Int := l.foldl (fun acc b => acc + delta b) 0

/-- The append-a-singleton balance step — `bal (e ++ [x]) = bal e + delta x`.  This is the substrate
    bridge both the metric sibling and the structural brick fold through (toy of the
    `pbalance_append` + `flowBracketBalance_eq_pbalance` composition). -/
theorem bal_append_singleton (e : List Brak) (x : Brak) :
    bal (e ++ [x]) = bal e + delta x := by
  unfold bal
  rw [List.foldl_append]
  simp

/-! ## The STRUCTURAL completeness predicate — projects to `bal e = 0` (toy of `RecSeqEntry`) -/

/-- The head entry's structural completeness, projecting to its balance (toy of `RecSeqEntry e` whose
    `toWellBracketed.1` gives `pbalance e = 0`).  In the real proof this is an inductive with four
    constructors; here we keep the single field the cut derivation actually reads. -/
structure EntryOk (e : List Brak) : Prop where
  balanced : bal e = 0

/-! ## The METRIC-keyed sibling and the STRUCTURE-keyed lifted brick — SAME downstream body -/

/-- **The metric-keyed sibling's inline cut** (toy of `recseqbody_advance`'s `h_bal_sep`,
    `seqWindowRecSeqBody`'s `h_bal_m1`).  Its `bal e = 0` is the DISPATCH BYPRODUCT — the metric-keyed
    dispatch LOCATED the separator at the window position where balance returns to `0`, handing this in.
    The cut `bal (e ++ [fe]) = 0` then folds through `bal_append_singleton` + the separator's delta-`0`. -/
theorem metricCut (e : List Brak) (fe : Brak)
    (h_located : bal e = 0)         -- the located-separator balance, FROM the metric dispatch
    (h_fe : delta fe = 0) :
    bal (e ++ [fe]) = 0 := by
  rw [bal_append_singleton, h_located, h_fe]; rfl

/-- **The structure-keyed lifted brick** (toy of `nestedSeq_recseqentry_locate_advance_balance`, R364).
    The length-arithmetic dispatch makes NO balance call, so `bal e = 0` is re-sourced from the head
    entry's STRUCTURE — `h_entry.balanced` (toy of `RecSeqEntry.toWellBracketed.1`).  Note the body below
    is TOKEN-IDENTICAL to `metricCut`'s: only the SOURCE of `bal e = 0` differs (`h_entry.balanced` vs the
    located `h_located`).  The metric fact migrated from dispatch byproduct to structural derivation — the
    inline block did not change, it was lifted. -/
theorem structureCut (e : List Brak) (fe : Brak)
    (h_entry : EntryOk e)           -- the STRUCTURAL completeness, replacing the located balance
    (h_fe : delta fe = 0) :
    bal (e ++ [fe]) = 0 := by
  rw [bal_append_singleton, h_entry.balanced, h_fe]; rfl

/-! ## POSITIVE — a concrete complete entry whose ADVANCE cut is `bal (e ++ [sep]) = 0` -/

-- a complete `[ a ]` entry (balanced) followed by the depth-`0` separator.
def entryPos : List Brak := [os, a, cs]
def fePos : Brak := sep

#guard bal entryPos == 0            -- the entry is a complete balanced unit
#guard delta fePos == 0             -- the separator has delta 0
#guard bal (entryPos ++ [fePos]) == 0   -- so the entry-plus-separator cut is balance-0

/-- The structural completeness is constructible on the concrete entry. -/
example : EntryOk entryPos := ⟨by decide⟩

/-- The lifted brick FIRES on the concrete entry — the ADVANCE cut fact lands from STRUCTURE, with no
    located separator (`metricCut` would need the balance handed in; `structureCut` derives it). -/
example : bal (entryPos ++ [fePos]) = 0 :=
  structureCut entryPos fePos ⟨by decide⟩ (by decide)

/-! ## NEGATIVE — `EntryOk` is LOAD-BEARING; an incomplete entry cannot produce the cut -/

-- a lone opener `[` — NOT a complete entry (`bal = 1`), the structural hypothesis fails.
def incomplete : List Brak := [os]

#guard bal incomplete == 1                    -- not balanced…
#guard bal (incomplete ++ [sep]) == 1         -- …so the cut fact is genuinely FALSE (≠ 0).

/-- The cut fact is false for the incomplete entry — the metric fact does NOT hold for arbitrary `e`. -/
example : bal (incomplete ++ [sep]) ≠ 0 := by decide

/-- So `EntryOk incomplete` is uninhabitable: the structural completeness is load-bearing (exactly as
    `RecSeqEntry` is) — without it the brick cannot fire, and the migrated metric fact must come from the
    structure, never invented. -/
example : ¬ EntryOk incomplete := fun h => absurd h.balanced (by decide)

end Tests.Reflections.DemotedDispatchMetricFromStructure
