/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Reflection 408 — a carry-up splits at a reversed import edge

Self-contained toy for [[ref-carry-up-splits-at-import-edge]].

A plan says "carry field `F` up through consumer `L` to a global fact `G`", and `G` already has a
landed producer `mkG : per-window F + boundary facts → G`.  It is tempting to call `mkG` INSIDE `L`.
But if `mkG`'s module IMPORTS `L`'s module (the producer lives DOWNSTREAM), `L` cannot reference
`mkG` — the call-graph grain runs the wrong way.  The fix is NOT to move code or restructure imports:
recognize the carry-up was always a TWO-MODULE operation.  `L` EXPOSES the per-window primitive `F`
as an additive CONCLUSION conjunct (the only channel that carries a fact across a reversed import
edge), and the DOWNSTREAM module CONSUMES `L`'s output + the boundary facts into `G`.

The L4YAML case (R408, step (c)): `scanFiltered_emit{Seq,Map}_nonempty_structure` live in
`NonemptyStructure`, but the global producer `globalFlowSeqOpenerAdj_of_structure` lives in
`SeqInteriorSeparators`, which IMPORTS `NonemptyStructure`.  So the structure consumers cannot make
`GlobalFlowSeqOpenerAdj` directly — step (c) EXPOSES the all-depth `.flowSequenceStart`-opener field
over `[2, size-2)` in both structure conclusions (this increment), and the downstream PRODUCE-GLOBAL
is the next sub-step.

The toy strips this to its bones.  A single file cannot have two modules, but DEFINITION ORDER models
the import edge: `expose` (the upstream producer of the window primitive) is defined BEFORE `mkGlobal`
(the downstream global producer) and CANNOT reference it; the window primitive — `expose`'s
conclusion — is the only thing that reaches `mkGlobal`.

POSITIVE: the split WORKS — `expose` outputs `windowField`; `mkGlobal`, consuming `windowField` + a
boundary fact, produces `globalField`.
NEGATIVE: the window primitive ALONE cannot make the global fact — `window_alone_does_not_entail_global`
exhibits `8` (even, so `windowField` holds, but `¬(8 ≠ 8)`, so the boundary fact fails), proving the
downstream producer genuinely needs the boundary fact and the carry-up cannot collapse upstream. -/

namespace Tests.Reflections.CarryUpSplitsAtImportEdge

/-- The per-window primitive (toy of the body opener field over `[2, size-2)`): an interior-only
    property, here "even". -/
def windowField (x : Nat) : Prop := x % 2 = 0

/-- The boundary fact the window primitive does NOT carry (toy of "the end token is the matching
    close" — `.flowSequenceEnd` for seq, `.flowMappingEnd` for map): here "not 8". -/
def boundaryOK (x : Nat) : Prop := x ≠ 8

/-- The global closure (toy of `GlobalFlowSeqOpenerAdj`): the whole = interior primitive + boundary. -/
def globalField (x : Nat) : Prop := x % 2 = 0 ∧ x ≠ 8

/-- **UPSTREAM producer** (the analogue of the structure lemma).  It projects the window primitive out
    of a richer body fact and EXPOSES it as its conclusion — the cross-edge channel.  Defined BEFORE
    `mkGlobal`, so (like the structure lemma vs. the downstream global producer) it cannot reference
    it: the conclusion `windowField x` is the only thing that reaches downstream. -/
theorem expose (x : Nat) (h : 0 < x ∧ x % 2 = 0) : windowField x := h.2

/-- **DOWNSTREAM producer** (the analogue of `globalFlowSeqOpenerAdj_of_structure`).  Defined AFTER
    `expose`, it CONSUMES the upstream window primitive + the boundary fact into the global closure.
    This is the second half of the carry-up; the split is two-module precisely because this consumer
    sits below the import edge. -/
theorem mkGlobal (x : Nat) (hw : windowField x) (hb : boundaryOK x) : globalField x := ⟨hw, hb⟩

/-- **NEGATIVE.**  The window primitive ALONE does not entail the global closure — the boundary fact
    is independent.  Witness `8`: it is even (`windowField` holds) yet `¬(8 ≠ 8)` (`boundaryOK`
    fails), so `globalField 8` is false.  This is why the carry-up cannot collapse into one upstream
    step: the downstream producer genuinely needs the boundary fact `expose` does not carry. -/
theorem window_alone_does_not_entail_global :
    ∃ x, windowField x ∧ ¬ globalField x := by
  refine ⟨8, ?_, ?_⟩
  · unfold windowField; decide
  · intro h; obtain ⟨_, hb⟩ := h; exact absurd hb (by decide)

/-! The split works on a clean witness (`4`), and fails exactly at the boundary (`8`). -/

-- POSITIVE: 4 passes both halves, so the downstream `mkGlobal` produces the global closure.
#guard (4 % 2 == 0 && decide (4 ≠ 8))
-- the window primitive holds for the negative witness `8` …
#guard (8 % 2 == 0)
-- … but the boundary fact fails for it, so the window alone cannot make the global fact.
#guard (decide ((8 : Nat) ≠ 8) == false)

end Tests.Reflections.CarryUpSplitsAtImportEdge
