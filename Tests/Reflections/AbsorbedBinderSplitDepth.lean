/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Reflection 407 — un-ignoring an absorbed binder: the split DEPTH is arm-specific

Self-contained toy for [[ref-absorbed-binder-split-depth-per-glue]].

When you mirror a co-produced field onto a multi-arm producer (Reflection 406), each arm
READS the field off a per-item predicate whose tail conjuncts are currently ABSORBED into
one `_`-ignored binder.  To feed the field to the arm's glue lemma you un-ignore that
binder — and the DEPTH you un-ignore to is ARM-SPECIFIC, set by the arm's glue-lemma
signature, not a uniform split:

  * a glue that ADMITS THE DEGENERATE RIGHT (an append whose right side may be empty)
    reconstructs the boundary INTERNALLY from a pure fact, so it needs only the orthogonal
    FIELD — split shallow (expose just the field, leave the boundary `_`-ignored);
  * a SEAM glue (`left ++ [sep] ++ right`) EXTERNALIZES the boundary as a hypothesis, so for
    a left of shape `inner ++ subblock` it also needs the subblock's degenerate-case facts —
    split deep (expose the boundary too).

The L4YAML case (R407, step (b)-map): `emitPairList_scans_safebody`'s value-block
destructure had one binder absorbing `ContentStart ∧ tail-not-opener ∧ OpenerAdj`.  The
SINGLETON arm's `OpenerAdj_map_single` (admits an empty value block; rebuilds the tail from
the pure token fact `value ≠ .flowSequenceStart`) needed only the `OpenerAdj` → split
`_h_cs_v, _h_btail_v, h_oa_v`.  The CONS arm's `OpenerAdj_seam` (takes the entry's
tail-not-opener as a hypothesis) needed `OpenerAdj` AND the boundary facts (`block_v ≠ []`
from `ContentStart`, plus `block_v`'s tail) → split `h_cs_v, h_btail_v, h_oa_v`.

The toy strips this to its bones.  The producer's conclusion is `Core ∧ Boundary ∧ Field`.
Two arms read it: `single_arm` needs only `Field` (exposes 1 conjunct); `seam_arm` needs
`Field` AND `Boundary` (exposes 2).  Same predicate, different depth.

POSITIVE: both arms type-check from the SAME `produces` at their own depths.
NEGATIVE: the boundary is INDEPENDENT of the field (witness `8`: even, so `Field` holds, but
`¬(8 ≠ 8)`, so `Boundary` fails), so the seam arm CANNOT shortcut to the single arm's shallow
split — it must bind the boundary explicitly. -/

namespace Tests.Reflections.AbsorbedBinderSplitDepth

/-- The producer's conclusion: a flat `∧`-chain `Core ∧ Boundary ∧ Field`.  The L4YAML
    analogue: the value block's `EmitScansInFlowBlock` ends
    `… ∧ ContentStart ∧ tail-not-opener ∧ OpenerAdj` — and a destructure that ignores the
    tail binds all three as ONE absorbed `_`. -/
def produces (n : Nat) : Prop := 0 < n ∧ n ≠ 8 ∧ n % 2 = 0

/-- **SINGLE arm.**  Its glue needs only the orthogonal FIELD; the `obtain` exposes just the
    LAST conjunct and leaves the boundary an ignored `_`.  (L4YAML singleton map case:
    `OpenerAdj_map_single` internalizes the entry's tail via `lastNonOpener_wrap` off a PURE
    token fact and admits an empty right, so it needs only `h_oa_v` → split shallow.) -/
theorem single_arm (n : Nat) (h : produces n) : n % 2 = 0 := by
  obtain ⟨_, _, hf⟩ := h          -- depth: exposes 1 (the field)
  exact hf

/-- **SEAM arm.**  Its glue needs the FIELD *and* the BOUNDARY; the `obtain` must expose TWO
    conjuncts.  (L4YAML cons map case: `OpenerAdj_seam` externalizes the entry's
    tail-not-opener as a hypothesis, rebuilt from the value block's own non-emptiness +
    tail, so the destructure reaches `h_cs_v, h_btail_v, h_oa_v` — deeper than the single
    arm.) -/
theorem seam_arm (n : Nat) (h : produces n) : n % 2 = 0 ∧ n ≠ 8 := by
  obtain ⟨_, hb, hf⟩ := h         -- depth: exposes 2 (boundary + field)
  exact ⟨hf, hb⟩

/-- **NEGATIVE.**  The boundary is INDEPENDENT of the field, so the seam arm cannot read it
    off the field alone — the deeper split is mandatory, not stylistic.  Witness `8`: it is
    even (`Field` holds) yet `¬(8 ≠ 8)` (`Boundary` fails). -/
theorem field_does_not_entail_boundary : ∃ n, n % 2 = 0 ∧ ¬ (n ≠ 8) :=
  ⟨8, by decide, by decide⟩

/-! The negative witness `8` separates the field (holds) from the boundary (fails). -/

-- the field holds for the witness …
#guard (8 % 2 == 0)
-- … but the boundary fails for it, so the seam arm must bind it explicitly.
#guard (decide ((8 : Nat) ≠ 8) == false)

end Tests.Reflections.AbsorbedBinderSplitDepth
