/-!
# Reflection 389 — a DOMAIN-RESTRICTED producer is REDUNDANT (off the critical path) when an existing
sibling already serves the same universal WHOLE-DOMAIN via a strictly WEAKER guard.

Self-contained core-Lean toy of L4YAML R389.  Continuing the seq frontier, the CONSUME plan queued a
"gate-strengthening bridge" so the forward emission locator (R386–R388, keyed on the all-seq PATH gate
`SeqPathAllSeq`) could discharge `h_seq_rec` (the seq half of `flowSubrangesOk_of_window_producers`,
ranging over EVERY nested seq window).  The de-risk found the bridge FALSE — minimal pair in ONE scanned
object `[["1"], {"a": ["2"]}]`: the map-path inner seq `[2]` has opener stack `[false, true]` (the
enclosing `{` pushed `false`), so it FAILS `SeqPathAllSeq` yet satisfies every `h_seq_rec` guard.  The
tempting conclusion — "split `h_seq_rec`: locator for the all-seq-path part, a fixpoint for the rest" —
is wrong.  An EXISTING sibling, the width driver `seqWindowRecSeqBody`, already serves the WHOLE domain
via the TOP-only `SeqEnclosed` guard (weaker than the path gate), which HOLDS on the excluded `[2]`
window.  So the locator is REDUNDANT; `h_seq_rec` reduces by import to the sibling's residual (the root
carrier), no split.

The transferable rule: when a strong-gate producer `P` cannot bridge to a broader consumer universal
`U` (the bridge `G_U → G_P` is minimal-pair FALSE), DON'T split.  First read the TRUE minimum guard
`G_P'` of an existing sibling `P'`, and test it on the very witness `G_P` excludes — if `G_P'` holds
there, `P'` covers the whole domain and `P` was never on the critical path.

Mapping to L4YAML: `D` ~ `RecSeqBody window`; `GU` ~ `h_seq_rec`'s bracket guards (broad);
`GP` ~ the locator's `SeqPathAllSeq` (strong, narrow); `GP'` ~ `seqWindowRecSeqBody`'s top-only
`SeqEnclosed` (weaker, whole-domain).  `n = 6` ~ the map-path window: in `GU`, outside `GP`, inside
`GP'`.

POSITIVE: `producerP` — `P` delivers `D` under its strong gate; `siblingP'` — `P'` delivers `D` under
its weaker guard; `U_via_sibling` — the consumer universal is discharged WHOLE-DOMAIN through `P'`, no
split; `sibling_covers_excluded` — `P'`'s guard holds on the witness `P` excludes.
NEGATIVE: `bridge_false` — `GU → GP` is false (minimal pair `n = 6`), so `P` cannot serve `U`;
`P_cannot_cover_U` — restated as the coverage gap that would force a (needless) split.

Sharpens [[ref-locate-consumer-by-gate-strength]]; builds on [[ref-reduction-by-import]].
-/

namespace Tests.Reflections.WholeDomainSiblingViaWeakerGuard

set_option autoImplicit false

/-- The deliverable the universal demands. -/
def D (n : Nat) : Prop := n % 2 = 0
/-- The CONSUMER universal's domain (broad): divisible by 6. -/
def GU (n : Nat) : Prop := n % 6 = 0
/-- The restricted producer `P`'s STRONG gate (narrow, NOT ⊇ `GU`): divisible by 4. -/
def GP (n : Nat) : Prop := n % 4 = 0
/-- The sibling `P'`'s TRUE minimum guard (strictly WEAKER than `GP`; covers all of `GU`): even. -/
def GP' (n : Nat) : Prop := n % 2 = 0

/-- The restricted producer: delivers `D` under its strong gate `GP`. -/
theorem producerP (n : Nat) (h : GP n) : D n := by unfold GP at h; unfold D; omega
/-- The sibling producer: delivers `D` under the WEAKER guard `GP'`. -/
theorem siblingP' (n : Nat) (h : GP' n) : D n := by unfold GP' at h; unfold D; exact h

/-- **NEGATIVE — the strengthening bridge is FALSE.**  `GU → GP` fails at the minimal pair `n = 6`
    (divisible by 6, not by 4).  So `P` cannot discharge `U` (in L4YAML: the map-path window passes
    `h_seq_rec`'s guard but fails `SeqPathAllSeq`). -/
theorem bridge_false : ∃ n, GU n ∧ ¬ GP n := by
  refine ⟨6, ?_, ?_⟩ <;> simp [GU, GP]

/-- **The DIAGNOSTIC — the sibling's guard holds on the very witness `GP` excludes.**  `GP' 6` is true
    even though `GP 6` is false.  That single fact proves `P'` covers the case `P` cannot, so the
    "domain split" the false bridge seemed to force collapses: `P` is redundant. -/
theorem sibling_covers_excluded : GP' 6 := by unfold GP'; omega

/-- **POSITIVE (whole-domain, no split).**  The consumer universal is discharged over ALL of `GU`
    through the SIBLING, via the whole-domain coverage `GU → GP'` (divisible-by-6 ⟹ even).  The
    restricted producer `P` never appears — it is verified-but-unconsumed scaffolding. -/
theorem U_via_sibling : ∀ n, GU n → D n := fun n h =>
  siblingP' n (by unfold GU at h; unfold GP'; omega)

/-- **NEGATIVE — what would (needlessly) force a split.**  `P` alone leaves a coverage gap on `GU`:
    some `GU`-witness (n = 6) is outside `GP`.  Naively this reads as "split: `P` for `GP`, something
    else for the rest" — averted precisely because the weaker-guard sibling already covers it. -/
theorem P_cannot_cover_U : ∃ n, GU n ∧ ¬ GP n := bridge_false

#guard 6 % 6 == 0          -- n = 6 is in the consumer's domain GU
#guard !(6 % 4 == 0)       -- but outside the strong gate GP (bridge false here)
#guard 6 % 2 == 0          -- yet inside the sibling's weaker guard GP' — so P' covers it

end Tests.Reflections.WholeDomainSiblingViaWeakerGuard
