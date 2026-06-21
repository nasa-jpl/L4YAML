/-!
# Reflection 482 — the located encloser is at depth ≥ 1, so the close locator must be DEPTH-GENERAL;
# the matching-close scan is purely RELATIVE, so the depth-0 lemma re-bases mechanically.

Self-contained (core Lean, no `L4YAML` import) toy recording what R482 discovered while trying to wire
the (α) seq assemble `seqEnclosingLocate_of_seqOpener_at_depth` (R481) into
`seqWidthEnc_of_enclosingLocate_and_recIH` (R475).

**The obstruction.**  The seq carrier `seqLocalCarrier_of_widthEnc` locates, at every gated window
`[a, b)`, its INNERMOST enclosing opener `p` (`seqEnclosingOpener_of_gate`) and asks
`enclosingLocate`/`h_widthEnc` for `p`'s full bracket span `[p, hiE)`.  For a DEEPLY-NESTED gated window
the innermost encloser `p` sits at depth ≥ 1 in the body window — so the R481 assemble's
`h_p_depth : flowBracketBalance tokens lo p = 0` (inherited from `seqClose_of_located_and_enclosing_within`
and ultimately `flowBracketBalance_matching_close_seq`'s `h_k_depth`) is FALSE.  The depth-0-only close
locator cannot find a nested opener's matching close, so the naive wiring is impossible — the first
discriminator (`h_open : .flowSequenceStart`) is FREE in the consume context
(`seqOpenerType_of_located_and_gate`, from the gate's enclosure mark), but the SECOND (`h_p_depth`) is
not even true.

**The fix — re-base, don't re-restrict.**  The matching-close SCAN never reads the opener's absolute
depth; every clause is a DIFFERENCE from the opener's own level `balance lo k`.  So the depth-0 lemma
`flowBracketBalance_matching_close` generalizes to a nested opener purely by substituting the return
level `0 ↦ balance lo k` and the just-after-opener level `1 ↦ balance lo k + 1`; the global Dyck floor
`≥ 0`, load-bearing in the depth-0 proof's recurse step, survives only to pin the opener's own depth
`d ≥ 0` (the recurse step now leans on the threaded interior invariant instead).  That is exactly the
landed production brick `flowBracketBalance_matching_close_nested`
(`L4YAML/Proofs/Parser/ParserGrammableBase.lean`).

This toy abstracts the running balance as an arbitrary `B : Nat → Int` and the matching-close relation
as `matchesClose`, then proves (1) the relation is invariant under a uniform SHIFT of `B` — the formal
content of "the scan is depth-relative, so depth-0 re-bases to any depth"; and (2) a concrete NESTED
opener genuinely sits at depth `1 ≠ 0`, the obstruction that makes the depth-0 locator inapplicable.
-/

namespace DepthGeneralMatchingClose

set_option autoImplicit false

/-- `B` is a running bracket balance over positions `0 … N`.  `matchesClose B k j` says position `j` is
    the matching close of an opener at `k`: `j` sits one ABOVE the opener's own depth (`B j = B k + 1`),
    the close step at `j` RETURNS to the opener's depth (`B (j+1) = B k`), and the interior never drops
    back to the opener's depth (`B i ≥ B k + 1` for `k < i ≤ j`).

    Crucially every clause is a DIFFERENCE from `B k` — the opener's own depth — never an absolute
    value.  This is the depth-free shape the production lemma's conclusion takes
    (`balance (k+1) j = 0`, `balance (k+1) i ≥ 0`). -/
def matchesClose (B : Nat → Int) (k j : Nat) : Prop :=
  k < j ∧ B j = B k + 1 ∧ B (j + 1) = B k ∧
    (∀ i, k < i → i ≤ j → B i ≥ B k + 1)

/-- **The matching-close relation is DEPTH-FREE — invariant under a uniform shift of the balance.**
    Raising or lowering the opener's depth by a constant `c` (`B' n = B n + c`) changes nothing: every
    clause is a difference from `B k`, so the `+ c` cancels.  This is the formal reason
    `flowBracketBalance_matching_close` generalizes from a depth-0 opener to a NESTED one by merely
    re-basing the return level `0 ↦ balance lo k` — the scan never reads the absolute depth.

    (What does NOT shift-transfer is the GLOBAL Dyck floor `B i ≥ 0`: under the shift it becomes
    `B' i ≥ c`, so it cannot be reduced from the depth-0 lemma.  In the real proof this is exactly why
    the global floor survives only to pin `d ≥ 0` while the recurse step switches to the threaded
    interior invariant — the generalization re-proves rather than reduces.) -/
theorem matchesClose_shift (B B' : Nat → Int) (c : Int) (hc : ∀ n, B' n = B n + c) (k j : Nat) :
    matchesClose B k j ↔ matchesClose B' k j := by
  unfold matchesClose
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, ?_⟩
    · rw [hc j, hc k]; omega
    · rw [hc (j + 1), hc k]; omega
    · intro i hi hj; rw [hc i, hc k]; have := h4 i hi hj; omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, ?_, ?_⟩
    · rw [hc j, hc k] at h2; omega
    · rw [hc (j + 1), hc k] at h3; omega
    · intro i hi hj; have h5 := h4 i hi hj; rw [hc i, hc k] at h5; omega

/-- A balance for `[ [ x ] ]` (outer `[`, inner `[`, scalar, inner `]`, outer `]`).  The INNER opener
    sits at position `1` (just after the outer `[`), at depth `B 1 = 1`. -/
def Bnest : Nat → Int
  | 0 => 0      -- before the outer `[`
  | 1 => 1      -- after the outer `[` — the inner opener sits HERE, at depth 1
  | 2 => 2      -- after the inner `[`
  | 3 => 2      -- after the scalar `x`
  | 4 => 1      -- after the inner `]`  (returns to the inner opener's depth)
  | _ => 0      -- after the outer `]`

/-- **A NESTED opener genuinely sits at depth ≥ 1** — the obstruction.  The innermost encloser
    `seqEnclosingOpener_of_gate` hands back is at position `1`, where `Bnest 1 = 1 ≠ 0`.  So it CANNOT
    be fed to a `balance lo k = 0` close locator: the depth-0 lemma's precondition is simply false. -/
theorem depth0_precondition_fails : Bnest 1 ≠ 0 := by decide

/-- …yet the nested opener has a perfectly good matching close (`j = 3`): `Bnest 3 = 2 = Bnest 1 + 1`,
    the close step `Bnest 4 = 1 = Bnest 1`, and the interior stays `≥ 2`.  So the close IS locatable —
    just not by a depth-0 scan.  Combined with `matchesClose_shift`, this is the whole R482 point:
    the relation holds at depth 1 exactly as it would at depth 0, because it is shift-invariant. -/
theorem nested_opener_has_matching_close : matchesClose Bnest 1 3 :=
  ⟨by omega, by decide, by decide, by
    intro i hi hj
    have : i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl <;> decide⟩

end DepthGeneralMatchingClose
