/-!
# Reflection 323 — a VACUOUSLY-PROVEN POSITIVE cannot EXCLUDE the case its premise forbids; thread a DISCRIMINATOR that contradicts the conclusion

Self-contained (core Lean) toy of the R323 finding in the seq `RecSeqBody` window producer
(`seqWindowRecSeqBody`).

The real situation: the per-window recursion's advance branch must rule out a *trailing
separator* (`m + 1 = hi` — a comma at the window's last interior position).  The carrier was
believed to forbid it via `noTrailingSepFact tokens lo hi`, of shape
`(last position is a depth-`0` separator) → isFlowContentStart tokens[hi]`.  That fact is
proven VACUOUSLY at the root (no trailing comma exists, so the premise is refuted internally).

The trap: a vacuously-true `prem → pos` hands the CONSUMER only `pos`, never `¬ prem`.  And the
conclusion `isFlowContentStart tokens[hi]` is CONSISTENT with the very trailing-comma window it
was meant to forbid — the three-conjunct guard `G` (balanced + Dyck + seq-enclosed) genuinely
admits a window `[… ,]` whose `tokens[hi]` is content.  So the carrier alone provably cannot
exclude `m + 1 = hi`.

The resolution: thread a DISCRIMINATOR that directly contradicts the conclusion.  Here the
recursion maintains "`hi` is the enclosing close" as an invariant the guard never carried;
making `tokens[hi]! = .flowSequenceEnd` an explicit `G`-conjunct gives `¬ isFlowContentStart
tokens[hi]`, which with the carrier's positive yields the refutation `m + 1 ≠ hi`.

This file models the shape abstractly: a tiny token alphabet, the vacuous-positive carrier fact,
a NEGATIVE theorem that the carrier ALONE is co-satisfiable with the bad case (cannot exclude
it), and a POSITIVE theorem that the carrier PLUS the window-END discriminator excludes it.

Sharpens `ProbeDeferredUniversalBeforeProducing` (a draft-`sorry` on the suspected obligation
surfaced the gap the plan narrative hid) and complements `DownstreamDeriskRestoresUpstream`
(a later consumer's de-risk re-opens a deliverable — here the window-END invariant is restored
into the guard / IH-thread, not the producer body).
-/

namespace Tests.Reflections.VacuousPositiveCannotExclude

set_option autoImplicit false

-- ════════════════════ A tiny token alphabet (toy of `YamlToken`) ════════════════════
inductive Tok where
  | content   -- a scalar / `[` / `{` head (toy of `isFlowContentStart`)
  | sep       -- a `.flowEntry` separator `,`
  | close     -- the enclosing bracket's close `]` (the window-END token)
deriving DecidableEq

/-- The conclusion of the carrier fact (toy of `isFlowContentStart tokens[hi]`). -/
def isContentStart (t : Tok) : Prop := t = .content

-- ════════════════════ The carrier fact: a VACUOUS-POSITIVE implication `prem → pos` ════════════════════
/-- `noTrailingSep lastIsSep bnd` is the carrier fact's shape (toy of `noTrailingSepFact`):
    "IF the window ends on a separator (`lastIsSep`) THEN the boundary token `bnd` (= `tokens[hi]`)
    is a content start".  At the root it is proven VACUOUSLY (no trailing separator), so the
    premise is refuted and the conclusion never actually fires. -/
def noTrailingSep (lastIsSep : Prop) (bnd : Tok) : Prop := lastIsSep → isContentStart bnd

-- ════════════════════ NEGATIVE — the carrier ALONE cannot exclude the bad case ════════════════════
/-- The vacuous positive is CO-SATISFIABLE with the very case its premise was meant to forbid:
    take the boundary token to be `.content`, then `noTrailingSep` holds (its conclusion is
    `isContentStart .content`, true) WHILE `lastIsSep` also holds.  So from `noTrailingSep` one
    cannot derive `¬ lastIsSep` — the carrier, alone, has NO exclusion power. -/
theorem carrier_cannot_exclude :
    ∃ (lastIsSep : Prop) (bnd : Tok), noTrailingSep lastIsSep bnd ∧ lastIsSep := by
  refine ⟨True, .content, ?_, trivial⟩
  intro _; rfl

-- ════════════════════ The DISCRIMINATOR — the window-END invariant ════════════════════
/-- The window-END invariant the recursion maintains (toy of `tokens[hi]! = .flowSequenceEnd`):
    the boundary token is the enclosing CLOSE.  The guard silently assumed this; it must be made
    explicit. -/
def windowEnd (bnd : Tok) : Prop := bnd = .close

/-- The discriminator directly CONTRADICTS the carrier's positive conclusion: a close is not a
    content start. -/
theorem close_not_contentStart {bnd : Tok} (h : windowEnd bnd) : ¬ isContentStart bnd := by
  unfold windowEnd at h; subst h; unfold isContentStart; decide

-- ════════════════════ POSITIVE — carrier PLUS discriminator EXCLUDES the bad case ════════════════════
/-- With the window-END discriminator in hand, the carrier's positive becomes a CONTRADICTION at
    the bad case, yielding the refutation `¬ lastIsSep` (toy of `m + 1 ≠ hi`).  This is exactly
    `seqWindowRecSeqBody`'s O1 discharge: `feContentStart` gives `isFlowContentStart tokens[hi]`,
    the fourth `G`-conjunct gives `tokens[hi]! = .flowSequenceEnd`, and the two collide. -/
theorem exclude_with_discriminator {lastIsSep : Prop} {bnd : Tok}
    (h_carrier : noTrailingSep lastIsSep bnd) (h_end : windowEnd bnd) : ¬ lastIsSep := by
  intro h_sep
  exact close_not_contentStart h_end (h_carrier h_sep)

end Tests.Reflections.VacuousPositiveCannotExclude
