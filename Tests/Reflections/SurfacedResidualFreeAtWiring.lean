/-!
# Reflection 486 — a surfaced refinement residual is FREE at the wiring site.

Self-contained (core Lean, no `L4YAML` import) toy recording how R486 *discharged* the consume-side
residual that R481 (`GenericDiscriminantUnderdeterminesOutput`) had *surfaced*.

**The setup (R481).**  The (α) `enclosingLocate` assemble for the seq child needs the TYPE-SPECIFIC
fact `tokens[p]!.val = .flowSequenceStart` (`[`), but the slot R475 offers it is the GENERIC opener
premise `flowBracketDelta tokens[p]!.val = 1` — which admits BOTH `[` and `{`.  R481 proved the
refinement is PROVABLY NOT derivable from that generic premise (a `{` satisfies `delta = 1` yet has a
map child), so the honest move was to SURFACE `.flowSequenceStart` as an explicit hypothesis
`h_open` of the assemble (`seqEnclosingLocate_of_seqOpener_…`).

**The closure (R486 — this reflection).**  When that assemble is finally WIRED into R475
(`seqWidthEnc_of_recIH`), the surfaced residual `h_open` costs the caller NOTHING.  The SAME gate
that delivers `SeqTypedInterior tokens a b` also carries the enclosing-type MARK — its `btFold`-top
`= some true` conjunct (`hgate.2.1`) — and `seqOpenerType_of_located_and_gate` RECONSTRUCTS the `[`
from `delta = 1` + that mark + the locator floor.  So the residual is discharged in place at the
wiring; it never reaches R475's caller interface.

**The transferable rule.**  A refinement surfaced as an explicit consume-side residual (because the
producer's slot names too WEAK a discriminator) is often discharged FOR FREE at the wiring site from
a CO-LOCATED invariant the consumer already carries.  So:

* R481 (the negative): the WEAK premise alone underdetermines the output — surface the refinement,
  don't invent a derivation that cannot exist.
* R486 (the positive): before threading that residual through every caller, CHECK whether the wiring
  context already DETERMINES it.  Two facts that each underdetermine the output can, TOGETHER, pin it
  — the missing refinement is then reconstructed, not supplied.

The discriminating question is not "does the producer's NAMED premise determine the refinement?"
(R481: no) but "does SOME fact co-located at the wiring determine it?" (R486: yes — the gate mark).
A residual is only truly owed by the caller if NO co-located invariant pins it.

This toy models the two premises as predicates over a 3-token alphabet, shows each alone
underdetermines the typed output (so neither is the producer's named premise by accident), and shows
their CONJUNCTION reconstructs the refinement that builds the output — the toy
`seqOpenerType_of_located_and_gate`.
-/

namespace SurfacedResidualFreeAtWiring

set_option autoImplicit false

/-- The token alphabet: a seq opener `[`, a map opener `{`, and a content token. -/
inductive Tok where
  | seqOpen   -- `[`
  | mapOpen   -- `{`
  | content
  deriving DecidableEq

open Tok

/-- **The WEAK discriminator** — the toy `flowBracketDelta tokens[p]!.val = 1`: `p` is SOME opener.
    Admits both `[` and `{`; cannot distinguish them. -/
def delta1 : Tok → Prop
  | seqOpen => True
  | mapOpen => True
  | content => False

/-- **The co-located MARK** — the toy gate's `btFold`-top `= some true` (`hgate.2.1`): the pushed bit
    at this position is `true`.  `[` pushes `true`; `{` pushes `false`; a content token also reads
    `true` here (so the mark ALONE is not opener-specific). -/
def markTrue : Tok → Prop
  | seqOpen => True
  | mapOpen => False
  | content => True

/-- **The refinement** R481 surfaced — the toy `tokens[p]!.val = .flowSequenceStart`: admits only `[`. -/
def isSeqOpener (t : Tok) : Prop := t = seqOpen

/-- **The typed output** the assemble must build — needs the refinement. -/
inductive SeqChild : Tok → Prop where
  | mk : SeqChild seqOpen

/-- The output constructor from the refinement (the toy child-bracket constructors). -/
theorem seqChild_of_seqOpener {t : Tok} (h : isSeqOpener t) : SeqChild t := by
  rw [isSeqOpener] at h; subst h; exact .mk

/-! ### R481 — each premise ALONE underdetermines the output.

Neither `delta1` nor `markTrue` is, by itself, the producer's named premise by accident: each admits
a witness with no seq output.  This is why R481 had to SURFACE the refinement rather than derive it
from the generic `delta1`. -/

/-- The WEAK discriminator alone underdetermines: `{` satisfies `delta1` yet is not a seq child. -/
theorem delta1_alone_underdetermines : delta1 mapOpen ∧ ¬ SeqChild mapOpen := by
  refine ⟨trivial, ?_⟩
  intro h; cases h

/-- The MARK alone underdetermines: a content token reads `markTrue` yet is not even an opener. -/
theorem mark_alone_underdetermines : markTrue content ∧ ¬ SeqChild content := by
  refine ⟨trivial, ?_⟩
  intro h; cases h

/-! ### R486 — the CONJUNCTION reconstructs the refinement.  This is the toy
`seqOpenerType_of_located_and_gate`: `delta1` narrows to `{[, {}` and `markTrue` rules out `{`. -/

/-- **The reconstruction lemma** (toy `seqOpenerType_of_located_and_gate`): the two co-located premises
    TOGETHER pin the refinement that NEITHER pins alone. -/
theorem reconstruct {t : Tok} (hδ : delta1 t) (hm : markTrue t) : isSeqOpener t := by
  cases t with
  | seqOpen => rfl
  | mapOpen => exact absurd hm (by simp [markTrue])
  | content => exact absurd hδ (by simp [delta1])

/-! ### The wiring: the surfaced residual is discharged FOR FREE.

The wiring lemma's interface offers only the WEAK discriminator `delta1` (R475's slot) plus the
co-located `markTrue` (carried by the gate) — NOT the refinement `isSeqOpener`.  Yet it builds the
typed output, because `reconstruct` recovers the refinement in place.  This is `seqWidthEnc_of_recIH`
in miniature: R485's assemble owes `h_open : isSeqOpener`, and the wiring discharges it from the gate,
so the residual never reaches the caller. -/

/-- **The wired producer** (toy `seqWidthEnc_of_recIH`): from the weak discriminator + the co-located
    mark — NO `isSeqOpener` in the interface — the typed output, the residual reconstructed in place. -/
theorem wire {t : Tok} (hδ : delta1 t) (hm : markTrue t) : SeqChild t :=
  seqChild_of_seqOpener (reconstruct hδ hm)

/-- The converse closes the loop: once the OUTPUT is in hand the refinement is recoverable too — so the
    irreducibility R481 found was purely about the too-WEAK named premise (`delta1`), not the
    refinement being unknowable.  The wiring exploits exactly this: a richer co-located fact reaches
    it where the named premise could not. -/
theorem seqOpener_of_seqChild {t : Tok} (h : SeqChild t) : isSeqOpener t := by
  cases h; rfl

end SurfacedResidualFreeAtWiring
