/-! # Reflection 499 — a *unifying* consumer forces a *second, fuller* projection

When a weaker-guard twin's CONSUMER **unifies** a residual the strong consumer **split**, the unified
field ranges over a strictly LARGER domain than the split's boundary-only piece, so the producer's
recursive deliverable must be projected a SECOND way (the fuller projection) that the split residual
never needed. The number of projections of the deliverable a producer must supply is set by the
CONSUMER's choice to split-vs-unify its residual, not by the deliverable's own shape.

This mirrors L4YAML R499 `seqChild_safeBody_seq`, the `SafeBody`-projecting sibling of R494
`seqChild_safeBodyUnit_seq`:

* the strong `flowBodyContent_of_deep` SPLIT the separator obligation — interior from the guard's own
  `feContentStart` field, only the BOUNDARY (last position) as a `noTrailingSepFact`, which the UNIT
  projection (`RecSeqBody.toSafeBodyUnit`) supplies;
* the weaker `flowBodyContent_of_deepSeq` (R393) UNIFIED both grains into ONE `h_feContent` over EVERY
  interior separator (because the weak guard's `feContentStart` carries a `≠ .key` premise undischargeable
  locally), which only the FULL projection (`RecSeqBody.toSafeBody`, via `SafeBody_array_flowEntry_window`)
  supplies.

So the SAME child `RecSeqBody` must be projected BOTH ways; the second projection is the one the
unifying consumer forced. Here `Deliv` models `RecSeqBody`; `unitProj`/`fullProj` model
`.toSafeBodyUnit`/`.toSafeBody`; `GoalBoundary`/`GoalAll` model the split/unified consumer residuals.
-/

namespace UnifiedResidualForcesSiblingProjection

/-- The recursive deliverable (models `RecSeqBody`): a non-empty all-`true` list. -/
inductive Deliv : List Bool → Prop
  | single : Deliv [true]
  | cons (rest : List Bool) : Deliv rest → Deliv (true :: rest)

/-- The UNIT projection (models `.toSafeBodyUnit`): exposes ONE BOUNDARY position (the head). -/
def unitProj (l : List Bool) : Prop := l.head? = some true

/-- The FULL projection (models `.toSafeBody`): exposes EVERY interior position. -/
def fullProj (l : List Bool) : Prop := ∀ x ∈ l, x = true

/-- Both projections come off the SAME deliverable — the unit form by reading the head. -/
theorem Deliv.toUnit : {l : List Bool} → Deliv l → unitProj l
  | _, .single => rfl
  | _, .cons _ _ => rfl

/-- …and the full form by structural recursion (the SECOND projection R499 adds). -/
theorem Deliv.toFull : {l : List Bool} → Deliv l → fullProj l
  | _, .single => by intro x hx; simp only [List.mem_singleton] at hx; exact hx
  | _, .cons rest h => by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · rfl
      · exact h.toFull x hx'

/-- SPLIT consumer (models strong `flowBodyContent_of_deep`): its residual is a BOUNDARY fact, so the
    UNIT projection alone discharges it — only ONE projection of the deliverable is needed. -/
def GoalBoundary (l : List Bool) : Prop := l.head? = some true
theorem split_route {l : List Bool} (h : Deliv l) : GoalBoundary l := h.toUnit

/-- UNIFIED consumer (models weak `flowBodyContent_of_deepSeq`): its residual ranges over EVERY interior
    position, so it is FORCED to the FULL projection — a SECOND projection of the same deliverable. -/
def GoalAll (l : List Bool) : Prop := ∀ x ∈ l, x = true
theorem unified_route {l : List Bool} (h : Deliv l) : GoalAll l := h.toFull

/-- NECESSITY: the unit projection genuinely CANNOT serve the unified consumer — a list whose boundary
    holds but whose interior fails satisfies `unitProj` yet refutes `GoalAll`. So the second projection
    is not redundant; the consumer's unification forced it. (`[true, false]`: head `true` ⇒ `unitProj`,
    but `false` inside ⇒ `¬ GoalAll`.) -/
theorem unit_cannot_serve_unified : unitProj [true, false] ∧ ¬ GoalAll [true, false] :=
  ⟨rfl, by intro h; exact absurd (h false (by simp)) (by decide)⟩

end UnifiedResidualForcesSiblingProjection
