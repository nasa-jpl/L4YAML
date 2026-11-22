/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Parser.ParserWfaScannable
public import L4YAML.Parser.IndexedComposition

@[expose] public section Blanket

/-!
# The `Scannable`-valued parse-side anchor table — indexed twin

`ParserWfaScannable` carries the table-level content: `WellFormedAnchorsS`,
`compose_value_scannable` (the one declaration with new content — it takes no
`AllAliasesResolve` hypothesis), `WFAS_of_push` and `cleaned_scannable_forall`
are all stated on the anchor TABLE, not on a parser state, so the twins share
them outright.  Only the two declarations that touch a state need a twin, and
they are below.
-/

namespace L4YAML.Proofs.Indexed.WfaScannable

open L4YAML
open L4YAML.Grammar
open L4YAML.Algebra.Value
open L4YAML.TokenParser.Indexed
open L4YAML.Proofs.ParserGrammable

variable {input : String}

/-- `addAnchor` preserves `WellFormedAnchorsS` — indexed twin. -/
lemma addAnchor_wfaS (ps : ParseStateIx input) (name : String) (val : YamlValue)
    (h_wfa : WellFormedAnchorsS ps.anchors)
    (h_scan : ∀ inFlow,
      Scannable (((val.stripAnchors.adaptForFlowContext).resolveAliases ps.anchors).stripAnchors)
        inFlow) :
    WellFormedAnchorsS (ps.addAnchor name val).anchors := by
  rw [ParseStateIx.addAnchor_anchors]
  exact WFAS_of_push _ _ h_wfa h_scan

/-- Node finalization preserves `WellFormedAnchorsS` — indexed twin.  As in the
    legacy one, the `AllAliasesResolve` premise its `Grammable` original takes
    is gone: `compose_value_scannable` splits on the lookup instead. -/
lemma applyNodeFinalization_wfaS
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos)
    (h_wfa : WellFormedAnchorsS ps.anchors)
    (h_scannable : Scannable val false) :
    WellFormedAnchorsS (applyNodeFinalization val ps props nodeStartPos).2.anchors := by
  rcases props with ⟨anchor, tag, dup⟩
  cases anchor with
  | none =>
    simp only [applyNodeFinalization]
    split <;> exact h_wfa
  | some name =>
    cases val with
    | scalar s =>
      simp only [applyNodeFinalization]
      split <;> exact addAnchor_wfaS ps name _ h_wfa
        (cleaned_scannable_forall _ ps.anchors h_scannable h_wfa)
    | alias a =>
      simp only [applyNodeFinalization]
      split <;> exact addAnchor_wfaS ps name _ h_wfa
        (cleaned_scannable_forall _ ps.anchors h_scannable h_wfa)
    | sequence style items otag oanchor =>
      cases otag <;> cases oanchor <;> simp only [applyNodeFinalization] <;> split
      all_goals (first
        | exact addAnchor_wfaS ps name _ h_wfa
            (cleaned_scannable_forall _ ps.anchors h_scannable h_wfa)
        | (exact addAnchor_wfaS ps name _ h_wfa
            (cleaned_scannable_forall _ ps.anchors
              (.sequence _ _ _ _ _
                (by cases h_scannable with | sequence _ _ _ _ _ h => exact h))
              h_wfa)))
    | mapping style pairs otag oanchor =>
      cases otag <;> cases oanchor <;> simp only [applyNodeFinalization] <;> split
      all_goals (first
        | exact addAnchor_wfaS ps name _ h_wfa
            (cleaned_scannable_forall _ ps.anchors h_scannable h_wfa)
        | (exact addAnchor_wfaS ps name _ h_wfa
            (cleaned_scannable_forall _ ps.anchors
              (.mapping _ _ _ _ _
                (by cases h_scannable with | mapping _ _ _ _ _ hk _ => exact hk)
                (by cases h_scannable with | mapping _ _ _ _ _ _ hv => exact hv))
              h_wfa)))

end L4YAML.Proofs.Indexed.WfaScannable

end Blanket
