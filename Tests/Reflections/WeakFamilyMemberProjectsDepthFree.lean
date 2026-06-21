/-!
# Reflection 479 — the WEAK member of a child-window structure family PROJECTS its strong sibling
# through the family's existing `strong→weak` projector, residuals VACUOUS against the window's own
# interior floor — and is DEPTH-AGNOSTIC because the floor is keyed on the CHILD origin.

Self-contained (core Lean, no `L4YAML` import) toy recording the brick R479 landed:
`flowBodyContent_child_bracket`
(`L4YAML/Proofs/Output/EmitterScannability/NonemptyStructure.lean`), the (α.2) content half of the seq
`enclosingLocate` residual — the THIRD and final opener-inclusive child-bracket sibling, completing the
trio `{flowBodyWindow_child_bracket, flowBodyContentDeep_child_bracket, flowBodyContent_child_bracket}`.

**The setup.**  A child bracket `[`/`{` opens at `k` inside the body window `[lo, hi)`, matching close at
`j`.  The seq carrier↔recursion co-construction owes the depth-`0` `FlowBodyContent tokens k (j+1)` over
the FULL child window.  Two siblings already exist: `flowBodyWindow_child_bracket` (the bracket facts,
LOCATES `j` via an outer-origin `flowBracketBalance_matching_close` scan that NEEDS the depth-`0`
discriminator `balance lo k = 0`), and `flowBodyContentDeep_child_bracket` (the recursion-stable,
all-depth, balance-FREE deep guard `FlowBodyContentDeep tokens k (j+1)`).

**The brick — don't author a fresh producer; PROJECT the strong sibling.**  `FlowBodyContent` is a
PROJECTION of `FlowBodyContentDeep` (the family already ships the projector `flowBodyContent_of_deep`).
So the weak member is: pipe the deep sibling through that projector and discharge its two named residuals
(`bodySucc`, `noTrailingSep`) VACUOUSLY against the bracket's strict interior floor — the only
child-origin balance-`0` prefix ends in `[k, j+1)` are the two ENDPOINTS (the opener fails the separator
premise / sits at balance `≥ 1`; the close takes the trivial disjunct, and contradicts the `.flowEntry`
premise via its own close type).  This realizes the projection `flowBodyContentDeep_child_bracket`'s doc
only PROMISED.

**DEPTH-AGNOSTIC.**  The strict floor is keyed on the CHILD origin `k` (`balance k i ≥ 1`), NOT an outer
origin `lo`.  So the weak member needs no `balance lo k = 0` discriminator — the depth caveat lives
ENTIRELY in the LOCATING sibling (`flowBodyWindow_child_bracket`'s scan), never in the content
projection.  The family splits into a depth-NEEDING locator and a depth-FREE projector.

This toy abstracts the four reusable facts away from the bracket-balance specifics.
-/

namespace WeakFamilyMemberProjectsDepthFree

set_option autoImplicit false

/-- The interior FLOOR, keyed on the CHILD origin `k` (the depth-agnostic input — never an outer origin):
    every prefix end in the strict interior `(k, j]` sits at balance `≥ 1`. -/
def Floor (b : Nat → Int) (k j : Nat) : Prop := ∀ i, k + 1 ≤ i → i ≤ j → b i ≥ 1

/-- The WEAK member's two fields — a stand-in for `FlowBodyContent`'s `bodySucc` / `noTrailingSep`:
    every balance-`0` prefix end is the close, and the close is never a separator. -/
structure Content (b : Nat → Int) (isSep : Nat → Prop) (k j : Nat) : Prop where
  bodySucc : ∀ k', k ≤ k' → k' ≤ j → b (k' + 1) = 0 → k' = j
  noTrailingSep : ∀ k', k ≤ k' → k' = j → ¬ isSep k'

/-- **The PROJECTOR** — the family's existing `strong→weak` lemma (models `flowBodyContent_of_deep`):
    builds the weak member from the strong sibling `deep` PLUS two named residuals.  The residuals carry
    the whole content; `deep` supplies the head fact this toy elides. -/
theorem content_of_deep (b : Nat → Int) (isSep : Nat → Prop) (k j : Nat)
    (_deep : True)
    (h_bodySucc : ∀ k', k ≤ k' → k' ≤ j → b (k' + 1) = 0 → k' = j)
    (h_noTrailingSep : ∀ k', k ≤ k' → k' = j → ¬ isSep k') :
    Content b isSep k j :=
  ⟨h_bodySucc, h_noTrailingSep⟩

/-- **The WEAK member projects via the projector, both residuals VACUOUS against the floor.**  No fresh
    producer: pipe the strong sibling `deep` through `content_of_deep` and discharge its residuals from
    the interior floor (`bodySucc`: interior is `≥ 1`, so the ONLY balance-`0` prefix end is the close)
    and the close type (`noTrailingSep`: the close `j` is not a separator).  DEPTH-AGNOSTIC: `Floor` is
    keyed on `k`, so no `balance lo k = 0` discriminator appears.  Mirrors
    `flowBodyContent_child_bracket`. -/
theorem content_child_bracket (b : Nat → Int) (isSep : Nat → Prop) (k j : Nat)
    (deep : True)
    (h_floor : Floor b k j)
    (h_close : b (j + 1) = 0)
    (h_close_notSep : ¬ isSep j) :
    Content b isSep k j := by
  refine content_of_deep b isSep k j deep ?_ ?_
  · -- bodySucc: a balance-`0` prefix end forces `k' = j` (interior prefixes are `≥ 1`).
    intro k' hk1 hk2 hbal
    rcases Nat.lt_or_ge k' j with h | h
    · have hf := h_floor (k' + 1) (by omega) (by omega)
      omega
    · omega
  · -- noTrailingSep: the close `j` is not a separator.
    intro k' hk1 hk2 hsep
    subst hk2
    exact h_close_notSep hsep

/-- **The floor is LOAD-BEARING** (the vacuity is genuine, not cosmetic — cf. R478's `erasure_is_genuine`).
    Drop it and an INTERIOR balance-`0` prefix end breaks `bodySucc`: here `b` returns to `0` at the
    interior `i = 2` (not the close `4`), so `bodySucc` at `k' = 1` would demand `1 = 3`. -/
theorem floor_is_load_bearing :
    ¬ Content (fun i => if i = 2 then (0 : Int) else 1) (fun _ => False) 0 3 := by
  intro h
  have hbs := h.bodySucc 1 (by omega) (by omega) (by simp)
  omega

/-- CONCRETE, non-vacuous — `content_child_bracket` runs end-to-end on a real `b`/`isSep`/window
    (`b i = 1` on the interior `[1,2]`, returning to `0` only at the close `3`; `isSep i ↔ i = 5`). -/
example : Content (fun i => if i = 3 then (0 : Int) else 1) (fun i => i = 5) 0 2 :=
  content_child_bracket _ _ 0 2 trivial
    (by
      intro i h1 h2
      have hne : i ≠ 3 := by omega
      simp [hne])
    (by simp)
    (by decide)

end WeakFamilyMemberProjectsDepthFree
