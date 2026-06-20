/-!
# Reflection 471 — the BOUNDARY-INCLUSIVE SIBLING CASCADE: when a BUNDLED multi-structure deliverable
# needs the opener-inclusive convention, EACH structure owes its own sibling — but the COST DECREASES,
# and the boundary token INVERTS which field is hardest (the head goes FREE).

Self-contained (core Lean, no `L4YAML` import) toy continuing Reflection 470.

Context (the real situation).  R470 showed the seq carrier↔recursion co-construction's `h_widthEnc`
deliverable needs the FULL bracket window `[p, j+1)` (opener-INCLUSIVE), and that the landed INTERIOR
producer `flowBodyWindow_descend` (`[k+1, j)`, opener-EXCLUSIVE) cannot be COERCED UP — so it authored
the opener-inclusive sibling `flowBodyWindow_child_bracket`.

But `h_widthEnc` does NOT deliver one structure — it delivers a BUNDLE over the SAME window:
`FlowBodyWindow tokens p hiE ∧ FlowBodyContentDeep tokens p hiE ∧ FlowBodyContent tokens p hiE`.  So the
opener-inclusive convention cascades: EACH of the three owes its own opener-inclusive sibling.  R471 (the
brick `flowBodyContentDeep_child_bracket`) lands the SECOND, and the reading reveals the cascade is
COST-GRADED — the structures are NOT equally expensive:

1. `FlowBodyWindow` (the LOCATING structure) — DEAREST.  Its sibling must search for the matching close
   `j` (`flowBracketBalance_matching_close`) and rebuild the dyck floor / `WellTyped` subrange.  Axioms
   `[propext, Classical.choice, Quot.sound]`.
2. `FlowBodyContentDeep` (a BALANCE-FREE / window-ABSOLUTE structure) — CHEAP.  Its sibling is a PURE
   RESTRICTION: the quantified opener/separator fields narrow their domain `[k, j+1) ⊆ [lo, hi)` by
   `omega`; `j` is handed in, not searched.  Axioms `[propext, Quot.sound]` — it DROPS `Classical.choice`
   the window sibling keeps.  **The axiom set is the cost meter**: a restriction sibling inherits the
   parent's quantified facts by domain-narrowing instead of re-deriving them, so it needs strictly fewer
   axioms than its locating bundle-mate.
3. `FlowBodyContent` (the depth-`0` PROJECTION of `FlowBodyContentDeep`) — FREE.  It follows from #2 via
   the existing `flowBodyContent_of_deep` bridge, whose two named residuals discharge VACUOUSLY against
   the window's interior floor (the only child-origin balance-`0` positions in `[k, j+1)` are the opener
   `k` — `.flowEntry` premise fails — and the close `j` — `k+1 = j+1` takes `bodySucc`'s left disjunct).

**The boundary token INVERTS the head field.**  The sharpest new point.  Every one of these structures
has a `headContentStart` field.  For the INTERIOR sibling (`flowBodyContentDeep_descend`) the head is the
HARDEST field: the interior head `tokens[k+1]` sits a nesting level down, so it must be READ OFF THE
PARENT's all-depth opener-content fact at `k`.  For the OPENER-INCLUSIVE sibling the head IS the boundary
token — the opener `tokens[k]` — which is content-start BY ITS OWN DELTA (`flowBracketDelta = 1` ⟹
`.flowSequenceStart`/`.flowMappingStart`, both `isFlowContentStart`).  So the field that was the
producer's hardest becomes FREE, needing no parent fact at all.  The boundary that complicates the
CONSUMER (extra tokens to re-scan) SIMPLIFIES the PRODUCER's head — the opposite-sign storage asymmetry
of `near-leaf-mirror-sheds-machinery`, now applied to a FIELD, not a guard.

This toy reproduces the STRUCTURE of #2 + the head inversion:

* `tok xs i` — the `tokens[i]!` analog (a single global token list; `1` opener, `-1` closer, `0`
  scalar); `isContentStart t := 0 ≤ t` (opener and scalar, NOT closer); `delta = tok` (each token IS its
  bracket delta).
* `contentStart_of_opener` — the boundary-token head bridge: an opener `= 1` is content-start FOR FREE
  (the `flowBracketDelta_eq_one_iff` + `isFlowContentStart` chain, in the toy a one-liner).
* `DeepGuard xs lo hi` — the `FlowBodyContentDeep` analog: a `headContentStart` field + a window-ABSOLUTE,
  balance-FREE `openerCS` quantifier (domain `lo ≤ k → k+1 < hi` only).
* `deepGuard_descend` — the INTERIOR sibling `[k+1, j)`: its head READS OFF THE PARENT (`h.openerCS k`).
* `deepGuard_child_bracket` — the OPENER-INCLUSIVE sibling `[k, j+1)`: its head is FREE from the boundary
  token (`contentStart_of_opener h_open`), and it SHEDS the descend sibling's `k+1 < j`
  interior-non-emptiness guard (only `j+1 ≤ hi` remains).  The `openerCS` restriction is IDENTICAL to
  the descend sibling's — same domain-narrowing by `omega`.
* The concrete contrast: the interior head `tok [1,0,-1] 1 = 0` is a SCALAR, so `contentStart_of_opener`
  does NOT apply to it (it is `≠ 1`) — the descend sibling genuinely needs the parent; the boundary head
  `tok [1,0,-1] 0 = 1` is always the opener, always free.
-/

namespace BoundaryInclusiveSiblingCascade

set_option autoImplicit false

/-- A minimal bracket-delta token: `1` opener `[`, `-1` closer `]`, `0` content scalar.  Each token IS
    its own bracket delta (the `flowBracketDelta` analog). -/
abbrev Tok := Int

/-- `tokens[i]!` analog over a single global list, defaulting out-of-range to a scalar. -/
def tok (xs : List Tok) (i : Nat) : Tok := xs.getD i 0

/-- `isFlowContentStart` analog: an opener (`1`) or a scalar (`0`) is content-start; a closer (`-1`) is
    NOT. -/
def isContentStart (t : Tok) : Prop := 0 ≤ t

/-- **THE BOUNDARY-TOKEN HEAD BRIDGE** (the `flowBracketDelta_eq_one_iff` + `isFlowContentStart` chain):
    an opener is content-start FOR FREE — no parent fact, just its own delta.  This is why the
    opener-inclusive sibling's head field is free. -/
theorem contentStart_of_opener {t : Tok} (h : t = 1) : isContentStart t := by
  simp only [isContentStart, h]; decide

/-- **THE DEEP-CONTENT GUARD** (the `FlowBodyContentDeep` analog) on a window `[lo, hi)`: a head field
    plus a window-ABSOLUTE, balance-FREE quantifier (domain `lo ≤ k → k+1 < hi` only; body keyed solely
    on `tok`, never an origin or a balance).  Balance-freedom is what makes BOTH recursion edges — and
    the opener-inclusive sibling — pure RESTRICTIONS. -/
structure DeepGuard (xs : List Tok) (lo hi : Nat) : Prop where
  headCS : isContentStart (tok xs lo)
  openerCS : ∀ k, lo ≤ k → k + 1 < hi → tok xs k = 1 → isContentStart (tok xs (k + 1))

/-- **THE INTERIOR SIBLING** `[k+1, j)` (the `flowBodyContentDeep_descend` analog, opener-EXCLUSIVE).
    Its head `tok xs (k+1)` sits one level in, so it is READ OFF THE PARENT's `openerCS` at `k` — the
    head is the HARDEST field.  The `openerCS` body is the parent's, restricted by domain narrowing.
    Guarded on interior non-emptiness `k+1 < j`. -/
theorem deepGuard_descend (xs : List Tok) (lo k j hi : Nat)
    (h : DeepGuard xs lo hi) (h_lo_k : lo ≤ k) (h_open : tok xs k = 1)
    (h_kj : k + 1 < j) (h_j_hi : j ≤ hi) :
    DeepGuard xs (k + 1) j where
  headCS := h.openerCS k h_lo_k (by omega) h_open          -- READS the parent's opener fact
  openerCS := fun k' hk1 hk2 hop => h.openerCS k' (by omega) (by omega) hop

/-- **THE OPENER-INCLUSIVE SIBLING** `[k, j+1)` (the `flowBodyContentDeep_child_bracket` brick,
    opener-INCLUSIVE — the second sibling of the bundle cascade).  Two changes from the interior sibling:

    1. **The head goes FREE.**  The window head IS the opener `tok xs k`, content-start by its own delta
       (`contentStart_of_opener h_open`) — NO parent fact consulted.  The interior sibling's HARDEST
       field is this sibling's EASIEST.
    2. **The guard is SHED.**  `[k, j+1)` is never empty and the head no longer reads an interior
       position, so the `k+1 < j` interior-non-emptiness guard is gone — only `j+1 ≤ hi` remains.

    The `openerCS` body is UNCHANGED — the identical parent restriction by domain narrowing.  In the real
    development this drops `Classical.choice` (axioms `[propext, Quot.sound]`) that the LOCATING window
    sibling keeps — the axiom set is the cost meter. -/
theorem deepGuard_child_bracket (xs : List Tok) (lo k j hi : Nat)
    (h : DeepGuard xs lo hi) (h_lo_k : lo ≤ k) (h_open : tok xs k = 1)
    (h_j_hi : j + 1 ≤ hi) :
    DeepGuard xs k (j + 1) where
  headCS := contentStart_of_opener h_open                  -- FREE from the boundary token, no parent
  openerCS := fun k' hk1 hk2 hop => h.openerCS k' (by omega) (by omega) hop

/-- CONCRETE — the boundary head is ALWAYS the opener `1`, content-start for free. -/
example : tok [1, 0, -1] 0 = 1 := rfl

/-- CONCRETE — the INTERIOR head can be a SCALAR `0`, NOT an opener: `contentStart_of_opener` does NOT
    apply to it (it is `≠ 1`), so the descend sibling genuinely needs the parent.  This is the head
    inversion in one line. -/
example : tok [1, 0, -1] 1 = 0 := rfl

/-- CONCRETE — and a scalar head IS content-start, but only via the guard (`0 ≤ 0`), never via the
    opener bridge. -/
example : isContentStart (tok [1, 0, -1] 1) := by unfold isContentStart tok; decide

end BoundaryInclusiveSiblingCascade
