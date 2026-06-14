/-!
# Reflection 430 — an edge-adjacent read comes from the global universal, not the restricted field

Self-contained (core Lean, no `L4YAML` import) toy of the R430 step.

Context.  An assembler builds a window carrier `FlowBodyContentDeepSeq tokens lo hi` from three fields:
two INTERIOR universals (`openerContentStart`, `feContentStart`) and one position-keyed HEAD read
(`headContentStart : isFlowContentStart tokens[lo]`).  The two interior fields are window-RESTRICTED
universals, cheap to source (R411 / R429 window providers).  The head is the subtle one: it reads the
token AT the window's lower edge `lo`, established by the opener that sits one position BEFORE it, at
`lo - 1`.

The finding.  Source the head from the UNBOUNDED GLOBAL universal at `k = lo - 1`, NOT from the
window-RESTRICTED field.  The restricted field carries a lower bound `lo₀ ≤ k`, and the index the head
needs is `lo - 1` — which, when `lo` IS the field's lower bound, is `lo₀ - 1 < lo₀`, OUT of the field's
domain.  So a window-bounded source forces a degenerate boundary special-case (R391's
`flowBodyContentDeep_window_of_root` had to fall back to a root-head fact at `lo = 2`).  The GLOBAL
universal quantifies from `k = 0`, so `lo - 1` is always in domain and the head recovery is UNIFORM — one
application, no boundary case.

Reusable rule: when a consumer needs a fact at the window EDGE (`lo`, established at `lo - 1`), restricting
a universal to the window THROWS AWAY exactly the `lo - 1` index you need — read it off the global instead.
The restriction is the right move for INTERIOR fields (cheap subset narrowing); it is the WRONG move for an
edge-adjacent read.

The toy below: a global adjacency `GlobalAdj` (`P k → Q (k+1)`, here `toks[k]! = 1 → isQ toks[k+1]!`) and
its window restriction `windowAdj` with lower bound `base`.  `head_from_global` recovers `Q lo` for ANY
`lo ≥ 1`; `head_from_restricted` recovers it only OFF-boundary (`lo ≥ base + 1`), and a `#guard` exhibits
the boundary it misses (`lo = base` ⇒ the needed index `lo - 1 = base - 1` is below the field's domain).
-/

namespace Tests.Reflections.EdgeAdjacentReadFromGlobal

set_option autoImplicit false

/-- Toy "content-start" test (mirror of `isFlowContentStart`). -/
def isQ (x : Nat) : Prop := x = 7

/-- **The UNBOUNDED global adjacency** — every position carrying the opener marker `1` is followed by
    content.  Quantifies over all `k` from `0` (mirror of `GlobalFlowSeqOpenerAdj`, whose domain is the
    whole `tokens.size`). -/
def GlobalAdj (toks : List Nat) : Prop :=
  ∀ k, k + 1 < toks.length → toks[k]! = 1 → isQ toks[k+1]!

/-- **The window restriction** — the same body, narrowed to `[lo₀, hi)` (mirror of the
    `FlowBodyContentDeepSeq.openerContentStart` field, lower bound `lo₀`). -/
def windowAdj (toks : List Nat) (lo₀ hi : Nat) : Prop :=
  ∀ k, lo₀ ≤ k → k + 1 < hi → toks[k]! = 1 → isQ toks[k+1]!

/-! ## The head recovery — uniform from the global, boundary-broken from the restriction. -/

/-- **Head from the GLOBAL universal — UNIFORM for every `lo ≥ 1`.**  The window's head `toks[lo]` is the
    successor of the opener at `lo - 1`; the global universal has no lower bound, so `k = lo - 1` is always
    in domain.  No boundary special-case.  Toy of `flowBodyContentDeepSeq_of_window_producers`'s
    `headContentStart` (sourced from `seqGlobalFlowSeqOpenerAdj_of_emit` at `k = lo - 1`). -/
theorem head_from_global (toks : List Nat) (lo hi : Nat)
    (h_glob : GlobalAdj toks)
    (h_lo : 1 ≤ lo) (h_lo_hi : lo < hi) (h_hi : hi ≤ toks.length)
    (h_open : toks[lo - 1]! = 1) :
    isQ toks[lo]! := by
  have hlo1 : lo - 1 + 1 = lo := Nat.sub_add_cancel h_lo
  have h := h_glob (lo - 1) (by omega) h_open
  rwa [hlo1] at h

/-- **Head from the RESTRICTED field — only OFF-boundary (`lo ≥ base + 1`).**  The field's lower bound
    `base` admits `k = lo - 1` only when `base ≤ lo - 1`, i.e. `lo ≥ base + 1`.  At the boundary `lo = base`
    this lemma is INAPPLICABLE — the head must be sourced elsewhere (R391's degenerate `lo = 2` root-head
    fallback).  This is the cost the global route erases. -/
theorem head_from_restricted (toks : List Nat) (base lo hi : Nat)
    (h_win : windowAdj toks base hi)
    (h_lo : base + 1 ≤ lo) (h_lo_hi : lo < hi)
    (h_open : toks[lo - 1]! = 1) :
    isQ toks[lo]! := by
  have hlo1 : lo - 1 + 1 = lo := by omega
  have h := h_win (lo - 1) (by omega) (by omega) h_open
  rwa [hlo1] at h

-- **The boundary the restricted route MISSES** — at `lo = base`, the index the head needs is
-- `lo - 1 = base - 1`, strictly BELOW the field's domain `base ≤ k`.  THIS is the degenerate special-case
-- a window-bounded source forces and the unbounded global source erases.
#guard decide ((2 - 1 : Nat) < 2)      -- 1 < 2 : at lo = base = 2 the head index is below domain `base ≤ k`
#guard (5 - 1 + 1 == 5)                -- the global index lo-1 reaches lo (lo = 5)

end Tests.Reflections.EdgeAdjacentReadFromGlobal
