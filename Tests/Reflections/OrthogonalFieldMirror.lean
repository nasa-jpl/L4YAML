/-!
# Reflection 429 — a new orthogonal per-window field costs only its discriminator

Self-contained (core Lean, no `L4YAML` import) toy of the R429 step.

Context.  A per-window CONSUMER (`FlowBodyContentDeepSeq`) needs several adjacency fields, each of the
shape "every position carrying a GATE token whose successor avoids an EXCLUDED token is followed by
content".  The opener field gates on `.flowSequenceStart` excluding `.flowSequenceEnd` (R411); the new
separator field gates on `.flowEntry` excluding `.key` (R429).  Each is sourced by RESTRICTING a GLOBAL
predicate of that shape to the window `[lo, hi)`.

The finding.  Because the global predicate is AXIS-UNIFORM (same shape for both emit sources, seq and
map) and WINDOW-ABSOLUTE (the gate reads only `toks[k]`/`toks[k+1]`, never the window origin `lo`/`hi`),
the restriction is a ONE-`omega`-bound subset narrowing, and the per-window provider for a NEW orthogonal
field is a TWO-LINE copy-mirror of the sibling field's: the ENTIRE delta is the discriminator
`(gate, excluded)`.  All the real work front-loads into the GLOBAL producer — for the separator that was
R428's contradiction-branch boundary discharge (`tokens[size-3] ≠ .flowEntry`) plus a separate non-mirror
map producer; by the time you reach the window wrapper there is nothing left to prove.

The diagnostic (the "tell").  If the per-window wrapper is MORE than a trivial restriction — if narrowing
`[lo, hi) ⊆ [0, size)` requires re-basing balances or re-locating a boundary — then the global predicate
is NOT window-absolute, and the fix is to RE-DESIGN the predicate (drop the origin-relative keying), not
to thread the wrapper.

The toy below makes the discriminator explicit as a parameter `(gate, excl)`, gives ONE restriction
lemma, then instantiates the two fields as pure applications differing ONLY in that pair — and exhibits
the NEGATIVE case (an origin-relative predicate whose index drifts under narrowing, so its restriction is
not a subset step).
-/

namespace Tests.Reflections.OrthogonalFieldMirror

set_option autoImplicit false

/-- Toy "content-start" successor test (mirror of `isFlowContentStart`). -/
def isContent (x : Nat) : Prop := x = 7

/-! ## The axis-uniform, window-absolute global predicate, parameterized by its discriminator. -/

/-- **The global adjacency predicate, parameterized by its discriminator `(gate, excl)`.**  `gate` is the
    token a position must carry to fire; `excl` is the successor that switches the body off.  The body
    reads ONLY `toks[k]!`/`toks[k+1]!` — never any window origin — which is exactly what makes the window
    restriction a pure subset narrowing.  (`GlobalFlowSeqOpenerAdj` and `GlobalFlowSeqSepAdj` are the two
    real instances; the real code keeps them as separate-but-mirror `def`s rather than one parameterized
    `def`, but the shape — and the cost of a new instance — is exactly this.) -/
def GlobalAdj (gate excl : Nat) (toks : List Nat) : Prop :=
  ∀ k, k + 1 < toks.length → toks[k]! = gate → toks[k+1]! ≠ excl → isContent toks[k+1]!

/-- **The restriction is ONE bound step** — the global predicate at any window `[lo, hi)` with
    `hi ≤ length`.  Mirror of the real `flowSeqSepAdj_window_of_global` /
    `flowSeqOpenerAdj_window_of_global`: `lo`/`hi` enter ONLY via the domain bound, discharged by a single
    `omega`; the discriminator passes through untouched. -/
theorem adj_window_of_global (gate excl : Nat) (toks : List Nat) (lo hi : Nat)
    (h : GlobalAdj gate excl toks) (h_hi : hi ≤ toks.length) :
    ∀ k, lo ≤ k → k + 1 < hi → toks[k]! = gate → toks[k+1]! ≠ excl → isContent toks[k+1]! := by
  intro k _ hk hg hx
  exact h k (by omega) hg hx

/-! ## The two orthogonal fields — same restriction lemma, only the discriminator swapped. -/

/-- The opener gates on `OPEN` excluding `CLOSE`; the separator gates on `SEP` excluding `KEY`. -/
def OPEN : Nat := 1
def CLOSE : Nat := 2
def SEP : Nat := 3
def KEY : Nat := 4

/-- **Opener window field** — toy of R411's `seqWindowOpenerAdj_of_emit`. -/
theorem windowOpenerAdj (toks : List Nat) (lo hi : Nat)
    (h : GlobalAdj OPEN CLOSE toks) (h_hi : hi ≤ toks.length) :
    ∀ k, lo ≤ k → k + 1 < hi → toks[k]! = OPEN → toks[k+1]! ≠ CLOSE → isContent toks[k+1]! :=
  adj_window_of_global OPEN CLOSE toks lo hi h h_hi

/-- **Separator window field** — toy of R429's `seqWindowSepAdj_of_emit`.  The SAME restriction lemma,
    only the discriminator `(gate, excl)` swapped `(OPEN, CLOSE) → (SEP, KEY)`.  THIS is the whole cost of
    a new orthogonal field: the difficulty already front-loaded into the global producer upstream. -/
theorem windowSepAdj (toks : List Nat) (lo hi : Nat)
    (h : GlobalAdj SEP KEY toks) (h_hi : hi ≤ toks.length) :
    ∀ k, lo ≤ k → k + 1 < hi → toks[k]! = SEP → toks[k+1]! ≠ KEY → isContent toks[k+1]! :=
  adj_window_of_global SEP KEY toks lo hi h h_hi

/-! ## The diagnostic — a NON-window-absolute predicate does not restrict by a single bound. -/

/-- A predicate whose body RE-BASES on the window origin `lo` (reads `toks[k - lo]!`).  This is what you
    must AVOID.  Restricting a global (`lo = 0`) instance to a sub-window `[lo', hi)` with `lo' > 0` would
    need `toks[k - lo']!` — a DIFFERENT position than the global's `toks[k]!` — so no single `omega` bound
    discharges it; the field would have to be RE-DERIVED, not restricted. -/
def GlobalAdjRebased (toks : List Nat) (lo : Nat) : Prop :=
  ∀ k, lo ≤ k → k + 1 < toks.length → isContent toks[k - lo]!

-- **NEGATIVE / the "tell"** — the re-based index drifts under narrowing.  At absolute position `k = 5`
-- the global (`lo = 0`) reads index `5`, but a sub-window opened at `lo' = 2` reads index `3`.  Different
-- facts ⇒ the restriction is NOT a subset narrowing.  When the wrapper stops being a two-line mirror,
-- THIS is the mis-design to fix in the predicate — do not thread a stronger wrapper.
#guard (5 - 0) == 5
#guard (5 - 2) == 3
#guard (5 - 0) != (5 - 2)

end Tests.Reflections.OrthogonalFieldMirror
