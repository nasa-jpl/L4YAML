/-!
# Reflection 491 — the TERMINAL ASSEMBLE of a guard re-thread is GREP-BOUNDED: its cost is exactly the
guard's read sites (each swapped to a pre-landed child twin), while the locate/floor SKELETON is
guard-agnostic and copies verbatim.

Self-contained (core Lean, no `L4YAML` import) toy recording the structure that step γ′ surfaced while
landing `seqEnclosingLocate_of_seqOpener_nested_seq` — the `_seq` re-thread of the R485 `enclosingLocate`
assemble, keyed on the root-TRUE weaker guard `FlowBodyContentDeepSeq` instead of the root-FALSE
`FlowBodyContentDeep`.

**The setup.**  The `_seq` re-thread ([[RethreadStaysInWeakerTwinFamily]], R489; seeded per
[[RootSeedNeedsRootTrueGuard]], R488) replaces the strong content guard with its root-true weaker twin
throughout the seq carrier chain.  R489 landed the `_seq` DEEP child producer; R490 landed the `_seq`
CONTENT child producer.  This turn assembles the parent — R485's whole locate/floor/close proof, now
keyed on the weaker guard.

**The find — the assemble is the CHEAPEST brick of the re-thread, and it is mechanical.**  A guard
hypothesis `h_deep` funnels to a SMALL, enumerable set of read sites: the LEAF constructors that build the
deliverable's guard-typed conjuncts.  EVERYTHING ELSE in the assemble — locating the matching close, the
child-keyed floor, the `close < hi` re-derivation, the guard-NEUTRAL window constructor — reads OTHER
hypotheses (the window facts, the locator) and is GUARD-AGNOSTIC.  So:

  cost(re-scope an assembler) = (grep `h_deep` in the body) read sites,
    each a SWAP to the corresponding pre-landed child twin,
  + (swap the guard TYPE in the signature + conclusion).

The bulk skeleton copies VERBATIM.  In the real proof `h_deep` funnelled to EXACTLY two sites — site 1
(swap `flowBodyContentDeep_child_bracket ↦ flowBodyContentDeepSeq_child_bracket`, R489) and site 2 (swap
`flowBodyContent_child_bracket ↦ flowBodyContent_child_bracket_seq`, R490, which also DROPS the close
argument); the ~50-line locate/floor skeleton was byte-identical to R485.

**The transferable rule.**  When a guard re-thread reaches its terminal ASSEMBLE, do not re-prove it: GREP
the guard hypothesis in the strong parent's body.  Its read sites are the only edits — each swaps to the
child twin you landed in a PRIOR turn, and the guard type swaps in the signature/conclusion.  This is WHY
the child twins are built first, one per turn: they convert the parent assemble from a proof obligation
into a mechanical, grep-bounded copy.  The assemble is the last brick AND the cheapest.

This is the structural-GUARD analog of [[DepthHypCostIsItsEqualityReads]] (a scalar-baseline hypothesis,
where each read either swaps to a depth-general twin or re-derives one equality) — here the hypothesis is a
whole inductive GUARD and every read swaps uniformly to its `_seq` twin (no equality re-derivation, because
a guard re-scope changes WHICH producer you call, not a numeric baseline).

This toy models a window `n`, two additive-parallel guard families (`Strong` interior-only/root-false,
`Weak` root-true), a guard-AGNOSTIC `skeleton` (built from the window fact alone — byte-identical in both
assemblers), the two pre-landed child twins per leaf (`childGuard_strong`/`childGuard_weak`,
`content_strong`/`content_weak`), and the two assemblers (`assemble_strong` = R485, `assemble_seq` = R491)
that differ in EXACTLY the two guard-reading calls + the guard type — the skeleton call is verbatim.
-/

namespace RescopeAssembleCostIsGuardReadSites

set_option autoImplicit false

/-! ### Two additive-parallel guard families: `Strong` interior-only (root-false), `Weak` root-true. -/

/-- Toy `FlowBodyContentDeep` — the strong content guard (interior-only; in the real chain it is provably
    FALSE at the root). -/
abbrev Strong (n : Nat) : Prop := 2 ≤ n

/-- Toy `FlowBodyContentDeepSeq` — the root-TRUE weaker twin the re-thread is keyed on. -/
abbrev Weak (n : Nat) : Prop := 1 ≤ n

/-! ### The deliverable conjuncts produced at the LEAF constructors — the guard funnels here, ONLY here. -/

/-- Toy `FlowBodyContentDeep tokens p hiE` (the child deep guard, strong family). -/
abbrev ChildGuardStrong (n : Nat) : Prop := 2 ≤ n
/-- Toy `FlowBodyContentDeepSeq tokens p hiE` (the child deep guard, weak family). -/
abbrev ChildGuardWeak (n : Nat) : Prop := 1 ≤ n
/-- Toy `FlowBodyContent tokens p hiE` (the depth-`0` content, family-NEUTRAL — same on both sides). -/
abbrev Content (n : Nat) : Prop := 0 < n

/-! ### The guard-AGNOSTIC skeleton — reads the window fact + locator, NEVER the content guard. -/

/-- The window fact the assembler is handed (toy `FlowBodyWindow`). -/
abbrev WindowFacts (n : Nat) : Prop := 1 ≤ n

/-- The positional facts the locate/floor skeleton derives: a located typed opener, a child-bracket floor
    (whose range reaches the close), and a close marker.  NONE reads the content guard — all come from the
    window fact + the locator, so the skeleton CALL is byte-identical in both assemblers. -/
structure Skeleton (n : Nat) : Prop where
  opener : 0 < n   -- the located typed opener (R485 already establishes it for the close locator)
  floor : 1 ≤ n    -- the child-bracket floor (reaches the close position)
  close : 0 < n    -- the close marker — only the STRONG content path consumes it (R490 sheds it)

/-- The skeleton is built from the window fact ALONE — GUARD-AGNOSTIC. This is the ~50-line
    locate/floor/close block that copies verbatim between the strong assemble and its `_seq` twin. -/
theorem skeleton (n : Nat) (hw : WindowFacts n) : Skeleton n := ⟨hw, hw, hw⟩

/-! ### The pre-landed child twins — one per leaf, built in PRIOR turns (R489 site 1, R490 site 2). -/

/-- Site 1 STRONG (`flowBodyContentDeep_child_bracket`): needs the strong guard. -/
theorem childGuard_strong (n : Nat) (h_deep : Strong n) : ChildGuardStrong n := h_deep

/-- Site 1 `_seq` (`flowBodyContentDeepSeq_child_bracket`, R489): needs the weak guard + the located TYPED
    opener (strictly more information than the strong site's delta, and freely in scope).  (The real
    producer consumes `h_open` for the head field; the toy's defeq discharges from the guard alone, so it
    is `_`-marked here.) -/
theorem childGuard_weak (n : Nat) (h_deep : Weak n) (_h_open : 0 < n) : ChildGuardWeak n := h_deep

/-- Site 2 STRONG (`flowBodyContent_child_bracket`): needs the strong guard + a CLOSE marker (boundary).
    (The real producer consumes the guard; the toy's defeq discharges from the close marker, so it is
    `_`-marked here.) -/
theorem content_strong (n : Nat) (_h_deep : Strong n) (h_close : 0 < n) : Content n := h_close

/-- Site 2 `_seq` (`flowBodyContent_child_bracket_seq`, R490): needs the weak guard + the typed opener +
    the floor; DROPS the close marker — the unified residual routes through the floor instead
    ([[UnifiedResidualRoutesThroughOneInvariant]]).  (The real producer consumes the guard and floor; the
    toy's defeq discharges from the opener alone, so they are `_`-marked here.) -/
theorem content_weak (n : Nat) (_h_deep : Weak n) (h_open : 0 < n) (_h_floor : 1 ≤ n) : Content n := h_open

/-! ### The two assemblers — the re-scope touches EXACTLY the guard-reading sites. -/

/-- The STRONG assemble (toy `seqEnclosingLocate_of_seqOpener_nested`, R485).  The guard `h_deep : Strong n`
    funnels to EXACTLY two sites (grep `h_deep`): site 1 + site 2.  The skeleton call is guard-agnostic. -/
theorem assemble_strong (n : Nat) (hw : WindowFacts n) (h_deep : Strong n) :
    Skeleton n ∧ ChildGuardStrong n ∧ Content n := by
  have sk := skeleton n hw                              -- guard-AGNOSTIC skeleton
  exact ⟨sk, childGuard_strong n h_deep,                -- site 1: reads h_deep
            content_strong n h_deep sk.close⟩           -- site 2: reads h_deep + the close marker

/-- **THE BRICK (toy `seqEnclosingLocate_of_seqOpener_nested_seq`, R491).**  The `_seq` re-scope: a
    near-verbatim copy of `assemble_strong` with EXACTLY the two guard-reading calls swapped to their
    pre-landed twins, plus the guard type swapped in the signature/conclusion.  The skeleton call is
    BYTE-IDENTICAL — that is the grep-bounded cost realized: 2 swaps + 1 type swap, no skeleton re-proof. -/
theorem assemble_seq (n : Nat) (hw : WindowFacts n) (h_deep : Weak n) :
    Skeleton n ∧ ChildGuardWeak n ∧ Content n := by
  have sk := skeleton n hw                              -- IDENTICAL — guard-agnostic, copied verbatim
  exact ⟨sk, childGuard_weak n h_deep sk.opener,        -- site 1: swap to the R489 `_seq` twin (typed opener)
            content_weak n h_deep sk.opener sk.floor⟩   -- site 2: swap to the R490 `_seq` twin, DROP sk.close

/-- The shedding made explicit: the `_seq` assemble's content leaf closes WITHOUT consuming the close
    marker `sk.close` — site 2's twin routes through the opener + floor the skeleton already holds. -/
example (n : Nat) (hw : WindowFacts n) (h_deep : Weak n) : Content n :=
  let sk := skeleton n hw
  content_weak n h_deep sk.opener sk.floor

end RescopeAssembleCostIsGuardReadSites
