/-!
# Reflection 484 — a base-depth hypothesis costs exactly its EQUALITY reads to drop.

Self-contained (core Lean, no `L4YAML` import) toy recording how R484 generalized the seq
close-within locator (`seqClose_of_located_and_enclosing_within` →
`…_within_nested` in `Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`) off its
base-depth hypothesis `h_p_depth : flowBracketBalance tokens lo p = 0` — and how to SCOPE that cost
*before* editing.

**The move.**  R483 already landed the depth-general *primitive*
(`flowBracketBalance_matching_close_seq_nested`, the typed locator that frames over the enclosing
opener's base stack — [[ref-nested-typed-locator-is-a-frame]]).  R484 is the CONSUME side: re-prove
the close-within locator without `h_p_depth`.  The proof body turned out byte-identical except the
single matching-close call swapped `…_seq` → `…_seq_nested` (dropping the `h_p_depth` argument).

**Why it was a one-line swap — and how to know in advance.**  Grep where the base-depth hypothesis
is actually *read*.  Two kinds of read, two different costs:

* A **floor read** — a fact derived from the Dyck floor `balance … ≥ 0` (monotone, frame-stable).
  These never touch `h_p_depth`; they read the *enclosing* floor `≥ 0`, which holds at every depth.
  In the close-within locator EVERY downstream fact (`a ≤ j`, `balance a j = 0`, `b ≤ j`, and the
  upper containment `j ≤ hi` via `seqLocatedClose_within_body`) is a floor read.  So `h_p_depth`
  funnelled to exactly ONE consume site: the locator call.  Cost to drop it there = a pure swap.

* An **equality read** — an `rw [h_depth]` that substitutes the pinned baseline `= 0`.  This is
  depth-BOUND: at depth ≥ 1 the baseline is `d := balance lo p ≥ 0`, not `0`, so the rewrite is gone
  and the downstream `omega` must re-derive from `≥ 0` instead.  Each equality read is one
  re-derivation.  The SIBLING brick R481 (`seqEnclosingLocate_of_seqOpener_at_depth`) has exactly one
  such read — step (4)'s `rw [h_p_depth] at hc1` computing `balance lo hiS = 0 + 1 = 1`; dropping
  `h_p_depth` there costs swapping that to `balance lo hiS = d + 1 ≥ 1 > 0` from `d ≥ 0`.

**R485 — the prediction realized, off-by-zero.**  The R481 assemble was generalized to
`seqEnclosingLocate_of_seqOpener_nested` (same file) by dropping `h_p_depth`.  `grep` showed EXACTLY
the two predicted sites and no more: (1) the matching-close call — a pure SWAP to the R484 `_nested`
close (whose three containments are all floor reads), and (2) step (4)'s single `rw [h_p_depth]`
equality read, re-derived in one `omega` from the enclosing Dyck floor `h_dyck p : balance lo p ≥ 0`
(witness `= 1 ↦ ≥ 1`).  So the assemble is the first L4YAML consumer to exercise BOTH read kinds in
ONE proof — it is literally `consumerAN` (the swap) composed with `consumerBN` (the re-derivation)
below.  Moreover the assemble CONSUMES R484's `_nested` close, so this turn also retyped that
verified-but-unconsumed primitive into a consumed one ([[ref-reduction-by-import]]).

**The rule:**  cost(drop a base-depth hypothesis) = (locator call → pure swap to the depth-general
twin) + (one re-derivation per `=0`-equality read).  Both are countable by `grep`-ing the hypothesis
before touching the proof.  The tell of a free read vs a costly one: does the fact come from a floor
`≥ 0` (frame-stable, free) or from substituting the equality `= 0` (pinned, re-derive)?

This toy strips the balance arithmetic to a single `Int` depth `d`, models the depth-0 primitive as a
specialization of the depth-general one (the general subsumes the special — exactly
`flowBracketBalance_matching_close_seq_nested` subsuming `…_seq`), and shows the two consumer shapes:
a FLOOR-only consumer that generalizes by pure swap, and an EQUALITY-reading consumer that costs one
`omega` re-derivation.
-/

namespace DepthHypCostIsItsEqualityReads

set_option autoImplicit false

/-! ### The primitive: a depth-general locator that SUBSUMES its depth-0 special case.

`d` models the located opener's depth `balance lo p`.  The locator delivers a close witness whose
interior balance is `0`.  The depth-general form needs only the *floor* `0 ≤ d`; the depth-0 form is
its `d = 0` specialization. -/

/-- **Depth-general locator** (the toy `flowBracketBalance_matching_close_seq_nested`): from the floor
    `0 ≤ d` it produces a close witness with interior balance `0`. -/
theorem closeN (d : Int) (h : 0 ≤ d) : ∃ inner : Int, inner = 0 ∧ 0 ≤ d :=
  ⟨0, rfl, h⟩

/-- **Depth-0 locator** (the toy `…_seq`), DERIVED from `closeN` — the general one subsumes the
    special, just as the nested locator subsumes the depth-0 one. -/
theorem close0 (d : Int) (h : d = 0) : ∃ inner : Int, inner = 0 ∧ 0 ≤ d :=
  closeN d (by omega)

/-! ### Consumer A — FLOOR-only reads: generalizes by a PURE SWAP.

The depth hypothesis is read at exactly one site, the locator call.  Every other fact comes from the
existential the locator hands back.  So the depth-general version is byte-identical except the
hypothesis `d = 0 ↦ 0 ≤ d` and the call `close0 ↦ closeN`. -/

/-- depth-0 consumer: `h` used SOLELY to call `close0`. -/
theorem consumerA0 (d : Int) (h : d = 0) : ∃ inner : Int, inner = 0 := by
  obtain ⟨inner, hinner, _⟩ := close0 d h
  exact ⟨inner, hinner⟩

/-- depth-general consumer: the pure swap.  Diff vs `consumerA0` is exactly `d = 0 ↦ 0 ≤ d` and
    `close0 ↦ closeN`; the `obtain`/`exact` lines are byte-identical. -/
theorem consumerAN (d : Int) (h : 0 ≤ d) : ∃ inner : Int, inner = 0 := by
  obtain ⟨inner, hinner, _⟩ := closeN d h
  exact ⟨inner, hinner⟩

/-! ### Consumer B — an EQUALITY read: costs one re-derivation.

This consumer concludes the located close `bal lo close = d + 1 + inner` is nonzero (so the close is
BEFORE the window end `bal lo hi = 0`).  The depth-0 proof `rw [h]`s the equality to compute
`0 + 1 + 0 = 1 ≠ 0`.  That `rw` is depth-BOUND: at depth ≥ 1 it is gone, and the conclusion must be
re-derived from the floor `0 ≤ d` (giving `d + 1 ≥ 1 > 0`). -/

/-- depth-0 consumer: reads the depth EQUALITY via `rw [h]`. -/
theorem consumerB0 (d inner : Int) (hinner : inner = 0) (h : d = 0) : d + 1 + inner ≠ 0 := by
  rw [h, hinner]   -- the EQUALITY read — depth-BOUND: `0 + 1 + 0 ≠ 0`
  omega

/-- depth-general consumer: the `rw [h]` is GONE; the SAME conclusion re-derives from `0 ≤ d` by
    `omega` (`d + 1 ≥ 1 > 0`).  This is the one re-derivation the equality read costs. -/
theorem consumerBN (d inner : Int) (hinner : inner = 0) (h : 0 ≤ d) : d + 1 + inner ≠ 0 := by
  omega   -- the FLOOR read — frame-stable; no equality needed

/-! ### The cost, side by side.

`consumerA0 → consumerAN` is a pure swap (zero re-derivations: all reads are floor reads).
`consumerB0 → consumerBN` costs one re-derivation (one equality read: the `rw [h]`).
So `cost(drop the base-depth hypothesis) = number of `=0`-equality reads`, countable by grep before
editing.  In L4YAML R484: the close-within locator has 0 equality reads (pure swap, landed).  R485:
the assemble `seqEnclosingLocate_of_seqOpener_nested` has exactly 1 (LANDED) — `consumerAN ∘ consumerBN`,
the prediction off-by-zero. -/

/-- The pure-swap pair really do prove the same statement up to the hypothesis weakening: the general
    consumer, fed `0 ≤ d` recovered from `d = 0`, reproduces the depth-0 one. -/
theorem consumerA_general_subsumes (d : Int) (h : d = 0) :
    (∃ inner : Int, inner = 0) :=
  consumerAN d (by omega)

/-- And the equality-reading pair likewise: the general B, fed `0 ≤ d`, reproduces depth-0 B. -/
theorem consumerB_general_subsumes (d inner : Int) (hinner : inner = 0) (h : d = 0) :
    d + 1 + inner ≠ 0 :=
  consumerBN d inner hinner (by omega)

end DepthHypCostIsItsEqualityReads
