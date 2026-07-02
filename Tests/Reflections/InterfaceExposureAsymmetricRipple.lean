/-!
# Reflection 445 — clearing a recursive producer's DESCEND-edge obstruction (R444's ROUTE A) by EXPOSING
# the hidden relation through a forwarded IH/callback interface has an ASYMMETRIC cost: O(chain length)
# signature edits but only O(consuming sinks) proof edits.  The exposed relation is PROVED at the sink,
# TYPED-THROUGH the forwarders (verbatim, zero proof), and CONSUMED at the provider — where the
# maintained invariant is re-established by COMPOSING the captured outer bound with the now-exposed local
# relation (descend = one transitivity; advance = one omega, no exposure needed).

Self-contained (core Lean, no `L4YAML` import) toy of the R445 finding — STEP D continued: ROUTE A of the
R444 obstruction, EXECUTED.

Context.  R444 ([[ref-generalization-hides-descend-obstruction]]) found that generalizing
`seqWindowRecSeqBody`'s carrier span to a parametric `[lo0, hi0]` makes the recursion maintain the bound
`lo0 ≤ lo ∧ hi ≤ hi0` as an invariant — FREE at the ADVANCE edge but UNPROVABLE at DESCEND, because the
dispatch's IH adapter (`recseqentry_window_dispatch`'s `h_ih`) exposed ONLY the width-decrease
`hi' - lo' < hi - lo`, not the containment `lo ≤ lo' ∧ hi' ≤ hi` the bound needs.  R444 isolated two
routes; R445 executes ROUTE A: add `lo ≤ lo' → hi' ≤ hi →` to the shared `RecSeqBody`-producing IH
interface, threaded through the WHOLE descent chain.

The execution revealed the cost STRUCTURE of an interface exposure.  The two containment premises were:

* ADDED to the `h_ih` type of NINE lemmas (the two bracket oracles, two window dispatches,
  `seqChild_safeBodyUnit`, `flowBodyContent_descend`, `seqDescent_provider_of_located`, and the embedded
  IHs of `seqDescent_provider_of_gate`'s `h_enc` and `seqRoot_carrier_of_widthEnc`'s `h_widthEnc`);
* PROVED at only TWO sites — the bracket oracles' internal `h_ih (lo+1) j …` calls, the ONE place the IH
  is genuinely CALLED rather than forwarded.  There the descend is `[lo,hi) → [lo+1, j)` with `j < hi`,
  so `lo ≤ lo+1` (`omega`) and `j ≤ hi` (`Nat.le_of_lt`) are trivially available;
* FORWARDED VERBATIM everywhere else — every intermediate node passes `h_ih` by name, carrying the new
  premises in the `∀`-type and proving NOTHING.

So the ripple is asymmetric: its SIZE is O(chain length) signatures but its DIFFICULTY is O(consuming
sinks) = two `omega`s.  The exposed relation is proved at the sink, typed through the forwarders, and
CONSUMED at the PROVIDER — the recursion adapter (`seqWindowRecSeqBody_general`'s
`fun lo' hi' h_lt h_cont_lo h_cont_hi … => ih lo' hi' h_lt ⟨…, Nat.le_trans …, Nat.le_trans …⟩`), which
combines the captured outer invariant `lo0 ≤ lo ∧ hi ≤ hi0` with the now-exposed local containment by
transitivity to re-establish the bound at the descend child.  Both edges become one-liners: descend = one
`Nat.le_trans` (compose captured + exposed); advance = one `omega` (the easy edge, no exposure needed).

The deliverable.  `seqWindowRecSeqBody_general` / `_seq_general` — the carrier-span generalization now
RIDES the recursion (parametric `[lo0, hi0]` carrier threaded as two extra `G`-conjuncts), with the
root-span `seqWindowRecSeqBody` / `_seq` as thin `lo0 := 2`, `hi0 := size-2` instances reading the bounds
off `FlowBodyWindow.lo_ge`/`hi_le` (additive `_general` + signature-preserving wrapper, consumers
untouched).

The reusable rule.  When you strengthen a FORWARDED callback/IH interface to expose a hidden relation,
the relation is PROVED ONCE at the consuming sink, merely TYPED through the forwarding chain, and CONSUMED
at the provider by composing it with the captured invariant.  The ripple's SIZE (signatures) is not its
DIFFICULTY (proofs); count the genuine CALL sites, not the forwarders.

This toy models the three roles — `forward` (typed-through, the identity, zero proof), `supply_at_sink`
(the descend call, trivial), `consume_descend` / `build_dispatch_callback` (the provider's composition,
one `Nat.le_trans`) — and `consume_advance` (the easy edge), with `r445_finding` the capstone: with
containment EXPOSED the descend bound is re-establishable (contrast R444's countermodel from width-decrease
alone).  All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.InterfaceExposureAsymmetricRipple

/-! ## The parametric bound the recursion maintains: `[lo, hi) ⊆ [lo0, hi0)`.  Models
    `seqWindowRecSeqBody_general`'s two extra `G`-conjuncts `lo0 ≤ lo ∧ hi ≤ hi0`. -/
def Covers (lo0 hi0 lo hi : Nat) : Prop := lo0 ≤ lo ∧ hi ≤ hi0

/-! ## The shared IH/callback interface AFTER exposing the local containment `lo ≤ lo' ∧ hi' ≤ hi`.
    Models `recseqentry_window_dispatch`'s `h_ih` post-R445 (`D` stands for the per-window deliverable). -/
def Callback (lo hi : Nat) (D : Nat → Nat → Prop) : Prop :=
  ∀ lo' hi', hi' - lo' < hi - lo → lo ≤ lo' → hi' ≤ hi → D lo' hi'

/-! ## FORWARD — the typed-through node.  An intermediate node passes the callback VERBATIM: the exposed
    premises ride along in the TYPE and the forwarder proves NOTHING.  Models the descent chain
    (`seqChild_safeBodyUnit`, the dispatches, `seqDescent_provider_of_*`, `…_widthEnc`'s embedded IH) each
    forwarding `h_ih` by name.  Cost: a signature edit, zero proof — this is the bulk of the ripple. -/
theorem forward {lo hi : Nat} {D : Nat → Nat → Prop} (k : Callback lo hi D) : Callback lo hi D := k

/-! ## SUPPLY AT SINK — the ONE site that CALLS the callback.  The descend `[lo,hi) → [lo+1, j)` with
    `j < hi`: the exposed premises discharge trivially (`lo ≤ lo+1`, `j ≤ hi`).  Models the bracket
    oracles' internal `h_ih (lo+1) j … (by omega) (Nat.le_of_lt h_j_hi) …` call — the only genuine
    proof content of the whole ripple. -/
theorem supply_at_sink {lo hi j : Nat} {D : Nat → Nat → Prop}
    (k : Callback lo hi D) (h_lt : j - (lo + 1) < hi - lo) (h_j : j < hi) : D (lo + 1) j :=
  k (lo + 1) j h_lt (Nat.le_succ lo) (Nat.le_of_lt h_j)

/-! ## CONSUME AT PROVIDER (descend) — the recursion adapter combines the CAPTURED outer invariant
    `Covers lo0 hi0 lo hi` with the now-EXPOSED local containment to re-establish the maintained bound at
    the descend child `[lo', hi')`.  One `Nat.le_trans` each.  UNPROVABLE before the exposure (R444's
    countermodel: width-decrease alone admits `[5,10] → [0,1]`, `5 ≤ 0` false). -/
theorem consume_descend {lo0 hi0 lo hi lo' hi' : Nat}
    (h_cov : Covers lo0 hi0 lo hi) (h_cont_lo : lo ≤ lo') (h_cont_hi : hi' ≤ hi) :
    Covers lo0 hi0 lo' hi' :=
  ⟨Nat.le_trans h_cov.1 h_cont_lo, Nat.le_trans h_cont_hi h_cov.2⟩

/-! ## CONSUME AT PROVIDER (advance) — the EASY edge.  Re-establish the bound at `(lo+1, hi)` from the
    captured invariant alone — one transitivity, no exposure needed.  Models the advance tail-call
    `ih (m+1) hi … ⟨…, by omega, h_hi_hi0⟩`. -/
theorem consume_advance {lo0 hi0 lo hi : Nat} (h_cov : Covers lo0 hi0 lo hi) :
    Covers lo0 hi0 (lo + 1) hi :=
  ⟨Nat.le_trans h_cov.1 (Nat.le_succ lo), h_cov.2⟩

/-! ## The PROVIDER builds the exposing callback from the recursion's OUTER `ih`.  This is the EXACT shape
    of `seqWindowRecSeqBody_general`'s dispatch adapter: the outer `ih` demands the child's guard include
    the maintained bound `Covers`, and the dispatch's callback exposes the containment; the adapter
    bridges them by CONSUMING the exposed containment (`consume_descend`) to build the `Covers` conjunct.
    The exposed premise has a CONSUMER — that is the whole point of ROUTE A. -/
theorem build_dispatch_callback {lo0 hi0 lo hi : Nat}
    {Gcore : Nat → Nat → Prop} {P : Nat → Nat → Prop}
    (h_cov : Covers lo0 hi0 lo hi)
    (ih : ∀ lo' hi', hi' - lo' < hi - lo → (Gcore lo' hi' ∧ Covers lo0 hi0 lo' hi') → P lo' hi') :
    Callback lo hi (fun lo' hi' => Gcore lo' hi' → P lo' hi') :=
  fun lo' hi' h_lt h_cont_lo h_cont_hi h_core =>
    ih lo' hi' h_lt ⟨h_core, consume_descend h_cov h_cont_lo h_cont_hi⟩

/-- The finding in one proposition: with the containment EXPOSED, the provider re-establishes the
    maintained bound at the descend child by composition (total) and the advance edge is free — whereas
    R444 showed the bound is UNPROVABLE from width-decrease alone.  The ripple between sink and provider
    is pure type-plumbing (`forward` is the identity). -/
theorem r445_finding {lo0 hi0 lo hi : Nat} (h_cov : Covers lo0 hi0 lo hi) :
    (∀ lo' hi', lo ≤ lo' → hi' ≤ hi → Covers lo0 hi0 lo' hi')   -- provider: exposed ⇒ re-established
    ∧ Covers lo0 hi0 (lo + 1) hi :=                              -- advance: free
  ⟨fun _ _ h_lo h_hi => consume_descend h_cov h_lo h_hi, consume_advance h_cov⟩

end Tests.Reflections.InterfaceExposureAsymmetricRipple
