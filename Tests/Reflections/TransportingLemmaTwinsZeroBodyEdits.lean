/-!
# Reflection 492 — a TRANSPORTING lemma (guard obtained-then-rethreaded, never inspected) re-threads to
its `_seq` twin with ZERO body edits: a SIGNATURE-ONLY swap, the FLOOR of the grep-bounded cost.

Self-contained (core Lean, no `L4YAML` import) toy recording the structure that step γ′ surfaced while
landing `seqWidthEnc_of_enclosingLocate_and_recIH_seq` — the `FlowBodyContentDeepSeq`-keyed twin of R475
`seqWidthEnc_of_enclosingLocate_and_recIH`, the next link of the `_seq` re-thread after the leaf assemble
`seqEnclosingLocate_of_seqOpener_nested_seq` (R491).

**The setup.**  The `_seq` re-thread ([[RethreadStaysInWeakerTwinFamily]], R489; seeded per
[[RootSeedNeedsRootTrueGuard]], R488) re-keys the seq carrier chain off the root-FALSE strong content guard
`FlowBodyContentDeep` onto its root-TRUE weaker twin `FlowBodyContentDeepSeq`.  R491
([[RescopeAssembleCostIsGuardReadSites]]) landed the LEAF ASSEMBLE — a CONSTRUCTING lemma whose guard
hypothesis is READ at the child-bracket constructors that BUILD the deliverable's guard conjuncts, so its
twin cost EXACTLY the read sites (2 body swaps).  This turn lands the next link UP the chain — R475, the
per-step width-enc ASSEMBLE — and finds it is a different KIND of lemma.

**The find — TRANSPORT vs CONSTRUCT: a transporting lemma's twin is a SIGNATURE-ONLY swap, ZERO body
edits.**  R475 never CONSTRUCTS the guard.  It `obtain`s `h_deep : Strong` from its `locate` hypothesis,
`refine`s it straight into the conclusion's matching slot, and threads the conclusion's IH premise straight
into `recIH`.  The guard is never matched, destructured, or pattern-analysed — it is TRANSPORTED.  Grep the
guard name in R475's BODY: ZERO hits; every occurrence is in the SIGNATURE (4 positions: the `locate`
deliverable, the `recIH` premise, the conclusion deliverable, the conclusion IH premise).  So:

  cost(re-scope a CONSTRUCTING assemble) = (grep the guard hyp) read sites, each a SWAP to its child twin
                                           + swap the guard TYPE in the signature.        [R491: 2 + types]
  cost(re-scope a TRANSPORTING lemma)    = swap the guard TYPE in the signature; BODY copies byte-identical.
                                                                                          [R492: 0 + types]

The transporting lemma is the FLOOR of the grep-bounded cost — its read-site count is literally 0 because
the guard is carried, not consumed.  This is WHY a whole re-thread chain is cheap: its cost concentrates in
the few CONSTRUCTING leaves (R489/R490/R491), while every PLUMBING link (R475→R492) re-keys for free.

**The formal content of "zero body edits."**  Below, `transport_generic {G}` is the guard-AGNOSTIC core:
its proof term does not mention which guard `G` is — it works for ANY proposition.  The two concrete named
lemmas `transport_strong` (toy R475) and `transport_seq` (toy R492) each derive from `transport_generic` by
the IDENTICAL one-liner application; only the signature's guard differs (`Strong` ↦ `Weak`, 4 positions).
That two concrete lemmas share one generic core is precisely "byte-identical body" made provable.

This is the structural-GUARD floor of [[DepthHypCostIsItsEqualityReads]] (a scalar baseline, where each read
swaps to a depth-general twin OR re-derives one equality) and of [[RescopeAssembleCostIsGuardReadSites]] (a
constructing assemble, where each read swaps to a child twin): when the read-site count is 0 (pure
transport), even the swaps vanish and only the signature type changes.
-/

namespace TransportingLemmaTwinsZeroBodyEdits

set_option autoImplicit false

/-! ### Two additive-parallel guard families: `Strong` interior-only (root-false), `Weak` root-true. -/

/-- Toy `FlowBodyContentDeep` — the strong content guard (in the real chain, provably FALSE at the root). -/
abbrev Strong (n : Nat) : Prop := 2 ≤ n
/-- Toy `FlowBodyContentDeepSeq` — the root-TRUE weaker twin the re-thread is keyed on. -/
abbrev Weak (n : Nat) : Prop := 1 ≤ n

/-- A family-NEUTRAL conjunct of the deliverable (toy `FlowBodyContent`). -/
abbrev Content (n : Nat) : Prop := 0 < n
/-- The recursion deliverable the IH produces (toy `RecSeqBody`). -/
abbrev Rec (n : Nat) : Prop := 0 < n

/-! ### The guard-AGNOSTIC core — the formal witness that the body has ZERO guard dependence. -/

/-- **The transport body, written ONCE for ANY guard `G`.**  It obtains `⟨hc, hg⟩` from the locator,
    re-threads `hg` into the deliverable and `recIH` into the IH slot — never inspecting `hg`.  Because the
    proof term does not mention which proposition `G` is, the SAME term serves every guard: that is the
    formal content of "the body copies byte-identical across the re-thread." -/
theorem transport_generic {G C R : Prop} (locate : C ∧ G) (recIH : G → R) :
    G ∧ C ∧ (G → R) := by
  obtain ⟨hc, hg⟩ := locate          -- guard `hg` is OBTAINED…
  exact ⟨hg, hc, recIH⟩              -- …and re-threaded verbatim; never matched/destructured.

/-! ### The two concrete named lemmas — each the IDENTICAL application of the core, differing only in type. -/

/-- **The STRONG transporting assemble (toy `seqWidthEnc_of_enclosingLocate_and_recIH`, R475).**  Names the
    strong guard in 4 signature positions (the `locate` deliverable, the `recIH` premise, the conclusion
    deliverable, the conclusion IH premise).  Body = one application of the guard-agnostic core. -/
theorem transport_strong (n : Nat)
    (locate : Content n ∧ Strong n) (recIH : Strong n → Rec n) :
    Strong n ∧ Content n ∧ (Strong n → Rec n) :=
  transport_generic locate recIH

/-- **THE BRICK (toy `seqWidthEnc_of_enclosingLocate_and_recIH_seq`, R492).**  The `_seq` re-scope: the
    guard type swaps `Strong ↦ Weak` in EXACTLY the same 4 signature positions, and the BODY is the IDENTICAL
    one-liner — `transport_generic locate recIH`, character-for-character `transport_strong`'s.  Zero body
    edits: that is the grep-bounded cost's FLOOR realized (a transporting lemma reads the guard 0 times). -/
theorem transport_seq (n : Nat)
    (locate : Content n ∧ Weak n) (recIH : Weak n → Rec n) :
    Weak n ∧ Content n ∧ (Weak n → Rec n) :=
  transport_generic locate recIH

/-! ### Contrast — a CONSTRUCTING lemma DOES read the guard, so its twin's body DOES change (R491's case). -/

/-- A CONSTRUCTING leaf (toy R491 child producer): the guard is READ to build the deliverable's guard
    conjunct.  Swapping the family forces a body edit — the read site must call the OTHER family's producer.
    Modelled here as the read being the guard itself; in the real chain the read is a child-bracket
    constructor call (`flowBodyContentDeep_child_bracket ↦ flowBodyContentDeepSeq_child_bracket`). -/
theorem construct_strong (n : Nat) (h_deep : Strong n) : Strong n := h_deep   -- reads h_deep (strong)
theorem construct_seq (n : Nat) (h_deep : Weak n) : Weak n := h_deep          -- body CHANGES: strong↦weak read

/-- The distinction made explicit: `transport_seq`'s body is the SAME core application as `transport_strong`
    (the guard is carried), whereas `construct_seq`'s body differs from `construct_strong`'s at the read
    site (the guard is consumed).  Transport = 0 read sites = signature-only; construct = k read sites. -/
example (n : Nat) (hc : Content n) (hg : Weak n) (recIH : Weak n → Rec n) :
    Weak n ∧ Content n ∧ (Weak n → Rec n) :=
  transport_seq n ⟨hc, hg⟩ recIH

end TransportingLemmaTwinsZeroBodyEdits
