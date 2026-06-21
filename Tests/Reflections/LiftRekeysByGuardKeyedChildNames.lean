/-!
# Reflection 493 — a LIFT (a lemma whose body is a composition of child-lemma calls) re-keys to a
guard's weaker twin via one NAME swap per guard-KEYED child it invokes; guard-NEUTRAL calls are free.
The swap unit at a lift is the guard-keyed NAME, not the guard READ — so even a TRANSPORTING child's call
swaps its name at the parent's call site.

Self-contained (core Lean, no `L4YAML` import) toy recording the structure step γ′ surfaced while landing
`seqWidthEnc_of_recIH_seq` — the `FlowBodyContentDeepSeq`-keyed twin of R486 `seqWidthEnc_of_recIH`, the
next link of the `_seq` re-thread after the per-step ASSEMBLE `seqWidthEnc_of_enclosingLocate_and_recIH_seq`
(R492) and the leaf assemble `seqEnclosingLocate_of_seqOpener_nested_seq` (R491).

**The setup.**  The `_seq` re-thread ([[RethreadStaysInWeakerTwinFamily]], R489; seeded per
[[RootSeedNeedsRootTrueGuard]], R488) re-keys the seq carrier chain off the root-FALSE strong content guard
`FlowBodyContentDeep` onto its root-TRUE weaker twin `FlowBodyContentDeepSeq`.  R491
([[RescopeAssembleCostIsGuardReadSites]]) landed a CONSTRUCTING leaf (its twin cost = guard read sites);
R492 ([[TransportingLemmaTwinsZeroBodyEdits]]) landed a TRANSPORTING per-step assemble (its twin's BODY is
byte-identical, 0 read sites).  This turn lands the LIFT above both of them — R486 `seqWidthEnc_of_recIH`,
whose body COMPOSES a transporting child, a guard-neutral helper, and a constructing child.

**The find — the swap unit at a lift is the guard-keyed NAME, not the guard READ.**  R492 measured a
lemma's OWN twinning cost by counting guard READS in its body (transport = 0, construct = k).  But a LIFT
that CALLS a guard-keyed child must swap that call's NAME to the child's twin REGARDLESS of whether the
child is transport or construct — because the child's NAME is guard-typed and the strong name produces the
strong deliverable, which won't unify with the `_seq` conclusion.  R486 calls THREE lemmas:
  1. `seqWidthEnc_of_enclosingLocate_and_recIH` — a TRANSPORTING child (R475/R492).  Its body twins for
     free, but its NAME is guard-keyed ⇒ the lift swaps the call to `…_seq` (R492).
  2. `seqOpenerType_of_located_and_gate` — a guard-NEUTRAL helper (names no content guard).  UNCHANGED,
     character-for-character.
  3. `seqEnclosingLocate_of_seqOpener_nested` — a CONSTRUCTING child (R485/R491).  NAME guard-keyed ⇒ swap
     the call to `…_seq` (R491).
So the lift's body cost is TWO named swaps (the two guard-keyed children), not the "≈1 swap" an
earlier read predicted by counting only the constructing call.  The transport/construct distinction governs
each CHILD's own twinning cost; it does NOT discount the lift's call to a transporting child.

  cost(re-key a LIFT) = #(guard-KEYED child lemmas it invokes), each a NAME swap to the child's twin.
                        Guard-NEUTRAL invocations are free.            [R486→R493: 2 keyed + 1 neutral]

**Why "transport ⇒ verbatim" is right for the child but wrong for the parent's call.**  Transport (R492)
means the child's PROOF TERM is guard-agnostic, so the child's strong/weak versions are one core (its body
copies byte-identical).  But the parent does not copy the child's body — it NAMES the child.  A name is a
guard-typed reference; the strong name has the strong type.  So the parent's call to a transporting child
is a name swap exactly like its call to a constructing child.  The distinction collapses at the call site:
both keyed children cost one name swap; only the guard-NEUTRAL helper is free.
-/

namespace LiftRekeysByGuardKeyedChildNames

set_option autoImplicit false

/-! ### Two additive-parallel guard families + a guard-neutral discriminator. -/

/-- Toy `FlowBodyContentDeep` — the strong content guard (root-FALSE in the real chain). -/
abbrev Strong (n : Nat) : Prop := 2 ≤ n
/-- Toy `FlowBodyContentDeepSeq` — the root-TRUE weaker twin the re-thread is keyed on. -/
abbrev Weak (n : Nat) : Prop := 1 ≤ n
/-- A family-neutral conjunct (toy `FlowBodyContent`). -/
abbrev Content (n : Nat) : Prop := 0 < n
/-- The recursion deliverable (toy `RecSeqBody`). -/
abbrev Rec (n : Nat) : Prop := 0 < n
/-- A guard-NEUTRAL discriminator (toy `flowSequenceStart` opener type) — names no content guard. -/
abbrev Disc (n : Nat) : Prop := n = n

/-! ### The three children: transport child, neutral helper, construct child. -/

/-- **Transporting child** (toy `seqWidthEnc_of_enclosingLocate_and_recIH`, R475/R492).  Carries the
    guard `G` and an IH; never inspects `G`.  Body is guard-agnostic ⇒ the strong/weak versions share
    one core and copy byte-identical ([[TransportingLemmaTwinsZeroBodyEdits]]). -/
theorem transport_child_strong (n : Nat) (hg : Strong n) (k : Strong n → Rec n) :
    Strong n ∧ (Strong n → Rec n) := ⟨hg, k⟩
theorem transport_child_seq (n : Nat) (hg : Weak n) (k : Weak n → Rec n) :
    Weak n ∧ (Weak n → Rec n) := ⟨hg, k⟩          -- body IDENTICAL to strong; only the signature type swapped

/-- **Guard-NEUTRAL helper** (toy `seqOpenerType_of_located_and_gate`).  Names no content guard ⇒ there is
    NO `_seq` twin and the lift's call to it is UNCHANGED. -/
theorem neutral_helper (n : Nat) (_hc : Content n) : Disc n := rfl

/-- **Constructing child** (toy `seqEnclosingLocate_of_seqOpener_nested`, R485/R491).  READS the guard to
    build the deliverable; its strong/weak bodies differ at the read site
    ([[RescopeAssembleCostIsGuardReadSites]]). -/
theorem construct_child_strong (n : Nat) (hg : Strong n) : Strong n ∧ Content n :=
  ⟨hg, Nat.le_of_succ_le hg⟩                    -- reads hg (strong) via `le_of_succ_le` to drop 2≤n to 0<n
theorem construct_child_seq (n : Nat) (hg : Weak n) : Weak n ∧ Content n :=
  ⟨hg, hg⟩                                       -- body CHANGES at the read site: `1 ≤ n` IS `0 < n`, read direct

/-! ### The LIFT and its twin — two NAME swaps (the keyed children), the neutral call verbatim. -/

/-- **The strong LIFT** (toy `seqWidthEnc_of_recIH`, R486).  Composes the three children: a transporting
    call, a guard-neutral call, a constructing call.  Conclusion bundles the guard, the discriminator, and
    the constructed deliverable. -/
theorem lift_strong (n : Nat) (hg : Strong n) (hc : Content n) (k : Strong n → Rec n) :
    (Strong n ∧ (Strong n → Rec n)) ∧ Disc n ∧ (Strong n ∧ Content n) :=
  ⟨transport_child_strong n hg k, neutral_helper n hc, construct_child_strong n hg⟩

/-- **THE BRICK** (toy `seqWidthEnc_of_recIH_seq`, R493).  The `_seq` re-key.  The signature swaps the
    guard type (`Strong ↦ Weak`); the BODY swaps exactly the TWO guard-keyed child NAMES
    (`transport_child_strong ↦ transport_child_seq`, `construct_child_strong ↦ construct_child_seq`) and
    leaves the guard-NEUTRAL `neutral_helper` call character-for-character.  The transporting child's call
    swapped its NAME just like the constructing child's — transport ⇒ verbatim BODY (in the child), NOT
    verbatim CALL (in the parent). -/
theorem lift_seq (n : Nat) (hg : Weak n) (hc : Content n) (k : Weak n → Rec n) :
    (Weak n ∧ (Weak n → Rec n)) ∧ Disc n ∧ (Weak n ∧ Content n) :=
  ⟨transport_child_seq n hg k, neutral_helper n hc, construct_child_seq n hg⟩

/-- The count made explicit: re-keying `lift_strong` to `lift_seq` swapped TWO child names (the two
    guard-keyed children) and zero else; the neutral helper was free.  `#(guard-keyed children) = 2`. -/
example (n : Nat) (hg : Weak n) (hc : Content n) (k : Weak n → Rec n) :
    (Weak n ∧ (Weak n → Rec n)) ∧ Disc n ∧ (Weak n ∧ Content n) :=
  lift_seq n hg hc k

end LiftRekeysByGuardKeyedChildNames
