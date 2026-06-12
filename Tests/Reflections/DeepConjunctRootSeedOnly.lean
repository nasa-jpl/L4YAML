/-!
# Reflection 391 — an all-depth BALANCE-FREE conjunct flagged "owes a deep characterization" owes
it at the ROOT WINDOW ONLY; every gated window RESTRICTS from a single root instance.

Self-contained core-Lean toy of L4YAML R391.  R390 ([[ref-depth-gate-restriction-diagnostic]]) split
the per-window provider into restriction conjuncts and one ALL-DEPTH conjunct it flagged as "owes a
deep characterization."  The trap is to read that as a window-PARAMETERIZED induction — proving the
fact afresh at every window.  R391's resolution: if the conjunct is BALANCE-FREE (its universals
carry no balance gate — a true subset-restriction across windows), the deep fact is owed at the
ROOT window ONLY.  Land a restriction lemma `*_window_of_root`; the residual collapses to ONE root
instance (the genuine emitter induction), and every gated window is then free.

Mapping to L4YAML: `content` ~ "position holds a content-start head" (`isFlowContentStart`);
`opener` ~ a `flowSequenceStart` opener (`flowBracketDelta = 1`); `N` ~ `tokens.size - 2`;
`rootHead`/`rootOpen` ~ the two non-trivial fields of the ROOT `FlowBodyContentDeep tokens 2 (N)`;
`windowOpener_from_root`/`windowHead_from_root` ~ `flowBodyContentDeep_window_of_root`'s interior
and head obligations; `gate0` ~ the depth-`0` balance gate; `gated_holds`/`root_not_from_gated` ~
the DUALITY (the root fact is NOT a consequence of the gated depth-`0` fact, so it owes the deep
characterization — but ONCE seeded, every window restricts for free).

POSITIVE: `windowOpener_from_root` — interior universals are direct sub-universals of the root's
(pure omega, balance-freeness makes nesting irrelevant); `windowHead_from_root` — the position-keyed
head recovers from the root's opener field at the window's own opener `lo-1`, with `lo = 2` falling
back to the root head (mirrors the real proof's `rcases Nat.eq_or_lt_of_le` / `Nat.sub_add_cancel`).
NEGATIVE: `gated_holds` ∧ `root_not_from_gated` — the deep ROOT fact is NOT derivable from the gated
depth-`0` fact (the balance-freeness that BLOCKS the gated route is what the root seed must supply),
so it is the lone irreducible residual.

Sharpens [[ref-non-restriction-residual-root-seed]] and resolves [[ref-depth-gate-restriction-diagnostic]].
-/

namespace Tests.Reflections.DeepConjunctRootSeedOnly

set_option autoImplicit false

/-! ## The all-depth, balance-free conjunct as a position predicate.

`content k` models "the token after position `k` is a content-start head"; `opener k` models
"position `k` is an opener" (`flowBracketDelta = 1`).  They are abstract — the restriction is a
pure quantifier-domain narrowing, independent of what they mean. -/

/-- **POSITIVE — interior universal RESTRICTS from the root.**  The window's `openerContentStart`
    over `[lo, hi) ⊆ [2, N)` is a DIRECT sub-universal of the root's: drop the window bounds via
    `omega` (the field carries NO balance gate, so nesting is irrelevant).  Mirrors the real
    `flowBodyContentDeep_window_of_root`'s `openerContentStart`/`feContentStart` arms. -/
theorem windowOpener_from_root
    (content opener : Nat → Prop) (N : Nat)
    (rootOpen : ∀ k, 2 ≤ k → k + 1 < N → opener k → content (k + 1))
    (lo hi : Nat) (h_lo : 2 ≤ lo) (h_hi : hi ≤ N) :
    ∀ k, lo ≤ k → k + 1 < hi → opener k → content (k + 1) :=
  fun k hk1 hk2 ho => rootOpen k (by omega) (by omega) ho

/-- **POSITIVE — position-keyed head RECOVERS from the root.**  The window's `headContentStart`
    (`content lo`) is recovered from the root's OPENER field at the window's own opener `lo - 1`
    (the gate supplies `opener (lo - 1)`), with the degenerate `lo = 2` falling back to the root
    HEAD itself.  Mirrors the real proof's `rcases Nat.eq_or_lt_of_le` + `Nat.sub_add_cancel`. -/
theorem windowHead_from_root
    (content opener : Nat → Prop) (N : Nat)
    (rootHead : content 2)
    (rootOpen : ∀ k, 2 ≤ k → k + 1 < N → opener k → content (k + 1))
    (lo hi : Nat) (h_lo : 2 ≤ lo) (h_lo_hi : lo < hi) (h_hi : hi ≤ N)
    (h_open : opener (lo - 1)) :
    content lo := by
  rcases Nat.eq_or_lt_of_le h_lo with h_eq | h_gt
  · -- lo = 2: the root head directly
    rw [← h_eq]; exact rootHead
  · -- lo > 2: the root opener fact at k = lo - 1
    have h := rootOpen (lo - 1) (by omega) (by omega) h_open
    rwa [Nat.sub_add_cancel (by omega)] at h

/-! ## The DUALITY — the root fact is NOT a consequence of the gated depth-`0` fact.

Concrete instance: `content` genuinely fails at position `4`, `gate0` is the even (depth-`0`) gate. -/

/-- The all-depth conjunct, here failing at one position (`content 4` is false). -/
def content (k : Nat) : Prop := k ≠ 4
/-- The depth-`0` gate the in-scope global fact carries (even positions ~ `balance = 0`). -/
def gate0 (k : Nat) : Prop := k % 2 = 0

/-- **NEGATIVE (part 1) — the gated depth-`0` fact HOLDS.**  At every gated (even) `k`,
    `content (k + 1)` holds: an even `k` can never have `k + 1 = 4` (that needs `k = 3`, odd). -/
theorem gated_holds : ∀ k, gate0 k → content (k + 1) := by
  intro k hg; unfold gate0 at hg; unfold content; omega

/-- **NEGATIVE (part 2) — the all-depth ROOT fact does NOT follow.**  The ungated position `k = 3`
    (odd, the gate can't reach it) gives `content 4`, which is false.  No bounding of the gated fact
    yields the all-depth one — the root seed carries strictly more information (it owes the emitter
    induction).  This is the balance-freeness BLOCKING the gated route; the root seed supplies it,
    and `windowOpener_from_root`/`windowHead_from_root` then make every window free. -/
theorem root_not_from_gated : ¬ (∀ k, content (k + 1)) := by
  intro h; have h3 := h 3; unfold content at h3; omega

#guard (0 % 2 == 0) && (2 % 2 == 0)   -- gate0 holds at the even (depth-0) positions
#guard !(3 % 2 == 0)                  -- k = 3 is ungated — the position the deep fact fails at
#guard !(4 == 4) == false             -- content 4 is false (4 = 4): the all-depth fact's failure point

end Tests.Reflections.DeepConjunctRootSeedOnly
