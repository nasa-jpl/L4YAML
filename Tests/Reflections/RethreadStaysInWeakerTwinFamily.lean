/-!
# Reflection 489 — a RESTRICTION producer cannot upgrade the guard: re-threading a window-parametric
chain onto the boundary-true WEAKER twin stays in the weak family END-TO-END, even at descended windows
where the strong guard genuinely holds.

Self-contained (core Lean, no `L4YAML` import) toy recording the de-risk that step γ′ surfaced while
landing `flowBodyContentDeepSeq_child_bracket` (the `_seq` twin of `flowBodyContentDeep_child_bracket`).

**The setup.**  R488 ([[RootSeedNeedsRootTrueGuard]]) established that the seq carrier chain must be
SEEDED at the root with the boundary-TRUE weaker guard `FlowBodyContentDeepSeq` (the interior-only
`FlowBodyContentDeep` is provably FALSE at the root).  Step γ′ re-threads the `enclosingLocate` chain
(R485 `seqEnclosingLocate_of_seqOpener_nested`) onto that weaker guard.  The chain's first `h_deep` read
is `flowBodyContentDeep_child_bracket`, which RESTRICTS the parent's deep guard to a child bracket window
`[p, hiE)` and delivers `FlowBodyContentDeep tokens p hiE` for the recursion's IH.

**The trap (and why a `_seq` twin, not a coercion).**  The child `[p, hiE)` IS a nested `[ … ]` window
where the strong `FlowBodyContentDeep` genuinely HOLDS — so the tempting shortcut is "produce the strong
child and feed the existing strong recursion."  This is FALSE in a restriction setting.  The producer
works by RESTRICTION (domain narrowing), which is MONOTONE in the guard: it can only carry forward the
fields the parent actually holds.  The weaker `FlowBodyContentDeepSeq` parent does not carry the strong
guard's `{`-opener / empty-`[]`-opener facts (it is gated to non-empty `.flowSequenceStart`), so the
strong child is UNREACHABLE from a weak parent — its truth at the child comes from GLOBAL emitter
structure the local restriction cannot see.  `Strong ⇒ Weak` coerces (drop to the gated subset), but
`Weak ⇒ Strong` does not.  So the re-thread must stay in the WEAK twin family end-to-end (weak parent →
weak child → weak-keyed IH, exactly `seqWindowRecSeqBody_seq`'s conjunct), and each child-producing
primitive needs a `_seq` twin — never a coercion back to the strong guard.

**The transferable rule.**  When you re-thread a window-parametric producer chain onto a boundary-true
WEAKER guard `P'` (to seed a recursion where the strong interior guard `P` is false), every
RESTRICTION-shaped child producer must output `P'` children, not `P` — even at descended windows where
`P` holds — because restriction is monotone in the guard and only propagates what the `P'` parent
carries.  The strong child's truth is irrelevant; what matters is derivability from the parent you hold.
Build a `_seq` twin of each child producer; do not reach for a `P' ⇒ P` upgrade (it does not exist).

This toy models a strong guard `Strong` (fires at EVERY opener, false at the root) and its re-scoped
weaker twin `Weak` (fires only at SEQ openers, true at the root), the one-way membrane between them, the
two restriction producers (`child_strong` / `child_weak`), and shows: at the root only `child_weak` is
available, so the chain stays weak — and the membrane is non-invertible (`Weak` holds where `Strong`
fails).
-/

namespace RethreadStaysInWeakerTwinFamily

set_option autoImplicit false

/-- Toy "this position is a (non-empty) SEQ opener" — the re-scoped opener class
    (`FlowBodyContentDeepSeq`, gated to `.flowSequenceStart`).  Concretely: only position `5`. -/
abbrev IsSeq (k : Nat) : Prop := k = 5

/-- Toy "this position is content-start".  Concretely: only position `6` (the successor of the lone seq
    opener `5`).  Every OTHER opener's successor is NOT content-start — the region the weak guard is
    silent about and the strong guard (wrongly, at the root) asserts. -/
abbrev Content (n : Nat) : Prop := n = 6

/-- **The interior (strong) guard** — toy `FlowBodyContentDeep.openerContentStart`, keyed type-blindly:
    fires at EVERY opener `k ≥ lo`.  Strong ⇒ demands content at non-seq openers too. -/
def Strong (lo : Nat) : Prop := ∀ k, lo ≤ k → Content (k + 1)

/-- **The re-scoped (weak) guard** — toy `FlowBodyContentDeepSeq.openerContentStart`: fires only at SEQ
    openers (`IsSeq k`).  A strict SUPERSET of premises, hence strictly weaker. -/
def Weak (lo : Nat) : Prop := ∀ k, lo ≤ k → IsSeq k → Content (k + 1)

/-! ### The membrane is ONE-WAY. -/

/-- `Strong ⇒ Weak` — drop to the gated subset of openers (toy `deepSeq_of_deep`). -/
theorem strong_to_weak {lo : Nat} (h : Strong lo) : Weak lo := by
  intro k hk _; exact h k hk

/-! ### The two RESTRICTION producers (child-bracket): both narrow the domain to a child window. -/

/-- The STRONG restriction producer (toy `flowBodyContentDeep_child_bracket`).  Needs a STRONG parent. -/
theorem child_strong {lo k : Nat} (h : Strong lo) (hlk : lo ≤ k) : Strong k := by
  intro k' hk'; exact h k' (by omega)

/-- **THE BRICK** — the WEAK restriction producer (toy `flowBodyContentDeepSeq_child_bracket`).  Needs
    only a WEAK parent; outputs a WEAK child.  This is the `_seq` twin step γ′ landed. -/
theorem child_weak {lo k : Nat} (h : Weak lo) (hlk : lo ≤ k) : Weak k := by
  intro k' hk' hs; exact h k' (by omega) hs

/-! ### Non-invertibility — Weak holds at the root where Strong fails. -/

/-- At the root the WEAK guard HOLDS (the only seq opener `5` has content successor `6`). -/
theorem weak_at_root : Weak 0 := by intro k _ hs; subst hs; rfl

/-- At the root the STRONG guard FAILS (position `0` is a non-seq opener; its successor `1 ≠ 6`).  So
    there is NO `Weak 0 → Strong 0` upgrade — the membrane cannot be inverted by restriction. -/
theorem not_strong_at_root : ¬ Strong 0 := by
  intro h; exact absurd (h 0 (Nat.zero_le 0)) (by decide)

/-! ### Consequence: at the ROOT SEED only `child_weak` is available; the chain stays weak. -/

/-- The root carries only `Weak` (`weak_at_root`); the only producer it feeds is `child_weak`, yielding a
    WEAK child.  The chain stays in the weak twin family end-to-end. -/
theorem root_child_is_weak : Weak 1 := child_weak weak_at_root (by omega)

/-- The STRONG child producer is UNAVAILABLE at the root: it would need the false `Strong 0`
    (`not_strong_at_root`).  Off the root (with a genuine `Strong` parent in hand) it is fine — the
    vacuity is localized to the seed, exactly as in [[RootSeedNeedsRootTrueGuard]]. -/
theorem strong_child_needs_strong_parent (h : Strong 0) : Strong 1 := child_strong h (by omega)

end RethreadStaysInWeakerTwinFamily
