/-
# Reflection 540 — a separator fact threaded through a SUBSET-RESTRICTION carrier must be
BOUNDARY-ROBUST: its conclusion may CONSTRAIN the boundary token but must not REQUIRE the
successor to lie STRICTLY INSIDE the window. A fact of the *fragile* shape
`trigger k → k + 1 < b ∧ P (k+1)` is FALSE at the window that ends one past the trigger
(`b = k+1`), so it cannot be carried over arbitrary sub-windows — even though that window is a
perfectly good gated interior. The *robust* shape `trigger k → k + 1 = b ∨ P (k+1)` survives,
because the `k + 1 = b` disjunct fires exactly at that cut.

## Why this matters — the map separator carrier is UNPROVABLE as defined

The seq separator carrier `SeqInteriorSeparators tokens lo hi`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean:96`) is

    ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → SeqTypedInterior tokens a b →
      bodySuccFact tokens a b ∧ noTrailingSepFact tokens a b

and it IS constructed (`seqRoot_seqInteriorSeparators:2127`) because `bodySuccFact`
(`k+1 = b ∨ ∃ following entry`) and `noTrailingSepFact` (`isFlowContentStart tokens[k+1]`, a
fact about the boundary token, NOT a strict-interior demand) are both boundary-robust.

The map carrier `MapInteriorSeparators tokens lo hi` (`:187`) copies the *shape* —

    ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → MapTypedInterior tokens a b → MapGrammarFacts tokens a b

— but `MapGrammarFacts` (`:166`) is boundary-FRAGILE: conjuncts 1/2/3/5 conclude
`k + 1 < b ∧ …` / `k + 2 < b ∧ …` (the `.key`/`.value` marker's content must be strictly inside),
and conjuncts 4/6 conclude `k + 2 ≤ b ∧ (… ∨ (mapEnd ∧ k+2 = b))` — every one references a token at
or past the window edge and demands it sit inside. Because `flowBracketDelta .key = 0` and
`flowBracketDelta .value = 0` (`ParserGrammableBase.lean:506`), a window can END right after a
`.key`/`.value` marker at balance 0, and there the fragile conjunct's `k+1 < b` is `b < b` — FALSE.

**Verified against the real defs** on the stream `{a: 1}` =
`#[ {, .key, scalar a, .value, scalar 1, } ]` (positions 0..5). The mid-key-cut window `[1,2)`
covering only the `.key` marker satisfies `MapTypedInterior toks 1 2` (balance 0, `btFold`-top
`some false`, floor ≥ 0) yet refutes `MapGrammarFacts toks 1 2` (conjunct 1 at `k=1` forces
`2 < 2`). Since `[1,2) ⊆ [1,5)` and `[1,5)` is the genuine outer map body,
`MapInteriorSeparators toks 1 5` is FALSE. The carrier is only ever *assumed* (`h_carrier`), never
constructed — which is exactly why the falsity never surfaced
([[ref-probe-deferred-universal-before-producing]]: a target you only PROJECT hides its own
falsity). The map ASSEMBLE half (building `mapRoot_mapInteriorSeparators` toward this carrier) was
aimed at an unprovable target.

**The fix** (next step, NOT done here): land a boundary-ROBUST `MapGrammarFacts'` as a NEW additive
parallel type ([[ref-additive-parallel-type-over-shared-edit]]) — each conjunct gains a `k+i = b`
window-close escape exactly as the seq facts have — and rebuild the carrier on it; the genuine-window
consumers (`mapGrammarFacts_of_mapRoot`, which queries only the full body `b = hi`) recover the strict
form because at a real map body the marker's content is genuinely interior.

This file isolates the principle abstractly: the robust fact REBASES to sub-windows (the seq
`bodySuccFact_rebase` mechanism), the fragile fact does NOT.
-/

namespace BoundaryRobustVsFragileFact

/-- A separator/marker fires at positions `trig`; the followed content satisfies `P`.
    FRAGILE conclusion — the successor must lie STRICTLY inside `[a,b)`. The map
    `MapGrammarFacts` conjunct-1 shape. -/
def FragileFact (trig P : Nat → Prop) (a b : Nat) : Prop :=
  ∀ k, a ≤ k → k < b → trig k → k + 1 < b ∧ P (k + 1)

/-- ROBUST conclusion — a window-close escape disjunct. The seq `bodySuccFact` shape. -/
def RobustFact (trig P : Nat → Prop) (a b : Nat) : Prop :=
  ∀ k, a ≤ k → k < b → trig k → k + 1 = b ∨ P (k + 1)

/-! ### The cut that separates them — a window ending one past a single trigger at `k = 1`. -/

/-- The FRAGILE fact is FALSE at the boundary-cut window `[1,2)`: a trigger at `k=1` would force
    `1 + 1 < 2`. This is the abstract twin of `¬ MapGrammarFacts toks 1 2`. -/
example (P : Nat → Prop) : ¬ FragileFact (· = 1) P 1 2 := by
  intro h
  have hk : (1 : Nat) + 1 < 2 := (h 1 (Nat.le_refl 1) (by decide) rfl).1
  omega

/-- The ROBUST fact SURVIVES the same cut: the `k+1 = b` disjunct fires. This is why the seq carrier
    tolerates the very sub-window that breaks the map carrier. -/
example (P : Nat → Prop) : RobustFact (· = 1) P 1 2 := by
  intro k _ _ htrig
  have hk1 : k = 1 := htrig
  exact Or.inl (by omega)

/-! ### The rebase asymmetry — the carrier mechanism (`SeqInteriorSeparators_narrow` /
    `bodySuccFact_rebase`) works for the robust fact and provably fails for the fragile one. -/

/-- **The robust fact REBASES to any sub-window** — the abstract `bodySuccFact_rebase` (`:1940`):
    the enclosing window's close disjunct `k+1 = hiS` collapses to `k+1 = b` because `k < b ≤ hiS`.
    (The real lemma additionally reseats the depth premise via `flowBracketBalance_compose`; that is
    orthogonal to the boundary robustness this file isolates.) -/
theorem robustFact_rebase (trig P : Nat → Prop) (loS a b hiS : Nat)
    (h_loS_a : loS ≤ a) (h_b_hiS : b ≤ hiS)
    (h : RobustFact trig P loS hiS) : RobustFact trig P a b := by
  intro k hak hkb htrig
  rcases h k (Nat.le_trans h_loS_a hak) (by omega) htrig with heq | hp
  · exact Or.inl (by omega)
  · exact Or.inr hp

/-- **The fragile fact does NOT rebase** — there is no analogue of `robustFact_rebase` for the
    fragile shape. Concrete refutation: the enclosing `[1,5)` satisfies the fragile fact (the trigger
    at `k=1` has its content strictly inside, `2 < 5`), but the sub-window `[1,2) ⊆ [1,5)` does not —
    exactly the `MapInteriorSeparators toks 1 5 → MapGrammarFacts toks 1 2` step that fails. -/
example :
    ¬ (∀ (trig P : Nat → Prop) (loS a b hiS : Nat),
        loS ≤ a → b ≤ hiS → FragileFact trig P loS hiS → FragileFact trig P a b) := by
  intro hrebase
  have henc : FragileFact (· = 1) (· = 2) 1 5 := by
    intro k _ _ htrig
    have hk1 : k = 1 := htrig
    exact ⟨by omega, by omega⟩
  have hsub : FragileFact (· = 1) (· = 2) 1 2 :=
    hrebase _ _ 1 1 2 5 (Nat.le_refl 1) (by omega) henc
  have hbad : (1 : Nat) + 1 < 2 := (hsub 1 (Nat.le_refl 1) (by decide) rfl).1
  omega

-- Axiom audit — the robust rebase is the only positive content; it leans only on core.
/-- info: 'BoundaryRobustVsFragileFact.robustFact_rebase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BoundaryRobustVsFragileFact.robustFact_rebase

/-! ### The general discipline this instance teaches — INHABITATION DEBT
    ([[ref-inhabitation-debt-validate-target-defs]])

A `def P : Prop` you intend to CONSTRUCT is validated by type-checking only as well-formed, never
as TRUE. It carries *inhabitation debt* until a closed witness proves it. Over decidable data a
`decide` probe at the BOUNDARY of the universal catches a fragile definition in one line — the cost
of NOT probing it at definition time is pure negligence. Below: two toy carriers (the fragile/robust
shapes again, now over a DECIDABLE bounded `∀`), and the one-line boundary probe that would have
caught the real bug the moment `MapInteriorSeparators` was defined. -/

-- `abbrev` (reducible) so `decide` can see the bounded-`∀` shape and synthesize `Nat.decidableBallLT`.
/-- A toy fragile carrier — a successor must lie strictly inside `[0,b)`. Decidable (bounded `∀`). -/
abbrev ToyFragile (b : Nat) : Prop := ∀ k, k < b → k = 1 → k + 1 < b
/-- A toy robust carrier — same trigger, with a `k+1 = b` window-close escape. -/
abbrev ToyRobust (b : Nat) : Prop := ∀ k, k < b → k = 1 → k + 1 = b ∨ k + 1 < b

-- The boundary probe at `b = 2` (the window ending one past the trigger at `k = 1`):
-- the fragile carrier is FALSE, the robust carrier is TRUE — one `decide` each, owed at birth.
example : ¬ ToyFragile 2 := by decide
example : ToyRobust 2 := by decide
-- (Probing the comfortable INTERIOR, `b = 9`, hides the bug — both pass. Probe the EDGE.)
example : ToyFragile 9 := by decide
example : ToyRobust 9 := by decide

end BoundaryRobustVsFragileFact
