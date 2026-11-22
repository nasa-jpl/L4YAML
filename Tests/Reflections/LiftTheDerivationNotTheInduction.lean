/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 671 — lift the derivation, not the induction

**The rule.**  When a reading at a GENERIC index is needed and the only
producer is a deep induction concluding at one index, look at the
constructors that cover your case before generalizing the producer: if they
bind the index without constraining it, the general reading is the pinned
DERIVATION re-tagged — one `cases`, no new induction — and the cases they do
not cover come back as a located witness instead of a generalized proof.  The
price difference is the whole induction: the producer, its loop lemmas, and
every consumer of their statements stay untouched at the pinned index.

**The instance** (item 45).  The scalar `_prod` chains
(`collectDoubleQuotedLoop_prod`, `foldQuotedNewlines_prod`, the plain-scalar
loop) conclude at 0 through hundreds of lines of scan-loop induction — but
`[116] nb-double-multi-line(n)`'s `single` constructor takes `n` and uses it
nowhere: a single-line body at 0 IS a single-line body at every `n`.  So
`SCDoubleQuoted_at` cases the 0-derivation, re-tags `single`, and returns
`multi` as `DoubleQuotedCrossed` — the first line's own content and the break,
in the constructor's own fields — for the consumer to collapse on.  The same
move serves single-quoted and plain scalars; only plain keeps its CONTEXT,
because `[127] ns-plain-safe(c)` makes its characters context-sensitive while
the quoted body classes are context-free.

Contrast [[ReindexPriceIsTheSignatures]]: there the index was a PARAMETER the
constructions never mention, so generalizing cost signatures only; here the
index is constrained by SOME constructors (`multi`'s line prefixes), so full
generalization would cost the induction — and the lift buys everything the
uncovered constructors don't touch, for a `cases`.

§1 the toy: a two-constructor reading with the index constrained only in
`multi`.  §2 the deep producer at 0, and the lift.  §3 what the lift cannot
do — the `multi` case genuinely needs the index — pinned by refutation.
-/

namespace L4YAML.Tests.Reflections.LiftTheDerivationNotTheInduction

/-- A line prefix at index `n` (toy `s-indent(n)`): the constraint that makes
    multi-line readings index-sensitive. -/
def Prefix' (n : Nat) : Prop := n ≤ 2

instance (n : Nat) : Decidable (Prefix' n) := inferInstanceAs (Decidable (n ≤ 2))

/-- A scalar body reading at `n`: one line (index bound, unused), or a
    continuation line whose prefix must satisfy the index. -/
inductive Body (n : Nat) : Type where
  | oneLine (text : String) : Body n
  | multi (text : String) (rest : String) (h : Prefix' n) : Body n

/-- The deep producer, standing in for a scan-loop induction: it concludes at
    0 and nobody wants to re-prove it at `n`. -/
def scanBody (text : String) : Body 0 :=
  if text.length ≤ 3 then .oneLine text else .multi text "" (by decide)

/-! ## §2  The lift: one `cases`, no new induction -/

/-- The crossing, located in the constructor's own fields. -/
def Crossed : Prop := True

/-- The lift: re-tag `oneLine`, return `multi` as the witness.  The producer
    and its induction are not touched. -/
def Body.at (n : Nat) : Body 0 → Body n ⊕ PLift Crossed
  | .oneLine text => .inl (.oneLine text)
  | .multi _ _ _ => .inr ⟨trivial⟩

/-- The lift preserves the content it lifts — nothing is re-derived. -/
example (t : String) (h : t.length ≤ 3) :
    (scanBody t).at 5 = .inl (.oneLine t) := by
  simp [scanBody, Body.at, h]

/-! ## §3  The boundary: `multi` genuinely needs the index -/

/-- A multi-line body at 5 cannot exist at all — its prefix constraint fails —
    so no lift could produce one: the witness branch is not a shortcut, it is
    the only honest answer. -/
example (b : Body 5) : ∃ t, b = .oneLine t := by
  cases b with
  | oneLine t => exact ⟨t, rfl⟩
  | multi _ _ h => exact absurd h (by decide)

end L4YAML.Tests.Reflections.LiftTheDerivationNotTheInduction

end Blanket
