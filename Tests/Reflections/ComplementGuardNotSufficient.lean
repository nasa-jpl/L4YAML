/-!
# Reflection 333 — the COMPLEMENT of a sufficient dispatch guard need not be a sufficient guard

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind `recseqbody_descend`,
the DESCEND arm of the nested-`RecSeqBody` projection recursion.

A spine-walk recursion splits into arms by where a located opener `p` sits relative to the body's
head entry `e` (span `[lo, lo + e.length)`):

* **ADVANCE** — `p` is PAST the head entry. Guard `bal lo p = 0 ∧ lo < p` is SUFFICIENT for this:
  the head entry's interior never returns to balance `0` strictly inside (a single bracket pair),
  so a top-level `0` at `p > lo` forces `p ≥ lo + e.length`.
* **DESCEND** — `p` is strictly INSIDE the head entry.

The trap: authoring DESCEND by NEGATING the ADVANCE guard — `bal lo p ≥ 1` — is UNSOUND. The negation
is floor-blind: `p` can be nested inside a LATER entry of the body and still have `bal lo p ≥ 1`
(the head balances back to `0`, then a later entry re-opens). The real DESCEND guard is the
window-absolute FLOOR `∀ i ∈ (lo, p], bal lo i ≥ 1`, which forbids the return-to-`0` and so pins `p`
strictly inside the HEAD bracket.

A SECOND, independent finding: the head being a `.seq` (vs a `.map`) is provably NOT a balance fact —
both openers have delta `+1` — so it cannot be derived; it is a dispatch hypothesis the caller
supplies.

The witness is the body `1 , [ [ 2 ] ]` (the interior of `[1, [[2]]]`): a SCALAR head entry `1`
(span `[0, 1)`), a separator, then a doubly-nested seq second entry. Position `p = 3` (the inner
`[`) has `bal 0 3 = 1 ≥ 1` yet is PAST the head — the negation admits it; the floor rejects it.
-/

namespace Tests.Reflections.ComplementGuardNotSufficient

set_option autoImplicit false

/-- Toy token alphabet: seq opener/closer, a scalar, and a DISTINCT map opener (same `+1` delta as
    the seq opener — so the balance cannot tell them apart). -/
inductive Tok | op | cl | ct | comma | mop
  deriving DecidableEq, Repr, Inhabited

/-- Bracket delta: any opener `+1`, the closer `-1`, content/separator `0`. -/
def delta : Tok → Int
  | .op | .mop => 1
  | .cl => -1
  | _ => 0

/-- The witness body `1 , [ [ 2 ] ]` (interior of `[1, [[2]]]`) as an indexed stream.
    Head entry `1` is the lone `ct` at index `0`, span `[0, 1)`. -/
def tok : Nat → Tok
  | 0 => .ct       -- `1`   the SCALAR head entry, span [0,1)
  | 1 => .comma    -- `,`   separator
  | 2 => .op       -- `[`   second entry opens
  | 3 => .op       -- `[`   inner seq opener  ← located `p`
  | 4 => .ct       -- `2`
  | 5 => .cl       -- `]`
  | 6 => .cl       -- `]`
  | _ => .cl

/-- Prefix balance from `0` to `m`. -/
def balAux : Nat → Int
  | 0       => 0
  | (m + 1) => balAux m + delta (tok m)

/-- Window balance from `lo` to `m` as a prefix difference. -/
def bal (lo m : Nat) : Int := balAux m - balAux lo

/-- The head entry `1` ends at index `1` (`lo = 0`, `e.length = 1`). -/
def headEnd : Nat := 1

/-! ## NEGATIVE — `bal lo p ≥ 1` is NOT sufficient for "p inside the head entry"

`p = 3` (the inner `[`) has `bal 0 3 ≥ 1`, so the NAIVE negated guard fires — yet `p = 3` is PAST
the head entry (which ends at `headEnd = 1`). The window-absolute FLOOR correctly REJECTS it: the
balance returns to `0` at `i = 1` (the scalar head), so `bal 0 1 = 0 < 1`. -/

-- The naive negated guard `bal 0 3 ≥ 1` is satisfied…
example : decide (bal 0 3 ≥ 1) = true := by decide
#guard decide (bal 0 3 ≥ 1) = true

-- …yet `p = 3` is PAST the head entry — the negation admits a position the DESCEND arm cannot serve.
#guard decide (3 ≥ headEnd) = true

-- The FLOOR `∀ i ∈ (0, 3], bal 0 i ≥ 1` FAILS — at `i = 1` (the head's end) the balance is `0`,
-- so the floor is the discriminator the bare `≥ 1` lacks.
#guard bal 0 1 = 0
#guard decide (bal 0 1 ≥ 1) = false

/-! ## NEGATIVE — head-is-`.seq` is NOT a balance fact (the seq/map opener delta collision)

A `.seq` opener and a `.map` opener carry the SAME `+1` delta, so no balance/floor predicate can
distinguish them. Head-is-`.seq` must therefore be a DISPATCH HYPOTHESIS, not a derivation. -/

#guard delta .op = delta .mop          -- both `+1` — balance is blind to seq-vs-map
#guard decide (delta .op = 1) = true
#guard decide (delta .mop = 1) = true

/-! ## POSITIVE — the FLOOR pins `p` strictly inside the head bracket (proven)

The crux of `recseqbody_descend`'s `h_p_lt`, stated abstractly over any `bal`: if the head entry
balances to `0` at its end `m` (`bal lo m = 0`, with `lo < m`) and the FLOOR holds over `(lo, p]`,
then `p < m`. The floor instance at `i = m` would force `bal lo m ≥ 1`, contradicting `= 0`. -/

theorem floor_implies_in_head
    (B : Nat → Int) (lo m p : Nat)
    (h_lo_m : lo < m) (h_head_bal : B m = 0)
    (h_floor : ∀ i, lo < i → i ≤ p → B i ≥ 1) :
    p < m := by
  rcases Nat.lt_or_ge p m with h | h
  · exact h
  · exact absurd (h_floor m h_lo_m h) (by rw [h_head_bal]; decide)

/-- Applied to the witness with the head end `m = headEnd = 1`: ANY `p` whose floor holds is `< 1`,
    i.e. there is no nested `p` inside a length-`1` scalar head — the floor correctly rules DESCEND
    out for this body (forcing the driver to ADVANCE past the scalar instead). -/
example (p : Nat) (h_floor : ∀ i, 0 < i → i ≤ p → bal 0 i ≥ 1) : p < 1 :=
  floor_implies_in_head (bal 0) 0 1 p (by decide) (by decide) h_floor

end Tests.Reflections.ComplementGuardNotSufficient
