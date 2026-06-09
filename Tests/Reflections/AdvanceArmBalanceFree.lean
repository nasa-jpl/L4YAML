/-!
# Reflection 334 — the GENERAL ADVANCE arm is BALANCE-FREE once the caller supplies the decomposition

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`recseqbody_advance_general`, the balance-free GENERAL ADVANCE arm of the nested-`RecSeqBody`
projection recursion.

A spine-walk recursion advances a located opener `p` PAST the body's head entry `e`. The R332 arm
`recseqbody_advance` guarded this with a BALANCE fact (`bal lo p = 0`) and spent the bulk of its
proof USING that balance to RECONSTRUCT the structural fact `p ≥ lo + e.length`. R333 found the
balance guard incomplete (it misses a `p` nested in a LATER entry: `bal lo p ≥ 1`).

The R334 finding: the balance was never intrinsic to *advancing*. The CALLER (the driver) already
extracts the head entry and dispatches on `p ≥ lo + e.length`, so in the advance branch it already
HOLDS that inequality AND the `cons` decomposition `body = head ++ sep :: rest`. Pass those DOWN as
hypotheses and the balance machinery EVAPORATES — the arm becomes pure slice algebra plus one
opener-vs-separator inequality. The guard was the callee's way of reconstructing structure the
caller has for free.

The witness is the body `1 , [ [ 2 ] ]` (interior of `[1, [[2]]]`): a SCALAR head entry `1`
(span `[0, 1)`, `headEnd = 1`), a separator, then a doubly-nested seq second entry. Position
`p = 3` (the inner `[`) has `bal 0 3 = 1 ≠ 0` (balance route cannot advance) yet `p ≥ headEnd`
(structural route can).
-/

namespace Tests.Reflections.AdvanceArmBalanceFree

set_option autoImplicit false

/-- Toy token alphabet (as in Reflection 333): seq opener/closer, a scalar, a separator. -/
inductive Tok | op | cl | ct | comma | mop
  deriving DecidableEq, Repr, Inhabited

/-- Bracket delta: any opener `+1`, the closer `-1`, content/separator `0`. -/
def delta : Tok → Int
  | .op | .mop => 1
  | .cl => -1
  | _ => 0

/-- The witness body `1 , [ [ 2 ] ]` (interior of `[1, [[2]]]`) as an indexed stream.
    Head entry `1` is the lone `ct` at index `0`, span `[0, 1)`; the separator `,` is at index `1`. -/
def tok : Nat → Tok
  | 0 => .ct       -- `1`   the SCALAR head entry, span [0,1)
  | 1 => .comma    -- `,`   separator at `headEnd`
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

/-! ## NEGATIVE — the BALANCE guard `bal 0 p = 0` is incomplete; the STRUCTURAL bound `p ≥ headEnd` is not

At `p = 3` (the inner `[`, nested inside the SECOND entry) the balance is `bal 0 3 = 1 ≠ 0`, so the
R332 balance-`0` guard does NOT fire — yet `p = 3 ≥ headEnd = 1`, so `p` IS past the head entry and
the GENERAL ADVANCE arm should serve it.  The balance route cannot advance here; the structural
route can.  This is exactly the nested-in-a-later-entry case R333 flagged. -/

-- The balance guard `bal 0 3 = 0` is FALSE (it is `1`) — the balance route cannot advance past the head.
#guard bal 0 3 = 1
#guard decide (bal 0 3 = 0) = false

-- …yet the STRUCTURAL past-head bound the caller hands the arm DOES hold.
#guard decide (3 ≥ headEnd) = true

-- The opener and separator deltas COLLIDE in sign-of-balance but the TOKENS differ — so the one
-- positional fact the arm needs (`p ≠ headEnd`) is a constructor inequality, not a balance fact.
#guard decide (tok headEnd = .comma) = true        -- separator at headEnd is a `,`
#guard decide (tok 3 = .op) = true                  -- located opener at p is a `[`
#guard decide (tok headEnd ≠ tok 3) = true          -- distinct tokens ⇒ p ≠ headEnd

/-! ## POSITIVE — the BALANCE-FREE re-base (proven)

The crux of `recseqbody_advance_general`: GIVEN the head's `cons` decomposition
`body = head ++ sep :: rest` (which the caller already has), re-basing past the head entry and its
separator is PURE slice algebra — no balance, no floor, no `pbalance` bridge.  `body.drop (headLen
+ 1) = rest`. -/

theorem advance_rebase {α : Type} (head rest : List α) (sep : α) (headLen : Nat)
    (h_headLen : head.length = headLen) :
    (head ++ sep :: rest).drop (headLen + 1) = rest := by
  subst h_headLen
  simp [List.drop_append]

/-! ## POSITIVE — the ONE positional obligation is a constructor inequality (proven)

The only fact the arm cannot read off the decomposition is `lo + e.length ≠ p` — and it is a
TOKEN-distinctness fact (the separator is a `.flowEntry`, `p` is a `.flowSequenceStart`), NOT a
balance fact.  Abstractly: if the token at `headLen` is `sep` and at `p` is `opener` with `sep ≠
opener`, then `p ≠ headLen`. -/

theorem sep_ne_opener {α : Type} (body : List α) (sep opener : α) (headLen p : Nat)
    (h_sep : body[headLen]? = some sep) (h_op : body[p]? = some opener)
    (h_ne : sep ≠ opener) : p ≠ headLen := by
  intro h
  subst h
  rw [h_sep] at h_op
  exact h_ne (Option.some.inj h_op)

/-- Applied to the witness: `headEnd = 1` holds the separator `,`, `p = 3` holds the opener `[`,
    they differ, so `p ≠ headEnd` — the arm advances with `lo' = headEnd + 1 ≤ p`. -/
example : (3 : Nat) ≠ headEnd :=
  sep_ne_opener [Tok.ct, Tok.comma, Tok.op, Tok.op, Tok.ct, Tok.cl, Tok.cl]
    Tok.comma Tok.op headEnd 3 (by decide) (by decide) (by decide)

end Tests.Reflections.AdvanceArmBalanceFree
