/-
# Reflection 525 — the head dispatch that LOCATES a witness also PINS its depth, for free

Self-contained companion to the extended `mapPairSkeleton_locate`
(`L4YAML/Proofs/Output/EmitterScannability/NonemptyStructure.lean`).

R524 (`SubblockNonemptyFromClassCollision`) narrowed a map pair into its key/value sub-block windows
and found ONE fact it could not get from the grammar bundle `MapBodyProps`: the depth-`0`-ness of the
value separator, `balance lo kv = 0`.  `MapBodyProps` does not assert it — the successor fields M6/M7/M8
take it as a GUARD, so it cannot be bootstrapped from them.  R524 isolated it as the lone hypothesis
`h_kv_depth` and left it to "the head dispatch".

This reflection discharges it AT ITS SOURCE.  The locator `mapPairSkeleton_locate` already case-splits
on the key's head shape (scalar vs bracket) to PLACE `kv` — and the very same dispatch determines `kv`'s
depth, because the depth is just the telescoped sum of the bracket-deltas of the tokens the dispatch
walked over from `lo`:

  * **scalar key** `kv = lo+2`: the dispatch stepped over a `.key` (delta `0`) and a scalar (delta `0`),
    so `balance lo (lo+2) = balance lo lo + 0 + 0 = 0`.
  * **bracket key** `kv = j+1` for the matching close `j`: the dispatch stepped over a `.key` (delta `0`),
    an opener (`+1`), a balanced interior (the locator's OWN `h_inner_bal : balance (lo+2) j = 0`), and
    the matching close (`-1`), so `balance lo (j+1) = 0 + 1 + 0 + (-1) = 0`.

So the fact a downstream consumer isolates as its lone head-shape-dependent hypothesis is FREE at the
upstream locator that already dispatches on that head shape: the dispatch that PLACES the witness also
PINS the property — recovered by un-discarding binders (`h_close`/`h_inner_bal`) the locator already had
in hand, never by re-deriving anything downstream.  This file proves both telescoping identities in
general and bundles them into a locator that returns BOTH the position `kv` AND its depth `balance lo
kv = 0`, on concrete scalar-key and bracket-key pairs.
-/

namespace DispatchPinsLocatedDepth

set_option autoImplicit false

/-- Toy flow tokens: `ky` key, `sc` scalar, `op`/`cl` brackets, `vl` value, `fe` flowEntry. -/
inductive Tok | ky | sc | op | cl | vl | fe
  deriving DecidableEq

/-- Bracket delta: `op` opens, `cl` closes; every other token is delta-`0`. -/
def delta : Tok → Int
  | .op => 1 | .cl => -1 | _ => 0

def tokAt (l : List Tok) (m : Nat) : Tok := l.getD m .sc

/-- The bracket-delta at position `i` — what the running balance accumulates as it crosses `i`. -/
def deltaAt (l : List Tok) (i : Nat) : Int := delta (tokAt l i)

/-- Prefix balance from the origin, defined by recursion on the position so that the single-step law
    `bal l (n+1) = bal l n + deltaAt l n` is DEFINITIONAL (the toy analog of `flowBracketBalance_single`
    composed with `flowBracketBalance_compose`). -/
def bal (l : List Tok) : Nat → Int
  | 0     => 0
  | n + 1 => bal l n + deltaAt l n

/-- The single-step law, free by `rfl`. -/
theorem bal_succ (l : List Tok) (n : Nat) : bal l (n + 1) = bal l n + deltaAt l n := rfl

/-! ## The two telescoping identities — the depth is the sum of the deltas the dispatch walked over. -/

/-- **Scalar branch.**  The dispatch placed `kv = a+2` after a delta-`0` head and a delta-`0` content,
    so the located separator sits at the SAME depth as the origin.  Mirrors the scalar branch of
    `mapPairSkeleton_locate`, where `.key` and the scalar both carry `flowBracketDelta = 0`. -/
theorem depth_scalar {l : List Tok} {a : Nat}
    (h_key : deltaAt l a = 0) (h_content : deltaAt l (a + 1) = 0) :
    bal l (a + 2) = bal l a := by
  rw [bal_succ, bal_succ, h_key, h_content]; omega

/-- **Bracket branch.**  The dispatch placed `kv = j+1` just past the matching close `j`.  The opener
    raised the depth by `1` and the interior `(a+2, j)` is balanced (`h_interior` packages
    `balance lo (lo+2) = 1` with the locator's own `h_inner_bal`), so `bal l j = bal l a + 1`; the
    matching close then contributes `-1`, returning the separator to the origin depth.  Mirrors the
    bracket branch's `1 + 0 + (-1) = 0` telescope. -/
theorem depth_bracket {l : List Tok} {a j : Nat}
    (h_interior : bal l j = bal l a + 1) (h_close : deltaAt l j = -1) :
    bal l (j + 1) = bal l a := by
  rw [bal_succ, h_interior, h_close]; omega

/-! ## The locator's BUNDLED output — position AND depth, the depth free from the branch dispatch. -/

/-- **Scalar-key locator.**  Returns the value separator `kv = lo+2` together with `bal l kv = 0`,
    the depth conjunct discharged by `depth_scalar` (free).  The toy of `mapPairSkeleton_locate`'s
    scalar branch now bundling the depth fact. -/
theorem locate_scalar {l : List Tok} {lo : Nat}
    (h_key : deltaAt l lo = 0) (h_content : deltaAt l (lo + 1) = 0)
    (h_lo0 : bal l lo = 0) (h_val : tokAt l (lo + 2) = .vl) :
    ∃ kv, tokAt l kv = .vl ∧ bal l kv = 0 :=
  ⟨lo + 2, h_val, by rw [depth_scalar h_key h_content, h_lo0]⟩

/-- **Bracket-key locator.**  Returns `kv = j+1` together with `bal l kv = 0`, the depth conjunct
    discharged by `depth_bracket` (free).  The toy of `mapPairSkeleton_locate`'s bracket branch. -/
theorem locate_bracket {l : List Tok} {lo j : Nat}
    (h_interior : bal l j = bal l lo + 1) (h_close : deltaAt l j = -1)
    (h_lo0 : bal l lo = 0) (h_val : tokAt l (j + 1) = .vl) :
    ∃ kv, tokAt l kv = .vl ∧ bal l kv = 0 :=
  ⟨j + 1, h_val, by rw [depth_bracket h_interior h_close, h_lo0]⟩

/-! ## Concrete witnesses. -/

/-- Scalar-key pair `{ a : b }` as `key, sc, value, sc, fe`.  `kv = 2`. -/
def scalarPair : List Tok := [.ky, .sc, .vl, .sc, .fe]
/-- Bracket-key pair `{ [x] : z }` as `key, [ , x , ] , value, z, fe`.  `kv = j+1 = 4` (close at `j=3`). -/
def bracketPair : List Tok := [.ky, .op, .sc, .cl, .vl, .sc, .fe]

-- scalar: head/content are delta-0, the separator at depth-0.
#guard bal scalarPair 0 == 0
#guard bal scalarPair 2 == 0
#guard tokAt scalarPair 2 == Tok.vl
-- bracket: depth rises to 1 across the opener, the interior `(2,3)` is balanced so `bal l 3 = 1`,
-- the close returns it to 0 at the separator `kv = 4`.
#guard bal bracketPair 3 == 1
#guard deltaAt bracketPair 3 == -1
#guard bal bracketPair 4 == 0
#guard tokAt bracketPair 4 == Tok.vl

/-- Scalar pair: the locator emits `kv = 2` with its depth proved free. -/
theorem scalarPair_located : ∃ kv, tokAt scalarPair kv = .vl ∧ bal scalarPair kv = 0 :=
  locate_scalar (l := scalarPair) (lo := 0) (by decide) (by decide) (by decide) (by decide)
/-- Bracket pair: the locator emits `kv = 4` with its depth proved free (`j = 3`). -/
theorem bracketPair_located : ∃ kv, tokAt bracketPair kv = .vl ∧ bal bracketPair kv = 0 :=
  locate_bracket (l := bracketPair) (lo := 0) (j := 3) (by decide) (by decide) (by decide) (by decide)

/-- The punchline: the scalar locator's depth conjunct is a CONSEQUENCE of the branch dispatch
    (delta-`0` head + delta-`0` content), not a parameter the caller must supply. -/
theorem demo {l : List Tok} {lo : Nat}
    (h_key : deltaAt l lo = 0) (h_content : deltaAt l (lo + 1) = 0)
    (h_lo0 : bal l lo = 0) (h_val : tokAt l (lo + 2) = .vl) :
    ∃ kv, tokAt l kv = .vl ∧ bal l kv = 0 :=
  locate_scalar h_key h_content h_lo0 h_val

end DispatchPinsLocatedDepth

/-- info: 'DispatchPinsLocatedDepth.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DispatchPinsLocatedDepth.demo
