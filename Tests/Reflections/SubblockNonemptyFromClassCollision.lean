/-
# Reflection 524 — a sub-block's NON-emptiness is a token-CLASS collision, not a balance fact

Self-contained companion to `mapPairSubblocks_flowBodyWindow`
(`L4YAML/Proofs/Output/EmitterScannability/NonemptyStructure.lean`).

When a width-recursion driver narrows a composite node (a map pair `.key K .value V`) into its
sub-block windows — the key `[lo+1, kv)` and the value `[kv+1, e)` — it must show each sub-block is
NON-empty before it can package it as a `FlowBodyWindow` and hand it to a `RecSeqEntry` oracle.  The
reusable finding: that non-emptiness is NOT a balance computation.  It falls straight out of a grammar
SUCCESSOR field that asserts a *content-start* token at the sub-block's first position, colliding with
the structural token (a `.value` separator, or a `.flowEntry`/window-end marker) that sits at the
position a collapse would identify it with.  The two token CLASSES are disjoint, so the collapse is
impossible — no depth is ever measured.

A second, head-shape-FREE move accompanies it: because the split points (`.key`/`.value` separators)
carry bracket-delta `0`, they sit at depth `0`, and the sub-block's running balance equals the outer
one re-based to the same origin — so the outer Dyck floor transports to each sub-block verbatim.  The
ONE head-shape-dependent fact (that the value separator `kv` is at depth `0`, i.e. `bal lo kv = 0`) is
isolated as a single hypothesis the head dispatch supplies; everything in the narrowing is then
shape-free.  This file proves the collision principle in general and witnesses the depth-`0` re-basing
on concrete scalar-key and bracket-key map pairs.
-/

namespace SubblockNonemptyFromClassCollision

set_option autoImplicit false

/-- Toy flow tokens: the content-start CLASS (`sc` scalar, `op`/`cl` brackets) versus structural
    separators/markers (`ky` key, `vl` value, `fe` flowEntry).  Mirrors the split in `isFlowContentStart`
    (a content node head) versus the `.key`/`.value`/`.flowEntry` structural tokens. -/
inductive Tok | sc | op | cl | ky | vl | fe
  deriving DecidableEq

/-- The content-start class (mirrors `isFlowContentStart`: a scalar or an opening bracket). -/
def isContentStart : Tok → Prop
  | .sc => True
  | .op => True
  | _   => False

/-- Bracket delta: `op` opens, `cl` closes; every structural token (`ky`, `vl`, `fe`) is delta-`0`. -/
def delta : Tok → Int
  | .op => 1 | .cl => -1 | _ => 0

def tokAt (l : List Tok) (m : Nat) : Tok := l.getD m .sc

/-- Prefix balance from `0` — the depth at position `n` measured from the outer origin. -/
def bal (l : List Tok) (n : Nat) : Int := ((l.take n).map delta).foldl (· + ·) 0

/-! ## Move 1 — non-emptiness is a token-CLASS collision (the novel principle).

`.vl` and `.fe` are not in the content-start class.  So a content-start at `a` can never coincide with
a `.vl`/`.fe` at `b`: if `a ≤ b` then `a < b`.  Zero balance is touched. -/

theorem vl_not_contentStart : ¬ isContentStart .vl := by unfold isContentStart; exact not_false
theorem fe_not_contentStart : ¬ isContentStart .fe := by unfold isContentStart; exact not_false

/-- **KEY block non-empty.**  A grammar field (the analog of M3 `key_content`) puts a content-start at
    `a = lo+1`; the located value separator sits at `b = kv` carrying `.vl`.  The classes are disjoint,
    so `a < b`.  This is exactly the `lo+1 < kv` step of `mapPairSubblocks_flowBodyWindow`. -/
theorem key_nonempty {l : List Tok} {a b : Nat}
    (h_cs : isContentStart (tokAt l a)) (h_val : tokAt l b = .vl) (h_le : a ≤ b) : a < b := by
  rcases Nat.lt_or_ge a b with h | h
  · exact h
  · exfalso; have h_eq : a = b := by omega
    rw [h_eq, h_val] at h_cs; exact vl_not_contentStart h_cs

/-- **VALUE block non-empty.**  A grammar field (the analog of M6 `value_content`) puts a content-start
    at `a = kv+1`; the located pair end `b = e` is a marker.  Here only the `.fe` horn is a class
    collision — the `b = window-end` horn is closed separately by the successor field's own in-bounds
    clause (M6's `kv+1 < hi`), modeled here by the explicit `h_lt` premise that makes `a = b` absurd. -/
theorem val_nonempty {l : List Tok} {a b : Nat}
    (h_cs : isContentStart (tokAt l a)) (h_marker : tokAt l b = .fe ∨ a < b) (h_le : a ≤ b) : a < b := by
  rcases h_marker with h_fe | h_lt
  · rcases Nat.lt_or_ge a b with h | h
    · exact h
    · exfalso; have h_eq : a = b := by omega
      rw [h_eq, h_fe] at h_cs; exact fe_not_contentStart h_cs
  · exact h_lt

/-! ## Move 2 — the split points sit at depth `0`, so the outer floor re-bases verbatim.

The `.key`/`.value` separators are delta-`0`, so on a well-formed pair the running balance returns to
`0` at `lo`, `kv`, and `e`.  The ONE head-shape-dependent fact is `bal lo kv = 0` (here `lo = 0`); once
it holds, the sub-block floors equal the outer floor.  We witness this on concrete pairs, including a
bracketed key whose INTERIOR `.fe` sits at depth `1` (NOT a depth-`0` marker — which is why it does not
split the pair). -/

/-- Scalar-key pair `{ a : b }` as `key, sc, value, sc, fe`. -/
def scalarPair : List Tok := [.ky, .sc, .vl, .sc, .fe]
/-- Bracket-key pair `{ [x, y] : z }` as `key, [ , x , , , y , ] , value, z, fe`. -/
def bracketPair : List Tok := [.ky, .op, .sc, .fe, .sc, .cl, .vl, .sc, .fe]

-- scalar key: value separator `kv = 2` and pair end `e = 4` are both at depth `0`.
#guard bal scalarPair 0 == 0
#guard bal scalarPair 2 == 0
#guard bal scalarPair 4 == 0
#guard tokAt scalarPair 2 == Tok.vl
#guard tokAt scalarPair 4 == Tok.fe

-- bracket key: value separator `kv = 6` is at depth `0` (the matching `]` returns the balance) ...
#guard bal bracketPair 6 == 0
#guard bal bracketPair 8 == 0
-- ... but the key's INTERIOR `.fe` at index 3 sits at depth `1` — invisible to the depth-`0` split.
#guard bal bracketPair 3 == 1
#guard tokAt bracketPair 3 == Tok.fe
#guard tokAt bracketPair 6 == Tok.vl

/-! ## The two narrowings, on the concrete witnesses. -/

/-- Scalar pair: key block `[1, 2)` non-empty by the class collision (`sc` at 1 vs `vl` at 2). -/
theorem scalarPair_key_nonempty : (1 : Nat) < 2 :=
  key_nonempty (l := scalarPair) True.intro (by decide) (by decide)
/-- Scalar pair: value block `[3, 4)` non-empty (`sc` at 3 vs `fe` at 4). -/
theorem scalarPair_val_nonempty : (3 : Nat) < 4 :=
  val_nonempty (l := scalarPair) True.intro (Or.inl (by decide)) (by decide)
/-- Bracket pair: key block `[1, 6)` non-empty (`op` at 1 — a content-start — vs `vl` at 6). -/
theorem bracketPair_key_nonempty : (1 : Nat) < 6 :=
  key_nonempty (l := bracketPair) True.intro (by decide) (by decide)

/-- The punchline: the general collision principle, instantiated to the key-block step. -/
theorem demo {l : List Tok} {a b : Nat}
    (h_cs : isContentStart (tokAt l a)) (h_val : tokAt l b = .vl) (h_le : a ≤ b) : a < b :=
  key_nonempty h_cs h_val h_le

end SubblockNonemptyFromClassCollision

/-- info: 'SubblockNonemptyFromClassCollision.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SubblockNonemptyFromClassCollision.demo
