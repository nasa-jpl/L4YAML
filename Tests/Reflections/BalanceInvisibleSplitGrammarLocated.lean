/-! # Reflection 523 — a balance-invisible split point is grammar-located, and the "it precedes the
    boundary" proof bifurcates by head shape

The L4YAML map locate recursion needs, for the first key/value pair of a body window `[lo, hi)`, the
*skeleton* `∃ kv e, …` pinning the depth-`0` value separator `kv` and the pair end `e`.  R282/R284
flagged that `kv` cannot be found by a balance locator — a pair `.key K .value V` returns balance to
`0` at the depth-`0` `.value`, but ALSO at every nested-entry end inside `K` and `V`, so the `.value`
position is *balance-invisible* — and so the no-interior-boundary fact was SUPPLIED.  R523
(`mapPairSkeleton_locate`) now PRODUCES the skeleton from the per-window grammar bundle
`MapBodyProps`, and the lesson is two-fold:

* **Balance-invisibility blocks a balance LOCATOR, not the location.**  The value separator `kv` is
  read off the typed grammar instead: the `.key` head (M1) + content-start at `lo+1` (M3), dispatched
  by shape into M4 (scalar key ⟹ `kv = lo+2`) or M5 (bracket key ⟹ `kv = j+1` for the matching close).
  The pair end `e` is the SHARED half — the least depth-`0` marker, from the axis-agnostic
  `firstEntryBoundary`.

* **The crux `kv < e` — that the value separator precedes the first boundary — has a proof cost that
  BIFURCATES by the key's head shape.**  Both branches rule out a marker in `(lo, kv]`.  For a FLAT
  (scalar) key the two interior positions fall to *token identity alone* (`lo+1` is a scalar, `kv` is
  the `.value`; neither is a `.flowEntry`, neither is `hi`) — NO balance reasoning.  For a NESTED
  (bracket) key the bracket interior is genuinely depth-positive, so `lo+2 ≤ k ≤ j` is ruled out by the
  interior-positivity invariant (`bal lo k ≥ 1 ≠ 0`) — one balance step the flat case never pays;
  endpoints still fall to token identity.

This file models both with a toy `List Tok` stream and prefix-balance `bal`.  The two `*_clean`
theorems are the per-shape no-marker lemmas; note `scalar_clean` takes NO positivity hypothesis while
`bracket_clean` takes and CONSUMES one — the bifurcation made textual.  The two `kv_lt_e_*` theorems
are the crux, deriving `kv < e` from the clean lemma plus `e` being a marker.  Concrete `bk`/`sk`
streams witness the balance-invisibility (`bal` returns to `0` at several positions, only the token
distinguishing `kv`).  `demo := kv_lt_e_scalar` is the headline: a split point provably *preceding* a
boundary with zero balance reasoning when the head is flat.

Self-contained core Lean (no imports).
-/

namespace BalanceInvisibleSplitGrammarLocated

set_option autoImplicit false

/-- Toy token alphabet: `.sc` scalar, `.ky`/`.vl` the depth-`0` pair markers (`.key`/`.value`),
    `.op`/`.cl` one bracket kind, `.fe` the body separator (`.flowEntry`). -/
inductive Tok | sc | ky | vl | op | cl | fe
deriving DecidableEq

/-- Bracket delta — `+1` open, `-1` close, `0` otherwise.  The pair markers `ky`/`vl` and the
    separator `fe` all have delta `0`, so they mark a boundary only *at depth 0* — which is exactly why
    `vl` is balance-invisible (balance cannot tell it from any other depth-`0` token). -/
def delta : Tok → Int
  | .op => 1
  | .cl => -1
  | _   => 0

/-- Running bracket balance over the prefix `[0, n)` (toy of `flowBracketBalance tokens 0 n`). -/
def bal (l : List Tok) (n : Nat) : Int := ((l.take n).map delta).foldl (· + ·) 0

/-- Total token at index `m` (scalar default out of range), so predicates are total. -/
def tokAt (l : List Tok) (m : Nat) : Tok := l.getD m .sc

/-- A boundary marker (toy of `firstEntryBoundary`'s predicate): depth-`0` and either the window end
    or a `.fe` separator. -/
def isMarker (l : List Tok) (hi m : Nat) : Prop :=
  bal l m = 0 ∧ (m = hi ∨ tokAt l m = .fe)

/-! ## The two `*_clean` lemmas — no marker lies in `(0, kv]`, BIFURCATED by head shape. -/

/-- **SCALAR key** (toy of `mapPairSkeleton_locate`'s scalar branch).  `kv = 2`.  No marker lies in
    `(0, 2]` — proved by TOKEN IDENTITY ALONE: position `1` is a scalar (not `.fe`), position `2` is the
    `.value` (not `.fe`), and both are `< hi` so neither is the window end.  Takes NO balance
    hypothesis. -/
theorem scalar_clean (l : List Tok) (hi : Nat)
    (h1 : tokAt l 1 ≠ .fe) (h2 : tokAt l 2 = .vl) (h3 : 2 < hi) :
    ∀ k, 0 < k → k ≤ 2 → ¬ isMarker l hi k := by
  rintro k hk1 hk2 ⟨_, hmark⟩
  rcases hmark with h | h
  · omega
  · rcases Nat.lt_or_ge k 2 with hlt | hge
    · have hk : k = 1 := by omega
      subst hk; exact h1 h
    · have hk : k = 2 := by omega
      subst hk; rw [h2] at h; cases h

/-- **BRACKET key** (toy of `mapPairSkeleton_locate`'s bracket branch).  `kv = j+1` for the matching
    close `j`.  No marker lies in `(0, j+1]`: the endpoints (`1` the opener, `j+1` the `.value`) fall to
    token identity, but the bracket INTERIOR `[2, j]` is ruled out by the POSITIVITY invariant
    `h_pos` — the one balance step the scalar branch never pays.  Note this lemma TAKES and CONSUMES
    `h_pos`; `scalar_clean` has no such hypothesis. -/
theorem bracket_clean (l : List Tok) (hi j : Nat)
    (h_op : tokAt l 1 ≠ .fe) (h_val : tokAt l (j + 1) = .vl)
    (h_j : j + 1 < hi) (_h_loj : 1 < j)
    (h_pos : ∀ k, 2 ≤ k → k ≤ j → bal l k ≥ 1) :
    ∀ k, 0 < k → k ≤ j + 1 → ¬ isMarker l hi k := by
  rintro k hk1 hk2 ⟨hbal, hmark⟩
  rcases hmark with h | h
  · omega
  · rcases Nat.lt_or_ge k 2 with hlt | hge
    · have hk : k = 1 := by omega
      subst hk; exact h_op h
    · rcases Nat.lt_or_ge k (j + 1) with hltj | hgej
      · have hp := h_pos k hge (by omega); omega
      · have hk : k = j + 1 := by omega
        subst hk; rw [h_val] at h; cases h

/-! ## The crux `kv < e`, derived from the clean lemma + `e` being a marker. -/

/-- **SCALAR crux** — `kv = 2 < e`.  If `e ≤ 2`, then `scalar_clean` says `e` is NOT a marker,
    contradicting `h_e`.  Pure token identity underneath (no balance). -/
theorem kv_lt_e_scalar (l : List Tok) (hi e : Nat)
    (h1 : tokAt l 1 ≠ .fe) (h2 : tokAt l 2 = .vl) (h3 : 2 < hi)
    (h_lo_e : 0 < e) (h_e : isMarker l hi e) : 2 < e := by
  rcases Nat.lt_or_ge 2 e with h | h
  · exact h
  · exact absurd h_e (scalar_clean l hi h1 h2 h3 e h_lo_e h)

/-- **BRACKET crux** — `kv = j+1 < e`, the same shape but routed through `bracket_clean` (so it
    inherits the positivity dependency). -/
theorem kv_lt_e_bracket (l : List Tok) (hi j e : Nat)
    (h_op : tokAt l 1 ≠ .fe) (h_val : tokAt l (j + 1) = .vl)
    (h_j : j + 1 < hi) (h_loj : 1 < j)
    (h_pos : ∀ k, 2 ≤ k → k ≤ j → bal l k ≥ 1)
    (h_lo_e : 0 < e) (h_e : isMarker l hi e) : j + 1 < e := by
  rcases Nat.lt_or_ge (j + 1) e with h | h
  · exact h
  · exact absurd h_e (bracket_clean l hi j h_op h_val h_j h_loj h_pos e h_lo_e h)

/-! ## Concrete witnesses — balance-invisibility, then the crux instantiated. -/

/-- Scalar-key pair `k : v` then `,` — `[ky, sc, vl, sc, fe]`.  No brackets, so EVERY prefix balance is
    `0`: balance gives zero information; only the token locates `kv = 2`. -/
def sk : List Tok := [.ky, .sc, .vl, .sc, .fe]

/-- Bracket-key pair `[x] : v` then `,` — `[ky, op, sc, cl, vl, sc, fe]`.  Balance returns to `0` at
    indices `1, 4, 5, 6` — the value separator `kv = 4` is INDISTINGUISHABLE by balance from `5` or the
    marker `6`; only the token tells them apart. -/
def bk : List Tok := [.ky, .op, .sc, .cl, .vl, .sc, .fe]

-- Balance-invisibility on the flat (scalar) stream: every position is depth-`0`.
#guard bal sk 2 == 0       -- kv (vl) is depth-0
#guard bal sk 3 == 0       -- so is index 3 — NOT kv
#guard bal sk 4 == 0       -- so is the marker e (fe)
#guard tokAt sk 2 == Tok.vl
#guard tokAt sk 4 == Tok.fe

-- Balance-invisibility on the nested (bracket) stream: kv, a non-kv position, and e all sit at depth-0;
-- only the bracket interior (`2, 3`) is positive — the fact `bracket_clean` consumes.
#guard bal bk 4 == 0       -- kv (vl) is depth-0
#guard bal bk 5 == 0       -- so is index 5 — NOT kv (balance-invisible)
#guard bal bk 6 == 0       -- so is the marker e (fe)
#guard bal bk 2 == 1       -- bracket interior is POSITIVE …
#guard bal bk 3 == 1       -- … so a marker (which needs depth-0) cannot live there
#guard tokAt bk 4 == Tok.vl
#guard tokAt bk 6 == Tok.fe

/-- The scalar crux on `sk`: `kv = 2 < e = 4`, proved with no balance reasoning at all. -/
theorem sk_kv_lt_e : (2 : Nat) < 4 :=
  kv_lt_e_scalar sk 5 4 (by decide) (by decide) (by decide) (by decide)
    ⟨by decide, Or.inr (by decide)⟩

/-- The bracket crux on `bk`: `kv = j+1 = 4 < e = 6`, this time paying the interior-positivity step. -/
theorem bk_kv_lt_e : (3 + 1 : Nat) < 6 :=
  kv_lt_e_bracket bk 7 3 6 (by decide) (by decide) (by decide) (by decide)
    (by intro k hk1 hk2
        have hk : k = 2 ∨ k = 3 := by omega
        rcases hk with h | h <;> subst h <;> decide)
    (by decide) ⟨by decide, Or.inr (by decide)⟩

/-- **The demo deliverable**: the scalar crux — a split point provably PRECEDING a boundary marker with
    ZERO balance reasoning, the surprising half of the bifurcation (the nested half pays one
    positivity step; balance-invisibility routes the location through the grammar either way). -/
theorem demo (l : List Tok) (hi e : Nat)
    (h1 : tokAt l 1 ≠ .fe) (h2 : tokAt l 2 = .vl) (h3 : 2 < hi)
    (h_lo_e : 0 < e) (h_e : isMarker l hi e) : 2 < e :=
  kv_lt_e_scalar l hi e h1 h2 h3 h_lo_e h_e

end BalanceInvisibleSplitGrammarLocated

-- Axiom audit (machine-checked: `#guard_msgs` pins the profile and fails the build if it drifts).
-- `[propext, Quot.sound]` — the `Quot.sound` comes from the `DecidableEq Tok` derivation (the `cases`
-- on token equalities inside `scalar_clean`); no `Classical.choice`, and crucially no `sorryAx`.  The
-- real `mapPairSkeleton_locate` carries `[propext, Classical.choice, Quot.sound]` (the
-- `Classical.choice` from `firstEntryBoundary`/`flowBracketBalance_compose`), still `sorryAx`-free.
/-- info: 'BalanceInvisibleSplitGrammarLocated.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BalanceInvisibleSplitGrammarLocated.demo
