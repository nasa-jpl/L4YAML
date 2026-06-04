/-
# Reflection 264 — the entry-boundary location splits into an *input side* (locate the split point) and a *shape side* (classify the item); the input side is a single axis-agnostic combinatorial brick

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflection 264 (and memory `ref-entry-boundary-input-shape-split`).

**The principle.** Once a navigation recursion's *structural moves* are in hand (descend + build +
advance, R262/R263), what remains is the **analytical entry-boundary location**, and it decomposes
into two independent halves:

  - **input side** — find *where* the first body item ends: the split point `m`, a pure
    bracket-balance combinatorial fact owing nothing to the item's shape;
  - **shape side** — classify *what* the first item is: a scalar, or a matched-bracket sub-window
    (the bracket-balance matching-close analysis that *consumes* the located `m`).

This file models the **input side**: a general constructive least-witness locator
`exists_least_in_range` (no `Nat.find`, no classical choice, no well-founded recursion — structural
induction on the search gap with the decidability instance) and its specialization
`firstEntryBoundary`, which for a balanced window locates the least depth-`0` *boundary marker* `m`
(balance returns to `0`, and `m` is the window end or a separator) with the minimality certificate
that no earlier interior position is such a marker.

**Why the input side is axis-agnostic — the discriminator.** Every prior navigation brick came as a
seq lemma plus a one-session-later map mirror, because each named a collection-specific *deliverable
type* (a sequence body vs a mapping body) whose constructor differed. The split-point locator breaks
that rhythm: the body-separator token `FE` (the toy of `.flowEntry`) is **identical for sequences
and mappings**, so the boundary predicate is shared and the single lemma feeds both recursions. The
discriminator worth carrying: a navigation brick mirrors across seq/map exactly when it mentions a
collection-specific deliverable type; one phrased purely over the shared token stream (balance, the
shared separator) is written *once*. The shape side *will* split again (it builds the
collection-specific entry); the input side does not.

Positive witnesses: `firstMarker_l1` locates the separator after the first bracketed item in `[a],b`;
`firstMarker_l2` locates the *window end* (the last-item branch) in the single item `[a]`. Negative
witnesses: `not_marker_inside` — an interior position with non-zero balance is not a marker;
`bal_l1_*` `#guard`s witness that no position earlier than the located `m` is a marker (minimality is
concrete). The general helper is exercised by `least_ge3` on a pure-`Nat` predicate.
-/

namespace Tests.Reflections.EntryBoundaryLocator

/-! ## The general constructive least-witness locator (toy of `exists_least_in_range`) -/

/-- For a decidable predicate `P` holding at the range end `start + gap`, the **least** witness in
    `[start, start + gap]`, with the minimality certificate that no `k` in `[start, m)` satisfies
    `P`.  Fully constructive: structural induction on `gap`, decidability-driven upward scan via
    `if h : P start then …` — no `Nat.find`, no classical choice, no well-founded recursion.  This is
    *verbatim* the real `exists_least_in_range`. -/
theorem exists_least_in_range (P : Nat → Prop) [DecidablePred P] :
    ∀ (gap start : Nat), P (start + gap) →
      ∃ m, start ≤ m ∧ m ≤ start + gap ∧ P m ∧ ∀ k, start ≤ k → k < m → ¬ P k := by
  intro gap
  induction gap with
  | zero =>
    intro start hP
    refine ⟨start, Nat.le_refl _, ?_, ?_, ?_⟩
    · omega
    · simpa using hP
    · intro k hk1 hk2; exfalso; omega
  | succ g ih =>
    intro start hP
    if h0 : P start then
      refine ⟨start, Nat.le_refl _, ?_, h0, ?_⟩
      · omega
      · intro k hk1 hk2; exfalso; omega
    else
      have hP' : P ((start + 1) + g) := by
        have he : (start + 1) + g = start + (g + 1) := by omega
        rw [he]; exact hP
      obtain ⟨m, hm1, hm2, hm3, hm4⟩ := ih (start + 1) hP'
      refine ⟨m, by omega, by omega, hm3, ?_⟩
      intro k hk1 hk2
      rcases Nat.lt_or_ge k (start + 1) with hlt | hge
      · have hk_eq : k = start := by omega
        rw [hk_eq]; exact h0
      · exact hm4 k hge hk2

/-- The helper exercised on a pure-`Nat` predicate: the least `m` in `[1, 6]` with `m ≥ 3` is `3`. -/
theorem least_ge3 :
    ∃ m, 1 ≤ m ∧ m ≤ 6 ∧ 3 ≤ m ∧ ∀ k, 1 ≤ k → k < m → ¬ 3 ≤ k :=
  exists_least_in_range (fun n => 3 ≤ n) 5 1 (by omega)

/-! ## The toy token stream and the first-entry-boundary locator (toy of `firstEntryBoundary`) -/

/-- A toy flow token: scalar, open/close bracket, and the body separator `FE` (`.flowEntry`). -/
inductive Tok | sc | op | cl | fe
  deriving DecidableEq

/-- Bracket delta — `+1` open, `-1` close, `0` otherwise.  The separator `FE` has delta `0`, so it
    only marks a boundary *at depth 0*. -/
def delta : Tok → Int
  | .op => 1
  | .cl => -1
  | _   => 0

/-- Is this token the body separator? -/
def isFE : Tok → Bool
  | .fe => true
  | _   => false

/-- Running bracket balance over the prefix `[0, n)`. -/
def bal (l : List Tok) (n : Nat) : Int := ((l.take n).map delta).foldl (· + ·) 0

/-- Total token at index `m` (scalar default out of range), so the boundary predicate is total. -/
def tokAt (l : List Tok) (m : Nat) : Tok := l.getD m .sc

/-- **First entry-boundary locator** (toy of `firstEntryBoundary`).  For a balanced window
    (`bal l l.length = 0`), the least depth-`0` boundary marker `m` in `(0, l.length]` — a position
    where the balance from `0` returns to `0` and which is either the window end or a separator —
    with the certificate that no earlier interior position is such a marker.  Axis-agnostic: the
    separator `FE` is the *same* token whatever the surrounding collection, so this single lemma is
    the split-point locator for *both* a sequence body and a mapping body. -/
theorem firstEntryBoundary (l : List Tok) (h_pos : 0 < l.length)
    (h_total : bal l l.length = 0) :
    ∃ m, 0 < m ∧ m ≤ l.length ∧
      bal l m = 0 ∧
      (m = l.length ∨ isFE (tokAt l m) = true) ∧
      (∀ k, 0 < k → k < m →
        ¬ (bal l k = 0 ∧ (k = l.length ∨ isFE (tokAt l k) = true))) := by
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ :=
    exists_least_in_range
      (fun m => bal l m = 0 ∧ (m = l.length ∨ isFE (tokAt l m) = true))
      (l.length - 1) 1
      (by
        have he : 1 + (l.length - 1) = l.length := by omega
        rw [he]; exact ⟨h_total, Or.inl rfl⟩)
  refine ⟨m, by omega, by omega, hm3.1, hm3.2, ?_⟩
  intro k hk1 hk2
  exact hm4 k (by omega) hk2

/-! ## Positive witnesses -/

/-- `[a],b` — open, scalar, close, separator, scalar.  Balanced (`bal = 0`). -/
def l1 : List Tok := [.op, .sc, .cl, .fe, .sc]

/-- `[a]` — open, scalar, close.  A single bracketed item, no separator. -/
def l2 : List Tok := [.op, .sc, .cl]

/-- `[],a` — open, close (an *empty* bracket `[ ]`), separator, scalar.  The empty-bracket leaf
    fires at the head: `op` immediately followed by `cl`, the matching close one step in. -/
def l3 : List Tok := [.op, .cl, .fe, .sc]

-- The locator applies to both balanced windows (these type-check ⇒ the lemma fires).
theorem firstMarker_l1 :
    ∃ m, 0 < m ∧ m ≤ l1.length ∧ bal l1 m = 0 ∧
      (m = l1.length ∨ isFE (tokAt l1 m) = true) ∧
      (∀ k, 0 < k → k < m →
        ¬ (bal l1 k = 0 ∧ (k = l1.length ∨ isFE (tokAt l1 k) = true))) :=
  firstEntryBoundary l1 (by decide) (by decide)

theorem firstMarker_l2 :
    ∃ m, 0 < m ∧ m ≤ l2.length ∧ bal l2 m = 0 ∧
      (m = l2.length ∨ isFE (tokAt l2 m) = true) ∧
      (∀ k, 0 < k → k < m →
        ¬ (bal l2 k = 0 ∧ (k = l2.length ∨ isFE (tokAt l2 k) = true))) :=
  firstEntryBoundary l2 (by decide) (by decide)

-- In `l1` the first marker is at `m = 3` (the separator after the bracketed item `[a]`):
--   balance returns to 0 there, and the token is `FE`.
#guard bal l1 3 == 0
#guard isFE (tokAt l1 3) == true
-- and nowhere earlier — positions 1, 2 have non-zero balance (inside the bracket), so the located
-- `m = 3` is genuinely the least marker (minimality, witnessed concretely):
#guard bal l1 1 == 1
#guard bal l1 2 == 1

-- In `l2` the first marker is the *window end* `m = 3 = length` (the last-item branch): balance is 0
-- there and `m = length`, with no interior separator.
#guard bal l2 3 == 0
#guard l2.length == 3
#guard bal l2 1 == 1
#guard bal l2 2 == 1

/-! ## Negative witnesses -/

/-- An interior position with non-zero balance is **not** a marker (it lies *inside* the first
    bracketed item, depth ≥ 1) — so the locator correctly skips it. -/
theorem not_marker_inside :
    ¬ (bal l1 2 = 0 ∧ (2 = l1.length ∨ isFE (tokAt l1 2) = true)) := by decide

/-- The depth-`0` separator marker is the `FE`, not the close bracket: position `2` (the `cl` in
    `l1`) is not the separator. -/
theorem cl_is_not_separator : isFE (tokAt l1 2) = false := by decide

/-! ## The shape side — per-constructor window-lifts (toy of `recseqentry_{scalar,seqempty}_window`, Reflections 265 & 266)

Once the input side has located the split point `m`, the **shape side** classifies *what* the first
item `[lo, m)` is — building the entry inductive.  The shape side is the *family of per-constructor
window-lifts* — one lemma per constructor, building that constructor from the window.  The recursive
constructor's lift is the BUILD structural move (in the real development, `located_entry_of_recseqbody`,
already landed), so the shape side's genuinely-new work is the **non-recursive leaves**.

There are two leaves, and **they come as a family** (Reflection 266): the one-token **scalar** leaf
(`entry_scalar_window`, the recursion's base case — no matching-close, no descent, `m = lo + 1`), and
the two-token **empty-bracket** leaf (`entry_seqempty_window` — an empty `[ ]`, `m = lo + 2`, the
matching close one step in).  The empty-bracket lift is the scalar lift *scaled by one token*: the
same window-singleton identity run twice (peel `[lo]`, then `[lo+1]`), the same trailing-`drop`-nil
and `getElem_take` simplifications, the same head-value transport — only the arity of the fixed shape
moved.  That is the signature of a *leaf family*: once the first leaf is proven, the rest are the same
proof at a different arity, not fresh analysis.

This is also where the **seq/map mirror re-splits**: these lemmas name the entry inductive (a
collection-specific deliverable type, unlike the axis-agnostic `firstEntryBoundary`), so they are
seq-specific — the map shape side's leaf is a whole key/value *pair*, a different (heavier) shape. -/

/-- A toy recursive seq entry (toy of `RecSeqEntry`): a scalar leaf, an empty-bracket leaf, or a
    bracketed sub-window.  `scalar` and `seqEmpty` are the non-recursive leaves the shape side lands
    first; `seq` is the recursive constructor whose window-lift is the BUILD structural move (so it is
    *not* new shape-side work).  `seqEmpty` is written with parametric tokens + value hypotheses,
    mirroring the real `RecSeqEntry.seqEmpty (op cl) (h_op …) (h_cl …)`. -/
inductive Entry : List Tok → Prop where
  | scalar (t : Tok) (h : t = .sc) : Entry [t]
  | seqEmpty (a b : Tok) (h_op : a = .op) (h_cl : b = .cl) : Entry (a :: ([] ++ [b]))
  | seq (interior : List Tok) : Entry (.op :: (interior ++ [.cl]))

/-- **Scalar-leaf window-lift** (toy of `recseqentry_scalar_window`).  The one-token window at a
    scalar head is an `Entry.scalar` — the non-recursive base case.  Same proof skeleton as the real
    lemma: the window-singleton identity `(l.take (lo+1)).drop lo = [l[lo]]` (`List.getElem_cons_drop`
    + `List.getElem_take`, trailing `drop (lo+1)` killed by `List.drop_eq_nil_of_le`), then the leaf
    constructor with the head value transported off `tokAt` (`List.getElem_eq_getD`). -/
theorem entry_scalar_window (l : List Tok) (lo : Nat)
    (h_lo : lo < l.length) (h_sc : tokAt l lo = .sc) :
    Entry ((l.take (lo + 1)).drop lo) := by
  have hlen : lo < (l.take (lo + 1)).length := by rw [List.length_take]; omega
  have h_drop_nil : (l.take (lo + 1)).drop (lo + 1) = [] := by
    apply List.drop_eq_nil_of_le; rw [List.length_take]; omega
  have h_win : (l.take (lo + 1)).drop lo = [l[lo]'h_lo] := by
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take, h_drop_nil] at h
    exact h
  rw [h_win]
  have h_val : l[lo]'h_lo = .sc := by
    rw [List.getElem_eq_getD (.sc)]; exact h_sc
  exact Entry.scalar _ h_val

/-! ### Positive witnesses — the scalar leaf fires at every scalar head -/

-- In `l1 = [op, sc, cl, fe, sc]` the scalar heads are positions `1` and `4`; the leaf lift fires at
-- each, producing an `Entry` of the one-token window `[sc]`.
theorem scalar_window_l1_1 : Entry ((l1.take (1 + 1)).drop 1) :=
  entry_scalar_window l1 1 (by decide) (by decide)

theorem scalar_window_l1_4 : Entry ((l1.take (4 + 1)).drop 4) :=
  entry_scalar_window l1 4 (by decide) (by decide)

-- The located window really is the singleton `[sc]`:
#guard (l1.take (1 + 1)).drop 1 == [Tok.sc]
#guard (l1.take (4 + 1)).drop 4 == [Tok.sc]

/-! ### Negative witnesses — the leaf does *not* cover the bracketed (recursive) constructor -/

/-- The window head at position `0` of `l1` is `op`, not a scalar — so `entry_scalar_window` does
    **not** apply there: an opener head is the recursive `seq` constructor's job (its window-lift is
    the BUILD structural move), not the leaf's. -/
theorem op_head_is_not_scalar_leaf : tokAt l1 0 ≠ .sc := by decide

-- And the bracketed first item `[op, sc, cl]` is three tokens, not the one-token shape the scalar
-- leaf produces — the recursive constructor genuinely is a different (non-leaf) window-lift.
#guard (l1.take 3).length == 3

/-! ### The empty-bracket leaf — the scalar leaf scaled by one token (toy of `recseqentry_seqempty_window`, Reflection 266)

The second non-recursive leaf: an empty bracket `[ ]`.  The proof is `entry_scalar_window`'s window
identity run **twice** — the only thing that changed is the arity (one token → two). -/

/-- **Empty-bracket window-lift** (toy of `recseqentry_seqempty_window`).  Given an opener `op` at the
    window head immediately followed by a closer `cl`, the two-token window `(l.take (lo+2)).drop lo`
    is an `Entry.seqEmpty` — `m = lo + 2`, non-recursive (no interior to descend into).  Same skeleton
    as `entry_scalar_window`, the `List.getElem_cons_drop` peel applied twice (`[lo]` then `[lo+1]`,
    trailing `drop (lo+2)` killed by `List.drop_eq_nil_of_le`), each index through the `take` by
    `List.getElem_take`, both head values transported off `tokAt` (`List.getElem_eq_getD`). -/
theorem entry_seqempty_window (l : List Tok) (lo : Nat)
    (h_lo1 : lo + 1 < l.length)
    (h_open : tokAt l lo = .op) (h_close : tokAt l (lo + 1) = .cl) :
    Entry ((l.take (lo + 2)).drop lo) := by
  have h_lo : lo < l.length := by omega
  have hlen0 : lo < (l.take (lo + 2)).length := by rw [List.length_take]; omega
  have hlen1 : lo + 1 < (l.take (lo + 2)).length := by rw [List.length_take]; omega
  have h_drop_nil : (l.take (lo + 2)).drop (lo + 2) = [] := by
    apply List.drop_eq_nil_of_le; rw [List.length_take]; omega
  have h_win : (l.take (lo + 2)).drop lo = [l[lo]'h_lo, l[lo + 1]'h_lo1] := by
    have e1 := (List.getElem_cons_drop hlen1).symm
    rw [List.getElem_take, h_drop_nil] at e1
    have e0 := (List.getElem_cons_drop hlen0).symm
    rw [List.getElem_take, e1] at e0
    exact e0
  rw [h_win]
  have h_op_val : l[lo]'h_lo = .op := by rw [List.getElem_eq_getD (.sc)]; exact h_open
  have h_cl_val : l[lo + 1]'h_lo1 = .cl := by rw [List.getElem_eq_getD (.sc)]; exact h_close
  exact Entry.seqEmpty _ _ h_op_val h_cl_val

/-! #### Positive witness — the empty-bracket leaf fires at an `op`-then-`cl` head -/

-- In `l3 = [op, cl, fe, sc]` the empty bracket sits at the head (`lo = 0`); the leaf lift fires,
-- producing an `Entry` of the two-token window `[op, cl]`.
theorem seqempty_window_l3_0 : Entry ((l3.take (0 + 2)).drop 0) :=
  entry_seqempty_window l3 0 (by decide) (by decide) (by decide)

-- The located window really is the two-token `[op, cl]`:
#guard (l3.take (0 + 2)).drop 0 == [Tok.op, Tok.cl]

/-! #### Negative witnesses — the empty-bracket leaf is *not* a one-token shape, and needs the close adjacent -/

-- The empty-bracket window is two tokens, distinct from the scalar leaf's one-token shape: the two
-- leaves are genuinely different members of the family (different arity), not the same lemma.
#guard (l3.take (0 + 2)).drop 0 != [Tok.op]

/-- The empty-bracket leaf needs `cl` *immediately* after `op`.  In `l1 = [op, sc, cl, …]` the token
    after the opener is `sc`, not `cl` — so `entry_seqempty_window` does **not** apply at `l1`'s head:
    that is the recursive `seq` constructor's job (a non-empty interior), not the empty leaf's. -/
theorem l1_head_is_not_empty_bracket : tokAt l1 (0 + 1) ≠ .cl := by decide

end Tests.Reflections.EntryBoundaryLocator
