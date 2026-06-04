/-
# Reflection 264 — the entry-boundary location splits into an *input side* (locate the split point) and a *shape side* (classify the item); the input side is a single axis-agnostic combinatorial brick

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflection 264 (and memory `ref-entry-boundary-input-shape-split`).

**Extended by Reflection 271** (the ADVANCE-step *invariant-preservation* certificate): the input
side is not only *locating* the split point (`firstEntryBoundary`) but also *certifying the tail past
it* (`advanceTail_invariant`) — two axis-agnostic balance facts, with the collection-specific shape
side classifier between them.  A recursion can be *structurally complete* (every constructor liftable)
yet not *runnable* (no proof the recursive call's precondition holds); the gap is this certificate.
See the final section.

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

/-- A toy flow token: scalar, sequence open/close bracket `op`/`cl`, the body separator `FE`
    (`.flowEntry`), a *distinct* mapping open/close bracket `mo`/`mc` — the toy of the real
    `.flowSequenceStart`/`.flowSequenceEnd` vs `.flowMappingStart`/`.flowMappingEnd` distinction (so a
    nested mapping is a different shape from a nested sequence, as in the real grammar) — and the
    depth-`0` map *pair* markers `ky`/`vl` (toy of `.key`/`.value`), which glue a key/value pair on the
    map shape side (Reflection 268). -/
inductive Tok | sc | op | cl | fe | mo | mc | ky | vl
  deriving DecidableEq

/-- Bracket delta — `+1` open, `-1` close, `0` otherwise.  Both bracket kinds (`op`/`cl` and
    `mo`/`mc`) count; the separator `FE` and the pair markers `ky`/`vl` have delta `0`, so they only
    mark a boundary *at depth 0*. -/
def delta : Tok → Int
  | .op => 1
  | .cl => -1
  | .mo => 1
  | .mc => -1
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

/-- `{a}` — map-open, scalar, map-close (a nested *mapping* with a one-token interior `[sc]`).  The
    map near-leaf fires at the head: `mo` at `lo`, the matching `mc` at `hi`, interior `[sc]`
    well-bracketed (`WB`). -/
def l4 : List Tok := [.mo, .sc, .mc]

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

/-! ## The shape side — per-constructor window-lifts (toy of `recseqentry_{scalar,seqempty,map}_window`, Reflections 265, 266 & 267)

Once the input side has located the split point `m`, the **shape side** classifies *what* the first
item `[lo, m)` is — building the entry inductive.  The shape side is the *family of per-constructor
window-lifts* — one lemma per constructor, building that constructor from the window.  The recursive
constructor's lift is the BUILD structural move (in the real development, `located_entry_of_recseqbody`,
already landed), so the shape side's genuinely-new work is the **non-recursive leaves**.

There are two true leaves, and **they come as a family** (Reflection 266): the one-token **scalar**
leaf (`entry_scalar_window`, the recursion's base case — no matching-close, no descent, `m = lo + 1`),
and the two-token **empty-bracket** leaf (`entry_seqempty_window` — an empty `[ ]`, `m = lo + 2`, the
matching close one step in).  The empty-bracket lift is the scalar lift *scaled by one token*: the
same window-singleton identity run twice (peel `[lo]`, then `[lo+1]`), the same trailing-`drop`-nil
and `getElem_take` simplifications, the same head-value transport — only the arity of the fixed shape
moved.  That is the signature of a *leaf family*: once the first leaf is proven, the rest are the same
proof at a different arity, not fresh analysis.

The family's **last member** (Reflection 267) is the **nested-mapping near-leaf** (`entry_map_window`):
a nested mapping `{ … }` as one item of the enclosing sequence.  It is a *near*-leaf, not a true leaf
— it spans a *variable* interior, not a fixed token count — but still NOT a recursion edge, because
the `map` constructor STORES only the flat `WB interior` projection fact (not a recursive body, R244),
so the enclosing locate does not descend through it.  Its lift is **the recursive `seq` BUILD move
minus one field**: it transports the *same* window plumbing (rest-decomposition `(take (hi+1)).drop
(lo+1) = (take hi).drop (lo+1) ++ [b]` via `List.take_add_one`/`List.drop_append_of_le_length`, opener
peel via `List.getElem_cons_drop`/`List.getElem_take`, into `op :: (interior ++ [cl])` shape) and
differs only in the terminal constructor (`Entry.map`, not `seq`) and that it is fed the bare
`WB interior` hypothesis (not a recursive body).  That one-field arity delta *is* the store-vs-project
decision — the same principle the constructor arity expressed in R246/R261/R263, here one tier up.

This is also where the **seq/map mirror re-splits**: these lemmas name the entry inductive (a
collection-specific deliverable type, unlike the axis-agnostic `firstEntryBoundary`), so they are
seq-specific — the map shape side's leaf is a whole key/value *pair*, a different (heavier) shape.
With scalar + seqEmpty + map + the BUILD-move `seq`, the seq shape side's four-way head dispatch is
complete. -/

/-- A toy *well-bracketed* predicate (toy of `WellBracketed`): the interior's running balance returns
    to `0` over its whole length.  This is the **flat projection fact** the `map` near-leaf STORES —
    contrast the recursive `seq`, whose interior is a recursive body structure.  It is decidable, so
    the witnesses below discharge it by `decide`. -/
def WB (l : List Tok) : Prop := bal l l.length = 0

instance (l : List Tok) : Decidable (WB l) := by unfold WB; infer_instance

/-- A toy recursive seq entry (toy of `RecSeqEntry`): a scalar leaf, an empty-bracket leaf, a
    bracketed sub-*sequence*, or a nested *mapping*.  `scalar` and `seqEmpty` are the non-recursive
    leaves the shape side lands first; `seq` is the recursive constructor whose window-lift is the
    BUILD structural move (so it is *not* new shape-side work); `map` is the **near-leaf** — a
    bracketed window like `seq`, but it STORES only the flat `WB interior` projection fact (toy of
    `RecSeqEntry.map` storing only `WellBracketed`, R244), NOT a recursive body, so it does not extend
    the recursion graph.  `seqEmpty`/`map` are written with parametric tokens + value hypotheses,
    mirroring the real `RecSeqEntry.{seqEmpty,map} (op cl) (h_op …) (h_cl …)`. -/
inductive Entry : List Tok → Prop where
  | scalar (t : Tok) (h : t = .sc) : Entry [t]
  | seqEmpty (a b : Tok) (h_op : a = .op) (h_cl : b = .cl) : Entry (a :: ([] ++ [b]))
  | seq (interior : List Tok) : Entry (.op :: (interior ++ [.cl]))
  | map (a b : Tok) (interior : List Tok)
      (h_op : a = .mo) (h_cl : b = .mc) (h_wb : WB interior) :
      Entry (a :: (interior ++ [b]))

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

/-! ### The nested-mapping near-leaf — the recursive `seq` BUILD move minus one field (toy of `recseqentry_map_window`, Reflection 267)

The family's last member.  A *variable*-width interior (so a near-leaf, not a true leaf), but it
STORES only the flat `WB interior` fact, so it terminates the dispatch rather than recursing.  The
proof is the *same* window plumbing as the recursive `seq` BUILD move, differing only in the terminal
constructor and the one stored field (`WB`, not a recursive body). -/

/-- **Nested-mapping window-lift** (toy of `recseqentry_map_window`).  Given a map-opener `mo` at the
    window head `lo`, its matching map-closer `mc` at `hi`, and a well-bracketed interior window
    `(l.take hi).drop (lo+1)` (the flat `WB` projection fact), the opener-window
    `(l.take (hi+1)).drop lo` is an `Entry.map`.  The proof transports the recursive `seq` BUILD move's
    window plumbing verbatim: rest-decomposition `(take (hi+1)).drop (lo+1) = (take hi).drop (lo+1) ++
    [l[hi]]` (`List.take_add_one` + `List.drop_append_of_le_length`), opener peel
    (`List.getElem_cons_drop` + `List.getElem_take`) into `op :: (interior ++ [cl])` shape, head values
    off `tokAt` (`List.getElem_eq_getD`) — then `Entry.map` fed the bare `h_wb`.  The *only* differences
    from a recursive `seq` build are the constructor (`map`) and that one stored field (`WB`, not a
    body): the one-field arity delta IS the store-vs-project decision. -/
theorem entry_map_window (l : List Tok) (lo hi : Nat)
    (h_lo_hi : lo < hi) (h_hi : hi < l.length)
    (h_open : tokAt l lo = .mo) (h_close : tokAt l hi = .mc)
    (h_wb : WB ((l.take hi).drop (lo + 1))) :
    Entry ((l.take (hi + 1)).drop lo) := by
  have h_lo : lo < l.length := by omega
  -- rest-decomposition: the `interior ++ [cl]` tail.
  have h_rest : (l.take (hi + 1)).drop (lo + 1)
      = (l.take hi).drop (lo + 1) ++ [l[hi]'h_hi] := by
    have h_ts : l.take (hi + 1) = l.take hi ++ [l[hi]'h_hi] := by
      rw [List.take_add_one, List.getElem?_eq_getElem h_hi]; rfl
    rw [h_ts]
    have h_len : lo + 1 ≤ (l.take hi).length := by rw [List.length_take]; omega
    rw [List.drop_append_of_le_length h_len]
  -- peel the opener.
  have h_peel : (l.take (hi + 1)).drop lo
      = l[lo]'(by omega) :: (l.take (hi + 1)).drop (lo + 1) := by
    have hlen : lo < (l.take (hi + 1)).length := by rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    exact h
  rw [h_peel, h_rest]
  have h_op_val : l[lo]'(by omega) = .mo := by rw [List.getElem_eq_getD (.sc)]; exact h_open
  have h_cl_val : l[hi]'h_hi = .mc := by rw [List.getElem_eq_getD (.sc)]; exact h_close
  exact Entry.map _ _ _ h_op_val h_cl_val h_wb

/-! #### Positive witness — the map near-leaf fires at a `mo … mc` window -/

-- In `l4 = [mo, sc, mc]` the nested map sits at the head (`lo = 0`, `hi = 2`); the near-leaf fires,
-- producing an `Entry` of the window `[mo, sc, mc]` — its interior `[sc]` is well-bracketed (`WB`).
theorem map_window_l4_0 : Entry ((l4.take (2 + 1)).drop 0) :=
  entry_map_window l4 0 2 (by decide) (by decide) (by decide) (by decide) (by decide)

-- The interior window really is `[sc]`, and it is `WB` (balance returns to 0):
#guard (l4.take 2).drop (0 + 1) == [Tok.sc]
theorem interior_l4_is_wb : WB ((l4.take 2).drop (0 + 1)) := by decide
-- and the located opener-window really is the whole `[mo, sc, mc]`:
#guard (l4.take (2 + 1)).drop 0 == [Tok.mo, Tok.sc, Tok.mc]

/-! #### Negative witnesses — the near-leaf needs the matching `mc`, a balanced interior, and stores no body -/

-- The map near-leaf is a (≥2)-token shape, not the scalar leaf's one-token window: it is a genuinely
-- different family member.
#guard (l4.take (2 + 1)).drop 0 != [Tok.mo]

/-- An *unbalanced* interior is not a valid near-leaf input: `WB` is exactly the stored projection
    fact, and it fails for `[mo]` (a lone opener, balance `1 ≠ 0`).  This is the flat fact the
    constructor stores in place of a recursive body. -/
theorem unbalanced_interior_not_wb : ¬ WB [Tok.mo] := by decide

/-- The map near-leaf needs the *map* closer `mc`, distinct from the sequence closer `cl`: in
    `l1 = [op, sc, cl, …]` the bracket is a sequence bracket, so the map near-leaf does not apply
    there (that is the seq side's dispatch — `seqEmpty`/`seq`/`scalar` — not `map`). -/
theorem cl_is_not_map_close : tokAt l1 2 ≠ .mc := by decide

/-! ## The map shape side — one pair assembler, not a dispatch (toy of `recmappair_window`, Reflection 268)

The shape side **re-splits** across seq/map (it names a collection-specific deliverable type — here
the `Pair` inductive — unlike the axis-agnostic `firstEntryBoundary`).  But the map shape side, unlike
the seq side, is **not a per-constructor dispatch at all**.  A map-body item is always a whole
key/value *pair* `ky <block_k> vl <block_v>` (`Pair`), and `Pair.mk` is the inductive's sole
constructor — there is nothing to classify by head token.  So the map shape side is **one assembler**,
`pair_window`, that does two things, both of which *reuse already-landed work*:

  - it **consumes the complete seq dispatch as its two sub-blocks**: the key and value blocks are
    arbitrary `Entry`s — a scalar, an empty bracket, a nested sequence, or a nested mapping — so the
    seq side being finished (R265–R267) means the map side adds *zero* per-constructor classification.
    `pair_window` takes the two `Entry` blocks as hypotheses and never inspects their shape;
  - its one new piece — the **pair glue** — is a *composition of two already-landed positional
    patterns*: the **segment split** at the `vl` separator (the ADVANCE plumbing
    `List.take_append_drop`/`take_take`/`drop_drop`, splitting the pair interior `[lo+1, m)` at `kv`)
    and the **opener peel** of `l[lo]` (the BUILD/leaf peel `List.getElem_cons_drop`/`List.getElem_take`),
    terminated by `Pair.mk`.

So the seq/map re-split that the prior sections anticipated as "a separate brick" surfaces here as
**composition** (ADVANCE-split ∘ BUILD-peel), not a fresh family of lemmas. -/

/-- A toy map pair (toy of `RecMapPair`): `ky :: (block_k ++ vl :: block_v)`, with the key and value
    blocks each a recursive seq `Entry`, glued by the depth-`0` `ky`/`vl` markers.  Sole constructor —
    the map shape side classifies nothing, it only assembles. -/
inductive Pair : List Tok → Prop where
  | mk (kt : Tok) (block_k : List Tok) (vt : Tok) (block_v : List Tok)
      (h_kt : kt = .ky) (h_ke : Entry block_k) (h_vt : vt = .vl) (h_ve : Entry block_v) :
      Pair (kt :: (block_k ++ vt :: block_v))

/-- **Map-pair window assembler** (toy of `recmappair_window`).  Given a key marker `ky` at the window
    head `lo`, a key block over `[lo+1, kv)` as an `Entry`, a value marker `vl` at `kv`, and a value
    block over `[kv+1, m)` as an `Entry`, the pair window `(l.take m).drop lo` is a `Pair`.  The proof
    composes two already-landed plumbing patterns: the **segment split** at the `vl` separator
    (`recseqbody_cons_window`'s ADVANCE plumbing — `List.take_append_drop`/`take_take`/`drop_drop`,
    splitting `[lo+1, m)` at `kv`) and the **opener peel** of `l[lo]` (`List.getElem_cons_drop` +
    `List.getElem_take`), terminated by `Pair.mk`, with both marker values transported off `tokAt`
    (`List.getElem_eq_getD`).  The two `Entry` sub-blocks are *hypotheses* — agnostic to how they were
    produced (the seq dispatch covers every block shape). -/
theorem pair_window (l : List Tok) (lo kv m : Nat)
    (h_lo_kv : lo < kv) (h_kv_m : kv < m) (h_m : m ≤ l.length)
    (h_key : tokAt l lo = .ky) (h_value : tokAt l kv = .vl)
    (h_ke : Entry ((l.take kv).drop (lo + 1)))
    (h_ve : Entry ((l.take m).drop (kv + 1))) :
    Pair ((l.take m).drop lo) := by
  have h_lo : lo < l.length := by omega
  have h_kv : kv < l.length := by omega
  -- segment split: the pair interior `[lo+1, m)` divides at the `vl` marker `kv`.
  have hA : (l.take m).drop (lo + 1)
      = (l.take kv).drop (lo + 1) ++ (l.take m).drop kv := by
    rw [← List.take_append_drop (kv - (lo + 1)) ((l.take m).drop (lo + 1))]
    congr 1
    · rw [List.drop_take, List.drop_take, List.take_take,
        Nat.min_eq_left (show kv - (lo + 1) ≤ m - (lo + 1) by omega)]
    · rw [List.drop_drop, Nat.add_sub_cancel' (show lo + 1 ≤ kv by omega)]
  -- separator peel: the `vl` marker at `kv` heads the value half `[kv, m)`.
  have hB : (l.take m).drop kv = l[kv]'h_kv :: (l.take m).drop (kv + 1) := by
    have hlen : kv < (l.take m).length := by rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    exact h
  -- opener peel: the `ky` marker at `lo` heads the whole pair window `[lo, m)`.
  have h_peel : (l.take m).drop lo = l[lo]'h_lo :: (l.take m).drop (lo + 1) := by
    have hlen : lo < (l.take m).length := by rw [List.length_take]; omega
    have h := (List.getElem_cons_drop hlen).symm
    rw [List.getElem_take] at h
    exact h
  rw [h_peel, hA, hB]
  have h_kt_val : l[lo]'h_lo = .ky := by rw [List.getElem_eq_getD (.sc)]; exact h_key
  have h_vt_val : l[kv]'h_kv = .vl := by rw [List.getElem_eq_getD (.sc)]; exact h_value
  exact Pair.mk _ _ _ _ h_kt_val h_ke h_vt_val h_ve

/-! ### Positive witness — the pair assembler glues two scalar `Entry` blocks -/

/-- `{a: b}` flattened to a body: `ky a vl b` — a scalar-key/scalar-value pair. -/
def l5 : List Tok := [.ky, .sc, .vl, .sc]

-- The pair occupies `[0, 4)`: key marker at `0`, key block `[sc]` over `[1, 2)`, value marker at `2`,
-- value block `[sc]` over `[3, 4)`.  Both blocks are produced by the *seq* scalar leaf — the seq
-- dispatch supplies the map side's sub-blocks.
theorem pair_window_l5 : Pair ((l5.take 4).drop 0) :=
  pair_window l5 0 2 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (entry_scalar_window l5 1 (by decide) (by decide))
    (entry_scalar_window l5 3 (by decide) (by decide))

-- The two sub-blocks really are the singleton `[sc]`, and the whole window is the four-token pair:
#guard (l5.take 2).drop (0 + 1) == [Tok.sc]
#guard (l5.take 4).drop (2 + 1) == [Tok.sc]
#guard (l5.take 4).drop 0 == [Tok.ky, Tok.sc, Tok.vl, Tok.sc]

/-! ### Negative witnesses — the pair is a composite (not a single `Entry`), and needs both markers -/

-- The pair window is a four-token composite, distinct from any single-`Entry` window shape (the
-- scalar leaf's one token, the empty bracket's two): the map item is a heavier shape than a seq item.
#guard (l5.take 4).drop 0 != [Tok.sc]
#guard (l5.take 4).drop 0 != [Tok.ky]

/-- The pair assembler needs the *key* marker `ky` at the head: in `l1` (a sequence body) the head is
    `op`, not `ky`, so `pair_window` does not apply — a sequence body is not a mapping body. -/
theorem seq_head_is_not_key : tokAt l1 0 ≠ .ky := by decide

/-- And the *value* marker `vl` separating the two blocks is distinct from the seq separator `fe`: in
    `l1` position `3` is `fe`, not `vl`. -/
theorem fe_is_not_value : tokAt l1 3 ≠ .vl := by decide

/-! ## The ADVANCE-step tail invariant — invariant preservation (toy of `advanceTail_invariant`, Reflection 271)

The input/shape split above gives the recursion its *moves* and its *split-point locator*, but a
recursion is not **runnable** until one more fact is proved: after it ADVANCEs past a depth-`0`
separator at `m`, the tail `[m+1, hi)` is **itself a valid recursive sub-instance**.  The structural
moves are all *assembly* lemmas (given the pieces — a located entry, a recursive tail — build the
constructor); **none of them certifies the recursive call's _precondition_** (that the tail is a
balanced window the locator and classifier can act on).  That certificate is `advanceTail_invariant`,
the toy's final brick: pure bracket-balance algebra, and — like `firstEntryBoundary`, unlike the
structural moves — **axis-agnostic** (it names no entry/pair deliverable type, so it is written once
for both the sequence and the mapping recursion).

It needs a *range* balance `balR l lo hi` (toy of `flowBracketBalance`, balance over `[lo, hi)`), its
additivity `balR_compose` (toy of `flowBracketBalance_compose`), and the single-token value
`balR_single`.  Then, given a balanced window with a depth-`0` separator at `m`, it delivers the three
facts the recursive call on `[m+1, hi)` needs: (a) the prefix *through* the separator is balanced;
(b) the **tail is balanced**; (c) the tail **re-bases** — every depth from the outer origin `lo`
equals the depth from the new origin `m+1` (`balR lo p = balR (m+1) p`), so the recursion threads its
invariants from a *moving* origin for free.  This sharpens R264's input/shape split: the *input* side
is locate-the-point **and** certify-the-tail, both axis-agnostic; structural-complete ≠ runnable. -/

/-- Sum of bracket deltas over a token list. -/
def sumD (l : List Tok) : Int := (l.map delta).foldl (· + ·) 0

/-- Shifting the `foldl` accumulator out (toy of the real `foldl_add_shift`). -/
theorem foldl_add_shift (l : List Int) (init : Int) :
    l.foldl (· + ·) init = init + l.foldl (· + ·) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih => simp only [List.foldl]; rw [ih, ih (0 + hd)]; omega

/-- `sumD` is additive over append — the workhorse behind `balR_compose`. -/
theorem sumD_append (a b : List Tok) : sumD (a ++ b) = sumD a + sumD b := by
  unfold sumD
  rw [List.map_append, List.foldl_append]
  exact foldl_add_shift (b.map delta) ((a.map delta).foldl (· + ·) 0)

/-- **Range balance** over `[lo, hi)` (toy of `flowBracketBalance`). -/
def balR (l : List Tok) (lo hi : Nat) : Int :=
  if lo ≥ hi then 0 else sumD ((l.drop lo).take (hi - lo))

/-- **Additivity** of the range balance: splitting `[lo, hi)` at a midpoint adds (toy of
    `flowBracketBalance_compose`).  Same proof shape as the real lemma: the two degenerate ends by
    `simp`, the middle by the slice decomposition `take (hi-lo) (drop lo) = take (mid-lo) (drop lo) ++
    take (hi-mid) (drop mid)` (`List.take_add` + `List.drop_drop`) fed to `sumD_append`. -/
theorem balR_compose (l : List Tok) (lo mid hi : Nat) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    balR l lo hi = balR l lo mid + balR l mid hi := by
  by_cases hlm : lo = mid
  · subst hlm; simp [balR]
  · by_cases hmh : mid = hi
    · subst hmh; simp [balR]
    · have e1 : ¬ lo ≥ hi := by omega
      have e2 : ¬ lo ≥ mid := by omega
      have e3 : ¬ mid ≥ hi := by omega
      unfold balR
      rw [if_neg e1, if_neg e2, if_neg e3]
      have hsplit : (l.drop lo).take (hi - lo)
          = (l.drop lo).take (mid - lo) ++ (l.drop mid).take (hi - mid) := by
        rw [show hi - lo = (mid - lo) + (hi - mid) from by omega, List.take_add,
            List.drop_drop, show lo + (mid - lo) = mid from by omega]
      rw [hsplit, sumD_append]

/-- The range balance of a single token equals its bracket delta (toy of
    `flowBracketBalance_single`). -/
theorem balR_single (l : List Tok) (i : Nat) (h : i < l.length) :
    balR l i (i + 1) = delta (l[i]'h) := by
  have hslice : (l.drop i).take (i + 1 - i) = [l[i]'h] := by
    rw [show i + 1 - i = 1 from by omega, List.drop_eq_getElem_cons h]; rfl
  unfold balR
  rw [if_neg (show ¬ i ≥ i + 1 from by omega), hslice]
  simp [sumD]

/-- **ADVANCE-step tail invariant** (toy of `advanceTail_invariant`).  Given a balanced window
    `[lo, hi)` and a depth-`0` separator `fe` at `m` (`lo ≤ m < hi`, `balR l lo m = 0`,
    `tokAt l m = .fe`), the tail `[m+1, hi)` is a valid recursive sub-instance: (a) the prefix through
    the separator is balanced, (b) the tail is balanced, (c) every outer-origin depth on the tail
    equals the new-origin depth.  *Verbatim* the real proof's structure: the separator's delta is `0`
    (`balR_single`), so `balR_compose` split at `m` and at `m+1` gives all three by linear arithmetic
    — no structural induction, axis-agnostic. -/
theorem advanceTail_invariant (l : List Tok) (lo m hi : Nat)
    (h_lo_m : lo ≤ m) (h_m_hi : m < hi) (h_hi : hi ≤ l.length)
    (h_m_bal : balR l lo m = 0)
    (h_sep : tokAt l m = .fe)
    (h_total : balR l lo hi = 0) :
    balR l lo (m + 1) = 0 ∧ balR l (m + 1) hi = 0 ∧
    (∀ p, m + 1 ≤ p → p ≤ hi → balR l lo p = balR l (m + 1) p) := by
  have h_m_len : m < l.length := by omega
  -- the separator's delta is 0, so the single-token range `[m, m+1)` is balanced.
  have h_val : l[m]'h_m_len = .fe := by rw [List.getElem_eq_getD (.sc)]; exact h_sep
  have h_single : balR l m (m + 1) = 0 := by rw [balR_single l m h_m_len, h_val]; rfl
  -- (a) prefix through the separator.
  have h_prefix : balR l lo (m + 1) = 0 := by
    rw [balR_compose l lo m (m + 1) h_lo_m (by omega), h_m_bal]; omega
  -- (b) tail balanced (total − prefix).
  have h_tail : balR l (m + 1) hi = 0 := by
    have hc := balR_compose l lo (m + 1) hi (by omega) (by omega)
    rw [h_total, h_prefix] at hc; omega
  refine ⟨h_prefix, h_tail, ?_⟩
  -- (c) re-basing: `balR lo p = balR lo (m+1) + balR (m+1) p = 0 + balR (m+1) p`.
  intro p hp1 hp2
  rw [balR_compose l lo (m + 1) p (by omega) hp1, h_prefix]; omega

/-! ### Positive witness — the invariant fires on a depth-`0` separator -/

/-- `[a],[b]` — `op sc cl fe op sc cl`.  Balanced, with the body separator `fe` at depth `0` (position
    `3`) splitting it into two bracketed items.  A richer tail than `l1`'s lone scalar — the tail
    `[4, 7)` is itself a bracketed item, so re-basing is exercised *mid-bracket*. -/
def l6 : List Tok := [.op, .sc, .cl, .fe, .op, .sc, .cl]

theorem advanceTail_l6 :
    balR l6 0 (3 + 1) = 0 ∧ balR l6 (3 + 1) 7 = 0 ∧
    (∀ p, 3 + 1 ≤ p → p ≤ 7 → balR l6 0 p = balR l6 (3 + 1) p) :=
  advanceTail_invariant l6 0 3 7 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- (a) the prefix `op sc cl fe` through the separator is balanced; (b) the tail `op sc cl` is balanced:
#guard balR l6 0 4 == 0
#guard balR l6 4 7 == 0
-- (c) re-basing exercised *mid-bracket*: inside the tail's `[b]` the running depth is `1` from EITHER
-- origin — the outer origin `0` and the new origin `4` agree precisely because the prefix `[0,4)` is
-- balanced.  This is the fact that lets the recursion thread its invariants from a moving origin.
#guard balR l6 0 5 == balR l6 4 5
#guard balR l6 0 6 == balR l6 4 6
#guard balR l6 0 5 == 1
#guard balR l6 4 5 == 1

/-! ### Negative witnesses — the depth-`0` hypothesis is load-bearing -/

/-- `[ , ]` — an `fe` *inside* the bracket (position `1`), at depth `1` not `0`. -/
def l7 : List Tok := [.op, .fe, .cl]

/-- An **interior** separator (inside a bracket, depth ≥ 1) does **not** satisfy `balR l lo m = 0`, so
    `advanceTail_invariant` correctly does not apply there — only a *depth-0* separator splits the body
    into recursive sub-instances.  (The token *is* a separator; what disqualifies it is its depth.) -/
theorem interior_sep_not_depth0 : balR l7 0 1 ≠ 0 := by decide
#guard tokAt l7 1 == Tok.fe       -- it is an `fe`…
#guard balR l7 0 1 == 1           -- …but at depth 1, so not a body boundary

-- Re-basing is **not** a free identity: it holds on the tail *because* the prefix `[0, m+1)` is
-- balanced.  At a position *before* the new origin the two frames disagree — origin `0` sees the
-- leading bracket, origin `4` sees an empty (clamped) range.
#guard balR l6 0 2 != balR l6 4 2

end Tests.Reflections.EntryBoundaryLocator
