/-
# Reflection 526 — one separator-successor fact, two descend-tail obligations, opposite polarity

Self-contained companion to `recmapbody_map_descend_tail`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the map twin of
`recseqbody_seq_descend_tail` (R511).

A body-recursion driver, after locating a depth-`0` `.flowEntry` pair/entry separator `m`, must DESCEND
its per-window guard to the suffix `[m+1, hi)`.  That descent has TWO obligations:

  * **O1 — suffix non-degeneracy** (`m + 1 < hi`): there is no trailing separator, so the suffix is a
    real window, not empty.
  * **O2 — guard advance**: re-establish the structural guard (`FlowBodyContentDeep…`) at the new head
    `m + 1`.

The reflection: **both obligations are discharged by ONE per-window fact — the separator's successor
token class — and the seq and map twins differ only in WHICH provider supplies it and its POLARITY.**

  * The **seq** edge reads the successor from `FlowBodyContent.feContentStart`: the `.flowEntry` is
    followed by a *content-start*.  That single fact (O1) contradicts `tokens[hi] = .flowSequenceEnd`
    (a close is not content) at `m + 1 = hi`, and (O2) yields the deep advance's `≠ .key` premise.
  * The **map** edge reads the successor from `MapBodyProps.after_fe`: the `.flowEntry` is followed by a
    `.key`.  That single fact (O1) contradicts `tokens[hi] = .flowMappingEnd` (`.key ≠ .flowMappingEnd`)
    at `m + 1 = hi`, and (O2) IS the deep advance's `tokens[m+1] = .key` child-head premise, supplied
    verbatim.

So the descend-tail is a single proof skeleton parameterized by the successor class `Succ` and the
window-close token `closeTok`, with the lone side condition `¬ Succ closeTok` (the successor class is
disjoint from the close).  This file abstracts that skeleton, proves the dual-use `descend_tail` once,
and instantiates it at both polarities — `Succ := (· = .key)` / `closeTok := .mapEnd` for maps,
`Succ := isContent` / `closeTok := .seqEnd` for sequences — plus a concrete two-pair map body.
-/

namespace DescendTailDualUseSeparatorSuccessor

set_option autoImplicit false

/-- Toy flow tokens: `key`/`val` map separators, `sc` a scalar (content), `fe` the entry separator,
    `mapEnd`/`seqEnd` the two window-close markers. -/
inductive Tok | key | val | sc | fe | mapEnd | seqEnd
  deriving DecidableEq

def tokAt (l : List Tok) (i : Nat) : Tok := l.getD i .sc

/-- The toy "deep content guard", parameterized by the allowed separator-successor class `Succ`
    (the map analog uses `(· = .key)`, the seq analog a content-start predicate).  The body head is a
    `Succ` token, and every depth-`0` `.fe` separator is followed by a `Succ` token.  This is the toy of
    `FlowBodyContentDeepMap` / `FlowBodyContentDeepSeq`, whose advance edges read exactly the
    separator-successor. -/
structure DeepGuard (Succ : Tok → Prop) (l : List Tok) (lo hi : Nat) : Prop where
  head : Succ (tokAt l lo)
  sepSucc : ∀ k, lo ≤ k → k + 1 < hi → tokAt l k = .fe → Succ (tokAt l (k + 1))

/-! ## The two obligations, each consuming the lone separator-successor fact. -/

/-- **O1 — suffix non-degeneracy.**  The located separator's successor is a `Succ` token; the window
    close `closeTok` is NOT (`h_disj`); so `m + 1 = hi` is impossible.  Toy of the seq edge's
    "`tokens[hi] = .flowSequenceEnd` is not content-start" and the map edge's
    "`tokens[hi] = .flowMappingEnd` ≠ `.key`". -/
theorem no_trailing_sep {Succ : Tok → Prop} {l : List Tok} {closeTok : Tok} {m hi : Nat}
    (h_succ : Succ (tokAt l (m + 1)))
    (h_close : tokAt l hi = closeTok) (h_disj : ¬ Succ closeTok)
    (h_m1_le : m + 1 ≤ hi) :
    m + 1 < hi := by
  rcases Nat.lt_or_ge (m + 1) hi with h | h
  · exact h
  · exfalso
    have h_eq : m + 1 = hi := by omega
    rw [h_eq, h_close] at h_succ
    exact h_disj h_succ

/-- **O2 — guard advance.**  Re-establish the guard on the suffix `[m+1, hi)`, taking the SAME
    separator-successor `h_succ : Succ (tokAt l (m+1))` as the new head.  Toy of
    `flowBodyContentDeepMap_advance` (child head `tokens[m+1] = .key`) /
    `flowBodyContentDeepSeq_advance` (child head a content-start). -/
theorem guard_advance {Succ : Tok → Prop} {l : List Tok} {lo hi m : Nat}
    (h_g : DeepGuard Succ l lo hi)
    (h_lo_m : lo ≤ m) (_h_m1_hi : m + 1 < hi)
    (h_succ : Succ (tokAt l (m + 1))) :
    DeepGuard Succ l (m + 1) hi where
  head := h_succ
  sepSucc := fun k hk1 hk2 hfe => h_g.sepSucc k (by omega) (by omega) hfe

/-! ## The dual-use descend-tail: ONE `h_succ` feeds BOTH obligations. -/

/-- **The descend-tail skeleton.**  Given the per-window guard, the window close, the disjointness
    `¬ Succ closeTok`, and the located separator with its successor fact `h_succ`, narrow the guard to
    the suffix and prove it non-degenerate — `h_succ` is consumed TWICE (by `no_trailing_sep` and by
    `guard_advance`), the whole content of the reflection. -/
theorem descend_tail {Succ : Tok → Prop} {l : List Tok} {closeTok : Tok} {lo hi m : Nat}
    (h_g : DeepGuard Succ l lo hi)
    (h_close : tokAt l hi = closeTok) (h_disj : ¬ Succ closeTok)
    (h_lo_m : lo ≤ m)
    (h_succ : Succ (tokAt l (m + 1)))
    (h_m1_le : m + 1 ≤ hi) :
    m + 1 < hi ∧ DeepGuard Succ l (m + 1) hi :=
  have h_m1_hi : m + 1 < hi := no_trailing_sep h_succ h_close h_disj h_m1_le
  ⟨h_m1_hi, guard_advance h_g h_lo_m h_m1_hi h_succ⟩

/-! ## The two POLARITY instances — same skeleton, different provider & close. -/

/-- **MAP polarity.**  `Succ := (· = .key)`, `closeTok := .mapEnd`; the disjointness is
    `.mapEnd ≠ .key`.  The successor fact IS the deep advance's child head. -/
theorem descend_tail_map {l : List Tok} {lo hi m : Nat}
    (h_g : DeepGuard (· = .key) l lo hi)
    (h_close : tokAt l hi = .mapEnd)
    (h_lo_m : lo ≤ m)
    (h_succ : tokAt l (m + 1) = .key)
    (h_m1_le : m + 1 ≤ hi) :
    m + 1 < hi ∧ DeepGuard (· = .key) l (m + 1) hi :=
  descend_tail h_g h_close (by decide) h_lo_m h_succ h_m1_le

/-- Toy content-start class (a scalar head). -/
def isContent (t : Tok) : Prop := t = .sc

instance : DecidablePred isContent := fun t => decEq t .sc

/-- **SEQ polarity.**  `Succ := isContent`, `closeTok := .seqEnd`; the disjointness is
    `¬ isContent .seqEnd` (a close is not content).  The successor fact is the content head; in the
    real seq edge the deep advance further reads `≠ .key` off it. -/
theorem descend_tail_seq {l : List Tok} {lo hi m : Nat}
    (h_g : DeepGuard isContent l lo hi)
    (h_close : tokAt l hi = .seqEnd)
    (h_lo_m : lo ≤ m)
    (h_succ : isContent (tokAt l (m + 1)))
    (h_m1_le : m + 1 ≤ hi) :
    m + 1 < hi ∧ DeepGuard isContent l (m + 1) hi :=
  descend_tail h_g h_close (by decide) h_lo_m h_succ h_m1_le

/-! ## A concrete two-pair map body, run through the map descend-tail. -/

/-- `{ a : b , c : d }` interior + close: `key sc val sc fe key sc val sc mapEnd`.
    Body window `[0, 9)`, the depth-`0` `.fe` pair separator at index `4`, its successor `.key` at `5`,
    the close `.mapEnd` at `9`. -/
def mapList : List Tok := [.key, .sc, .val, .sc, .fe, .key, .sc, .val, .sc, .mapEnd]

#guard tokAt mapList 0 == Tok.key      -- head is `.key`
#guard tokAt mapList 4 == Tok.fe       -- pair separator
#guard tokAt mapList 5 == Tok.key      -- successor is `.key` (the child head)
#guard tokAt mapList 9 == Tok.mapEnd   -- window close

/-- The concrete map guard holds on `[0, 9)`: head `.key`, and the only depth-`0` `.fe` (at `4`) is
    followed by `.key`. -/
theorem mapGuard : DeepGuard (· = .key) mapList 0 9 where
  head := by decide
  sepSucc := by
    intro k _ hk hfe
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hfe <;> decide

/-- Running the map descend-tail on the concrete body: the suffix `[5, 9)` is non-degenerate and still
    carries the map guard. -/
theorem mapSuffix : 4 + 1 < 9 ∧ DeepGuard (· = .key) mapList (4 + 1) 9 :=
  descend_tail_map (lo := 0) mapGuard (by decide) (by omega) (by decide) (by omega)

/-- The punchline: the descend-tail's two outputs both flow from the single `h_succ`, abstractly. -/
theorem demo {Succ : Tok → Prop} {l : List Tok} {closeTok : Tok} {lo hi m : Nat}
    (h_g : DeepGuard Succ l lo hi)
    (h_close : tokAt l hi = closeTok) (h_disj : ¬ Succ closeTok)
    (h_lo_m : lo ≤ m)
    (h_succ : Succ (tokAt l (m + 1)))
    (h_m1_le : m + 1 ≤ hi) :
    m + 1 < hi ∧ DeepGuard Succ l (m + 1) hi :=
  descend_tail h_g h_close h_disj h_lo_m h_succ h_m1_le

end DescendTailDualUseSeparatorSuccessor

/-- info: 'DescendTailDualUseSeparatorSuccessor.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DescendTailDualUseSeparatorSuccessor.demo
