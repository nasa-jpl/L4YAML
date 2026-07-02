/-
# Reflection 527 — a first-entry DISPATCH becomes a whole-window single-entry producer via a
no-interior-boundary certificate

Self-contained companion to `recseqentry_whole_window_seq`
(`L4YAML/Proofs/Output/EmitterScannability/NonemptyStructure.lean`), the bridge that lets the map
width-recursion driver reuse the *seq* entry dispatch for a map pair's key/value sub-blocks.

A body-recursion's dispatch (`recseqentry_window_dispatch_seq`) locates the **first** entry of a body
window `[lo, hi)`: it returns a boundary `m` (`lo < m ≤ hi`, depth-`0`, either the window end or a
`.flowEntry` separator), its minimality, and `RecSeqEntry` of the located prefix `[lo, m)`.  But a map
pair `.key K .value V` splits into a key block `[lo+1, kv)` and a value block `[kv+1, e)`, and each
sub-block oracle owes a *single* `RecSeqEntry` for the **whole** sub-block — not the first entry of a
body.

The reflection: **these are the same producer once the window carries a no-interior-boundary
certificate.**  A map key/value has no top-level comma, so its sub-block has no depth-`0` `.flowEntry`
strictly inside; that single fact forces the dispatch's located `m` to the window END (`m = hi`), so
"the first entry" IS "the whole window".  The certificate is not assumed out of thin air — it is exactly
the *enclosing* recursion's pair-end minimality: `mapPairSkeleton_locate` returns the pair end `e` as the
LEAST depth-`0` boundary after `lo`, so a separator inside a sub-block would be an earlier boundary,
which cannot exist.

This file abstracts the dispatch's output shape (`FirstEntry`), the toy depth function (`bal`), and the
entry predicate (`Entry`), proves the bridge `whole_window` once — the marker-disjunct collapse, verbatim
from the real proof — then runs it on a concrete single-value window `[ sc ]` and exhibits the negative:
a window WITH an interior separator, where the certificate genuinely fails.
-/

namespace DispatchFirstEntryToWholeWindow

set_option autoImplicit false

/-- Toy flow tokens: `sc` a scalar (content), `fe` the depth-`0` entry separator, `op`/`cl` a bracket
    pair (a nested collection whose interior commas live at depth `≥ 1`). -/
inductive Tok | sc | fe | op | cl
  deriving DecidableEq

def tokAt (l : List Tok) (i : Nat) : Tok := l.getD i .sc

/-- Toy running bracket balance on `[lo, hi)`: `+1` per `op`, `-1` per `cl`, `0` otherwise.  The toy of
    `flowBracketBalance`; a depth-`0` position is where this returns to `0`. -/
def bal (l : List Tok) (lo hi : Nat) : Int :=
  (List.range (hi - lo)).foldl
    (fun acc i => acc + (match tokAt l (lo + i) with | .op => 1 | .cl => -1 | _ => 0)) 0

/-- The DISPATCH output shape — `recseqentry_window_dispatch_seq`'s existential, abstracted.  A body
    locator over `[lo, hi)`: the first entry ends at a depth-`0` boundary `m` that is either the window
    end or a `.fe` separator, no earlier position is such a boundary (minimality), and the located prefix
    `[lo, m)` is an `Entry`. -/
def FirstEntry (Entry : Nat → Nat → Prop) (l : List Tok) (lo hi : Nat) : Prop :=
  ∃ m, lo < m ∧ m ≤ hi ∧ bal l lo m = 0 ∧ (m = hi ∨ tokAt l m = .fe) ∧
    (∀ k, lo < k → k < m → ¬ (bal l lo k = 0 ∧ (k = hi ∨ tokAt l k = .fe))) ∧
    Entry lo m

/-! ## The bridge: dispatch (first entry) + no-interior-boundary ⟹ whole-window single entry. -/

/-- **The whole-window producer.**  Given the dispatch's first-entry output and the certificate that no
    depth-`0` `.fe` separator lies strictly inside `[lo, hi)`, the located boundary is forced to the
    window end and the first entry IS the whole window: `Entry lo hi`.

    The proof is the real lemma's marker-disjunct collapse verbatim: the boundary disjunct `m = hi ∨
    tokAt l m = .fe` gives the goal in the first horn; in the second, `m < hi` is refuted by the
    certificate at `k = m`, and `m ≥ hi` collapses to `m = hi` against the dispatch's `m ≤ hi`.  Note the
    IH the real dispatch carries (delivering `RecSeqBody` for narrower windows) is threaded UNTOUCHED —
    this brick is silent on the driver's cross-deliverable knot, isolating boundary-pinning from
    IH-sourcing. -/
theorem whole_window {Entry : Nat → Nat → Prop} {l : List Tok} {lo hi : Nat}
    (h_disp : FirstEntry Entry l lo hi)
    (h_noInterior : ∀ k, lo < k → k < hi → ¬ (bal l lo k = 0 ∧ tokAt l k = .fe)) :
    Entry lo hi := by
  obtain ⟨m, h_lo_m, h_m_hi, h_bal_m, h_marker, _h_min, h_entry⟩ := h_disp
  have h_m_eq : m = hi := by
    rcases h_marker with h | h
    · exact h
    · rcases Nat.lt_or_ge m hi with h_lt | h_ge
      · exact absurd ⟨h_bal_m, h⟩ (h_noInterior m h_lo_m h_lt)
      · omega
  rw [h_m_eq] at h_entry; exact h_entry

/-! ## A concrete single-value window `[ sc ]` — the key sub-block of a map pair. -/

/-- A bracketed scalar `[ sc ]`: window `[0, 3)`, balance returns to `0` only at the end (`op` `+1`,
    `sc` `0`, `cl` `-1`), no `.fe` anywhere. -/
def keyBlock : List Tok := [.op, .sc, .cl]

#guard bal keyBlock 0 3 == (0 : Int)   -- depth-`0` at the window end
#guard bal keyBlock 0 1 == (1 : Int)   -- depth-`1` after the opener
#guard bal keyBlock 0 2 == (1 : Int)   -- depth-`1` over the interior scalar
#guard tokAt keyBlock 1 == Tok.sc      -- no `.fe` at the interior positions
#guard tokAt keyBlock 2 == Tok.cl

/-- Toy entry predicate: the located prefix `[lo, m)` is "the whole `keyBlock`" exactly when it spans
    `[0, 3)`.  (Stand-in for `RecSeqEntry ((take m).drop lo)`.) -/
def Entry (lo m : Nat) : Prop := lo = 0 ∧ m = 3

/-- The dispatch result for `keyBlock`: its single entry ends at the window end `m = 3` (depth-`0`,
    `m = hi`), no earlier boundary, and the located prefix is the whole block. -/
theorem keyBlock_dispatch : FirstEntry Entry keyBlock 0 3 :=
  ⟨3, by omega, by omega, by decide, Or.inl rfl,
    by intro k hk1 hk2
       have hk' : k = 1 ∨ k = 2 := by omega
       rcases hk' with rfl | rfl <;> rintro ⟨h, _⟩ <;> exact absurd h (by decide),
    ⟨rfl, rfl⟩⟩

/-- The certificate: no depth-`0` `.fe` strictly inside `[0, 3)` — the two interior positions are `.sc`
    and `.cl`, neither a `.fe`. -/
theorem keyBlock_noInterior :
    ∀ k, 0 < k → k < 3 → ¬ (bal keyBlock 0 k = 0 ∧ tokAt keyBlock k = .fe) := by
  intro k hk1 hk2
  have hk' : k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl <;> rintro ⟨_, h⟩ <;> exact absurd h (by decide)

/-- Running the bridge on `keyBlock`: the whole window `[0, 3)` is the single entry. -/
theorem keyBlock_whole : Entry 0 3 :=
  whole_window keyBlock_dispatch keyBlock_noInterior

/-! ## The negative: a window WITH an interior separator — the certificate genuinely fails. -/

/-- Two scalars separated by a depth-`0` `.fe`: `sc , sc` — a body of TWO entries, not one. -/
def twoEntries : List Tok := [.sc, .fe, .sc]

#guard bal twoEntries 0 1 == (0 : Int)   -- the `.fe` at index 1 sits at depth `0` …
#guard tokAt twoEntries 1 == Tok.fe      -- … and it IS a separator

/-- The interior boundary that BLOCKS the bridge: at `k = 1` the depth is `0` and the token is `.fe`, so
    `whole_window`'s certificate `h_noInterior` is FALSE here — the dispatch would stop at `m = 1 < hi`,
    and the window is correctly NOT a single entry. -/
theorem twoEntries_interiorBoundary : bal twoEntries 0 1 = 0 ∧ tokAt twoEntries 1 = .fe := by
  decide

theorem twoEntries_certificate_fails :
    ¬ (∀ k, 0 < k → k < 3 → ¬ (bal twoEntries 0 k = 0 ∧ tokAt twoEntries k = .fe)) := by
  intro h
  exact h 1 (by omega) (by omega) twoEntries_interiorBoundary

/-- The punchline: the dispatch's existential collapses to the whole window precisely under the
    no-interior-boundary certificate. -/
theorem demo {Entry : Nat → Nat → Prop} {l : List Tok} {lo hi : Nat}
    (h_disp : FirstEntry Entry l lo hi)
    (h_noInterior : ∀ k, lo < k → k < hi → ¬ (bal l lo k = 0 ∧ tokAt l k = .fe)) :
    Entry lo hi :=
  whole_window h_disp h_noInterior

end DispatchFirstEntryToWholeWindow

/-- info: 'DispatchFirstEntryToWholeWindow.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DispatchFirstEntryToWholeWindow.demo
