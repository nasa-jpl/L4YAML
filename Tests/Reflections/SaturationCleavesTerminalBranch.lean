/-!
# Reflection 381 — a window-search recursion's TERMINAL (separator-free) branch is cleaved by
container SATURATION; SHORT separator-free entries close VACUOUSLY by slice arithmetic, with no
structural refutation at all

Self-contained core-Lean toy of L4YAML BRICK D's two short-entry HEAD cells
(`nestedSeq_recseqentry_locate_{scalar,seqEmpty}_head_step`).

A bottom-up locator recurses over a body split into a CONS branch (head entry `e` has a SUCCESSOR
past a separator) and a TERMINAL / HEAD branch (`body = e`, NO separator, no successor).  In the
TERMINAL branch a separator-free container SATURATES its own window: the slice forces
`off + e.length = H` (the entry spans the whole `[off, H)` span).  The target being searched for is
a STRICTLY-INTERIOR window `[a, b)` with `off + 1 ≤ a < b < H`.  Since `H = off + e.length`, split
the branch by `Nat.lt_or_ge a (off + e.length)`:

* `a ≥ off + e.length` half — pure ARITHMETIC CONTRADICTION (`a ≥ H > b > a`), FREE from saturation,
  needs NO structure; it even subsumes the boundary exclusion the interior branch needs.
* `a < off + e.length` half — the genuine LEAF/DESCEND interior, refuted by the structural bricks.

For a SHORT entry the interior half is itself empty, so the WHOLE terminal branch is pure `omega`:
`e.length = 1` (scalar) ⇒ `off+1 ≤ a < b < off+1`; `e.length = 2` (empty seq) ⇒ `off+1 ≤ a < b <
off+2`.  Only `e.length ≥ 3` leaves interior room.  Don't reflexively refute the terminal branch
structurally — derive the cleave from the slice-length equation; short entries fall out for free.
-/

namespace Tests.Reflections.SaturationCleavesTerminalBranch

set_option autoImplicit false

/-! ## The saturation equation — a separator-free entry spans its window.

In the real locator this is `body.length = ((tokens.toList.take H).drop off).length`, which with
`H ≤ tokens.size` simplifies to `H - off`.  The toy states the post-simplification fact. -/

/-- The slice length of a separator-free window: `body.length = H - off` (saturation). -/
theorem saturation_slice_len (off H bodyLen : Nat) (h_sat : bodyLen = H - off)
    (h_bound : off + bodyLen ≤ H) : off + bodyLen = H := by omega

/-! ## The cleave — `Nat.lt_or_ge` splits the terminal branch at the container's end. -/

/-- The terminal branch splits into the structural interior `a < off + L` and the FREE arithmetic
    contradiction region `a ≥ off + L` — for ANY entry length `L`, pure `omega` plumbing. -/
theorem cleave (off L a : Nat) : (a < off + L) ∨ (off + L ≤ a) := Nat.lt_or_ge a (off + L)

/-- The past-the-container half is a CONTRADICTION, with NO appeal to structure or the boundary
    exclusion: a target end `b` strictly below the window top `H = off + L` cannot have its start
    `a` at or beyond `off + L`. -/
theorem past_container_is_contra (off L a b H : Nat) (h_sat : off + L = H)
    (h_ab : a < b) (h_hi : b < H) (h_ge : off + L ≤ a) : False := by omega

/-! ## POSITIVE (long entry, `L = 4`) — the interior half is INHABITED, so the branch is NOT
    vacuous; it genuinely needs the structural bricks on the `a < off + L` side. -/

/-- At `L = 4` (off = 4, so `H = 8`) an interior target `[5, 6)` exists and lands in the structural
    half `a < off + L` — the half the real proof closes with BRICK B, not `omega`. -/
theorem long_interior_inhabited : (4 + 1 ≤ 5 ∧ (5 : Nat) < 6 ∧ 6 < 8) ∧ (5 : Nat) < 4 + 4 := by
  refine ⟨⟨by omega, by omega, by omega⟩, by omega⟩

/-! ## DEGENERATE / NEGATIVE (short entries) — the WHOLE terminal branch is vacuous by `omega`. -/

/-- `e.length = 1` (a bare scalar `[t]`): saturation `off + 1 = H` plus the strict target window
    `off+1 ≤ a < b < H` is impossible — `off+1 ≤ a < b < off+1`.  This IS the whole scalar-HEAD cell:
    `exfalso; … omega`. -/
theorem scalar_head_vacuous (off a b H : Nat) (h_sat : off + 1 = H)
    (h_lo : off + 1 ≤ a) (h_ab : a < b) (h_hi : b < H) : False := by omega

/-- `e.length = 2` (an empty seq `[op, cl]`): saturation `off + 2 = H`, so `off+1 ≤ a < b < off+2` —
    only `off+1` fits, leaving no room for `a < b`.  The whole seqEmpty-HEAD cell. -/
theorem seqEmpty_head_vacuous (off a b H : Nat) (h_sat : off + 2 = H)
    (h_lo : off + 1 ≤ a) (h_ab : a < b) (h_hi : b < H) : False := by omega

/-- Why `L = 3` is the threshold: at `L = 3` (off = 4, H = 7) an interior target `[5, 6)` DOES fit,
    so the short-entry vacuity argument no longer applies — the branch must use structure. -/
theorem threshold_at_3 : (4 + 1 ≤ 5 ∧ (5 : Nat) < 6 ∧ 6 < 7) := by
  refine ⟨by omega, by omega, by omega⟩

/-- The terminal-branch cost as a function of the entry metric `L`: `0` structural refutations for
    short entries (pure `omega`), `1` interior region (LEAF/DESCEND via the bricks) for `L ≥ 3`.
    Mirrors `ref-metric-minimum-collapses-dispatch`'s decreasing arm-count on the CONS branch. -/
def structuralRefutationsNeeded (L : Nat) : Nat := if L ≤ 2 then 0 else 1

#guard structuralRefutationsNeeded 1 == 0    -- scalar HEAD: pure omega
#guard structuralRefutationsNeeded 2 == 0    -- empty-seq HEAD: pure omega
#guard structuralRefutationsNeeded 3 == 1    -- minimal nonempty-seq HEAD: needs interior bricks
#guard structuralRefutationsNeeded 4 == 1    -- seq/map HEAD: needs interior bricks
#guard !decide (structuralRefutationsNeeded 1 == 1)    -- short ≠ the long-entry cost

end Tests.Reflections.SaturationCleavesTerminalBranch
