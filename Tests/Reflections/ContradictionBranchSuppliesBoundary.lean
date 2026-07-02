/-!
# Reflection 428 — the contradiction branch supplies its own boundary fact

Self-contained (core Lean, no `L4YAML` import) toy of the R428 finding.

To discharge a "no-X-at-the-boundary" residual BY CONTRADICTION, do NOT try to source an
UNCONDITIONAL helper fact about the boundary — it may be FALSE off the contradiction branch.
Instead derive the helper FROM the negated-goal assumption itself: the assumption typically pins a
structural quantity that makes the helper hold *locally, in that branch only*.

The L4YAML case (R428).  The separator-adjacency emit-wrapper must prove the pre-close token is not a
trailing separator: `tokens[size-3] ≠ .flowEntry`.  The first attempt (R419,
`noTrailingSep_preClose_of_carrier`) demanded the boundary balance `flowBracketBalance tokens 2
(size-3) = 0` as an UNCONDITIONAL hypothesis.  But that fact is FALSE in general: when the sequence's
last element is a nested collection the pre-close token is a closing `]`/`}` (bracket-delta `-1`), so
the pre-close pfx balance is `+1`, not `0`.  The fix: refute by contradiction — ASSUME
`tokens[size-3] = .flowEntry`; that token has bracket-delta `0`, so the one-step balance recurrence
`outer = pfx + delta(preClose)` collapses the pfx balance to the outer balance (`= 0`).  The
boundary balance is not a free-standing fact, it is a CONSEQUENCE of the very separator assumption the
proof is refuting.  Then the structure's depth-`0` successor conjunct at that position forces the
successor to be content (seq) / a `.key` (map) — contradicting the close token.

The toy below models exactly that, with `Nat` "tokens" (0 = separator, 1 = open, 2 = close,
3 = scalar/content, 4 = key) and an `Int` bracket balance:

* `preClose_balance_zero_of_sep` — the SHARED kernel: the boundary balance is `0` only IN THE BRANCH
  where the pre-close token is a separator (delta `0`).  Off that branch it is false (a `#guard`
  exhibits the close-bracket counterexample, pfx `= 1`).
* `preClose_not_sep` / `preClose_not_sep_map` — the two AXES: the same kernel, but the final
  token-clash differs (close vs content on the seq, close vs key on the map), each read off the
  axis-specific successor-pattern conjunct.
-/

namespace Tests.Reflections.ContradictionBranchSuppliesBoundary

set_option autoImplicit false

/-- Toy bracket-delta of a "token": open `1` pushes `+1`, close `2` pops `-1`, everything else
    (separator `0`, scalar `3`, key `4`) is balance-neutral.  Mirror of `flowBracketDelta`. -/
def delta : Nat → Int
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- A separator (token `0`) is balance-neutral — the load-bearing fact (mirror of
    `flowBracketDelta_flowEntry : flowBracketDelta .flowEntry = 0`). -/
theorem delta_sep : delta 0 = 0 := rfl

/-! ## The shared kernel — the boundary balance holds only in the contradiction branch. -/

/-- **The boundary balance is `0` IN THE BRANCH where the pre-close token is a separator.**  Given the
    outer balance `0` and the one-step recurrence `outer = pfx + delta preClose`, the *separator*
    assumption `preClose = 0` (delta `0`) collapses `pfx` to the outer balance.  This is the toy of
    `preClose_balance_zero_of_flowEntry` — the kernel BOTH axes' emit-wrappers share. -/
theorem preClose_balance_zero_of_sep
    (outer pfx : Int) (preClose : Nat)
    (h_outer : outer = 0)
    (h_rec : outer = pfx + delta preClose)
    (h_sep : preClose = 0) :
    pfx = 0 := by
  subst h_sep h_outer
  rw [delta_sep] at h_rec
  omega

-- **NEGATIVE** — the boundary balance is NOT an unconditional fact.  When the pre-close token is a
-- close bracket (`2`, delta `-1`) and the outer balance is `0`, the pfx balance is `+1`, not `0`.
-- So the R419 route's unconditional `h_bal : pfx = 0` hypothesis is *unsatisfiable* here — which is
-- exactly why the fact must be derived inside the separator branch, not assumed.
#guard delta 2 == (-1 : Int)
#guard (let outer : Int := 0; let preClose := 2; let pfx := outer - delta preClose; pfx == 1)

/-! ## The two axes — same kernel, different final token-clash. -/

/-- Only a scalar (`3`) is flow content (toy of `isFlowContentStart`). -/
def isContent (x : Nat) : Prop := x = 3
/-- Only a key marker (`4`) is a `.key` (toy of the map body's `= .key` successor). -/
def isKey (x : Nat) : Prop := x = 4

/-- **SEQ axis** — refute the pre-close separator via the seq's body-successor conjunct
    (`h_pattern`: a depth-`0` separator's successor is content).  Derive the boundary balance from the
    separator assumption (the shared kernel), feed it to the conjunct to force the successor to be
    content, then contradict the close (`succ = 2`, not content).  Toy of
    `seqGlobalFlowSeqSepAdj_of_emit`'s inline `h_nts`. -/
theorem preClose_not_sep
    (outer pfx : Int) (preClose succ : Nat)
    (h_outer : outer = 0)
    (h_rec : outer = pfx + delta preClose)
    (h_pattern : preClose = 0 → pfx = 0 → isContent succ)
    (h_close : succ = 2) :
    preClose ≠ 0 := by
  intro h_sep
  have hp := preClose_balance_zero_of_sep outer pfx preClose h_outer h_rec h_sep
  have hc := h_pattern h_sep hp
  rw [h_close] at hc
  simp [isContent] at hc

/-- **MAP axis** — the SAME kernel `preClose_balance_zero_of_sep`, but the final clash differs: the
    map's body-successor conjunct says a depth-`0` separator is followed by a `.key`, not content
    (`h_pattern : … → isKey succ`), and the close `succ = 2` is not a key.  Toy of
    `mapGlobalFlowSeqSepAdj_of_emit`'s inline `h_nts` — demonstrating the boundary kernel is
    axis-blind and only the per-axis successor-pattern conjunct + token-clash change. -/
theorem preClose_not_sep_map
    (outer pfx : Int) (preClose succ : Nat)
    (h_outer : outer = 0)
    (h_rec : outer = pfx + delta preClose)
    (h_pattern : preClose = 0 → pfx = 0 → isKey succ)
    (h_close : succ = 2) :
    preClose ≠ 0 := by
  intro h_sep
  have hp := preClose_balance_zero_of_sep outer pfx preClose h_outer h_rec h_sep
  have hc := h_pattern h_sep hp
  rw [h_close] at hc
  simp [isKey] at hc

end Tests.Reflections.ContradictionBranchSuppliesBoundary
