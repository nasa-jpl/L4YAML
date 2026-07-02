/-!
# Reflection 480 — the depth-`0` premise belongs to the LOCATING SCAN, not to any family member;
# take the located close as INPUT and EVERY child-window constructor is DEPTH-AGNOSTIC.

Self-contained (core Lean, no `L4YAML` import) toy recording the brick R480 landed:
`flowBodyWindow_child_bracket_at`
(`L4YAML/Proofs/Output/EmitterScannability/NonemptyStructure.lean`), the WINDOW member of the "given
close" child-bracket trio that the (α) `enclosingLocate` assemble feeds uniformly — completing the trio
`{flowBodyWindow_child_bracket_at, flowBodyContentDeep_child_bracket, flowBodyContent_child_bracket}`.

**The setup.**  A child bracket `[`/`{` opens at `k` inside the body window `[lo, hi)`, matching close at
`j`.  `flowBodyWindow_child_bracket` LOCATES `j` itself via the forward scan
`flowBracketBalance_matching_close`, and that scan is the SOLE reason it needs the depth-`0` discriminator
`balance lo k = 0`: the scan reads the matching close off the `lo`-keyed running balance returning to
depth `0`, which only coincides with the bracket's OWN close when `k` itself sits at depth `0`.

**The brick — the SCAN owns the depth debt.**  R479 showed the PROJECTED content member is depth-free;
this shows the directly-CONSTRUCTED window member is too.  Remove the scan — take the located close `j`,
its interior balance, its closer delta, and the CHILD-ORIGIN floor (`balance k i ≥ 1`, keyed on `k`) as
INPUTS — and the construction of `FlowBodyWindow tokens k (j+1)` carries NO `balance lo k = 0`:

* `balanced` is `(+1) + 0 + (-1) = 0` (opener push, balanced interior, closer pop) — pure composition.
* the `dyck` floor is `≥ 0` on `[k, j+1]`: `0` at the two endpoints, `≥ 1` on the strict interior
  `(k, j]` DIRECTLY from the child-origin floor (no re-base through `balance lo k` — the step the scan
  version needed).
* `wellTyped` transports from the parent over `[k, j+1) ⊆ [lo, hi)` by the balanced-subrange transporter.

So the depth-`0` premise was never a property of the window's CONTENT — it was a precondition of the
LOCATOR.  The family splits into ONE depth-needing locator + THREE depth-free "given close" constructors,
all keyed on the child origin `k`.  This toy abstracts balance as `childBal B k i = B i - B k` (`B` =
`balance lo ·`) so the depth dependence is visible as the `- B k` term: the constructor cancels it
(every fact is a `childBal`), while the scan's return condition `B (j+1) = 0` keeps it.
-/

namespace ScanOwnsTheDepthDebt

set_option autoImplicit false

/-- Balance from the CHILD origin `k`, written as the outer balance `B` minus its value at `k`.  The
    `- B k` term is exactly the depth offset the scan must pay and the constructor cancels. -/
def childBal (B : Nat → Int) (k i : Nat) : Int := B i - B k

/-- The interior FLOOR, keyed on the CHILD origin `k`: every strict-interior prefix sits at `≥ 1`. -/
def Floor (B : Nat → Int) (k j : Nat) : Prop := ∀ i, k + 1 ≤ i → i ≤ j → childBal B k i ≥ 1

/-- The WINDOW member's two child-keyed fields — a stand-in for `FlowBodyWindow`'s `balanced` / `dyck`. -/
structure Win (B : Nat → Int) (k j : Nat) : Prop where
  balanced : childBal B k (j + 1) = 0
  dyck : ∀ i, k ≤ i → i ≤ j + 1 → childBal B k i ≥ 0

/-- **The "given close" constructor — DEPTH-AGNOSTIC** (mirrors `flowBodyWindow_child_bracket_at`).  Takes
    the located close `j` (closer delta `h_close`), the interior balance `h_inner`, the opener delta
    `h_open`, and the child-origin floor — and builds `Win B k j` with NO `B k = 0` hypothesis.
    `balanced` cancels `B k` by composition; `dyck` reads `≥ 1` off the floor directly. -/
theorem win_given_close (B : Nat → Int) (k j : Nat)
    (h_open : childBal B k (k + 1) = 1)
    (h_inner : childBal B (k + 1) j = 0)
    (h_close : childBal B j (j + 1) = -1)
    (h_floor : Floor B k j) :
    Win B k j := by
  refine ⟨?_, ?_⟩
  · -- balanced: `B(j+1) - B k = (+1) + 0 + (-1) = 0`; `omega` cancels the depth term `B k`.
    simp only [childBal] at h_open h_inner h_close ⊢
    omega
  · -- dyck `≥ 0` on `[k, j+1]`: endpoints `0`, strict interior `≥ 1` straight from the floor.
    intro i hi1 hi2
    rcases Nat.lt_or_ge k i with hki | hki
    · rcases Nat.lt_or_ge i (j + 1) with hij | hij
      · -- `k < i ≤ j`: the child-origin floor gives `≥ 1` (no re-base through `B k`).
        have hf := h_floor i (by omega) (by omega)
        simp only [childBal] at hf ⊢
        omega
      · -- `i = j + 1`: the window is balanced.
        have hij' : i = j + 1 := by omega
        subst hij'
        simp only [childBal] at h_open h_inner h_close ⊢
        omega
    · -- `i = k`: the empty prefix is `0`.
      have hik : i = k := by omega
      subst hik
      simp only [childBal]
      omega

/-- A concrete outer balance `B = balance lo ·` for the stream `… [ [ x ] ] …` (an inner bracket nested
    one level in): `0,1,2,2,1,0,…`.  The inner opener sits at `k = 1`, at OUTER depth `1` (`Bex 1 = 1`),
    and its matching close is `j = 3`. -/
def Bex : Nat → Int := fun i =>
  if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 2 else if i = 4 then 1 else 0

/-- **The constructor is DEPTH-FREE** — `win_given_close` builds the inner window `Win Bex 1 3` even
    though the child origin `k = 1` sits at outer depth `1` (`Bex 1 = 1 ≠ 0`).  No `Bex 1 = 0` needed. -/
example : Win Bex 1 3 :=
  win_given_close Bex 1 3
    (by simp [childBal, Bex])      -- childBal Bex 1 2 = Bex 2 - Bex 1 = 2 - 1 = 1
    (by simp [childBal, Bex])      -- childBal Bex 2 3 = Bex 3 - Bex 2 = 2 - 2 = 0
    (by simp [childBal, Bex])      -- childBal Bex 3 4 = Bex 4 - Bex 3 = 1 - 2 = -1
    (by                            -- Floor: childBal Bex 1 i ≥ 1 on i ∈ {2, 3}
      intro i h1 h2
      have : i = 2 ∨ i = 3 := by omega
      rcases this with h | h <;> subst h <;> simp [childBal, Bex])

/-- **The SCAN owns the depth debt.**  The scan locates the close as "first return to OUTER depth `0`"
    (`Bex (j+1) = 0`).  At the nested child origin `k = 1` (`Bex 1 ≠ 0`) it MISSES the true close `j = 3`
    (`Bex 4 = 1 ≠ 0`) and FIRES at the ENCLOSING close `j = 4` (`Bex 5 = 0`) — the wrong bracket, whose
    child-balance `childBal Bex 1 5 = -1 ≠ 0` is not even a close.  This is exactly the failure the
    depth-`0` premise rules out — and it lives in the LOCATOR, never in `win_given_close`. -/
theorem scan_misses_true_close_when_nested :
    Bex (3 + 1) ≠ 0 ∧ Bex (4 + 1) = 0 ∧ childBal Bex 1 (4 + 1) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Bex]
  · simp [Bex]
  · simp [childBal, Bex]

/-- **Depth-`0` is what ALIGNS the scan with the true close.**  When `B k = 0`, the scan's return
    condition `B (j+1) = 0` coincides with the child-balance close `childBal B k (j+1) = 0` for every `j`
    — the `- B k` offset vanishes.  So the scan is correct precisely at depth `0`; the constructor never
    needed the alignment because it consumes the close already located. -/
theorem scan_aligns_at_depth_zero (B : Nat → Int) (k j : Nat) (h_depth : B k = 0) :
    B (j + 1) = 0 ↔ childBal B k (j + 1) = 0 := by
  simp only [childBal, h_depth]
  omega

/-- **The floor is LOAD-BEARING** (the depth-freedom is genuine, not vacuous).  Drop it and an interior
    dip below child-depth `0` breaks `dyck`: here `B` dips to child-balance `-1` at the interior `i = 2`,
    so `Win`'s `dyck` would demand `childBal ≥ 0` where it is `-1`. -/
def Bbad : Nat → Int := fun i => if i = 2 then (-1 : Int) else 0

theorem floor_is_load_bearing : ¬ Win Bbad 1 3 := by
  intro h
  have hd := h.dyck 2 (by omega) (by omega)
  simp [childBal, Bbad] at hd

end ScanOwnsTheDepthDebt
