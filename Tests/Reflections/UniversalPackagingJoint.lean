/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Reflection 243 — universal packaging is its own consumer joint

Self-contained (core Lean, no `L4YAML` import) runnable demonstration of the principle in
Blueprint Reflection 243: when you package *per-element* results into a **universally-quantified**
consumer structure, the structure's per-field hypotheses are often strictly **weaker** than what
each element's per-element joint actually needs.  That difference is real, and it is exactly the
producer's per-element **deliverable type** — so name it, point the assembler at it, and you collapse
the whole packaging step into the producer's contract *before* writing the producer.

The L4YAML instance: the per-window joints `seqBodyProps_of_located_entry`/`mapBodyProps_of_located_entry`
reduce, for one guarded subrange, body-props to "the opener-window is a `Rec{Seq,Map}Entry`"; the sorry
sites consume the *universal* `FlowSubrangesOk tokens` whose fields supply only the bracket guards, NOT
the `1 ≤ lo` / Dyck / `WellTyped` / located-entry the joints need.  Naming that gap as `SeqLocated`/
`MapLocated` and building `flowSubrangesOk_of_locators` is the R243 move.

This toy strips the situation to its skeleton:

* `G lo hi`        — the universal structure's per-field guard (toy bracket guards).
* `Located lo hi`  — the locate recursion's per-window deliverable (toy `SeqLocated`).  It bundles a
  part **derivable** from `G` (`opener`, toy `1 ≤ lo`) and a part **not** derivable from `G` (`entry`,
  toy stand-in for the located recursive structure / Dyck / `WellTyped`).
* `P lo hi`        — the per-element props (toy `SeqBodyProps`); the joint's output.
* `elemProps_of_located` — the per-element joint (toy `*_of_located_entry`).
* `rangesOk_of_locator`  — the assembler keyed on the locator hypothesis (toy `flowSubrangesOk_of_locators`).

Positive witnesses: where the locate would fire (`entry` holds), `Located`/`P` hold and the joint +
assembler compose.  Negative witnesses: at a window where the *hard* part `entry` fails, `G` still
holds while `P` and `Located` both fail — the gap is real — and there is **no total locator** (which
is precisely why locate is the residual producer, not something the guard discharges for free).

Build: `lake build Tests.Reflections.UniversalPackagingJoint`.
-/

namespace UniversalPackagingJoint

/-- Toy "opener" fact — the part of the deliverable that IS recoverable from the field guard
    (mirrors `1 ≤ lo`, forced by `tokens[lo-1]` being a flow opener). -/
abbrev opener (lo : Nat) : Prop := 1 ≤ lo

/-- Toy "located recursive structure" fact — the genuinely-hard part of the deliverable that is
    NOT implied by the field guard (mirrors the located `RecSeqEntry` / Dyck / `WellTyped`, which the
    locate recursion must establish and the flat bracket guards cannot regenerate).  An arbitrary
    decidable predicate independent of the guard suffices to make the gap concrete. -/
abbrev entry (lo hi : Nat) : Prop := lo + hi ≠ 7

/-- The universally-quantified structure's per-field **guard** (toy `FlowSubrangesOk.seq`/`.map`
    hypotheses): a window plus the recoverable `opener`.  Deliberately weaker than `Located`. -/
abbrev G (lo hi : Nat) : Prop := lo < hi ∧ opener lo

/-- The locate recursion's per-window **deliverable** (toy `SeqLocated`/`MapLocated`): the joint-inputs
    the field omits — here `opener` (recoverable) bundled with `entry` (the true gap). -/
abbrev Located (lo hi : Nat) : Prop := opener lo ∧ entry lo hi

/-- The per-element **props** (toy `SeqBodyProps`) the universal structure's field must yield. -/
abbrev P (lo hi : Nat) : Prop := opener lo ∧ entry lo hi ∧ lo < hi

/-- **The per-element joint** (toy `seqBodyProps_of_located_entry`): consume the located deliverable
    plus the field's own guard, produce the element props.  Note it needs `Located`, not just `G`. -/
theorem elemProps_of_located {lo hi : Nat} (h_loc : Located lo hi) (h_g : G lo hi) : P lo hi :=
  ⟨h_loc.1, h_loc.2, h_g.1⟩

/-- The universally-quantified consumer structure (toy `FlowSubrangesOk`): one field, ranging over all
    windows under the *field guard* `G` only. -/
structure RangesOk : Prop where
  field : ∀ lo hi, G lo hi → P lo hi

/-- **The assembler keyed on the locator** (toy `flowSubrangesOk_of_locators`, the Reflection 243
    move): given the locate recursion's not-yet-built output as a bare universal hypothesis, package
    the per-element joint into the universal structure.  Each field instantiates the locator at the
    guarded window and hands the bundle + the field's own guard to the joint. -/
def rangesOk_of_locator (locate : ∀ lo hi, G lo hi → Located lo hi) : RangesOk :=
  ⟨fun lo hi hg => elemProps_of_located (locate lo hi hg) hg⟩

/-- End-to-end composition (toy of the two sorry sites consuming the assembler's output): the
    assembler, fed any locator, yields the per-element props at every guarded window — no total
    locator instance is required to state this, exactly as `flowSubrangesOk_of_locators` takes the
    locator as a hypothesis. -/
theorem assembler_yields_props (locate : ∀ lo hi, G lo hi → Located lo hi)
    (lo hi : Nat) (hg : G lo hi) : P lo hi :=
  (rangesOk_of_locator locate).field lo hi hg

/-! ## The gap is real — the field guard is strictly weaker than the deliverable / the props -/

/-- **Partially recoverable.**  The `opener` half of the deliverable IS derivable from the field
    guard alone — so not everything is missing; only `entry` is the true residual. -/
theorem opener_recoverable {lo hi : Nat} (hg : G lo hi) : opener lo := hg.2

/-- **The gap (props).**  At a window where the hard part `entry` fails, the field guard `G` still
    holds while the element props `P` do not — packaging from `G` alone is impossible. -/
theorem gap_field_weaker_than_props : G 2 5 ∧ ¬ P 2 5 := by decide

/-- **The gap (deliverable).**  At the same window the field guard holds but the *deliverable*
    `Located` fails — the missing piece is exactly what the locate must supply. -/
theorem gap_is_the_deliverable : G 2 5 ∧ ¬ Located 2 5 := by decide

/-- **No total locator** — the assembler's locator hypothesis is a genuine obligation, not free from
    the guard: at `(2,5)` `G` holds yet `Located` fails.  This is precisely why locate is the
    residual *producer* and not something the universal packaging discharges by itself. -/
theorem no_total_locator : ¬ ∀ lo hi, G lo hi → Located lo hi := by
  intro h
  have h25 := h 2 5 (by decide)
  revert h25; decide

/-! ## Positive witnesses — where the locate fires, everything composes -/

/-- A window where the hard part holds: `entry 2 6` (`2 + 6 = 8 ≠ 7`). -/
theorem located_holds : Located 2 6 := by decide

/-- ...so the props hold there. -/
theorem props_hold : P 2 6 := by decide

/-- ...and the joint composes them concretely, end to end. -/
theorem joint_composes : P 2 6 :=
  elemProps_of_located (by decide : Located 2 6) (by decide : G 2 6)

-- Decidable sanity checks (fail the build if any witness drifts).
#guard decide (G 2 5) = true        -- field guard holds at the gap window
#guard decide (P 2 5) = false       -- ...but props fail there (entry 2 5 = (7 ≠ 7) = False)
#guard decide (Located 2 5) = false -- ...and the deliverable fails there
#guard decide (P 2 6) = true        -- both hold where the locate fires
#guard decide (Located 2 6) = true
#guard decide (opener 2) = true      -- the recoverable half is true regardless of `entry`

end UniversalPackagingJoint
