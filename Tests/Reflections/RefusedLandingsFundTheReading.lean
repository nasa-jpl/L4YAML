/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 679 — the refused landings fund the reading

**The rule.**  A runtime floor check inside a scan loop is not only a
refutation device: once it covers EVERY landing of the loop, it is the
production's own justification at the checked index — the same induction
that builds the index-0 reading builds the reading at `n`, with the check's
negation as the only new fact per landing (the landing's run clears
`s-indent(n)` because the check would have refused it otherwise).  So before
generalizing a scan-loop induction, audit the loop's guards: a landing WITH
a floor check lifts for free, and a landing WITHOUT one is both a scanner
over-acceptance (spec-invalid inputs pass) and a hole in the reading (valid
inputs cannot lift) — one missing check, both halves, fixed by the same
edit.  Item 45 lifted derivations to AVOID the loop induction; this rule
says when the induction must after all be walked, the guards pay for it.

**The instance** (item 53).  The quoted collectors' FOLD landing has carried
the under-indent check since item 7 (and its tab gate in both contexts since
item 50), so `collectDoubleQuotedLoop_prod_at`/`collectSingleQuotedLoop_prod_at`
re-run the 0-inductions at any `n ≤ currentIndent + 1` and
`k:⏎  - "x⏎    y"` composes at the entry's own index.  The ESCAPED-break
landing (`"x\⏎y"`) had NO checks — `k:⏎  a: "x\⏎y"` was accepted end-to-end
though `[112] s-double-escaped(n)` ends in the same `s-flow-line-prefix(n)`
— and giving it the fold's three checks (on content landings; a blank
landing is `l-empty`, the fold's to check) both refused the invalid family
and made the escaped case of the induction provable.

§1 a loop over landings with a floor check; §2 the check's coverage IS the
reading at `n`; §3 an unchecked landing breaks both directions at once. -/

namespace L4YAML.Tests.Reflections.RefusedLandingsFundTheReading

/-- §1 a scan: a list of landing widths the loop accepted. -/
abbrev Scan := List Nat

/-- The loop's check: every landing clears the floor. -/
def Checked (floor : Nat) (s : Scan) : Prop := ∀ w ∈ s, floor < w

/-- The reading at `n`: every landing supplies `s-indent(n)`. -/
def ReadsAt (n : Nat) (s : Scan) : Prop := ∀ w ∈ s, n ≤ w

/-- §2 the check's coverage IS the reading: an accepted scan reads at every
    index the floor admits. -/
theorem checked_reads_at (floor n : Nat) (s : Scan)
    (hchk : Checked floor s) (hn : n ≤ floor + 1) : ReadsAt n s :=
  fun w hw => Nat.le_trans hn (hchk w hw)

/-- §3 one unchecked landing breaks both halves: the scan is accepted with
    an under-floor landing (the over-acceptance)… -/
theorem unchecked_overaccepts (floor : Nat) :
    ¬ Checked floor [floor] := by
  intro h
  exact absurd (h floor (by simp)) (by omega)

/-- …and the same landing refutes the reading at the index the pending
    carries — the hole and the over-acceptance are ONE missing check. -/
theorem unchecked_breaks_reading (floor : Nat) :
    ¬ ReadsAt (floor + 1) [floor] := by
  intro h
  exact absurd (h floor (by simp)) (by omega)

end L4YAML.Tests.Reflections.RefusedLandingsFundTheReading

end Blanket
