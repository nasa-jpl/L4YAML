/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 678 — the break binds the index

**The rule.**  A reading that crosses no break is index-UNIVERSAL: the
index has no occurrence in what was read, so one derivation serves every
index (Reflection 671's lift).  A reading that crosses a break is
index-INSTANTIATED: the landing's `s-indent(n)` CONSUMES the index, and the
derivation exists at exactly the widths the fresh line's spaces clear.  The
two are one production with two quantifier shapes, and the mistake the rule
prevents is asking the landing for the universal — the deferral then reads
as "the reading fails at a nonzero index" when what failed is only the
quantifier: instantiate at the pending's OWN `n` and the landing composes,
off the same separator lemma the index-free arms never needed.

**The instance** (item 52).  `k:⏎  -⏎    a` — an indented entry's value on
its own line — deferred at both indented content arms since item 23,
whose one-line lemma is break-free by construction.  The separator at a
given `n` existed since item 45 (`preprocess_some_separate_at_anyCol`:
`[70] s-separate-lines(n)` when the landing's whites open with
`s-indent(n)`); item 52's whole cost is a fourth disjunct in
`indentedValue_reads_at_any_indent` carrying the FIXED-index separator and
the same one-line content, and one mirror case per arm.  ZERO runtime
edits; the landed props/block-scalar/fold shapes keep the deferral (each
its own class).

§1 the two readings; §2 the inline one lifts to every index; §3 the landed
one holds at the measured index and REFUTABLY not at others — the break
binds. -/

namespace L4YAML.Tests.Reflections.TheBreakBindsTheIndex

/-- §1 a landing: `k` spaces on a fresh line. -/
inductive Landing : Nat → Prop
  | mk (k : Nat) : Landing k

/-- The separator before a value: inline whites (no index occurrence), or a
    break followed by `s-indent(n)` — the index consumed by the landing. -/
inductive Sep : Option Nat → Nat → Prop
  | inline (n : Nat) : Sep none n
  | landed (k : Nat) : Landing k → Sep (some k) k

/-- A value reads at `n` when some separator at `n` precedes it. -/
def ReadsAt (brk : Option Nat) (n : Nat) : Prop := Sep brk n

/-- §2 the break-free reading is index-universal: one derivation, every
    index. -/
theorem inline_reads_everywhere (n : Nat) : ReadsAt none n :=
  Sep.inline n

/-- §3 the landed reading holds at the landing's own width… -/
theorem landed_reads_at_own (k : Nat) : ReadsAt (some k) k :=
  Sep.landed k (Landing.mk k)

/-- …and at NO other: the break binds the index. -/
theorem landed_binds (k n : Nat) (h : ReadsAt (some k) n) : n = k := by
  cases h; rfl

/-- The universal is therefore unavailable on the landed side — asking for
    it is what the deferral was. -/
theorem landed_not_universal : ¬ (∀ n, ReadsAt (some 0) n) := by
  intro h
  have := landed_binds 0 1 (h 1)
  simp at this

end L4YAML.Tests.Reflections.TheBreakBindsTheIndex

end Blanket
