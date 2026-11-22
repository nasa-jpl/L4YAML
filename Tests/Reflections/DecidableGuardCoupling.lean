/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 639 — guard the coupling with decidable state facts; the consumer case-splits, never derives

**The rule.**  A conditional constructor field that couples a parked
obligation to a machine check (R636's carrier) should be GUARDED by
decidable propositions of the type-parameter state — not by the check's
own success.  Then every consumer fires the field with `by_cases` alone:
guard true and pack present → compose; anything else → the standing
fallback.  The runtime check never enters the proof, at EITHER end — the
pack *is* the grammar evidence, and soundness never needed the validator's
semantics, only the state facts the validator also happens to read.

The shipped instance (L4YAML item 15): the implicit key `a: b`.
`scanValueValidate`'s §7.4 pass demands a possible saved key resting on
the current line; the coupling field on `pendingContent` is guarded by
exactly those two facts — `simpleKey.possible = true` and
`simpleKey.pos.line = line`, both decidable on the pending's scanner-state
parameter — and concludes pack-or-punt.  The park site derives the pack
from line arithmetic (`saveSimpleKey` stamps `pos := currentPos` at the
content START; the scan only advances the line, the folds strictly), and
the same-line-`:` consumer is three `by_cases` plus one field application.
Zero lemmas about `scanValueValidate` exist in the pass.

**The honesty pressure.**  A pack-or-punt field is logically vacuous — any
site can punt — so nothing OBSERVABLE detects a pack that never fires.
What forces the construction is the campaign's endpoint: deleting the
deferral (row 12's `scannerDrop` retirement) deletes the punt arm, and
only packed parks type-check.  Interim honesty is by construction, checked
by the elaborator at the pack-capable park sites.

**The secondary carrier rule.**  The pack's one-line witness needed "same
exit line ⇒ the next-line star collapsed" — a fact about positions bound
EXISTENTIALLY in `collectPlainScalarLoop_prod`'s conclusion.  No separate
lemma can name those witnesses; the fact must ride the SAME conclusion as
a conjunct, proven in the same induction (two fold arms refute it by
strict line growth; eleven arms pass it through).

Self-contained: the state/pack/field/consumer miniature, the strict twin
that models the deferral's deletion, the ∃-conjunct shape, and the shipped
instance's counts (item 15, 2026-08-11).
-/

namespace L4YAML.Tests.Reflections.DecidableGuardCoupling

/-- The parking step's end state — the consuming step's start state (R636). -/
structure St where
  possible : Bool
  keyLine  : Nat
  line     : Nat

/-- The grammar evidence the consumer composes with.  Holding it suffices;
    no runtime check is consulted to use it. -/
inductive OneLineKey : St → Prop where
  | mk (st : St) (h : st.keyLine = st.line) : OneLineKey st

/-- The coupling field: two DECIDABLE guards on the state, pack-or-punt. -/
def KeyField (st : St) : Prop :=
  st.possible = true → st.keyLine = st.line → OneLineKey st ∨ True

/-- A pack-capable park: the pack needs only the guards' content. -/
theorem packSite (st : St) : KeyField st := fun _ h => Or.inl (OneLineKey.mk st h)

/-- A punting park (quoted content, col ≠ 0, inherited stale key). -/
theorem puntSite (st : St) : KeyField st := fun _ _ => Or.inr trivial

/-- The consumer's outcome: composed with evidence, or the standing fallback. -/
inductive Next (st : St) : Prop where
  | composed (h : OneLineKey st) : Next st
  | deferred : Next st

/-- The consumer: two `by_cases` on decidable state facts plus one field
    application — no lemma about any validator appears. -/
theorem consume (st : St) (f : KeyField st) : Next st := by
  by_cases h1 : st.possible = true
  · by_cases h2 : st.keyLine = st.line
    · cases f h1 h2 with
      | inl pack => exact .composed pack
      | inr _ => exact .deferred
    · exact .deferred
  · exact .deferred

/-- The deletion endpoint: without the deferral, only packed parks serve —
    the punt arm's disappearance is what forces every site to pack. -/
inductive NextStrict (st : St) : Prop where
  | composed (h : OneLineKey st) : NextStrict st

theorem strict_needs_pack (st : St)
    (f : st.possible = true → st.keyLine = st.line → OneLineKey st)
    (h1 : st.possible = true) (h2 : st.keyLine = st.line) : NextStrict st :=
  .composed (f h1 h2)

/-- The ∃-conjunct shape: a collapse fact about existentially bound
    witnesses cannot be a separate lemma — nothing can name `a` and `b`
    from outside — so it rides the same conclusion. -/
theorem walk (gain : Nat) : ∃ a b : Nat, a ≤ b ∧ (gain = 0 → b = a) :=
  ⟨0, gain, Nat.zero_le _, fun h => h⟩

-- ═══ §1  The shipped instance's shape (item 15, 2026-08-11) ═══

/-- `pendingContent` park sites in `StreamAccum.lean`. -/
def parkSites : Nat := 9
/-- Sites that punt this pass (quoted/alias/block-scalar content, value
    position, scannerDrop resume) — each awaits its own row-12 arm. -/
def puntingSites : Nat := 7
/-- Pack-capable constructions (both `content_dispatch_after_close` parks,
    fed by ONE `keyctx_of_preprocess` derivation at every caller). -/
def packCapableSites : Nat := 2
/-- Case splits in the consuming arm (`c = ':'`, possible, pos.line). -/
def consumerCaseSplits : Nat := 3
/-- Lemmas about `scanValueValidate` the pass needed. -/
def validatorLemmasNeeded : Nat := 0

#guard puntingSites + packCapableSites == parkSites
#guard consumerCaseSplits == 3
#guard validatorLemmasNeeded == 0

-- ═══ §2  The substrate's price ═══

/-- New line-arithmetic lemmas under the one-line conjunct
    (`advance`/`consumeNewline` breaks, blank-lines/fold `≥`, both fold
    helpers strict, the loop's `line_le`). -/
def lineLemmas : Nat := 7
/-- Arms of `collectPlainScalarLoop_prod` touched by the conjunct:
    2 fold arms refute it, 2 recursive arms transport it, 9 terminal arms
    close it with `rfl`. -/
def conjunctArms : Nat := 13
/-- Context lifts `.blockIn → .blockKey` (First/Char/Entry/GStar/OneLine)
    — definitional, `isNsPlainSafe` maps both to `isNsChar`. -/
def contextLifts : Nat := 5
/-- Scanner/runtime files edited. -/
def runtimeEdits : Nat := 0

#guard conjunctArms == 2 + 2 + 9
#guard lineLemmas == 7
#guard contextLifts == 5
#guard runtimeEdits == 0

end L4YAML.Tests.Reflections.DecidableGuardCoupling

end Blanket
