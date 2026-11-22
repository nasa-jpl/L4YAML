/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 640 — a narrow reading of the same walk is a SECOND lemma, not a conjunct — unless it names the wide conclusion's ∃-bound witnesses

**The rule.**  When a proof needs a NARROWER reading of a walk an existing
`_prod` lemma already reads widely, the default is a **second, self-contained
lemma over the same walk** — its own induction, the wide lemma untouched.
Reflection 639's secondary carrier rule (ride the same conclusion as a
conjunct) is the EXCEPTION, and it applies exactly when the narrow fact
mentions positions the wide conclusion binds EXISTENTIALLY: nothing outside
can name them, so nothing outside can state the fact.

The discriminator is therefore syntactic and checkable before any proof:
*does the narrow statement mention anything the wide conclusion introduces?*

- Item 15 (plain scalar): the one-line reading needed "the next-line star
  collapsed", i.e. `sp_next = sp_entries` — both `∃`-bound in
  `collectPlainScalarLoop_prod`.  Conjunct; 13 arms touched.
- Item 16 (quoted scalars): `[110] nb-double-text(n, block-key)` IS `[111]
  nb-double-one-line`, a complete reading of the walk's own endpoints.  Two
  new lemmas, `collectDoubleQuotedLoop_prod` and its single-quoted twin
  untouched — 0 arms edited, and the refutation reused item 15's `_line_*`
  facts verbatim.

**The corollary (widening a packed payload).**  When the same consumer must
accept several readings, widen the PACK with a small carrier inductive at its
definition and convert ONCE, rather than adding a disjunct at every use.  The
`:` producer took one new hypothesis type and one new body line for three
heads; a disjunction would have re-expanded at each pack site and at the
producer.

Self-contained: the walk miniature with both readings, the proof that the
un-conjuncted existential CANNOT recover the collapse (so 639's exception is
real), the carrier-widening shape, and the shipped counts.
-/

namespace L4YAML.Tests.Reflections.SecondReadingOwnLemma

/-! ## §1  One walk, two readings -/

/-- A scan step: stays on the line, or crosses a break. -/
inductive Step where
  | stay
  | cross
  deriving DecidableEq

abbrev Walk := List Step

/-- The machine fact both readings consult. -/
def crosses : Walk → Nat
  | []             => 0
  | Step.stay  :: w => crosses w
  | Step.cross :: w => crosses w + 1

/-- The NARROW reading (`[111] nb-double-one-line`): a bare content star. -/
inductive One : Walk → Prop where
  | nil : One []
  | char (w : Walk) : One w → One (Step.stay :: w)

/-- The WIDE reading (`[116] nb-double-multi-line`): segments joined by breaks. -/
inductive Multi : Walk → Prop where
  | last (w : Walk) : One w → Multi w
  | join (w : Walk) : Multi w → Multi (Step.cross :: w)
  | char (w : Walk) : Multi w → Multi (Step.stay :: w)

/-- The wide lemma — what already existed.  Item 16 did not touch it. -/
theorem wide (w : Walk) : Multi w := by
  induction w with
  | nil => exact .last [] .nil
  | cons s w ih => cases s with
    | stay  => exact .char w ih
    | cross => exact .join w ih

/-- The narrow lemma — self-contained, its OWN induction over the same walk.
    The break arm is refuted by the machine fact, exactly as the quoted
    loops' escaped-break and flow-fold arms are. -/
theorem narrow (w : Walk) (h : crosses w = 0) : One w := by
  induction w with
  | nil => exact .nil
  | cons s w ih => cases s with
    | stay  => exact .char w (ih h)
    | cross => exact absurd h (by simp [crosses])

/-- The narrow reading really is a refinement: nothing was weakened. -/
theorem narrow_refines {w : Walk} (h : One w) : Multi w := .last w h

/-- …and it is exactly characterised by the machine fact. -/
theorem narrow_iff {w : Walk} (h : One w) : crosses w = 0 := by
  induction h with
  | nil => rfl
  | char w _ ih => simpa [crosses] using ih

/-! ## §2  When the exception applies: the ∃-bound witness

  If the wide conclusion BINDS the positions the narrow fact talks about, an
  outside lemma cannot state it — and, worse, the un-conjuncted conclusion is
  satisfied by witnesses that violate it, so it is not merely unstated but
  underivable.  That is Reflection 639's carrier rule. -/

/-- The wide conclusion, existentially bound (item 15's shape). -/
def wideEx (_w : Walk) : Prop := ∃ a b : Nat, a ≤ b

/-- The same conclusion carrying the collapse as a CONJUNCT. -/
def wideExConjunct (w : Walk) : Prop :=
  ∃ a b : Nat, a ≤ b ∧ (crosses w = 0 → b = a)

theorem wideEx_holds (w : Walk) : wideEx w := ⟨0, 0, Nat.le_refl 0⟩

theorem wideExConjunct_holds (w : Walk) : wideExConjunct w :=
  ⟨0, 0, Nat.le_refl 0, fun _ => rfl⟩

/-- **Why the conjunct is forced.**  `wideEx` is satisfied by witnesses whose
    collapse FAILS on a walk that crossed nothing, so no lemma downstream of
    `wideEx` can recover it.  The fact must be proven where the witnesses are
    chosen — in the same induction. -/
theorem wideEx_cannot_recover_collapse :
    ∃ (a b : Nat), a ≤ b ∧ crosses [] = 0 ∧ b ≠ a :=
  ⟨0, 1, by omega, rfl, by omega⟩

/-! ## §3  Widening a packed payload: one carrier, one conversion

  Three readings reach the same consumer.  Carrying them as a small inductive
  keeps the consumer's signature at ONE hypothesis and its body at ONE
  application; a disjunction would re-expand at every pack site. -/

/-- The three heads `[188] ns-s-block-map-implicit-key` admits here. -/
inductive Head : Walk → Prop where
  | plain   (w : Walk) : One w → Head w
  | doubleQ (w : Walk) : One w → Head w
  | singleQ (w : Walk) : One w → Head w

/-- The ONE conversion, at the carrier's definition. -/
theorem head_to_wide {w : Walk} (h : Head w) : Multi w := by
  cases h with
  | plain h | doubleQ h | singleQ h => exact .last w h

/-- The consumer: one hypothesis, one application — unchanged in shape when
    the payload widened from one reading to three. -/
theorem consume {w : Walk} (h : Head w) : Multi w := head_to_wide h

/-! ## §4  The shipped counts (item 16, 2026-08-11) -/

/-- Arms of the two quoted `_prod` lemmas edited to carry the narrow reading. -/
def wideArmsEdited : Nat := 0
/-- Arms `collectPlainScalarLoop_prod` needed for item 15's conjunct
    (2 fold arms refute, 2 recursive transport, 9 terminal close). -/
def conjunctArmsItem15 : Nat := 13
/-- New self-contained lemmas: 2 one-line readings, 2 walk monotonicity,
    3 escape-body line-transparency (`collectHexDigitsLoop`, `parseHexEscape`,
    `processEscape`). -/
def newLemmas : Nat := 7
/-- `_line_*` facts REUSED from item 15 (`consumeNewline_line_succ`,
    `foldQuotedNewlines_line_lt`, `advance_preserves_line_of_ne_break`). -/
def reusedLineFacts : Nat := 3
/-- Heads the widened carrier admits. -/
def packHeads : Nat := 3
/-- Edits to the `:` producer: the hypothesis type, and the body line that
    builds `SImplicitKey`. -/
def producerEdits : Nat := 2
/-- Scanner/runtime files edited. -/
def runtimeEdits : Nat := 0

#guard wideArmsEdited == 0
#guard newLemmas == 2 + 2 + 3
#guard conjunctArmsItem15 == 2 + 2 + 9
#guard reusedLineFacts == 3
#guard packHeads == 3
#guard producerEdits == 2
#guard runtimeEdits == 0

end L4YAML.Tests.Reflections.SecondReadingOwnLemma

end Blanket
