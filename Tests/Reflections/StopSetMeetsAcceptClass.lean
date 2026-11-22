/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.LineOpenGuard

@[expose] public section Blanket

/-!
# Reflection 668 — a deferring arm's survivors are an intersection of two sets

**The rule.**  An arm that defers on a dispatched character is cut by TWO
independent sets: the park's STOP SET — what the producer's own validation
left possible on the rest of the line — and the consumer's ACCEPT CLASS —
what the dispatcher returns `.ok` on.  The arm's inhabitants are their
intersection, so compute the intersection ONCE instead of refuting the stop
set's members one at a time.

**When the two methods coincide, and when only one exists.**  At a dispatch
whose class is a short enumeration, per-character refutation IS the
intersection: L4YAML item 36 met `[204]`'s stop set with the block dispatch's
three indicators, three refutations, done.  But a CONTENT dispatch accepts an
unbounded class — every `ns-plain-first` character — so no enumeration of it
can be written down.  What can be written down is the class's DEFINING GUARDS
(`¬indicator`, `¬white`, `¬break`, printable, not the BOM, plus a short
exception list), and the guards are exactly what an intersection proof
consumes: each stop-set family contradicts one guard, and the members of the
exception list are checked individually.  The proof's size is the number of
guards plus the size of the exception list — not the size of the class.

**The asymmetry worth noticing.**  The stop set and the accept class are
produced at DIFFERENT times by DIFFERENT code: the stop set at the previous
step (the completed construct's trailing validation, carried on the pending as
a line fact), the accept class at the current one (the dispatcher's own
character tests).  Neither side was written to refute the other, and no new
runtime check is needed: the refutation is the observation that the two
independently-shipped sets barely overlap.  L4YAML item 42:
`dispatchContent_ok_charFacts` reads the class's guards off `.ok` once, and
then `TailSuffix ∩ A = ∅` empties the document-suffix park's content arm
(`docEnd_refutes_content_residue`) while `NodeStop ∩ A = {':'}` narrows the
complete-node parks to the one character the grammar itself puts there —
`[154]`'s implicit-key `:` (`nodeStop_content_residue_is_colon`).

§1 the two sets, as shipped.  §2 the intersection at the enumerable dispatch —
where refuting members one at a time is the same computation.  §3 the
intersection at the unbounded dispatch — where only the guard reading exists.
§4 the survivors are exact: each non-empty cell is inhabited.
-/

namespace L4YAML.Tests.Reflections.StopSetMeetsAcceptClass

open L4YAML L4YAML.CharPredicates L4YAML.Proofs.LineOpenGuard

/-! ## §1  The two sets, as shipped

The stop sets are the library's own (`TailSuffix`, `NodeStop` — items 36/37's
line facts).  The accept class is the content dispatcher's, stated by its
guards: one of the seven construct heads, or a `[126] ns-plain-first`
character.  For the `-`/`?`/`:` exception the follower and context matter to
the SCANNER but not to this intersection, so the model takes the accepting
side (a non-blank follower in block context) — the largest class, hence the
strongest refutation. -/

/-- The seven construct heads — the dispatcher's exception list. -/
def constructHead (c : Char) : Prop :=
  c = '&' ∨ c = '*' ∨ c = '!' ∨ c = '|' ∨ c = '>' ∨ c = '"' ∨ c = '\''

/-- The content dispatcher's accept class, by its guards. -/
def acceptContent (c : Char) : Prop :=
  constructHead c ∨
  (c = '-' ∨ c = '?' ∨ c = ':') ∨
  (isIndicatorBool c = false ∧ isWhiteSpaceBool c = false ∧
   isLineBreakBool c = false ∧ isPrintableBool c = true ∧ c ≠ '﻿')

/-- The block dispatcher's accept class: three indicators, enumerable. -/
def acceptBlock (c : Char) : Prop := c = '-' ∨ c = ':' ∨ c = '?'

/-! ## §2  The enumerable dispatch: refutation-per-member IS the intersection

`TailSuffix ∩ {-, :, ?}` is empty and a three-member walk checks it — this is
item 36's `docEnd_refutes_inline_residue`, seen as an intersection that
happened to be small enough to enumerate. -/

theorem tailSuffix_cap_block_empty : ∀ c, acceptBlock c → TailSuffix c → False := by
  rintro c (rfl | rfl | rfl) (h | h) <;> exact absurd h (by decide)

/-- …and `NodeStop ∩ {-, :, ?} = {':'}` is item 37's narrowing. -/
theorem nodeStop_cap_block_colon : ∀ c, acceptBlock c → NodeStop c → c = ':' := by
  rintro c (rfl | rfl | rfl) h
  · exact (NodeStop.not_dash_or_question h (Or.inl rfl)).elim
  · rfl
  · exact (NodeStop.not_dash_or_question h (Or.inr rfl)).elim

/-! ## §3  The unbounded dispatch: only the guard reading exists

No list of `acceptContent`'s members can be written down, but the intersection
is still one lemma: each stop-set family contradicts one GUARD, and the seven
construct heads are the exception list, checked individually.  The proof's
size is guards + exceptions — independent of the class's cardinality. -/

/-- No construct head is in `NodeStop` (nor, a fortiori, in `TailSuffix`). -/
theorem constructHead_not_nodeStop : ∀ c, constructHead c → NodeStop c → False := by
  rintro c (rfl | rfl | rfl | rfl | rfl | rfl | rfl) (((hb | hh) | hc) | (hn | hb2)) <;>
    exact absurd ‹_› (by decide)

theorem tailSuffix_cap_content_empty :
    ∀ c, acceptContent c → TailSuffix c → False := by
  rintro c (hmem | h3 | ⟨hind, -, hbr, -, -⟩) hts
  · exact constructHead_not_nodeStop c hmem hts.toNodeTail.toNodeStop
  · exact tailSuffix_cap_block_empty c
      (by rcases h3 with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl rfl)) hts
  · -- the guarded remainder: a break contradicts the break guard, a `#` the
    -- indicator guard — one guard per stop-set family
    rcases hts with hb | rfl
    · rw [hbr] at hb; cases hb
    · exact absurd hind (by decide)

theorem nodeStop_cap_content_colon :
    ∀ c, acceptContent c → NodeStop c → c = ':' := by
  rintro c (hmem | h3 | ⟨hind, -, hbr, hp, hbom⟩) hns
  · exact (constructHead_not_nodeStop c hmem hns).elim
  · exact nodeStop_cap_block_colon c
      (by rcases h3 with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl rfl)) hns
  · rcases hns with ((hb | rfl) | rfl) | (hn | hb2)
    · rw [hbr] at hb; cases hb
    · exact absurd hind (by decide)
    · rfl
    · rw [hp] at hn; cases hn
    · exact absurd hb2 hbom

/-! ## §4  The survivors are exact

An intersection argument earns its name only if the non-empty cells are
INHABITED — otherwise the "narrowing" might be an emptiness in disguise, and
the arm it leaves behind a phantom.  `':'` really is in both stop set and
accept class (the scanner really does dispatch `"a" :b`'s `:` to content),
so `NodeStop ∩ A = {':'}` is a narrowing and `TailSuffix ∩ A = ∅` is the
strict subfamily's emptiness, not the same fact twice. -/

example : NodeStop ':' := Or.inl (Or.inr rfl)
example : acceptContent ':' := Or.inr (Or.inl (Or.inr (Or.inr rfl)))
example : acceptBlock ':' := Or.inr (Or.inl rfl)
example : ¬TailSuffix ':' := by rintro (h | h) <;> exact absurd h (by decide)

end L4YAML.Tests.Reflections.StopSetMeetsAcceptClass

end Blanket
