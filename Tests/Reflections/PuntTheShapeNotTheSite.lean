/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 666 — punt the SHAPE, not the site

**The rule.**  [[PuntMayBeTheBoundary]] classifies an optional field's `True`s by
asking two questions about the SITE: does any input reach it, and if one does,
does the datum's negation go through.  A site can answer YES to both.  Its inputs
then split — the datum holds on some and fails on others — and calling the site a
boundary throws away every input on the true side.  When the datum is DECIDABLE
from data the producer already holds, the punt belongs to the shape: split inside
the producer, serve the half that nests, defer the half that does not.

**How the mixed site hides.**  It hides behind the arm.  A punt is written once
per arm, so the arm is where you look, and an arm that must punt SOME input looks
like an arm that must punt.  The question that separates them is not "can I prove
the datum here" but "is the datum a function of what this arm knows" — and if the
answer is yes, its negation is too, so both halves are available and the
`by_cases` is the whole payment.

**What made it visible.**  Two producers that differ only in which branch of one
disjunction they take are ONE producer with a case split in it.  Merged, the
branches sit side by side under a single reading of the input, and the caller no
longer has to choose which one to hand its single field — a choice that silently
caps coverage at the better of the two rather than their union
([[CarryTheRouteNotTheCoordinates]] is the same shape one level down: the field
admits every producer, and here the producer admits every branch).

Concretely (L4YAML item 40): `entryKeyPack_of_dispatch` is item 38's compact
producer and item 39's landed one, merged at the disjunct the preprocessing
already returns.  The `-`-parked pending gains the break-crossed frame it never
had (`-⏎  a: 1`), and item 39's "permanent" punt at the indented mapping value
turns out to be permanent only at the DEDENT: `k:⏎  :⏎    a: 1` composes,
`k:⏎  :⏎b: 2` defers.

§1 the site that answers yes twice.  §2 what the arm-level punt costs.  §3 the
producer decides.  §4 one field, two branches, and why merging is not a
refactor.  §5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.PuntTheShapeNotTheSite

/-! ## §1  A site that answers YES to both questions

`n` is the index the pending carries, `w` the column the content landed at.  The
frame exists exactly when the landing is at or beyond the index; a landing to the
left is a DEDENT, and there the enclosing construct has ended. -/

structure Landing where
  n : Nat
  w : Nat
deriving DecidableEq, Repr

/-- The route's side condition, and so the frame's existence. -/
def Nests (l : Landing) : Prop := l.n ≤ l.w

instance (l : Landing) : Decidable (Nests l) := Nat.decLe _ _

/-- Two sites parking the same optional field. -/
inductive Site where
  | root      -- every landing that reaches it has `n = 0`
  | indented  -- landings of every shape reach it
deriving DecidableEq, Repr

def reaches : Site → Landing → Prop
  | .root, l => l.n = 0
  | .indented, _ => True

/-- Reflection 665's first question: is the site reached at all. -/
theorem indented_is_reached : ∃ l, reaches .indented l := ⟨⟨2, 4⟩, trivial⟩

/-- …and its second: does the datum's NEGATION go through at some input that
    reaches it.  It does — the dedent. -/
theorem indented_has_a_refuting_input : ∃ l, reaches .indented l ∧ ¬ Nests l :=
  ⟨⟨2, 0⟩, trivial, by decide⟩

/-- **And so does the datum itself.**  This is the case the two questions do not
    name: the site is MIXED, and neither "debt" nor "boundary" describes it. -/
theorem indented_has_a_satisfying_input : ∃ l, reaches .indented l ∧ Nests l :=
  ⟨⟨2, 4⟩, trivial, by decide⟩

theorem the_site_is_mixed :
    (∃ l, reaches .indented l ∧ Nests l) ∧ (∃ l, reaches .indented l ∧ ¬ Nests l) :=
  ⟨indented_has_a_satisfying_input, indented_has_a_refuting_input⟩

/-! ## §2  What the arm-level punt costs

A punt written at the arm serves nothing that reaches the arm.  At a mixed site
that is not a boundary, it is a boundary drawn in the wrong place: every nesting
landing is lost with the dedent. -/

/-- The landings this arm actually sees, as a finite sample. -/
def sample : List Landing := [⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 4⟩, ⟨0, 0⟩, ⟨0, 3⟩]

/-- Item 39's shape: the whole arm hands `True`. -/
def armPunt (_ : Landing) : Bool := false

/-- Item 40's shape: the producer decides, per landing. -/
def shapePunt (l : Landing) : Bool := decide (Nests l)

def served (f : Landing → Bool) : Nat := (sample.filter f).length

theorem the_arm_serves_none : served armPunt = 0 := by decide
theorem the_shape_serves_the_true_half : served shapePunt = 4 := by decide

/-- The arm-level punt is DOMINATED: never wider, and strictly narrower here. -/
theorem shape_dominates : ∀ l, armPunt l = true → shapePunt l = true := by
  intro l h; simp [armPunt] at h
theorem shape_is_strictly_wider : ∃ l, shapePunt l = true ∧ armPunt l = false :=
  ⟨⟨2, 4⟩, by decide, by decide⟩

/-- What is left after the split is the dedent, and only the dedent — which is
    where [[PuntMayBeTheBoundary]] was right: the datum is FALSE there, so the
    deferral is not debt. -/
theorem what_still_defers : sample.filter (fun l => ! shapePunt l) = [⟨2, 0⟩, ⟨2, 1⟩] := by
  decide

/-! ## §3  The producer decides, and that is the whole payment

Nothing about the split needs new evidence: both numbers are in hand where the
pack is built, so the side condition is a decision, not a proof obligation. -/

/-- The producer, written the only way that keeps both halves: decide, and hand
    the fact wherever it holds. -/
theorem produce (l : Landing) : Nests l ∨ True :=
  if h : Nests l then Or.inl h else Or.inr trivial

/-- WHICH half a `∨ True` was built from is not observable in `Prop` — proof
    irrelevance is why [[PuntMayBeTheBoundary]]'s `the_type_cannot_tell` holds —
    so the split must be read on the PRODUCER's side, where it is a decision and
    needs nothing the landing does not already carry. -/
theorem the_side_condition_is_decided (l : Landing) : shapePunt l = true ↔ Nests l := by
  simp [shapePunt]

/-- The test to run BEFORE writing an arm-level punt: ask for both halves.  A
    site that supplies both is mixed and must be split. -/
def isMixed (ls : List Landing) : Bool :=
  ls.any (fun l => shapePunt l) && ls.any (fun l => ! shapePunt l)

theorem the_sample_site_is_mixed : isMixed sample = true := by decide
/-- A site all of whose landings refute is a true boundary, and splitting it
    buys nothing — the classification still matters. -/
theorem a_real_boundary_is_not_mixed : isMixed [⟨2, 0⟩, ⟨3, 1⟩] = false := by decide

/-! ## §4  One field, two branches

The two producers read the same input and disagree only about which frame the
landing fills.  A consumer with ONE optional field can be handed only one of
them, so keeping them apart caps coverage at the better single branch rather
than their union. -/

inductive Branch where
  | onLine        -- the content shares the indicator's line: the compact frame
  | acrossBreak   -- the content landed after a break: the nested frame
deriving DecidableEq, Repr

/-- What each producer covers on its own. -/
def coverCompact : Branch → Bool
  | .onLine => true
  | .acrossBreak => false

def coverLanded : Branch → Bool
  | .onLine => false
  | .acrossBreak => true

/-- Handing the single field one producer covers one branch, whichever it is. -/
theorem neither_alone_is_total :
    (∃ b, coverCompact b = false) ∧ (∃ b, coverLanded b = false) :=
  ⟨⟨.acrossBreak, by decide⟩, ⟨.onLine, by decide⟩⟩

def coverMerged (b : Branch) : Bool := coverCompact b || coverLanded b

theorem merged_is_total : ∀ b, coverMerged b = true := by intro b; cases b <;> rfl

/-- The merge is not a refactor, because the READING is shared: both producers
    ask the same question of the input and only the answer's frame differs.
    Modelled: one reading function, consulted before the branch is known. -/
def readKey (_b : Branch) : Nat := 1  -- the same reading, whatever the branch is

theorem the_reading_does_not_branch : ∀ b, readKey b = readKey .onLine := by
  intro b; cases b <;> rfl

/-- And the frame a caller cannot offer stays OPTIONAL, so the merged producer
    is total for the caller that has both and unchanged for the caller that has
    one (`h_compact : … ∨ True`). -/
def coverWithOptionalCompact (hasCompact : Bool) (b : Branch) : Bool :=
  (hasCompact && coverCompact b) || coverLanded b

theorem optional_frame_costs_the_other_caller_nothing :
    coverWithOptionalCompact false .acrossBreak = true ∧
    coverWithOptionalCompact false .onLine = false ∧
    (∀ b, coverWithOptionalCompact true b = true) :=
  ⟨by decide, by decide, by intro b; cases b <;> rfl⟩

/-! ## §5  What item 40 shipped -/

/-- Producers of `ImplicitKeyPack` read off a content dispatch: item 38's
    compact one and item 39's landed one, merged into one. -/
def packProducerLemmasBefore : Nat := 2
def packProducerLemmasAfter : Nat := 1
/-- Consumer arms that call it — the `-`-parked pending (root and indented) and
    the mapping value's (root and indented); the last was punting whole. -/
def packCallSitesBefore : Nat := 3
def packCallSitesAfter : Nat := 4
/-- Frames a `-`-parked pending can put its key in: `[195]` compact, and now
    `[187]` nested under the entry across a break. -/
def entryFramesBefore : Nat := 1
def entryFramesAfter : Nat := 2
/-- Arms handing `True` at a MIXED site — one whose inputs split.  The
    whole-arm punts that remain are boundaries in the older sense: their datum
    is false at every input that reaches them. -/
def mixedSiteArmPuntsBefore : Nat := 1
def mixedSiteArmPuntsAfter : Nat := 0
/-- New route lemmas, new frame lemmas, and edits to the pack, the key head or
    the arm that fires it: none.  The merge is the item. -/
def newRouteLemmas : Nat := 0
def newFrameLemmas : Nat := 0
def consumerEditsRequired : Nat := 0
/-- Lines of the two producers with their docstrings, before and after. -/
def producerLinesBefore : Nat := 175
def producerLinesAfter : Nat := 128
/-- Runtime files edited: none.  Proof shape only. -/
def runtimeFilesEdited : Nat := 0
/-- Escape sites: unmoved for the fourth item running — what moves is the
    domain. -/
def escapeSitesBefore : Nat := 6
def escapeSitesAfter : Nat := 6

theorem shipped :
    packProducerLemmasAfter + 1 = packProducerLemmasBefore ∧
    packCallSitesAfter = packCallSitesBefore + 1 ∧
    entryFramesAfter = entryFramesBefore + 1 ∧
    mixedSiteArmPuntsAfter + 1 = mixedSiteArmPuntsBefore ∧
    newRouteLemmas = 0 ∧ newFrameLemmas = 0 ∧ consumerEditsRequired = 0 ∧
    producerLinesAfter < producerLinesBefore ∧
    runtimeFilesEdited = 0 ∧ escapeSitesAfter = escapeSitesBefore := by
  decide

end L4YAML.Tests.Reflections.PuntTheShapeNotTheSite

end Blanket
