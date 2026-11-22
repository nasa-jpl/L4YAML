/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 662 — project at the consumer, not at the producer

**The rule.**  A producer that has decided a SET must hand over the set.  The
moment it projects onto the one question its first consumer asks, everything
else it knew is gone — and the loss is invisible, because the projected fact
is still true, still used, and still named after the thing it proves.  The next
consumer arrives with a different question that the same evidence already
answered, finds a predicate that cannot answer it, and prices the work as a
missing derivation instead of a discarded one.  Carrying the set costs the
first consumer one monotonicity step, and it is the same step the producer was
taking anyway.

**And an escape is a projection.**  A shared consumer's fallback hypothesis,
written as the CONCLUSION it produces (`h : Goal`), has already thrown away the
occasion: nothing in its type says when it is needed, so every caller must pay
it and no caller can refuse it.  Written as a function of the occasion's own
premise (`h : Residue → Goal`), the paying callers are unchanged —
`fun _ => h` — and a caller that can show the premise empty pays `nofun`.  The
case distinction moves to the call sites, which is where it already existed;
the shared lemma is not split.

**The two are one rule.**  `Goal` is `Residue → Goal` projected at the
producer.  In both cases the fix is to state the thing at the strength its
producer knows and let each consumer weaken it for itself.

Concretely (L4YAML): item 10 derived "the rest of the line" from four scanner
validators whose allowlists are narrow — `[204] l-document-suffix` admits a
break or a `#` and nothing else — and stored `¬(c = '[' ∨ c = '{')`, because
the consumer of the day asked about a flow open.  The block dispatch's inline
residue later asked about `-`/`?`/`:` at a `...` and got no answer, though the
scanner had refused those shapes all along.  Indexing the predicate by its stop
set, with monotonicity at the consumer, answered it; making the block dispatch's
escape a function of the residue let one of its seven pendings refuse the escape
without splitting the lemma the other six share.

§1 the projection at the producer, and what it costs.  §2 the set carried, and
`mono`.  §3 the escape as the same mistake.  §4 why no split is needed.
§5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.ProjectAtTheConsumer

/-! ## §1  The projection at the producer

`Head` is what a validator found at the end of a construct's line.  `suffixOK`
is the set `[204]`'s check admits.  `notOpen` is the projection item 10 stored
in its place — true wherever `suffixOK` is, and true in two other places. -/

inductive Head where
  | brk
  | hash
  | dash
  | flowOpen
  | colon
deriving DecidableEq

/-- `[204] l-document-suffix ::= c-document-end s-l-comments` — the set the
    producing validator actually decided. -/
def suffixOK : Head → Bool
  | .brk => true
  | .hash => true
  | _ => false

/-- Item 10's stored fact: the one question its consumer asked. -/
def notOpen : Head → Bool
  | .flowOpen => false
  | _ => true

/-- The projection is sound — which is exactly why nothing flags it. -/
theorem projection_is_sound (h : Head) : suffixOK h = true → notOpen h = true := by
  cases h <;> simp [suffixOK, notOpen]

/-- The first consumer is served by either fact. -/
theorem first_consumer_served : notOpen .flowOpen = false := rfl

/-- **The cost.**  A second consumer asks about `-`, which the producer had
    already refused; the stored fact admits it.  The evidence was not missing,
    it was spent. -/
theorem projected_fact_cannot_answer :
    notOpen .dash = true ∧ suffixOK .dash = false := ⟨rfl, rfl⟩

/-- …and the loss is the difference of the two sets, which is not small: the
    stored fact admits four of five heads where the producer admitted two. -/
theorem the_gap_is_two_of_five :
    ([Head.brk, .hash, .dash, .flowOpen, .colon].filter notOpen).length = 4 ∧
    ([Head.brk, .hash, .dash, .flowOpen, .colon].filter suffixOK).length = 2 :=
  ⟨rfl, rfl⟩

/-! ## §2  The set carried, and the projection moved

Index the predicate by its stop set.  The producer states what it knows; each
consumer weakens for itself with one `mono`. -/

/-- The rest of the line: a head in `P`, or nothing at all. -/
inductive Line (P : Head → Bool) : List Head → Prop where
  | nil : Line P []
  | stop {h : Head} (rest : List Head) (hst : P h = true) : Line P (h :: rest)

/-- **The projection, at the consumer.**  One step, and the producer takes
    none. -/
theorem Line.mono {P Q : Head → Bool} (hPQ : ∀ h, P h = true → Q h = true) :
    ∀ {l : List Head}, Line P l → Line Q l := by
  intro l h
  cases h with
  | nil => exact .nil
  | stop rest hst => exact .stop rest (hPQ _ hst)

/-- The old consumer, unchanged in what it proves and one `mono` longer. -/
theorem old_consumer_still_served {rest : List Head}
    (h : Line suffixOK (Head.flowOpen :: rest)) : False := by
  cases h.mono projection_is_sound with
  | stop _ hst => exact absurd hst (by decide)

/-- The new consumer, served directly — no derivation, no new production. -/
theorem new_consumer_now_served {rest : List Head}
    (h : Line suffixOK (Head.dash :: rest)) : False := by
  cases h with
  | stop _ hst => exact absurd hst (by decide)

/-- And nothing was invented: the same set still admits what it always did. -/
theorem the_admitted_are_untouched : Line suffixOK [Head.hash] := .stop _ rfl

/-! ## §3  The escape is a projection too

`Goal` stands for what the shared consumer produces — data, so that the
statements below are about which VALUE arrives and not merely about
inhabitation.  `Residue` is the premise under which the escape is taken: the
case the shared consumer cannot handle. -/

/-- The shared consumer's conclusion (a stream, in the real setting). -/
abbrev Goal : Type := Nat

/-- The occasion.  `Residue true` is empty — that is the caller whose producer
    already refuted the shape; `Residue false` is inhabited. -/
def Residue (refutable : Bool) : Prop := refutable = false

theorem residue_true_is_empty : ¬ Residue true := fun h => Bool.noConfusion h
theorem residue_false_is_inhabited : Residue false := rfl

/-- **v1 — the escape as its conclusion.**  Nothing in the type mentions the
    occasion, so nothing about the occasion can be said at a call site. -/
abbrev Escape₁ : Type := Goal

/-- **v2 — the escape as a function of the occasion.** -/
abbrev Escape₂ (r : Prop) : Type := r → Goal

/-- Every caller that was paying still pays, in the same characters. -/
def old_payer {r : Prop} (g : Goal) : Escape₂ r := fun _ => g

/-- **The caller that knows the occasion is empty pays nothing** — this is the
    `nofun` the refutable pending is owed. -/
def refusing_payer : Escape₂ (Residue true) := fun h => Bool.noConfusion h

/-- The sharpest form: v2 is inhabited from the REFUTATION alone, with no
    `Goal` anywhere in hand.  v1 cannot be — `Escape₁` is `Goal`, so producing
    one is producing a stream, refutation or not. -/
def escape_from_refutation_alone (h : ¬ Residue true) : Escape₂ (Residue true) :=
  fun r => absurd r h

/-- …and that is not an artifact of this toy: `Escape₁` is literally the
    conclusion, so the two obligations are the same obligation. -/
theorem bare_escape_is_the_conclusion : Escape₁ = Goal := rfl

/-! ## §4  Why the shared lemma is not split

The consumer takes the escape and applies it; it never learns which caller it
came from.  Both kinds of caller feed one body, and the refuser's arm is
unreachable rather than special. -/

def shared_consumer {r : Prop} (e : Escape₂ r) (hr : r) : Goal := e hr

/-- The paying caller's value arrives unchanged. -/
theorem paying_caller_unchanged (g : Goal) :
    shared_consumer (old_payer (r := Residue false) g) residue_false_is_inhabited = g := rfl

/-- The refusing caller never reaches the body at all: there is no `hr` to
    supply, and that is the whole content of the change. -/
theorem refusing_caller_has_no_argument :
    (∀ hr : Residue true, shared_consumer refusing_payer hr = 0) :=
  fun hr => Bool.noConfusion hr

/-- The count that moved: seven callers of one lemma, one of which can now
    refuse.  The lemma itself is still one lemma. -/
def callersOfTheSharedLemma : Nat := 7
def callersThatNowRefuse : Nat := 1
def lemmasSplit : Nat := 0

theorem the_decision_moved_not_the_lemma :
    callersThatNowRefuse < callersOfTheSharedLemma ∧ lemmasSplit = 0 := by decide

/-! ## §5  What item 36 shipped -/

/-- Predicates replaced by one indexed family: `LineNoOpen` becomes
    `LineStop P`, and the old name is its own specialization. -/
def predicatesUnified : Nat := 1
/-- Rungs of the ladder now named: `[204]`'s suffix set, and item 10's. -/
def stopSetsNamed : Nat := 2
/-- Producer sites restated at the stronger set: one — the `...` scan.  Every
    other producer keeps its old conclusion, re-derived by `mono`. -/
def producersRestated : Nat := 1
/-- Grammar productions added: none.  The fact was already decided. -/
def newProductions : Nat := 0
/-- Runtime files edited: none.  This item is proof shape only. -/
def runtimeFilesEdited : Nat := 0
/-- The escape's call sites, before and after: the site survives, and one of
    its seven pendings no longer reaches it. -/
def escapeSitesBefore : Nat := 6
def escapeSitesAfter : Nat := 6
def pendingsReachingSiteBefore : Nat := 7
def pendingsReachingSiteAfter : Nat := 6

theorem shipped :
    predicatesUnified = 1 ∧ stopSetsNamed = 2 ∧ producersRestated = 1 ∧
    newProductions = 0 ∧ runtimeFilesEdited = 0 ∧
    escapeSitesAfter = escapeSitesBefore ∧
    pendingsReachingSiteAfter < pendingsReachingSiteBefore := by
  decide

end L4YAML.Tests.Reflections.ProjectAtTheConsumer

end Blanket
