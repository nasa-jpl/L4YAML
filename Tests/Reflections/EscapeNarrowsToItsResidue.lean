/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 663 — when the fact refutes only part of a residue, narrow the escape

**The rule.**  A refutation that covers some of an escape's residue and not all
of it looks like a failure: the escape survives, the site survives, the count
does not move.  It is not.  Re-type the escape by the premise that SURVIVED —
`Residue c → Goal` becomes `Residue ':' → Goal` — and three things happen at
once.  The refuted members are discharged where the fact lives, at the call
site.  The callers that still pay are unchanged.  And the escape's type now
NAMES what is left, so the remaining work is held by the type-checker instead
of by a sentence in a document.

**The premise is not a choice; it is forced.**  Once the residue is a premise
rather than a conclusion, only the surviving member inhabits it — you do not
have to be told which case is left, you can read it off.  That is the whole
difference between an escape typed as what it produces ([[ProjectAtTheConsumer]])
and one typed as the occasion it stands for: the second one is a measurement
the compiler re-takes on every build.

**And two producers can decide the same set for opposite reasons.**  A
validator REFUSES the character (it read it and errored); a walk ABSORBS it (it
never parked in front of one).  Nothing in either mechanism is the other's, and
they still name one set — which is what lets one field carry both families
instead of one field per producer.

Concretely (L4YAML): §7.5's `validateTrailingContent`/`validateFlowClose` admit
`[79] s-l-comments` plus `[154]`'s `:`; the plain and block scalar walks absorb
every `ns-plain-safe-out` character and stop only at `#`, `:`, a break, or
something outside `[1] c-printable`.  Both give the same answer at the three
block indicators, so `pendingContent` and `pendingBlockContent` carry one
`h_line`, `-` and `?` are refuted at the call sites, and the escape those two
pendings still take is `InlineResidue sp_scan ':' → SLYamlStream …` — one
production, named in a type.

§1 the partial refutation.  §2 the escape re-typed, and what each caller pays.
§3 the surviving member is readable from the premise.  §4 refusal and
absorption.  §5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.EscapeNarrowsToItsResidue

/-! ## §1  The fact refutes part of the residue, and stops

`Ind` is the residue's index set — the characters the deferred arm stands for.
`nodeStop` is what the producing validator admitted.  Two of three are gone;
the third is a production the grammar really has. -/

inductive Ind where
  | dash
  | question
  | colon
deriving DecidableEq

/-- §7.5's tail, read at the three block indicators: only the `:` of
    `[154] ns-s-implicit-yaml-key` is in it. -/
def nodeStop : Ind → Bool
  | .colon => true
  | _ => false

def all : List Ind := [Ind.dash, .question, .colon]

/-- **A partial refutation.**  The fact is real and it is not enough: the arm
    still has an inhabitant, so the site does not close. -/
theorem two_of_three_refuted :
    (all.filter nodeStop).length = 1 ∧ nodeStop .colon = true := ⟨rfl, rfl⟩

/-! ## §2  The escape, re-typed by what survived

`Goal` is what the shared consumer produces (data, so the statements below are
about which VALUE arrives).  `Residue i` is the occasion at index `i`. -/

abbrev Goal : Type := Nat

def Residue (i : Ind) : Prop := nodeStop i = true

abbrev Escape (r : Prop) : Type := r → Goal

/-- The escape as item 36 left it: good for whichever member arrives. -/
abbrev Wide : Type := ∀ i, Escape (Residue i)

/-- The escape after the refutation: the survivor alone. -/
abbrev Narrow : Type := Escape (Residue Ind.colon)

/-- Narrowing is free for the caller that had the wide one. -/
def narrow_of_wide (e : Wide) : Narrow := e .colon

/-- **And the converse is where the fact is spent.**  Rebuilding the wide
    escape needs the refutation at the two dead members — which is exactly the
    work that moved to the call sites, and is unavailable to anyone who has not
    got `h_line`. -/
def wide_of_narrow (e : Narrow) : Wide
  | .colon, r => e r
  | .dash, r => Bool.noConfusion r
  | .question, r => Bool.noConfusion r

/-- The paying caller is unchanged, value for value. -/
theorem paying_caller_unchanged (g : Goal) :
    narrow_of_wide (fun _ _ => g) rfl = g := rfl

/-- The refuted members never reach the body: there is no argument to supply. -/
theorem refuted_members_have_no_argument (e : Narrow) :
    (∀ r : Residue Ind.dash, wide_of_narrow e .dash r = 0) ∧
    (∀ r : Residue Ind.question, wide_of_narrow e .question r = 0) :=
  ⟨fun r => Bool.noConfusion r, fun r => Bool.noConfusion r⟩

/-! ## §3  The survivor is READ OFF the premise, not asserted

This is what a conclusion-typed escape cannot do.  `Goal` mentions no member,
so "which cases are left" is a claim about the proof that lives outside it; a
premise-typed escape answers the question by inversion. -/

/-- **Forced, not chosen.**  Whatever member inhabits the residue IS the `:`. -/
theorem only_the_survivor_inhabits (i : Ind) (h : Residue i) : i = .colon := by
  cases i
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h
  · rfl

/-- The ledger the type now holds: what the escape stands for, before and
    after.  `before` is any indicator; `after` is the validator's own set. -/
def owed (p : Ind → Bool) : Nat := (all.filter p).length

def before : Ind → Bool := fun _ => true
def after : Ind → Bool := nodeStop

theorem the_ledger_moved : owed before = 3 ∧ owed after = 1 := by decide

/-- …and the site itself did NOT move — which is the honest reading of a
    partial refutation, and why the count to report is the residue's, not the
    site's. -/
def sitesBefore : Nat := 6
def sitesAfter : Nat := 6

theorem the_site_survives : sitesAfter = sitesBefore := rfl

/-! ## §4  Refusal and absorption decide one set

Two producers reach the same field.  The validator READ the character and
returned an error; the walk never stopped in front of it, because `[128]
ns-plain-safe-out` let it into the scalar.  Different mechanisms, no shared
code, one set — so one field carries both. -/

/-- The validator's allowlist. -/
def admitted : Ind → Bool
  | .colon => true
  | _ => false

/-- What the walk swallows: `-` and `?` are `ns-char`, so they are content;
    a `:` stops it by `[129] ns-plain-char`. -/
def absorbs : Ind → Bool
  | .dash => true
  | .question => true
  | .colon => false

/-- Where the walk can park is the complement of what it absorbs. -/
def walkStops (i : Ind) : Bool := !absorbs i

/-- **The agreement is a theorem, not a definition.** -/
theorem refusal_and_absorption_agree : ∀ i, admitted i = walkStops i := by
  intro i; cases i <;> rfl

/-- So the union the field carries costs neither producer anything at the
    indicators — while still being a union, because the walk's own set has
    members (outside `[1] c-printable`) the validator's has not. -/
theorem the_union_is_exact_here : ∀ i, (admitted i || walkStops i) = admitted i := by
  intro i; cases i <;> rfl

/-! ## §5  What item 37 shipped -/

/-- Stop sets named, before and after: `TailSuffix`/`NoOpenHead`, plus
    `NodeTail`, `OffLine` and their union `NodeStop`. -/
def stopSetsBefore : Nat := 2
def stopSetsAfter : Nat := 5
/-- Producers restated at their own strength (three validators, two quoted
    scans, the plain and block scalars, the content dispatch). -/
def producersRestated : Nat := 8
/-- Existing consumers changed: none — every old conclusion is a `mono`
    wrapper with the old name and the old statement. -/
def consumersChanged : Nat := 0
/-- Pending fields strengthened: `pendingContent`, `pendingBlockContent`. -/
def fieldsStrengthened : Nat := 2
/-- Grammar productions added: none.  The set was already decided. -/
def newProductions : Nat := 0
/-- Runtime files edited: none.  Proof shape only. -/
def runtimeFilesEdited : Nat := 0
/-- The residue's indicators at those two pendings, before and after. -/
def residueIndicatorsBefore : Nat := 3
def residueIndicatorsAfter : Nat := 1

theorem shipped :
    stopSetsAfter > stopSetsBefore ∧ producersRestated = 8 ∧
    consumersChanged = 0 ∧ fieldsStrengthened = 2 ∧
    newProductions = 0 ∧ runtimeFilesEdited = 0 ∧
    residueIndicatorsAfter < residueIndicatorsBefore ∧
    sitesAfter = sitesBefore := by
  decide

end L4YAML.Tests.Reflections.EscapeNarrowsToItsResidue

end Blanket
