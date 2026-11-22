/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 681 — split the facts, not the question

**The rule.**  When two situations reach the same question with DIFFERENT facts
in hand, split the facts and ask the question once.  Splitting the question
instead — a branch per situation, each with its own copy of the answers — costs
coverage silently: the branch written second gets whichever answers its author
had appetite for, and every answer missing there reads afterwards as a separate
"class" of deferral, one per answer rather than one per missing FACT.  The
count of deferral classes is then an artifact of the duplication, and merging
the branches deletes them all at once (§3, §4).

The merge is only available when each situation can produce the facts in its
own way, so the second half of the rule is: state each fact at the weakest form
BOTH can supply, and make optional the one that only the first can (§2).  A
fact one side cannot give is not a reason to duplicate the question — it is a
reason to make that fact optional and let the answer that needs it punt.

**The instance** (item 60).  A value on the line BELOW its indicator deferred
as three classes — a landed property run, a landed block scalar, a landed fold
— because `indentedValue_reads_at_any_indent` asked its question in two
branches: the break-free one (with the universal separator and indent
stability) got all five answers, the landing got one.  Asked once, with the
separator at the pending's own index, the stability optional, and the FLOOR
derived per branch — from stability inline, and across a break from the
landing's own `s-indent(n)` plus the scanner's dedent check
(`preprocess_some_floor_at_landing`) — every answer serves both, and the three
classes vanish together with one dead disjunct (item 52's landing case,
identical to the inline one once the quantifier moved).

§1 the facts and the answers; §2 the weakest form both sides supply; §3 asked
once, both situations answer; §4 asked twice, the second copy loses coverage —
and the loss counts as one class per ANSWER. -/

namespace L4YAML.Tests.Reflections.SplitTheFactsNotTheQuestion

/-- §1 Three answers a step can give, and the facts they need. -/
inductive Answer where
  | node
  | props
  | scalar
deriving DecidableEq, Repr

/-- The facts: the separator (both situations have it, at the same strength
    once it is stated at the pending's own index), the indent STABILITY (the
    break-free step's alone), and the FLOOR (both, by different routes). -/
structure Facts where
  sep : Bool
  stable : Bool
  floor : Bool
deriving Repr

/-- §2 What each answer needs.  `props` is the only one that reads stability —
    and it reads it as an OPTIONAL extra, so the landing still answers. -/
def answers (f : Facts) : List Answer :=
  (if f.sep then [Answer.node] else []) ++
  (if f.sep then [Answer.props] else []) ++
  (if f.sep && f.floor then [Answer.scalar] else [])

/-- The break-free step: every fact. -/
def inlineFacts : Facts := ⟨true, true, true⟩

/-- The landing: no stability — the unwind may have moved the stack — but the
    floor comes from its own indent and the scanner's dedent check. -/
def landedFacts : Facts := ⟨true, false, true⟩

/-- §3 Asked ONCE, both situations give all three answers. -/
theorem asked_once_inline : answers inlineFacts = [.node, .props, .scalar] := rfl
theorem asked_once_landed : answers landedFacts = [.node, .props, .scalar] := rfl

/-- The two differ only in the fact neither answer here requires. -/
theorem facts_differ : inlineFacts.stable ≠ landedFacts.stable := by decide

/-- §4 Asked TWICE — a branch per situation, the second written with only the
    answer its author reached for. -/
def askedTwice : Bool → List Answer
  | true => answers inlineFacts
  | false => [Answer.node]

/-- The duplicate loses exactly the answers it did not copy… -/
theorem duplicate_loses : askedTwice false = [Answer.node] := rfl

/-- …and what is lost is one class per ANSWER, not one per missing fact: the
    landing had every fact these answers need. -/
theorem loss_is_per_answer :
    (answers landedFacts).length - (askedTwice false).length = 2 := rfl

/-- The merge is sound precisely because the facts, not the question, differ. -/
theorem merge_recovers : askedTwice false ≠ answers landedFacts := by decide

end L4YAML.Tests.Reflections.SplitTheFactsNotTheQuestion

end Blanket
