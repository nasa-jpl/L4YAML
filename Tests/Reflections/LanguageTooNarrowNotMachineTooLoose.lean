/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # An arm that will not close can mean the LANGUAGE is too narrow (Reflection 625)

A proof arm has to produce a derivation for everything that reaches it.  When it
cannot, the reflex is to ask what the MACHINE lets through that it should not,
and to answer with a guard.  The reflex is right often enough to become
automatic: nine consecutive scanner strictenings answered exactly that question.

The alphabet for pricing such an arm already says otherwise
(`ref-split-mixed-arm-before-pricing`): generate the arm's inhabitants, run them
through the shipped pipeline, and classify — **rejects** ⟹ refutable,
**accepts-correct** ⟹ vocabulary, **accepts-wrong** ⟹ a defect.  The trap is in
the middle verdict.  "Vocabulary" gets read as the *accumulator's* vocabulary —
one more frame constructor, one more pending state — because that is the layer
being built.  It can just as well be the vocabulary of the **grammar the
accumulator targets**: the formalized inductive may simply lack the production
alternative the spec has.

The check is mechanical, and it is not the same as staring at the arm: for each
shape the arm must produce, name the *production alternative* it lands in, then
confirm the inductive HAS that alternative.

And the enumeration pays twice.  The same neighbour list, run through the
shipped pipeline, finds disagreements in BOTH directions — legal shapes the
grammar cannot derive (§2), and legal shapes the pipeline REJECTS (§3).  Some
words are in both, and each half needs its own repair: no guard can supply a
missing constructor, and no constructor can un-reject valid input.  §4 is the
sting — a guard suite cannot find the second kind, because guard suites pin
refusals, and every refusal here survives the repair untouched.

L4YAML DOCS item 9l, 2026-08-08: `[143]`'s `( e-node e-node )` and `[146]`'s
empty key were missing from `SFlowSeqEntry`/`SFlowMapEntry`, and the same
enumeration turned up `[? a, b: c]` — valid, and rejected.
-/

namespace Tests.Reflections.LanguageTooNarrowNotMachineTooLoose

/-! ## §0  The toy language

Four tokens.  A *word* is a `c`-separated list of entries, and an entry is one
of five shapes: an atom, an explicit `q` with an atom, a BARE `q` (the empty
explicit entry), a `col`-headed empty-key entry, and an atom with a trailing
`col` (a pair with an empty value). -/

inductive Tok where
  | q      -- `?`  — opens an explicit entry
  | col    -- `:`  — the value indicator
  | a      -- an atom (a node)
  | c      -- `,`  — the entry separator
  deriving DecidableEq, Repr, BEq

/-- The five legal entry shapes, as token lists. -/
def entryShapes : List (List Tok) :=
  [[.a], [.q, .a], [.q], [.col, .a], [.a, .col]]

/-- Split a word at its `c`s. -/
def entries : List Tok → List (List Tok)
  | [] => [[]]
  | .c :: rest => [] :: entries rest
  | t :: rest => match entries rest with
    | [] => [[t]]
    | e :: es => (t :: e) :: es

/-- **The intended language**: every entry is one of the five shapes. -/
def derives (w : List Tok) : Bool :=
  w != [] && (entries w).all (fun e => entryShapes.contains e)

/-- **The grammar as formalized before item 9l.**  The two arms with an EMPTY
    node — the bare `q` and the `col`-headed empty key — are missing.  Nothing
    about it is wrong; it is NARROW. -/
def derivesNarrow (w : List Tok) : Bool :=
  w != [] && (entries w).all (fun e => [[.a], [.q, .a], [.a, .col]].contains e)

/-! ## §1  The corpus — every word of length ≤ 5 -/

def allToks : List Tok := [.q, .col, .a, .c]

def wordsOfLen : Nat → List (List Tok)
  | 0 => [[]]
  | n + 1 => (wordsOfLen n).flatMap (fun w => allToks.map (fun t => t :: w))

def corpus : List (List Tok) := (List.range 6).flatMap wordsOfLen

#guard corpus.length == 1365
#guard (corpus.filter derives).length == 38
#guard (corpus.filter derivesNarrow).length == 13

/-! ## §2  The grammar is too NARROW

The narrow grammar derives nothing illegal — it is a strict subset.  What it
misses is exactly the two empty-node arms, and every missing word uses one. -/

def missing : List (List Tok) := (corpus.filter derives).filter (fun w => !derivesNarrow w)

#guard (corpus.filter derivesNarrow).all derives          -- narrow ⊆ intended
#guard missing.length == 25
#guard missing.all (fun w => (entries w).any (fun e => e == [.q] || e == [.col, .a]))

-- The two smallest witnesses: the bare `q` (`[? ]`) and the empty-key entry
-- (`[: a]`), plus the bare `q` followed by another entry (`[? , a]`).
#guard missing.contains [.q]
#guard missing.contains [.col, .a]
#guard missing.contains [.q, .c, .a]

/-! ## §3  The machine is too STRICT — same enumeration, other direction

The toy machine IS the pipeline: it recognizes the language, and its one defect
is a flag.  `q` raises the flag; while it is up, a `col` is refused.  The flag
is meant to cover the explicit entry — but nothing lowers it at the `c`, so it
covers the whole rest of the word. -/

def flagOk (clearAtComma : Bool) : List Tok → Bool :=
  go false
where
  go (flag : Bool) : List Tok → Bool
    | [] => true
    | .q :: rest => go true rest
    | .col :: rest => !flag && go flag rest
    | .a :: rest => go flag rest
    | .c :: rest => go (if clearAtComma then false else flag) rest

/-- The shipped machine: the flag is never lowered. -/
def accepts (w : List Tok) : Bool := derives w && flagOk false w

/-- Item 9l: the `c` ENDS the explicit entry, so it lowers the flag. -/
def acceptsFixed (w : List Tok) : Bool := derives w && flagOk true w

/-- Legal words the shipped machine REJECTS. -/
def overRejected : List (List Tok) := (corpus.filter derives).filter (fun w => !accepts w)

#guard overRejected.length == 4
#guard overRejected.contains [.q, .a, .c, .col, .a]     -- `[? a, : b]`
#guard overRejected.contains [.q, .a, .c, .a, .col]     -- `[? a, b: c]`
-- Every one of them puts a `col` after an explicit entry and a separator.
#guard overRejected.all (fun w => w.contains .q && w.contains .c && w.contains .col)
-- Lowering the flag at the separator fixes exactly those, and nothing else.
#guard ((corpus.filter derives).filter (fun w => !acceptsFixed w)).length == 0
#guard (corpus.filter (fun w => acceptsFixed w && !accepts w)).all
         (fun w => w.contains .q && w.contains .c)

/-! ### The two findings are not the same finding

Three of the four over-rejected words are ALSO underivable in the narrow
grammar, and one is not: `[.q, .a, .c, .a, .col]` had a derivation all along and
was still refused.  That one is the proof that the halves are independent — a
constructor could not have repaired it, and a guard could not have repaired the
missing derivations. -/

#guard (overRejected.filter (fun w => missing.contains w)).length == 3
#guard (overRejected.filter derivesNarrow) == [[.q, .a, .c, .a, .col]]

/-! ## §4  Why a guard suite could not have found it

A guard suite pins REFUSALS: "this shape must be rejected".  Every such pin
survives the repair untouched, because the repair only ever turns a rejection
into an acceptance on words that are LEGAL — which the pins, by construction,
never mention.  The suite is not weak; it is pointed the other way. -/

/-- What a guard suite pins: illegal words, which the machine refuses. -/
def rejectionPins : List (List Tok) := corpus.filter (fun w => !derives w)

#guard rejectionPins.length == 1327
#guard rejectionPins.all (fun w => !accepts w)
-- Every pin still holds after the repair: the suite is blind to the defect.
#guard rejectionPins.all (fun w => !acceptsFixed w)
-- The defect lives entirely outside what the pins talk about.
#guard (overRejected.filter (fun w => rejectionPins.contains w)).length == 0

/-! ## §5  What the arm actually needed

Given a frame that has just read a `q`, the close step must produce a derivation
for the entry `[q]`.  Against `derivesNarrow` there is none — and no guard on
the machine can create one, because the machine is right and the word is legal.
The repair is a constructor, in the grammar. -/

#guard derivesNarrow [.q] == false
#guard derives [.q] == true
#guard accepts [.q] == true          -- the pipeline was never the problem

end Tests.Reflections.LanguageTooNarrowNotMachineTooLoose

end Blanket
