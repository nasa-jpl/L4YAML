/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # A flag scoped by the WRONG DIMENSION (Reflection 626)

A machine records a flag so a later step knows it is inside some construct.  The
flag has to expire when the construct ends — and the bug is not forgetting to
clear it, it is clearing it *along the wrong axis*.

`ref-operational-flag-witnesses-history` says a machine that must ACT on its
history has already stored it.  This is the dual: the machine stored a
**different** history than the one it must act on.  The construct's extent lives
on one axis (here: the ENTRY); the flag records a position on another (here: the
LINE).  Both axes are real, both are in the state, and the flag is right exactly
where they coincide.

Three things make it survive review:

1. **They coincide on everything short.**  §2: on the sublanguage with neither a
   line break nor a separator the two scopes are the same function.  That is
   most hand-written input, and all of the examples in the docstring that
   introduced the flag.
2. **The failure is a REFUSAL, not a wrong answer.**  A flag that SUPPRESSES
   work makes the machine reject valid input.  Nothing wrong is ever emitted, so
   no round-trip, no differential comparison and no output check fires — and a
   guard suite pins refusals, so it cannot see one refusal too many
   (Reflection 625 §4).
3. **The counts match.**  §3: the two scopes accept the SAME NUMBER of words
   over the corpus, 670 apiece, on different sets.  A summary statistic shows
   nothing; only the pointwise difference does.

And the repair is one-sided.  §4: correcting the axis moves 14 words in one
direction and 14 in the other.  Fixing the entry boundary does not touch the
line boundary — the residual is a *different* set of inputs, and it stays open.

L4YAML DOCS item 9l, 2026-08-08.  `scanKey` records `explicitKeyLine := some
line`; what it must bound is `[150] ns-flow-pair`'s explicit alternative, which
is ONE entry.  `scanFlowEntry` now clears it.  The residual is the other half —
`{?⏎ a: b}`, one entry, two lines, still refused.
-/

namespace Tests.Reflections.FlagScopedByTheWrongDimension

/-! ## §0  The toy machine

Five tokens.  `br` advances the LINE, `c` advances the ENTRY, `q` raises the
flag, and `col` is the step that consults it.  The machine "accepts" a word when
no `col` was suppressed. -/

inductive Tok where
  | q      -- `?`  — raises the flag
  | a      -- an atom
  | col    -- `:`  — consults the flag
  | c      -- `,`  — next ENTRY
  | br     -- a line break — next LINE
  deriving DecidableEq, Repr, BEq

/-- Which axis the flag is scoped by. -/
inductive Scope where
  | line       -- what the machine shipped
  | entry      -- what the construct actually spans
  deriving DecidableEq, Repr, BEq

/-- Run a word.  `fl`/`fe` are the line and entry the `q` was seen at; the flag
    is "up" when the recorded coordinate still equals the current one on the
    chosen axis — so the ENTRY scope needs no explicit clearing at all, which is
    the tell that it is the right axis. -/
def run (scope : Scope) : List Tok → Bool :=
  go 0 0 none none
where
  go (line entry : Nat) (fl fe : Option Nat) : List Tok → Bool
    | [] => true
    | .br :: rest => go (line + 1) entry fl fe rest
    | .c :: rest => go line (entry + 1) fl fe rest
    | .q :: rest => go line entry (some line) (some entry) rest
    | .a :: rest => go line entry fl fe rest
    | .col :: rest =>
      let suppressed := match scope with
        | .line => fl == some line
        | .entry => fe == some entry
      !suppressed && go line entry fl fe rest

/-! ## §1  The corpus — every word of length ≤ 4 -/

def allToks : List Tok := [.q, .a, .col, .c, .br]

def wordsOfLen : Nat → List (List Tok)
  | 0 => [[]]
  | n + 1 => (wordsOfLen n).flatMap (fun w => allToks.map (fun t => t :: w))

def corpus : List (List Tok) := (List.range 5).flatMap wordsOfLen

#guard corpus.length == 781

/-! ## §2  Why it survives: the two axes coincide on everything short

With no break and no separator there is only one line and one entry, so the two
scopes are literally the same function.  Every example that would be written
down to explain the flag lives here. -/

def flat : List (List Tok) := corpus.filter (fun w => !w.contains .br && !w.contains .c)

#guard flat.length == 121
#guard flat.all (fun w => run .line w == run .entry w)

/-! ## §3  Why a summary statistic misses it: the counts are equal

Both scopes accept 670 of 781 words.  They are not the same 670. -/

#guard (corpus.filter (run .line)).length == 670
#guard (corpus.filter (run .entry)).length == 670
#guard (corpus.filter (fun w => run .line w != run .entry w)).length == 28

/-! ## §4  The repair is one-sided, and the residual is a different set

Correcting the axis is not "clear the flag more often": it moves words in BOTH
directions.  The `c` half is the over-rejection item 9l repaired; the `br` half
is untouched by that repair and remains open. -/

/-- The shipped scope suppresses and the correct one does not: valid input
    REFUSED.  This is `[? a, : b]` — the flag outliving its entry. -/
def overSuppressed : List (List Tok) :=
  corpus.filter (fun w => !run .line w && run .entry w)

/-- The correct scope suppresses and the shipped one does not — the other half
    of the same conflation, reached by a break rather than a separator.  This is
    `{?⏎ a: b}`: one entry, two lines. -/
def underSuppressed : List (List Tok) :=
  corpus.filter (fun w => run .line w && !run .entry w)

#guard overSuppressed.length == 14
#guard underSuppressed.length == 14

-- Each half is characterised by the token that moves ITS axis, and only that
-- one: the over-suppressed words all cross a separator, the under-suppressed
-- ones all cross a break.
#guard overSuppressed.all (fun w => w.contains .c)
#guard underSuppressed.all (fun w => w.contains .br)
#guard overSuppressed.contains [.q, .c, .col]
#guard overSuppressed.contains [.q, .a, .c, .col]
#guard underSuppressed.contains [.q, .br, .col]
#guard underSuppressed.contains [.q, .a, .br, .col]

-- The two halves are disjoint, so repairing one says nothing about the other.
#guard (overSuppressed.filter (fun w => underSuppressed.contains w)).length == 0
-- Twelve of the fourteen over-suppressed words never cross a break at all,
-- which is why the `,` half is the one a single-line corpus can reach.
#guard (overSuppressed.filter (fun w => !w.contains .br)).length == 12

end Tests.Reflections.FlagScopedByTheWrongDimension

end Blanket
