module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The indent stack is monotone, and the cover gets its floor (DOCS item 130)

Item 129 carried `Covered ks s` — every open mapping level is a frame — through
every scanner step and attached both of its ends.  What it did not do is pay it,
and the payment is where the shape of the statement is decided: a producer that
opens a mapping at `k` hands over the frames its own route knows, and the levels
BELOW the node its park fused are not among them.  `a:⏎  b: 1⏎  : 2` holds levels
0 and 2 open (§3 pins both `+MAP`s) while the landing at width 2 reads as a fresh
root map whose frames are `[2]` — so `Covered 0 [2]` is false there and
`Covered 2 [2]` is true.  §3 checks exactly that pair on the stack itself.

**What makes the floored statement payable is monotonicity.**  On a stack whose
consecutive columns strictly increase, a fact about the TOP is a fact about the
whole stack: a top at or left of `k` leaves `k` as the only level at or right of
`k`.  That is `ScannerState.WellFormed`'s fifth conjunct, and — like the sixth
(item 128) — it was proved for the state operations and for nothing that a
production proof can reach.  `IndentStackMono` carries it through every step.

**And the floor itself comes from the landing, when the landing unwinds.**  The
unwind stops on its own guard, so the top it leaves is at or left of the column
it unwound to; the guard's other exit is a stack popped to the sentinel, at `-1`.
The escape is a preprocess that does not unwind at all, which hands its incoming
stack straight on — named in §4, where the cover transports rather than being
re-seeded.

§1 types the predicate, its consequence, its writers, its step and its seed.
§2 is the runtime: strictly increasing levels, and the landing BETWEEN two of
them that both pipelines refuse.  §3 is the floor's discrimination on a concrete
stack.  §4 is the escape and what still owes it. -/

namespace L4YAML.Tests.Guards.IndentStackMonotone

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.IndentStackMono L4YAML.Proofs.IndentStackCover
open L4YAML.Proofs.IndentStackBase

/-! ## §1  The predicate, its consequence, its writers, its step and its seed -/

/-- The predicate: consecutive entries strictly increase. -/
example (s : ScannerState) :
    Mono s ↔ ∀ (i : Nat) (h : i + 1 < s.indents.size),
      (s.indents[i]'(by omega)).column < (s.indents[i + 1]'h).column :=
  Iff.rfl

/-- **The consequence the cover spends**: every entry is at or left of the top. -/
example {s : ScannerState} (h : Mono s) : ∀ e ∈ s.indents, e.column ≤ s.currentIndent :=
  h.le_currentIndent

/-- The writers: the unwind pops, and each of the two pushes is guarded by
    `col > currentIndent` — the strict step the new top owes the old one. -/
example {s : ScannerState} (col : Int) (h : Mono s) : Mono (unwindIndents s col) :=
  unwindIndents_mono s col h

example {s : ScannerState} (col : Int) (h : Mono s) (hb : SentinelBase s) :
    Mono (pushMappingIndent s col) := pushMappingIndent_mono s col h hb

example {s : ScannerState} (col : Int) (h : Mono s) (hb : SentinelBase s) :
    Mono (pushSequenceIndent s col) := pushSequenceIndent_mono s col h hb

/-- The step, and the seed. -/
example {s s' : ScannerState} (hok : scanNextToken s = .ok (some s'))
    (h : Mono s) (hb : SentinelBase s) : Mono s' := scanNextToken_mono hok h hb

example (input : String) : Mono (ScannerState.mk' input) := mk'_mono input

/-! ## §2  The runtime: the levels strictly increase, and a landing between two
    of them is refused -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

private def scannerRefuses (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .error _ => true
   | _, _ => false) &&
  (match Events.streamToEvents input, Events.streamToEventsIx input with
   | .error _, .error _ => true
   | _, _ => false)

-- (a) Three mapping levels at 0, 2 and 4 — one `+MAP` each, opened in order.
#guard emits "a:\n  b:\n    c: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+MAP", "=VAL :c",
   "=VAL :1", "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]

-- …and a dedent landing that pops the deepest and resumes at an open level.
#guard emits "a:\n  b:\n    c: 1\n  d: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+MAP", "=VAL :c",
   "=VAL :1", "-MAP", "=VAL :d", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]

-- (b) A landing that names no level is refused by both pipelines: strictly
-- BETWEEN two open ones (columns 0 and 2, landing at 1), and to the LEFT of the
-- only one an indented root opens (item 128's family).  That is the runtime's
-- own reason for reading a landing as a level rather than as a column.
#guard scannerRefuses "a:\n  b: 1\n c: 2\n"
#guard scannerRefuses "  a: 1\nb: 2\n"

-- (c) …while a landing AT an open level resumes, whichever level it is.
#guard accepts "a:\n  b: 1\n  c: 2\n"
#guard accepts "a:\n  b:\n    c: 1\n  d: 2\n"

/-! ## §3  The floor, on a stack the runtime builds

    The state below is `a:⏎  b: 1⏎  : 2`'s: the sentinel, the root map's level at
    0, and the inner map's at 2 (§2's `+MAP`s are those two).  A producer that
    reads the landing at 2 as a fresh root map hands over the frames `[2]` — and
    that list does not cover level 0, which is open and real.  With the floor at
    the landing's own level it covers everything the statement asks about. -/

-- The input, and its two open mapping levels: one `+MAP` at column 0, one at 2.
#guard emits "a:\n  b: 1\n  : 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :1", "=VAL :",
   "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]

private def twoLevels : ScannerState :=
  { ScannerState.mk' "" with
      indents := #[ { column := -1, isSequence := false },
                    { column := 0, isSequence := false },
                    { column := 2, isSequence := false } ] }

private lemma twoLevels_mono : Mono twoLevels := by
  intro i hi
  have hsz : twoLevels.indents.size = 3 := rfl
  rw [hsz] at hi
  match i, hi with
  | 0, _ =>
    show (twoLevels.indents[0]'(by decide)).column
      < (twoLevels.indents[1]'(by decide)).column
    decide
  | 1, _ =>
    show (twoLevels.indents[1]'(by decide)).column
      < (twoLevels.indents[2]'(by decide)).column
    decide

/-- The stack is monotone: `-1 < 0 < 2`. -/
example : Mono twoLevels := twoLevels_mono

/-- **The unfloored cover is false there**: level 0 is open, a mapping level, at
    a non-negative column, and `0 ∉ [2]`. -/
example : ¬ Covered 0 [FrameLevel.map 2] twoLevels := by
  intro h
  have hmem : { column := (0 : Int), isSequence := false } ∈ twoLevels.indents := by
    simp [twoLevels]
  have := h { column := 0, isSequence := false } hmem rfl (by decide)
  simp at this

/-- **The floored one is true**, and it is the top that says so. -/
example : Covered 2 [FrameLevel.map 2] twoLevels :=
  covered_singleton_of_top_le twoLevels_mono (by decide)

/-- The floor only weakens: a lower floor covers a higher one's obligations. -/
example {lo lo' : Nat} {ks : List FrameLevel} {s : ScannerState} (h : Covered lo ks s)
    (hle : lo ≤ lo') : Covered lo' ks s := h.raise_floor hle

/-! ## §4  Where the floor comes from, and the escape that still owes one

    The unwind supplies the floor outright.  What does not is a preprocess that
    never unwinds — its `needIndentCheck` was already down — and it is named
    here by its own disjunct: the stack it hands on is the one it was given, so
    the cover TRANSPORTS across it (item 129's step) instead of being re-seeded.
    A threading pays that side; this item builds the side that needs no history. -/

example {s : ScannerState} {col : Int} (h : SentinelBase s) (hnn : 0 ≤ col) :
    (unwindIndents s col).currentIndent ≤ col := unwindIndents_top_le h hnn

example {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : SentinelBase s) :
    s'.currentIndent ≤ (s'.col : Int) ∨ s'.indents = s.indents :=
  preprocess_top_le_col hok h

-- The escape's family: a landing whose step does not unwind is one that crossed
-- no break — the `:` and the value on the key's own line — and there the stack
-- is the one the key's own landing left.
#guard accepts "a: 1\nb: 2\n"
#guard accepts "- a: 1\n  b: 2\n"

end L4YAML.Tests.Guards.IndentStackMonotone

end Blanket
