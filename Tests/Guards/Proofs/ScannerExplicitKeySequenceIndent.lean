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

/-! # The `?` at a block sequence's own indent (DOCS item 131)

A block sequence reaches the indent stack only when it stands strictly right of
the collection that owns it — `pushSequenceIndent`'s guard is
`col > currentIndent` — so a stacked sequence level's column is a column no
mapping is open at.  An entry that starts there ends the sequence and belongs to
nothing.  §8.2.1 is where the spec says so, and `scanValueValidate` has always
refused the implicit twin (`a:⏎  - x⏎  b: 2` is `trailing content`).

`scanKey` runs the same test, as `scanKeyValidate`'s third check.  The `-` does
NOT, and that asymmetry is the content of the rule: a `-` at a sequence's own
indent is that sequence's next entry.

**What the check is worth is visible in the events.**  Without it the `?`
reaches `pushMappingIndent`, whose guard is the same `col > currentIndent` and
so pushes nothing — the entry is opened at a level no collection holds, and the
parser closes the document and opens a second one for it.  §4 pins the whole
family at the refusal instead.

§1 types the predicate and both refuters.  §2 is the discrimination: one landing
column, three indicators.  §3 is the boundary the check must not cross — a
sequence AT its parent mapping's indent is never stacked, so a `?` there is an
ordinary sibling entry.  §4 is the family the check refuses. -/

namespace L4YAML.Tests.Guards.ScannerExplicitKeySequenceIndent

open L4YAML L4YAML.Scanner
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.IndentStackCover

/-! ## §1  The predicate, and the two refuters it completes -/

/-- The predicate: the cursor's column is the stacked top's, and that top is a
    sequence level.  The top's column IS `currentIndent`, so no `≤` is needed. -/
example (s : ScannerState) (top : IndentEntry) (h : s.indents.back? = some top) :
    atSequenceIndent s = true ↔
      top.isSequence = true ∧ (s.col : Int) = top.column := by
  unfold atSequenceIndent; rw [h]; simp

/-- **The `?`'s refuter** — an accepted explicit key at the top entry's own
    column has a MAPPING level under it. -/
example {s s' : ScannerState} {top : IndentEntry}
    (hok : scanKey s = .ok s') (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.col : Int) = top.column) :
    top.isSequence = false :=
  scanKey_top_not_sequence hok h_noflow h_top h_at

/-- …and the `:`'s, which has said the same since item 129. -/
example {s : ScannerState} {top : IndentEntry}
    (hok : scanValueValidate s = .ok ())
    (h_poss : s.simpleKey.possible = true) (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.simpleKey.pos.col : Int) = top.column)
    (h_le : (s.simpleKey.pos.col : Int) ≤ s.currentIndent) :
    top.isSequence = false :=
  scanValue_top_not_sequence hok h_poss h_noflow h_top h_at h_le

/-- **The cover's sequence disjunct, refuted at the `?`** — the half item 129
    left open.  `preprocess_landing_mem_or_seq` returns the landing width as a
    frame OR the landing on a sequence level; both consumers now close the
    second. -/
example {lo : Nat} {ks : List FrameLevel} {s s' : ScannerState} {top : IndentEntry}
    (hok : scanKey s = .ok s') (h_noflow : s.inFlow = false)
    (h_top : s.indents.back? = some top)
    (h_at : (s.col : Int) = top.column)
    (h_floor : lo ≤ s.col)
    (h_cov : Covered lo ks s) :
    FrameLevel.map s.col ∈ ks :=
  landing_mem_of_key hok h_noflow h_top h_at h_floor h_cov

/-! ## §2  One landing column, three indicators -/

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

-- The stack under all three: a mapping at 0, a sequence at 2, a mapping at 4.
-- The landing is at column 2 — the sequence level's own.
#guard scannerRefuses "a:\n  - b:\n      x: 1\n  ? c\n  : 2\n"
#guard scannerRefuses "a:\n  - b:\n      x: 1\n  c: 2\n"
#guard emits "a:\n  - b:\n      x: 1\n  - c: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "+MAP", "=VAL :b", "+MAP",
   "=VAL :x", "=VAL :1", "-MAP", "-MAP", "+MAP", "=VAL :c", "=VAL :2", "-MAP",
   "-SEQ", "-MAP", "-DOC", "-STR"]

-- …and the same three at a MAPPING landing, where all of them resume.
#guard emits "a:\n  b:\n    x: 1\n  ? c\n  : 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+MAP", "=VAL :x",
   "=VAL :1", "-MAP", "=VAL :c", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
#guard accepts "a:\n  b:\n    x: 1\n  c: 2\n"

/-! ## §3  The boundary the check must not cross

    A block sequence at its parent mapping's OWN indent is never pushed, so the
    stack's top there is the mapping and the check does not fire.  A `?` at that
    column opens the mapping's next entry, and so does a plain key. -/

#guard emits "a:\n- x\n? c\n: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :x", "-SEQ", "=VAL :c",
   "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "a:\n- x\nc: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :x", "-SEQ", "=VAL :c",
   "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "a:\n  b:\n  - x\n  ? c\n  : 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+SEQ", "=VAL :x",
   "-SEQ", "=VAL :c", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]

-- The `?` inside a sequence entry stands to the RIGHT of the level, compact or
-- landed, and is untouched.
#guard accepts "- ? a\n  : b\n"
#guard accepts "a:\n  - ? x\n    : y\n"
#guard accepts "? a\n: b\n? c\n: d\n"

/-! ## §4  The family the check refuses

    Every one of these opens an entry at a stacked sequence level's own column:
    at the document root, under a mapping, with and without a key, with the `?`
    alone on its line.  Each is `trailing content`, as its implicit twin is. -/

#guard scannerRefuses "- a\n? b\n: c\n"
#guard scannerRefuses "- a\nb: c\n"
#guard scannerRefuses "a:\n  - x\n  ? c\n  : 2\n"
#guard scannerRefuses "a:\n  - x\n  ? c\n"
#guard scannerRefuses "a:\n  - x\n  ?\n"
#guard scannerRefuses "- x\n?\n"
#guard scannerRefuses "- - a\n  ? b\n  : c\n"

end L4YAML.Tests.Guards.ScannerExplicitKeySequenceIndent

end Blanket
