module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The under-run has two halves, and only one is a landing (DOCS item 64)

`WhiteRunUnderRun n` — what a landing's white run is when it fails to supply
`[63] s-indent(n)` — is `j < n` spaces followed by *the run's end* or *a tab*.
Item 64 separates the two:

* the **TAB** half is a scanner REFUSAL.  §6.1 forbids a tab at or left of the
  block's current indent, and `skipToContentWs` throws `tabInIndentation`
  there unless the line stops immediately (a comment, a break, end of input) —
  so a landing that carries a tab under the floor is never followed by the
  content the arm would have to read.  §1 and §2 pin the boundary the proof's
  arithmetic names: refused at every column at or left of `currentIndent`,
  accepted one column past it.

* the **run-end** half survives, and is the pure-space DEDENT
  (`FlowIndexLift.DedentLanding`).  §4 pins that it is INHABITED — these are
  accepted inputs whose value belongs to an enclosing collection, not to the
  entry the pending awaits — which is what makes the disjunct the proof now
  returns a claim rather than a formality.  §5 pins the edge of that domain:
  a dedent that lands between levels, or below all of them, is refused.

ZERO runtime edits: every pin below behaved this way before item 64 too.  The
item is a proof narrowing — it is `skipToContentWs`'s existing gate, carried
out of the preprocessing loop so the accumulation can spend it. -/

namespace L4YAML.Tests.Guards.ScannerLandingDedentSplit

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The TAB half, at an indented pending whose `currentIndent` is 2: refused
-- at column 0, 1 and 2 — every column the floor's `j < n ≤ currentIndent + 1`
-- admits — behind each of the three block indicators.
#guard refuses "k:\n  -\n\tx\n"
#guard refuses "k:\n  -\n \tx\n"
#guard refuses "k:\n  -\n  \tx\n"
#guard refuses "k:\n  :\n\tx\n"
#guard refuses "k:\n  ?\n\tx\n"

-- §2 The boundary, which the item does not move: a tab one column PAST
-- `currentIndent` is `[66] s-separate-in-line`, and the value reads there.
#guard emits "k:\n  -\n   \tx\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :x", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  :\n   \tx\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :x", "-MAP",
   "-MAP", "-DOC", "-STR"]

-- §3 The three exits §6.1 leaves open, and which the proof's conclusion
-- therefore names (`pk = none ∨ pk = some '#'`): a tab under the floor is
-- legal when nothing follows it on the line.  The loop then crosses that
-- line, so the landing the arm reads is a LATER one.
#guard emits "k:\n  -\n\t#c\n   x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :x", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  -\n\t\n   x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :x", "-SEQ", "-MAP",
   "-DOC", "-STR"]

-- §4 The DEDENT half is inhabited: the landing lands on an ENCLOSING
-- collection's own indent, the awaited entry closes with `[72] e-node`, and a
-- sibling opens where the pending's index never reaches.
#guard emits "k:\n  -\nj: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :", "-SEQ", "=VAL :j",
   "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  :\nj: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL :j", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  -\n  - x\nj: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :", "=VAL :x", "-SEQ",
   "=VAL :j", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- …and at a nonzero landing width, where the enclosing entry is itself
-- indented: the dedent's `j` is 2, the pending's index 4.
#guard emits "a:\n  b:\n    -\n  c: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+SEQ", "=VAL :",
   "-SEQ", "=VAL :c", "=VAL :v", "-MAP", "-MAP", "-DOC", "-STR"]

-- §5 The edge of that domain, which is the scanner's and not the grammar's: a
-- landing that matches NO open level is `trailingContent`, and one that
-- unwinds past every level restarts a document body without a marker.
#guard refuses "k:\n  -\n a\n"
#guard refuses "k:\n  -\na\n"

end L4YAML.Tests.Guards.ScannerLandingDedentSplit

end Blanket
