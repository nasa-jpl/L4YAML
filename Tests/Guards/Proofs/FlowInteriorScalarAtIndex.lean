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

/-! # A flow-interior scalar's floor is the ENCLOSING block indent (DOCS item 67a)

Item 45 lifted a scalar token's reading at 0 to every index and returned the
MULTI-LINE ones as `*Crossed` witnesses, which item 46's collapse then rode.
Item 67a builds those readings at the flow stack's own index instead, and the
whole arithmetic rests on one runtime fact, pinned here: **a flow scalar's
continuation lines are measured against the enclosing BLOCK indent, not
against the scalar's own start column.**

* §1 the floor is exact, and it is `currentIndent`.  A `-` at column 2 puts
  the sequence's indent at 2, so the flow node inside it reads at 3 — and a
  continuation line clears `s-indent(3)` at column 3 and no earlier, however
  far right the scalar itself started.  All three scalar styles measure the
  same way, which is why one loop lemma serves them.
* §2 **and §6.1's own gate covers the tab**, at every column at or left of the
  floor: `s-indent(n)` is spaces, so a tab there is not indentation.  Past the
  floor it is `[66] s-separate-in-line`'s `s-white` and reads fine.
* §3 the ROOT is where the two coincide and the arithmetic is vacuous: with no
  enclosing block collection the index is 0, `s-indent(0)` asks for nothing,
  and the tab is a leading white.

ZERO runtime edits: every pin below behaved this way before item 67a too. -/

namespace L4YAML.Tests.Guards.FlowInteriorScalarAtIndex

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

-- §1 A sequence entry at index 2: the flow node reads at 3, and so does every
-- continuation line inside it.  The double-quoted scalar starts at column 6.
#guard refuses "k:\n  - [\"a\nb\"]\n"
#guard refuses "k:\n  - [\"a\n  b\"]\n"
#guard emits "k:\n  - [\"a\n   b\"]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ []", "=VAL \"a b", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]

-- …the single-quoted and plain walks take the same floor, from their own
-- checks (`collectSingleQuotedLoop`'s and item 50's flow break).
#guard refuses "k:\n  - [a\n  b]\n"
#guard emits "k:\n  - [a\n   b]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ []", "=VAL :a b", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - ['a\n   b']\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ []", "=VAL 'a b", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]

-- One level out, the floor moves with the enclosing collection rather than
-- with the scalar: a `-` at column 0 reads its flow node at 1.
#guard refuses "- [\"a\nb\"]\n"
#guard emits "- [\"a\n b\"]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ []", "=VAL \"a b", "-SEQ", "-SEQ", "-DOC",
   "-STR"]

-- §2 The tab: refused at or left of the floor, a leading white past it.
#guard refuses "k:\n  - [\"a\n  \tb\"]\n"
#guard refuses "k:\n  - [\"a\n\t b\"]\n"
#guard emits "k:\n  - [\"a\n   \tb\"]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ []", "=VAL \"a b", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]

-- §3 At the root the index is 0, so both questions are vacuous.
#guard emits "[\"a\n\tb\"]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL \"a b", "-SEQ", "-DOC", "-STR"]
#guard emits "[\"a\nb\"]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL \"a b", "-SEQ", "-DOC", "-STR"]

end L4YAML.Tests.Guards.FlowInteriorScalarAtIndex

end Blanket
