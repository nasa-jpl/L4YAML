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

/-! # §8.1's OTHER half — the floor inside an open flow collection (DOCS item 69)

§8.1's floor for a flow OPEN is `scanNextToken_checkFlowValueIndent`, guarded
on `!inFlow`, so it says nothing once a collection is open (items 66, 172).  The half
that runs INSIDE one is `scanNextToken_dispatchStructural`'s, and it is both
wider and narrower: it refuses EVERY character at or left of `currentIndent`,
not just `[` and `{`.  That is what refutes the run-END half of a flow-interior
separator whose landing under-runs the stack's reading index.

* §1 the refusal, at each frame transition the interior takes: a `,` entry, a
  close, a nested open, a flushed `[96]` run, and the `?`/`:` key routes — with
  the reading one column right beside it.
* §2 the floor is the ENCLOSING block's `currentIndent + 1`, so it moves: at
  the top level nothing under-runs and a continuation at column 0 reads.
* §3 the TAB half, which the same landing can take instead.  §6.1 refuses it
  too; the proof does not yet, because refuting it needs the flow park's own
  column — so these pin what the next increment has to reach.

ZERO runtime edits: every pin below behaved this way before item 69 too. -/

namespace L4YAML.Tests.Guards.ScannerFlowInteriorUnderRun

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def errAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.underIndentedFlowContent l c) => some (l, c)
  | _ => none

private def tabAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.tabInIndentation l c) => some (l, c)
  | _ => none

-- §1 The enclosing block map sits at indent 2, so `currentIndent` is 1 and the
-- collection reads its interior at 2 — a landing at 2 is at the floor and
-- refused, one column right it composes.

-- (a) a `,` entry.
#guard errAt "k:\n  a: [1,\n  2]\n" == some (2, 2)
#guard emits "k:\n  a: [1,\n   2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []", "=VAL :1", "=VAL :2",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]

-- (b) a CLOSE — item 50: `]` and `}` are content of the same node and clear
-- the same floor.
#guard errAt "k:\n  a: [1,\n  ]\n" == some (2, 2)
#guard emits "k:\n  a: [1,\n   ]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []", "=VAL :1",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]
#guard errAt "k:\n  a: {x: 1,\n  }\n" == some (2, 2)
#guard emits "k:\n  a: {x: 1,\n   }\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+MAP {}", "=VAL :x", "=VAL :1",
   "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]

-- (c) a NESTED open, which pushes a child frame at the same index.
#guard errAt "k:\n  a: [1,\n  [2]]\n" == some (2, 2)
#guard emits "k:\n  a: [1,\n   [2]]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []", "=VAL :1", "+SEQ []",
   "=VAL :2", "-SEQ", "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]

-- (d) a held `[96]` run — the gap's `props` arm, whose leading separation is
-- preprocessing's own.
#guard errAt "k:\n  a: [&x\n  1]\n" == some (2, 2)
#guard emits "k:\n  a: [&x\n   1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []", "=VAL &x :1",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]

-- (e) the `:` key route, over a plain node and over a flushed run.
#guard emits "k:\n  a: {x\n   : 1}\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+MAP {}", "=VAL :x", "=VAL :1",
   "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]
#guard errAt "k:\n  a: {&x\n  : 1}\n" == some (2, 2)
#guard emits "k:\n  a: {&x\n   : 1}\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+MAP {}", "=VAL &x :", "=VAL :1",
   "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]

-- (f) the `?` route, and its held-run twin (item 9g rejects `{&x ? y}` for its
-- own reason, so only the floor's refusal is pinned there).
#guard errAt "k:\n  a: {?\n  x}\n" == some (2, 2)
#guard emits "k:\n  a: {?\n   x}\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+MAP {}", "=VAL :x", "=VAL :",
   "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]
#guard errAt "k:\n  a: {&x\n  ? y}\n" == some (2, 2)

-- §2 The floor is the ENCLOSING block's, so it moves with it.  At the top
-- level `currentIndent` is -1 and the reading index is 0, where a landing
-- cannot under-run at all; under a `- ` entry it is 0, so column 0 is refused
-- and column 1 reads.
#guard emits "[1,\n2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard errAt "- [1,\n2]\n" == some (1, 0)
#guard emits "- [1,\n 2]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-SEQ", "-DOC", "-STR"]

-- §3 The TAB half of the same landing: §6.1 refuses it at or left of the
-- floor, and past the floor it is an `[66] s-white` like any other.  This is
-- the half the proof still rides `scannerDrop` for.
#guard tabAt "k:\n  a: [1,\n  \t2]\n" == some (2, 2)
#guard tabAt "k:\n  a: [1,\n \t2]\n" == some (2, 1)
#guard emits "k:\n  a: [1,\n   \t2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []", "=VAL :1", "=VAL :2",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerFlowInteriorUnderRun

end Blanket
