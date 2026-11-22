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

/-! # A park's own COLUMN, at the two parks that had none (DOCS item 68)

Item 59 gave `pendingBlock` its park column and item 66 spent it: the landing
that under-runs a flow open with a TAB in its indent run is `[63]`'s own
refusal, because a column-0 landing that is not the park is a landing that
crossed a break — `LandingTabFacts`' premise.  `pendingProps` and
`pendingMapValue` carried no column, so the same input rode `scannerDrop`
there; item 68 gives them one and the two arms join `pendingBlock`'s.

The same field carries item 67a's floor onto the flow stack, so a collection
opened over either park reads its interior at the park's own index.

* §1 the OPEN's under-run, both halves, at all three parks.
* §2 the interior floor those parks now hand the stack: a multi-line scalar
  inside the collection is measured against the ENCLOSING block indent, and
  all three scalar styles measure the same way.
* §3 where the route index is 0 the arithmetic is vacuous — a props run parked
  at a mapping VALUE closes at 0, so its collection reads at 0.

ZERO runtime edits: every pin below behaved this way before item 68 too. -/

namespace L4YAML.Tests.Guards.ScannerFlowParkColumn

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

private def errAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.underIndentedFlowContent l c) => some (l, c)
  | _ => none

private def tabAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.tabInIndentation l c) => some (l, c)
  | _ => none

-- §1 The open's under-run at a held property RUN (`k:⏎  b:⏎    &x`) and at a
-- mapping VALUE (`k:⏎  a:`).  §8.1 refuses the run-end half, §6.1 the tab.
#guard errAt "k:\n  b:\n    &x\n  [1]\n" == some (3, 2)
#guard tabAt "k:\n  b:\n    &x\n \t[1]\n" == some (3, 1)
#guard tabAt "k:\n  a:\n \t[1]\n" == some (2, 1)
-- …and one column past the floor both read.
#guard emits "k:\n  b:\n    &x\n     [1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :b", "+SEQ [] &x", "=VAL :1",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]

-- §2 The floor the park hands the stack.  A mapping value at index 2 opens a
-- collection whose interior reads at 2: a continuation at column 2 under-runs,
-- at column 3 it folds.  All three scalar styles.
#guard refuses "k:\n  a: [\"p\n  q\"]\n"
#guard emits "k:\n  a: [\"p\n   q\"]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []", "=VAL \"p q",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]
#guard refuses "k:\n  a: [p\n  q]\n"
#guard emits "k:\n  a: [p\n   q]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []", "=VAL :p q",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]
#guard refuses "k:\n  a: ['p\n  q']\n"
#guard emits "k:\n  a: ['p\n   q']\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []", "=VAL 'p q",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]

-- …and a property run parked at a sequence ENTRY closes at the entry's index,
-- so its collection measures there too — the tab is refused at or left of the
-- floor and is an `[66] s-white` past it.
#guard refuses "k:\n  - &x [\"p\n  q\"]\n"
#guard refuses "k:\n  - &x [\"p\n\tq\"]\n"
#guard emits "k:\n  - &x [\"p\n   q\"]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ [] &x", "=VAL \"p q", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - &x [\"p\n   \tq\"]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+SEQ [] &x", "=VAL \"p q", "-SEQ",
   "-SEQ", "-MAP", "-DOC", "-STR"]

-- §3 The run parked at a mapping VALUE routes at 0, so the collection it rides
-- into reads at 0 and a continuation at column 2 is fine — the index, not the
-- run's own column, is what the interior measures.
#guard emits "k:\n  &x [\"p\n  q\"]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ [] &x", "=VAL \"p q", "-SEQ", "-MAP",
   "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerFlowParkColumn

end Blanket
