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

/-! # The landing serves every answer the inline step does (DOCS item 60)

A value on the line BELOW its indicator was three deferral classes — a landed
property run, a landed block scalar, a landed fold — for one reason: the
question was asked TWICE, once with the facts a break-free step has and once
without them.  Asked once, with the separator at the pending's own index and
the floor derived per branch, the landing answers with the same disjuncts:
across the break the floor comes from the landing's own `s-indent(n)` and the
scanner's dedent check rather than from indent stability.

ZERO runtime edits; every pin is an ACCEPT pin. -/

namespace L4YAML.Tests.Guards.ScannerLandedValueClasses

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

-- The landed block scalar, at an indented sequence entry…
#guard emits "k:\n  -\n    |\n      x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL |x\\n", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- …the folded twin under an empty-key mapping entry…
#guard emits "k:\n  :\n    >\n      x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL >x\\n", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- …and at the root's own index.
#guard emits "-\n  |\n   x\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |x\\n", "-SEQ", "-DOC", "-STR"]
-- The landed value that itself FOLDS: quoted…
#guard emits "k:\n  -\n    \"a\n    b\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"a b", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- …and plain.
#guard emits "k:\n  -\n    a\n    b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a b", "-SEQ", "-MAP",
   "-DOC", "-STR"]

-- The bound: a landing that DEDENTS below the entry is refused, and the
-- reading at the pending's index is not owed for it.
#guard refuses "k:\n  -\n a\n"
#guard refuses "k:\n  :\n a\n"

end L4YAML.Tests.Guards.ScannerLandedValueClasses

end Blanket
