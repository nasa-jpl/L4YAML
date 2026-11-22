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

/-! # The landed `[96]` run reads at the entry's index (DOCS item 57)

A property run on the line BELOW its indicator (`k:⏎  -⏎    &a x`) is the same
single-half run the inline step reads — it has no occurrence of the index to
lift — and item 52's separator supplies the rest at the pending's own `n`.  The
one thing the break costs is the indent STABILITY: preprocessing unwinds the
stack on a fresh line, so the run's pending inherits no floor and the
consumer's transport punts, which costs the run nothing it uses here.

ZERO runtime edits; every pin is an ACCEPT pin. -/

namespace L4YAML.Tests.Guards.ScannerLandedPropsCompose

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

-- The anchored run below an indented sequence entry…
#guard emits "k:\n  -\n    &a x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &a :x", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- …the tag twin…
#guard emits "k:\n  -\n    !t x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL <!t> :x", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- …the empty-key mapping twin…
#guard emits "k:\n  :\n    &a x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL &a :x", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- …the explicit entry's landed value…
#guard emits "k:\n  ? a\n  :\n    &a x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL &a :x", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- …and at the root's own index.
#guard emits "-\n  &a x\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :x", "-SEQ", "-DOC", "-STR"]
-- The sibling snoc after the landed run.
#guard emits "k:\n  -\n    &a x\n  - b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &a :x", "=VAL :b", "-SEQ",
   "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerLandedPropsCompose

end Blanket
