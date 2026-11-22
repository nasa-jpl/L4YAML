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

/-! # The props-decorated fold reads at the run's route index (DOCS item 55)

The last fold shape: a held `[96]` run at an INDENTED route (`k+1`) whose
decorated value crosses a line — `k:⏎  - &a "x⏎     y"`.  The props
consumer's one-question lemma gains a fourth answer (the fixed-index content
at `k+1`, items 53/54's readings fired off the pending's inherited floor),
and its consumer is the first arm's park with `SFlowNode.propsContent` at
the route index.  ZERO runtime edits; all pins ACCEPT. -/

namespace L4YAML.Tests.Guards.ScannerPropsFoldCompose

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

#guard emits "k:\n  - &a \"x\n     y\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &a \"x y", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  - &a x\n     y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &a :x y", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  : !t 'a\n    b'\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL <!t> 'a b",
   "-MAP", "-MAP", "-DOC", "-STR"]
-- The sibling snoc after the decorated fold.
#guard emits "k:\n  - &a x\n     y\n  - c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &a :x y", "=VAL :c",
   "-SEQ", "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerPropsFoldCompose

end Blanket
