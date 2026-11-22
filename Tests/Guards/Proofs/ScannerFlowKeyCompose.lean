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

/-! # The closed flow collection reads as `[193]`'s JSON key (DOCS item 56)

A depth-0 `[`/`{` is opened over whatever block construct awaits a node, and
whether the collection is that node or the KEY of a mapping entry is decided by
the `:` that arrives after the close.  The frame therefore carries the entry
routes its enclosing construct offers (`FlowBaseRoutes.key`/`.vslot`, paid at
the five open arms) and the close joins them with the collection re-read as
`[161] ns-flow-node(0, block-key)` (`FlowKeyLift`).

ZERO runtime edits: every pin here is an ACCEPT pin at the shape the routes
now serve, plus the three refusals that bound them — a multi-line collection is
not a key at all, a value admits no same-line mapping, and a `---` line admits
no content. -/

namespace L4YAML.Tests.Guards.ScannerFlowKeyCompose

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

-- The root: `rootMapRoute` off the park's own column-0 line start.
#guard emits "[1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
#guard emits "{a: 1}: b\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b",
   "-MAP", "-DOC", "-STR"]
#guard emits "[[1]]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "+SEQ []", "=VAL :1", "-SEQ", "-SEQ",
   "=VAL :b", "-MAP", "-DOC", "-STR"]
-- The compact entry route: the key shares the `-`'s line.
#guard emits "- [1]: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- - [1]: b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ",
   "=VAL :b", "-MAP", "-SEQ", "-SEQ", "-DOC", "-STR"]
-- The nested entry route: the mapping the key opens sits in the value slot.
#guard emits "k:\n  [1]: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "+SEQ []", "=VAL :1", "-SEQ",
   "=VAL :b", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "? a\n: [1]: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "+SEQ []", "=VAL :1", "-SEQ",
   "=VAL :b", "-MAP", "-MAP", "-DOC", "-STR"]
-- The props run decorates the key head (`[161]`'s `propsContent` arm).
#guard emits "&a [1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ [] &a", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
-- The explicit `?`: the collection is the KEY half, the `:` lands later.
#guard emits "? [1]\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :v", "-MAP",
   "-DOC", "-STR"]
#guard emits "? [1] : v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :v",
   "-MAP", "=VAL :", "-MAP", "-DOC", "-STR"]
-- The explicit document's own node.
#guard emits "---\n[1]: b\n"
  ["+STR", "+DOC ---", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]

-- The bounds.  A collection that crossed a line is not a key…
#guard refuses "[1,\n 2]: b\n"
-- …an implicit value admits no same-line mapping (§8.2.2)…
#guard refuses "k: [1]: b\n"
-- …and the `---` line itself admits no content.
#guard refuses "--- [1]: b\n"

end L4YAML.Tests.Guards.ScannerFlowKeyCompose

end Blanket
