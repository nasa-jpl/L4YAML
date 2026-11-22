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

/-! # The anchored null key composes (DOCS item 49)

`&a : b` is a parked `[96] c-ns-properties` run read whole as the implicit
KEY: `[161] ns-flow-node`'s props-only alternative under `[193]
ns-s-block-map-implicit-key`, then `[189]`'s `:` and the parked value.  Item
48 refused the run's same-line `-`/`?` (no compact alternative behind
properties) and left the `:` as the family's one grammatical inhabitant;
item 49 composes it through `PropsKeyPack`'s entry route — no runtime
change, so every pin here is an ACCEPT pin, and what the item moves is the
derivation (the props park's `:` arm fires `colon_fires_props_key` instead
of the escape).

The pins fix the event shape — the run is ONE key node (`=VAL &a :`), not a
property attached to the value — at the root, under a mapping value, under a
sequence entry, with both halves, with an empty value, and with a sibling
entry continuing the mapping. -/

namespace L4YAML.Tests.Guards.ScannerPropsNullKeyCompose

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

-- The root landing, one half at a time and both.
#guard emits "&a : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "!t : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL <!t> :", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "&a !t : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a <!t> :", "=VAL :b", "-MAP", "-DOC", "-STR"]
-- The `( e-node s-l-comments )` value: `[189]`'s other arm.
#guard emits "&a :\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :", "=VAL :", "-MAP", "-DOC", "-STR"]
-- The run parked at an entry route (item 41's frames), key'd the same way.
#guard emits "k:\n  &p : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL &p :", "=VAL :b", "-MAP",
   "-MAP", "-DOC", "-STR"]
#guard emits "- &p : b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :", "=VAL :b", "-MAP", "-SEQ",
   "-DOC", "-STR"]
-- The entry is an ordinary `[188]` sibling: the mapping continues.
#guard emits "&a : b\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerPropsNullKeyCompose

end Blanket
