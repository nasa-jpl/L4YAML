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

/-! # The compact key measures its own column (DOCS item 59)

An entry's index IS its indicator's column, and the park sits one character
past it — so a pending that carries its own column hands `[195]`'s compact
route the datum item 28 had to punt (`ImplicitKeyPack`'s column conjunct:
"the compact route cannot measure its own column").  With it, `- a:` opens its
value pending WITH a floor, and the value shapes that need one — the block
scalar and the multi-line scalar at the compact index — read there instead of
deferring.

ZERO runtime edits; every pin is an ACCEPT pin. -/

namespace L4YAML.Tests.Guards.ScannerCompactKeyFloorCompose

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

-- The block scalar at a compact index: the sequence twin…
#guard emits "- - |\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL |x\\n", "-SEQ", "-SEQ", "-DOC", "-STR"]
-- …and the keyless mapping twin.
#guard emits "- : |\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL |x\\n", "-MAP", "-SEQ",
   "-DOC", "-STR"]
-- The multi-line value at a compact index.
#guard emits "- - \"a\n    b\"\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL \"a b", "-SEQ", "-SEQ", "-DOC", "-STR"]
-- The compact KEY's own value: `- a:` opens its pending with a floor now.
#guard emits "- a: |\n    b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL |b\\n", "-MAP", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- a: \"p\n    q\"\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL \"p q", "-MAP", "-SEQ",
   "-DOC", "-STR"]
-- …with a property run in front of the value (the props consumer's k+1 arm).
#guard emits "- a: &x |\n    b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL &x |b\\n", "-MAP", "-SEQ",
   "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerCompactKeyFloorCompose

end Blanket
