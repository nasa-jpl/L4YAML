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

/-! # The two floorless producers measure their own push (DOCS item 63)

`[183] l+block-sequence(n)` and `[187] l+block-mapping(n)` are opened by
`pushSequenceIndent` / `pushMappingIndent`, both at the INDICATOR's column —
so a pending's index is discharged by the push it was created alongside.
Items 27/28 proved that for the `-`, the `?` and the `:`, and packaged it
(`dash_floor`, `key_floor_or`, `value_floor_or`, `value_key_floor_or`); two
producers were still handing `IndentFloor … ∨ True` its right disjunct:

* `compact_open_map` — the KEYLESS compact routes `- : v` and `- ? k`
  (`[195] ns-l-compact-mapping`), whose index is the indicator's column, one
  past the `-` at `s-indent(n)` plus `[185]`'s own `s-indent(m)`;
* `colon_open_map_props` — the props-decorated implicit key `&a : v`, whose
  index is the PROPERTY's column, the one `PropsKeyPack` already carried.

With the floors paid, the value shapes that need one — the block scalar and
the multi-line scalar at that index — read there instead of deferring.

ZERO runtime edits; every pin is an ACCEPT pin, and each was an accept
before. -/

namespace L4YAML.Tests.Guards.ScannerCompactKeylessFloor

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

-- §1 `compact_open_map`'s keyless `:` route: the block scalar at the compact
-- index…
#guard emits "- : |\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL |x\\n", "-MAP", "-SEQ",
   "-DOC", "-STR"]
-- …the multi-line quoted value there…
#guard emits "- : \"a\n    b\"\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL \"a b", "-MAP", "-SEQ",
   "-DOC", "-STR"]
-- …and the same one level in, where the index is not 0.
#guard emits "k:\n  - : |\n      x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+MAP", "=VAL :", "=VAL |x\\n",
   "-MAP", "-SEQ", "-MAP", "-DOC", "-STR"]

-- §2 The `?` route, whose push is unconditional in block context — this is
-- the half the proof states as the LEFT disjunct rather than routing through
-- a punt.
#guard emits "- ? |\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL |x\\n", "=VAL :", "-MAP", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- ? \"a\n    b\"\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL \"a b", "=VAL :", "-MAP", "-SEQ",
   "-DOC", "-STR"]
-- The compact fill with a wider `[185] s-indent(m)`.
#guard emits "-   : |\n      x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL |x\\n", "-MAP", "-SEQ",
   "-DOC", "-STR"]

-- §3 `colon_open_map_props`: the key is the PROPERTY run, and the entry index
-- is its column.
#guard emits "&a : |\n  x\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :", "=VAL |x\\n", "-MAP", "-DOC", "-STR"]
#guard emits "&a : \"p\n  q\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :", "=VAL \"p q", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  &a : |\n    x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL &a :", "=VAL |x\\n",
   "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "- &a : |\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &a :", "=VAL |x\\n", "-MAP", "-SEQ",
   "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerCompactKeylessFloor

end Blanket
