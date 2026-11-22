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

/-! # The `,` ends the explicit-key entry (DOCS item 9l)

Items 9g and 9j pinned the flow `?`'s two *character* neighbours — what may
stand before it, and that a separation must follow.  This pins its *entry*
boundary, and it turned out to be wrong on both layers at once.

## The scanner half

`scanKey` records `explicitKeyLine := some line` so that content on the `?`'s
line reads as the explicit key's own node rather than as a fresh implicit key —
the guard in `saveSimpleKey` and branch (1) of `scanValueClearKey`.  That scope
is the ENTRY, not the line:

    [150] ns-flow-pair(n,c) ::= ( "?" s-separate(n,c)
                                   ns-flow-map-explicit-entry(n,c) )
                              | ns-flow-pair-entry(n,c)

is ONE `ns-flow-seq-entry`, and `[138]`/`[141]`'s `","` starts the next one.
Leaving the line set made every later entry on that line unable to reserve a
simple key, so the retroactive `.key` token was never written — and
`parseFlowSequenceLoop` dispatches on exactly that token.  The result was a
shipped **over-rejection**:

    [? a, b: c]        [? a, : b]        [? a, : ]        [? a,⏎: b]

all valid, all handled correctly one collection kind over (the flow-MAPPING
parser does not need the marker), all rejected with `expected ']' but reached
end of tokens`.  `scanFlowEntry` now clears `explicitKeyLine`; §1 pins the
repair and §3 pins what the repair must not break.

## The grammar half

The same boundary is missing from the surface grammar, in the opposite
direction — it is too NARROW where the scanner was too broad.  Every `?`-headed
constructor of `SFlowSeqEntry`/`SFlowMapEntry` demanded an `SFlowNode` key, but

    [143] ns-flow-map-explicit-entry(n,c) ::= ns-flow-map-implicit-entry(n,c)
                                            | ( e-node /* Key */
                                                e-node /* Value */ )

has an arm with no key at all, and `[151] ns-flow-pair-entry`'s
`c-ns-flow-map-empty-key-entry` [146] has an empty key with a `:`.  So `[? ]`,
`{? }`, `[? , a]`, `[: a]` and `[:]` parse — correctly, and have done all
along — with no derivation to point at.  §4 pins the shapes the three new
constructors (`explicitPairEmptyNodes`, `emptyKeyValue`, `emptyKeyEmpty` on the
sequence side; `explicitEmptyNodes` on the mapping side) exist to derive.

Nothing here is pinned as a rejection except §5, which re-checks that repairing
the boundary did not re-open item 9j.
-/

namespace Tests.Guards.ScannerFlowExplicitEntryBoundary

open L4YAML
open L4YAML.Events

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection.
    Equal pairs mean the two pipelines agree. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match streamToEvents input with | .ok s => some s | .error _ => none)
  , (match streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected` (one event per
    list element; `streamToEvents` adds the trailing newline). -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-- Both pipelines reject `input`. -/
private def bothReject (input : String) : Bool := bothEvents input == (none, none)

/-! ## §1  The over-rejection, repaired

Every one of these was `expected ']' but reached end of tokens` before item 9l.
The events are the ones the flow-MAPPING twin already produced for the same
entries (§2). -/

-- `[? a, b: c]` — an implicit-key entry after an explicit one.
#guard emits "[? a, b: c]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "+MAP {}", "=VAL :b", "=VAL :c", "-MAP", "-SEQ", "-DOC", "-STR"]

-- `[? a, : b]` — an EMPTY-key entry after an explicit one.
#guard emits "[? a, : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "+MAP {}", "=VAL :", "=VAL :b", "-MAP", "-SEQ", "-DOC", "-STR"]

-- `[? a, : ]` — …with an empty value too.
#guard emits "[? a, : ]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "+MAP {}", "=VAL :", "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]

-- Across a line break: `saveSimpleKey`'s guard did not fire here, but branch (1)
-- of `scanValueClearKey` cleared the reservation instead — the same defect
-- reached by the other consumer of `explicitKeyLine`.
#guard emits "[? a,\n: b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "+MAP {}", "=VAL :", "=VAL :b", "-MAP", "-SEQ", "-DOC", "-STR"]

-- Two entries on: the scope is per-entry, not just "the entry after the `?`".
#guard emits "[? a, b: c, : d]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "+MAP {}", "=VAL :b", "=VAL :c", "-MAP",
   "+MAP {}", "=VAL :", "=VAL :d", "-MAP", "-SEQ", "-DOC", "-STR"]

/-! ## §2  What always worked, unchanged

The flow MAPPING never showed the defect — `parseFlowMappingLoop` reads a
missing `.key` as an empty key — which is why the sequence twin went unnoticed.
An explicit entry that CONSUMES its `:` was fine too, because `scanValue` clears
`explicitKeyLine` itself. -/

#guard emits "{? a, b: c}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :", "=VAL :b", "=VAL :c",
   "-MAP", "-DOC", "-STR"]

#guard emits "{? a, : b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :", "=VAL :", "=VAL :b",
   "-MAP", "-DOC", "-STR"]

-- `? a: b` consumes a `:`, so the line was already cleared before the `,`.
#guard emits "[? a: b, : c]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP",
   "+MAP {}", "=VAL :", "=VAL :c", "-MAP", "-SEQ", "-DOC", "-STR"]

-- No explicit key at all: the empty-key entry was always reachable.
#guard emits "[a, : b]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :a", "+MAP {}", "=VAL :", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]

-- A single explicit entry, and two of them: neither needs a reservation.
#guard emits "[? a]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[? a, ? b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "+MAP {}", "=VAL :b", "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]

/-! ## §3  What clearing at the `,` must not break

`explicitKeyLine` also serves the BLOCK explicit key, and a block key's node may
be a flow collection whose commas run through `scanFlowEntry`.  Those commas
belong to the NESTED collection, and the block `:` on the following line
resolves through the indent stack rather than through `explicitKeyLine` — so
clearing is invisible to it. -/

#guard emits "? [a, b]\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :a", "=VAL :b", "-SEQ",
   "=VAL :v", "-MAP", "-DOC", "-STR"]

#guard emits "? {a: 1, b: 2}\n: v\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :1", "=VAL :b",
   "=VAL :2", "-MAP", "=VAL :v", "-MAP", "-DOC", "-STR"]

-- The ordinary block explicit key, with no flow anywhere.
#guard emits "? a\n: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]

-- A block explicit key on ONE line: `:` on the `?`'s line is the value
-- indicator of a nested implicit key, so the explicit key is the COMPACT
-- mapping `{[a, b]: v}` and the entry's own value is empty (§8.2.2 [196]).
-- The pair below is the point — the comma-free twin has the same shape, so a
-- `,` inside the key's node does not change how the trailing `:` is read.
#guard emits "? [a] : v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "+SEQ []", "=VAL :a", "-SEQ", "=VAL :v",
   "-MAP", "=VAL :", "-MAP", "-DOC", "-STR"]

#guard emits "? [a, b] : v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "+SEQ []", "=VAL :a", "=VAL :b", "-SEQ",
   "=VAL :v", "-MAP", "=VAL :", "-MAP", "-DOC", "-STR"]

#guard emits "? {a: 1, b: 2} : v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "+MAP {}", "=VAL :a", "=VAL :1",
   "=VAL :b", "=VAL :2", "-MAP", "=VAL :v", "-MAP", "=VAL :", "-MAP",
   "-DOC", "-STR"]

/-! ## §4  The shapes the new grammar constructors derive

These have parsed correctly all along; what they did not have was a derivation.
`[143]`'s `( e-node e-node )` arm is `explicitPairEmptyNodes` /
`explicitEmptyNodes`; `[146]`'s empty key is the sequence-side `emptyKeyValue` /
`emptyKeyEmpty`, whose mapping twins were already there. -/

-- `( e-node e-node )`: the explicit entry with no key and no value.
#guard emits "[? ]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "{? }\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :", "=VAL :", "-MAP", "-DOC", "-STR"]

#guard emits "[? , a]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :", "-MAP",
   "=VAL :a", "-SEQ", "-DOC", "-STR"]

#guard emits "{? , a}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :", "=VAL :", "=VAL :a", "=VAL :",
   "-MAP", "-DOC", "-STR"]

-- `c-ns-flow-map-empty-key-entry` in a flow SEQUENCE.
#guard emits "[: a]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :a", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[:]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :", "-MAP",
   "-SEQ", "-DOC", "-STR"]

#guard emits "[: a, : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :", "=VAL :a", "-MAP",
   "+MAP {}", "=VAL :", "=VAL :b", "-MAP", "-SEQ", "-DOC", "-STR"]

/-! ## §5  Item 9j is still closed

The repair is about the `,` AFTER the entry, not about the separation the `?`
demands.  A `?` with a flow indicator directly after it is still rejected. -/

#guard bothReject "[?]\n"
#guard bothReject "[?,a]\n"
#guard bothReject "{?}\n"
#guard bothReject "{?,a}\n"
#guard bothReject "[a, ?]\n"

end Tests.Guards.ScannerFlowExplicitEntryBoundary

end Blanket
