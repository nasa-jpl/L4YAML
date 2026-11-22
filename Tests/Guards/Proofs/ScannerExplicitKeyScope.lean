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

/-! # The explicit-key stamp is scoped to its flow level (DOCS item 98)

A block `?` records `explicitKeyLine`/`explicitKeyCol` so that the landed `:`
is read as `[197] l-block-map-explicit-value(n)`'s `s-indent(n) ":"` — whose
value slot `[201] s+block-indented` has the compact alternatives — rather
than as an implicit `:`, whose `[194]` slot admits no same-line collection
(item 48's stamp).  The stamp is per-flow-level state: a flow open pushes the
pair onto `explicitKeyStack` and clears it, the matching close restores it.
Without the scoping, a `,` or `:` inside the key's own flow collection
consumed the stamp, and the landed `:` refused its compact value
(`? {a: b}⏎: - w` — `sameLineBlockCollection`, an over-refusal of valid
YAML); the `?`-line save guard also leaked INTO the nested collection, so a
flow-sequence pair there never wrote its retroactive `.key` token
(`? [a: b]⏎: v` — `expected ']' but reached end of tokens`). -/

namespace L4YAML.Tests.Guards.ScannerExplicitKeyScope

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

-- §1 The stamp survives the key's own flow collection: the landed `:` takes
-- `[197]`'s compact value.
#guard emits "? {a: b}\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP",
   "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "? {a: }\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "? [a: b]\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :b",
   "-MAP", "-SEQ", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "? [1, 2]\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "? [1,\n   2]\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- The compact-MAPPING value twin, and the nested/deep shapes.
#guard emits "? {a: b}\n: ? w\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP",
   "+MAP", "=VAL :w", "=VAL :", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "? {a: {b: c}}\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "+MAP {}", "=VAL :b",
   "=VAL :c", "-MAP", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC",
   "-STR"]
#guard emits "? [[1, 2]]\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "+SEQ []", "=VAL :1", "=VAL :2",
   "-SEQ", "-SEQ", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "? [? a, b]\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :",
   "-MAP", "=VAL :b", "-SEQ", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC",
   "-STR"]
-- The indented twin, and the sibling chain.
#guard emits "k:\n  ? {a: b}\n  : - w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "+MAP {}", "=VAL :a",
   "=VAL :b", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-MAP", "-DOC",
   "-STR"]
#guard emits "? {a: b}\n: - w\n? c\n: - x\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP",
   "+SEQ", "=VAL :w", "-SEQ", "=VAL :c", "+SEQ", "=VAL :x", "-SEQ",
   "-MAP", "-DOC", "-STR"]

-- §2 The `?`-line save guard stops at the nested collection's edge: the
-- flow-sequence pair inside the key writes its retroactive `.key`.
#guard emits "? [a: b]\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :b",
   "-MAP", "-SEQ", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "? [a: b, c]\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :b",
   "-MAP", "=VAL :c", "-SEQ", "=VAL :v", "-MAP", "-DOC", "-STR"]

-- §3 The boundary, which must NOT move: the flow `?`'s own-level clears
-- (`,` ends its entry), the leak shapes, and the plain-value neighbors.
#guard emits "[? a, b: c]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "+MAP {}", "=VAL :b", "=VAL :c", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "[? a, : b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :", "-MAP",
   "+MAP {}", "=VAL :", "=VAL :b", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "[? [x], b]\n"
  ["+STR", "+DOC", "+SEQ []", "+MAP {}", "+SEQ []", "=VAL :x", "-SEQ",
   "=VAL :", "-MAP", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "[? a]: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "+MAP {}", "=VAL :a", "=VAL :",
   "-MAP", "-SEQ", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "? {a: b}\n: v\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP",
   "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "? {a: b}: v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "+MAP {}", "=VAL :a", "=VAL :b",
   "-MAP", "=VAL :v", "-MAP", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "? a\n: - w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :w", "-SEQ", "-MAP",
   "-DOC", "-STR"]

-- §4 Item 48's refusals keep their ground: the stamp still refuses what
-- `[194]` has no derivation for.
#guard refuses "k: - a\n"
#guard refuses "k: v: w\n"
#guard refuses "{a: b}: - w\n"
#guard refuses ": - a\n"

end L4YAML.Tests.Guards.ScannerExplicitKeyScope

end Blanket
