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

/-! # The compact collection composes on the indicator's own line (DOCS item 33)

Row 12's inline residue is a mid-line park that crosses no break, so
`[79] s-l-comments` — the evidence every close in the accumulation spends — does
not exist there and cannot be manufactured.  Item 19 called the family
irreducible on those grounds and it was, for the arms that were looking: every
close-and-reopen route goes through a landing.

What the SPEC offers instead is a production none of those arms names.
`[185] s-l+block-indented(n,c)` has four alternatives and the accumulation had
consumers for two of them (`s-l+block-node` and `e-node s-l-comments`).  The
other two are

    s-indent(m) ns-l-compact-sequence(n+1+m)
    s-indent(m) ns-l-compact-mapping(n+1+m)

and they ask for no comments at all, because a compact collection HAS no line of
its own — it shares the entry indicator's.  That is exactly the shape of the
input the residue is looking at.

So the residue at a `-`-parked pending is not a weaker landing case; it is a
different `[185]` alternative, and the whites the step left in front of the new
indicator are its `s-indent(m)` — the same run item 22 reads at a landing,
through the same splitter.

Two things are worth pinning beyond the shapes themselves.

* **The index is `n+1+m`.** Both constructors said `n+m` — off by the column the
  entry indicator occupies — for as long as they had no producer and no
  consumer, which is to say since they were written.  Nothing could disagree
  with an index nothing instantiates.  At `n+m` the SIBLINGS of a compact entry
  are required one column to the left of where the input puts them, so
  `- - a⏎  - b` (§2) is the pin that would have caught it.
* **The compact pending is an ORDINARY one.** `- - a` parks `pendingBlock` at
  the inner index and `- : a` parks `pendingMapValue`, so everything downstream
  — the sibling snoc, the nested open, the value readings of items 23–29 — fires
  again one level in without knowing it is inside a compact collection.

§4 pins the boundary: a tab in the compact `s-indent(m)` is refused, which is
the same §6.1 rule §3 of `ScannerTabBeforeBlockEntry` records one production up.
-/

namespace Tests.Guards.ScannerCompactCollectionCompose

open L4YAML

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-- Both pipelines reject `input`, and with the same error. -/
private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error e, .error e' => e == e'
  | _, _ => false

/-! ## §1  `ns-l-compact-sequence` — the second `-` on the first one's line

`SIndent m` is the run between the two indicators, so `m` is measured, not
pinned, and the outer entry may sit at any width of its own. -/

#guard emits "- - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "  - - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "-   - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "- -\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "---\n- - a\n"
  ["+STR", "+DOC ---", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
-- The pending it parks is an ordinary `pendingBlock`, so the arm fires again
-- on itself: compact nests compactly to any depth.
#guard emits "- - - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- - - - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ",
   "-SEQ", "-SEQ", "-DOC", "-STR"]

/-! ## §2  …and its `[186]` tail, which is where the index shows

`ns-l-compact-sequence(N)`'s later entries are `s-indent(N) c-l-block-seq-entry`,
so a sibling of the compact entry stands at column `N = n+1+m` — the column the
compact `-` itself is at.  These are the pins that fix the arithmetic. -/

#guard emits "- - a\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- - a\n  - b\n  - c\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "=VAL :b", "=VAL :c", "-SEQ",
   "-SEQ", "-DOC", "-STR"]
-- A wider `s-indent(m)` moves the whole tail with it.
#guard emits "-   - a\n    - b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-SEQ", "-DOC",
   "-STR"]
#guard emits "  - - a\n    - b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-SEQ", "-DOC",
   "-STR"]
-- A dedent back to the OUTER collection ends the compact one.
#guard emits "- - a\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "=VAL :b", "-SEQ", "-DOC",
   "-STR"]

/-! ## §3  `ns-l-compact-mapping` — the `:` and `?` on the entry's line

The same two `[188]` alternatives `indicator_open_map` opens at a landing —
`[189]`'s empty-key entry and `[186]`'s explicit key with an `e-node` value —
under `[195]` instead of under `[187]` + `[199]`. -/

#guard emits "- : a\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL :a", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- ? a\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- :\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL :", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- ?\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL :", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "-   : a\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL :a", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "  - : a\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL :a", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- ? \"k\"\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL \"k", "=VAL :", "-MAP", "-SEQ", "-DOC",
   "-STR"]
-- The awaited node is whatever `[196]` admits, so items 23–29's value readings
-- fire inside a compact entry too.
#guard emits "- - &x a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL &x :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "- - \"a\"\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL \"a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "- - [1]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ", "-SEQ", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- : [1]\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "+SEQ []", "=VAL :1", "-SEQ",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- - |\n    t\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL |t\\n", "-SEQ", "-SEQ", "-DOC", "-STR"]
-- The compact forms mix where the grammar has a compact slot: `-` and `?`
-- take `s-l+block-indented`.  An implicit `:` takes `[194] s-l+block-node`,
-- which has NO compact alternative — the scanner refuses that direction
-- (item 48's `sameLineBlockCollection`).
#guard emits "- - : a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "=VAL :", "=VAL :a", "-MAP", "-SEQ",
   "-SEQ", "-DOC", "-STR"]
#guard refuses "- : - a\n"
#guard emits "- ? - a\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ", "=VAL :a", "-SEQ", "=VAL :",
   "-MAP", "-SEQ", "-DOC", "-STR"]

/-! ## §4  The tab, one production down

`[185]`'s `s-indent(m)` is `[63] s-indent`, so it is spaces — a tab in the run
between the entry indicator and the compact one was used as indentation, and
§6.1 forbids it.  The scanner refuses all three, from `[66]`'s backward scan
(items 31/32's checks, reached here from a run that is NOT the whole line). -/

#guard refuses "-\t- a\n"
#guard refuses "- \t- a\n"
#guard refuses "- \t? a\n"
#guard refuses "- \t: a\n"
#guard refuses "- \t\t: a\n"
#guard refuses "?\t- a\n"
#guard refuses ": \t- a\n"
#guard refuses "- - \t- a\n"

/-! ## §5  What this item does NOT reach, and both are still accepted

`- a: 1` is a compact mapping too, and the commonest one in the language, but
its `:` arrives with the entry's content ALREADY parked (`pendingBlockContent`),
so re-reading that content as `[193]`'s implicit key is item 25's pack on a
different pending — a different obstruction, not a harder case of this one.

Sibling compact-mapping entries (`- : a⏎  : b`) close and re-open through
`[211]`'s document continuation rather than through `[195]`'s tail, because
`pendingMapValue` carries no entries-level closure — the same
over-approximation `: a⏎: b` has ridden since item 13 (action row 19). -/

#guard emits "- a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- - a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ",
   "-SEQ", "-DOC", "-STR"]
#guard emits "- : a\n  : b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL :a", "=VAL :", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- ? a\n  ? b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :", "=VAL :b", "=VAL :",
   "-MAP", "-SEQ", "-DOC", "-STR"]

end Tests.Guards.ScannerCompactCollectionCompose

end Blanket
