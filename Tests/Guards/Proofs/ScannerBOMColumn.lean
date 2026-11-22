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

/-! # The BOM spends no column — and nothing parks mid-line with nothing pending
    (DOCS item 35)

Item 35 set out to empty one escape site: the inline residue at
`accum_block_on_noPending`, a `-`/`?`/`:` dispatched from a park that crossed
no break and sits off column 0.  The claim it wanted is an UNREACHABILITY —
in block context a pending-free park is a line start — and the field that
states it (`PendingNode.noPending`'s `h_col`) has exactly one producer outside
flow: the scan's own seed.

The seed could not discharge it.  `scan` consumed a leading
`[3] c-byte-order-mark` with `advance`, which spends a column, so after a BOM
the seed sat at column 1 — and so did the whole first line, one deeper than
every line after it.  That is a runtime defect, not a proof inconvenience:

* `﻿a: 1⏎b: 2` — the second entry dedents below the mapping the first opened,
  and the scan REFUSES a document every other processor accepts.
* `﻿---` — off column 0, so it is not `[203] c-directives-end` at all: the
  document-start marker was read as a plain scalar `--- …`.

§5.2 is explicit that in UTF-8 the BOM is not part of the content, and
`[63] s-indent(n)` counts the characters of the line after it.  `consumeBOM`
(both pipelines) and `SLDocumentPrefix.bom` now agree on that.

§1 pins the two shapes the defect broke.  §2 pins that the BOM is transparent
to every indentation reading, not just those two.  §3 pins the BOM against its
own absence — the same input without the marker, event for event — which is
what "spends no column" means operationally.  §4 pins the block-indicator
boundary item 35 reasons about: the dispatches that reach a pending-free state
all start a line, and a block indicator mid-line after a complete node is
scanner-refused before any pending question is asked.
-/

namespace Tests.Guards.ScannerBOMColumn

open L4YAML

/-- The BOM, as a `String` — written once so no pin carries a bare `\uFEFF`
    that a later reader might mistake for whitespace. -/
private def bom : String := "\uFEFF"

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

/-- Both pipelines reject `input`.  (Error IDENTITY across the twins is pinned
    where the two agree; these four disagree on which check fires first, which
    is a separate question from the verdict this file is about.) -/
private def rejects (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-- Both pipelines' verdicts on `input`, as comparable text — the event stream
    when accepted, the error's own reading when refused. -/
private def outcome (input : String) : String × String :=
  ( (match Events.streamToEvents input with
     | .ok s => "ok:" ++ s | .error e => "err:" ++ toString (repr e))
  , (match Events.streamToEventsIx input with
     | .ok s => "ok:" ++ s | .error e => "err:" ++ toString (repr e)) )

/-- Both pipelines read `input` exactly as they read `bom ++ input` — same
    verdict, same events, same error at the same line and column. -/
private def bomTransparent (input : String) : Bool :=
  outcome (bom ++ input) == outcome input

/-! ## §1  The two shapes the column cost broke

Both were REJECTED or MISREAD before item 35; both are ordinary documents. -/

-- A mapping whose first entry is on the BOM's line: the second entry is at the
-- same indentation, and must not read as a dedent.
#guard emits (bom ++ "a: 1\nb: 2\n")
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-DOC", "-STR"]
-- …and its sequence twin.
#guard emits (bom ++ "- a\n- b\n")
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]

-- `---` after a BOM is `[203] c-directives-end`, which is a column-0 reading:
-- one column of drift turned the marker into a plain scalar.
#guard emits (bom ++ "---\na\n")
  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
#guard emits (bom ++ "---\n- a\n")
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
-- …including through a directive prelude, where `[202] l-document-prefix`'s
-- BOM and `[82] l-directive` meet.
#guard emits (bom ++ "%YAML 1.2\n--- a\n")
  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
-- …and the document-end marker, which is column-0 for the same reason.
#guard emits (bom ++ "a: 1\nb: 2\n...\n")
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-DOC ...", "-STR"]

/-! ## §2  Transparent to every indentation reading

The BOM's column is not a special case of the first line — it is not a column
at all, so a nested collection opened on that line measures from 0. -/

#guard emits (bom ++ "a:\n  b: 1\n")
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :1", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- An INDENTED root collection: `[183]`'s auto-detected width is 2, not 3.
#guard emits (bom ++ "  - a\n")
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
-- A multiline plain scalar folds across the BOM's line the same way.
#guard emits (bom ++ "- a\n  - b\n")
  ["+STR", "+DOC", "+SEQ", "=VAL :a - b", "-SEQ", "-DOC", "-STR"]
-- The degenerate prefixes: BOM alone, and BOM before a comment line.
#guard emits (bom ++ "\n") ["+STR", "-STR"]
#guard emits (bom ++ "# c\na\n") ["+STR", "+DOC", "=VAL :a", "-DOC", "-STR"]

/-! ## §3  The marker against its own absence

"Spends no column" is exactly: prefixing the BOM changes nothing.  These pin
that as an EQUALITY of the two pipelines' whole outputs, so a future reading
that shifts one line by one column fails here even if it lands on some other
accepted parse. -/

#guard bomTransparent "a: 1\nb: 2\n"
#guard bomTransparent "---\na\n"
#guard bomTransparent "  - a\n"
#guard bomTransparent "a:\n  b: 1\n"
#guard bomTransparent "[1, 2]\n"
#guard bomTransparent "\"x\"\n"
#guard bomTransparent "- a\n- b\n"
#guard bomTransparent "%YAML 1.2\n--- a\n"
-- …including on inputs that are rejected: the refusal must not move either.
#guard bomTransparent "a: 1\n b: 2\n"
#guard bomTransparent "\"a\" - b\n"

/-! ## §4  The block-indicator boundary item 35 reasons about

With nothing pending, a block indicator is reached at a LINE START — the
stream's seed (§1/§2 above put that at column 0 with or without a BOM), or a
boundary whose `[79] s-l-comments` the previous step already absorbed.  A
block indicator MID-LINE is a different question and the scanner answers it
first: after a complete node on the same line the run is `trailingContent`,
not `[63] s-indent(n)`. -/

-- Reached with nothing pending, all at a line start.
#guard emits "- a\n" ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "  - a\n" ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits ": a\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :a", "-MAP", "-DOC", "-STR"]
#guard emits "? a\n: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "---\n- a\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits (bom ++ "- a\n")
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits (bom ++ "  - a\n")
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]

-- Mid-line, after a node that is already complete: refused by the scan.
#guard rejects "[1] - b\n"
#guard rejects "\"a\" - b\n"
#guard rejects "[1] ? b\n"
#guard rejects "{a: 1} - b\n"

-- …and the `:` is the one that is NOT refused, because it is not an indent at
-- all: `[154] ns-s-implicit-yaml-key`'s own trailing separation, resolving the
-- node in front of it as a key.  Pinned so §4's refusals read as a statement
-- about `s-indent`, not a ban on indicators after a node.
#guard emits "[1] : b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
#guard emits "\"a\" : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "-MAP", "-DOC", "-STR"]

end Tests.Guards.ScannerBOMColumn

end Blanket
