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

/-! # The block-scalar collection loop's TAB stop is refused (DOCS item 97)

The loop's non-empty stop is a line of fewer-than-indent spaces and then a
non-space non-break character.  When that character is a TAB the line derives
nowhere: `[167]`/`[168]`'s `s-indent(≤n)`/`s-indent(<n)` and `[169]
l-trail-comments`' head are all `[63] s-indent`, which is *spaces* (§6.1),
and nothing after the scalar can absorb the line either — a following
token's own indent is `[63]` too.  The preprocessing walk used to skip it
(its §6.1 gate exempts blank and comment landings), so both pipelines
accepted inputs the spec has no derivation for.

This is a RUNTIME narrowing: the accepts below were already accepts, the
refusals below were accepts and are now `tabInIndentation` — reported at the
stop line's own tab, by `scanBlockScalarBody`'s gate (legacy) and
`blockScalarTabStopErrIx` (indexed). -/

namespace L4YAML.Tests.Guards.ScannerBlockScalarTabStop

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

-- §1 The narrowed shape: the stop line opens with spaces (fewer than the
-- content indent) and then a TAB.  A `#` behind the tab does not save it —
-- `[169]`'s head indent is spaces-only.
#guard refuses "k: |\n  x\n\t# c\na: b\n"
-- One space, then the tab.
#guard refuses "k: |\n  x\n \t# c\na: b\n"
-- A tab-only line after the body is not `l-empty` either.
#guard refuses "? |\n  x\n\t\n: - w\n"
#guard refuses "k: |\n  x\n\t\na: b\n"
-- The folded, chomping and explicit-indicator twins.
#guard refuses "k: >\n  x\n\t# c\na: b\n"
#guard refuses "k: |-\n  x\n\t# c\na: b\n"
#guard refuses "k: |2\n  x\n\t# c\na: b\n"
-- The explicit-key park (`? |` — item 95's family).
#guard refuses "? |\n  x\n\t# c\n: - w\n"
-- The offending line need not be the first one past the body.
#guard refuses "k: |\n  x\n\n\t# c\na: b\n"

-- §2 The boundary, which must NOT move.
-- A spaces-only comment head IS `[169] l-trail-comments`.
#guard emits "k: |\n  x\n# c\na: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL |x\\n", "=VAL :a", "=VAL :b",
   "-MAP", "-DOC", "-STR"]
#guard emits "k: |\n  x\n # c\na: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL |x\\n", "=VAL :a", "=VAL :b",
   "-MAP", "-DOC", "-STR"]
-- A tab-led line AFTER a valid head is `[78] l-comment`, whose
-- `s-separate-in-line` admits tabs — the loop never sees it.
#guard emits "k: |\n  x\n# c\n\t# d\na: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL |x\\n", "=VAL :a", "=VAL :b",
   "-MAP", "-DOC", "-STR"]
-- A tab at (or past) the full content indent is CONTENT — `[27] nb-char`
-- admits it, and the loop consumes the line.
#guard emits "k: |\n  x\n  \t y\na: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL |x\\n\\t y\\n", "=VAL :a",
   "=VAL :b", "-MAP", "-DOC", "-STR"]
-- An over-indented `#` line is content too, not a comment.
#guard emits "k: |\n  x\n   # c\na: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL |x\\n # c\\n", "=VAL :a",
   "=VAL :b", "-MAP", "-DOC", "-STR"]
-- A zero-indent scalar owns every line, tabs included: no stop, no gate.
#guard emits "--- |\nx\n\ty\n"
  ["+STR", "+DOC ---", "=VAL |x\\n\\ty\\n", "-DOC", "-STR"]
-- The plain sibling stop (no tab) is untouched.
#guard emits "k: |\n  x\na: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL |x\\n", "=VAL :a", "=VAL :b",
   "-MAP", "-DOC", "-STR"]

-- §3 The refusals the family already had keep their position: a tab line
-- with CONTENT behind it was refused by the walk's own §6.1 gate at the
-- same line and column the new gate reports, so the error is unchanged.
#guard refuses "k: |\n  x\n\tz\na: b\n"
#guard refuses "k: |\n  x\n\t: v\na: b\n"
#guard refuses "k: |\n\t x\na: b\n"

end L4YAML.Tests.Guards.ScannerBlockScalarTabStop

end Blanket
