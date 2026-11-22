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

/-! # A blank fold line's tab is measured against the floor (DOCS item 62)

`[70] l-empty(n,c)` opens with `s-line-prefix(n,c)` or `[64] s-indent-lt(n)`,
and both begin in `[63] s-indent`, which is *spaces* (§6.1).  A tab is admitted
only by `[69] s-flow-line-prefix(n)`'s trailing `s-separate-in-line?` — that
is, only once the `n` spaces are already there — and `s-indent-lt(n)` takes its
break immediately after its short run.  So a blank interior fold line whose
white run reaches a tab BEFORE the floor matches neither arm, and both
pipelines used to fold it anyway.

This is a RUNTIME narrowing: the accepts below were already accepts, the
refusals below were accepts and are now `tabInIndentation` — reported at the
blank line's own tab, which is where the fold's existing §6.1 gate reads once
the blank-line loop stops there. -/

namespace L4YAML.Tests.Guards.ScannerBlankFoldTabRefused

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

-- §1 The narrowed shape: fewer than `n` spaces, then a TAB, on a blank line
-- inside the fold.  Here the entry's content indent is 4.
-- Double-quoted, tab at column 0…
#guard refuses "k:\n  - \"a\n\t\n    b\"\n"
-- …and one space short of the floor.
#guard refuses "k:\n  - \"a\n \t\n    b\"\n"
-- The single-quoted twin.
#guard refuses "k:\n  - 'a\n\t\n    b'\n"
-- The flow PLAIN twin (the same fold, `[134] s-ns-plain-next-line`).
#guard refuses "k:\n  - [a\n\t\n    b]\n"
-- A mapping value's quoted scalar: the floor is 1, the tab sits at 0.
#guard refuses "k: \"a\n\t\n b\"\n"
-- The offending line need not be the first blank one.
#guard refuses "k:\n  - \"a\n\n\t\n    b\"\n"

-- §2 The boundary, which must NOT move.
-- Exactly `n` spaces and then a tab IS `s-flow-line-prefix(4)`.
#guard emits "k:\n  - \"a\n    \t\n    b\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"a\\nb", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- A short PURE-SPACE run is `[64] s-indent-lt(4)`.
#guard emits "k:\n  - \"a\n  \n    b\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"a\\nb", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- So is the empty run.
#guard emits "k:\n  - \"a\n\n    b\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"a\\nb", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- At the ROOT the floor is 0, so `s-indent(0)` is already met and the tab is
-- `s-separate-in-line` — a tab-only blank line is a legitimate `l-empty(0)`.
#guard emits "\"a\n\t\nb\"\n"
  ["+STR", "+DOC", "=VAL \"a\\nb", "-DOC", "-STR"]
#guard emits "\"a\n \t\nb\"\n"
  ["+STR", "+DOC", "=VAL \"a\\nb", "-DOC", "-STR"]
#guard emits "[a\n\t\nb]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :a\\nb", "-SEQ", "-DOC", "-STR"]

-- §3 The BLOCK plain walk (`skipBlankLinesLoop`) reads its blank lines at the
-- SAME production — this section used to call it `l-empty(n,block-in)` and
-- pin the fold as accepted, but `[134] s-ns-plain-next-line(n,c)` folds
-- through `[74] s-flow-folded(n)`, whose empty lines are `l-empty(n,flow-in)`,
-- exactly the ones above.  Item 100 gates that loop too; the family's own pins
-- are in `ScannerPlainBlankFoldTab`.
#guard refuses "k:\n  - a\n\t\n    b\n"

end L4YAML.Tests.Guards.ScannerBlankFoldTabRefused

end Blanket
