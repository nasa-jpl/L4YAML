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

/-! # The escaped break's landing is a fold (DOCS item 87)

`[112] s-double-escaped(n)` is `s-white* c-escape b-non-content
l-empty(n,FLOW-IN)* s-flow-line-prefix(n)`.  Two consequences the escape arm
used to skip:

* each blank line the landing opens is `[70] l-empty`, which folds to a LINE
  FEED — the arm handed those lines, stripped, to the next fold, whose
  `b-non-content` slot then swallowed the landing's own break (one `\n` short
  on every blank landing, and `b-as-space` where the landing was the only
  blank line);
* the blank landing's white run owes the same §6.1 floor as the fold's blank
  lines (`[63] s-indent` is spaces; `[64] s-indent-lt(n)` takes its break
  immediately), so a run that reaches a tab before the floor matches neither
  arm of `[70]` — item 62's gate, which the arm bypassed.

Both close by running the landing through `foldQuotedNewlines` itself, with
`b-as-space` mapped to nothing (the escaped break is excluded from content)
and no trailing trim (`[112]` preserves the `s-white*` before the escape).
The refusals below were accepts; the content rows moved by exactly the
landing's line feed.  Every content row's value matches PyYAML 6.0.3.  The
§1 refusals are the spec's own — `[63] s-indent` is spaces, so a run that
reaches a tab before the floor matches neither arm of `[70]` — and PyYAML
accepts all three, as it accepts item 62's un-escaped family
(`k:⏎  - "a⏎→⏎    b"`): its laxity is uniform here, not a datum about the
escape path. -/

namespace L4YAML.Tests.Guards.ScannerEscapedBreakLanding

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

-- §1 The narrowed shape: a blank landing directly after `\<break>` whose run
-- reaches a tab before the floor.  Entry content indent 4; tab at column 0…
#guard refuses "k:\n  - \"a\\\n\t\n    b\"\n"
-- …and one space short of the floor.
#guard refuses "k:\n  - \"a\\\n \t\n    b\"\n"
-- The mapping-value twin: floor 1, tab at 0.
#guard refuses "k: \"a\\\n\t\n b\"\n"

-- §2 The landing's `l-empty` lines are content: one blank landing line is one
-- line feed (it used to fold to a SPACE — the next fold's `b-as-space`).
#guard emits "\"a\\\n\nb\"\n"
  ["+STR", "+DOC", "=VAL \"a\\nb", "-DOC", "-STR"]
-- Two blank lines, two feeds (one used to be the next fold's trimmed break).
#guard emits "\"a\\\n\n\nb\"\n"
  ["+STR", "+DOC", "=VAL \"a\\n\\nb", "-DOC", "-STR"]
-- A short pure-space run is `s-indent-lt(n)` — still an `l-empty` line.
#guard emits "k:\n  - \"a\\\n \n    b\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"a\\nb", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- `[112]`'s `s-white*` is preserved even across a blank landing (no trim on
-- the escape path).
#guard emits "\"a \\\n\nb\"\n"
  ["+STR", "+DOC", "=VAL \"a \\nb", "-DOC", "-STR"]

-- §3 The boundary, which must NOT move.
-- A CONTENT landing contributes nothing — the escaped break is excluded and
-- the prefix is layout.
#guard emits "\"a\\\n b\"\n"
  ["+STR", "+DOC", "=VAL \"ab", "-DOC", "-STR"]
-- Exactly `n` spaces then a tab on the blank landing IS
-- `s-flow-line-prefix(4)` — legal, and its feed now counts.
#guard emits "k:\n  - \"a\\\n    \t\n    b\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL \"a\\nb", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- At the ROOT the floor is 0, so a tab-only blank landing is `l-empty(0)`
-- (the tab is `s-separate-in-line` past the zero-width `s-indent(0)`).
#guard emits "\"a\\\n\t\nb\"\n"
  ["+STR", "+DOC", "=VAL \"a\\nb", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerEscapedBreakLanding

end Blanket
