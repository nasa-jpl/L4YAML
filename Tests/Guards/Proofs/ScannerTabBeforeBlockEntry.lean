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

/-! # A tab in front of a block entry is indentation (DOCS item 31)

Row 12's remainder listed the TAB branch of `gstar_white_sIndent_or_tab` as
four escape sites "expected VACUOUS": `[63] s-indent` is spaces only, and the
scanner was supposed to answer `tabInIndentation` before any block indicator
could reach the accumulation.  It answered for ONE of the three.

`scanBlockEntry` (`-`) has scanned back over the preceding whitespace since
Step 5b.2.  `scanKey` (`?`) checked only the tab AFTER the indicator, and
`scanValue` (`:`) only the tab after the colon — so with one space in front of
the tab, enough to put the column past `currentIndent` where `skipToContentWs`
reads tabs as `[66] s-separate-in-line`, four FAMILIES of shape PARSED in both
pipelines that no `[187] l+block-mapping` derivation reaches — the empty key,
the explicit key, and an implicit key plain or quoted.  §3 pins them, refused.

The line the fix has to hold is §1's: the same `␣␣→` prefix is LEGAL in front
of a flow node or a plain scalar, because `[197] s-l+flow-in-block` reaches
those through `s-separate-lines`, whose `[69] s-flow-line-prefix(n)` is
`s-indent(n) s-separate-in-line?` — a genuine separation slot.  DK95:00 is
exactly that shape and must keep parsing.  `[187]`'s entry has no such slot:
it is `s-indent(n+m) ns-l-block-map-entry(n+m)` and nothing between.  So the
check is anchored at the ENTRY's first character — the key when there is one
(§2: the run between key and `:` IS separation), the indicator when there is
not.

Unlike items 22–30, this item DOES edit runtime files (four scanners, two per
pipeline).  These are the shapes it moves, and the shapes it must not.

§5 records item 32, which moves none of them: the same verdicts, computed from
the coordinate `[187]`'s `s-indent(n)` names rather than from the simple-key
machine's saved position, so that the accumulator's TAB branch can refute.
-/

namespace Tests.Guards.ScannerTabBeforeBlockEntry

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

/-! ## §1  The separation reading, which the item must not lose

A line prefix that ends in `s-separate-in-line?` admits a tab, and every one of
these lands on `[69] s-flow-line-prefix` — the value is a flow node or a plain
scalar, not a block collection. -/

-- DK95:00 itself: the tab precedes a PLAIN SCALAR value.
#guard emits "foo:\n \tbar\n"
  ["+STR", "+DOC", "+MAP", "=VAL :foo", "=VAL :bar", "-MAP", "-DOC", "-STR"]
-- …at two spaces as well as one; the width is not what decides it.
#guard emits "foo:\n  \tbar\n"
  ["+STR", "+DOC", "+MAP", "=VAL :foo", "=VAL :bar", "-MAP", "-DOC", "-STR"]
-- A FLOW node in the same slot, for the same reason.
#guard emits "a:\n  \t[1, 2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "-MAP", "-DOC", "-STR"]
#guard emits "a:\n  \t{b: c}\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP {}", "=VAL :b", "=VAL :c", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- UV7Q's "legal tab after indentation": a plain-scalar CONTINUATION line.
#guard emits "x:\n - x\n  \tx\n"
  ["+STR", "+DOC", "+MAP", "=VAL :x", "+SEQ", "=VAL :x x", "-SEQ", "-MAP",
   "-DOC", "-STR"]

/-! ## §2  The run between a key and its `:` is separation, not indentation

`[154] ns-s-implicit-yaml-key(c)` is `ns-flow-yaml-node(0,c) s-separate-in-line?`,
so the check may not be anchored at the indicator. -/

#guard emits "a\t: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "\"a\"\t: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "- a\t: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-SEQ",
   "-DOC", "-STR"]
-- Flow context has no `s-indent` at all, so nothing here changes.
#guard emits "{a\t: b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
-- The tab as value separation, and inside a value, both still stand.
#guard emits "a:\tb\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "a: b\tc\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b\\tc", "-MAP", "-DOC", "-STR"]
-- Tab before a comment, and a tab-only line, are `[79] s-l-comments`.
#guard emits "a: b\n  \t#c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "a: b\n\t\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d", "-MAP",
   "-DOC", "-STR"]
-- Block-scalar content is content, not indentation.
#guard emits "a: |\n  x\n  \ty\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |x\\n\\ty\\n", "-MAP", "-DOC", "-STR"]

/-! ## §3  The shapes that parsed and no longer do

Each is a block-mapping entry whose `s-indent(n+m)` would have to contain a
tab.  Every one was accepted identically by both pipelines before the item —
which is why the deferral's "expected vacuous" survived: the arm anybody
sampled was the `-`, and it was the one already guarded. -/

-- Empty key (`[192]`'s `e-node`), the shape the `:` arm owns.
#guard refuses "a:\n  \t: b\n"
#guard refuses "a:\n  \t:\n"
#guard refuses "a:\n \t: b\n"
-- Explicit key `[191]`.
#guard refuses "a:\n  \t? b\n"
#guard refuses "a:\n \t? b\n"
-- Implicit key: the indentation in front of the KEY is what is wrong, and the
-- `:` is where the entry is recognised.
#guard refuses "a:\n  \tk: b\n"
#guard refuses "a:\n  \t\"k\": b\n"
#guard refuses "a:\n \tk: 1\n"
-- Nested one level deeper — the same entry, at a different index.
#guard refuses "a:\n  b:\n    \t: c\n"
#guard refuses "a:\n  b:\n    \tc: 1\n"
-- A compact entry after `-`: `[185] s-l+block-indented`'s `s-indent(m)` is
-- spaces only too, so the mid-line run is indentation as much as a line's is.
#guard refuses "-\t? a\n"
#guard refuses "- \t? a\n"
#guard refuses "-\ta: b\n"

/-! ## §4  What was already refused, and still is

The `-` arm's own check, and the `col ≤ currentIndent` route in
`skipToContentWs` that catches a tab with no space in front of it. -/

#guard refuses "\ta: 1\n"
#guard refuses " \ta: 1\n"
#guard refuses "a:\n\tb: 1\n"
#guard refuses "a:\n\t b: 1\n"
#guard refuses "a:\n  \t- b\n"
#guard refuses "a:\n \t- x\n"
#guard refuses "-\t- a\n"
-- 4EJS, the suite's own "invalid tabs as indentation in a mapping".
#guard refuses "---\na:\n\tb:\n\t\tc: value\n"

/-! ## §5  The line reading, and what it does not touch (DOCS item 32)

Item 31's check reads the run in front of the ENTRY, which is the simple-key
machine's `simpleKey.pos` when a key was recorded there — the right verdict in
a coordinate the grammar accumulation has no coupling for.  Item 32 added the
same verdict computed from `s.col`: walk back exactly the line's own
characters, and refuse when every one of them is an `s-white` and one is a tab.
That is `[63] s-indent(n)`'s own coordinate, and it decides the keyless `:`
without consulting the key machine at all.

The two readings agree — the whole `yaml-test-suite` is byte-identical per test
and a 3,267-case tab-shape differential moves nothing in either pipeline — so
these pins are not new rejections.  They are the shapes that say WHICH reading
decides, which is what item 32 changed. -/

-- The line reading decides these: nothing on the line but whites, so there is
-- no key and the run is the entry's `[63] s-indent(n)`.
#guard refuses "a:\n \t : b\n"            -- the tab need not touch the `:`
#guard refuses "a:\n  \t\t: b\n"
#guard refuses "b:\n  a:\n    \t: c\n"    -- at a deeper entry
-- The KEY reading still decides these: something on the line precedes the `:`,
-- so the indentation is the run in front of THAT, not in front of the colon.
#guard refuses "a:\n  \tb\t: c\n"         -- `b\t:` is legal [154]; `␣␣→b` is not
#guard refuses "a:\n  \t'k': v\n"         -- the third quote form
-- And neither reading touches these: a tab after `- ` is separation before a
-- plain scalar, flow context has no `s-indent` at all, and a tab-only line is
-- `[79] s-l-comments` however far it is indented.
#guard emits "- a\n- \tb\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "{a:\n  \tb}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "[\n  \t1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard emits "a: b\n  \t\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d", "-MAP",
   "-DOC", "-STR"]

end Tests.Guards.ScannerTabBeforeBlockEntry

end Blanket
