module

public import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
public meta import L4YAML.Token.Token
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The break-crossed block dispatch composes (DOCS item 19)

Items 13–17 composed the block arms whose PENDING was parked at column 0.  A
pending parked mid-line — after `a` in `- a`, after `]` in `- [1]`, after the
indicator in a bare `-` — reaches the very same column-0 line start by crossing
a break, and every one of those arms is anchored at the landing, not at the
park.  Item 19 gates them on the landing instead
(`preprocess_some_ssl_comments_landing`, the join of the column-0 and
crossed-break producers of one package), so the multi-line block sequence — the
commonest shape in the language — leaves the deferral: `- a⏎- b` snocs through
`h_entry_old` exactly as a column-0 park does, and a break-crossed `:` opens
`[189]`'s empty-key entry exactly as `colon_open_map` already did.

Nothing here is new BEHAVIOUR: item 19 edits no runtime file, and these pins
are the shapes whose accumulation changed, held fixed so a later runtime change
cannot move them silently.  What is still punted is the residue the join cannot
reach — whites before the indicator (the indent machinery) and a mid-line park
that crosses nothing.
-/

namespace Tests.Guards.ScannerBreakCrossedBlockCompose

open L4YAML

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-- Legacy and indexed end-to-end verdicts as a comparable pair: `none` on
    success (scan errors and parse errors share `ScanError`). -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match Events.streamToEvents input with | .ok _ => none | .error e => some e)
  , (match Events.streamToEventsIx input with | .ok _ => none | .error e => some e) )

/-! ## §1  Sibling sequence entries across a break

The park is mid-line in every one of these; the landing is column 0, and the
new entry snocs onto the accumulated `SBlockSeqEntries` there. -/

#guard emits "- a\n- b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "- a\n- b\n- c\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "=VAL :c", "-SEQ", "-DOC", "-STR"]
-- An EMPTY entry on either side: the park is the bare indicator itself
-- (`pendingBlock`), and the entry it opened closes as `[199]`'s `e-node`.
#guard emits "-\n- b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "- a\n-\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n-\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "=VAL :", "-SEQ", "-DOC", "-STR"]
-- Every park shape reaches the landing: a flow collection, a property run, a
-- nested sequence.
#guard emits "- [1]\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- {a: 1}\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP {}", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b",
   "-SEQ", "-DOC", "-STR"]
#guard emits "- &a v\n- b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :v", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "- - a\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "=VAL :b", "-SEQ",
   "-DOC", "-STR"]

/-! ### The landing absorbs comments and blank lines — that is what makes it
`[79] s-l-comments` and not merely a break -/

#guard emits "- a\n\n\n- b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "- a\n  # c\n- b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "# c\n- a\n- b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]

/-! ### Document frames around the same entries -/

#guard emits "---\n- a\n- b\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "- a\n...\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC ...", "-STR"]
#guard emits "- a\n---\n- b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "+DOC ---", "+SEQ",
   "=VAL :b", "-SEQ", "-DOC", "-STR"]

/-! ## §2  The empty-key mapping reached across a break

Item 13's `colon_open_map` was already anchored at the landing; only its gate
kept `: a⏎: b`'s second entry out. -/

#guard emits ": a\n: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :a", "=VAL :", "=VAL :b",
   "-MAP", "-DOC", "-STR"]

/-! ## §3  Break-crossed `:` after content — scanned, then refused by the parser

The accumulation's bare-document over-approximation admits the SCAN (this is
what item 19 turns from `scannerDrop` into `[189]`'s empty-key entry); the
parser rejects the document that results.  Both pipelines, same place. -/

#guard verdicts "x\n: v\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))
#guard verdicts "x\n:\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))
#guard verdicts "\"a\"\n: b\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))
#guard verdicts "&a x\n: v\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))
-- Two breaks land just as one does; only the reported line moves.
#guard verdicts "x\n\n: v\n" ==
  (some (.invalidBareDocument 2 0), some (.invalidBareDocument 2 0))

/-! ## §4  Still punted — the residue the join cannot reach

Whites before the indicator are the indent machinery's arm (`hws` is `cons`,
not `nil`), and a nested level is `n ≠ 0`.  Both accept through the deferral,
unchanged. -/

#guard emits "a:\n  - b\n  - c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :b", "=VAL :c", "-SEQ",
   "-MAP", "-DOC", "-STR"]
-- Not an indented entry at all: `  - b` is absorbed by the plain scalar, which
-- is why the punted set is smaller than the indentation looks.
#guard emits "- a\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a - b", "-SEQ", "-DOC", "-STR"]

/-! ## §5  The neighbours — must NOT move, identical in BOTH pipelines -/

-- A sequence and a mapping cannot share one bare document.
#guard verdicts "- a\n: v\n" == (some (.trailingContent 1 0), some (.trailingContent 1 0))
#guard verdicts "- a\nb: c\n" == (some (.trailingContent 1 0), some (.trailingContent 1 0))
#guard verdicts ": a\n- b\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))
#guard verdicts "a: b\n- c\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))
-- No break, mid-line park: §3 of Reflection 643's residue — `- b` here is
-- plain content, not an entry.
#guard emits "x\ny\n"
  ["+STR", "+DOC", "=VAL :x y", "-DOC", "-STR"]
#guard emits "x\n- a\n"
  ["+STR", "+DOC", "=VAL :x - a", "-DOC", "-STR"]

end Tests.Guards.ScannerBreakCrossedBlockCompose

end Blanket
