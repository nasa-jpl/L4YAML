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

/-! # The explicit `?` key composes (DOCS item 20)

Item 13 gave the col-0 `:` its arm — `[189]`'s EMPTY-key entry — and parked
`PendingNode.pendingMapValue`, whose closure names only the node it awaits and
never the indicator that opened it.  Item 20 spends that: `?` is `[188]`'s
OTHER alternative, so a second producer (`question_open_map`) reuses the same
pending, the same consumers and the same dispatch arm — `indicator_open_map`
takes `:` and `?` in ONE branch — and the entry it composes is
`[186] c-l-block-map-explicit-entry` with its `e-node` value.

That `e-node` value alternative had to be ADDED to the surface grammar
(`SBlockMapEntry.explicitEmpty`): `SBlockMapEntry.explicit` demanded the `:`
line, so every key-only entry below parsed correctly with no derivation at all.
The whole cost of the arm was that constructor.

Nothing here is new BEHAVIOUR: item 20 edits no runtime file, and these pins
are the shapes whose accumulation changed, held fixed so a later runtime change
cannot move them silently.  What is still punted is the indented `?` (`- ? a`,
whites before the indicator) — the indent machinery's arm, accepted through the
deferral, pinned in §3.
-/

namespace Tests.Guards.ScannerExplicitKeyCompose

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

/-! ## §1  The key-only entry — `[186]`'s `e-node` value

The shape with NO `:` line is the one that had no derivation.  Its value is
the zero-width `e-node`, so the entry ends exactly where its key does. -/

#guard emits "? a\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-DOC", "-STR"]
-- Both halves empty: the key is `s-l+block-indented`'s own `e-node` arm.
#guard emits "?\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :", "-MAP", "-DOC", "-STR"]
-- Every key shape rides the awaited-node closure, exactly as the `:` arm's
-- VALUE does: a flow collection, a property run, a quoted scalar.
#guard emits "? [1]\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :", "-MAP",
   "-DOC", "-STR"]
#guard emits "? {a: 1}\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :1", "-MAP", "=VAL :",
   "-MAP", "-DOC", "-STR"]
#guard emits "? &a v\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :v", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "? \"x\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"x", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "? |\n  t\n"
  ["+STR", "+DOC", "+MAP", "=VAL |t\\n", "=VAL :", "-MAP", "-DOC", "-STR"]

/-! ## §2  Siblings and frames

A following `?` closes this entry and opens the next as a bare-document
continuation — `[211]`'s over-approximation, the same route `: a⏎: b` takes. -/

#guard emits "? a\n? b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "=VAL :b", "=VAL :", "-MAP",
   "-DOC", "-STR"]
-- The two-line explicit entry: the `:` on its own line is the SAME col-0 `:`
-- arm item 13 built, reached across the break by item 19.
#guard emits "? a\n: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "? a\n: b\n? c\n: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d", "-MAP",
   "-DOC", "-STR"]
-- Mixed with implicit entries, either order.
#guard emits "? a\nb: c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "=VAL :b", "=VAL :c", "-MAP",
   "-DOC", "-STR"]
#guard emits "a: b\n? c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :", "-MAP",
   "-DOC", "-STR"]

/-! ### The landing absorbs comments and blank lines here too -/

#guard emits "? a\n\n? b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "=VAL :b", "=VAL :", "-MAP",
   "-DOC", "-STR"]
#guard emits "? a\n  # c\n? b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "=VAL :b", "=VAL :", "-MAP",
   "-DOC", "-STR"]
#guard emits "# c\n? a\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-DOC", "-STR"]

/-! ### Document frames -/

#guard emits "---\n? a\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "? a\n...\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-DOC ...", "-STR"]

/-! ## §3  Still punted — the indent machinery's `?`

A `?` inside an entry sits at column 2, so it is the indented arm, not this
one.  It accepts through the deferral, unchanged. -/

#guard emits "- ? a\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-SEQ",
   "-DOC", "-STR"]

/-! ## §4  The neighbours — must NOT move, identical in BOTH pipelines

`?x` is not an indicator at all (`isKeyCandidate` wants a blank after it), and
the two refusals below are the scanner's and the parser's, unchanged. -/

#guard emits "?x\n" ["+STR", "+DOC", "=VAL :?x", "-DOC", "-STR"]
-- §6.1: a tab right after the block `?` would be the key's indentation.
#guard verdicts "?\ta\n" ==
  (some (.tabInIndentation 0 1), some (.tabInIndentation 0 1))
-- A mapping and a sequence cannot share one bare document.
#guard verdicts "? a\n- b\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))

end Tests.Guards.ScannerExplicitKeyCompose

end Blanket
