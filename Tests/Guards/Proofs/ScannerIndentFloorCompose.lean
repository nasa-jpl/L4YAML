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

/-! # The entry index survives into the block scalar's floor (DOCS items 27–29)

Item 26 gave `[170] c-l+literal(n)` / `[174] c-l+folded(n)` a reading at every
index the body's collected content indent admits, and left ONE inequality owed:
`n ≤ d`, where `n` is the entry the accumulator parked at and `d` is the indent
the scanner collected the body at.  It is true of every accepted input — an
entry sits at `currentIndent`, and `scanBlockScalarBody`'s floor for `d` is
`(max 0 (currentIndent + 1)).toNat` — and it was unstatable, because
`currentIndent` occurred in the accumulation invariant zero times.

Item 27 carries it: `IndentFloor sc n` rides `pendingBlock` / `pendingMapValue`
/ `pendingProps`, discharged at the producer from the push the scanner just
made, and transported across the next preprocessing step by the fact that
`skipToContent` never writes `indents` — only the ARMED `unwindIndents` does,
and its arming flag is exactly what the break-free branch already excludes.

The field is `IndentFloor sc n ∨ True`, so a producer that cannot measure hands
`True` and no consumer gains a route (Reflection 653).  Item 27 discharged it
for the two indicators that push at their OWN column (`-`, `?`) and for the `:`
whose saved key is the fresh one at the indicator itself.

Item 28 discharges the third: `scanValuePrepare` pushes at the column of the
key it RESOLVES, so measuring the push there rather than at the indicator
reaches item 15's implicit-key entry too (`  a: |`).  The coupling is one
conjunct on `ImplicitKeyPack` — the pack's `[63] s-indent(k)` read on the
scanner's side as the saved key's column — and it is optional for the same
reason the floor is, so the producers that cannot supply it hand `True`
(Reflection 654).

Item 29 supplies it at the two that did.  A property-headed key (`  &x a: |`)
is measured to the PROPERTY, which is where the scanner saved the key too, so
`PropsKeyPack` carries the column beside the line it already carried; an alias
key (`  *m : |`) needed one lemma saying `[104]`'s scan leaves the saved key's
position alone.  Both were the SAME one-conjunct move, which is what makes the
pack's coupling total: all five of its producer families discharge it, across
the seven construction sites the two routes spend between them.

Nothing here is new BEHAVIOUR: items 27, 28 and 29 edit no runtime file and no
grammar file.  These are the shapes whose ACCUMULATION changed, held fixed so a
later runtime change cannot move them silently.
-/

namespace Tests.Guards.ScannerIndentFloorCompose

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

/-! ## §1  The `-` entry, at every depth

`scanBlockEntry` pushes `[183]`'s indent at the indicator's own column, and the
entry index the accumulator reads off the landing IS that column
(`SIndent_col`).  So the floor is discharged from the push, at any width. -/

#guard emits "  - |\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "      - |\n        text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - >\n    a\n    b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL >a b\\n", "-SEQ", "-DOC", "-STR"]
-- Extra `s-separate-in-line` between the indicator and the header changes the
-- header's column but not the ENTRY's, which is what the floor is measured at.
#guard emits "  -   |\n      text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]
-- `[162] c-b-block-header`'s explicit indentation indicator: the floor still
-- holds, because `parseBlockHeaderLoop` refuses the digit `0`.
#guard emits "  - |2\n     text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL | text\\n", "-SEQ", "-DOC", "-STR"]

/-! ## §2  Siblings, and the re-park

Each sibling `-` opens a fresh pending, so each measures its own floor; the
sequence's entries are snoc'd through a closure that never mentions it. -/

#guard emits "  - |\n    a\n  - |\n    b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |a\\n", "=VAL |b\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - |\n    a\n\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |a\\n", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "  -\n  - |\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "---\n  - |\n    text\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]

/-! ## §3  The two mapping indicators the runtime measures at the indicator

`?` pushes `[187]`'s indent at its own column exactly as `-` does.  So does the
`:` that opens `[189]`'s EMPTY-key entry, because the key it resolves is the
fresh save taken at the indicator itself. -/

#guard emits "  ? |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL |text\\n", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "    ? |\n      text\n"
  ["+STR", "+DOC", "+MAP", "=VAL |text\\n", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "  : |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]

/-! ## §4  The held property run inherits the entry's floor

A `[96] c-ns-properties` scan writes tokens, not indents
(`dispatchContent_props_indents`), so the run parked at an entry's route index
carries the entry's measurement verbatim — `  - &a |` discharges exactly where
`  - |` does, at both the fresh and the extended run. -/

#guard emits "  - &a |\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a |text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - !!str |\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL <tag:yaml.org,2002:str> |text\\n", "-SEQ", "-DOC",
   "-STR"]
#guard emits "  - &a !!str |\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a <tag:yaml.org,2002:str> |text\\n", "-SEQ",
   "-DOC", "-STR"]

/-! ## §5  The implicit key's own floor (item 28)

`scanValuePrepare` pushes `[187]`'s indent at `s.simpleKey.pos.col` — the
column of the key the `:` RESOLVES, not the `:`'s own — and declines to push
exactly when that column is already at or below the stack top.  So an entry
index bounded by the KEY is bounded by the resulting stack top either way, and
item 15's `  a: |` measures its floor where `  : |` measures it.

The index is `[63] s-indent(k)` between a column-0 landing and the key, which
is the same measurement item 25 gave the pack — read here on the scanner's
side, which is the whole content of the coupling. -/

#guard emits "  a: |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "      abc: |\n        text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :abc", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  a: >\n    x\n    y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL >x y\\n", "-MAP", "-DOC", "-STR"]
-- Whites after the `:` move the header's column, not the KEY's.
#guard emits "  a:   |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
-- `[162]`'s explicit offset and both chomping indicators ride it unchanged.
#guard emits "  a: |2\n     text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL | text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  a: |-\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |text", "-MAP", "-DOC", "-STR"]
-- `[194]`'s JSON key: the quoted heads take the same coupling, because the
-- quoted scans leave the saved key's POSITION alone.
#guard emits "  \"a\": |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  'a': |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL 'a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  \"a b\": >\n    x\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a b", "=VAL >x\\n", "-MAP", "-DOC", "-STR"]
-- Siblings each resolve their own key, so each measures its own floor.
#guard emits "  a: |\n    p\n  b: |\n    q\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |p\\n", "=VAL :b", "=VAL |q\\n", "-MAP",
   "-DOC", "-STR"]
#guard emits "---\n  a: |\n    text\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
-- The VALUE's own properties sit inside `[198]`'s props slot and change no
-- coordinate the floor is measured at.
#guard emits "  a: &x |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL &x |text\\n", "-MAP", "-DOC", "-STR"]

/-! ## §6  The two heads item 28 left (item 29)

A PROPERTY-headed key is `[161]`'s `propsContent` arm read at `block-key`, and
its `[63] s-indent(k)` is measured to the PROPERTY — which is exactly where the
scanner saved the key, because a `[96]` scan is not a key save and turns fresh
saves off.  So the run's column is the column the `:` will push at, and
`PropsKeyPack` carries it beside the line datum it already carried.  The
extension arms transport it: `&x !!str a: |` keeps the key at the `&`.  (Item 41
moved the measurement itself into the pack's ROUTE, where the producer that took
it spends it; the column conjunct is unchanged and still optional, because a
COMPACT route cannot measure its own column — `- &p a: |` reads its body at 0
where `-⏎  &p a: |` reads at the entry's index.)

An ALIAS key needs no new coupling at all, only the observation that `[104]`'s
scan leaves the saved key's position alone (`dispatchContent_alias_simpleKey`)
— the one datum item 28's alias arm had no way to state. -/

#guard emits "  &x a: |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x :a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  !!str a: |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL <tag:yaml.org,2002:str> :a", "=VAL |text\\n", "-MAP",
   "-DOC", "-STR"]
-- The EXTENDED run: the second property does not move the key.
#guard emits "  &x !!str a: |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x <tag:yaml.org,2002:str> :a", "=VAL |text\\n",
   "-MAP", "-DOC", "-STR"]
#guard emits "      &x abc: |\n        text\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x :abc", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
-- `[194]`'s JSON key under a run, and the folded and offset headers.
#guard emits "  &x \"a\": |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x \"a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  &x 'a': |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x 'a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  &x a: >\n    x\n    y\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x :a", "=VAL >x y\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  &x a: |2\n     text\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x :a", "=VAL | text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  &x a: |-\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x :a", "=VAL |text", "-MAP", "-DOC", "-STR"]
-- The VALUE may carry its own run without moving the key's column.
#guard emits "  &x a: &v |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x :a", "=VAL &v |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "---\n  &x a: |\n    text\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL &x :a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  &x a: |\n    p\n  &y b: |\n    q\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x :a", "=VAL |p\\n", "=VAL &y :b", "=VAL |q\\n",
   "-MAP", "-DOC", "-STR"]
-- The alias key, which needs a DEFINED anchor and a space before the `:`
-- (`ns-anchor-char` admits `:`, so `*m:` is one alias name).
#guard emits "  a: &m v\n  *m : |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL &m :v", "=ALI *m", "=VAL |text\\n", "-MAP",
   "-DOC", "-STR"]
#guard emits "  a: &m v\n  *m : >\n    x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL &m :v", "=ALI *m", "=VAL >x\\n", "-MAP",
   "-DOC", "-STR"]
#guard emits "      a: &m v\n      *m : |\n        text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL &m :v", "=ALI *m", "=VAL |text\\n", "-MAP",
   "-DOC", "-STR"]

/-! ## §7  What the floor does NOT reach — accepted, derivation owed

Three different causes, none of them the block scalar:

* `  ? a⏎  : |` is the explicit-key `:`.  `scanValueClearKey` drops the saved
  key when a `?` is open, and what survives is `[197]
  l-block-map-explicit-value(n)`, measured at the `:` again — a different arm,
  not a harder instance.
* `  - - |` is a COMPACT nested collection, which is family C of the escape's
  inventory and reaches the pending through a route no item here touched.
* A step that crosses a BREAK before the header is the landing branch, where
  `unwindIndents` is exactly what may fire — so the transport is unavailable by
  construction, not by omission. -/

#guard emits "  ? a\n  : |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  - - |\n      text\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL |text\\n", "-SEQ", "-SEQ", "-DOC", "-STR"]

/-! ## §8  A tab still refutes the indentation reading

Unchanged by the floor: the scanner answers first, and `[63] s-indent` is
spaces only. -/

#guard verdicts "\t- |\n" == (some (.tabInIndentation 0 0), some (.tabInIndentation 0 0))
#guard verdicts "  \t- |\n" == (some (.tabInIndentation 0 2), some (.tabInIndentation 0 2))

end Tests.Guards.ScannerIndentFloorCompose

end Blanket
