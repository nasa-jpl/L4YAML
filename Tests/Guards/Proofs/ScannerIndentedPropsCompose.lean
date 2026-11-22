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

/-! # The indented entry's PROPERTY RUN composes (DOCS item 24)

Item 23 gave the indented entry's inline value a reading at the entry's own
index, and named four ways for that reading to be unavailable.  The first was
not about the reading at all: `&`/`!` do not complete a value, they open a
`[96] c-ns-properties` run that item 12 PARKS, and `PendingNode.pendingProps`
routed the eventually-decorated node through a closure typed at
`SBlockNode 0 .blockIn`.  So the obstruction was in the pending, one step
before the content — `  - &a v` deferred even though `  - v` composed.

Re-indexing the route is the whole of item 24, and it needs no lift: a FRESH
run is single-half (`PropsRun.anchor` / `.tag`), and `PropsRun`'s only
occurrence of the index is the `s-separate(n,c)` inside `[96]`'s optional
SECOND half.  A one-half run therefore reads at every index by construction —
Reflection 649's rule with the strongest possible answer, no occurrence at
all — and the two-half extension (`&a !t v`) builds its internal separator
from the preprocessing's residual whites, which are `[66] s-separate-in-line`
and read at every index too.  What the value then needs is `[156]
ns-flow-content` rather than `[161] ns-flow-node`, because `[161]`'s
`propsContent` arm slots the content UNDER the run; that is item 23's reading
one production lower down, and the alias is the whole difference (a run
followed by an alias is scanner-refuted anyway).

Nothing here is new BEHAVIOUR — item 24 edits no runtime file.  These are the
shapes whose accumulation changed, held fixed so a later runtime change cannot
move them silently.  §5 pins what is still accepted-only, and its two residues
have two different causes, neither of them the run.
-/

namespace Tests.Guards.ScannerIndentedPropsCompose

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

/-! ## §1  An anchored or tagged value at the entry's indent

The run parks at the entry index; the next step reads the value as
`[156] ns-flow-content` at that same index and `[161]`'s `propsContent` arm
joins them.  The width is read off the landing, so 2 and 4 are one proof. -/

#guard emits "  - &a v\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :v", "-SEQ", "-DOC", "-STR"]
#guard emits "    - &a v\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :v", "-SEQ", "-DOC", "-STR"]
#guard emits "  - !!str v\n"
  ["+STR", "+DOC", "+SEQ", "=VAL <tag:yaml.org,2002:str> :v", "-SEQ", "-DOC",
   "-STR"]

/-! ## §2  Both halves of `[96]`

The run EXTENDS on its own line (item 12's guard arithmetic, unchanged), and
the separator between the halves is the residual whites — `[66]`, which
mentions no indent, so the two-half run reads at the entry's index as well. -/

#guard emits "  - &a !t v\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a <!t> :v", "-SEQ", "-DOC", "-STR"]
#guard emits "  - !t &a v\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a <!t> :v", "-SEQ", "-DOC", "-STR"]

/-! ## §3  Quoted values under a run

`[111]`/`[122]`'s one-line bodies are what item 23 lifted; slotting them under
the run costs the `SFlowContent` reading and nothing else. -/

#guard emits "  - &a \"x\"\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a \"x", "-SEQ", "-DOC", "-STR"]
#guard emits "  - &a 'x'\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a 'x", "-SEQ", "-DOC", "-STR"]

/-! ## §4  The run with no value, siblings, and the mapping twin

`[161]`'s `( c-ns-properties e-scalar )` arm closes a run that never gets a
value (`PendingNode.propsClose`, now at every index).  A sibling `-` re-opens
rather than snocs — the props route carries the stream closure only — and the
mapping indicators reach the same run through `pendingMapValue`. -/

#guard emits "  - &a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :", "-SEQ", "-DOC", "-STR"]
#guard emits "  - &a # c\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :", "-SEQ", "-DOC", "-STR"]
#guard emits "  - &a\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "  - &a v\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :v", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "  - &a v\n  - &b w\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :v", "=VAL &b :w", "-SEQ", "-DOC", "-STR"]
#guard emits "  - &a v\n\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :v", "=VAL :b", "-SEQ", "-DOC", "-STR"]
-- The anchor is usable at the entry index: item 23's alias reading is the
-- consumer.
#guard emits "  - &a x\n  - *a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :x", "=ALI *a", "-SEQ", "-DOC", "-STR"]
#guard emits "  : &a v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL &a :v", "-MAP", "-DOC", "-STR"]
#guard emits "  ? &a v\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :v", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "  ? &a v\n  : &b w\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :v", "=VAL &b :w", "-MAP", "-DOC", "-STR"]
#guard emits "---\n  - &a v\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL &a :v", "-SEQ", "-DOC", "-STR"]

/-! ## §5  What the re-indexed route does NOT reach — accepted, derivation owed

The run is not the cause of any of these:

* `  - &a |` was filed here as `[170]`/`[174]`'s auto-detected content indent,
  the SAME gap `  - |` has with no run at all.  That attribution was right and
  item 26 has since taken it: `[198]`'s props slot now carries the block scalar
  at the run's own route index (`ScannerIndentedBlockScalarCompose`), and what
  is left of it is one inequality against the scanner's indent stack rather
  than a production.
* `  - &a [b]` is not a props question either: the flow collection re-enters
  through `FlowOpenStack`'s resume closure, whose argument is `SFlowContent 0
  .flowOut`, so it rides the opaque `scannerDrop` for exactly the reason
  `  - [1]` does.
* A value that FOLDS onto a second line is the case in which the index DOES
  occur, so there is nothing to lift. -/

#guard emits "  - &a [1]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ [] &a", "=VAL :1", "-SEQ", "-SEQ", "-DOC",
   "-STR"]
#guard emits "  - &a v\n    b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :v b", "-SEQ", "-DOC", "-STR"]

/-! ## §6  A tab still refutes the indentation reading

Unchanged by the route's index: the scanner answers first, and these verdicts
are what a scanner-side refutation would have to read. -/

#guard verdicts "\t- &a v\n" == (some (.tabInIndentation 0 0), some (.tabInIndentation 0 0))
#guard verdicts "  \t- &a v\n" == (some (.tabInIndentation 0 2), some (.tabInIndentation 0 2))

end Tests.Guards.ScannerIndentedPropsCompose

end Blanket
