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

/-! # The INDENTED block collection composes (DOCS item 22)

Items 13–20 composed the block collections that open at column 0, and item 21
found why none of the others could: `[183] l+block-sequence(n)` and
`[187] l+block-mapping(n)` are `( s-indent(n+m) … )+` for an auto-detected
`m > 0`, and the surface grammar had inlined that `m` at its smallest legal
value — so `  -`, `  ?`, `  :` and every indented collection parsed correctly
with NO derivation at all.  Item 22 binds `m` where the production binds it, on
the constructor that OPENS the collection (`SBlockNode.blockSeq` / `.blockMap`),
and threads it through the pendings, whose awaited node was pinned at
`SBlockNode 0 .blockIn`.

The dispatch arm that reads it is not new: the whites between where
preprocessing LANDS (item 19) and the indicator ARE `[63] s-indent(k)`, so the
`nil` case is not a separate branch — it is `k = 0`, and one body serves the
column-0 collection and the indented one alike.

What is composed here is the indented FRAME: the entry opener, its siblings and
its empty close.  An indented entry with CONTENT still defers, on one named
residue — every content reading in the accumulation is stated at indent 0
(`dispatchContent_evidence` concludes `SFlowNode 0 .flowOut`, `SCLLiteral 0`,
`SCLFolded 0`), and lifting those to the entry's own indent is the next item.
The last three sections pin those shapes too: they are ACCEPTED, identically in
both pipelines, and it is only their derivation that is owed.

Nothing here is new BEHAVIOUR — item 22 edits no runtime file.  These are the
shapes whose accumulation changed, held fixed so a later runtime change cannot
move them silently.
-/

namespace Tests.Guards.ScannerIndentedBlockCompose

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

/-! ## §1  An indented sequence entry

`[183]`'s `m` is 2 here, and 4 in the second pin — the width is read off the
landing, not fixed by the constructor.  The entry itself closes as `[199]`'s
`e-node` (`SBlockNode.emptyNode`, which is indent-INERT and therefore served
the new index with no edit at all). -/

#guard emits "  -\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "-SEQ", "-DOC", "-STR"]
#guard emits "    -\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "-SEQ", "-DOC", "-STR"]
-- Trailing separation after the indicator does not change the entry.
#guard emits "  - \n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "-SEQ", "-DOC", "-STR"]
#guard emits "  -  \n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "-SEQ", "-DOC", "-STR"]

/-! ## §2  Siblings at the SAME indentation

The snoc route is item 19's, at the collection's own index: a following `-`
joins the sequence exactly when the landing leaves the indentation the
collection was opened at.  A different width is a nested or dedented
collection, and still defers (§6). -/

#guard emits "  -\n  -\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "=VAL :", "-SEQ", "-DOC", "-STR"]
#guard emits "  -\n  -\n  -\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "=VAL :", "=VAL :", "-SEQ", "-DOC", "-STR"]
#guard emits "  -\n  - \n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "=VAL :", "-SEQ", "-DOC", "-STR"]
-- Blank lines and comment lines between entries are the collection's own
-- `[79] s-l-comments`, exactly as at column 0.
#guard emits "  -\n\n  -\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "=VAL :", "-SEQ", "-DOC", "-STR"]
#guard emits "  # c\n  -\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "-SEQ", "-DOC", "-STR"]

/-! ## §3  The indented MAPPING indicators

`[189]`'s empty-key entry (item 13) and `[186]`'s explicit key (item 20) reach
the same generalization through the same pending: `pendingMapValue` now carries
the entry index, and its producer's conversion into the `.blockOut` value slot
is no longer restricted to `n = 0` either — `seq-spaces`' one-step disagreement
between the two block contexts is absorbed by `[183]`'s `m`. -/

#guard emits "  :\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "  ?\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "  :\n  :\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :", "=VAL :", "=VAL :", "-MAP",
   "-DOC", "-STR"]
#guard emits "  ?\n  ?\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :", "=VAL :", "=VAL :", "-MAP",
   "-DOC", "-STR"]

/-! ## §4  Inside an explicit document frame

The collection opens after the `---` marker's own line, so the landing and the
indentation reading are the same as at stream level. -/

#guard emits "---\n  - \n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :", "-SEQ", "-DOC", "-STR"]

/-! ## §5  Indented entries WITH content

The residue item 22 named: the entry frame is built at index `k`, but the value
must be READ at `k` too, and every content reading in `StreamAccum` was stated
at 0.  Item 23 closed the first of these — a break-free reading mentions no
indent, so a one-line scalar value re-reads at the entry's index
(`ScannerIndentedValueCompose`).  The other two are still accepted-only, for
reasons that are no longer the same one: `  a: 1` needs the IMPLICIT-KEY pack
off column 0, and `  - [1]`'s pinned 0 lives in `FlowStackB`'s resume type
rather than in a content reading. -/

#guard emits "  - a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "  - [1]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ", "-SEQ", "-DOC", "-STR"]

/-! ## §6  Indentation the arm does NOT read as this collection's

A `-` at a different width from the pending's is a nested or dedented
collection; here the scanner folds the second line into the first entry's plain
scalar instead, which is the reading both pipelines already had. -/

#guard emits "- a\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a - b", "-SEQ", "-DOC", "-STR"]

/-! ## §7  A tab is not `s-indent`

`[63] s-indent(n)` is spaces only, so the whites-to-indentation reading is a
disjunction and its other side — a tab — is what the four block-dispatch arms
now defer on.  For a BLOCK indicator the scanner refuses first, so the branch
is expected vacuous; refuting it from the scanner is future work, and these
pins record the verdict it would have to read. -/

#guard verdicts "\t-\n" == (some (.tabInIndentation 0 0), some (.tabInIndentation 0 0))
#guard verdicts "  \t-\n" == (some (.tabInIndentation 0 2), some (.tabInIndentation 0 2))
#guard verdicts "  \t:\n" == (some (.tabInIndentation 0 2), some (.tabInIndentation 0 2))

end Tests.Guards.ScannerIndentedBlockCompose

end Blanket
