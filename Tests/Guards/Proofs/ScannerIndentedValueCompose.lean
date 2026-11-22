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

/-! # The indented entry's VALUE composes (DOCS item 23)

Item 22 gave `[183]`/`[187]` their auto-detected `m` back, so an indented block
collection derives at its own index — but only its FRAME.  Every content
reading in the accumulation was stated at 0 (`dispatchContent_evidence`
concludes `SFlowNode 0 .flowOut`), and `[196] s-l+block-node(n,c)`'s flow arm
wants the value at the ENTRY's index, so `  - a` still had no derivation.

Widening those readings is not monotonicity and is false in general: the index
occurs in `[71] s-flow-line-prefix(n)` and `[134] s-ns-plain-next-line(n,c)`,
both of which sit AFTER a line break, and a reading at 0 admits continuation
lines that a reading at `n` forbids.  It holds for one structural reason — **a
derivation that crosses no break contains no occurrence of the index at all** —
and the spec names the shapes that say so: `[111] nb-double-one-line`,
`[122] nb-single-one-line` and `[133] ns-plain-one-line(c)` take no indent, and
`[104] c-ns-alias-node` takes neither indent nor context.

The side condition is therefore `s'.line = sc.line`, the SAME decidable state
fact item 15's implicit key reads — one measurement, two consumers: §7.4 reads
it to decide whether a scan can be a key, and item 23 reads it to decide at
what indent a scan can be a value.

Nothing here is new BEHAVIOUR — item 23 edits no runtime file.  These are the
shapes whose accumulation changed, held fixed so a later runtime change cannot
move them silently.  §6 and §7 pin what is still accepted-only, and those
residues are now three DIFFERENT causes rather than the one item 22 recorded.
-/

namespace Tests.Guards.ScannerIndentedValueCompose

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

/-! ## §1  A plain scalar as an indented entry's value

`[133] ns-plain-one-line(c)` carries no indent, so `[135] ns-plain-multi-line`'s
continuation star — the only place `n` occurs in a plain scalar — is empty and
the reading transports to the entry's index.  The width is read off the
landing, so 2 and 4 are the same proof. -/

#guard emits "  - a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "    - a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
-- Interior whitespace is `[132] nb-ns-plain-in-line`, still one line.
#guard emits "  - hello world\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :hello world", "-SEQ", "-DOC", "-STR"]
-- Trailing separation rides the evidence's `GStar SSWhite`, not the value.
#guard emits "  - a  \n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]

/-! ## §2  Quoted values

`[110] nb-double-text(n,block-key)` IS `[111] nb-double-one-line`, and
`[116] nb-double-multi-line(n)`'s `single` arm admits that body at every `n` —
so the lift rebuilds the quotes and transports the body verbatim.  `'` is the
same rebuild over `[122]`. -/

#guard emits "  - \"x\"\n"
  ["+STR", "+DOC", "+SEQ", "=VAL \"x", "-SEQ", "-DOC", "-STR"]
#guard emits "  - 'x'\n"
  ["+STR", "+DOC", "+SEQ", "=VAL 'x", "-SEQ", "-DOC", "-STR"]
-- An escape stays inside the one-line body.
#guard emits "  - \"a\\tb\"\n"
  ["+STR", "+DOC", "+SEQ", "=VAL \"a\\tb", "-SEQ", "-DOC", "-STR"]
-- The empty quoted scalar is the empty `GStar`.
#guard emits "  - \"\"\n"
  ["+STR", "+DOC", "+SEQ", "=VAL \"", "-SEQ", "-DOC", "-STR"]

/-! ## §3  An alias as the value

`[104] c-ns-alias-node` takes neither an indent nor a context, so this is the
one content reading that is index-polymorphic with no side condition at all —
`dispatchContent_aliasNode_prod` hands over the node itself rather than
`[161]`'s wrapper at 0. -/

#guard emits "  - &a x\n  - *a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a :x", "=ALI *a", "-SEQ", "-DOC", "-STR"]

/-! ## §4  Siblings, and the entry-level snoc at a nonzero index

The value arm parks `pendingBlockContent` at the entry's index, so the sibling
`-` snocs onto `SBlockSeqEntries k` — the same closure item 19 built at 0. -/

#guard emits "  - a\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "  - a\n  - b\n  - c\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "=VAL :c", "-SEQ", "-DOC",
   "-STR"]
-- Mixed empty and valued entries at one width.
#guard emits "  -\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "  - a\n  -\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :", "-SEQ", "-DOC", "-STR"]
-- A blank line and a comment line between siblings.
#guard emits "  - a\n\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "  - a\n  # c\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]

/-! ## §5  The mapping twin, and the explicit document frame

`  : v` is `[189]`'s empty-key entry at a nonzero index and `  ? a` is `[186]`'s
key-only entry (item 20's `explicitEmpty`); both park `pendingMapValue` at the
entry index, so both take the same lift. -/

#guard emits "  : v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "  : \"x\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL \"x", "-MAP", "-DOC", "-STR"]
#guard emits "  ? a\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "---\n  - a\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]

/-! ## §6  What the one-line lift does NOT reach — accepted, derivation owed

`indentedValue_reads_at_any_indent` asks the whole question once, and what is
left of its negative answer is a value that FOLDS onto a second line —
precisely the case in which the index DOES occur, so there is nothing to lift.

Two of the answers recorded here turned out not to be about the reading at all.
Item 24 showed the property run never was: `&`/`!` complete no value, they open
a run that `pendingProps` PARKS, and re-indexing that pending's route composes
`  - &a v` with no lift whatever (`ScannerIndentedPropsCompose`).  Item 26
showed the block scalar never was either — `[170]`/`[174]` bind their
auto-detected content indent themselves, so there was no pinned existential of
`[183]`/`[187]`'s kind to widen; the reading was thrown away by the production
lemma rather than absent from the grammar
(`ScannerIndentedBlockScalarCompose`). -/

#guard emits "  - a\n    b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a b", "-SEQ", "-DOC", "-STR"]

/-! ## §7  Not a content lift at all

`  - [1]`'s pinned 0 is in `FlowOpenStack`'s resume type — the flow node is
supplied when the COLLECTION closes, not by the dispatch step — so it rides
`scannerDrop` rather than the block deferral, and neither a wider content
reading nor item 24's wider props route reaches it.

`  a: 1` was here too, as the indented IMPLICIT key whose pack demanded a
column-0 line start.  Item 25 showed that demand was not a fact about keys at
all — `[193]`/`[194]` take no indent — but the value the pack's producer got
by declining to read the whites in front of the key, which are the entry's own
`[63] s-indent(k)` (`ScannerIndentedImplicitKeyCompose`). -/

#guard emits "  - [1]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "  - a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]

/-! ## §8  A tab still refutes the indentation reading

The value lift changes nothing about `[63] s-indent(n)`: the scanner answers
first, and these verdicts are what a scanner-side refutation would have to
read. -/

#guard verdicts "\t- a\n" == (some (.tabInIndentation 0 0), some (.tabInIndentation 0 0))
#guard verdicts "  \t- a\n" == (some (.tabInIndentation 0 2), some (.tabInIndentation 0 2))

end Tests.Guards.ScannerIndentedValueCompose

end Blanket
