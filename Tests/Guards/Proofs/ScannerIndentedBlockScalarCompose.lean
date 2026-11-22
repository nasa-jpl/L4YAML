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

/-! # The indented entry's BLOCK SCALAR composes (DOCS item 26)

Item 23 named a block scalar as one of the ways an indented entry's value fails
to read at the entry's index, and diagnosed it as `[183]`/`[187]`'s gap one
level down: an auto-detected indent that a reading at 0 pins.  That diagnosis
was wrong, and item 26 is the correction.

`[170] c-l+literal(n)` is `"|" c-b-block-header(m,t) l-literal-content(n+m,t)`
and `SCLLiteral`'s constructor binds `m` ITSELF — unlike `SBlockNode.blockSeq`,
which item 22 had to give an `m` it did not have.  So there was never a
production to widen.  What `scanBlockScalar_prod` did was measure the indent
(`contentIndent`, handed up as an existential by
`scanBlockScalarBody_literal_prod`) and then throw it away by instantiating the
conclusion at `n = 0` — Reflection 651's shape, one file over.  Keeping it is
`scanBlockScalar_prod_at`, and the reading then holds at every `n ≤ d` with
`m := d - n`, no sub-production touched.

The scanner also already proves the floor: `scanBlockScalarBody` computes
`minContentIndent = (max 0 (currentIndent + 1)).toNat` and takes `max` with the
detected column (auto) or `currentIndent + m, m ≥ 1` (explicit `|2`), so
`autoDetectBlockScalarIndent_ge_min` and `parseBlockHeaderLoop_offset_preserves`
— both already in the tree — compose into
`scanBlockScalarBody_contentIndent_floor` with no new induction.

What is left is one inequality, `n ≤ d`.  It is true of every input below
(an entry sits at `currentIndent`, the body's floor is `currentIndent + 1`), but
`currentIndent` appears nowhere in the accumulation invariant, so the guard is
asked and the negative branch still defers.  That inequality — not a grammar
widening — is what the next item on this family owes.

Nothing here is new BEHAVIOUR: item 26 edits no runtime file and no grammar
file.  These are the shapes whose accumulation changed, held fixed so a later
runtime change cannot move them silently.
-/

namespace Tests.Guards.ScannerIndentedBlockScalarCompose

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

/-! ## §1  A literal or folded value at the entry's own indent

The entry indent is `[183]`'s auto-detected `n + m` (item 22); the block
scalar's content indent is `[170]`'s own `n + m'`, detected independently and
one level deeper.  Both are existentials the producer measures — which is why
the two nest without either being pinned. -/

#guard emits "  - |\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "    - |\n      text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - >\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL >text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - |\n    a\n    b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |a\\nb\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - >\n    a\n    b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL >a b\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - |\n\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |\\ntext\\n", "-SEQ", "-DOC", "-STR"]

/-! ## §2  The header's own indicators change nothing about the index

`[162] c-b-block-header` carries neither the index nor a link to it — the chomp
indicator is not modelled at all and the indentation indicator is not correlated
with `m` — so the chomping and explicit-offset forms take the same reading.  The
explicit form is where `m ≥ 1` comes from on the runtime side
(`parseBlockHeaderLoop` refuses the digit `0`), and it is the other half of the
floor the auto-detect form gets from `max`. -/

#guard emits "  - |-\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |text", "-SEQ", "-DOC", "-STR"]
#guard emits "  - |+\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - |2\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - | # c\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]

/-! ## §3  The mapping twin

Item 13's `pendingMapValue` names only the node it awaits, so the value of a
keyless `:` entry, of an explicit `?` key and of item 25's indented implicit key
all reach the same arm. -/

#guard emits "  a: |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  : |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL |text\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  ? |\n    text\n"
  ["+STR", "+DOC", "+MAP", "=VAL |text\\n", "=VAL :", "-MAP", "-DOC", "-STR"]

/-! ## §4  Under a held property run

`[198] s-l+block-scalar(n,c)` has a props slot of its own, and item 24 gave
`pendingProps` the route index the run closes at, so the decorated block scalar
is the same node one production up.  Item 24 filed `  - &a |` as belonging to
`[170]`/`[174]`'s gap rather than to the run's route; that attribution was
right, and this is where it lands. -/

#guard emits "  - &a |\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a |text\\n", "-SEQ", "-DOC", "-STR"]
#guard emits "  - !!str |\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL <tag:yaml.org,2002:str> |text\\n", "-SEQ", "-DOC",
   "-STR"]
#guard emits "  - &a !!str |\n    text\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &a <tag:yaml.org,2002:str> |text\\n", "-SEQ", "-DOC",
   "-STR"]

/-! ## §5  Siblings and the document frame

The block scalar's node is complete where the scanner stops — `[173]`'s
`l-chomped-empty` has already taken the trailing breaks — so the entry closes at
the dispatch step and what parks is the plain content pending.  A following
sibling therefore re-opens through `[211]`'s bare-document continuation rather
than snocing, exactly as item 13 recorded for the mapping twin. -/

#guard emits "  - |\n    x\n  - y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |x\\n", "=VAL :y", "-SEQ", "-DOC", "-STR"]
#guard emits "  a: |\n    x\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :b", "=VAL :2", "-MAP",
   "-DOC", "-STR"]
#guard emits "---\n  - |\n    text\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL |text\\n", "-SEQ", "-DOC", "-STR"]

/-! ## §6  What is still owed here — accepted, derivation conditional

The reading above is available at every index up to the body's collection
indent; the guard `n ≤ d` is what says the entry's index is one of them.  Every
shape in §1–§5 satisfies it, but the accumulator cannot yet SAY so, because the
quantity that would prove it — `sc.currentIndent`, against which the scanner set
the floor in the first place — is not part of the accumulation invariant.  So
the negative branch of that one `by_cases` still defers, and it is the only
block-scalar residue left: a single inequality, not a construct.

The other two negatives of `indentedValue_reads_at_any_indent` are unchanged and
are one question, not two — a reading that crosses a break genuinely mentions
the index. -/

#guard emits "  - a\n    b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a b", "-SEQ", "-DOC", "-STR"]

/-! ## §7  A tab still refutes the indentation reading

The block-scalar lift changes nothing about `[63] s-indent(n)`: the scanner
answers first, and these verdicts are what a scanner-side refutation would have
to read. -/

#guard verdicts "\t- a\n" == (some (.tabInIndentation 0 0), some (.tabInIndentation 0 0))
#guard verdicts "  \t- a\n" == (some (.tabInIndentation 0 2), some (.tabInIndentation 0 2))

end Tests.Guards.ScannerIndentedBlockScalarCompose

end Blanket
