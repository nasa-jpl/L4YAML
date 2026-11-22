module

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

/-! # The nested block sequence composes at the entry's own index (DOCS item 30)

Item 22 gave `SBlockNode.blockSeq` `[183] l+block-sequence(n)`'s auto-detected
`m`, and item 23 onwards spent it on the INDENTED collection — a root sequence
whose entries sit at `n + m` with nothing above them.  This file is the other
consumer: a collection nested UNDER an entry that is still awaiting its node.

`accum_block_on_pendingBlock` and `accum_block_on_pendingBlockContent` both
gated their `-` arm on `k = n` — the landing's width against the pending's
entry index — and sent every disagreement to `block_dispatch_deferred` as one
case.  It was two, and they are different constructs:

* `n < k` is a NESTED collection (`-⏎  - a`).  The pending's entry has no node
  yet, so the deeper `-` is not a sibling of anything — it opens `[199]
  s-l+block-collection` filling that node, with `[183]`'s `m = k - n`
  (`nestedBlockSeq`).  The new pending is `pendingBlock` at the INNER index and
  is snoc-capable in its own right, so the nesting composes to any depth with
  the inner collection's entries-level fidelity intact.
* `k < n` is a DEDENT (`-⏎  -⏎- b`): the inner collection ENDS and the one it
  lands back in resumes.  `m` would have to be negative, so no reading of the
  awaited node reaches this `-`, and resuming the outer collection needs a
  frame the pending does not carry.  It takes the route the `:` and `?` arms of
  these same two lemmas have used at EVERY width since item 13 — close the
  pending, open at `k` as `[211]`'s document continuation.

`pendingBlockContent` has only the second case, at both signs: its entry
already HAS its node (that is the difference between the two pendings), so
`[183]`'s entries at `n` are complete at the landing and no `-` at any other
width extends them.

Nothing here is new BEHAVIOUR: item 30 edits no runtime file and no grammar
file.  These are the shapes whose ACCUMULATION changed, held fixed so a later
runtime change cannot move them silently.
-/

namespace Tests.Guards.ScannerNestedBlockCompose

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

/-! ## §1  The nested open

The outer `-` parks a `pendingBlock` awaiting `s-l+block-node(n, block-in)`;
the break lands at column 0; `[63] s-indent(k)` measures the next line's
width.  At `k > n` that node is `[199]`'s collection and the entry index the
inner pending carries is `k`. -/

#guard emits "-\n  - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
-- The outer entry may itself be indented — `m` is a difference, not a column.
#guard emits "  -\n    - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "      -\n        - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
-- A trailing `s-separate-in-line` before the break changes nothing: the gap is
-- `[79] s-l-comments` either way, and it is spent on the inner collection's
-- leading comments rather than on a previous entry's tail.
#guard emits "- \n  - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n\n  - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  # c\n  - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "---\n-\n  - a\n"
  ["+STR", "+DOC ---", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]

/-! ## §2  To any depth, and the inner collection is a real collection

The nested pending is `pendingBlock` at `k`, not a special state, so the same
arm fires again one level down and the k = n snoc (item 22) fires for the inner
siblings.  `m` is re-detected per level, so the widths need not be uniform. -/

#guard emits "-\n  -\n    - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-SEQ",
   "-DOC", "-STR"]
#guard emits "-\n  -\n    -\n      - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ",
   "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  - a\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-SEQ", "-DOC",
   "-STR"]
#guard emits "-\n  - a\n  - b\n  - c\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "=VAL :b", "=VAL :c", "-SEQ",
   "-SEQ", "-DOC", "-STR"]
-- The inner entry's own value is whatever `s-l+block-indented(k, block-in)`
-- admits, at the inner index — items 23–29's readings, one level down.
#guard emits "-\n  - &x a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL &x :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  - \"a\"\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL \"a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  - |\n    t\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL |t\\n", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  - [1]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ", "-SEQ", "-SEQ",
   "-DOC", "-STR"]
-- A nested MAPPING under the entry is the mapping indicators' own arm, which
-- has taken every width since item 13 — it is here as the sibling of what §1
-- composes, not as something item 30 changed.
#guard emits "-\n  - a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ",
   "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  ? a\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-SEQ", "-DOC",
   "-STR"]

/-! ## §3  The dedent — accepted, and derived the way the sibling indicators are

`k < n` closes the pending and re-opens at `k` through `[211]`'s implicit
document continuation, exactly as a `:` or `?` at a mismatched width has since
item 13.  The entries-level structure of the collection being RESUMED is not
recovered — that is what a frame stack on the pending would buy — but language
membership is, which is what row 12 asks for. -/

#guard emits "-\n  - a\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "=VAL :b", "-SEQ", "-DOC",
   "-STR"]
#guard emits "-\n  -\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :", "-SEQ", "=VAL :b", "-SEQ", "-DOC",
   "-STR"]
#guard emits "-\n  - a\n  - b\n- c\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "=VAL :c",
   "-SEQ", "-DOC", "-STR"]
-- Two levels up in one step.
#guard emits "-\n  -\n    - a\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "=VAL :b", "-SEQ",
   "-SEQ", "-DOC", "-STR"]

/-! ## §4  What is NOT this family

Two shapes the plan named for it, and neither reaches it — the family is
selected by the LANDING, so an indicator that crosses no break is never
measured against the pending's index at all:

* `- - a` is the compact form.  Its second `-` is a mid-line park crossing no
  break, so it is the INLINE RESIDUE, and what it wants is
  `SBlockIndented.compactSeq` — a different production from `nestedBlockSeq`'s
  `[199]`, and a different escape family.
* `a:⏎  - x` parks a `pendingMapValue`, which routes to
  `accum_block_on_closeThenBlock` and has no width comparison to make.

Both are ACCEPTED today; they are pinned here so the boundary of item 30's
claim stays visible. -/

#guard emits "- - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "  - - a\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "- - a\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a", "-SEQ", "=VAL :b", "-SEQ", "-DOC",
   "-STR"]
#guard emits "a:\n  - x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :x", "-SEQ", "-MAP", "-DOC",
   "-STR"]

/-! ## §5  A completed entry does not admit a deeper `-` as its own

`pendingBlockContent` is the entry whose node is already there, and the
deeper-`-` shapes that would test it mostly never reach block dispatch: a PLAIN
scalar absorbs the next line through `[135] s-ns-plain-next-line`, whose
`ns-plain-char` admits a leading `-` where `[126] ns-plain-first` would not, and
a block scalar absorbs it into its body.  What does reach it is refused
downstream, by the parser's §9.2 check rather than by the scanner — so the
accumulation must still derive a stream for it, and does, through the same
continuation §3 uses. -/

#guard emits "- a\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a - b", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  - a\n    - b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "=VAL :a - b", "-SEQ", "-SEQ", "-DOC", "-STR"]
#guard emits "- |\n  x\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |x\\n- b\\n", "-SEQ", "-DOC", "-STR"]
-- A QUOTED entry cannot absorb it, so the `-` reaches block dispatch and the
-- parser answers.  Both pipelines agree on the verdict.
#guard verdicts "- \"a\"\n  - b\n" == (some (.invalidBareDocument 1 2),
                                       some (.invalidBareDocument 1 2))
#guard verdicts "- [1]\n  - b\n" == (some (.invalidBareDocument 1 2),
                                     some (.invalidBareDocument 1 2))

end Tests.Guards.ScannerNestedBlockCompose

end Blanket
