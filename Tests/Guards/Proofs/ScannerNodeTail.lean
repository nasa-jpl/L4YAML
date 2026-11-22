module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # §7.5's node tail: `s-l-comments` plus `[154]`'s `:` (DOCS item 37)

Item 36 took the block dispatch's inline residue at the one pending whose tail
admits nothing — `pendingDocEnd`, by `[204] l-document-suffix`.  Item 37 takes
the next rung down, where the parked construct IS a node: a quoted scalar, an
alias, a flow collection returned to block context, a plain or a block scalar.

`validateTrailingContent` and `validateFlowClose` are the same five lines of
code and admit exactly `[79] s-l-comments` — a break, a `#`, end of input —
PLUS a `:`, because a complete node in block context may be re-read as
`[154] ns-s-implicit-yaml-key` / `[155] c-s-implicit-json-key`.  That is a
DICHOTOMY, not a filter: of the three block indicators the residue stands for,
`-` and `?` are refused outright and `:` is the grammatical continuation.

The proof could not say so for the same reason item 36 could not: item 10 had
derived this allowlist and then stored only `¬(c = '[' ∨ c = '{')`.  The stop
set now rides the predicate (`LineStop NodeTail`), the two scalar WALKS supply
their own (`OffLine` — outside `[1] c-printable`, or the BOM), and the pendings
carry the union.  So `accum_block_on_pendingContent` and
`accum_block_on_pendingBlockContent` refuse the `-`/`?` residue and the escape
they still take names the `:` alone.

§1 pins the admitted tails.  §2 pins the refused residue, park by park and
indicator by indicator.  §3 pins why the plain and block scalars never even
reach it — they ABSORB, which is a different reason for the same emptiness.
§4 pins the `:` that must survive: refuting it would be a bug, and it is the
whole of what row 12 still owes at these two pendings.  §5 pins the boundary —
a property run is not a node, so the same shape is scanner-accepted there.
-/

namespace Tests.Guards.ScannerNodeTail

open L4YAML

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

/-- Both pipelines reject `input` with the SAME error. -/
private def rejectsAlike (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error e₁, .error e₂ => toString (repr e₁) == toString (repr e₂)
  | _, _ => false

/-- Both pipelines reject `input` (the twins may disagree on WHICH check fires
    first; that is a separate question from the verdict). -/
private def rejects (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-- The SCANNER's own verdict, apart from the parser's. -/
private def scanAccepts (input : String) : Bool :=
  match Scanner.scan input with | .ok _ => true | .error _ => false

/-! ## §1  What §7.5 admits after a complete node

A break and a `#` — `[79] s-l-comments` — with the `s-white` run before them
that `[77] s-b-comment` allows. -/

#guard emits "k: \"a\"\nj: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL \"a", "=VAL :j", "=VAL :1", "-MAP",
   "-DOC", "-STR"]
#guard emits "k: \"a\"   \nj: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL \"a", "=VAL :j", "=VAL :1", "-MAP",
   "-DOC", "-STR"]
#guard emits "k: \"a\" # c\nj: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL \"a", "=VAL :j", "=VAL :1", "-MAP",
   "-DOC", "-STR"]
#guard emits "k: [1]\nj: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :j",
   "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "k: [1] # c\nj: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :j",
   "=VAL :1", "-MAP", "-DOC", "-STR"]

/-! ## §2  The residue's own inhabitants, refused

These are the shapes `accum_block_on_pendingContent` and
`accum_block_on_pendingBlockContent` used to defer: a park mid-line at a
complete node, no break crossed, a `-` or a `?` reached across `s-white`
alone.  Every park the two `h_line` fields have a producer for is here. -/

-- The quoted park (`validateTrailingContent`), at stream level and as a value.
#guard rejects "\"a\" - b\n"
#guard rejects "\"a\" ? b\n"
#guard rejects "'a' - b\n"
#guard rejects "'a' ? b\n"
#guard rejects "k: \"a\" - b\n"

-- The flow-close park (`validateFlowClose`), sequence and mapping.
#guard rejects "[1] - b\n"
#guard rejects "[1] ? b\n"
#guard rejects "{a: 1} - b\n"
#guard rejects "{a: 1} ? b\n"
#guard rejects "k: [1] - b\n"

-- The alias park (`validateAliasClose`, which IS `validateTrailingContent`).
#guard rejects "k: &x 1\nj: *x - c\n"
#guard rejects "k: &x 1\nj: *x ? c\n"

-- `pendingBlockContent`: the same node, one production in (`[185]`'s compact
-- alternative), and at a nonzero entry indent.
#guard rejects "- \"a\" - b\n"
#guard rejects "- \"a\" ? b\n"
#guard rejects "- 'a' - b\n"
#guard rejects "- [1] - b\n"
#guard rejects "- [1] ? b\n"
#guard rejects "- - \"a\" - b\n"
#guard rejects "? \"a\" - b\n"
#guard rejects "x:\n  - [1] - b\n"

/-! ## §3  The two WALKS never park in front of one

A plain scalar's stop set is `NodeTail` or `OffLine` for a different reason
than the validators': `[128] ns-plain-safe-out` is `ns-char`, so a `-` or a `?`
is ABSORBED into the scalar and no park in front of one exists to refute.  The
block scalar's line collection is the same walk, and it ends at column 0. -/

#guard emits "a - b\n" ["+STR", "+DOC", "=VAL :a - b", "-DOC", "-STR"]
#guard emits "a ? b\n" ["+STR", "+DOC", "=VAL :a ? b", "-DOC", "-STR"]
#guard emits "- a - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a - b", "-SEQ", "-DOC", "-STR"]
-- …and where the walk DOES stop, it stops at `#` or `:` — `NodeTail` again.
#guard emits "a #c - b\n" ["+STR", "+DOC", "=VAL :a", "-DOC", "-STR"]
#guard emits "k: |\n x\nj: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL |x\\n", "=VAL :j", "=VAL :1",
   "-MAP", "-DOC", "-STR"]

/-! ## §4  The `:` is the residue, and it must survive

What item 37 leaves at these two pendings is exactly one production —
`[154]`/`[155]`'s implicit key at a MID-LINE anchor — so the escape's type now
says `InlineResidue sp_scan ':'` and nothing else.  Refuting any of these would
be a defect, not a tightening; they are pinned so the boundary is visible. -/

#guard emits "\"a\" : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "[1] : b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
#guard emits "{a: 1} : b\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b",
   "-MAP", "-DOC", "-STR"]
#guard emits "- [1] : b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- 'a' : b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL 'a", "=VAL :b", "-MAP", "-SEQ",
   "-DOC", "-STR"]
#guard emits "a : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]

/-! ## §5  The boundary: a property run is not a node

`&a`/`!t` park a `[96] c-ns-properties` run, which is not a complete node and
so carries no §7.5 tail at all — nothing validated its line.  The scanner
refuses the identical shape there too, but by a different check: item 48's
same-line rule (`[200] s-l+block-collection` puts `s-l-comments` between a
node's properties and the collection), not this rung's node tail. -/

#guard !scanAccepts "&a - b\n" && rejectsAlike "&a - b\n"
#guard !scanAccepts "!t - b\n" && rejectsAlike "!t - b\n"
-- The contrast, one character apart: the node park refuses at the SCANNER.
#guard !scanAccepts "\"a\" - b\n"
#guard !scanAccepts "[1] - b\n"

end Tests.Guards.ScannerNodeTail

end Blanket
