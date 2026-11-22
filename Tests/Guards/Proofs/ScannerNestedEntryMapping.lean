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

/-! # `-⏎  a: 1` — the mapping NESTED under a block entry (DOCS item 40)

Item 38 gave `ImplicitKeyPack` a route instead of one producer's coordinates and
spent it on the compact entry (`- a: 1`); item 39 spent it again on the mapping
that is the VALUE of a `[189]` entry (`k:⏎  a: 1`).  Both producers read the same
characters with the same lemma and differed only in the branch of the landing
they took — one stayed on the line, one crossed a break — so item 40 merges them
into `entryKeyPack_of_dispatch`, and the merge is what closes this file's family:
a `-`-parked pending now has the break-crossed frame too, which is `[185]
s-l+block-indented`'s block-node alternative with `[187] l+block-mapping`
auto-detected at the landing's width (`valueMapRoute` over `nestedBlockMap`,
item 39's lemma unchanged).

The second half is item 39's own boundary, re-cut.  `nestedBlockMap`'s side
condition `n ≤ k` is a statement about the LANDING, not about the arm: both
numbers are in hand where the pack is built, so the producer decides per input
and only a DEDENT defers.  Item 39 read it as a property of
`accum_content_on_pendingMapValue_indented` and left that arm punting whole;
§3 pins what it was punting.

§1 the family itself.  §2 composing.  §3 the indented value pending, re-opened,
with the dedents that genuinely defer.  §4 what still punts and the boundary the
scanner keeps.
-/

namespace Tests.Guards.ScannerNestedEntryMapping

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

/-! ## §1  The mapping nested under a `-`

The `-` parks the entry, the step crosses a break to column 0, and `[63]
s-indent(w)` walks to the key.  What the pending awaits is `[185]`'s
`s-l+block-node(n, block-in)`, so the landing is `[199] s-l+block-collection`'s
own `s-l-comments` and the mapping's width is auto-detected at `w` — the same
reading item 39 gave the mapping VALUE, under a different frame. -/

#guard emits "-\n  a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- The width is auto-detected, not fixed: any indent past the `-` opens it.
#guard emits "-\n a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n   a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- `[193]`'s `s-separate-in-line?` slot, `[189]`'s empty value, a comment tail.
#guard emits "-\n  a : 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  a:\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  a: 1 # c\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- `[188]`'s JSON arm at the nested key: both quote styles.
#guard emits "-\n  \"a\": 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL \"a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  'a': 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL 'a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- …and its alias arm, which needs no one-line reading at all (item 17).
#guard emits "-\n  a: &x 1\n  *x : 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL &x :1", "=ALI *x", "=VAL :2", "-MAP",
   "-SEQ", "-DOC", "-STR"]
-- The VALUE is whatever node may follow; the key's reading does not touch it.
#guard emits "-\n  a: [1,2]\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  a: &p 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL &p :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- …and the entry reads inside an explicit document too.
#guard emits "---\n-\n  a: 1\n"
  ["+STR", "+DOC ---", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]

/-! ## §2  Composing

Siblings at the nested width, a second level, the sibling ENTRY of the enclosing
sequence, the landing's own comment and blank lines, and the two nestings that
put this frame under another entry.  The block scalars are the floor conjunct's
shapes: crossing a break to a known zero is what lets `[63]`'s width be
measured, so the pack carries the entry's index here where item 38's compact
route had to punt it. -/

#guard emits "-\n  a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  a:\n    b: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :1", "-MAP", "-MAP",
   "-SEQ", "-DOC", "-STR"]
-- The enclosing sequence continues over it, compact and not.
#guard emits "-\n  a: 1\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b", "-SEQ", "-DOC",
   "-STR"]
#guard emits "-\n  a: 1\n-\n  b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "+MAP", "=VAL :b",
   "=VAL :2", "-MAP", "-SEQ", "-DOC", "-STR"]
-- The landing is `[79] s-l-comments`, so comment and blank lines are part of it.
#guard emits "-\n  # c\n  a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n\n  a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- The block scalar the pack's recovered index is about.
#guard emits "-\n  a: |\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL |x\\n", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  a: >\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL >x\\n", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  a: |\n   x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL |x\\n", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  a: |\n    x\n  b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :b", "=VAL :2", "-MAP",
   "-SEQ", "-DOC", "-STR"]
-- Under an enclosing entry: item 33's compact SEQUENCE, and item 30's indented
-- one, each with this item's mapping inside it.
#guard emits "- -\n    a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-SEQ",
   "-DOC", "-STR"]
#guard emits "k:\n  -\n    a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ",
   "-MAP", "-DOC", "-STR"]
-- The document end closes the nested map like any other `[79]` landing.
#guard emits "-\n  a: 1\n...\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC ...", "-STR"]

/-! ## §3  Item 39's boundary, re-cut

`accum_content_on_pendingMapValue_indented` was left punting whole because a
landing THERE may be a dedent.  It may also not be: `n ≤ k` is decidable where
the pack is built, so the arm now serves every landing that nests.  The last two
are the dedents, which still take the deferral — they are pinned as ACCEPTED,
because the boundary is about which derivation the accumulation can name, not
about what the runtime does. -/

#guard emits "k:\n  :\n    a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "+MAP", "=VAL :a", "=VAL :1",
   "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  ? x\n  :\n    a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :x", "+MAP", "=VAL :a", "=VAL :1",
   "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "- :\n    a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-SEQ", "-DOC", "-STR"]
#guard emits "- :\n    a: 1\n    b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b",
   "=VAL :2", "-MAP", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "k:\n  :\n    a: |\n      x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "+MAP", "=VAL :a", "=VAL |x\\n",
   "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]
-- The dedents: the enclosing entry has ENDED, so there is no node left to nest
-- inside and the pack's fact is false rather than unproved (Reflection 665's
-- boundary, now a shape rather than an arm).
#guard emits "k:\n  :\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP", "=VAL :b",
   "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  -\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :", "-SEQ", "=VAL :b", "=VAL :2",
   "-MAP", "-DOC", "-STR"]

/-! ## §4  What still punts, and the boundary the scanner keeps

The `&`/`!` head was item 17's pack, still carrying the coordinates
`ImplicitKeyPack` shed — item 41 gave it the same route and the first two pins
below now COMPOSE (`Tests/Guards/Proofs/ScannerEntryPropsKey.lean`); they stay
here because the emitted events are the same either way and this file's family is
where the head was first named.  A closed FLOW node is `FlowOpenStack`'s resume
type; and `[186]`'s explicit entry is an opener, not a key the content dispatch
parked.  Below them is what the scanner decides before any of it is asked. -/

#guard emits "-\n  &p a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  !t a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL <!t> :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "-\n  [1]: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP", "-SEQ",
   "-DOC", "-STR"]
#guard emits "-\n  {a: 1}: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP {}", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  ? a\n  : b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-SEQ", "-DOC", "-STR"]
-- A landing at the entry's OWN width is not this construct, and the scanner says
-- so first: `[183]`'s auto-detected `m` is positive, so an entry's node cannot
-- open at the indicator's column.  (A landing LEFT of it is the dedent of §3,
-- which the scanner accepts and the producer defers.)  So the `n ≤ w` the
-- producer tests is strict wherever a sequence entry parks it.
#guard !scanAccepts "-\na: 1\n" && rejectsAlike "-\na: 1\n"
#guard !scanAccepts "k:\n  -\n  a: 1\n" && rejectsAlike "k:\n  -\n  a: 1\n"
#guard !scanAccepts "- -\n  a: 1\n" && rejectsAlike "- -\n  a: 1\n"
-- …while at a mapping VALUE the equal-width landing IS accepted, and the parser
-- reads it as a SIBLING entry of the enclosing map rather than a nested one.
-- `SBlockNode.blockMap` takes `m : Nat` where `[187]` writes `m > 0` (item 22),
-- so the route the accumulation names there is one the spec would not — an
-- over-width of the encoding, row 19's business and not this item's.
#guard emits "k:\n  :\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "=VAL :b", "=VAL :2",
   "-MAP", "-MAP", "-DOC", "-STR"]
-- `[63] s-indent(w)` is SPACES, wherever in the run the tab sits (items 31/32).
#guard !scanAccepts "-\n\ta: 1\n" && rejectsAlike "-\n\ta: 1\n"
#guard !scanAccepts "-\n \ta: 1\n" && rejectsAlike "-\n \ta: 1\n"
-- Ragged indentation inside the nested map is refused at the scanner.
#guard !scanAccepts "-\n  a: 1\n b: 2\n" && rejectsAlike "-\n  a: 1\n b: 2\n"
-- A block scalar body shallower than its key is not the entry's node.
#guard !scanAccepts "-\n  a: |\n x\n" && rejectsAlike "-\n  a: |\n x\n"
-- …and flush with it the body is empty, leaving `x` a DANGLING run at the
-- key's own level — §9.2's, refused at the scanner (item 133).
#guard !scanAccepts "-\n  a: |\n  x\n" && rejectsAlike "-\n  a: |\n  x\n"
-- A second `:` on the line is refused at the scanner (item 48's
-- `nestedMappingOnLine`): `[194]`'s value slot has no same-line mapping.
#guard !scanAccepts "-\n  a: b: c\n" && rejectsAlike "-\n  a: b: c\n"
-- The `-` after a plain scalar is ABSORBED by `[128] ns-plain-safe-out` (item
-- 37), so no residue reaches the dispatch; after a QUOTED one it is genuine.
#guard emits "-\n  a - b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a - b", "-SEQ", "-DOC", "-STR"]
#guard !scanAccepts "-\n  \"a\" - b\n" && rejects "-\n  \"a\" - b\n"

end Tests.Guards.ScannerNestedEntryMapping

end Blanket
