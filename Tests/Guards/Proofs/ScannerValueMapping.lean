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

/-! # `k:⏎  a: 1` — the mapping nested in a `[189]` VALUE (DOCS item 39)

Item 38 replaced `ImplicitKeyPack`'s three coordinates with the one thing its
consumer does with them — a route from the finished `[188]` entry back into the
stream — and used the room that made to give `- a: 1` its own frame.  This file
pins the family that came next for free: the entry whose mapping is the VALUE of
an enclosing entry.

The frame is `[199] s-l+block-collection` under the node `k:` is waiting for,
with `[187] l+block-mapping`'s auto-detected width set to the column the key
actually landed at (`nestedBlockMap`, the mapping twin of item 30's
`nestedBlockSeq`).  Nothing else moved: the key head is items 15–17's, read by
`implicitKeyHead_of_dispatch` exactly as it reads `a: 1`'s and `- a: 1`'s, the
pack is unchanged, and `colon_fires_implicit_key` does not know there is a third
producer.

Between this route and the root one the landing is the SAME measurement — a
break crossed to column 0, with `[63] s-indent(k)` in front of the key.  What
differs is which `[79] s-l-comments` occurrence it fills: `[211]`'s implicit
continuation for the root mapping, `[199]`'s own leading comments here.  One
reading of the characters, two productions that want it — and because this route
crosses a break to a known zero, it also RECOVERS the floor conjunct the compact
route had to punt (§2's block scalars read their bodies at the entry's index).

§1 pins the value mapping itself.  §2 pins it composing — siblings, nesting,
dedent, and the two ways the enclosing entry can be opened.  §3 pins the shapes
whose pack still punts; they PARSE, and each is a different construct rather
than a weaker instance of this one.  §4 pins the boundary the scanner keeps.
-/

namespace Tests.Guards.ScannerValueMapping

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

/-! ## §1  The value mapping

One entry, opened at a landing INSIDE the node an enclosing `k:` is waiting for.
The `s-indent(k)` in front of the key is the whites between the landing and the
content, and `k` is the key's own column — `[187]`'s auto-detected width, which
`nestedBlockMap` sets to `k - n` rather than inlining it. -/

#guard emits "k:\n  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- The width is auto-detected, not fixed: any positive indent opens the same map.
#guard emits "k:\n a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n   a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- `[193]`'s `s-separate-in-line?` slot, and `[189]`'s empty value.
#guard emits "k:\n  a : 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  a:\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  a: 1 # c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- `[188]`'s JSON arm at the nested key: both quote styles.
#guard emits "k:\n  \"a\": 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL \"a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  'a': 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL 'a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- …and its alias arm, which needs no one-line reading at all (item 17).
#guard emits "k:\n  a: &x 1\n  *x : 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL &x :1", "=ALI *x",
   "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
-- The VALUE is whatever node may follow; the key's reading does not touch it.
#guard emits "k:\n  a: [1,2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []", "=VAL :1", "=VAL :2",
   "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a: &p 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL &p :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- …and the entry reads inside an explicit document too.
#guard emits "---\nk:\n  a: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]

/-! ## §2  Composing

Siblings at the nested width, a second level, the dedent that ends the nested
map, the landing's own comment and blank lines, and the two other ways a
`pendingMapValue` at column 0 is opened (`[189]`'s empty key, `[186]`'s explicit
one).  The block scalars are the floor conjunct's pin: their bodies are read
against the ENTRY's index, which is what this route recovers and the compact
route (item 38) had to punt. -/

#guard emits "k:\n  a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2",
   "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a:\n    b: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :1",
   "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]
-- The dedent CLOSES the nested map — the route's side condition `n ≤ k` fails
-- there by design, and the sibling belongs to the enclosing one.
#guard emits "k:\n  a: 1\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b",
   "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a: 1\nk2:\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "=VAL :k2",
   "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a: 1\n  b:\n    c: 2\nd: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "+MAP",
   "=VAL :c", "=VAL :2", "-MAP", "-MAP", "=VAL :d", "=VAL :3", "-MAP", "-DOC", "-STR"]
-- The landing is `[79] s-l-comments`, so comment and blank lines are part of it.
#guard emits "k:\n  # c\n  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n\n  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- `[189]`'s empty key and `[186]`'s explicit one park the SAME pending (item 13
-- / item 20), so both reach this route.
#guard emits ":\n  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "? x\n:\n  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :x", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- The floor: a block scalar body collected against the nested entry's index.
#guard emits "k:\n  a: |\n    x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL |x\\n", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  a: |\n   x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL |x\\n", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  a: >\n    x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL >x\\n", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  a: |\n    x\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :b",
   "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
-- The sequence twin of the same value slot, which item 30 already composed.
#guard emits "k:\n  - a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP",
   "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n- a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP",
   "-SEQ", "-MAP", "-DOC", "-STR"]

/-! ## §3  What still punts

Each of these PARSES; what the pack hands the `:` is `True`.  None of them is a
weaker instance of §1 — each names a construct with its own frame, which is what
makes the residue a list of routes rather than a residue.

The first is this item's own boundary and the reason the route is confined to
`n = 0`: at an INDENTED `pendingMapValue` a landing can be a dedent, and then
`n ≤ k` is false — the enclosing entry has ended, so there is no mapping to nest
inside its value. -/

#guard emits "- k:\n    a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP",
   "-MAP", "-SEQ", "-DOC", "-STR"]
-- A `[96]` property run parks `pendingProps`, whose pack (item 17) still
-- carries the coordinates this one shed.
#guard emits "k:\n  &x a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL &x :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  !t a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL <!t> :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- A closed FLOW node as the key is `FlowOpenStack`'s resume type, not this
-- pending's route.
#guard emits "k:\n  [1]: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  {a: 1}: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "+MAP {}", "=VAL :a", "=VAL :1", "-MAP",
   "=VAL :b", "-MAP", "-MAP", "-DOC", "-STR"]
-- `[186]`'s explicit entry inside the nested map: a `?` opener, not a key the
-- content dispatch parked.
#guard emits "k:\n  ? a\n  : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-MAP",
   "-DOC", "-STR"]

/-! ## §4  The boundary

What the scanner refuses outright, what it accepts and the parser refuses (row
19's business, unchanged by this item), and what `[128] ns-plain-safe-out`
absorbs before any of it can be asked. -/

-- The TAB punt is unobservable: `[63] s-indent(k)` wants spaces, and §6.1
-- refuses the tab first, wherever in the run it sits.
#guard !scanAccepts "k:\n\ta: 1\n" && rejectsAlike "k:\n\ta: 1\n"
#guard !scanAccepts "k:\n \ta: 1\n" && rejectsAlike "k:\n \ta: 1\n"
-- Ragged indentation inside the nested map is refused at the scanner.
#guard !scanAccepts "k:\n  a: 1\n b: 2\n" && rejectsAlike "k:\n  a: 1\n b: 2\n"
-- A block scalar body flush with its key is not the entry's node: the empty
-- body leaves `x` a DANGLING run at the key's own level, which §9.2 refuses at
-- the scanner (item 133).
#guard !scanAccepts "k:\n  a: |\n  x\n" && rejectsAlike "k:\n  a: |\n  x\n"
-- A second `:` on the line is refused at the scanner (item 48's
-- `nestedMappingOnLine`): `[194]`'s value slot has no same-line mapping.
#guard !scanAccepts "k: a: 1\n" && rejectsAlike "k: a: 1\n"
#guard !scanAccepts "k:\n  a: b: c\n" && rejectsAlike "k:\n  a: b: c\n"
-- The `-` after a plain scalar is ABSORBED into it (item 37), so no residue
-- reaches the dispatch at all…
#guard emits "k:\n  a - b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a - b", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a: 1 - b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1 - b", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- …while after a QUOTED one it is a genuine residue, and refused.
#guard scanAccepts "k:\n  \"a\" - b\n" = false && rejects "k:\n  \"a\" - b\n"
-- The document end closes the nested map like any other `[79]` landing.
#guard emits "k:\n  a: 1\n...\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC ...", "-STR"]

end Tests.Guards.ScannerValueMapping

end Blanket
