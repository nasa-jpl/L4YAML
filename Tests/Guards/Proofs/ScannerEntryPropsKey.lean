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

/-! # `- &p a: 1` — the property run as a key head at every frame (DOCS item 41)

A `[96] c-ns-properties` run is not a node, so the accumulator PARKS it
(`pendingProps`) and finishes the value one step later.  Item 17 also made the
parked run a KEY head — `&p a` is `[161]`'s `propsContent` arm read at
`block-key`, which is `[188] ns-s-block-map-implicit-key`'s `[194]` alternative —
but it wrote what the finished entry does with itself as the run's own
COORDINATES: a column-0 line start, the stream closed there, `[63] s-indent(k)`
in between.  That triple is `rootMapRoute`'s argument list, so the only producer
it ever admitted was the root one, and `- &p a: 1` deferred.

Item 41 is item 38 applied to the sibling pack.  `PropsKeyPack` now carries the
CONCLUSION those coordinates were only one way to reach —
`∀ sp_v, SBlockMapEntry k sp_p sp_v → SLYamlStream sp_start sp_v` — and
`entryPropsKeyPack_of_dispatch` is `entryKeyPack_of_dispatch` with the run in the
key head's place, merged over the landing disjunct exactly as item 40 merged the
scalar pack's two producers.  The consumer got shorter by the one `rootMapRoute`
application it used to make.

What the four call sites gain is the INTERSECTION of two independent
restrictions — which landing branch the caller's input analysis can see, and
which frame the pending it parks can close (Reflection 667):

| parked at                        | branches seen | frames offered  | served  |
| :------------------------------- | :------------ | :-------------- | :------ |
| `-` / root, index 0              | line + break  | compact + node  | both    |
| `-`, indented                    | line only     | compact + node  | compact |
| `[189]` value, index 0           | line + break  | node only       | break   |
| `[189]` value, indented          | line only     | node only       | none    |

§1 the family at each frame.  §2 composing.  §3 the two halves of the pack that
did NOT move.  §4 what still punts — including the fourth row above — and the
boundary the scanner keeps.
-/

namespace Tests.Guards.ScannerEntryPropsKey

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

/-- The SCANNER's own verdict, apart from the parser's. -/
private def scanAccepts (input : String) : Bool :=
  match Scanner.scan input with | .ok _ => true | .error _ => false

/-! ## §1  The run heads a key at each of the entry's frames

Three frames, one reading of the characters.  On the `-`'s own line the entry is
`[185] s-l+block-indented`'s `s-indent(m) ns-l-compact-mapping(n+1+m)`, closing
the enclosing entry (`compactMapRoute`).  Across a break to column 0 it belongs
to a mapping nested inside the node the pending awaits — `[185]`'s block-node
alternative under a `-`, `[189]`'s value slot under a `k:` — and `[199]
s-l+block-collection` spends the landing as its own leading comments
(`valueMapRoute`).  The key HEAD is the same in all three: `[194]`'s
`c-flow-json-node` at `block-key`, whose props slot the run fills. -/

#guard emits "- &p a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  &p a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "k:\n  &p a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]
-- The INDENTED sequence entry, which sees the compact branch only.
#guard emits "  - &p a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- Either half of `[96]`, and both halves: the pack takes the run at whatever
-- index the property push built it with (`PropsRun`'s `(ha, ht)`).
#guard emits "- !t a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL <!t> :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- &p !t a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p <!t> :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- !!str a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL <tag:yaml.org,2002:str> :a", "=VAL :1", "-MAP",
   "-SEQ", "-DOC", "-STR"]
#guard emits "- !<tag:x> a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL <tag:x> :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
-- `[193]`'s `s-separate-in-line?` slot, `[189]`'s empty value, a comment tail,
-- and a multi-word plain key behind the run.
#guard emits "- &p a : 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- &p a:\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- &p a: 1 # c\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- &p a b: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a b", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
-- `[188]`'s JSON arm behind the run: both quote styles.
#guard emits "- &p \"a\": 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p \"a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- &p 'a': 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p 'a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- The VALUE is whatever node may follow; the key's reading does not touch it.
#guard emits "- &p a: [1,2]\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- &p a: &q 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL &q :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
-- …and the entry reads inside an explicit document too.
#guard emits "---\n- &p a: 1\n"
  ["+STR", "+DOC ---", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]

/-! ## §2  Composing

Siblings at the entry's width, a second level, the enclosing collection
continuing over it compact and not, the landing's own comment and blank lines,
block scalars, and the run's frame under each of the two nestings item 40
closed. -/

#guard emits "- &p a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  &p a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-SEQ", "-DOC", "-STR"]
#guard emits "k:\n  &p a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL &p :a", "=VAL :1", "=VAL :b",
   "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "-\n  &p a:\n    b: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "+MAP", "=VAL :b", "=VAL :1", "-MAP",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "k:\n  &p a:\n    b: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL &p :a", "+MAP", "=VAL :b", "=VAL :1",
   "-MAP", "-MAP", "-MAP", "-DOC", "-STR"]
-- The enclosing sequence continues over it, compact and not, and each sibling
-- entry opens the same frame again.
#guard emits "- &p a: 1\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "=VAL :b", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- &p a: 1\n- &q b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "+MAP", "=VAL &q :b",
   "=VAL :2", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n  &p a: 1\n-\n  &q b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "+MAP", "=VAL &q :b",
   "=VAL :2", "-MAP", "-SEQ", "-DOC", "-STR"]
-- The landing is `[79] s-l-comments`, so comment and blank lines are part of it.
#guard emits "-\n  # c\n  &p a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-\n\n  &p a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- Block scalars: the compact frame cannot measure its own column, so the
-- pack punts the floor conjunct there and recovers it across a break, exactly
-- as `ImplicitKeyPack` does (items 28/29, 38, 39).
#guard emits "- &p a: |\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL |x\\n", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "-\n  &p a: |\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL |x\\n", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- &p a: >\n    x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL >x\\n", "-MAP", "-SEQ", "-DOC",
   "-STR"]
-- Under an enclosing entry: item 33's compact SEQUENCE and item 30's indented
-- one, each with this item's key inside it.
#guard emits "- -\n    &p a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-SEQ",
   "-DOC", "-STR"]
#guard emits "k:\n  -\n    &p a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP",
   "-SEQ", "-MAP", "-DOC", "-STR"]
-- The document end closes the entry's map like any other `[79]` landing.
#guard emits "- &p a: 1\n...\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC ...",
   "-STR"]

/-! ## §3  The two halves of the pack that did NOT move

Only the route changed.  The run's `block-key` re-read is item 17's — `[96]`'s
context occurs inside its optional second half alone, so a single-half run reads
anywhere (`PropsRun.toPropertiesBlockKey`) and a two-half one only when its
internal separation stayed on the line, which is what the extension arm builds
it from.  And the §7.4 datum is item 17's too: the key the `:` will resolve was
saved AT the property, so `&p a: 1` records its key one column left of where
`a: 1` does, and the root reading is unchanged. -/

#guard emits "&p a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "  &p a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- The run's second half arrives on its own step and the key does not move, so
-- long as it stays on the LINE — which is the two-half re-read's whole side
-- condition.  Across a break the run decorates the COLLECTION instead, and is
-- no longer a key head at all: `+MAP &p` rather than `=VAL &p <!t> :a`.
#guard emits "- &p !t a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p <!t> :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- &p\n  !t a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP &p", "=VAL <!t> :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
-- `? a` behind a run is `[186]`'s explicit key, not this pack's implicit one:
-- the run decorates the key's NODE and the entry was opened by the `?`.
#guard emits "? &p a\n: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "- ? &p a\n  : 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]

/-! ## §4  What still punts, and the boundary the scanner keeps

The fourth row of this file's table is the site that gains nothing, and it is
empty for two reasons at once: the arm sees the break-free branch only, and a
`[189]` VALUE slot is `s-l+block-node`, which has no compact alternative to
close.  Neither restriction is a boundary alone — `k:⏎  &p a: 1` above is the
same pending's break-crossed reading, and `  - &p a: 1` above is the same
branch's compact one — which is what makes the intersection worth computing
before writing the call (Reflection 667).

Below that: a closed FLOW node parks through the flow machinery, so its `:` is
`FlowOpenStack`'s business; a block-scalar header is a node and never a key; and
what the scanner refuses it refuses before any of this is asked. -/

-- The mapping VALUE's on-line landing: `[194]`'s value slot has no same-line
-- mapping, and the scanner refuses it there (item 48's `nestedMappingOnLine`).
#guard !scanAccepts ": &p a: 1\n" && rejectsAlike ": &p a: 1\n"
#guard !scanAccepts "k:\n  : &p a: 1\n" && rejectsAlike "k:\n  : &p a: 1\n"
-- A run in front of a closed flow collection: `[194]`'s own alternative, parked
-- by the flow machinery rather than by this content dispatch.
#guard emits "- &p [1]: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ [] &p", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]
#guard emits "- &p {a: 1}: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP {} &p", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]
-- `&p |` is `[198]`'s props-slotted block scalar, a node and never a key.
#guard emits "- &p |\n    x\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &p |x\\n", "-SEQ", "-DOC", "-STR"]
-- `[63] s-indent(w)` is SPACES, wherever in the run the tab sits (items 31/32).
#guard !scanAccepts "-\n\t&p a: 1\n" && rejectsAlike "-\n\t&p a: 1\n"
#guard !scanAccepts "-\n \t&p a: 1\n" && rejectsAlike "-\n \t&p a: 1\n"
#guard !scanAccepts "- \t&p a: 1\n" && rejectsAlike "- \t&p a: 1\n"
-- A landing at or left of the entry's own width is not this construct, and
-- `[183]`'s auto-detected `m` is positive, so the scanner says so first.
#guard !scanAccepts "-\n&p a: 1\n" && rejectsAlike "-\n&p a: 1\n"
#guard !scanAccepts "- -\n  &p a: 1\n" && rejectsAlike "- -\n  &p a: 1\n"
#guard !scanAccepts "k:\n  -\n  &p a: 1\n" && rejectsAlike "k:\n  -\n  &p a: 1\n"
-- Ragged indentation, and a block-scalar body shallower than its key.
#guard !scanAccepts "- &p a: 1\n b: 2\n" && rejectsAlike "- &p a: 1\n b: 2\n"
#guard !scanAccepts "- &p a: |\n x\n" && rejectsAlike "- &p a: |\n x\n"
-- A second half of the same kind dies at item 9k's own guard, and an ALIAS
-- behind a run dies at item 9e's — neither reaches the pack.
#guard !scanAccepts "- &a &b x: 1\n" && rejectsAlike "- &a &b x: 1\n"
#guard !scanAccepts "- &p *m : 1\n" && rejectsAlike "- &p *m : 1\n"

end Tests.Guards.ScannerEntryPropsKey

end Blanket
