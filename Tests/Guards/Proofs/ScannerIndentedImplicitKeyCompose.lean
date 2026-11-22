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

/-! # The INDENTED implicit key composes (DOCS item 25)

Items 15–17 built `[188] ns-s-block-map-implicit-key`'s whole vocabulary —
plain, quoted, alias and property-prefixed heads — and then admitted exactly
one of its inhabitants, the key at column 0.  The restriction was not in any
key production: `ImplicitKeyPack` demanded `sp_key.col = 0`, and
`keyctx_of_preprocess` supplied that fact by REFUSING the case where
preprocessing crossed residual whites (`GStar.cons` punted).  So `a: 1` had a
derivation and `  a: 1` did not — and an indented mapping is most of the
language, including every nested one.

The whites were a measurement, not an obstruction.  `[187] l+block-mapping(n)`
is `( s-indent(n+m) ns-l-block-map-entry(n+m) )+` for an auto-detected `m`, so
the run between the line start and the key IS the entry's `[63] s-indent(k)` —
the same reading item 22 gave the whites before a block indicator, through the
same splitter (`gstar_white_sIndent_or_tab`), with the TAB disjunct the only
thing left punting.

Nothing about the KEY moves with it.  `[193] ns-s-block-map-implicit-key` and
`[194] c-s-implicit-json-key` take no indent at all — the spec writes `n/a` —
which is why `SImplicitKey` has never been indexed and why item 25 adds no
lift, no side condition, and no arm to any of items 15–17's readings.  The
index enters in exactly two places: the `s-indent(k)` in front of the entry,
and `rootBlockMap k`, which binds `m` once for the collection exactly as
`colon_open_map` has since item 22.

Nothing here is new BEHAVIOUR — item 25 edits no runtime file.  These are the
shapes whose accumulation changed, held fixed so a later runtime change cannot
move them silently.  §6 pins what the pack still does not reach, and each of
those has a cause that is not the key.
-/

namespace Tests.Guards.ScannerIndentedImplicitKeyCompose

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

/-! ## §1  A plain key at a nonzero indent

The width is read off the whites the preprocessing already crossed, so 2 and 4
are the same proof — `k` is whatever `[63] s-indent(k)` measures. -/

#guard emits "  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "    a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- `[132] nb-ns-plain-in-line` inside the key, and inside the value.
#guard emits "  a b: c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a b", "=VAL :c", "-MAP", "-DOC", "-STR"]
#guard emits "  a: b c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b c", "-MAP", "-DOC", "-STR"]
-- `[192] c-l-block-map-implicit-value`'s `e-node` alternative, at indent.
#guard emits "  a:\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "  a: \n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "  a: 1 # c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]

/-! ## §2  The quoted heads

`[194] c-s-implicit-json-key` carries no indent, so items 16's one-line bodies
slot in unchanged — the pack's new `s-indent(k)` sits in front of the head, not
inside it. -/

#guard emits "  \"a\": b\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "  'a': b\n"
  ["+STR", "+DOC", "+MAP", "=VAL 'a", "=VAL :b", "-MAP", "-DOC", "-STR"]

/-! ## §3  The property-prefixed head

Item 17's `PropsKeyPack` took the same treatment: its column-0 coordinate
became a line start plus `s-indent(k)`, and the run itself is re-read at
`block-key`, where `s-separate(n,block-key)` is `[66] s-separate-in-line` and
mentions no index at all.  (Item 41 then spent those coordinates once, into the
route the pack now carries, which is what lets the same head read inside a block
ENTRY — `Tests/Guards/Proofs/ScannerEntryPropsKey.lean`.) -/

#guard emits "  &x a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "  !!str a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL <tag:yaml.org,2002:str> :a", "=VAL :1", "-MAP",
   "-DOC", "-STR"]
#guard emits "  &x a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-DOC", "-STR"]
#guard emits "  a: 1\n  &x b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL &x :b", "=VAL :2", "-MAP",
   "-DOC", "-STR"]

/-! ## §4  Values at the entry's own index

The value is `[192]`'s `s-l+block-node(n,block-out)` at the same `k` the key
was measured at, which is item 23's break-free reading — one question, two
consumers. -/

#guard emits "  a: \"x\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL \"x", "-MAP", "-DOC", "-STR"]
#guard emits "  a: 'x'\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL 'x", "-MAP", "-DOC", "-STR"]
#guard emits "  a: &x v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL &x :v", "-MAP", "-DOC", "-STR"]

/-! ## §5  Siblings, blank and comment lines, and the document frame

A sibling entry re-measures its own `s-indent(k)` and rides `[211]`'s bare
document continuation, exactly as item 13's col-0 `: v` chain does. -/

#guard emits "  a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-DOC", "-STR"]
#guard emits "  a: 1\n  b: 2\n  c: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2", "=VAL :c",
   "=VAL :3", "-MAP", "-DOC", "-STR"]
#guard emits "  a: 1\n  b:\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :", "-MAP",
   "-DOC", "-STR"]
#guard emits "  a: 1\n\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-DOC", "-STR"]
#guard emits "  a: 1\n  # c\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-DOC", "-STR"]
#guard emits "---\n  a: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- The explicit twin at the same width (items 20/22), for contrast: it never
-- needed the pack, because `?` parks the mapping before any key exists.
#guard emits "  ? a\n  : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]

/-! ## §6  What the indented pack does NOT reach — accepted, derivation owed

Three residues, and the KEY is none of them — each is a value the entry's index
cannot yet be pushed into:

* `  a: |` is `[170]`/`[174]`'s auto-detected content indent, the same gap
  `  - |` has (Reflection 647 one level down);
* `  a: [1,2]` is `FlowOpenStack`'s resume type, the same pin `  - [1]` rides;
* `  a:⏎  - x` is a nested block collection, which wants `SBlockIndented`'s
  `compactSeq`/`compactMap` arms.

`  - a: 1` is not an indented key at all: the mapping is COMPACT inside a
sequence entry, so it is `[185]`'s `compactMap` and never reaches the pack —
the pending it parks under is the entry's, not a line start's. -/

#guard emits "  a: |\n    t\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |t\\n", "-MAP", "-DOC", "-STR"]
#guard emits "  a: [1,2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "-MAP", "-DOC", "-STR"]
#guard emits "  a:\n  - x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :x", "-SEQ", "-MAP", "-DOC",
   "-STR"]
#guard emits "  - a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]

/-! ## §7  The width is fixed once for the collection

`[187]`'s `m` is auto-detected and then SHARED, so a sibling at a different
width is not a wider mapping — the scanner refuses it, which is what keeps
`rootBlockMap k`'s single `k` faithful.  A tab is `[63]`'s other disjunct and
still punts on the grammar side, but the scanner answers first. -/

#guard verdicts "  a: 1\n   b: 2\n" ==
  (some (.invalidImplicitKey 1), some (.invalidImplicitKey 1))
#guard verdicts "  a: 1\nb: 2\n" ==
  (some (.trailingContent 1 0), some (.trailingContent 1 0))
#guard verdicts "\ta: 1\n" ==
  (some (.tabInIndentation 0 0), some (.tabInIndentation 0 0))
#guard verdicts "  \ta: 1\n" ==
  (some (.tabInIndentation 0 2), some (.tabInIndentation 0 2))

end Tests.Guards.ScannerIndentedImplicitKeyCompose

end Blanket
