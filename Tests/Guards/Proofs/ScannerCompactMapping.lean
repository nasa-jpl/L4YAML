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

/-! # `- a: 1` — `[195] ns-l-compact-mapping` (DOCS item 38)

Item 37 left `pendingContent` and `pendingBlockContent` owing exactly one
production: `[154] ns-s-implicit-yaml-key` / `[155] c-s-implicit-json-key` read
at an anchor that is not a column-0 line start.  This file pins the half of it
that a block-sequence ENTRY asks for.

`- a: 1` is `[185] s-l+block-indented`'s second alternative,
`s-indent(m) ns-l-compact-mapping(n+1+m)`: a mapping whose first entry has no
`s-indent` and no `s-l-comments` in front of it, because its key sits on the
same line as the `-` that opened the sequence entry.  The KEY head is the one
items 15–17 already read — `a` here reads exactly as the `a` of `a: 1` — and
what was missing was the FRAME.  Item 38 stopped writing the frame as the three
coordinates one producer happens to have (a column-0 landing, the stream closed
there, `[63] s-indent(k)` in front of the key) and started writing it as the
one thing the consumer does with them: a route from the finished `[188]` entry
back into the stream.  With that, `compactMapRoute` is a second producer of the
same pack and `- a: 1` composes where `a: 1` did.

§1 pins the compact mapping itself.  §2 pins it composing — siblings, nesting,
and the enclosing collection closing over it.  §3 pins the shapes whose pack
still punts: they PARSE, and what they are missing is a route, which is the
next item's business, not a defect.  §4 pins the boundary the scanner keeps.
-/

namespace Tests.Guards.ScannerCompactMapping

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

/-! ## §1  The compact mapping

One entry, opened by a key on the `-`'s own line.  The `s-indent(m)` in front
of the key is the whites between the indicator and the content — `m = 1` for a
single space, and `[195]`'s index is `n+1+m`, one for the `-` itself. -/

#guard emits "- a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- The `s-separate-in-line?` slot of `[193]`, and a wider `s-indent(m)`.
#guard emits "- a : 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "-  a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- `[189]`'s empty value, and `[79] s-l-comments` after the entry.
#guard emits "- a:\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- a: 1 # c\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- `[188]`'s JSON arm at the compact key: both quote styles, adjacent and spaced.
#guard emits "- \"a\": 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL \"a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- 'a': 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL 'a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- \"a\" : 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL \"a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- 'a' : 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL 'a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- The VALUE is whatever `[185]`'s awaited node may be — flow, block scalar,
-- property-decorated — none of which the key's own reading touches.
#guard emits "- a: [1,2]\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- a: |\n   x\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL |x\\n", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- a: &p 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL &p :1", "-MAP", "-SEQ", "-DOC", "-STR"]
-- …and the entry reads inside an explicit document too.
#guard emits "---\n- a: 1\n"
  ["+STR", "+DOC ---", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]

/-! ## §2  Composing

`[195]`'s own tail, `[186]`'s sibling entries at the enclosing width, one level
of nesting, and the collection closing over the mapping. -/

-- The mapping's second entry, at `[195]`'s `s-indent(n+1+m)`.
#guard emits "- a: 1\n  b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "-SEQ", "-DOC", "-STR"]
#guard emits "- a:\n  b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :", "=VAL :b", "=VAL :2", "-MAP",
   "-SEQ", "-DOC", "-STR"]
-- A sibling ENTRY of the enclosing sequence, compact and not.
#guard emits "- a: 1\n- b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "+MAP", "=VAL :b",
   "=VAL :2", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- a: 1\n- b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- a: 1\n  b: 2\n- c\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "=VAL :b", "=VAL :2", "-MAP",
   "=VAL :c", "-SEQ", "-DOC", "-STR"]
#guard emits "- a: 1\n- - b: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "+SEQ", "+MAP",
   "=VAL :b", "=VAL :2", "-MAP", "-SEQ", "-SEQ", "-DOC", "-STR"]
-- Nested: `[186]`'s compact SEQUENCE (item 33) with `[195]`'s compact mapping
-- inside it — the two alternatives of `[185]` that had no producer at all
-- before this campaign, composed.
#guard emits "- - a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- - a: 1\n  - b\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b",
   "-SEQ", "-SEQ", "-DOC", "-STR"]
-- The INDENTED entry: the same route at a nonzero enclosing index (item 22's
-- `n` riding through, item 38's `n+1+m`).
#guard emits "k:\n  - a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP",
   "-SEQ", "-MAP", "-DOC", "-STR"]

/-! ## §3  What still punts

These PARSE.  What their pack cannot build is a route, and each is a different
construct rather than a weaker instance of `[195]`:

* `-⏎  a: 1` crossed a break, so the mapping opens under `[79] s-l-comments` —
  `[185]`'s FIRST alternative, a nested collection, which wants the enclosing
  index bounded by the inner one;
* `- &p a: 1` parks a `[96] c-ns-properties` run, whose own pack is item 17's
  `PropsKeyPack` and whose route is the run's — item 41 gave that pack this
  item's route too, so this one composes now
  (`Tests/Guards/Proofs/ScannerEntryPropsKey.lean`);
* `- [1]: b` opens a FLOW collection, and its resume is `FlowOpenStack`'s
  pinned index — the row's other family entirely;
* `k:⏎  a: 1` is the same missing route one construct over, on the mapping
  VALUE's pending rather than the sequence entry's.

Pinning them here is what keeps the next item honest: the boundary is a list of
named routes, not a vague remainder. -/

#guard emits "-\n  a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- &p a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- [1]: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]
#guard emits "k:\n  a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-MAP",
   "-DOC", "-STR"]

/-! ## §4  The boundary

`[63] s-indent(m)` is SPACES, and the scanner says so before any of this is
reached (items 31/32).  A second `:` on the line is not a second key — §7.5's
tail admits one — and item 37's refutation at this very pending is unchanged by
the arm added in front of it. -/

#guard !scanAccepts "- \ta: 1\n" && rejectsAlike "- \ta: 1\n"
#guard !scanAccepts "-\ta: 1\n" && rejectsAlike "-\ta: 1\n"
-- A second `:` on the line: `[194]`'s value slot has no same-line mapping, and
-- the scanner refuses it there (item 48's `nestedMappingOnLine`).
#guard !scanAccepts "- a: b: c\n" && rejectsAlike "- a: b: c\n"
-- Item 37, at the pending this item extended: `-` and `?` are still refused.
#guard !scanAccepts "- \"a\" - b\n" && rejects "- \"a\" - b\n"
#guard rejects "- [1] ? b\n"
-- …and a `-` after a compact mapping's value is plain-scalar content, not an
-- entry: `[128] ns-plain-safe-out` absorbs it (item 37 §3).
#guard emits "- a: 1 - b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1 - b", "-MAP", "-SEQ", "-DOC", "-STR"]

end Tests.Guards.ScannerCompactMapping

end Blanket
