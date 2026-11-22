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

/-! # The explicit document's one-line body composes (DOCS item 43)

`--- a` is `[208] l-explicit-document`'s body taken as `[207] l-bare-document`
on the marker's own line: `[80] s-separate(0)`'s inline arm crosses the whites
after the `---`, the node reads at the top level, and `[79] s-l-comments`
closes it.  The park after a `---` is mid-line, so it cannot CLOSE first — the
route items 15–42 used everywhere else (close the pending at a landing, then
re-anchor) does not exist here — and the pending has carried its own closer
since the constructor was written: `h_doc_builder`'s `GAlt` left branch takes
exactly an `SLBareDocument` starting at the park.  Item 43 parameterizes the
content dispatch by that closer (`content_dispatch_routed`; the old
`content_dispatch_after_close` is its bare-document instance), and the branch
gets its FIRST consumer.

§1 pins the family: every content head the dispatch serves, at the marker —
plain, both quote styles, properties bare and valued, verbatim and shorthand
tags, both block scalars, tab separation, a trailing comment, the empty-node
`#c` form — and the closures behind it (a second document, a suffix, a
directive document, the multiline fold).  §2 pins the boundary the scanner
keeps: a block COLLECTION may not open on the marker's line (`[200]` puts
`s-l-comments` between `---` and a collection — `contentOnDocumentStartLine`,
scanner-accepted parser-refused, which is why the routed arm's key context
PUNTS and loses nothing: no implicit key ever fires behind this park), a
glued `---a`/`---#c` is no marker at all, and an alias at the root can never
resolve. -/

namespace Tests.Guards.ScannerDocStartInlineCompose

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

/-! ## §1  The one-line body, at every content head the dispatch serves -/

#guard emits "--- a\n"     ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
#guard emits "--- a b\n"   ["+STR", "+DOC ---", "=VAL :a b", "-DOC", "-STR"]
#guard emits "--- \"a\"\n" ["+STR", "+DOC ---", "=VAL \"a", "-DOC", "-STR"]
#guard emits "--- 'a'\n"   ["+STR", "+DOC ---", "=VAL 'a", "-DOC", "-STR"]
-- the property run parks `pendingProps` with the docStart ROUTE, bare or valued
#guard emits "--- &x a\n"  ["+STR", "+DOC ---", "=VAL &x :a", "-DOC", "-STR"]
#guard emits "--- &x\n"    ["+STR", "+DOC ---", "=VAL &x :", "-DOC", "-STR"]
#guard emits "--- !t\n"    ["+STR", "+DOC ---", "=VAL <!t> :", "-DOC", "-STR"]
#guard emits "--- !!str a\n"
  ["+STR", "+DOC ---", "=VAL <tag:yaml.org,2002:str> :a", "-DOC", "-STR"]
-- block scalars: `[198]`'s props slot is empty, the body reads below
#guard emits "--- |\n x\n" ["+STR", "+DOC ---", "=VAL |x\\n", "-DOC", "-STR"]
#guard emits "--- >\n x\n" ["+STR", "+DOC ---", "=VAL >x\\n", "-DOC", "-STR"]
#guard emits "--- |+\n x\n" ["+STR", "+DOC ---", "=VAL |x\\n", "-DOC", "-STR"]
-- the separation is `[66] s-separate-in-line`: a tab serves
#guard emits "---\ta\n"    ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
-- a comment tail, and the empty-node form it leaves behind
#guard emits "--- a #c\n"  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
#guard emits "--- #c\n"    ["+STR", "+DOC ---", "=VAL :", "-DOC", "-STR"]

-- …and what closes BEHIND the parked body: a second document, a suffix, a
-- directive document, the multiline fold.
#guard emits "--- a\n--- b\n"
  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "+DOC ---", "=VAL :b", "-DOC", "-STR"]
#guard emits "--- a\n...\n"
  ["+STR", "+DOC ---", "=VAL :a", "-DOC ...", "-STR"]
#guard emits "%YAML 1.2\n--- a\n"
  ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
#guard emits "--- a\nb\n"
  ["+STR", "+DOC ---", "=VAL :a b", "-DOC", "-STR"]
#guard emits "--- &x a\n--- &x b\n"
  ["+STR", "+DOC ---", "=VAL &x :a", "-DOC", "+DOC ---", "=VAL &x :b", "-DOC",
   "-STR"]

/-! ## §2  The boundary the scanner keeps

A block COLLECTION may not open on the marker's line: `[200]
s-l+block-collection` puts `s-l-comments` between a node's properties and the
collection, and the same reading holds at the document level.  The SCANNER
refuses the whole family (item 48: `sameLineBlockCollection` for `-`/`?`,
`contentOnDocumentStartLine` for a `:` behind the marker), which is the
reason the routed arm's key context punts without loss: no implicit key ever
fires behind a `---` park, spaced or not. -/

#guard !scanAccepts "--- a: 1\n" && rejectsAlike "--- a: 1\n"
#guard !scanAccepts "--- - a\n" && rejectsAlike "--- - a\n"
#guard !scanAccepts "--- ? a\n" && rejectsAlike "--- ? a\n"
#guard !scanAccepts "--- : a\n" && rejectsAlike "--- : a\n"
#guard !scanAccepts "--- a : b\n" && rejectsAlike "--- a : b\n"
#guard !scanAccepts "--- \"a\" : b\n" && rejectsAlike "--- \"a\" : b\n"
-- content past the one-line body's own close: the comment stops the plain
-- walk, so the root node is COMPLETE and the next line is a second bare
-- document — §9.2's refusal, at the scanner since item 132.
#guard !scanAccepts "--- a #c\nb\n" && rejectsAlike "--- a #c\nb\n"

-- A `---` with content glued to it is not `[203] c-directives-end` at all:
-- the plain walk absorbs the line ([206] c-forbidden wants a break, a white
-- or the end of input after the marker).
#guard emits "---a\n"  ["+STR", "+DOC", "=VAL :---a", "-DOC", "-STR"]
#guard emits "---#c\n" ["+STR", "+DOC", "=VAL :---#c", "-DOC", "-STR"]

-- An alias at the document root can never resolve (no anchor precedes it),
-- and dies at the dispatch.
#guard !scanAccepts "--- *x\n" && rejectsAlike "--- *x\n"

end Tests.Guards.ScannerDocStartInlineCompose

end Blanket
