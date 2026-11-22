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

/-! # `[204]`'s tail admits `s-l-comments` and nothing else (DOCS item 36)

Item 36 took the block dispatch's inline residue — a `-`/`?`/`:` reached from
a park that crossed no break and sits off column 0 — at the one of its seven
pendings that can refuse it outright.

`[204] l-document-suffix ::= c-document-end s-l-comments`.  A `...` is not a
node: it opens nothing, it closes a document, and `[79] s-l-comments` is the
whole of what may follow it on its own line.  `scanDocumentEnd` enforces
exactly that — whites, then a `#`, a break, or end of input — so a block
indicator on the marker's line is a state the machine never parks in.

The proof could not say so, because the fact it had was `LineNoOpen`: item 10
derived the same allowlist from the same check and then projected it onto the
ONE question its consumer asked ("is the head a `[` or a `{`?").  The stop set
now rides the predicate and the projection happens at the consumer, which is
what makes this file's §2 provable rather than merely true.

§1 pins the admitted tails.  §2 pins the refused ones — the residue's own
inhabitants, indicator by indicator.  §3 pins that the marker is DELIMITED, so
§2 is a statement about a real `...` and not about three dots inside a scalar.
§4 pins the next rung of the same ladder: §7.5's node tails, whose allowlist is
`s-l-comments` PLUS the `:` of `[154]`/`[155]`'s implicit key — a dichotomy, not
a filter.  §5 pins what this item deliberately leaves alone.
-/

namespace Tests.Guards.ScannerDocEndTail

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

/-- Both pipelines reject `input` (the twins may disagree on which check
    fires first; that is a separate question from the verdict). -/
private def rejects (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-- The SCANNER's own verdict, apart from the parser's. -/
private def scanAccepts (input : String) : Bool :=
  match Scanner.scan input with | .ok _ => true | .error _ => false

/-! ## §1  What `[79] s-l-comments` admits after the marker -/

-- Bare, and with the whites `s-b-comment` allows before end of line.
#guard emits "a\n...\n" ["+STR", "+DOC", "=VAL :a", "-DOC ...", "-STR"]
#guard emits "a\n...  \n" ["+STR", "+DOC", "=VAL :a", "-DOC ...", "-STR"]
-- A comment: the one non-blank the suffix admits.
#guard emits "a\n... # c\n" ["+STR", "+DOC", "=VAL :a", "-DOC ...", "-STR"]
#guard emits "a\n...   # c\nb\n"
  ["+STR", "+DOC", "=VAL :a", "-DOC ...", "+DOC", "=VAL :b", "-DOC", "-STR"]
-- …and the marker composes with what follows on LATER lines, which is the
-- half of the pending that is not at issue here.
#guard emits "a\n...\n---\nb\n"
  ["+STR", "+DOC", "=VAL :a", "-DOC ...", "+DOC ---", "=VAL :b", "-DOC", "-STR"]

/-! ## §2  The residue's own inhabitants, refused

These are exactly the shapes the block dispatch's inline residue stands for at
`pendingDocEnd`: a park mid-line (the marker's own end), no break crossed, and
a block indicator reached across `s-white` alone.  All three indicators, plus
the tab spelling and a plain content head for contrast. -/

#guard rejectsAlike "a\n... - b\n"
#guard rejectsAlike "a\n... ? b\n"
#guard rejectsAlike "a\n... : b\n"
#guard rejectsAlike "a\n...\t- b\n"
#guard rejectsAlike "a\n... x\n"
#guard rejectsAlike "a\n... [1]\n"
-- …and after a mapping, where the marker's park is reached from a different
-- pending chain but the suffix check is the same one.
#guard rejectsAlike "a: 1\n... - b\n"

/-! ## §3  The marker is delimited, so §2 is about a real `...`

`atDocumentEnd` wants the three dots followed by a blank or end of input.
Without that they are the head of a plain scalar and no `pendingDocEnd` is ever
created — which is why the refutation above may assume the marker's own
whites, and why `...#x` does NOT reach the suffix check. -/

#guard emits "a\n...#x\n" ["+STR", "+DOC", "=VAL :a ...#x", "-DOC", "-STR"]
#guard emits "a\n...a\n" ["+STR", "+DOC", "=VAL :a ...a", "-DOC", "-STR"]
#guard emits "a\n...- b\n" ["+STR", "+DOC", "=VAL :a ...- b", "-DOC", "-STR"]
#guard emits "a\n...:b\n" ["+STR", "+DOC", "=VAL :a ...:b", "-DOC", "-STR"]

/-! ## §4  The next rung: §7.5's node tails are a DICHOTOMY

`validateTrailingContent` (after a quoted scalar) and `validateFlowClose`
(after a flow collection returns to block context) are the same five lines of
code, and their allowlist is `[79] s-l-comments` PLUS `:`.  Read as a filter
that says "`-` and `?` are refused"; read as a case analysis it says the only
same-line continuation of a complete block-context node is `[154]`'s implicit
key.  Both halves are pinned here; the proof owes the second. -/

#guard rejects "\"a\" - b\n"
#guard rejects "\"a\" ? b\n"
#guard rejects "[1] - b\n"
#guard rejects "[1] ? b\n"
#guard rejects "{a: 1} - b\n"
#guard rejects "- \"a\" - b\n"

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

/-! ## §5  What this item leaves alone

Two families reach the same residue and are NOT refutable there, for opposite
reasons — pinned so the boundary is a measurement rather than an omission.

`&a - b` and `--- - a` are refused by the SCANNER (item 48's same-line check):
`[200] s-l+block-collection` puts `s-l-comments` between a node's properties
and the collection, so neither sequence may start on the line that opened it,
and the scanner now says so before any pending is asked.

`&a : b` is the other direction: accepted by everything and grammatical, an
anchored empty key under `[154]`, still riding the escape because no pending
re-reads a parked property run as a key. -/

#guard !scanAccepts "&a - b\n" && rejectsAlike "&a - b\n"
#guard !scanAccepts "!t - b\n" && rejectsAlike "!t - b\n"
#guard !scanAccepts "--- - a\n" && rejectsAlike "--- - a\n"
#guard !scanAccepts "--- ? a\n" && rejectsAlike "--- ? a\n"

#guard emits "&a : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "!t : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL <!t> :", "=VAL :b", "-MAP", "-DOC", "-STR"]

end Tests.Guards.ScannerDocEndTail

end Blanket
