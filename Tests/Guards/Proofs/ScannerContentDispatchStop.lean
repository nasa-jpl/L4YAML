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

/-! # The content dispatch's own stop-set reading (DOCS item 42)

Items 36 and 37 read the parked line facts — `[204]`'s `TailSuffix` after a
`...`, §7.5's `NodeStop` after a complete node — against the BLOCK dispatch,
where the three indicators had to be refuted one by one from the validators'
allowlists.  At the CONTENT dispatch the same facts meet a different partner:
the dispatch's own character class.  `scanNextToken_dispatchContent` returns
`.ok` only on the seven construct heads (`&`, `*`, `!`, `|`, `>`, `"`, `'`)
or a `[126] ns-plain-first` character, and that class contains no break, no
`#`, no non-printable and no BOM (`dispatchContent_ok_charFacts`).

So the two arms close by intersection rather than by enumeration:

* a `...` park's line stops at a break or a `#` (`TailSuffix`), the dispatch
  accepts neither — the arm is EMPTY (`docEnd_refutes_content_residue`);
* a complete node's line stops at `NodeStop`, and the intersection with the
  dispatch's class is exactly `[154]`'s `:` with a non-blank follower
  (`nodeStop_content_residue_is_colon`) — which the scanner refuses at the
  dispatch boundary (`scanNextToken_checkAdjacentValue`, item 47): read as a
  `[126]` plain-scalar head it would be a SECOND node in a one-node slot,
  and no production derives one.

§1 pins the `...` side: every same-line content head dies at the marker's own
scan (`trailingContentAfterDocEnd`), the `s-l-comments` tail is accepted, and
a `...` with content glued to it never scans a marker at all ([206]
`c-forbidden` wants a break, a white, or the end of input after the `...`, so
the plain walk absorbs the line).  §2 pins the node side: every content head
but the `:` dies at the node's own trailing validation, the `#` that reaches
the dispatch with `commentOk` down dies AT the dispatch, and the glued `:`
dies at the adjacent-value check — one character from the legal `[154]` form,
refused where `isValueCandidate` fell through (item 47).
-/

namespace Tests.Guards.ScannerContentDispatchStop

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

/-! ## §1  `[204]`: nothing follows a `...` but its own comment tail

Every content head on the marker's line is refused by `scanDocumentEnd`
itself, before any park exists — which is exactly why the accumulator's arm
has nothing to serve. -/

#guard !scanAccepts "a\n... b\n" && rejectsAlike "a\n... b\n"
#guard !scanAccepts "a\n... \"x\"\n"
#guard !scanAccepts "a\n... 'x'\n"
#guard !scanAccepts "a\n... &x\n"
#guard !scanAccepts "a\n... |\n"
#guard !scanAccepts "a\n... : b\n"

-- The accepted boundary: `[204]`'s own `s-l-comments`, whites and all.
#guard emits "a\n... #c\n" ["+STR", "+DOC", "=VAL :a", "-DOC ...", "-STR"]
#guard emits "a\n...\n"    ["+STR", "+DOC", "=VAL :a", "-DOC ...", "-STR"]
#guard emits "a\n... \n"   ["+STR", "+DOC", "=VAL :a", "-DOC ...", "-STR"]
#guard emits "a\n..."      ["+STR", "+DOC", "=VAL :a", "-DOC ...", "-STR"]

-- A `...` with content glued to it is not `[204] c-document-end` at all:
-- `[206] c-forbidden` requires a break, a white or the end of input after the
-- marker, so the plain walk absorbs the line and no park ever exists.
#guard emits "a\n...#c\n" ["+STR", "+DOC", "=VAL :a ...#c", "-DOC", "-STR"]
#guard emits "a\n...b\n"  ["+STR", "+DOC", "=VAL :a ...b", "-DOC", "-STR"]

/-! ## §2  §7.5 at the content dispatch: the residue is the `:`

Every other content head is refused by the completed node's own trailing
validation — the park's line fact and the refusal are the same decision. -/

#guard !scanAccepts "\"a\" x\n" && rejects "\"a\" x\n"
#guard !scanAccepts "\"a\" \"b\"\n"
#guard !scanAccepts "\"a\" 'b'\n"
#guard !scanAccepts "\"a\" &x\n"
#guard !scanAccepts "\"a\" |\n"
#guard !scanAccepts "- \"a\" x\n"

-- The `#` whose `commentOk` is DOWN (no white between the node and the `#`)
-- is the one stop-set character the validators admit that is not a `:` — and
-- it dies AT the content dispatch (`unexpectedChar`), which is the lemma's
-- own refutation observed at runtime.
#guard !scanAccepts "\"a\"#x\n" && rejectsAlike "\"a\"#x\n"
#guard !scanAccepts "- \"a\"#x\n"

-- The survivor is now REFUSED at the scanner (item 47): a `:` with a
-- non-blank follower after a completed node would read as a plain-scalar
-- head — a second node in a one-node slot — and
-- `scanNextToken_checkAdjacentValue` refuses it where `isValueCandidate`
-- fell through.  The over-acceptance these pins used to record is gone.
#guard !scanAccepts "\"a\" :b\n" && rejectsAlike "\"a\" :b\n"
#guard !scanAccepts "[1] :b\n" && rejectsAlike "[1] :b\n"
#guard !scanAccepts "- [1] :b\n" && rejectsAlike "- [1] :b\n"
#guard !scanAccepts "\"a\":b\n" && rejectsAlike "\"a\":b\n"
#guard !scanAccepts "'a':b\n" && rejectsAlike "'a':b\n"
#guard !scanAccepts "[1]:b\n" && rejectsAlike "[1]:b\n"

-- …and the legal forms on either side of it.
#guard emits "\"a\" : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "\"a\" #c\n" ["+STR", "+DOC", "=VAL \"a", "-DOC", "-STR"]
-- A plain scalar never parks in front of ` :b` at all — the walk absorbs it.
#guard emits "a :b\n" ["+STR", "+DOC", "=VAL :a :b", "-DOC", "-STR"]

end Tests.Guards.ScannerContentDispatchStop

end Blanket
