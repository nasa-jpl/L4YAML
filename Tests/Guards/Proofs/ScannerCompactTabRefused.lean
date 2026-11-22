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

/-! # A tab in the COMPACT `s-indent(m)` is refused — including in front of `:`
    (DOCS item 34)

Item 33 gave the inline residue `[185] s-l+block-indented`'s compact
alternatives and left exactly one shape behind: a tab in front of a compact `:`.
The reason is worth stating precisely, because it is a statement about
COORDINATES rather than about evidence.

`[185]`'s `s-indent(m)` is `[63] s-indent`, so it is spaces, and §6.1 forbids a
tab there.  The scanner has two ways of saying so and they are not the same
question:

* `hasTabInPrecedingWhitespace` walks back over the whitespace RUN in front of
  the token and stops at the first non-white.  `scanBlockEntry` and `scanKey`
  read it unconditionally in block context, so `- →- a` and `- →? a` refuse.
* `tabInLineIndent` walks the whole LINE in front of the token and answers
  `false` the moment something on it is not a white.  That is the right
  coordinate for `[187] l+block-mapping`'s own entry — item 32 — and it answers
  `false` for a COMPACT indicator by construction: the entry's `-` really is on
  the line.

`scanValue` consults the second, then the recorded simple key, then the first.
So the compact `:` is decided by which branch it lands in, and that is a fact
about `simpleKeyAllowed`: every block indicator's scan sets it, a break-free
step never clears it, so preprocessing records a key AT the `:` and the key
branch walks back from the `:`'s own offset — the same run the fallback branch
would have read.  Both branches read the compact `s-indent(m)`; the run has a
tab; the scan throws.

That is what §1 and §2 pin.  §3 is what makes it exact rather than a blanket
ban on tabs after an indicator: a tab in front of CONTENT is
`[66] s-separate-in-line` and legal, and so is the gap between an implicit key
and its `:` (`[154] ns-s-implicit-yaml-key`'s own trailing separation).  The
line between the two is the line between `s-indent` and `s-separate-in-line`,
and the scanner draws it in the right place.

§4 pins the error itself — one rule, one error, at the tab's own coordinates in
both pipelines.
-/

namespace Tests.Guards.ScannerCompactTabRefused

open L4YAML

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-- Both pipelines reject `input` with §6.1's own error, at the same place. -/
private def refusesTab (input : String) (line col : Nat) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error e, .error e' => e == .tabInIndentation line col && e' == e
  | _, _ => false

/-! ## §1  The compact `:` — the shape item 34 closes

`- →: a` is `[195] ns-l-compact-mapping` opening on the entry's line, so the run
between the `-` and the `:` is `[185]`'s `s-indent(m)` and nothing else can it
be: there is no key in front of this `:` to make the run a separation. -/

#guard refusesTab "- \t: a\n" 0 3
#guard refusesTab "-\t: a\n" 0 2
#guard refusesTab "- \t\t: a\n" 0 4
#guard refusesTab "-  \t: a\n" 0 4
#guard refusesTab "  - \t: a\n" 0 5
#guard refusesTab "---\n- \t: a\n" 1 3
-- The value may be absent, may be a flow collection, may be a block scalar —
-- the run in front of the `:` is decided before any of that is read.
#guard refusesTab "- \t:\n" 0 3
#guard refusesTab "- \t: [1]\n" 0 3
#guard refusesTab "- \t: |\n  a\n" 0 3
-- …and one level in, where the pending doing the refusing is itself compact.
#guard refusesTab "- - \t: a\n" 0 5
#guard refusesTab "- - - \t: a\n" 0 7
#guard refusesTab "- \t: a\n  : b\n" 0 3

/-! ## §2  The other two indicators, for the contrast

These have refused since items 31/32 — `scanBlockEntry` and `scanKey` read the
run with no simple-key question asked.  Pinning them beside §1 is the point:
after item 34 all three `[185]` openers answer alike, so the accumulator's tab
disjunct is `False` at a compact pending rather than "`c = ':'`". -/

#guard refusesTab "- \t- a\n" 0 3
#guard refusesTab "-\t- a\n" 0 2
#guard refusesTab "- \t? a\n" 0 3
#guard refusesTab "- \t?\n" 0 3
#guard refusesTab "? \t- a\n" 0 3
#guard refusesTab "? \t: a\n" 0 3
#guard refusesTab ": \t- a\n" 0 3
-- The same-line check ([194] has no same-line mapping, item 48) sits in
-- `scanValueValidate`, ahead of the value's own tab check — so the nested
-- `:` outranks the tab here.
#guard (match Events.streamToEvents ": \t: a\n", Events.streamToEventsIx ": \t: a\n" with
        | .error e, .error e' => e == .nestedMappingOnLine 0 3 && e' == e
        | _, _ => false)

/-! ## §3  The boundary: `[66] s-separate-in-line` is still a tab, and still legal

What §1 forbids is a tab in an `s-indent`, not a tab after an indicator.  Three
families of tab sit in a SEPARATION and are accepted, and each one is a place
where a blanket rule would have been wrong. -/

-- (a) In front of CONTENT: `[184]`'s entry reaches `s-l+block-node` through
--     `s-separate`, and `[66] s-white` admits a tab.
#guard emits "- \ta\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "-\ta\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "- \t\"a\"\n"
  ["+STR", "+DOC", "+SEQ", "=VAL \"a", "-SEQ", "-DOC", "-STR"]
#guard emits "- \t[1]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ", "-SEQ", "-DOC", "-STR"]

-- (b) Between an implicit KEY and its `:` — `[154] ns-s-implicit-yaml-key`'s
--     own trailing `s-separate-in-line?`.  This is the branch item 34 reasons
--     about, taken by a key that is genuinely in front of the colon: the run
--     the scan reads is the KEY's, and the key's own indentation is clean.
#guard emits "a\t: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "- a\t: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- \"k\"\t: v\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL \"k", "=VAL :v", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "- - a\t: 1\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ",
   "-SEQ", "-DOC", "-STR"]

-- (c) After the `:`, and inside a flow collection, where `[63]` is not the
--     reading at all.
#guard emits "- :\tb\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL :b", "-MAP", "-SEQ", "-DOC",
   "-STR"]
#guard emits "a:\t b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "{a\t: b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "- {a\t: b}\n"
  ["+STR", "+DOC", "+SEQ", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- [1,\t2]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-SEQ",
   "-DOC", "-STR"]

/-! ## §4  One rule, one error

The refusal is §6.1's `tabInIndentation`, reported at the tab's own line and
column, identically in both pipelines — which is what `refusesTab` checks above
and what these two spell out, one shape per family, so a downstream error that
happened to reject the same input would not pass for this one. -/

#guard (match Events.streamToEvents "- \t: a\n" with
        | .error (.tabInIndentation 0 3) => true
        | _ => false)
#guard (match Events.streamToEventsIx "- \t: a\n" with
        | .error (.tabInIndentation 0 3) => true
        | _ => false)

end Tests.Guards.ScannerCompactTabRefused

end Blanket
