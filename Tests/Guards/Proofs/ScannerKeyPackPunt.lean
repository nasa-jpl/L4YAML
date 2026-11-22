module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # What the entry key pack punts on, and where each one is answered (DOCS item 65)

`entryKeyPack_of_dispatch` used to hand `True` for every shape it could not
read back as `[193]`/`[194]`'s implicit key, so the `:` step that consumes the
pack could not tell one from another and deferred on all of them.  Item 65
replaces that `True` with `KeyPackPunt`'s five named reasons and spends the one
that is the `:`'s own.  Everything below is RUNTIME behavior — none of it
changed at this item; the pins say what the proof's new case split has to be
consistent with.  They pin the SHAPES the reasons name and how the scanner
answers them, not which arm a given input takes: an escape is silent, so no
runtime observation can say that.

* §1 **the tab is the `:`'s to refuse, not preprocessing's.**  A tab in the
  whitespace in front of a KEY sits past `currentIndent`, so §6.1's
  preprocessing gate lets it through and the same run reads fine in front of a
  VALUE.  What refuses `k:⏎␣→a: 1` is `scanValueIndentTabCheck`, one step
  later, walking back from `simpleKey.pos` — which is exactly the reading
  `KeyPackPunt.tab` carries.  The error's own line and column name the KEY, not
  the `:`.
* §2 **and the tab in front of a `:` is legal**, because `[154]`'s trailing
  `s-separate-in-line?` admits `s-white`: only the run in front of the ENTRY is
  `[63] s-indent`.  This is the boundary the refutation must not cross.
* §3 **the key HEAD was never what was missing.**  A block scalar is a node and
  never a key, and the scanner says so by clearing the saved key — the `:` after
  `k: |⏎  x` opens a SECOND entry with an empty key rather than resolving the
  scalar.  An alias IS a key wherever a park offers one.
* §4 **the reasons that remain are claims, not formalities.**  `dedent` and
  ~~`noFrame`~~ each name a shape the scanner ACCEPTS, so the deferral they ride
  is carrying real inputs — row 19's frame stack and item 51's explicit-entry
  threading respectively.  (`noFrame`'s shape is `- ? a: b`, not the
  `? a⏎: b: c` pinned below — item 105's correction; the landed `:` pays its
  own slot and the COMPACT `?` was the one that did not.)
  **Half of `noFrame` did not** — struck 2026-09-06 by
  item 101, which read the two pins below against each other: `? a⏎: b: c` is
  accepted and `k: a: 1` is refused, so one name was covering two reasons.  The
  refused half is `[189]`'s IMPLICIT value, whose indicator stamped its line;
  it is now `KeyPackPunt.implicitValue` and it is REFUTED at the same place the
  tab is.  See `ScannerImplicitValueSameLineKey`.  **And half of `noKeyContext`
  did not either** — struck 2026-09-06 by item 103, which read the same pair one
  construct over: `k: [1]: 2` is refused where `[1]: 2` is accepted, so a flow
  close in a stamped value slot was riding the CALLER's name for the INPUT's
  reason.  It hands `implicitValue` now, carried across the whole collection on
  the mask's base slot; see `ScannerFlowCloseSameLineKey`.  What keeps the name
  is a frame with no route at all, and its complement is what is pinnable: where
  item 56's frame does carry a route, the closed flow collection reads as
  `[194]`'s JSON key.
* §5 **the phantom question, asked where the reason is BUILT** (item 211).
  Item 184 recorded `noKeyContext` as having no named input, "which by R646 is
  the signature of a branch that may be a phantom", and the note rode
  twenty-two NEXT lists unexamined.  `lake run punt-price -- reaches`
  asks it at the production instead:
  `content_dispatch_routed` reaches the punt only when FIVE optional contexts
  decline at once, and of its eight applications exactly ONE does — the `---`
  park's mid-line dispatch — while SEVEN relay their own `h_keyctx` to their
  callers.  The one that declines is the park whose implicit-key class the
  scanner refuses outright, which is what the rows below pin.  At
  `flowKeyPack_of_close` the question moves down a construct again: both
  callers pay with `close_col_of_base` and `resume.key`, and each of those
  carries the same `∨ True`.  So the doubt was right and its reason was not —
  the branch is not missing an input, it is behind a RELAY. -/

namespace L4YAML.Tests.Guards.ScannerKeyPackPunt

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The same run, twice: a VALUE reads over it and a KEY does not.
#guard emits "k:\n \ta\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  \ta\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "-MAP", "-DOC", "-STR"]
#guard refuses "k:\n \ta: 1\n"
#guard refuses "k:\n  \ta: 1\n"
-- …and the same in a COMPACT entry, where the run is `[185]`'s `s-indent(m)`.
#guard refuses "- \ta: 1\n"
-- The reported position is the KEY's, which is how the check's key branch is
-- told apart from its cursor branch: the `:` sits at column 4 and `a` at
-- column 2, and it is `a`'s that comes back.
private def tabAt (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input with
  | .error (.tabInIndentation l c) => some (l, c)
  | _ => none

#guard tabAt "k:\n \ta: 1\n" == some (1, 2)
#guard tabAt "k:\n  \ta: 1\n" == some (1, 3)
#guard tabAt "- \ta: 1\n" == some (0, 3)

-- §2 The boundary the refutation must not cross: `[154]`'s own trailing
-- `s-separate-in-line?` admits a tab, so only the ENTRY's run is `[63]`.
#guard emits "a\t: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]

-- §3 The head is total.  A block scalar never resolves as a key — the `:`
-- below it opens a second entry whose key is `e-node` …
#guard emits "k: |\n  x\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL |x\\n", "=VAL :", "=VAL :v", "-MAP",
   "-DOC", "-STR"]
-- … and an alias IS one wherever a park offers a frame.
#guard emits "- &x v\n- *x : b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &x :v", "+MAP", "=ALI *x", "=VAL :b", "-MAP",
   "-SEQ", "-DOC", "-STR"]
-- At the document root the same alias key is the SCANNER's refusal, not a
-- missing production.
#guard refuses "&x v\n*x : b\n"

-- §4 The surviving reasons.
-- `dedent` — the landing under-ran the pending's index (item 64's boundary).
#guard emits "k:\n  :\nj: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL :j", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- ~~`noFrame` — the key is on the park's own line and the park owns no compact
-- alternative: `[192]`'s explicit entry, whose value is a compact mapping.
-- This is what the name covers after item 101's split.~~  Not this input,
-- corrected 2026-09-06 by item 105: the landed `:` re-parks through
-- `colon_open_map_explicit`, which pays the slot, so the pin below is a
-- BOUNDARY the reason must not claim.  The park that reached `noFrame` is the
-- COMPACT `?` one line over — `- ? a: b`, whose producer paid neither field —
-- and it is pinned in `ScannerCompactExplicitKey`.
#guard emits "? a\n: b: c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :c", "-MAP",
   "-MAP", "-DOC", "-STR"]
#guard emits "- ? a: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP",
   "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]
-- …and its implicit sibling, which the scanner refuses (§8.2.2 [194]) — the
-- other half, `KeyPackPunt.implicitValue` since item 101, refuted rather than
-- deferred.  The family is pinned in `ScannerImplicitValueSameLineKey`.
#guard refuses "k: a: 1\n"
-- `noKeyContext`'s complement — a closed flow collection as `[194]`'s JSON
-- key, at the two frames item 56 gave routes and at the mapping form.  What
-- the constructor covers after item 103 is a frame with no route at all AND no
-- stamp, which is a fact about the pending and not about any input.
#guard emits "[1] : b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
#guard emits "- [1] : b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "{a: 1} : b\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :a", "=VAL :1", "-MAP", "=VAL :b",
   "-MAP", "-DOC", "-STR"]

-- §5 The one application that declines every context is the `---` park's, and
-- the class it would need is refused by the scanner: the marker's OWN line
-- takes no implicit key (item 43), while the landed line after it does (item
-- 137).  Both halves are pinned, because only the pair says the branch is
-- narrow rather than empty.
private def docStartRefusal (input : String) : Option (Nat × Nat) :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error (.contentOnDocumentStartLine l c),
    .error (.contentOnDocumentStartLine l' c') =>
      if l == l' && c == c' then some (l, c) else none
  | _, _ => none

#guard emits "--- a\n" ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
#guard docStartRefusal "--- a: 1\n" == some (0, 5)
-- and the spaced form the deferral would have had to carry too (item 43)
#guard docStartRefusal "--- a : b\n" == some (0, 6)
-- the landed line, where the marker's mapping route IS paid
#guard emits "---\na: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- The refusal is the document-start line's, not the key's: move the same key
-- one document on and it reads.
#guard docStartRefusal "a: 1\n" == none

end L4YAML.Tests.Guards.ScannerKeyPackPunt

end Blanket
