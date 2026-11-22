module

public import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Scanner.IndexedDispatch
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

/-! # The `-` at a block mapping's own column (DOCS item 134)

§9.2 `[211] l-yaml-stream` admits a bare document only as the stream's first or
after a `...`.  A `-` at a column strictly right of the enclosing collection
opens a sequence — `pushSequenceIndent`'s guard is `col > currentIndent`.  A `-`
at a MAPPING's own column opens nothing, and is legal only where a NODE is
expected: `[183] l+block-sequence(n)` is reached from `[185]
s-l+block-indented(n,c)` with the auto-detected `m` allowed to be 0, so a
zero-indented sequence stands exactly in a node's slot.  Item 119 measured the
refusal as the parser's and named the migration M3; this is the landing.

**Two things expect a node**, and `scanBlockEntryValidate` is their disjunction:

* the slot the previous indicator opened is still empty — `:` awaiting its
  value, `?` awaiting its key, `-` awaiting its entry, with at most a `[96]`
  property run standing in between.  That is item 133's own
  `YamlToken.offersNodeSlot`, read past the run by `slotHolderIdx?`;
* a zero-indented sequence at this very column is already open and this is its
  next entry — `sameIndentSequenceOpen`.

**M3 is the one mechanism whose test is a BACKWARD WALK.**  The entries of a
zero-indented sequence are separated from one another by every token of the
collections nested inside them (`a:⏎- k: 1⏎  m: 2⏎- y`), so "is this sequence
still open?" cannot be read off the array's tail.  The walk is bounded on the
other side by the mapping level's own opener: `pushMappingIndent` runs at the
column of a `.key`, or of the `.value` that opens a keyless entry, so a
`.key`/`.value` at a column ≤ this one is always reached, and everything behind
it belongs to a collection this `-` cannot continue.

§1 types the check and the three ways it stands aside.  §2 is the family item
119 mapped.  §3 is a family it did NOT map — a `-` at the column of a mapping
COMPACT IN A SEQUENCE ENTRY, which both pipelines ACCEPTED, and which PyYAML
and libyaml both reject.  §4 is the boundary the check must not cross.  §5 is
the discrimination from M1, M2 and §8.2.1's `?` twin. -/

namespace L4YAML.Tests.Guards.ScannerBlockEntryMappingIndent

open L4YAML L4YAML.Scanner

/-! ## §1  The check, and the three ways it stands aside -/

/-- A column that is not the top level's is no mapping's own column. -/
example (s : ScannerState) (h : atMappingIndent s = false) :
    scanBlockEntryValidate s = .ok () := by
  simp only [scanBlockEntryValidate, h, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- A slot still open takes the `-`'s sequence as its node. -/
example (s : ScannerState) (h : nodeSlotAwaited s.tokens = true) :
    scanBlockEntryValidate s = .ok () := by
  simp only [scanBlockEntryValidate, h, Bool.not_true, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- A same-indent sequence already open takes it as its next entry. -/
example (s : ScannerState) (h : sameIndentSequenceOpen s.tokens (s.col : Int) = true) :
    scanBlockEntryValidate s = .ok () := by
  simp only [scanBlockEntryValidate, h, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

/-- Otherwise it is §9.2's, reported at the `-` itself. -/
example (s : ScannerState) (h1 : atMappingIndent s = true)
    (h2 : nodeSlotAwaited s.tokens = false)
    (h3 : sameIndentSequenceOpen s.tokens (s.col : Int) = false) :
    scanBlockEntryValidate s = .error (.invalidBareDocument s.line s.col) := by
  simp only [scanBlockEntryValidate, h1, h2, h3, Bool.not_false, Bool.and_true,
    ↓reduceIte]

/-- The three indicators that offer the `-`'s sequence a slot — item 133's
    predicate, reused because it is the same question. -/
example : YamlToken.offersNodeSlot .value = true := rfl
example : YamlToken.offersNodeSlot .key = true := rfl
example : YamlToken.offersNodeSlot .blockEntry = true := rfl
example : YamlToken.offersNodeSlot (.scalar "x" .plain) = false := rfl

/-- `atMappingIndent` and `atSequenceIndent` are exclusive: both read the
    stack's top, and it is one kind or the other. -/
example (s : ScannerState) (h : atSequenceIndent s = true) :
    atMappingIndent s = false := by
  unfold atSequenceIndent atMappingIndent at *
  cases hb : s.indents.back? with
  | none => rfl
  | some top =>
    rw [hb] at h
    simp only [Bool.and_eq_true] at h
    simp only [h.1, Bool.not_true, Bool.false_and]

/-- The backward walk's base: an empty prefix opens no sequence. -/
example (ts : Array (Positioned YamlToken)) (c : Int) :
    sameIndentSequenceOpenLoop ts c 0 = false := rfl

/-! ## §2  The family item 119 mapped

    Its seven pins, and the shapes around them.  Every one is reported at the
    `-`'s own line and column — which is where the PARSER reported, so the
    migration is byte-invisible to the matrix and to `eventscore`. -/

private def scanErr (input : String) : Option String :=
  match Scanner.scan input with | .error e => some (toString e) | .ok _ => none

private def scanErrIx (input : String) : Option String :=
  match Indexed.ScannerStateIx.scanIx input with
  | .error e => some (toString e) | .ok _ => none

private def pipeErr (input : String) : Option String :=
  match Events.streamToEvents input with | .error e => some (toString e) | .ok _ => none

private def pipeErrIx (input : String) : Option String :=
  match Events.streamToEventsIx input with | .error e => some (toString e) | .ok _ => none

/-- One message, at one position, from both scanners AND both pipelines. -/
private def saysAlike (input : String) (line col : Nat) : Bool :=
  let m := some (toString (ScanError.invalidBareDocument line col))
  scanErr input == m && scanErrIx input == m
    && pipeErr input == m && pipeErrIx input == m

-- Item 119's seven §4 pins.
#guard saysAlike "a: 1\n- y\n" 1 0
#guard saysAlike "a: 1\n- y\nb: 2\n" 1 0
#guard saysAlike "? k\n- y\n" 1 0
#guard saysAlike "? k\n- y\n: v\n" 1 0
#guard saysAlike ": v\n- y\n" 1 0
#guard saysAlike "a:\n  b:\n  - x\n- y\n" 3 0
#guard saysAlike "a:\n- x\nb: 1\n- y\n" 3 0

-- Every way the entry can be complete: a plain value, a flow one, a quoted
-- one, a block scalar, a second entry, an explicit entry.
#guard saysAlike "a: 1\nb: 2\n- y\n" 2 0
#guard saysAlike "a: [1, 2]\n- y\n" 1 0
#guard saysAlike "a: \"q\"\n- y\n" 1 0
#guard saysAlike "a: |\n  t\n- y\n" 2 0
#guard saysAlike "? k\n: v\n- y\n" 2 0

-- Every shape the `-` itself can take: bare, with a compact mapping, with a
-- property run of its own.
#guard saysAlike "a: 1\n-\n" 1 0
#guard saysAlike "a: 1\n- k: 1\n" 1 0
#guard saysAlike "a: 1\n- &p y\n" 1 0

-- Nested and explicit-document landings — the column is the TOP level's,
-- whatever the depth and whatever opened the document.
#guard saysAlike "top:\n  a: 1\n  - y\n" 2 2
#guard saysAlike "? big\n:\n  a: 1\n  - y\n" 3 2
#guard saysAlike "---\na: 1\n- y\n" 2 0
#guard saysAlike "%YAML 1.2\n---\na: 1\n- y\n" 3 0

/-! ## §3  The family item 119 did NOT map

    A mapping COMPACT IN A SEQUENCE ENTRY (`[185] s-l+block-indented`) has its
    own column too, and a `-` there is the same shape for the same reason.  The
    map never recorded these because both pipelines ACCEPTED them — emitting a
    spurious empty second document for the tokens after the mapping ends — and
    the map's `parserGap` predicate only collects what the parser refuses.
    PyYAML and libyaml reject every one, and the check closes them with the
    rest: verdict CHANGED here, from accept to refuse. -/

#guard saysAlike "- a: 1\n  - y\n" 1 2
#guard saysAlike "- ? k\n  - y\n" 1 2
#guard saysAlike "- : v\n  - y\n" 1 2
#guard saysAlike "- a: 1\n  b: 2\n  - y\n" 2 2
#guard saysAlike "- a:\n    b: 1\n  - y\n" 2 2
#guard saysAlike "- a: [1, 2]\n  - y\n" 1 2
#guard saysAlike "- a: |\n    t\n  - y\n" 2 2
#guard saysAlike "- a: 1\n  ? k\n  : v\n  - y\n" 3 2

/-! ## §4  The boundary the check must not cross -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

-- The awaited value, with and without a `[96]` run in front of the sequence.
#guard emits "a:\n- y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :y", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard accepts "a:\n- y\nb: 2\n"
#guard emits "a: &x\n- y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ &x", "=VAL :y", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard accepts "a: !!seq\n- y\n"
#guard accepts "? k\n:\n- y\n"

-- The awaited KEY: suite 6PBE, a zero-indented sequence as an explicit key.
-- `?` offers a slot exactly as `:` does, which is why `offersNodeSlot` and not
-- "the last token is `.value`" is the test.
#guard emits "---\n?\n- a\n- b\n:\n- c\n- d\n"
  ["+STR", "+DOC ---", "+MAP", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ",
   "+SEQ", "=VAL :c", "=VAL :d", "-SEQ", "-MAP", "-DOC", "-STR"]

-- The continuing same-indent sequence — including the nested collections the
-- backward walk has to survive, and the level pops they bring with them.
#guard accepts "a:\n- x\n- y\n"
#guard emits "a:\n- k: 1\n- y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "+MAP", "=VAL :k", "=VAL :1",
   "-MAP", "=VAL :y", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard accepts "a:\n- k: 1\n  m: 2\n- y\n"
#guard emits "a:\n- m:\n    - x\n- y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "+MAP", "=VAL :m", "+SEQ",
   "=VAL :x", "-SEQ", "-MAP", "=VAL :y", "-SEQ", "-MAP", "-DOC", "-STR"]

-- A NEW awaited value re-opens the slot: `b:` ends the first sequence and the
-- next `-` is the second one's first entry, not a continuation.
#guard emits "a:\n- x\nb:\n- y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :x", "-SEQ", "=VAL :b",
   "+SEQ", "=VAL :y", "-SEQ", "-MAP", "-DOC", "-STR"]

-- The compact mapping's own legal twins — §3's family with the value AWAITED.
#guard accepts "- a:\n  - y\n"
#guard accepts "- a:\n  - x\n  - y\n"

-- An INDENTED sequence is a different column and never reaches the check.
#guard accepts "a:\n  - x\n  - y\n"
#guard accepts "a:\n- x\n  - y\n"

-- A sequence's own column is `atSequenceIndent`'s, not this check's.  The
-- equal-column entry value refuses as of item 177 (Finding A's floor,
-- `invalidBareDocument` at the run) — still not this check's constructor.
#guard accepts "- a\n- b\n"
#guard saysAlike "-\nb\n" 1 0

-- `?` and `:` at the mapping's column open new ENTRIES: M3 is `-` alone.
#guard emits "a: 1\n? k\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :k", "=VAL :v",
   "-MAP", "-DOC", "-STR"]
#guard emits "a: 1\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :", "=VAL :v",
   "-MAP", "-DOC", "-STR"]

-- Flow context has no block levels for the `-` to stand at.
#guard accepts "a: [1, -2]\n"
#guard accepts "{a: 1, b: -2}\n"

/-! ## §5  The discrimination from M1, M2 and the `?` twin

    M1 (`ScannerBareDocumentRefusal`) needs the indent stack at its sentinel
    alone; M3 needs a MAPPING level at the cursor's column, and a `Nat` is
    never `-1`, so they never overlap.  M2 (`ScannerDanglingNodeRefusal`) reads
    the array's TAIL for an unresolved node run; on M3's whole family that run's
    predecessor offers it a slot, so M2 stands aside — what has no slot is the
    `-` in front of it.  And §8.2.1's `atSequenceIndent` (item 131) is the
    OTHER indicator at the OTHER kind of level: a `?` at a sequence's own
    column, refused as `trailingContent`.  These pin the three boundaries by
    the message each mechanism produces. -/

private def refusesWith (input : String) (e : ScanError) : Bool :=
  (match Scanner.scan input with
   | .error e' => toString e' == toString e | .ok _ => false) &&
  (match Indexed.ScannerStateIx.scanIx input with
   | .error e' => toString e' == toString e | .ok _ => false)

-- M1's: the completed ROOT document, at the sentinel.
#guard refusesWith "[1, 2]\na\n" (.invalidBareDocument 1 0)
-- M2's: the dangling RUN, reported at the run's start.
#guard refusesWith "a: 1\n&p b\n" (.invalidBareDocument 1 0)
-- M3's: the `-`, reported at the `-`.
#guard refusesWith "a: 1\n- y\n" (.invalidBareDocument 1 0)
-- Item 131's `?` at a SEQUENCE's own column — a different error entirely.
#guard refusesWith "- a\n? k\n: v\n" (.trailingContent 1 0)

end L4YAML.Tests.Guards.ScannerBlockEntryMappingIndent

end Blanket
