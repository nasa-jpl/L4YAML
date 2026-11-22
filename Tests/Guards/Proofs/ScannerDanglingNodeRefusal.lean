module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
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

/-! # The dangling node run, refused at the scanner (DOCS item 133)

§9.2 `[211] l-yaml-stream` has no production for a node that belongs to nothing.
A trailing `[96]* (scalar|alias)?` run whose START sits at an OPEN indent
level's own column is exactly that shape: the level is already occupied by the
collection that opened it, so the run is neither that collection's next key nor
any indicator's content.  Item 119 measured the refusal as the parser's and
named the migration M2; this is the landing.

`scanNextToken_checkDanglingNode` runs BEFORE the structural dispatch — a
dangler dies at a `...`/`---` too, and the marker would otherwise consume the
step — and `scanLoop_checkDanglingNode` runs beside `scanLoop`'s other two final
validations, for the run the stream itself ends.  The mid-stream check takes TWO
states since item 140: the break off the landing, the RUN off the state the
landing arrived with, because preprocessing's unwind displaces the run from the
array it would otherwise be read in.  See
`Tests/Guards/Proofs/ScannerDanglingNodeDedent.lean`.

**What separates a dangler from a value is its PREDECESSOR**, and the three that
offer a slot are `YamlToken.offersNodeSlot`'s: `:`, `?` and `-`, whose own
productions are followed by `s-l+block-node`/`s-l+block-indented`.  So `a:⏎b` is
`{a: b}`, `?⏎b⏎: v` is the explicit key's content and `-⏎b` is the entry's,
while `a: 1⏎b` has a finished scalar behind it and no slot at all.

**The mid-stream check needs the break; the EOF one does not.**  A run still on
its own line may yet be resolved by a `:` (`a: 1⏎b: 2` — `b` becomes a key), and
`simpleKeyAllowed` is down there; at the end of input there is no `:` left to
come, so the flag is not asked for.  §2 pins both arms.

**The position reported is the RUN's start, not the cursor's** — that is where
the offending node begins, and where the parser reported.  §4 pins it.

§1 types the check and the four ways it stands aside.  §2 is the refused family.
§3 is the boundary.  §4 is the identity of the refusal.  §5 is the
discrimination from M1 and M3. -/

namespace L4YAML.Tests.Guards.ScannerDanglingNodeRefusal

open L4YAML L4YAML.Scanner

/-! ## §1  The check, and the four ways it stands aside -/

/-- Inside a flow collection there are no block levels to dangle at. -/
example (s : ScannerState) (h : s.inFlow = true) : danglingNodePos? s = none := by
  simp only [danglingNodePos?, h, ↓reduceIte]

/-- An array that does not end in a node run has no dangler in it. -/
example (s : ScannerState) (h : trailingNodeRun? s.tokens = none) :
    danglingNodePos? s = none := by
  unfold danglingNodePos?
  split
  · rfl
  · rw [h]

/-- A flow close ends no run: `]`/`}` are neither a node body nor a `[96]`
    property, which is what separates `isNodeBody` from `completesFlowValue`. -/
example : YamlToken.isNodeBody .flowSequenceEnd = false := rfl
example : YamlToken.isNodeBody .flowMappingEnd = false := rfl
example : YamlToken.completesFlowValue .flowSequenceEnd = true := rfl

/-- The three predecessors that OFFER the run a slot. -/
example : YamlToken.offersNodeSlot .value = true := rfl
example : YamlToken.offersNodeSlot .key = true := rfl
example : YamlToken.offersNodeSlot .blockEntry = true := rfl
example : YamlToken.offersNodeSlot (.scalar "x" .plain) = false := rfl
example : YamlToken.offersNodeSlot .flowSequenceEnd = false := rfl

/-- Mid-stream the break is required, and `simpleKeyAllowed` is it — read off
    the LANDING, which is the second of the check's two states (item 140). -/
example (s_run s_land : ScannerState) (h : s_land.simpleKeyAllowed = false) :
    scanNextToken_checkDanglingNode s_run s_land = .ok () := by
  simp only [scanNextToken_checkDanglingNode, h, Bool.false_eq_true, ↓reduceIte]

/-- At EOF it is not: the stream itself ended the run. -/
example (s : ScannerState) (p : YamlPos) (h : danglingNodePos? s = some p) :
    scanLoop_checkDanglingNode s = .error (.invalidBareDocument p.line p.col) := by
  simp only [scanLoop_checkDanglingNode, h]

/-! ## §2  The family the check refuses -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

/-- Both SCANNERS refuse, and so do both pipelines. -/
private def scannerRefuses (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .error _ => true
   | _, _ => false) &&
  (match Events.streamToEvents input, Events.streamToEventsIx input with
   | .error _, .error _ => true
   | _, _ => false)

-- The two arms: the run ended by the STREAM, and the run ended by a BREAK.
#guard scannerRefuses "a: 1\nb\n"          -- EOF
#guard scannerRefuses "a: 1\nb\nc: 2\n"    -- mid-stream

-- Every run shape, at a mapping's level.
#guard scannerRefuses "a: 1\n\"q\"\n"      -- quoted
#guard scannerRefuses "k: 1\n|\n  x\n"     -- block scalar (its `|` carries the column)
#guard scannerRefuses "k: 1\n|\n  x\nm: 2\n"
#guard scannerRefuses "a: &q 1\n*q\n"      -- alias
#guard scannerRefuses "a: 1\n&p b\n"       -- anchor + body
#guard scannerRefuses "a: 1\n&p\n"         -- anchor alone
#guard scannerRefuses "a: 1\n!t b\n"       -- tag + body
#guard scannerRefuses "a: 1\n!t\n"         -- tag alone
#guard scannerRefuses "a: 1\n&p !t b\n"    -- the full `[96]` run, either order
#guard scannerRefuses "a: 1\n!t &p b\n"

-- …and at a sequence's level, and after a flow close (the level survives it).
#guard scannerRefuses "- a\nb\n"
#guard scannerRefuses "- a\nb\n- c\n"
#guard scannerRefuses "- a\n\"q\"\n"
#guard scannerRefuses "k: [1, 2]\nb\n"
#guard scannerRefuses "- [1, 2]\nb\n"

-- Nested and dedented landings: the run's column has to be SOME open level's.
#guard scannerRefuses "a:\n  b: c\nd\n"
#guard scannerRefuses "a:\n  b: 1\n  c\n"
#guard scannerRefuses "a:\n  b:\n    c: 1\n  d\n"
#guard scannerRefuses "a:\n  b:\n    c: 1\nd\n"
#guard scannerRefuses "a:\n- x\ny\n"
#guard scannerRefuses "a:\n  - x\n  y\n"
#guard scannerRefuses "- - a\n  b\n"
#guard scannerRefuses "- - - a\n    b\n"
#guard scannerRefuses "a:\n  - b:\n      c: 1\n  d\n"

-- The explicit key's own content is a value; a SECOND run after it is not.
#guard scannerRefuses "? a\nb\n: c\n"
#guard scannerRefuses "? a\n: b\nc\n"

-- Comments and blank lines end a run without resolving it.
#guard scannerRefuses "a: 1\n# c\nb\n"
#guard scannerRefuses "a: 1\nb\n# c\n"
#guard scannerRefuses "a: 1\n\nb\n"

-- The dangler dies at a MARKER dispatch too — which is why the check runs
-- BEFORE the structural one.
#guard scannerRefuses "a: 1\nb\n...\n"
#guard scannerRefuses "a: 1\nb\n--- c\n"
#guard scannerRefuses "a: 1\n...\n- x\ny\n"

-- A block-scalar body flush with its key leaves the body a dangler of its own.
#guard scannerRefuses "k:\n  a: |\n  x\n"
#guard scannerRefuses "-\n  a: |\n  x\n"

/-! ## §3  The boundary the check must not cross

Items 177/178 MOVED this boundary: the three offered predecessors' equal-column
readings (`a:⏎b` = `{a: b}`, `?⏎b⏎: v`, `-⏎b`) were the slot exemption's own
over-acceptances — `s-separate(n+1)` cannot reach the level's column — and
they now refuse with the slot-less family's constructor and position; item 178
folded the `[96]`-headed runs in behind the same separator (`k:⏎&x a`,
`-⏎&x a`, `?⏎&x a⏎: v`).  What the exemption keeps is the one run shape
another reading owns (the props-less flow-close tail, item 172's floor), and
the boundary the check must not cross is the rest of this section: keys the
flag still allows, absorbed continuations, and every strictly deeper
landing. -/

-- The offered predecessors, at the equal column: refused as of items 177/178.
#guard scannerRefuses "a:\nb\n"
#guard scannerRefuses "?\nb\n: v\n"
#guard scannerRefuses "-\nb\n"
#guard scannerRefuses "a:\nb\nc: 2\n"
#guard scannerRefuses "a:\n&x b\n"
#guard scannerRefuses "?\n&x b\n: v\n"
#guard scannerRefuses "-\n&x b\n"
-- …and their strictly deeper twins stay the offered slot's own values.
#guard emits "a:\n b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "?\n b\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :b", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "-\n b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :b", "-SEQ", "-DOC", "-STR"]

-- A run still on its own line may yet become a key: the flag is down.
#guard accepts "a: 1\nb: 2\n"
#guard accepts "- a\n- b\n"
#guard accepts "a:\n- x\n- y\n"
#guard accepts "? a\n: b\n? c\n: d\n"

-- A plain scalar absorbs its own continuation lines, so it never dangles.
#guard accepts "hello\nworld\n"
#guard accepts "a: 1\n  2\n"
#guard accepts "a:\n  b\n  c\n"
#guard accepts "- a\n  b\n- c\n"
#guard accepts "a: >-\n  x\n  y\n"

-- Values of every shape, at their own indented columns.
#guard accepts "a: |\n  x\nb: 2\n"
#guard accepts "- |\n  x\n- y\n"
#guard accepts "a:\n  |\n  x\n"
#guard accepts "a: &x 1\nb: *x\n"
#guard accepts "- &x 1\n- *x\n"
#guard accepts "a: &p\n  b: 1\n"
#guard accepts "a: !t\n  b: 1\n"
#guard accepts "- &p\n  a: 1\n"
#guard accepts "a: {x: 1}\nb: 2\n"
#guard accepts "a:\n  b:\n    c: 1\nd: 2\n"

-- A root node pushes no level, so nothing at column 0 is at an OPEN one.
#guard accepts "hello\n"
#guard accepts "[1, 2]\n"
#guard accepts "&p 1\n"
#guard accepts "&p\nc: 2\n"
#guard accepts "&a x\n*a\n"
#guard accepts "--- a\nb\n"

-- A `...` or a `---` gives the next run a document of its own.
#guard accepts "a: 1\n...\nb\n"
#guard accepts "a: 1\n--- b\n"
#guard accepts "a: 1\n...\n"

-- Flow interiors are exempt outright.
#guard accepts "[a,\nb]\n"
#guard accepts "{a: 1,\nb: 2}\n"
#guard accepts "- [1,\n 2]\n"

-- Empty and comment-only streams.
#guard accepts "\n"
#guard accepts "# c\n"
#guard accepts "a:\n"

/-! ## §4  The refusal is the SCANNER's, and it names the RUN -/

private def scanErr (input : String) : Option String :=
  match Scanner.scan input with | .error e => some (toString e) | .ok _ => none

private def scanErrIx (input : String) : Option String :=
  match Indexed.ScannerStateIx.scanIx input with
  | .error e => some (toString e) | .ok _ => none

private def pipeErr (input : String) : Option String :=
  match Events.streamToEvents input with | .error e => some (toString e) | .ok _ => none

private def pipeErrIx (input : String) : Option String :=
  match Events.streamToEventsIx input with | .error e => some (toString e) | .ok _ => none

/-- One message, at one position, from all four. -/
private def saysAlike (input : String) (line col : Nat) : Bool :=
  let m := some (toString (ScanError.invalidBareDocument line col))
  scanErr input == m && scanErrIx input == m
    && pipeErr input == m && pipeErrIx input == m

-- The position is the RUN's start.  In the first, the check fires at the
-- dispatch of `c` on line 2 and still reports line 1; in the second, at the
-- end of input, three lines past the `|` it names.
#guard saysAlike "a: 1\nb\nc: 2\n" 1 0
#guard saysAlike "k:\n  a: 1\n|\n  x\n" 2 0
#guard saysAlike "a: 1\nb\n" 1 0
#guard saysAlike "- a\nb\n" 1 0
#guard saysAlike "a: 1\n&p b\n" 1 0      -- the RUN's start, not the scalar's
#guard saysAlike "a: 1\n&p !t b\n" 1 0
#guard saysAlike "a:\n  b: 1\n  c\n" 2 2
#guard saysAlike "- - a\n  b\n" 1 2
#guard saysAlike "a: 1\nb\n...\n" 1 0

/-! ## §5  The discrimination from M1 and M3

    M1 (`ScannerBareDocumentRefusal`) is the completed ROOT document, where the
    indent stack is the sentinel alone; M2 is a run at an OPEN level's column.
    The two never overlap, because a column is a `Nat` and the sentinel's is
    `-1`.  M3 — the `-` at a mapping top's own column with the entry complete —
    landed at item 134, and this check stands aside on its whole family for the
    reason §1 gives: the trailing run's PREDECESSOR offers it a slot (`k` is the
    explicit key's content, `1` is `a`'s value), so nothing is dangling.  What
    has no slot is the `-` in front of it, and that is
    `scanBlockEntryValidate`'s question, not this one's. -/

-- M1's family: the root, refused by the OTHER check, at the node's own column.
#guard saysAlike "[1, 2]\na\n" 1 0
#guard saysAlike "\"x\"\na\n" 1 0
-- M3's family: the same message, at the `-`, from all four layers — and the
-- slot-offering predecessor that keeps THIS check out of it.
#guard saysAlike "a: 1\n- y\n" 1 0
#guard saysAlike "? k\n- y\n" 1 0
#guard saysAlike ": v\n- y\n" 1 0

end L4YAML.Tests.Guards.ScannerDanglingNodeRefusal

end Blanket
