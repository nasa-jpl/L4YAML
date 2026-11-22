module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The raised-flag refusal map (DOCS item 119)

The tightening's last prerequisite (items 110/116–118) reads: where
`documentEverStarted` is up and no suffix intervened, every input the
fallback `.bare` sites still serve must be scanner-refused.  This item
MEASURED that sentence instead of building on it, and the measurement
repriced it:

**The §9.2 refusal lives in the parser, not the scanner.**  Every family
below scans clean in BOTH pipelines and dies downstream in
`parseStreamLoop` (`StreamState.validNextToken`,
`Parser/TokenParser.lean`) or the emitters' twins — as
`invalidBareDocument`, "expected '---' or '...' before new document".
So the refusal half is a runtime MIGRATION — the scanner must learn the
check — and it decomposes into exactly three mechanisms, each validated
here against the runtime's own verdicts:

* **M1 — the completed root document** (§2): block context, the indent
  stack at its sentinel alone, the last real token a flow close or a
  scalar of any style, and a line break crossed since its end.  Placed
  after the structural dispatch, so `---`/`...`/directives stay legal.
  Same-line junk is already refused (`validateFlowClose`,
  `validateTrailingContent` — §5); a root plain scalar completes only
  where its walk stops (a comment line), and the alias-as-root case is
  unreachable (`undefinedAlias` fires first).
  **LANDED** as `scanNextToken_checkBareDocument` (item 132), so §2's pins
  are `scannerRefuses` now — `ScannerBareDocumentRefusal` carries the
  mechanism's own boundary.  The break condition is read off
  `simpleKeyAllowed` rather than off the completing token's position: a
  scalar's `endPos` is not populated, so a line test on the TOKEN reads a
  multi-line scalar's START.
* **M2 — the dangling node run at an open level's column** (§3): a
  trailing token run `[anchor|tag]* (scalar|alias)?` whose start sits at
  an open indent level's exact column, whose structural predecessor is
  NOT `.value`/`.key`/`.blockEntry`, with a break crossed (or EOF, in
  `scanLoop`).  The three exempt predecessors are the equal-column value
  readings the pipeline ACCEPTS — `a:⏎b` = `{a: b}`, `?⏎b⏎: v`,
  `-⏎b` — pinned in §6.
  **LANDED** as `scanNextToken_checkDanglingNode` and its EOF twin
  `scanLoop_checkDanglingNode` (item 133), so §3's pins are
  `scannerRefuses` now — `ScannerDanglingNodeRefusal` carries the
  mechanism's own boundary.  The exempt predecessors are
  `YamlToken.offersNodeSlot`; the position reported is the RUN's start,
  which is where the parser reported.
* **M3 — the `-` at a mapping top's own column** (§4): valid iff a node
  is still awaited (the last real token, read past a `[96]` run, is one
  of `YamlToken.offersNodeSlot`'s) or a same-indent sequence is
  continuing (a `.blockEntry` at this column stands before any
  `.key`/`.value` at a column ≤ it, walking the array BACKWARD);
  otherwise refused.  `?` and `:` at the column open new entries and
  stay legal (§6).  **LANDED** as `scanBlockEntryValidate` (item 134),
  so §4's pins are `scannerRefuses` now, and
  `ScannerBlockEntryMappingIndent` carries the mechanism's own boundary
  — including the family this map did NOT record, a `-` at the column of
  a mapping COMPACT IN A SEQUENCE ENTRY (`- a: 1⏎␣␣- y`), which both
  pipelines ACCEPTED and which the check also closes.

All three reuse `.invalidBareDocument`; on every probed input the
parser's message AND position are what the scanner check would produce,
so the migration is byte-invisible to the matrix and eventscore.  Item 132
confirmed that for M1 by running its condition over the whole suite before
editing the runtime: two tests reach it (BS4K, KS4U), both error tests,
both with the identical message and position.

**The price, measured (and why this landed as a map, not a build).**
The emitter-scannability trees re-verify the scanning of emitted output
through `scanNextToken`'s decomposition: the `scanNextToken_via_*`
composition lemmas have ~105 call sites across ~20 files in the two
trees, the `dispatchStructural`-shape facts ~145 references, and
`scanBlockEntry` 276 references.  Every placement of a new refusal —
a new bind in `scanNextToken`'s chain, a throw inside
`dispatchStructural`, or one inside `scanBlockEntry` — lands its
discharge burden on one of those ladders, a 100+-site absorption PER
MECHANISM.  So the refusal half is at least three items (one mechanism
plus its absorption each), not one, and this guard pins today's
verdicts so each landing flips its section loudly and intentionally.
M1's absorption, measured by building it and counting what the
compiler asked for: **41** extra `split`s across **24** files that
decompose `scanNextToken`/`scanNextTokenIx`, and **56** discharges across
**17** files on the `via_*` ladder — which cost one ARGUMENT each rather
than a proof, because those lemmas take the checks as premises and the
converse extractor reads the new one off an `.ok` witness the site
already holds.  So the "100+-site absorption per mechanism" above is the
right order of magnitude and the right shape; what it is not is 100 sites
of REASONING.  M2's (item 133) is 63 + 84, and the difference is the
PLACEMENT: a bind before the structural dispatch lands in the preprocess
arm of every chain decomposition, `scanLoop` included, while one after it
is reached through a single `split`.

§2–§4 pin what WAS the gap (`parserGap`: both scanners accept, both
pipelines refuse) and is now `scannerRefuses` throughout, the class
itself pinned empty at the end of §4; §5 the neighbors the scanner
already refused; §6 the valid boundary each mechanism must not cross. -/

namespace L4YAML.Tests.Guards.ScannerRaisedFlagRefusalMap

open L4YAML L4YAML.Scanner

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

/-- Both pipelines refuse. -/
private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-- Both pipelines accept (event shape not pinned). -/
private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

/-- Both SCANNERS accept the input outright. -/
private def scansClean (input : String) : Bool :=
  match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
  | .ok _, .ok _ => true
  | _, _ => false

/-- THE GAP: the scanner accepts what the parser refuses (§9.2).  Every
    pin below is an input the tightening needs the SCANNER to refuse. -/
private def parserGap (input : String) : Bool :=
  scansClean input && refuses input

/-- The neighbors already refused at the scanner itself. -/
private def scannerRefuses (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .error _ => true
   | _, _ => false) && refuses input

-- §2 M1 — the completed root document, then content on a later line.
-- Flow close at the root:
#guard scannerRefuses "[1, 2]\na\n"
#guard scannerRefuses "[1, 2]\n[3]\n"
#guard scannerRefuses "[1, 2]\na: 1\n"
#guard scannerRefuses "[1, 2]\n- y\n"
#guard scannerRefuses "[1, 2]\n? k\n"
#guard scannerRefuses "[1, 2]\n: v\n"
#guard scannerRefuses "[1, 2]\n|\n  x\n"
#guard scannerRefuses "[1, 2]\n\"q\"\n"
#guard scannerRefuses "[1, 2]\n&p a\n"
#guard scannerRefuses "[1, 2]\n!t x\n"
#guard scannerRefuses "{a: b}\nx\n"
#guard scannerRefuses "[1, 2] # c\na\n"
#guard scannerRefuses "[1, 2]\n  a\n"
#guard scannerRefuses "[1,\n 2]\na\n"
-- Quoted scalar at the root:
#guard scannerRefuses "\"x\"\na\n"
#guard scannerRefuses "\"x\"\na: 1\n"
#guard scannerRefuses "\"x\"\n: v\n"
#guard scannerRefuses "\"x\"\n[1]\n"
#guard scannerRefuses "\"x\"\n\"y\"\n"
#guard scannerRefuses "\"x\"\n  a\n"
#guard scannerRefuses "\"x\"\n? k\n: v\n"
-- Block scalar at the root (the landing IS the later line):
#guard scannerRefuses "|\n  x\na\n"
#guard scannerRefuses "|\n  x\nb: 2\n"
#guard scannerRefuses "|\n  x\n- y\n"
#guard scannerRefuses "|\n  x\n[1]\n"
#guard scannerRefuses "|\n  x\n: v\n"
#guard scannerRefuses "|2\n  x\na\n"
-- Plain scalar at the root: the walk absorbs continuation lines, so the
-- completed-scalar state is reachable only where the walk stops — a
-- comment line.  (`hello⏎world` is ONE scalar; §6.)
#guard scannerRefuses "hello\n# c\nworld\n"
#guard scannerRefuses "hello\n# c\nw: 1\n"
#guard scannerRefuses "hello\n# c\n: v\n"
-- The explicit-document twins (`---` pushes no indent level).  The first
-- is M2's, not M1's: `a: 1` opens a mapping level at column 0, so the
-- dangling `b` sits at an OPEN level rather than at the sentinel, and M1's
-- check does not fire on it.  Both mechanisms have landed, so both refuse.
#guard scannerRefuses "---\na: 1\nb\n"
#guard scannerRefuses "--- [1]\nx\n"
#guard scannerRefuses "--- |\n  q\nx\n"
#guard scannerRefuses "--- \"x\"\na\n"

-- §3 M2 — the dangling node run at an open level's column.  LANDED
-- (item 133): every pin below is `scannerRefuses` now.
-- Plain danglers at a mapping's column (mid-stream and EOF deaths):
#guard scannerRefuses "a: 1\nb\n"
#guard scannerRefuses "a: 1\nb\nc: 2\n"
#guard scannerRefuses "a: 1\n\"q\"\n"
#guard scannerRefuses "a:\n  b: c\nd\n"
#guard scannerRefuses "a:\nb\nc\n"
-- ...at a sequence's column:
#guard scannerRefuses "- a\nb\n"
#guard scannerRefuses "- a\nb\n- c\n"
#guard scannerRefuses "- a\n\"q\"\n"
-- ...after a completed flow value (the level survives the close):
#guard scannerRefuses "k: [1, 2]\nb\n"
#guard scannerRefuses "- [1, 2]\nb\n"
-- Property-run and alias danglers (the run's START carries the column):
#guard scannerRefuses "x: &q 1\n*q\n"
#guard scannerRefuses "x: &q 1\n*q\ny: 2\n"
#guard scannerRefuses "a: 1\n&p b\n"
#guard scannerRefuses "a: 1\n&p b\nc: 2\n"
#guard scannerRefuses "a: 1\n&p\n"
#guard scannerRefuses "a: 1\n&p\nc: 2\n"
-- Block-scalar danglers at a level's column:
#guard scannerRefuses "k: 1\n|\n  x\n"
#guard scannerRefuses "k: 1\n|\n  x\nm: 2\n"
#guard scannerRefuses "k:\n  a: 1\n|\n  x\n"
-- The dangler dies at a MARKER dispatch too, so the check precedes the
-- structural dispatch:
#guard scannerRefuses "a: 1\nb\n...\n"
#guard scannerRefuses "a: 1\nb\n--- c\n"

-- §4 M3 — the `-` at a mapping top's own column, entry complete.  LANDED
-- at item 134 (`scanBlockEntryValidate`); every pin below was `parserGap`.
#guard scannerRefuses "a: 1\n- y\n"
#guard scannerRefuses "a: 1\n- y\nb: 2\n"
#guard scannerRefuses "? k\n- y\n"
#guard scannerRefuses "? k\n- y\n: v\n"
#guard scannerRefuses ": v\n- y\n"
#guard scannerRefuses "a:\n  b:\n  - x\n- y\n"
#guard scannerRefuses "a:\n- x\nb: 1\n- y\n"

-- Item 119's GAP CLASS IS EMPTY.  `parserGap` — both scanners accept, both
-- pipelines refuse — is the predicate this map was built on; one
-- representative of each mechanism now fails it, which is what the three
-- landings were for.
#guard !parserGap "[1, 2]\na\n"        -- M1 (item 132)
#guard !parserGap "a: 1\nb\n"          -- M2 (item 133)
#guard !parserGap "a: 1\n- y\n"        -- M3 (item 134)

-- §5 The neighbors the scanner ALREADY refuses — the map's boundary with
-- the existing checks (§8.1 under-indent, §8.2.1 trailing content, §7.4
-- implicit-key line, §7.3.2/§7.4 same-line junk, §9.1.5 directives):
#guard scannerRefuses "a: 1\n[1]\n"
#guard scannerRefuses "- a\n[1]\n"
#guard scannerRefuses "- a\nb: 2\n"
#guard scannerRefuses "hello\nb: 2\n"
#guard scannerRefuses "[1, 2], x\n"
#guard scannerRefuses "a: 1\n%YAML 1.2\n--- b\n"

-- §6 The valid boundary each mechanism must not cross.
-- M2's exempt structural predecessors (`.value`, `.key`, `.blockEntry`):
-- their equal-column readings REFUSE as of items 177/178 (Finding A's floor —
-- the narrowed exemption keeps only props-less flow-close tails), so the
-- boundary here is the strictly deeper twins, which stay the slots' own:
#guard scannerRefuses "a:\nb\n"
#guard scannerRefuses "?\nb\n: v\n"
#guard scannerRefuses "-\nb\n"
#guard scannerRefuses "a:\nb\nc: 2\n"
#guard emits "a:\n b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "?\n b\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :b", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "-\n b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :b", "-SEQ", "-DOC", "-STR"]
-- M3's two legal readings — the awaited value (with and without a
-- property run) and the continuing same-indent sequence (including the
-- level pops the back-scan must survive):
#guard emits "a:\n- y\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "=VAL :y", "-SEQ",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard accepts "a:\n- y\n"
#guard accepts "a: &x\n- y\n"
#guard accepts "a: !!seq\n- y\n"
#guard emits "a:\n- m:\n    - x\n- y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+SEQ", "+MAP", "=VAL :m",
   "+SEQ", "=VAL :x", "-SEQ", "-MAP", "=VAL :y", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "? k\n:\n- y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :y", "-SEQ",
   "-MAP", "-DOC", "-STR"]
-- `?` and `:` at the mapping's column open new ENTRIES — M3 is `-` only:
#guard emits "a: 1\n? k\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :k", "=VAL :v",
   "-MAP", "-DOC", "-STR"]
#guard emits "a: 1\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "=VAL :", "=VAL :v",
   "-MAP", "-DOC", "-STR"]
-- ...and the `?` at a SEQUENCE's own column is §8.2.1's, refused at the
-- scanner (item 131) exactly as its `:` twin above is — so M3, which is
-- about the `-` at a MAPPING's column, has no business here either way:
#guard scannerRefuses "- a\n? k\n: v\n"
#guard scannerRefuses "- a\nk: v\n"
-- M1's same-line boundary — the `:` that resolves the completed node as
-- an implicit key never crosses a line:
#guard emits "[1, 2]: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard accepts "\"x\": 1\nb: 2\n"
#guard emits "? \"x\"\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"x", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- M1's completing set excludes plain continuations, properties, markers:
#guard emits "hello\n[1]\n"
  ["+STR", "+DOC", "=VAL :hello [1]", "-DOC", "-STR"]
#guard accepts "hello\nworld\n"
#guard accepts "--- a\nb\n"
#guard emits "&p 1\nx\n"
  ["+STR", "+DOC", "=VAL &p :1 x", "-DOC", "-STR"]
#guard emits "&p\nc: 2\n"
  ["+STR", "+DOC", "+MAP &p", "=VAL :c", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard accepts "[1, 2]\n# c\n"
#guard accepts "\"x\"\n\n"
-- The suffix and explicit-document escapes stay open (items 116–118):
#guard accepts "[1, 2]\n...\na\n"
#guard accepts "a: 1\n...\n[1]\n"
#guard accepts "|\n  x\n...\n- y\n"
#guard accepts "\"x\"\n...\na\n"
#guard accepts "[1, 2]\n--- a\n"
#guard accepts "a: 1\n...\n%YAML 1.2\n--- b\n"
-- Entry continuations at the level's column resolve and never dangle:
#guard accepts "a: 1\nb: 2\n"
#guard accepts "a: 1\n\"q\": 2\nb: 3\n"
#guard accepts "- a\n- b\n"

/-! §7 The props-only run whose structural predecessor is `.value`
(`a:⏎&p⏎- y`) refuses at §9.2's own check as of item 178 — the residue
this section recorded is paid: the properties stand at the awaiting
level's own column, behind the same `s-separate(n+1)` every scalar
alternative spends, so the slot-offered exemption no longer covers a
`[96]`-headed run and the refusal moved up from the parser's
`trailing content` to `invalidBareDocument` at the run's start.  The
root twin `&p⏎c: 2` stays a legal anchored mapping: its predecessor
offers no slot and no level is open at its column. -/
#guard !scansClean "a:\n&p\n- y\n"
#guard refuses "a:\n&p\n- y\n"
#guard accepts "&p\nc: 2\n"

/-! §8 A measured SCANNER asymmetry, found by these pins: same-line junk
after a completed root flow close or quoted scalar is refused by the
LEGACY scanner (`validateFlowClose` / `validateTrailingContent`) but
accepted by the INDEXED one, which leaves it to the parser (verdict
parity holds; the LAYER differs).  The comma twin is symmetric.  M1's
landing inherits the indexed same-line boundary as its own obligation. -/
private def legacyOnlyScanRefusal (input : String) : Bool :=
  (match Scanner.scan input, Indexed.ScannerStateIx.scanIx input with
   | .error _, .ok _ => true
   | _, _ => false) && refuses input

#guard legacyOnlyScanRefusal "[1, 2] x\n"
#guard legacyOnlyScanRefusal "\"x\" y\n"

end L4YAML.Tests.Guards.ScannerRaisedFlagRefusalMap

end Blanket
