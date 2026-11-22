module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flip's remainder, mapped (DOCS items 171–183)

Row 19's 1c ends by narrowing `[210]`'s slot (`GOpt SLAnyDocument` →
`GOpt SLExplicitDocument`), and the narrowing instrument breaks FIVE
definitions: `topLevelFlowResumeSep`, `rootMapRoute`, `rootMapRouteF`,
`bareNodeRoute` — the four raw routes that append a completed construct to the
stream as a fresh BARE document — and `structural_dispatch_to_pending`, whose
breaking site passes `SLAnyDocument.explicit` and is the wrapper the flip
itself deletes.  Every consumer arm that still reaches a raw route is one of:

* the four guards' own fallback arms (`*_or_refused` at `Or.inr` and at a
  landing resting ON an open level),
* `flowKeyRoute_of_root`'s no-break arm,
* `content_dispatch_after_close`'s route,
* `accum_content_pending`'s two crossed-window arms (item 170's; their
  scanner-reachable domain is EMPTY as of item 180 — §3), and
* `bareNodeRoute_or_refused_content`'s two fallback arms.

This file pins the INPUT families those arms serve, at the runtime, one
`#guard` per family — so the map is measured, and any runtime move flips it
loudly.  Its DEFINITION-side twin is
`Tests/Guards/Proofs/FlipConsumerSurface.lean` (item 183), which pins who still
reaches a raw route — 8 definitions, 15 applications — and the deferral beside
it; the two move together and neither is the flip instrument's own five, which
count the flip's WORK and not its remainder.  Item 171 measured the map and named two findings; item 172 closed the
second, and the pins below are the map at the CLOSED state:

**The value at its own level's column (§4) is REFUSED as of item 177 —
Finding A's runtime floor.**  Every alternative of `[196] s-l+block-node(n,c)`
and `[185] s-l+block-indented(n,c)` that a scalar or alias can head spends
`s-separate(n+1)`, whose line-crossing branch demands `s-indent(n+1)` —
column `n` fails it — so a props-less scalar or alias run standing at an open
level's own column refuses at the scanner (`danglingNodePos?`, whose
slot-offered exemption item 177 narrowed to the run shapes other readings
own), with the same `invalidBareDocument` constructor and run-start position
the slot-LESS twin `a: 1⏎b` has always gotten.  The refusal covers plain,
quoted, and block-scalar forms and the alias, at any depth, mid-stream, and
in implicit and explicit entries alike; `[201] seq-spaces` keeps the sequence
(`k:⏎- a` arrives as a `-` indicator, not a run).  **Item 178 is the same
floor's `[96]` half**: the properties sit inside the same alternatives,
behind the same `s-separate(n+1)`, so a props-HEADED run at the column
refuses at the same check too — `k:⏎&x a` and the props-headed flow tail
`k:⏎&x [1]⏎: b` move from the parser's `trailingContent` to the scanner, and
the `-`/`?` faces (`-⏎&x a`, `?⏎&x a⏎: v`), which rode the exemption into
outright acceptance, flip to the refusal.  The exemption keeps only the
props-less flow-close tail, whose refusals are item 172's floor and whose
sibling-key readings never present a break-ended run.  PyYAML (6.x,
`yaml.parse`, event level) refuses every one of these at its scanner ("could
not find expected ':'") EXCEPT the block-scalar header forms (`k:⏎|⏎ x`),
which it accepts against `[199]`'s own `s-separate(n+1)` — item 177's one
named PyYAML gap, and the props-headed twin `k:⏎&x |⏎ x` is refused even
there (the `&x` is what PyYAML's scanner trips on); the one suite case in
any family is G9HC (`seq:⏎&anchor⏎- a`), an error case whose refusal moves
stage only.  **Item 179 landed the ENCODING half** — `SBlockNode` reads
`n_lean = n_spec + 1` through the three crossings that used to feed it raw
columns, `nestedBlockMap`'s `n ≤ k` is the spec's own strict floor at that
convention, and the equal-width landing's second derivation is gone
(`BlockCollectionWidthFloor.lean` §§4–5).  The runtime did not move at 179,
so every pin below is unchanged; what 179 leaves for the flip is one
acceptance that now survives ONLY through `[211]`'s bare continuation:
`k: &x⏎a` — the run parks DEEPER than the awaiting level (legal), the
content lands AT the level's column, and the attached reading
(`{k: &x a}`, the events pipeline's own) died with the re-index, so the
derivation left is the second-document over-approximation the flip deletes.
PyYAML refuses it; the run-start check cannot see it (the run is legal where
it stands); it joins ~~the crossed-window arms on~~ the flip's own prerequisite
list — **the crossed-window arms left it at item 180** (their family refuses
at the scanner now), so `k: &x⏎a` is the list's LAST runtime entry.
**Item 182 spends it** (§4b): the reading is taken between `[96]`'s
properties and the content they decorate rather than in FRONT of the run,
and the flip's prerequisite list is EMPTY.  The FLOW
half was never this floor's:
a flow node standing in the awaited slot at column `n` is item 172's refusal
(`underIndentedFlowContent`, §5), and the two readings stay disjoint by the
run's tail.

**The sibling implicit flow key (§5) is item 172's fix.**  `c-s-implicit-json-key`
is `c-flow-json-node(n/a, block-key)` — the flow key carries no indent
parameter — so a `[`/`{` landing AT an open level's column may be the level's
next KEY, and key-vs-value is not decidable at the open (item 159's own
measurement: a collection can head a key).  §8.1's floor is therefore read at
the CLOSE (`underIndentedFlowValuePos?`, the slot-offered complement of
`danglingNodePos?`): the same-line `:` after the close resolves the key half
through the simple key the close restores — the sibling entry, `a: 1⏎[1]: b`
= `{a: 1, [1]: b}`, exactly the reading the anchor-shifted twin
`a: 1⏎&p [b]: c` has always had — and a landing no `:` resolves refuses at
the break or EOF gate: as the awaited value's own under-indent where the slot
holder OFFERS a node (`k:⏎[1, 2]`, `underIndentedFlowContent` at the open's
position), and as §9.2's dangling node where it COMPLETES one (`a: 1⏎[1, 2]`,
`invalidBareDocument` — the same constructor the scalar twin `a: 1⏎b` gets,
and the same one the anchored twin `a: 1⏎&p [1, 2]` has always gotten). -/

namespace L4YAML.Tests.Guards.StreamFlipRemainderMap

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-- The scanner's own verdict, with `scanLoop`'s EOF checks applied — so a
    refusal names which scanner mechanism produced it, and `scan-accepted`
    means the per-step and BOTH EOF checks passed. -/
private def scanPhase (input : String) : String :=
  let rec go (s : ScannerState) (fuel : Nat) : String :=
    match fuel with
    | 0 => "fuel"
    | fuel' + 1 =>
      match scanNextToken s with
      | .ok (some s') => go s' fuel'
      | .ok none =>
        match scanLoop_checkDanglingNode s with
        | .error e => s!"scan-EOF-refused {repr e}"
        | .ok () =>
          match scanLoop_checkFlowValueIndent s with
          | .ok () => "scan-accepted"
          | .error e => s!"scan-EOF-refused {repr e}"
      | .error e => s!"scan-refused {repr e}"
  go ((ScannerState.mk' input).emit .streamStart) 200

private def flat (s : String) : String :=
  String.intercalate " " ((s.splitOn "\n").filter (· ≠ ""))

/-- Both pipelines' event output, asserted equal — a pin on this is a pin on
    the reading AND on parity. -/
private def evBoth (input : String) : String :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok a, .ok b => if a == b then flat a else s!"MISMATCH {flat a} ≠ {flat b}"
  | .error a, .error b =>
      if reprStr a == reprStr b then s!"ERR {repr a}" else s!"ERR-MISMATCH {repr a} ≠ {repr b}"
  | .ok a, .error b => s!"SPLIT ok {flat a} / err {repr b}"
  | .error a, .ok b => s!"SPLIT err {repr a} / ok {flat b}"

private def pins (input : String) : String × String := (scanPhase input, evBoth input)

/-! ## §1  The block lane: what `bareNodeRoute`'s holders serve

The guards' on-level arms (`rootMapRoute_or_refused`, `rootMapRouteF_or_refused`,
`bareNodeRoute_or_refused` at `h_op = true`, and `content_dispatch_after_close`)
serve exactly the SIBLING landings: a completed entry, a break, the next entry
at the same width.  Every accepted input here is one document read entry by
entry — the resume reading, not a second bare document — which is what the
arms must hand after the flip. -/

#guard pins "a: 1\nb: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "? a\n: 1\n? b\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "[1]: a\nb: 2\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :a =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "k:\na: 1\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : =VAL :a =VAL :1 -MAP -DOC -STR")
#guard pins "k: &p\na: 1\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &p : =VAL :a =VAL :1 -MAP -DOC -STR")
#guard pins "a: |\n  x\nb: 1\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL |x\\n =VAL :b =VAL :1 -MAP -DOC -STR")
#guard pins "a:\n- x\n- y\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a +SEQ =VAL :x =VAL :y -SEQ -MAP -DOC -STR")
#guard pins "k: v\nw: x\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL :v =VAL :w =VAL :x -MAP -DOC -STR")

/-! …and the INDICATOR-headed siblings — the `:`/`?` opened at a still-open
level's own width, which is what item 173's resume arm at
`colon_open_map`/`question_open_map` serves.  One mapping each, the empty or
explicit key consed as the level's next entry — at the root, one level in,
and on the awaited-value park (`k:⏎: 2` = `{k: null, null: 2}`, the flow twin
of which is §5's `k:⏎[1]: b`).  References: the SUITE certifies the colon
family itself — 2JQS is `: a⏎: b` with exactly this one-mapping event list —
and `[192]`'s `e-node` key alternative is the production; PyYAML is NOT the
reference here (it refuses every empty implicit key, first entry included —
its known `[192]` gap), while it parses the `?` siblings with matching
events.  The dedent-crossing colon sibling (`a:⏎- x⏎: 2`) is the same
reading at the parser and the swap's RECORDED residue on the proof side: the
entry parks carry no mapping-lane frames, so that landing keeps the guarded
fallback until a carrier crosses the `-`'s close. -/
#guard pins ": 1\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL : =VAL :1 =VAL : =VAL :2 -MAP -DOC -STR")
#guard pins "a: 1\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 =VAL : =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n  a: 1\n  : 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL :1 =VAL : =VAL :2 -MAP -MAP -DOC -STR")
#guard pins "k:\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : =VAL : =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n? b\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n  ? a\n  : 1\n  ? b\n  : 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL :1 =VAL :b =VAL :2 -MAP -MAP -DOC -STR")
#guard pins "a:\n- x\n: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a +SEQ =VAL :x -SEQ =VAL : =VAL :2 -MAP -DOC -STR")

/-! …and the landings that are NOT siblings are refused by the scanner —
§9.2 at the landing (M1), at EOF (M2), or at the `-` (M3 family) — so the
guards' refuted arms cover them and the raw route serves them nothing. -/
#guard pins "a: 1\nb\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a\n# c\nb\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "\"a\"\nb: 1\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: v\n- a\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")

/-! ## §2  The flow lane after item 172: the key half resumes, the value half
refuses at the gate

`topLevelFlowResumeSep_or_refused`'s fallback arms and `flowKeyRoute_of_root`'s
landing arm serve the deferred floor's two halves.  The KEY half — a landing
flow open whose close a same-line `:` resolves — is the sibling entry, accepted
with the resume reading in both pipelines.  The VALUE half is refused at the
break or EOF gate: `invalidBareDocument` where the run's slot holder completes
a node (§9.2's own reading through the close, item 159's walk-back), and the
more-indented interior refuses by column exactly as before (item 145).

**Item 176 pays the key half on the proof side.**  `flowKeyRoute_of_root`'s
landing arm takes the park's still-open mapping levels (`h_mapF`, the shape
the `:`/`?` openers took at item 173) and spends the RESUME first — the
sibling flow key conses onto the level's own tail (`resumeMapRoute`) instead
of falling to `rootMapRoute_or_refused`'s bare second document — paid by
`pendingContent.h_framesS` and `pendingBlockContent.h_closeF` (read at the
empty tail, item 110's own spend) through the flow open's landing.  And the
entries-level TWIN rides on every arm now — item 120's punt-gate ("the bare
flow key at a level's own column is §8.1-refused") expired at item 172 — so
the park made after the flow-keyed entry's value offers the NEXT landing the
same resume: the chains below are one mapping end to end, on both the flow
lane (`[2]: b`) and the block lane (`c: 2`, through `flowKeyPack_of_close` →
`pendingMapValue.h_frames` → items 109/151's content machinery). -/

#guard pins "a: 1\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n{x: y}: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +MAP {} =VAL :x =VAL :y -MAP =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n[1, 2]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 =VAL :2 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "k:\n  a: 1\n  [1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -MAP -DOC -STR")
#guard pins "[1]: a\n[2]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :a +SEQ [] =VAL :2 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "\"x\"\n[1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  \"a\"\n  [1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
#guard pins "k:\n  \"a\"\n    [1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 4", "ERR L4YAML.ScanError.invalidBareDocument 2 4")

/-! Item 176's paid families, park by park: the explicit entry's completed
value, the block-scalar value, the sequence dedent (`h_closeF` at the empty
tail), and the anchored value all land the sibling flow key through the new
resume arm.  PyYAML (6.x, `yaml.parse`) parses every one of these with
matching events. -/
#guard pins "? a\n: 1\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: |\n  x\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL |x\\n +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "k:\n  - x\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +SEQ =VAL :x -SEQ +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: &x 1\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL &x :1 +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n[1]:\n  c: d\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ +MAP =VAL :c =VAL :d -MAP -MAP -DOC -STR")

/-! …and the CHAINS the entries-level twin buys: the entry after the
flow-keyed one resumes too, on either lane.  The `...` chain rides the named
PyYAML suffix gap (item 175: PyYAML refuses ANY bare document after a `...`
suffix), so `[210]`'s text is the reference there; PyYAML parses the rest
with matching events. -/
#guard pins "a: 1\n[1]: b\nc: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b =VAL :c =VAL :2 -MAP -DOC -STR")
#guard pins "[1]: a\n[2]: b\nc: 3\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :a +SEQ [] =VAL :2 -SEQ =VAL :b =VAL :c =VAL :3 -MAP -DOC -STR")
#guard pins "[1]: a\nb: 2\nc: 3\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :a =VAL :b =VAL :2 =VAL :c =VAL :3 -MAP -DOC -STR")
#guard pins "a: 1\n[1, 2]: b\nc: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 =VAL :2 -SEQ =VAL :b =VAL :c =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n  a: 1\n  [1]: b\n  c: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b =VAL :c =VAL :2 -MAP -MAP -DOC -STR")
#guard pins "...\n[1]: b\nc: 2\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b =VAL :c =VAL :2 -MAP -DOC -STR")

/-! Item 176's measured punts, each with its location: the marker-seed chain
(`flowKeyRoute_of_open`'s twins stay punts — the `c: 2` landing keeps the
guarded fallback until that boundary pays); the seq-spaces sibling (the
`pendingBlockContent n = 0` park's `h_closeF` bound `k' < n` cannot list the
level, item 173's dedent residue one lane over); and the awaited-value park's
sibling (`k:⏎[1]: b` — the nested `m = 0` reading the `pendingMapValue` arm
used to spend died with item 179's re-indexing; the landing now falls past
the strict split to the guarded fallback, and the honest sibling reading —
the one the events above already emit — stays the punt's own to pay). -/
#guard pins "---\n[1]: b\nc: 2\n" == ("scan-accepted", "+STR +DOC --- +MAP +SEQ [] =VAL :1 -SEQ =VAL :b =VAL :c =VAL :2 -MAP -DOC -STR")
#guard pins "a:\n- x\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a +SEQ =VAL :x -SEQ +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "k:\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "k:\n[1]: b\nc: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : +SEQ [] =VAL :1 -SEQ =VAL :b =VAL :c =VAL :2 -MAP -DOC -STR")

/-! …and the boundaries: the value half refuses at the same parks the key
half now resumes through, and the flow key at the SEQUENCE's own width is
§8.2.1's key-at-sequence-column refusal.  PyYAML refuses all four. -/
#guard pins "a: |\n  x\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "? a\n: 1\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "a:\n- x\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "k:\n  - x\n  [1]: b\n" == ("scan-refused L4YAML.ScanError.trailingContent 2 2", "ERR L4YAML.ScanError.trailingContent 2 2")

/-! The routes the flow lane's park DOES spend — the seed (`nodoc`), the
marker, the suffix — are the flip-legal twins, and their inputs accept. -/
#guard pins "[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "---\n[1]: b\n" == ("scan-accepted", "+STR +DOC --- +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "...\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "&p [1]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] &p =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n...\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC ... +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n...\n[1, 2]\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC ... +DOC +SEQ [] =VAL :1 =VAL :2 -SEQ -DOC -STR")

/-! ## §3  The crossed-props arms — DELETED at item 181

`accum_content_pending`'s two `PropsWindowCross` fallbacks (item 170) applied
the raw route behind a window premise whose every scanner-reachable input the
parser refuses — `TokenParser.validNextToken`'s own §9.2 reading.  The full
window pins are `PropsCrossWindowRoute.lean`'s; the two families here were the
arms' whole domain, and **item 181 deletes the arms** now that the scanner
refuses both: the window, the park field that carried its route
(`pendingProps.h_routeX`) and the two raw `bareNodeRoute` applications go
together, and the raw-route census drops from THREE holders to TWO.  Item 178 moved the OFFERED family's refusal into the
scanner — the window's first property stands at the awaiting level's own
column, which is now `danglingNodePos?`'s own reading at the first break —
so the crossed window is never reached there any more; ~~the root family,
whose window has no offered slot, keeps the parser's refusal~~ — **item 180
moved it to the scanner too**: the crossed-block clause reads the over-full
trailing block at the checks, so the arms' whole scanner-reachable domain is
EMPTY, and the pins below show both families scanner-refused at the positions
the parser used to report. -/

#guard pins "a:\n!t\n&b\n  !s &c x\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
-- Item 180: the ROOT family refuses at the SCANNER now — the crossed-block
-- clause reads the over-full trailing block at the EOF check, at the excess
-- property's own position, which is exactly where the parser reported.  The
-- crossed-window arms' scanner-reachable domain is EMPTY.
#guard pins "&a\n!t &b x\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 3", "ERR L4YAML.ScanError.invalidBareDocument 1 3")

/-! ## §3b  Items 174–175 — the props ride across the break

`[161] ns-flow-node`'s third alternative separates the properties from the
content with `s-separate(n,c)`, which is `s-separate-lines` in every non-key
context — the BREAK IS INSIDE THE NODE.  So a sentinel-level `[96]` park's
break-crossed content is the run's OWN node, not an anchored-empty document
followed by a bare second one: the scalar and quoted forms ride `[161]`'s
props alternative, the block scalar rides `[198]`'s slot, and the implicit-key
mapping rides `[196] s-l+block-collection`'s optional properties — the
MAPPING's anchor (`+MAP &p`), where the same-line `&p b: 1` anchors the KEY
(`+MAP =VAL &p :b` — PyYAML agrees on both readings).  The ride bottoms in
the park's own route, so the seed, the marker and the suffix parks all ride
identically, and the explicit value's park (`? k⏎: &p⏎b` = `{k: &p b}`) is
the same `n = 0` swap — there PyYAML refuses at its simple-key scanner, a
PyYAML-side gap like `[192]`'s.

Item 174 paid the CONTENT-dispatch rides at the sentinel-indexed park.
**Item 175 paid the INDICATOR-dispatch rides**: a landed `-`/`?`/`:` opens
the RUN's own collection — `[196]`'s optional properties again, the
COLLECTION's anchor (`&p⏎- a` = `+SEQ &p`, where the same-line `&p - a` is
scanner-refused; `&p⏎? x⏎: v` and `&p⏎: v` = `+MAP &p`) — through the same
park route, carried as `PropsNodeRoute` (the ride's landing half): the FIFTH
arm of the `:`/`?` openers' cascades and the `-` arm's entries route
(`propsSeqRoute`).  PyYAML agrees on every accepted family below except its
three known gaps: the empty implicit key (`&p⏎: v` — `[192]`, the suite's
2JQS lineage is the reference), the explicit value's simple key
(`? k⏎: &p⏎…`), and ANY bare document after a `...` suffix (it refuses the
anchor-free `a: 1⏎...⏎b: 2` identically — `[210]`'s
`l-document-suffix+ l-any-document?` is the reference).

**Item 175 also STRUCK one of item 174's punt rows**: the flow-open ride
(`&p⏎[1, 2]`) was never on the fallback — `accum_flow_open_depth0`'s
`pendingProps` arm has ridden the run into the flow node (break or not,
`SFlowNode.propsContent` through the park's route) since items 9h/12, and
its only other branch serves under-run parks, which cannot exist at `n = 0`.

Recorded punts, each with the fallback still standing: the ENCLOSING-level
indented rides (`k:⏎  a: &p⏎    c: d`, `k:⏎  a: &p⏎  - w` — the ride pays
`n = 0` only), the two-park chain (`!t⏎&q b` and its break variants — one
`[96]` run whose internal separate crossed the break; the run-extension arm
is the NO-BREAK branch's, measured at item 175), the enclosing park's col-0
sibling `:` (`k:⏎  a: &p⏎: v` — a `[96]` park carries no mapping-lane
frames, item 173's recorded residue), and the alias landing (`&p⏎*p`,
scan-accepted and parser-refused).  The enclosing-level park's dedented
landing keeps `propsEmpty` + the sibling resume — the honest reading there
(`k:⏎  a: &p⏎c: 2`, `k:⏎  a: &p⏎  c: d`). -/

-- the paid rides: scalar, comments interleaved, indented, quoted, block
-- scalar, tag, two-half run, and the implicit-key mapping (root + indented)
#guard pins "&p\nb\n" == ("scan-accepted", "+STR +DOC =VAL &p :b -DOC -STR")
#guard pins "&p\n# c\nb\n" == ("scan-accepted", "+STR +DOC =VAL &p :b -DOC -STR")
#guard pins "&p\n  b\n" == ("scan-accepted", "+STR +DOC =VAL &p :b -DOC -STR")
#guard pins "&p\n\"b\"\n" == ("scan-accepted", "+STR +DOC =VAL &p \"b -DOC -STR")
#guard pins "&p\n|\n  x\n" == ("scan-accepted", "+STR +DOC =VAL &p |x\\n -DOC -STR")
#guard pins "!t\nb\n" == ("scan-accepted", "+STR +DOC =VAL <!t> :b -DOC -STR")
#guard pins "&p !t\nb\n" == ("scan-accepted", "+STR +DOC =VAL &p <!t> :b -DOC -STR")
#guard pins "&p\nb: 1\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL :b =VAL :1 -MAP -DOC -STR")
#guard pins "&p\n  b: 1\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL :b =VAL :1 -MAP -DOC -STR")
-- …through the marker's, the suffix's and the explicit value's own routes
#guard pins "---\n&p\nb\n" == ("scan-accepted", "+STR +DOC --- =VAL &p :b -DOC -STR")
#guard pins "a: 1\n...\n&p\nb\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC ... +DOC =VAL &p :b -DOC -STR")
-- Item 182: this ride's own input is REFUSED now — the props park at the
-- explicit value's column 2 and the content lands at the mapping's own 0, so
-- the run crosses the break BELOW its start (§4b).  PyYAML refuses it at the
-- same `2,0`; the ride the arm serves is the deeper landing beside it.
#guard pins "? k\n: &p\nb\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "? k\n: &p\n b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &p :b -MAP -DOC -STR")
-- the boundary: the enclosing-level park closes propsEmpty and the landing
-- resumes — the honest reading the ride must NOT displace
#guard pins "k:\n  a: &p\nc: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL &p : -MAP =VAL :c =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n  a: &p\n  c: d\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL &p : =VAL :c =VAL :d -MAP -MAP -DOC -STR")
-- item 175's paid rides: the landed `-`/`?`/`:` at the sentinel park opens
-- the run's own collection (multi-entry, indented, comment-interleaved,
-- valueless explicit key, tag, and two-half runs included)
#guard pins "&p\n- a\n" == ("scan-accepted", "+STR +DOC +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "&p\n? x\n: v\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL :x =VAL :v -MAP -DOC -STR")
#guard pins "&p\n: v\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL : =VAL :v -MAP -DOC -STR")
#guard pins "&p\n- a\n- b\n" == ("scan-accepted", "+STR +DOC +SEQ &p =VAL :a =VAL :b -SEQ -DOC -STR")
#guard pins "&p\n  - a\n" == ("scan-accepted", "+STR +DOC +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "&p\n# c\n- a\n" == ("scan-accepted", "+STR +DOC +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "&p\n? x\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL :x =VAL : -MAP -DOC -STR")
#guard pins "!t\n- a\n" == ("scan-accepted", "+STR +DOC +SEQ <!t> =VAL :a -SEQ -DOC -STR")
#guard pins "&p !t\n? x\n: v\n" == ("scan-accepted", "+STR +DOC +MAP &p <!t> =VAL :x =VAL :v -MAP -DOC -STR")
-- …and through the marker's, the suffix's and the explicit value's routes
#guard pins "---\n&p\n- a\n" == ("scan-accepted", "+STR +DOC --- +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "a: 1\n...\n&p\n- a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC ... +DOC +SEQ &p =VAL :a -SEQ -DOC -STR")
#guard pins "---\n&p\n: v\n" == ("scan-accepted", "+STR +DOC --- +MAP &p =VAL : =VAL :v -MAP -DOC -STR")
#guard pins "? k\n: &p\n- w\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +SEQ &p =VAL :w -SEQ -MAP -DOC -STR")
#guard pins "---\n&p\n? x\n: v\n" == ("scan-accepted", "+STR +DOC --- +MAP &p =VAL :x =VAL :v -MAP -DOC -STR")
-- the flow-open ride, paid on the FLOW lane since items 9h/12 (item 174's
-- punt row for it was wrong; struck at item 175)
#guard pins "&p\n[1, 2]\n" == ("scan-accepted", "+STR +DOC +SEQ [] &p =VAL :1 =VAL :2 -SEQ -DOC -STR")
#guard pins "---\n&p\n[1]\n" == ("scan-accepted", "+STR +DOC --- +SEQ [] &p =VAL :1 -SEQ -DOC -STR")
-- the recorded punts (all accepted, still on the fallback readings)
#guard pins "k:\n  a: &p\n    c: d\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a +MAP &p =VAL :c =VAL :d -MAP -MAP -MAP -DOC -STR")
#guard pins "k:\n  a: &p\n  - w\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a +SEQ &p =VAL :w -SEQ -MAP -MAP -DOC -STR")
#guard pins "k:\n  a: &p\n: v\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :a =VAL &p : -MAP =VAL : =VAL :v -MAP -DOC -STR")
#guard pins "!t\n&q b\n" == ("scan-accepted", "+STR +DOC =VAL &q <!t> :b -DOC -STR")
#guard pins "&p\n!t b\n" == ("scan-accepted", "+STR +DOC =VAL &p <!t> :b -DOC -STR")
#guard pins "!t\n&q\nb\n" == ("scan-accepted", "+STR +DOC =VAL &q <!t> :b -DOC -STR")
#guard pins "!t\n&q\n- a\n" == ("scan-accepted", "+STR +DOC +SEQ &q <!t> =VAL :a -SEQ -DOC -STR")
-- the refused shapes beside them
#guard pins "&p\nb\nc: 1\n" == ("scan-refused L4YAML.ScanError.invalidImplicitKey 2", "ERR L4YAML.ScanError.invalidImplicitKey 2")
-- Item 180: the anchor-anchor pair moves to the same scanner refusal — and
-- its MESSAGE upgrades from the parser's `duplicateAnchor` (there is no
-- duplicate NAME; it meant a second anchor for one node) to the family's own
-- `invalidBareDocument` at the second anchor, PyYAML's reading of the shape.
#guard pins "&p\n&q b\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "&p\n*p\n" == ("scan-accepted", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  a: &p\n- w\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "? k\n: &p\n[1]\n" == ("scan-EOF-refused L4YAML.ScanError.underIndentedFlowContent 2 0", "ERR L4YAML.ScanError.underIndentedFlowContent 2 0")

/-! ## §4  Finding A — the value at its own level's column (REFUSED, item 177)

The runtime floor, landed: the six §4 families items 171–176 pinned as
accepted readings now refuse at the scanner, with the slot-less twin's own
constructor at the run's start — mid-stream where a break ends the run, at
EOF where the stream does.  PyYAML refuses all but the block-scalar headers
(the named gap); no suite case decides any of them.  The `?`/`-`/`:` faces of
the same exemption (`?⏎b⏎: v`, `-⏎b`, `:⏎a`) and the mid-stream chain
(`k:⏎b⏎: 2`, which read as `{k: b, null: 2}`) refuse the same way. -/

#guard pins "k:\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n\"a\"\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n'a'\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  m:\n  a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
#guard pins "k:\na\nb: 2\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "? k\n:\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "k:\n|\n x\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n>\n x\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "x: &a 1\nk:\n*a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "k:\na\n b\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "?\nb\n: v\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "-\nb\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins ":\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\nb\n: 2\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
-- item 178: the `[96]`-headed runs at the column refuse at the same check —
-- the `:` families move stage (parser `trailingContent` → scanner), and the
-- `-`/`?` faces, which the exemption had let through to ACCEPTANCE, flip
#guard pins "k:\n&x a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n!t a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n&x\n a\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n&x |\n x\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n&x [1]\n: b\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n&x a\nb: 2\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  m:\n  &x a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
#guard pins "-\n&x a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "?\n&x a\n: v\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "?\n&x a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "- ?\n  &x a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 2", "ERR L4YAML.ScanError.invalidBareDocument 1 2")
-- …while the props runs other readings own stay where they were: strictly
-- deeper (the value's own props), the root's and the marker's (no offered
-- slot, no open level), the same-line-resolved sibling keys, and the
-- props-less flow tail (item 172's floor)
#guard pins "k:\n &x a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &x :a -MAP -DOC -STR")
#guard pins "k:\n &x\n- a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +SEQ &x =VAL :a -SEQ -MAP -DOC -STR")
#guard pins "&p\nc: 2\n" == ("scan-accepted", "+STR +DOC +MAP &p =VAL :c =VAL :2 -MAP -DOC -STR")
#guard pins "a: 1\n&x b: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 =VAL &x :b =VAL :2 -MAP -DOC -STR")
#guard pins "k:\n&x [1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : +SEQ [] &x =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "k:\n[1]\n: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
#guard pins "k:\n  m:\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "- k:\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n- a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +SEQ =VAL :a -SEQ -MAP -DOC -STR")
#guard pins "k:\n a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL :a -MAP -DOC -STR")
#guard pins "?\n a\n: v\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :v -MAP -DOC -STR")
#guard pins "-\n b\n" == ("scan-accepted", "+STR +DOC +SEQ =VAL :b -SEQ -DOC -STR")
#guard pins "-\n- a\n" == ("scan-accepted", "+STR +DOC +SEQ =VAL : =VAL :a -SEQ -DOC -STR")
#guard pins "k: x\n y\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL :x y -MAP -DOC -STR")
#guard pins "---\na\n" == ("scan-accepted", "+STR +DOC --- =VAL :a -DOC -STR")

/-! ## §4b  Item 182 — the run that crosses the break BELOW its start

§4's readings are all taken at the run's START, and a run may start where no
level stands and cross the break INSIDE itself: in `k: &x⏎a` the `&x` sits
legally at column 3 and it is the CONTENT that lands at the mapping's own
column.  `[96]`'s properties and the content they decorate are separated by
the same `s-separate(n+1)` §4 spends, so the token that starts the run's next
line has no derivation at an open level's column either.  `runLineCrossPos?`
reads it through `crossedPropsExcessIdx?`'s own three arms — a property tail,
a one-token body, a flow close read back to its open — so the property
BLOCK's internal crossing is seen at the close too, which is what keeps a
park's verdict and its collection's the same one.

PyYAML refuses every family below at the crossing token's own position, the
position pinned here, with ONE exception: the block-scalar form
`k: &x⏎|⏎␣x`, which it accepts against `[199]`'s own `s-separate(n+1)` —
item 177's named PyYAML gap, read one step over.  The suite decides one of
them: **H7J7** (`node-anchor-not-indented`, `key: &x⏎!!map⏎␣␣a: b`), an
error case whose refusal moves from the parser's `trailingContent` to the
scanner at the same `1,0`.  The one VALID suite entry in the reading's
neighbourhood is 6KGN (`---⏎a: &anchor⏎b: *anchor`), and it is untouched:
the check is gated on a break having ENDED the run, and `b`'s `:` is still
to come on `b`'s own line — the same gate that keeps `a: 1⏎b: 2`. -/

-- the content at the level's column, through every body style and both
-- indicator faces, at the root and one level in
#guard pins "k: &x\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: &x !t\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: !t\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: &x\n\"a\"\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: &x\n'a'\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: &x\n|\n x\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "- &x\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "? &x\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "? &x\na\n: v\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins ": &x\na\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "m:\n  k: &x\n  a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
#guard pins "- - &x\n  a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 2", "ERR L4YAML.ScanError.invalidBareDocument 1 2")
#guard pins "k:\n  m: &x\n  a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
-- the mid-stream faces: a sibling behind the crossing, the explicit value's
-- `:` on its own line, and the plain scalar's own continuation
#guard pins "k: &x\na\nb: 2\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: &x\nb\n: 2\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: &x\na\n b\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
-- …and the PROPERTY that starts the line, which `[96]`'s own internal
-- separation refuses: the block reading comes first, in token order, and the
-- flow arm reads it at the CLOSE (`k: &a⏎!t [1]`, where §8.1's floor sees
-- nothing because the OPEN sits at column 3)
#guard pins "k: &x\n!t a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: &x\n!t\na\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: !t\n&x a\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k: &a\n!t [1]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
-- the suite's own case: `node-anchor-not-indented`, moved from the parser
#guard pins "key: &x\n!!map\n  a: b\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
-- …and what the reading must NOT take: the same line, the strictly deeper
-- landing at every depth, the sibling key the gate keeps (6KGN's shape), the
-- seq-spaces entry, the sibling FLOW key, the props-less flow tails (item
-- 172's floor), the ROOT and marker runs (no level at their column), and the
-- two-park chain
#guard pins "k: &x a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &x :a -MAP -DOC -STR")
#guard pins "k: &x\n a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &x :a -MAP -DOC -STR")
#guard pins "k: &x\n  a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &x :a -MAP -DOC -STR")
#guard pins "k: &x\nb: 2\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &x : =VAL :b =VAL :2 -MAP -DOC -STR")
#guard pins "k: &x\n- a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +SEQ &x =VAL :a -SEQ -MAP -DOC -STR")
#guard pins "m:\n  k: &x\n   a\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :m +MAP =VAL :k =VAL &x :a -MAP -MAP -DOC -STR")
#guard pins "? k\n: &p\n b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &p :b -MAP -DOC -STR")
#guard pins "k: &a\n!t [1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL &a : +SEQ [] <!t> =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "k: &a !t\n[1]\n" == ("scan-EOF-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
#guard pins "k: &x\n[1]\n" == ("scan-EOF-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
#guard pins "&x\na\n" == ("scan-accepted", "+STR +DOC =VAL &x :a -DOC -STR")
#guard pins "---\n&x\na\n" == ("scan-accepted", "+STR +DOC --- =VAL &x :a -DOC -STR")
#guard pins "!t\n&q\nb\n" == ("scan-accepted", "+STR +DOC =VAL &q <!t> :b -DOC -STR")
#guard pins "---\na: &anchor\nb: *anchor\n" == ("scan-accepted", "+STR +DOC --- +MAP =VAL :a =VAL &anchor : =VAL :b =ALI *anchor -MAP -DOC -STR")

/-! ## §5  Item 172 — §8.1's floor at the close

The deferred floor's own boundary map.  The KEY half: a same-line `:` after
the close resolves the collection as the awaiting entry's sibling key — at the
root, one level in, after an explicit entry, and as the awaited value's OWN
sibling (`k:⏎[1]: b` = `{k: null, [1]: b}`, the flow twin of §1's
`k:⏎a: 1`).  The anchor-shifted twin now differs from the bare form by its
anchor alone, in verdict and in events alike.  The VALUE half: an unresolved
slot-OFFERED landing refuses as `underIndentedFlowContent` at the OPEN's own
position (`underIndentedFlowValuePos?` reads the close's matching open,
`flowOpenIdx?`, and the open's column against the open levels — the
`[96]`-transparent slot holder decides offered-vs-completed, and the props
face `k:⏎&p [1, 2]` refuses at §4's own check as of item 178, at the `&p`
the run starts at), and a
break kills the key exactly
where §7.4's single-line rule says it dies.  The seq sibling refuses at the
resolving `:` (§8.2.1's key-at-sequence-column), the glued `:` at the
adjacent-value check (item 47), and the under-indented INTERIOR line at §8.1's
in-flow check — each the anchored twin's own verdict at the same mechanism. -/

#guard pins "k:\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k =VAL : +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "? a\n: 1\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "k:\n  m:\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +MAP =VAL :m =VAL : -MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "a: 1\n&p [b]: c\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] &p =VAL :b -SEQ =VAL :c -MAP -DOC -STR")
-- the value half: slot-offered → the deferred floor, at the open's position;
-- slot-completed → §9.2's dangling reading, the anchored twin's constructor
#guard pins "k:\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.underIndentedFlowContent 1 0", "ERR L4YAML.ScanError.underIndentedFlowContent 1 0")
#guard pins "k:\n&p [1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a: 1\n&p [1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a: 1\n&p [b]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a: 1\n[1]\nb: 2\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a: 1\n[1]\n: b\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  a: 1\n  [1, 2]\nz: 1\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
-- the twin-consistent refusals at the OTHER mechanisms
#guard pins "- a\n[1]: b\n" == ("scan-refused L4YAML.ScanError.trailingContent 1 0", "ERR L4YAML.ScanError.trailingContent 1 0")
#guard pins "- a\n&p [1]: b\n" == ("scan-refused L4YAML.ScanError.trailingContent 1 0", "ERR L4YAML.ScanError.trailingContent 1 0")
#guard pins "a: 1\n[1]:b\n" == ("scan-refused L4YAML.ScanError.unseparatedValue 1 3", "ERR L4YAML.ScanError.unseparatedValue 1 3")
#guard pins "a: 1\n[1,\n2]: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 2 0", "ERR L4YAML.ScanError.underIndentedFlowContent 2 0")
#guard pins "a: 1\n&p [1,\n2]: b\n" == ("scan-refused L4YAML.ScanError.underIndentedFlowContent 2 0", "ERR L4YAML.ScanError.underIndentedFlowContent 2 0")

/-! ## §5b  Item 183 — the flow open's domain, by PARK

`accum_flow_open_depth0` is the one holder of
`topLevelFlowResumeSep_or_refused`, and its nine park arms split three ways.
Six route WITHOUT the guard — `noPending` through `nodocFlowResumeSep` (item
136), `pendingDocStart` through the marker's own content slot (item 56, which
is also where a `%YAML` directive's stream arrives, its `---` leaving the same
park), `pendingDocEnd` through `suffixFlowResumeSep` (item 118), `pendingProps`
through the park's own route (items 9h/12/165), and `pendingBlock` /
`pendingMapValue` through the opaque resume at a nonzero index (item 24).  What
reaches the guard is `pendingContent`, `pendingBlockContent` — and `pendingFlow`.

**The two content parks' domain is scanner-REFUSED**, at `h_op = true` as at
`h_op = false`: a depth-0 `[`/`{` across a break behind a completed value is
§9.2's dangling run, refused at the run's own start.  That is measured below,
not forecast, and PyYAML 6.0.3 (`yaml.parse`) refuses every one of them at the
same line and column ("could not find expected ':'", or "expected
'<document start>'" where no level is open).  So the guard's LIVE payer at this
door is `pendingFlow` alone — the same state
`bareNodeRoute_or_refused_content`'s arms reached at item 174 — and what the
two content halves want is the item-157 treatment on the FLOW lane: a gate on
the frame's value route, refuted at the close.

The `...` rows follow `[211]`'s own `l-document-suffix+ l-document-prefix*
l-any-document?`, whose document slot admits a bare one; PyYAML requires a
`---` there, which is item 175's named suffix gap and not this item's. -/

-- paid arms: the six park constructors that never reach the guard
#guard pins "[1, 2]\n" == ("scan-accepted", "+STR +DOC +SEQ [] =VAL :1 =VAL :2 -SEQ -DOC -STR")
#guard pins "# c\n[1, 2]\n" == ("scan-accepted", "+STR +DOC +SEQ [] =VAL :1 =VAL :2 -SEQ -DOC -STR")
#guard pins "[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "---\n[1, 2]\n" == ("scan-accepted", "+STR +DOC --- +SEQ [] =VAL :1 =VAL :2 -SEQ -DOC -STR")
#guard pins "%YAML 1.2\n---\n[1, 2]\n" == ("scan-accepted", "+STR +DOC --- +SEQ [] =VAL :1 =VAL :2 -SEQ -DOC -STR")
#guard pins "---\n[1]: b\n" == ("scan-accepted", "+STR +DOC --- +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "...\n[1, 2]\n" == ("scan-accepted", "+STR +DOC +SEQ [] =VAL :1 =VAL :2 -SEQ -DOC -STR")
#guard pins "a: 1\n...\n[1, 2]\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 -MAP -DOC ... +DOC +SEQ [] =VAL :1 =VAL :2 -SEQ -DOC -STR")
#guard pins "...\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")
#guard pins "&p [1, 2]\n" == ("scan-accepted", "+STR +DOC +SEQ [] &p =VAL :1 =VAL :2 -SEQ -DOC -STR")
#guard pins "k: &p\n  [1, 2]\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :k +SEQ [] &p =VAL :1 =VAL :2 -SEQ -MAP -DOC -STR")
-- the two content parks: every member REFUSED, at the bracket's own position
#guard pins "a: 1\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "- a\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "k:\n  a: 1\n  [1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 2", "ERR L4YAML.ScanError.invalidBareDocument 2 2")
#guard pins "a: 1\n{x: 1}\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "- a\n- b\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
#guard pins "\"x\"\n[1, 2]\n" == ("scan-refused L4YAML.ScanError.invalidBareDocument 1 0", "ERR L4YAML.ScanError.invalidBareDocument 1 0")
#guard pins "a: 1\n# c\n[1, 2]\n" == ("scan-EOF-refused L4YAML.ScanError.invalidBareDocument 2 0", "ERR L4YAML.ScanError.invalidBareDocument 2 0")
-- …and the KEY half at the same park is accepted and resumes (item 176), which
-- is what says the refusals above are the VALUE reading and not the door
#guard pins "a: 1\n[1]: b\n" == ("scan-accepted", "+STR +DOC +MAP =VAL :a =VAL :1 +SEQ [] =VAL :1 -SEQ =VAL :b -MAP -DOC -STR")

/-! ## §6  The record

Per surviving arm, what the pins say it serves and what pays after the flip:

| arm | accepted domain (pinned) | post-flip reading |
|---|---|---|
| `rootMapRoute(F)_or_refused` at `h_op = true` (from `colon_open_map`, `question_open_map`, `content_dispatch_routed` ×2) | §1's sibling keys | the resume routes at the open level's frames — **the two openers CARRY the resume arm as of item 173** (`h_res_land`, first in the cascade) **and the props arm as of item 175** (`h_pr_land`, fifth — the sentinel `[96]` park's landed `:`/`?` heads the RUN's collection), paid by `pendingContent.h_framesS`, `pendingMapValue.h_frames` and `pendingProps.h_route`; what still reaches the guard is a landing whose park pays no face (the dedent-crossing colon sibling `a:⏎- x⏎: 2` and §3b's enclosing-park residues, the recorded ones) |
| `bareNodeRoute_or_refused` at `h_op = true` (from `accum_block_on_closeThenBlock`) | §1's sibling keys and open-sequence entries | same |
| `content_dispatch_after_close` | §1's siblings after an empty close (`k:⏎a: 1`) resume ALREADY (items 109/151 — the entry route threads `resumectx_of_landing` at all three callers, measured at item 174); ~~§4's scalar family (`k:⏎a`, its pendingMapValue caller)~~ **REFUSED at the scanner as of item 177**, so what the raw route itself still serves is §3b's rides | the sibling half is PAID; §4's half is REFUSED; ~~the props half~~ **PAID by item 174** (the ride context bypasses the route at the sentinel park) |
| the guards at `Or.inr` (parks with no `CompletedTail`) | ~~§4's family is the scalar half of what reaches them~~ — refused at the scanner as of item 177; `bareNodeRoute_or_refused_content`'s two arms' LIVE payers are `pendingFlow`'s break-crossed landings alone (measured at item 174: `pendingContent`/`pendingBlockContent` pay `Or.inl` and refute, the marker parks exit on their own arms) | shrinks further with R3's `pendingFlow` deletion; the sibling residue resumes |
| `accum_content_pending`'s pendingProps landing (via `content_dispatch_after_close`) | §3b's rides — the sentinel run's break-crossed node (`&p⏎b`, `&p⏎b: 1`, `&p⏎|⏎  x`) read as propsEmpty + a bare second document | **PAID by item 174**: `PropsRideRoute` carries the park's route + run, `content_dispatch_routed` assembles `[161]`/`[198]`/`[196]`'s props slots, and the enclosing-level park (`0 < n`) keeps propsEmpty + resume; residues = the indented-enclosing/two-park/alias punts pinned in §3b |
| `accum_block_pending`'s pendingProps landing (via `accum_block_on_closeThenBlock`) | §3b's indicator rides — the sentinel run's break-crossed `-`/`?`/`:` (`&p⏎- a`, `&p⏎? x⏎: v`, `&p⏎: v`) read as propsEmpty + a bare second document | **PAID by item 175**: `PropsNodeRoute` (the ride's landing half) rides the same park route into `[196]`'s slot — `propsSeqRoute` at the `-` arm's entries, `propsMapRoute(F)` as the openers' fifth cascade arm; the flow-open twin was paid on the FLOW lane at items 9h/12 (174's punt row for it struck at 175), and the enclosing-level park (`0 < n`) keeps propsEmpty + resume |
| `topLevelFlowResumeSep_or_refused` fallbacks, `flowKeyRoute_of_root` landing arm | §2's sibling flow keys (item 172's key half); **and §5b measures the COLLECTION route's own domain park by park** — six of the nine park arms route without the guard, the two content parks' inputs are scanner-refused at the bracket (PyYAML agrees at every position), so the guard's live payer at this door is `pendingFlow` alone | the key half **RESUMES as of item 176** (`h_mapF` at the landing arm, `resumeMapRoute` first in the cascade, paid by `pendingContent.h_framesS`/`pendingBlockContent.h_closeF`; the entries-level twin rides every arm, so the chains resume too); the value half is refused at the gate and the refuted arms cover it; what still reaches the fallback is a landing whose park pays no face (the marker-seed chain at `flowKeyRoute_of_open`'s twins, the seq-spaces sibling, §2's recorded punts) |
| ~~`flowKeyRoute_of_root` no-break arm~~ | the seed key (`[1]: b`) | **PAID by item 173**: the no-break arm's premise carries the virgin park's own `h_nodoc` face beside the column, so `nodocMapRoute` is the arm's only route and the raw `rootMapRoute` application is deleted — the census's `rootMapRoute` holder is gone |
| ~~`accum_content_pending`'s crossed arms~~ | NONE accepted (§3) — **and NONE scanner-reachable as of item 180**: the crossed-block clause (`crossedPropsExcessPos?`, §9.2's fourth reading) refuses the root family at the next landing or EOF, at the excess property's own position | **DELETED by item 181**: the pushed property is the third of an adjacent block, so the widened verdict is `some` and the relay's premise refutes — `h_routeX`, `PropsWindowCross` and the two raw `bareNodeRoute` payments are gone |
| `structural_dispatch_to_pending`, `DocumentProduction.stream_implicit_continue` | n/a — `SLAnyDocument.explicit` wrappers | deleted by the flip itself |
-/

end L4YAML.Tests.Guards.StreamFlipRemainderMap

end Blanket
