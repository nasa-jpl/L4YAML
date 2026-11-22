module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The DEDENT composes as a sibling (DOCS item 99)

A landing that under-runs an indented pending's index ends the awaited entry:
the entry closes EMPTY (`[185]`'s comment form / `[72]`'s empty node) and the
landed content is a SIBLING at an enclosing mapping level — the parser emits
ONE outer mapping (`k:⏎  :⏎b: 2` is `{k: {null: null}, b: 2}`), never a
nested reading and never a refusal.  Item 64 LOCATED this landing
(`DedentLanding`, `KeyPackPunt.dedent`) and both consumers deferred it; item
99 drains the deferral at the two indented content arms
(`content_dispatch_after_close` off the e-noded close, the landing's own
`s-indent(j)` as the key context) and builds the frames the honest
entries-level cons needs (`ResumeFrames` — the still-open mapping levels,
each held as its `[195]`-tail continuation), which is where R4's
`implicitContinue`/`0 < m` tightening sends the equal-width sibling.

§1 pins the dedent family ACCEPTED with sibling-shaped events in both
pipelines; §2 the unmoved neighbors; §3 the standing refusals; §4 the frames
machinery at its types (at the STREAM bottom — item 108 made the bottom a
parameter without moving any of this). -/

namespace L4YAML.Tests.Guards.ScannerDedentSibling

open L4YAML L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover (FrameLevel)

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The dedent family: the entry ends empty, the landing is a SIBLING.
#guard emits "k:\n  :\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  -\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :", "-SEQ",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - x\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :x", "-SEQ",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - x\n  - y\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :x", "=VAL :y", "-SEQ",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a: 1\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :1", "-MAP",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The chained sibling, and a dedent landing that opens its own nest.
#guard emits "k:\n  :\nb: 2\nc: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL :b", "=VAL :2", "=VAL :c", "=VAL :3", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  :\nb:\n  c: 1\nd: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL :b", "+MAP", "=VAL :c", "=VAL :1", "-MAP", "=VAL :d", "=VAL :2",
   "-MAP", "-DOC", "-STR"]
-- Dedent to an INTERMEDIATE width: the sibling conses one level out, not at
-- the root.
#guard emits "a:\n  b:\n    -\n  c: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+SEQ", "=VAL :",
   "-SEQ", "=VAL :c", "=VAL :v", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "a:\n  b:\n    c: 1\n  d: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+MAP", "=VAL :c",
   "=VAL :1", "-MAP", "=VAL :d", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
-- The explicit key's e-node value, and decorated shapes.
#guard emits "k:\n  ? a\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL :", "-MAP",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  &p a: 1\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL &p :a", "=VAL :1",
   "-MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  :\n&q b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL &q :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - x\nb:\n  - y\nc: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :x", "-SEQ", "=VAL :b",
   "+SEQ", "=VAL :y", "-SEQ", "=VAL :c", "=VAL :3", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  :\n\"b\": 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL \"b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  :\nb : 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]

-- §2 Unmoved neighbors: the equal-width sibling (R4's case), the root
-- twin, the no-dedent entry, and the EOF close.
#guard emits "k:\n  :\n  b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :",
   "=VAL :b", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "k:\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :", "=VAL :b", "=VAL :2",
   "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :x", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "k:\n  :\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "-MAP", "-DOC", "-STR"]

-- §3 Standing refusals: a width matching no open level, a keyless scalar
-- sibling of a mapping, a `-` sibling at a mapping level, and the keyless
-- content sibling at EOF.
#guard refuses "k:\n  -\n a\n"
#guard refuses "k:\n  -\na\n"
#guard refuses "k:\n  - x\n- y\n"
#guard refuses "k:\n  :\nb\n"

-- §4 The frames machinery at its types: a two-level stack closes to the
-- fused stream, and the spend pops to the landing's own level.
example {sp_start sp : SurfPos} (h : ResumeFrames (SLYamlStream sp_start) [FrameLevel.map 2, FrameLevel.map 0] sp) :
    SLYamlStream sp_start sp := h.close

example {sp_start sp : SurfPos} (h : ResumeFrames (SLYamlStream sp_start) [FrameLevel.map 2, FrameLevel.map 0] sp) :
    ∃ ks', ResumeWidths [FrameLevel.map 2, FrameLevel.map 0] ks' 0 ∧
      (∀ sp_end, SCompactMapTail 0 sp sp_end →
        ResumeFrames (SLYamlStream sp_start) ks' sp_end) :=
  h.resumeAt (by decide)

/-- The level constructor demands the strict ordering, and this stack's bottom
    is the stream — the two invariants every producer of THIS instantiation
    pays.  The bottom became a parameter at item 108, where the same stack over
    the explicit frame's value line keeps a `?` open across a dedent
    (`ScannerDedentKeepsExplicitFrame`); everything here is that construct at
    `SLYamlStream sp_start` and is unchanged by it. -/
example {sp_start sp : SurfPos}
    (h_cont : ∀ sp_end, SCompactMapTail 3 sp sp_end →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map 1] sp_end) :
    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map 3, FrameLevel.map 1] sp :=
  ResumeFrames.level 3 [FrameLevel.map 1] sp (by decide) h_cont

/-- `rootMapRouteF` seeds the stack: the entry plus its whole tail close the
    root mapping over the bottomed stream. -/
example {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (hcol0 : sp_land.col = 0) (h_stream : SLYamlStream sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v →
    ∀ sp_e, SCompactMapTail k sp_v sp_e →
    ResumeFrames (SLYamlStream sp_start) [] sp_e :=
  rootMapRouteF hcol0 h_stream h_ind

end L4YAML.Tests.Guards.ScannerDedentSibling

end Blanket
