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

/-! # A dedent inside an explicit key keeps the frame (DOCS item 108)

Item 99 gave the landing a stack of still-open mapping levels (`ResumeFrames`)
and bottomed it at the finished stream, which is what its own inputs need:
`k:⏎  :⏎b: 2`'s `b` is a sibling in the ROOT mapping and the root mapping ends
in the stream.  Inside a `[186]` explicit KEY the same landing needs the same
stack over a different bottom.  `?⏎  a:⏎    b:⏎  c: 2⏎: - w` reads `c` as a
sibling of `a` — both entries of the mapping that IS the `?`'s key — and the
`?` entry has not been closed at that point: it still owes `[190] s-indent(nv)
':' s-l+block-indented(nv, block-out)`, the value line `: - w` supplies.  A
stack bottomed at the stream cannot say that, and not because the bottom is
hard to reach: the `?` entry is closed with `[188]`'s `e-node` value INSIDE the
outermost level's own continuation, so by the time the bottom is reached the
frame is already spent.

So the bottom is a parameter now (`ResumeFrames (P : SurfPos → Prop)`), and the
value-line bottom is `ExplValueLine`.  The two stacks are genuinely different
objects, not one stack read two ways: under `?⏎  a:` the stream stack is
`[2, 0]` (the key's own level, then the mapping the `?` entry sits in) and the
value-line stack is `[2]` (the key's level, and below it the `?`'s unpaid value
rather than an open level).  Both ride the pending, both pop at a dedent, and a
landing width can name a level in one and not the other.

§1 pins the family at the runtime; §2–§5 are the payment at its types, from the
`?` producer's bottom to the dedent branch's spend; §6 is what the item does
NOT close. -/

namespace L4YAML.Tests.Guards.ScannerDedentKeepsExplicitFrame

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

-- §1 The family: a landing INSIDE an explicit key that under-runs the awaited
-- value's index is a sibling at an enclosing level of the key's own mapping,
-- and the `?` entry is still open when its `:` line arrives.
#guard emits "?\n  a:\n    b:\n  c: 2\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :",
   "-MAP", "=VAL :c", "=VAL :2", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP",
   "-DOC", "-STR"]
#guard emits "?\n  a:\n    b: 1\n  c: 2\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :1",
   "-MAP", "=VAL :c", "=VAL :2", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- The value slot is `s-l+block-indented` in full, so a mapping sits there too.
#guard emits "?\n  a:\n    b: 1\n  c: 2\n: d: e\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :1",
   "-MAP", "=VAL :c", "=VAL :2", "-MAP", "+MAP", "=VAL :d", "=VAL :e", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- Two levels of dedent inside the key, and a chain of siblings after it.
#guard emits "?\n  a:\n    b:\n      c: 1\n  d: 2\n  e: 3\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "+MAP",
   "=VAL :c", "=VAL :1", "-MAP", "-MAP", "=VAL :d", "=VAL :2", "=VAL :e",
   "=VAL :3", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- The quoted key head reaches the same landing.
#guard emits "?\n  a:\n    b: 1\n  \"c\": 2\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "+MAP", "=VAL :b", "=VAL :1",
   "-MAP", "=VAL \"c", "=VAL :2", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- Unmoved neighbors: the same shapes with no `?` (item 99's own family), and
-- the key with no dedent in it (item 106's).
#guard emits "k:\n  a:\n    b: 1\n  c: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+MAP", "=VAL :b",
   "=VAL :1", "-MAP", "=VAL :c", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "?\n  a: b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- A landing that under-runs the `?` itself leaves the key: still refused.
#guard refuses "k:\n  ?\n    a:\n      b: 1\n c: 2\n  : - w\n"

/-! ## §2 The bottom is a parameter

Item 99's stack is the instantiation at the stream, unchanged, and `close`
reaches whatever the bottom holds. -/

example {sp_start sp : SurfPos} (h : ResumeFrames (SLYamlStream sp_start) [FrameLevel.map 2, FrameLevel.map 0] sp) :
    SLYamlStream sp_start sp := h.close

example {sp_start : SurfPos} {nv : Nat} {sp : SurfPos}
    (h : ResumeFrames (ExplValueLine sp_start nv) [FrameLevel.map 2] sp) :
    ExplValueLine sp_start nv sp := h.close

/-- And the value-line bottom is exactly the twin item 93 wrote inline: closing
    the stack leaves `s-indent(nv) ':'` and the value slot still to read. -/
example {sp_start : SurfPos} {nv : Nat} {sp_e : SurfPos}
    (h : ResumeFrames (ExplValueLine sp_start nv) [] sp_e) :
    ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
    ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w := h.close

/-! ## §3 The `?` producer's bottom

`question_open_map` already holds the route ANY `[188]` entry at its column
takes to the stream (`h_expl`, item 51).  Read through `[188]`'s `explicit`
alternative instead of `explicitEmpty`, that route IS the value-line bottom —
and the stack over it is EMPTY, because below the `?` there is no open mapping
level, only this entry's unpaid value. -/

example {sp_start sp_q sp_scan sp_v : SurfPos} {k : Nat}
    (h_qlit : GLit '?' sp_q sp_scan)
    -- Item 371: the route carries its TAIL — the mapping the `?` heads may go
    -- on with siblings after the value — and the bottom is one level deep.
    (route : ∀ sp_x : SurfPos, SBlockMapEntry k sp_q sp_x →
      ∀ sp_e : SurfPos, SCompactMapTail k sp_x sp_e → SLYamlStream sp_start sp_e)
    (h_key : SBlockIndented k .blockOut sp_scan sp_v) :
    ResumeFrames (ExplValueLine sp_start k) [] sp_v :=
  ResumeFrames.bottom sp_v
    (fun sp_i sp_c h_iv h_colon sp_w h_sbi =>
      ResumeFrames.one (route sp_w
        (SBlockMapEntry.explicit k sp_q sp_scan sp_v sp_i sp_c sp_w h_qlit h_key
          h_iv h_colon h_sbi)))

/-! ## §4 The threading hop

Each implicit `:` beneath the frame pushes its own entry's level onto the
value-line stack, exactly as it pushes onto the stream stack — the entry, then
the level's remaining tail, then whatever the pack carried. -/

-- 2026-11-10 (item 473, option (A)): the level constructors' bound and the park faces read `≤` (the root frame
-- stands under a column-0 opener's own level), `ResumeWidths` names the survivors positionally and `ResumeWidths.lt`
-- is `ResumeWidths.le`; the rows below restate the faces they mirror — a shape move, no obligation changed.
example {sp_start sp_key : SurfPos} {k nv : Nat} {ks : List FrameLevel}
    (h_lt : ∀ fr ∈ ks, fr.width ≤ k)
    (routeFV : ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
      ResumeFrames (ExplValueLine sp_start nv) ks sp_e)
    {sp_mid : SurfPos} (h_entry : SBlockMapEntry k sp_key sp_mid) :
    ResumeFrames (ExplValueLine sp_start nv) (FrameLevel.map k :: ks) sp_mid :=
  ResumeFrames.level k ks sp_mid h_lt
    (fun sp_end h_tail => routeFV sp_mid h_entry sp_end h_tail)

/-! ## §5 The dedent's spend

This is the payment item 99 could not make.  The landing pops the value-line
stack to its own level and conses the landed entry there; closing what is left
lands on the frame's value line, which is the pack's value-line twin —
`?⏎  a:⏎    b:⏎  c: 2⏎: - w`'s `c` with the `?` still open behind it. -/

example {sp_start sp_mid sp_land : SurfPos} {nv w : Nat} {ks : List FrameLevel}
    (frames : ResumeFrames (ExplValueLine sp_start nv) ks sp_mid)
    (hmem : FrameLevel.map w ∈ ks)
    (h_ind : SIndent w sp_mid sp_land) :
    ∀ sp_v : SurfPos, SBlockMapEntry w sp_land sp_v →
    ∀ sp_e : SurfPos, SCompactMapTail w sp_v sp_e →
    ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
    ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w :=
  match frames.resumeAt hmem with
  | ⟨_, _, cont⟩ =>
      fun sp_v h_entry sp_e h_tail =>
        (cont sp_e (SCompactMapTail.cons w sp_mid sp_land sp_v sp_e h_ind h_entry h_tail)).close

/-- The membership is the whole of the branch's decision, and it is taken
    SEPARATELY on the two stacks: the stream stack carries levels the
    value-line stack does not (the ones the `?` entry itself sits in), so a
    landing can name a level in one and not the other.  `resumeAt` is what
    refuses the rest. -/
example {sp_start : SurfPos} {nv : Nat} {sp : SurfPos}
    (h : ResumeFrames (ExplValueLine sp_start nv) [FrameLevel.map 4, FrameLevel.map 2] sp) :
    ∃ ks', ResumeWidths [FrameLevel.map 4, FrameLevel.map 2] ks' 2 ∧
      (∀ sp_end, SCompactMapTail 2 sp sp_end →
        ResumeFrames (ExplValueLine sp_start nv) ks' sp_end) :=
  h.resumeAt (by decide)

/-! ## §6 What this does NOT close

The sibling whose landing follows COMPLETED content — `? a: b⏎  c: d⏎: e`,
`?⏎  a: b⏎  c: d⏎: - w` — never reaches the branch above.  Those park a
`pendingContent`, and every parked constructor's break-crossed landing goes
through one shared skeleton (`h_defer_split` inside `accum_content_pending`):
close with `close_with_ssl`, then `content_dispatch_after_close` with a ROOT
key context, which re-opens the landed key as a fresh bare document through
`[211]`'s `implicitContinue`.  The frames are not consulted there at all, and
the park's `h_vpack` — the `?` frame it was holding — is discarded with the
close.  That path is row 19's `implicitContinue` (1c), not this branch. -/

#guard emits "?\n  a: b\n  c: d\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "? a: b\n  c: d\n: e\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "=VAL :e", "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.ScannerDedentKeepsExplicitFrame

end Blanket
