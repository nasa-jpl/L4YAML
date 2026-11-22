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

/-! # A landed key inside a `?` frame still owes the frame's value line (DOCS item 106)

`[186] c-l-block-map-explicit-key(n)`'s KEY is `s-l+block-indented(n,
block-out)`, and that production has TWO alternatives.  Items 92–96 paid the
frame's value line at the COMPACT one — `s-indent(m)` plus a compact
collection, so the key shares the `?`'s line (`? a: b⏎: - w`, `? - a⏎: - w`).
The other alternative is `[199] s-l+block-collection`: the key LANDS on a line
of its own, more indented than the `?` (`?⏎  a: b⏎: - w`).

Items 93 and 94 read that landing as frameless — "no compact alternative, so
no frame twins it" — and the first half is right for the wrong level.  The
SLOT has no compact alternative and never will; the FRAME is one level up, and
it is unchanged by which alternative its key took.  So the landed branch owes
exactly what the compact branch owes: `s-indent(n) ':'` and the value slot
(`[197] l-block-map-explicit-value(n)`), after which the `[188]` entry is
finished.

The route is the one the branch already builds.  `valueMapRoute` sends the
landed entry through `nestedBlockMap` into the node the pending awaits; the
twin sends the same `nestedBlockMap` into the frame's value line instead
(`explFrameValueLine`, derived once from the park's own `h_expl`).

Everything pinned below is RUNTIME behavior and none of it changed at this
item — no runtime file is touched.  The pins say what the proof's new payment
has to be consistent with; an escape is silent, so no runtime observation can
say which arm a given input takes. -/

namespace L4YAML.Tests.Guards.ScannerLandedNestingValueLine

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
  L4YAML.Proofs.NodeProduction

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def emitsOk (input : String) : Bool :=
  ( (Events.streamToEvents input).toOption.isSome
  , (Events.streamToEventsIx input).toOption.isSome ) == (true, true)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The MAP face: a landed implicit-key mapping as the `?`'s key, then the
-- frame's own value line one line further down.
#guard emits "?\n  a: b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- The value slot is `s-l+block-indented(n, block-out)` in full, so a compact
-- MAPPING sits there as readily as a compact sequence.
#guard emits "?\n  a: b\n: c: d\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "+MAP",
   "=VAL :c", "=VAL :d", "-MAP", "-MAP", "-DOC", "-STR"]
-- The key HEAD is `[188]`'s, so the quoted arm reaches the same route …
#guard emits "?\n  \"a\": b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL \"a", "=VAL :b", "-MAP", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- … and the landing width is the KEY's own, not a fixed one.
#guard emits "?\n   a: b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]

-- §2 The PROPS face — item 94's site, the same correction.  A `[96]` run in
-- front of the landed key changes the head and nothing else.
#guard emits "?\n  &p a: b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL &p :a", "=VAL :b", "-MAP", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "?\n  !t a: b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL <!t> :a", "=VAL :b", "-MAP", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "?\n  &p !t a: b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL &p <!t> :a", "=VAL :b", "-MAP", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]

-- §3 The SEQUENCE park's landed face.  A `-` inside the `?`'s key parks its
-- own pending, and the key that lands under THAT `-` reaches the same twin —
-- the entry's content wraps into the slot and the sequence tail is `nil`,
-- exactly as at the compact site item 92 pays.
#guard emits "? -\n    a: 1\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP",
   "-SEQ", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "? -\n    &p a: 1\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :1", "-MAP",
   "-SEQ", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]

-- §4 The frame the `?` itself sits in travels with the route, so the indented
-- twin is the same payment at a nonzero index.
#guard emits "k:\n  ?\n    a: b\n  : - w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "+MAP", "=VAL :a", "=VAL :b",
   "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emitsOk "k:\n  ? -\n      a: 1\n  : - w\n"

-- §5 The boundaries this payment must not move.
-- The COMPACT face, which items 92–96 already paid — unchanged.
#guard emits "? a: b\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "+SEQ",
   "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- The `[188]` value is optional, so the landed key alone is a whole entry and
-- the twin is never reached.
#guard emits "?\n  a: b\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "=VAL :",
   "-MAP", "-DOC", "-STR"]
-- A landing that UNDER-runs the `?`'s index is the dedent, and it never
-- reaches this branch: the runtime refuses this shape upstream.
#guard refuses "k:\n  ?\n    a: b\n: - w\n"
-- The SIBLING inside the landed key reads as one mapping with two entries —
-- accepted, and the twin's `SCompactMapTail` argument admits it — but the
-- second entry's composition is a residue this item does not close.  (~~`.cons`
-- still has no producer~~ — stale when written; item 99 gave it two at the
-- dedent branch's resume cons.  What blocks the sibling is the value-line twin
-- that branch cannot pay, `ResumeFrames` bottoming at the fused stream — item
-- 107's measurement, `BlockCollectionWidthFloor`.)
#guard emits "?\n  a: b\n  c: d\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]

/-! ## §6 The payment at its type

The twin is a derivation from the park's own explicit frame: fold the awaited
KEY node into `[186]`'s key slot, take `s-indent(n) ':'` and the value, hand
the finished `[188]` entry to the route the `?` producer already pays.  The
second argument is the park's own `h_kslot`, the frames it stands INSIDE —
~~so the two funders are one datum~~ and since item 196 both of them leave
together, as a chain the landing picks from by column. -/

-- 2026-10-30 (item 409): `explFrameValueLine` was deleted — its three callers pass the `?` park's
-- domained chain (`h_kslot`) straight to `entryKeyPack_of_dispatch`; the reader below it stays.

-- A `?` frame really does fund it, and this is the half that carries content:
-- the LEFT disjunct's payload is derivable from the frame alone.  (The
-- disjunction itself cannot be pinned by an equation — `∨ True` is a `Prop`,
-- so proof irrelevance would make any such pin vacuous.)
example {sp_start sp_scan sp_q : SurfPos} {n : Nat}
    (h_qlit : GLit '?' sp_q sp_scan)
    (route : ∀ sp_v : SurfPos, SBlockMapEntry n sp_q sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail n sp_v sp_e →
      SLYamlStream sp_start sp_e) :
    ∃ nv : Nat,
      ∀ sp_m : SurfPos, SBlockNode (n + 1) .blockIn sp_scan sp_m →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_m sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
      ResumeFrames (SLYamlStream sp_start) [L4YAML.Proofs.IndentStackCover.FrameLevel.map nv] sp_v :=
  ⟨n, fun sp_m h_node sp_i sp_c h_iv h_lit sp_v h_sbi =>
    ResumeFrames.one (route sp_v (SBlockMapEntry.explicit n sp_q sp_scan sp_m sp_i sp_c sp_v h_qlit
      (SBlockIndented.node n .blockOut sp_scan sp_m
        (SBlockNode_blockIn_to_blockOut h_node))
      h_iv h_lit h_sbi))⟩

end L4YAML.Tests.Guards.ScannerLandedNestingValueLine

end Blanket
