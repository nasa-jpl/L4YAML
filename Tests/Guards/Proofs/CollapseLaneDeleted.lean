module

public import L4YAML.Scanner.Scanner
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

/-! # The collapse lane was unreachable, and is deleted (DOCS item 126)

Item 46 gave the flow-stack invariant a third constructor for the arm that
could neither close nor refute: `FlowStackB.shape`, an open flow whose grammar
reading had been RENOUNCED, carrying depth, kinds, tail and one absorbing
close.  Items 50, 69, 72, 73, 82, 83 and 84 then refuted the renounce events
one at a time — the under-run at the flow open, the under-run in the interior,
the tab, and finally the floor made real at every park.

What no one checked is what that left.  Every construction of a `shape`
consumed a close taken OUT of a `shape` (`open_of_succ`'s right disjunct), and
the invariant is seeded at `nil`: so no reachable state carried one.  The lane
had no entrance, and its exits kept compiling — which is exactly why nothing
said so.  The measurement is the deletion: the constructor, `FlowStackK.collapse`,
the shape continuation the five flow indicators ran on it, and the nine splits
that dispatched on it come out, and the library builds unchanged, with zero
runtime edits.

**This corrects items 124 and 125.**  Both attributed a residue at the landed
`:` to "the collapse lane" — the restored register pair off a renounced flow
collection.  There is no such lane and there never was one at that landing.
The `?`-plus-flow-collection inputs ride the REAL flow lane, whose value slot
the open pays (`FlowBaseRoutes.vslot`) and the close converts
(`flowVPack_of_close`); what stays deferred is stated without the story, in
`UnderIndentInvariantMap`: a live register at the landing's own column with no
pack at that column.

§1 pins the constructor set; §2 that a positive depth is an OPEN one, with no
disjunction to dispatch on; §3 the flow families that ride the real lane. -/

namespace L4YAML.Tests.Guards.CollapseLaneDeleted

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

/-! ## §1  The constructor set

`FlowStackB` has TWO constructors.  A `match` that covers them is total, which
is what pins the deletion: were `shape` still there, this would not elaborate. -/

example {s0 : ScannerState} {sp_start : SurfPos} {n kc d : Nat} {ks km : Array Bool} {tl : FrameTail}
    {a b : SurfPos} (h : FlowStackB sp_start n kc none s0 d ks km tl a b) : True :=
  match h with
  | .nil _ _ => trivial
  | .«open» _ _ _ _ _ _ _ => trivial

/-! ## §2  A positive depth is an OPEN one

`open_of_succ` concludes the open stack outright.  The `example`'s ascribed
type is the pin: while the collapse existed this returned a disjunction, and
every consumer split on it. -/

example {s0 : ScannerState} {sp_start : SurfPos} {n kc d : Nat} {ks km : Array Bool} {tl : FrameTail}
    {a b : SurfPos} (h : FlowStackB sp_start n kc none s0 (d + 1) ks km tl a b) :
    FlowOpenStack sp_start n kc none s0 (d + 1) ks km tl a b := h.open_of_succ

/-! ## §3  The families that ride the real lane

The renounce events were a flow interior that under-ran its index and a scalar
token that crossed a line; these are their inputs, plus the four `[161]`
readings a depth-0 frame's routes serve (collection as implicit key, under a
`-`, property-headed, and as an explicit key).  Nothing here moved: the item
edits no runtime file. -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

-- The collection as an implicit key, by each of the three routes a depth-0
-- frame is opened from.
#guard emits "[1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
#guard emits "- [1]: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "&a [1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ [] &a", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]

-- …and as the EXPLICIT key, which is the `vslot` the open pays and the close
-- converts — the pair items 124/125 named the lane for.
#guard emits "? [1]\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :v", "-MAP",
   "-DOC", "-STR"]

-- The renounce events' own inputs: an interior that crosses a line between
-- entries, and a quoted scalar that crosses one inside a block value's flow.
#guard emits "[1,\n2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard emits "k:\n  a: [\"p\n     q\"]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "+SEQ []",
   "=VAL \"p q", "-SEQ", "-MAP", "-MAP", "-DOC", "-STR"]

-- The indented open, and the block value's flow — the two the collapse's
-- docstring named as composing through the resume at the pending's own index.
#guard emits "  - [1]\n"
  ["+STR", "+DOC", "+SEQ", "+SEQ []", "=VAL :1", "-SEQ", "-SEQ", "-DOC",
   "-STR"]
#guard emits "k: [1,2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ",
   "-MAP", "-DOC", "-STR"]

-- The two inputs `ParkFaceCoupling` §3 pinned as the lane's residue.  They are
-- accepted, they read as one explicit entry whose value is a compact map, and
-- what defers about them is a property of the landed `:`, not of the flow.
#guard emits "? [a]\n: b: c\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :a", "-SEQ", "+MAP", "=VAL :b",
   "=VAL :c", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "? {x: y}\n: b: c\n"
  ["+STR", "+DOC", "+MAP", "+MAP {}", "=VAL :x", "=VAL :y", "-MAP", "+MAP",
   "=VAL :b", "=VAL :c", "-MAP", "-MAP", "-DOC", "-STR"]

end L4YAML.Tests.Guards.CollapseLaneDeleted

end Blanket
