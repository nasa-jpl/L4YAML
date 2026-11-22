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

/-! # The props park keeps its context's holdings (DOCS item 114)

A `[96] c-ns-properties` run parks `pendingProps` where a node is awaited,
and until this item `h_route` — node in, whole stream out — was the only
closure the park carried: the ENTRY producers dropped their chain and frames
(the arm's own comment said "the entry closure is not carried, so a sibling
after `  - &a v` re-opens rather than snocs"), the MAPPING producers dropped
their node-domain frames, and every value completion parked `pendingContent`
with both resume faces punted.  So `k:⏎  - &p a⏎  - y` re-opened,
`k:⏎  - &p a⏎b: 2` could not pop, and `k:⏎  a: &p b⏎  c: d` lost the inner
level — where the runtime reads ONE collection in each.

**The build is five optional faces on the park, mirrored on the route's own
domain** so the awaited node folds in exactly as `h_route` folds it: the
entries-chain twin (`h_routeE`), the entry-level value-line pack with the
tail RIDING (`h_kslotE`, item 113's shape), the entry-level resume frames
(`h_closeFE`), and the mapping producers' node-domain pair
(`h_closeF`/`h_closeFV`).  The entry producers pay the first three from
their own fields, the mapping producers the last two; the run extensions
hand all five through verbatim.  Each value completion hoists the decorated
node at the landing ONCE — `[161] propsContent` around a flow value,
item 95's absorption closure through `[198]`'s props slot for a block
scalar — and parks `pendingBlockContent` when the entry chain rides, or
`pendingContent` with both frames faces paid when the mapping frames do.
A landing on the run itself closes `propsEmpty` and spends whichever face
the park holds at that node, so the landed key resumes instead of
re-opening.  Zero new lemmas, zero runtime edits.

§1 is the family at the runtime; §2–§5 are the node and the spends at their
types; §6 is what this item does not close. -/

namespace L4YAML.Tests.Guards.ScannerPropsParkSiblingResumes

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
  L4YAML.Proofs.NodeProduction
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

-- §1 The family.  The ENTRY side (`h_routeE`/`h_closeFE`): the decorated
-- entry's landing pops to the level the sequence stands in …
#guard emits "k:\n  - &p a\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &p :a", "-SEQ",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- … the sibling snocs the chain …
#guard emits "k:\n  - &p a\n  - y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &p :a", "=VAL :y",
   "-SEQ", "-MAP", "-DOC", "-STR"]
-- … and the full thread takes both faces off one park.
#guard emits "k:\n  - &p a\n  - y\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &p :a", "=VAL :y",
   "-SEQ", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The stack is a stack: the landing resumes the INNER level, the next pops.
#guard emits "k:\n  m:\n    - &p a\n  n: 2\no: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ",
   "=VAL &p :a", "-SEQ", "=VAL :n", "=VAL :2", "-MAP", "=VAL :o",
   "=VAL :3", "-MAP", "-DOC", "-STR"]
-- The tag twin rides the same arms, and a comment gap is absorbed.
#guard emits "k:\n  - !!str a\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ",
   "=VAL <tag:yaml.org,2002:str> :a", "-SEQ", "=VAL :b", "=VAL :2",
   "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - &p a\n# c\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &p :a", "-SEQ",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The ROOT entry's chain (`- &p a⏎- y` is ONE sequence).
#guard emits "- &p a\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL &p :a", "=VAL :y", "-SEQ", "-DOC", "-STR"]
-- The `?` frame's pack (`h_kslotE`): a nil tail, and the tail RIDING —
-- the sibling conses before the frame's `:` line spends.
#guard emits "? - &p a\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "=VAL &p :a", "-SEQ", "=VAL :v",
   "-MAP", "-DOC", "-STR"]
#guard emits "? - &p a\n  - y\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "=VAL &p :a", "=VAL :y", "-SEQ",
   "=VAL :v", "-MAP", "-DOC", "-STR"]
-- The props-slotted BLOCK SCALAR takes the same three faces through
-- item 95's absorption closure — the eager stream close is gone.
#guard emits "k:\n  - &p |\n    x\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &p |x\\n", "-SEQ",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - &p |\n    x\n  - y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL &p |x\\n", "=VAL :y",
   "-SEQ", "-MAP", "-DOC", "-STR"]

-- The MAPPING side (`h_closeF`/`h_closeFV`): the decorated value's
-- completion resumes the inner level …
#guard emits "k:\n  a: &p b\n  c: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL &p :b",
   "=VAL :c", "=VAL :d", "-MAP", "-MAP", "-DOC", "-STR"]
-- … or pops, and a blank-line gap rides.
#guard emits "k:\n  a: &p b\nc: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL &p :b",
   "-MAP", "=VAL :c", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a: &p b\n\n  c: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL &p :b",
   "=VAL :c", "=VAL :d", "-MAP", "-MAP", "-DOC", "-STR"]
-- The value-line bottom (`h_closeFV`): the landed `:` finds the `?`'s
-- entry open below the completed inner mapping.
#guard emits "?\n  a: &p b\n: v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL &p :b", "-MAP",
   "=VAL :v", "-MAP", "-DOC", "-STR"]
-- The full mapping thread, and the block-scalar value's twin.
#guard emits "k:\n  m:\n    a: &p b\n  n: 2\no: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+MAP",
   "=VAL :a", "=VAL &p :b", "-MAP", "=VAL :n", "=VAL :2", "-MAP",
   "=VAL :o", "=VAL :3", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a: &p |\n    x\n  c: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL &p |x\\n",
   "=VAL :c", "=VAL :d", "-MAP", "-MAP", "-DOC", "-STR"]

-- A landing on the RUN ITSELF closes it `propsEmpty` and spends the same
-- faces at that node: the entry pops, the mapping sibling resumes, and the
-- value line lands.
#guard emits "k:\n  m:\n    - &p\n  n: 2\no: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ",
   "=VAL &p :", "-SEQ", "=VAL :n", "=VAL :2", "-MAP", "=VAL :o",
   "=VAL :3", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  a: &p\n  c: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL &p :",
   "=VAL :c", "=VAL :d", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "?\n  a: &p\n: v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL &p :", "-MAP",
   "=VAL :v", "-MAP", "-DOC", "-STR"]

-- The boundaries.  A landing width that names no level is refused
-- (`trailingContent`), and so is a KEY at the entries' own width.
#guard refuses "k:\n  - &p a\n - y\n"
#guard refuses "k:\n  - &p a\n  b: 2\n"
-- The ROOT landing the root producers' frame punts would serve is refused.
#guard refuses "- &p a\nb: 2\n"
-- A `-` sibling after a mapping VALUE is `§9.2` bare-document content —
-- the mapping producers' entry-face punts have no input.
#guard refuses "k:\n  a: &p b\n  - y\n"
-- And the width-0 props-VALUE completions the ROUTED and root producers'
-- punts would serve are refused (`invalid implicit key` / `§9.2`).
#guard refuses "&p b\nc: 2\n"
#guard refuses "&p a\nb: 2\n"
#guard refuses "k:\n  a: 1\n&p b\nc: 2\n"

/-! ## §2 The decorated node at ANY landing

`[195] s-l+flow-in-block` folds the landing's `s-l-comments` into the node,
so the props-decorated value re-builds at every landing — one hoisted
closure, every face one application.  This is what lets the completion's
park keep faces stated over `SSLComments` at the park position. -/

example {sp_node sp_p sp_ne sp_scan' : SurfPos} {n : Nat}
    (h_sep : SSeparate n .flowOut sp_node sp_p)
    (h_fn : SFlowNode n .flowOut sp_p sp_ne)
    (h_tws : GStar SSWhite sp_ne sp_scan') :
    ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode n .blockIn sp_node sp_m :=
  fun _sp_m h_ssl =>
    flowInBlock_blockNode h_sep h_fn (white_prepend_SSLComments h_tws h_ssl)

/-! ## §3 The entries chain through the run

`h_routeE` is `pendingBlock.h_close_entry` mirrored on the route's domain:
the awaited node fills `[184]`'s slot and the collection's remaining tail
rides, so the completion's park keeps the chain — `pendingBlockContent`'s
`h_closable_entry`, which is TOTAL there, is one application of it. -/

example {sp_start sp_node sp_scan' : SurfPos} {n : Nat}
    (routeE : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ∀ sp_end : SurfPos, SCompactSeqTail n sp_m sp_end →
      SLYamlStream sp_start sp_end)
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode n .blockIn sp_node sp_m) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
    ∀ sp_end : SurfPos, SCompactSeqTail n sp_mid sp_end →
    SLYamlStream sp_start sp_end :=
  fun sp_mid h_ssl => routeE sp_mid (h_nodeAt sp_mid h_ssl)

/-! ## §4 The value-line pack with the tail RIDING

`h_kslotE` is the entry-level pack on the route's domain — the node closes
THIS entry, the sequence tail rides, and only then does the frame's `:`
line read (`? - &p a⏎  - y⏎: v`).  The park's older node-level `h_kslot`
is the nil-tail instance of it, so nothing weakens. -/

example {sp_start sp_node sp_scan' : SurfPos} {n nv : Nat}
    (kslotE : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ∀ sp_e : SurfPos, SCompactSeqTail n sp_m sp_e →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v)
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode n .blockIn sp_node sp_m) :
    -- The entry-level pack the completion pays `pendingBlockContent` …
    (∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
     ∀ sp_e : SurfPos, SCompactSeqTail n sp_m sp_e →
     ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
     ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
     ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v) ∧
    -- … subsumes the nil-tail reading the old field could state.
    (∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
     ∀ sp_i sp_c : SurfPos, SIndent nv sp_m sp_i → GLit ':' sp_i sp_c →
     ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
     ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v) :=
  ⟨fun sp_m h_ssl sp_e h_tail sp_i sp_c h_iv h_lit sp_v h_sbi =>
    kslotE sp_m (h_nodeAt sp_m h_ssl) sp_e h_tail sp_i sp_c h_iv h_lit sp_v h_sbi,
   fun sp_m h_bn sp_i sp_c h_iv h_lit sp_v h_sbi =>
    kslotE sp_m h_bn sp_m (SCompactSeqTail.nil n sp_m)
      sp_i sp_c h_iv h_lit sp_v h_sbi⟩

/-! ## §5 The frames: three spends off two shapes

The entry face (`h_closeFE`) funds `pendingBlockContent.h_closeF` by one
application; the mapping face (`h_closeF`, `pendingMapValue.h_closeF`'s
`FrameLevel.map n :: ks` instance) funds `pendingContent.h_framesS` the same way; and a
landing on the run itself spends either at the `propsEmpty` node — which is
how `resumectx_of_landing` receives a real stack from this park. -/

example {sp_start sp_node sp_scan' : SurfPos} {n : Nat} {ks : List FrameLevel}
    (closeFE : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ∀ sp_end : SurfPos, SCompactSeqTail n sp_m sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end)
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode n .blockIn sp_node sp_m) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
    ∀ sp_end : SurfPos, SCompactSeqTail n sp_mid sp_end →
    ResumeFrames (SLYamlStream sp_start) ks sp_end :=
  fun sp_mid h_ssl => closeFE sp_mid (h_nodeAt sp_mid h_ssl)

example {sp_start sp_node sp_scan' : SurfPos} {n : Nat} {ks : List FrameLevel}
    (closeF : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ResumeFrames (SLYamlStream sp_start) ks sp_m)
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode n .blockIn sp_node sp_m) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
    ResumeFrames (SLYamlStream sp_start) ks sp_mid :=
  fun sp_mid h_ssl => closeF sp_mid (h_nodeAt sp_mid h_ssl)

-- The landing spend: the run closes `propsEmpty` on the landing's own
-- comments, the entry closes around it with a nil tail, and the levels
-- below stand ready — the `SSLComments`-domain shape the landing skeleton's
-- resume context asks for.
example {sp_start sp_node sp_p sp_scan : SurfPos} {n : Nat} {ks : List FrameLevel}
    {ha ht : Bool}
    (h_sep : SSeparateLines n sp_node sp_p)
    (h_run : PropsRun n .flowOut ha ht sp_p sp_scan)
    (closeFE : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ∀ sp_end : SurfPos, SCompactSeqTail n sp_m sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) :
    ∀ sp_m : SurfPos, SSLComments sp_scan sp_m →
    ResumeFrames (SLYamlStream sp_start) ks sp_m :=
  fun sp_m h_ssl =>
    closeFE sp_m
      (flowInBlock_blockNode h_sep
        (SFlowNode.propsEmpty n .flowOut sp_p sp_scan h_run.toProperties) h_ssl)
      sp_m (SCompactSeqTail.nil n sp_m)

/-! ## §6 What this item does NOT close

* `entryPropsKeyPack_of_dispatch`'s two build sites still punt the pack's
  resume twins — the landed props-headed KEY under an explicit frame
  (`?⏎  &p a: b⏎  c: d⏎: - w`) waits on `entryKeyPack`'s four threaded
  premises transposed to props (item 111's second residue, unchanged).
  (CLOSED by item 115 — the four premises transposed, the landed branch
  paying strictly-deeper and the dedent branch popping; the compact
  branch's punt is item 99's shared residue.)
* The flow OPEN's props arm still drops the pack's twins at
  `FlowBaseRoutes.key` (67b's carrier, `&p [1]: b` at a resumed landing).
* The ROUTED producers' five faces punt with no input — a landed run's
  decorated VALUE at column 0 is refused (§1) — and the ROOT producers'
  frame faces likewise (`- &p a⏎b: 2` is `trailingContent`).
* The construction sites: `SLYamlStream.implicitContinue` still takes
  `GOpt SLAnyDocument` — item 110 measured the tightening at 16 sites,
  LAST. -/

end L4YAML.Tests.Guards.ScannerPropsParkSiblingResumes

end Blanket
