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

/-! # A landing after a block-scalar value resumes its level (DOCS item 112)

Items 109–111 taught `accum_content_pending`'s landing skeleton to resume, and
every paying arm folded the landing's `[79] s-l-comments` INTO the node it
transported — `[196]`'s flow-in-block ends with `s-l-comments`, so
`SBlockNode.flowInBlock` takes the walk as a constructor argument.  A block
scalar has no such tail: `[170]`/`[174]` end inside their own
`l-chomped-empty`, the node is complete at the PARK, and both
`accum_content_on_pendingMapValue` lemmas' (one lemma since item 179 —
the root instance folded into the indented twin) block-scalar arms punted every
landing face — `a: |⏎  x⏎c: d`'s `c` could still only re-enter as a second
bare document.

**The payment is item 95's closure, spent three faces wide.**  The absorption
closure (`dispatchContent_blockScalar_prod`'s third component, total since
item 97 refused the TAB stop) re-reads the scalar TO the landing — the walk
re-parents into `[169] l-trail-comments`' own `l-comment` rider — so the
transport face takes the node re-read instead of the node folded: `h_nodeAt`
once, then `h_vpack` (the `?` frame first, the park's twin after), `h_framesS`
(item 109's), and `h_framesV` (item 108's) are each one application.  The
root arm re-derives the closure (`dispatchContent_evidence` drops it); the
indented arm already held it.  The stream close is re-pointed at the same
re-read node, so it no longer needs `[211]`'s comment-suffix reading.

§1 is the family at the runtime; §2–§5 are the re-read, the spends, and the
subsumption at their types; §6 is what this item does not close. -/

namespace L4YAML.Tests.Guards.ScannerBlockScalarSiblingResumes

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

-- §1 The family.  A sibling after a block-scalar value: ONE `+DOC`, and `c`
-- is `a`'s sibling — the root mapping continues, level 0 resumed.
#guard emits "a: |\n  x\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]
-- The folded twin takes the same route ([174] reads through the same arm).
#guard emits "a: >\n  x\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL >x\\n", "=VAL :c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]
-- The indented twin: the inner mapping's level resumed at its own width.
#guard emits "k:\n  a: |\n    x\n  c: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :a", "=VAL |x\\n",
   "=VAL :c", "=VAL :d", "-MAP", "-MAP", "-DOC", "-STR"]
-- **The full thread**: `c` resumes the INNER level with two more below it,
-- and the NEXT landing pops to `k`'s — the stack the re-read node feeds.
#guard emits "k:\n  m:\n    a: |\n      x\n    c: d\n  n: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+MAP", "=VAL :a",
   "=VAL |x\\n", "=VAL :c", "=VAL :d", "-MAP", "=VAL :n", "=VAL :2", "-MAP",
   "-MAP", "-DOC", "-STR"]
-- The GAP is what the re-read absorbs: blank lines, comment lines, and both
-- mixed — `[169]`'s rider is `[78] l-comment`, `[79]`'s own unit.
#guard emits "a: |\n  x\n\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]
#guard emits "a: |\n  x\n# note\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]
#guard emits "a: |\n  x\n# note\n\n# more\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]
-- The VALUE LINE at the `?` frame (`h_vpack`'s `h_expl` branch): the scalar
-- is the frame's own KEY, root and nested.
#guard emits "? |\n  x\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL |x\\n", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  ? |\n    x\n  : v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL |x\\n", "=VAL :v",
   "-MAP", "-MAP", "-DOC", "-STR"]
-- A compact mapping inside an explicit key: the block-scalar-valued entry's
-- sibling resumes the compact level, then the `:` line closes the frame.
#guard emits "? a: |\n    x\n  c: d\n: v\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :c",
   "=VAL :d", "-MAP", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- The landed `:` as a SIBLING — an empty-key entry of the resumed level.
#guard emits "a: |\n  x\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL |x\\n", "=VAL :", "=VAL :v",
   "-MAP", "-DOC", "-STR"]

-- The boundaries.  A landing width that names no resumable level is refused
-- upstream — the membership test's deferred case has no input here either.
#guard refuses "a: |\n  x\n b: 2\n"
-- And a scalar whose content does not clear its own entry's width is refused
-- before any landing question arises: under `? a: |` the entry sits at 2, so
-- content at 2 is not a scalar body and the line re-reads as bare-document
-- content (§9.2).  The honest family indents the body past the entry.
#guard refuses "? a: |\n  x\n  c: d\n: v\n"

/-! ## §2 The re-read: one closure, every face's node

Item 95's absorption closure is TOTAL (item 97 refused the TAB stop), so the
walk between the park and the landing re-parents into the scalar's own
`[169]` slot and the node is available AT the landing — where the flow arm
folds its `s-l-comments` in, the block-scalar arm re-reads.  This is the
`h_nodeAt` both arms now hoist. -/

example {sp_scan sp_prep sp_scan' : SurfPos}
    (h_sep : SSeparate 0 .blockIn sp_scan sp_prep)
    (cl : ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
      SCLLiteral 0 sp_prep sp_mid ∨ SCLFolded 0 sp_prep sp_mid) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
      SBlockNode 0 .blockIn sp_scan sp_mid :=
  fun sp_mid h_ssl => (cl sp_mid h_ssl).elim
    (fun h_lit => literal_blockNode h_sep (GOpt.none sp_prep) h_lit)
    (fun h_fld => folded_blockNode h_sep (GOpt.none sp_prep) h_fld)

/-! ## §3 The frames spend: the transport face at the re-read node

`pendingMapValue.h_closeF` awaits a completed node; the re-read supplies one
per landing, so the park's `h_framesS` is one application — same for the
value-line bottom (`h_closeFV` → `h_framesV`). -/

example {sp_start sp_scan sp_scan' : SurfPos} {n : Nat} {ks : List FrameLevel}
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode n .blockIn sp_scan sp_m)
    (closeF : ∀ sp_mid : SurfPos, SBlockNode n .blockIn sp_scan sp_mid →
      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_mid) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_mid :=
  fun sp_mid h_ssl => closeF sp_mid (h_nodeAt sp_mid h_ssl)

example {sp_start sp_scan sp_scan' : SurfPos} {n nv : Nat} {ks : List FrameLevel}
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode n .blockIn sp_scan sp_m)
    (closeFV : ∀ sp_mid : SurfPos, SBlockNode n .blockIn sp_scan sp_mid →
      ResumeFrames (ExplValueLine sp_start nv) ks sp_mid) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
      ResumeFrames (ExplValueLine sp_start nv) ks sp_mid :=
  fun sp_mid h_ssl => closeFV sp_mid (h_nodeAt sp_mid h_ssl)

/-! ## §4 The value-line spend at the `?` frame

`? |⏎  x⏎: v`'s scalar is `[188]`'s KEY; the landing walk completes its
`s-l+block-indented` half through the re-read, and the frame's route closes
the ONE explicit entry — `h_vpack`'s `h_expl` branch, which both arms now pay
before falling to the park's twin. -/

example {sp_start sp_q sp_scan sp_scan' : SurfPos}
    (h_qlit : GLit '?' sp_q sp_scan)
    (route : ∀ sp_v : SurfPos, SBlockMapEntry 0 sp_q sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail 0 sp_v sp_e →
      SLYamlStream sp_start sp_e)
    -- Item 179: the key node reads at the SHIFTED index.
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode (0 + 1) .blockIn sp_scan sp_m) :
    ∀ sp_m sp_i sp_c : SurfPos, SSLComments sp_scan' sp_m →
      SIndent 0 sp_m sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v : SurfPos, SBlockIndented 0 .blockOut sp_c sp_v →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map 0] sp_v :=
  fun sp_m sp_i sp_c h_ssl h_ind h_lit sp_v h_sbi =>
    ResumeFrames.one (route sp_v (SBlockMapEntry.explicit 0 sp_q sp_scan sp_m sp_i sp_c sp_v
      h_qlit
      (SBlockIndented.node 0 .blockOut sp_scan sp_m
        (SBlockNode_blockIn_to_blockOut (h_nodeAt sp_m h_ssl)))
      h_ind h_lit h_sbi))

/-! ## §5 Nothing the park already said gets weaker

The stream close is the same application — `h_close_old` at the re-read node
— so the park's `h_closable` no longer needs `[211]`'s comment-suffix reading
(`ssl_comments_extend_stream`'s `GOpt.none`): the landing's comments live in
the scalar's own production, which is where the parser puts them. -/

example {sp_start sp_scan sp_scan' : SurfPos} {n : Nat}
    (h_close_old : ∀ sp : SurfPos, SBlockNode n .blockIn sp_scan sp →
      SLYamlStream sp_start sp)
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode n .blockIn sp_scan sp_m) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
      SLYamlStream sp_start sp_mid :=
  fun sp_mid h_ssl => h_close_old sp_mid (h_nodeAt sp_mid h_ssl)

/-! ## §6 What this item does NOT close

* The SEQUENCE side.  `accum_content_on_pendingBlock`'s block-scalar arms
  (root and indented; one lemma since item 179) close the entry and park `pendingContent` with every
  landing face punted, so `- |⏎  x⏎- y` and `k:⏎  - |⏎    x⏎  - y` (both
  runtime-accepted, ONE sequence) still re-open.  Two carriers wait there:
  an entry SIBLING rides the entries chain (`pendingBlockContent`'s park,
  item 110's shape), and a mapping-level landing rides the frames — both
  take this item's re-read at that lemma's own fields.  (CLOSED by item 113
  — both arms park `pendingBlockContent` with the re-read at every face.)
* `content_dispatch_routed`'s block-scalar arm — a landed scalar HEAD's own
  park; its landing faces still punt (`(Or.inr trivial)` ×3 at the build).
  (Item 113 gave it the re-read CLOSE and pinned the punts' inputs as
  refused — `|` heads no entry.)
* The props-decorated scalar parks (`accum_content_on_pendingProps`'s
  block-scalar arms) pay their value-line twin from the re-read but not the
  frames — the props park has no `h_closeF`/`h_frames` of its own to
  transport (item 111's residue).  (CLOSED by item 114.)
* The construction sites: `SLYamlStream.implicitContinue` still takes
  `GOpt SLAnyDocument` — item 110 measured the tightening at 16 sites, LAST. -/

end L4YAML.Tests.Guards.ScannerBlockScalarSiblingResumes

end Blanket
