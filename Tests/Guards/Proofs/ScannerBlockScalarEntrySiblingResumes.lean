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

/-! # A block ENTRY's block-scalar value keeps the entries chain (DOCS item 113)

Item 112 paid the MAPPING-value block-scalar arms with item 95's absorption
closure — the scalar re-read TO the landing.  The sequence side still dropped
its park: `accum_content_on_pendingBlock`'s (since item 179, the indented
lemma's) block-scalar arms closed the entry
and parked plain `pendingContent`, so `- |⏎  x⏎- y`'s second `-` could only
re-open through `[211]`'s bare-document continuation, and
`k:⏎  - |⏎    x⏎b: 2`'s landing could not pop to `k`'s level.  The runtime
reads ONE sequence in both.

**The build is the flow arm's park with the re-read in place of the fold.**
Both arms now park `pendingBlockContent` — the entries-chain park the flow and
multi-line arms have used since items 99/110 — with `h_nodeAt` hoisted once
and every face one application: the two entry-level closures (`h_closable` /
`h_closable_entry`, the sibling `-`'s snoc), the entry-level value-line pack
(`h_kslot`, whose sequence tail now RIDES where item 95's content park could
only close it `nil`), and `h_close_entry_old`'s resume face (`h_closeF`,
item 110's landing spend).  `content_dispatch_routed`'s block-scalar arm takes
the same re-read at its own route, dropping the last document-suffix reading a
completed scalar forced.  Zero new lemmas, zero runtime edits.

§1 is the family at the runtime; §2–§5 are the re-read and the three spends at
their types; §6 is what this item does not close. -/

namespace L4YAML.Tests.Guards.ScannerBlockScalarEntrySiblingResumes

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

-- §1 The family.  A sibling `-` after a block-scalar entry: ONE `+SEQ`, the
-- entries chain carried across the scalar.
#guard emits "- |\n  x\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |x\\n", "=VAL :y", "-SEQ", "-DOC", "-STR"]
-- The folded twin takes the same route ([174] reads through the same arm).
#guard emits "- >\n  x\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL >x\\n", "=VAL :y", "-SEQ", "-DOC", "-STR"]
-- The GAP is what the re-read absorbs — blank and comment lines re-parent
-- into the scalar's own `[169]` slot before the sibling's line.
#guard emits "- |\n  x\n\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |x\\n", "=VAL :y", "-SEQ", "-DOC", "-STR"]
#guard emits "- |\n  x\n# c\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL |x\\n", "=VAL :y", "-SEQ", "-DOC", "-STR"]
-- The indented twin: the sibling snocs at the entry's own width, inside the
-- mapping the sequence is the value of.
#guard emits "k:\n  - |\n    x\n  - y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL |x\\n", "=VAL :y",
   "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  - |\n    x\n# c\n  - y\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL |x\\n", "=VAL :y",
   "-SEQ", "-MAP", "-DOC", "-STR"]
-- The mapping LANDING (`h_closeF`, item 110's spend): the landing ends the
-- sequence and pops to the level it stands in — `b` is `k`'s sibling.
#guard emits "k:\n  - |\n    x\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL |x\\n", "-SEQ",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- **The full thread**: the sibling snocs first, then the landing pops — one
-- park hands out both faces.
#guard emits "k:\n  - |\n    x\n  - y\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL |x\\n", "=VAL :y",
   "-SEQ", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The stack is a stack: two open mapping levels below the sequence, and the
-- landing resumes the INNER one, then the next pops to the root.
#guard emits "k:\n  m:\n    - |\n      x\n  n: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ", "=VAL |x\\n",
   "-SEQ", "=VAL :n", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  m:\n    - |\n      x\n    - y\n  n: 2\no: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ", "=VAL |x\\n",
   "=VAL :y", "-SEQ", "=VAL :n", "=VAL :2", "-MAP", "=VAL :o", "=VAL :3",
   "-MAP", "-DOC", "-STR"]
-- The `?` frame's compact sequence (`h_kslot`): the frame's `:` line closes
-- the entry through the pack — with a `nil` tail …
#guard emits "? - |\n    x\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "=VAL |x\\n", "-SEQ", "=VAL :v", "-MAP",
   "-DOC", "-STR"]
-- … and with the tail RIDING: the sibling conses before the frame's `:` line
-- spends, which is what sizing the pack at the ENTRY level bought.
#guard emits "? - |\n    x\n  - y\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "=VAL |x\\n", "=VAL :y", "-SEQ",
   "=VAL :v", "-MAP", "-DOC", "-STR"]
-- The landed sequence inside an explicit key takes the same sibling.
#guard emits "?\n  - |\n    x\n  - y\n: v\n"
  ["+STR", "+DOC", "+MAP", "+SEQ", "=VAL |x\\n", "=VAL :y", "-SEQ",
   "=VAL :v", "-MAP", "-DOC", "-STR"]

-- The boundaries.  A ROOT sequence stands inside no mapping level, so the
-- landing that would spend the root arm's `h_closeF` is refused — its punt
-- costs nothing (item 110's root note, transposed).
#guard refuses "- |\n  x\nb: 2\n"
-- A landing width that names no resumable level is refused upstream, at the
-- root (§9.2) and landed (`trailingContent`) parks alike.
#guard refuses "- |\n  x\n - y\n"
#guard refuses "k:\n  - |\n    x\n - y\n"
-- And a KEY at the entries' own width continues nothing — the sequence is
-- the value already standing there.
#guard refuses "k:\n  - |\n    x\n  b: 2\n"
-- `content_dispatch_routed`'s own residual faces have no input either: a
-- landed block scalar heads no entry (`|` is no key head), so a scalar at a
-- landing inside open levels is bare-document content.
#guard refuses "k:\n  a: 1\n|\n  x\n"
#guard refuses "k:\n  a: 1\n  |\n    x\n"

/-! ## §2 The re-read at the ENTRY: one closure, both entry-level closures

Item 95's closure re-reads the scalar to the landing; `[184]`'s slot wraps it
in `SBlockIndented.node`, so the park keeps the stream close AND the
entries-level one — the pair `pendingBlockContent` was built to carry
(item 99), which the block-scalar arm could not fill before. -/

example {sp_scan sp_prep sp_scan' : SurfPos} {n : Nat}
    -- Item 179: the scalar and its separator read at the SHIFTED index; the
    -- entry slot stays raw.
    (h_sep : SSeparate (n + 1) .blockIn sp_scan sp_prep)
    (cl : ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
      SCLLiteral (n + 1) sp_prep sp_mid ∨ SCLFolded (n + 1) sp_prep sp_mid) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
      SBlockIndented n .blockIn sp_scan sp_mid :=
  fun sp_mid h_ssl =>
    SBlockIndented.node n .blockIn sp_scan sp_mid
      ((cl sp_mid h_ssl).elim
        (fun h_lit => literal_blockNode h_sep (GOpt.none sp_prep) h_lit)
        (fun h_fld => folded_blockNode h_sep (GOpt.none sp_prep) h_fld))

/-! ## §3 The entries-chain spend

`h_close_entry_old` is the park's own snoc route — the entry's content plus
`[183]`'s remaining tail.  The re-read node fills the content slot at every
landing, so a sibling `-` extends the collection across the scalar exactly as
it does across a flow value. -/

example {sp_start sp_scan sp_scan' : SurfPos} {n : Nat}
    (h_close_entry_old : ∀ sp : SurfPos, SBlockIndented n .blockIn sp_scan sp →
      ∀ sp_end : SurfPos, SCompactSeqTail n sp sp_end → SLYamlStream sp_start sp_end)
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode (n + 1) .blockIn sp_scan sp_m) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
    ∀ sp_end : SurfPos, SCompactSeqTail n sp_mid sp_end →
    SLYamlStream sp_start sp_end :=
  fun sp_mid h_ssl =>
    h_close_entry_old sp_mid
      (SBlockIndented.node n .blockIn sp_scan sp_mid (h_nodeAt sp_mid h_ssl))

/-! ## §4 The value-line pack with the tail RIDING

`pendingBlockContent.h_kslot` is stated at the entry level — the landing
closes THIS entry, `[183]`'s remaining tail rides, and only then does the
frame's `:` line read.  Item 95's content park forced the tail `nil` at the
park; the entry-level pack recovers `? - |⏎    x⏎  - y⏎: v`'s sibling, and
the `nil` instance IS the old reading. -/

example {sp_start sp_scan sp_scan' : SurfPos} {n nv : Nat}
    (kslot : ∀ sp_m : SurfPos, SBlockIndented n .blockIn sp_scan sp_m →
      ∀ sp_e : SurfPos, SCompactSeqTail n sp_m sp_e →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v)
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode (n + 1) .blockIn sp_scan sp_m) :
    -- The entry-level pack (what the arm now pays) …
    (∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
     ∀ sp_e : SurfPos, SCompactSeqTail n sp_m sp_e →
     ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
     ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
     ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v) ∧
    -- … subsumes the nil-tail reading (what item 95's park could say).
    (∀ sp_m sp_i sp_c : SurfPos, SSLComments sp_scan' sp_m →
     SIndent nv sp_m sp_i → GLit ':' sp_i sp_c →
     ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
     ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v) :=
  have pack : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      ∀ sp_e : SurfPos, SCompactSeqTail n sp_m sp_e →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_e sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v :=
    fun sp_m h_ssl sp_e h_tail sp_i sp_c h_iv h_lit sp_v h_sbi =>
      kslot sp_m
        (SBlockIndented.node n .blockIn sp_scan sp_m (h_nodeAt sp_m h_ssl))
        sp_e h_tail sp_i sp_c h_iv h_lit sp_v h_sbi
  ⟨pack, fun sp_m sp_i sp_c h_ssl h_iv h_lit sp_v h_sbi =>
    pack sp_m h_ssl sp_m (SCompactSeqTail.nil n sp_m) sp_i sp_c h_iv h_lit sp_v h_sbi⟩

/-! ## §5 The frames spend, and the routed close

`pendingBlock.h_closeF` awaits the entry's content; the re-read supplies it
per landing and the tail rides by partial application — item 110's landing
spend then pops `k:⏎  - |⏎    x⏎b: 2` to `k`'s level.  And a route applied
at the re-read node IS the stream close, with no `[211]` comment-suffix
reading left over — the landing's comments live in the scalar's own
production, where the parser puts them. -/

example {sp_start sp_scan sp_scan' : SurfPos} {n : Nat} {ks : List FrameLevel}
    (closeF : ∀ sp_mid : SurfPos, SBlockIndented n .blockIn sp_scan sp_mid →
      ∀ sp_end : SurfPos, SCompactSeqTail n sp_mid sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end)
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode (n + 1) .blockIn sp_scan sp_m) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
    ∀ sp_end : SurfPos, SCompactSeqTail n sp_mid sp_end →
    ResumeFrames (SLYamlStream sp_start) ks sp_end :=
  fun sp_mid h_ssl =>
    closeF sp_mid
      (SBlockIndented.node n .blockIn sp_scan sp_mid (h_nodeAt sp_mid h_ssl))

example {sp_start sp_anchor sp_scan' : SurfPos}
    (h_route : ∀ sp_m : SurfPos, SBlockNode 0 .blockIn sp_anchor sp_m →
      SLYamlStream sp_start sp_m)
    (h_nodeAt : ∀ sp_m : SurfPos, SSLComments sp_scan' sp_m →
      SBlockNode 0 .blockIn sp_anchor sp_m) :
    ∀ sp_mid : SurfPos, SSLComments sp_scan' sp_mid →
      SLYamlStream sp_start sp_mid :=
  fun sp_mid h_ssl => h_route sp_mid (h_nodeAt sp_mid h_ssl)

/-! ## §6 What this item does NOT close

* `content_dispatch_routed`'s block-scalar arm still punts its value-line and
  frames faces — §1 pins both landed-scalar inputs as refused (`|` heads no
  entry), so the punts have no input; what the arm gained is the re-read
  close.
* The ROOT arm's `h_kslot`/`h_closeF` punts, same status: a column-0 `-`
  owns no `?` frame, and `- |⏎  x⏎b: 2` is `trailingContent` (§1).
* The props-decorated scalar parks (`accum_content_on_pendingProps`'s
  block-scalar arms) pay their value-line twin from the re-read but not the
  frames — the props park has no `h_closeF`/`h_frames` of its own to
  transport (item 111's residue).  (CLOSED by item 114 — the park carries
  five resume faces and every value completion pays them.)
* The construction sites: `SLYamlStream.implicitContinue` still takes
  `GOpt SLAnyDocument` — item 110 measured the tightening at 16 sites, LAST. -/

end L4YAML.Tests.Guards.ScannerBlockScalarEntrySiblingResumes

end Blanket
