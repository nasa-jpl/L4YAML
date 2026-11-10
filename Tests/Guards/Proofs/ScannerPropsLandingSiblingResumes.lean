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

/-! # A landing whose key head is a `[96]` property run resumes its level (DOCS item 111)

Items 109/110 gave `accum_content_pending`'s landing skeleton the frames and
spent them wherever the landed key head was CONTENT — but a landing that opens
on `&`/`!` parks `pendingProps`, and `content_dispatch_routed`'s `h_props_key`
still read only the ROOT key context.  So `k:⏎  - a⏎&p b: 2`'s landing could
be given `b`'s entry only as a fresh `[187]` under a second bare document,
`[211]`'s `implicitContinue` — the third over-approximation, one construct
over from the two already paid.

**The build is the sibling move made once more.**  `PropsKeyPack` gains the two
RESUME twins `ImplicitKeyPack` has carried since items 99/108, stated at the
run's start; `h_props_key` assembles the pack from whichever context has a
route, resuming first (`h_buildP`, item 109's `h_build` on the sibling pack);
the run-extension and content arms hand the twins through untouched — the
pack's payload IS `ImplicitKeyPack`'s, so the handoff is projection (§4); and
the anchored null key's own `:` (`colon_open_map_props`) pays
`pendingMapValue`'s four frame faces exactly as `colon_open_map_implicit`
does.

§1 is the family at the runtime; §2–§5 are the carrier, the payment, the
handoff and the spend at their types; §6 is what this item does not close. -/

namespace L4YAML.Tests.Guards.ScannerPropsLandingSiblingResumes

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

-- §1 The family.  An anchored key at the landing: ONE `+DOC`, and `b` is `k`'s
-- sibling with the anchor on its own value.
#guard emits "k:\n  - a\n&p b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a", "-SEQ", "=VAL &p :b",
   "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The tag head takes the same route.
#guard emits "k:\n  - a\n!!str b: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a", "-SEQ",
   "=VAL <tag:yaml.org,2002:str> :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- **The full thread**: the props-headed key resumes the INNER level with the
-- root still below it, and the NEXT landing pops to the root — which is what
-- the pack's twins exist to carry (`h_props_key` → the content arm's handoff
-- → `colon_open_map_implicit`'s frames → the value park's faces).
#guard emits "k:\n  m:\n    - a\n  &p n: 2\no: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ", "=VAL :a",
   "-SEQ", "=VAL &p :n", "=VAL :2", "-MAP", "=VAL :o", "=VAL :3", "-MAP",
   "-DOC", "-STR"]
-- …and without the second landing, the resumed level just closes.
#guard emits "k:\n  m:\n    - a\n  &p n: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :m", "+SEQ", "=VAL :a",
   "-SEQ", "=VAL &p :n", "=VAL :2", "-MAP", "-MAP", "-DOC", "-STR"]
-- The anchored NULL key (item 49's `&a : b`), landed: the run IS the key and
-- `colon_open_map_props` is the `:` that spends the pack — twins included.
#guard emits "k:\n  - a\n&p : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :a", "-SEQ", "=VAL &p :",
   "=VAL :b", "-MAP", "-DOC", "-STR"]

-- The boundaries.  A landing width that names no resumable level is refused
-- upstream (`trailingContent`), so the membership test's deferred case has no
-- input at the props head either.
#guard refuses "k:\n  - a\n &p b: 2\n"
-- And a landed run whose decorated content completes a VALUE rather than a
-- key (`&p b` with no `:`) is §9.2's own refusal — the props-decorated value
-- completion still punts `pendingContent`'s faces (§6), and its width-0
-- input does not exist.
#guard refuses "k:\n  - a\n&p b\nc: 2\n"

/-! ## §2 The carrier: the pack holds both resume twins

Item 41 taught this pack to carry the route instead of one route's
coordinates; the twins are the same lesson at the ENTRIES level.  Projection,
so any consumer can read them — nothing about the state decides whether the
fields are THERE, only whether a producer could pay them. -/

-- 2026-11-10 (item 471, option (A)): the level constructors' bound and the park faces read `≤` (the root frame
-- stands under a column-0 opener's own level), `ResumeWidths` names the survivors positionally and `ResumeWidths.lt`
-- is `ResumeWidths.le`; the rows below restate the faces they mirror — a shape move, no obligation changed.
example {sc : ScannerState} {sp_start sp_p sp_scan : SurfPos}
    (h : PropsKeyPack sc sp_start sp_p sp_scan) :
    ∃ k : Nat,
      ((∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width ≤ k) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_p sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        ResumeFrames (SLYamlStream sp_start) ks sp_e) ∨ True) ∧
      ((∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width ≤ k) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_p sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        KeyFrames (ExplValueLine sp_start nv) ks sp_e) ∨ PackAlt sc) := by
  obtain ⟨⟨k, _, _, _, h_resF, h_resFV⟩, _⟩ := h
  -- Item 148: the twin carries the scanner's own stack beside the widths;
  -- a reader that wants only the widths projects past it.
  exact ⟨k, h_resF.imp (fun ⟨ks, h_lt, _, r⟩ => ⟨ks, h_lt, r⟩) id,
    -- Item 150: the value-line twin carries one too, and projects the same way.
    h_resFV.elim (fun ⟨nv, ks, h_lt, _, r⟩ => Or.inl ⟨nv, ks, h_lt, r⟩) Or.inr⟩

/-! ## §3 The landing's payment: the resumed context funds route and twin at once

`resumeMapRoute` conses the run-headed entry onto the level the landing width
names; `resumeMapRouteF` is the same cons read at the entries level, the
levels below left standing for the park this run opens.  One `cont` funds
both — which is why `h_props_key`'s resume branch costs no new lemma. -/

example {sp_start sp_land sp_prep : SurfPos} {k : Nat} {ks : List FrameLevel}
    (h_ind : SIndent k sp_land sp_prep)
    (cont : ∀ sp_end, SCompactMapTail k sp_land sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) :
    (∀ sp_v, SBlockMapEntry k sp_prep sp_v → SLYamlStream sp_start sp_v) ∧
    (∀ sp_v : SurfPos, SBlockMapEntry k sp_prep sp_v →
     ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
     ResumeFrames (SLYamlStream sp_start) ks sp_e) :=
  ⟨resumeMapRoute h_ind cont, resumeMapRouteF h_ind cont⟩

/-! ## §4 The handoff: the pack's payload IS `ImplicitKeyPack`'s

The content arm decorates the run with a head and hands every field through —
twins now included, where items 99/108's slots took `Or.inr trivial` from this
producer.  Stated as the arm states it: the pack, a head at the run's start,
and the trailing whites are the whole of an `ImplicitKeyPack`. -/

example {sc : ScannerState} {sp_start sp_p sp_scan sp_gram : SurfPos}
    (h : PropsKeyPack sc sp_start sp_p sp_scan)
    (head : ImplicitKeyHead sp_p sp_gram)
    (hws : GStar SSWhite sp_gram sp_scan) :
    ImplicitKeyPack sc sp_start sp_scan := by
  obtain ⟨⟨k, route, hcol, kslot, resF, resFV⟩, _, _, _⟩ := h
  -- Item 168: a run-headed key opens no compact mapping over a sequence entry,
  -- so the pack's fourth twin punts.
  exact ⟨k, sp_p, sp_gram, Or.inl route, head, hws, hcol, kslot, resF, resFV, Or.inr trivial⟩

/-! ## §5 The spend at the anchored null key

`colon_open_map_props` pays `pendingMapValue.h_closeF` from the pack's twin
exactly as `colon_open_map_implicit` does from its — the completed entry
conses onto the resumed level and this entry's own level goes on top.  The
`SImplicitKey` here is `[161]`'s props-only node, `[193]`'s key with no
content at all. -/

example {sp_start sp_p sp_prep sp_scan' : SurfPos} {k : Nat} {ks : List FrameLevel}
    (h_lt : ∀ fr ∈ ks, fr.width ≤ k)
    (routeF : ∀ sp_v : SurfPos, SBlockMapEntry k sp_p sp_v →
      ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
      ResumeFrames (SLYamlStream sp_start) ks sp_e)
    (h_ik : SImplicitKey sp_p sp_prep)
    (h_lit : GLit ':' sp_prep sp_scan') :
    -- Item 179: the entry's value reads at the SHIFTED index.
    ∀ sp_mid : SurfPos, SBlockNode (k + 1) .blockIn sp_scan' sp_mid →
    ResumeFrames (SLYamlStream sp_start) (FrameLevel.map k :: ks) sp_mid :=
  fun sp_mid h_node =>
    ResumeFrames.level k ks sp_mid h_lt
      (fun sp_end h_tail =>
        routeF sp_mid
          (SBlockMapEntry.implicitKeyNode k sp_p sp_prep sp_scan' sp_mid h_ik h_lit
            (SBlockNode_blockIn_to_blockOut h_node))
          sp_end h_tail)

/-! ## §6 What this item does NOT close

* `entryPropsKeyPack_of_dispatch`'s twins.  Paying them is
  `entryKeyPack_of_dispatch`'s four threaded premises (items 99/108)
  transposed to the props side — the entry-parked props key inside a still
  open construct (`?⏎  &p a: b⏎  c: d⏎: - w`'s `c`) still rides the deferral.
  (CLOSED by item 115 — the four premises transposed verbatim, six callers
  paying what their parks hold.)
* The flow frame's rider.  `FlowBaseRoutes.key` carries the value-line pair
  only, so the flow-open arm DROPS the twins at that boundary — `&p [1]: b`
  parked at a resumed landing keeps its levels only once 67b widens the
  carrier.
* The props park's own faces.  `pendingProps` carries no `h_closeF`/`h_frames`
  of its own, and the props-decorated VALUE completion punts `pendingContent`'s
  faces — §1 pins its width-0 input as §9.2-refused; the nested twin rides.
  (CLOSED by item 114 — five resume faces on the park, paid by the entry and
  mapping producers and spent at every value completion and at the landing.)
* The block-scalar value arms of the two `accum_content_on_pendingMapValue`
  (one lemma since item 179)
  lemmas (item 109's residue — CLOSED by item 112, the node re-read to the
  landing).
* The construction sites: `SLYamlStream.implicitContinue` still takes
  `GOpt SLAnyDocument` — item 110 measured the tightening at 16 sites, LAST. -/

end L4YAML.Tests.Guards.ScannerPropsLandingSiblingResumes

end Blanket
