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

/-! # A landed sibling after COMPLETED content resumes its level (DOCS item 109)

Item 108 split the sibling family in two and paid one half.  A landing that
meets a park still AWAITING a node reaches `entryKeyPack_of_dispatch`'s dedent
branch, which pops the frames; a landing that meets COMPLETED content does not
reach that branch at all.  It goes through `accum_content_pending`'s shared
landing skeleton (`h_defer_split`), which closes the park with `close_with_ssl`
and hands `content_dispatch_after_close` a ROOT key context — so the landed key
opened a fresh `[187] l+block-mapping` under `[211]`'s `implicitContinue`,
which is a document the parser never starts.  That is row 19's third
over-approximation, and it is why `?⏎  a: b⏎  c: d⏎: - w` was not closed.

This item gives the skeleton the frames.  `pendingContent` gains the two faces
the value completion can already state — the stream-bottomed stack and the
`?`-frame-bottomed one — `resumectx_of_landing` reads the landing at the
ENTRIES level, and `content_dispatch_routed` prefers that reading where it
exists.  Then the landed key's entry is the resumed level's next element
(`resumeMapRoute`), the levels below it stand ready for the landing after that
(`resumeMapRouteF`), and the `?` entry is still open when its `: - w` line
arrives.

Nothing about the two new fields makes the old ones weaker: `h_closable` is the
stream face's `ResumeFrames.close` and `h_vpack` is the value face's, which §3
checks.

§1 pins the family at the runtime; §2–§5 are the payment at its types; §6 is the
discrimination — what the resume route does NOT need — and §7 is what the item
does not close. -/

namespace L4YAML.Tests.Guards.ScannerLandedSiblingResumes

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.IndentStackCover

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The family.  Both inputs the item-106 ledger names: the sibling reads as
-- ONE inner mapping with two entries, and the `?`'s own value line follows it.
#guard emits "? a: b\n  c: d\n: e\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "=VAL :e", "-MAP", "-DOC", "-STR"]
#guard emits "?\n  a: b\n  c: d\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- The level takes as many siblings as the width matches — the resumed frame is
-- consed onto, not spent.
#guard emits "?\n  a: b\n  c: d\n  e: f\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d",
   "=VAL :e", "=VAL :f", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC",
   "-STR"]
-- The `[188]` value stays optional, so the sibling alone is a whole entry.
#guard emits "? a: b\n  c: d\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "=VAL :", "-MAP", "-DOC", "-STR"]
-- The key HEAD is `[188]`'s, so the quoted arm lands the same way …
#guard emits "?\n  \"a\": b\n  c: d\n: - w\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL \"a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-DOC", "-STR"]
-- … and the whole family travels with the frame the `?` itself sits in.
#guard emits "k:\n  ?\n    a: b\n    c: d\n  : - w\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "+MAP", "=VAL :a", "=VAL :b",
   "=VAL :c", "=VAL :d", "-MAP", "+SEQ", "=VAL :w", "-SEQ", "-MAP", "-MAP",
   "-DOC", "-STR"]

-- The boundaries.  A ROOT sibling is the case the old context already served —
-- there the landed key really does open the mapping, and `rootMapRoute` stays.
#guard emits "a: b\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL :c", "=VAL :d", "-MAP",
   "-DOC", "-STR"]
-- The dedent drains this item also pays: the awaited value never arrived, and
-- the landed key is a sibling one level out (items 64/99's own inputs).
#guard emits "k:\n  -\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ", "=VAL :", "-SEQ", "=VAL :b",
   "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "k:\n  :\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+MAP", "=VAL :", "=VAL :", "-MAP",
   "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- **A landing width that names NO open level is refused upstream.**  This is
-- what `resumectx_of_landing`'s membership test defers rather than assumes: the
-- scanner throws `trailingContent` before any dispatch runs, so the arm the
-- non-member case falls to has no input.
#guard refuses "?\n  a: b\n c: d\n: - w\n"

/-! ## §2 The resumed route, at its type

`[195]`'s tail is `(s-indent(k) ns-l-block-map-entry(k))*`, so the landed key's
entry is that tail's FIRST element and everything below the level closes with
`ResumeFrames.close`.  No document is started. -/

example {sp_start sp_land sp_key : SurfPos} {k : Nat} {ks : List FrameLevel}
    (h_ind : SIndent k sp_land sp_key)
    (h_frames : ∀ sp_end, SCompactMapTail k sp_land sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  resumeMapRoute h_ind h_frames

-- The ENTRIES-level twin is one lemma over item 108's parameterized bottom, so
-- the same construction serves the stream face …
example {sp_start sp_land sp_key : SurfPos} {k : Nat} {ks : List FrameLevel}
    (h_ind : SIndent k sp_land sp_key)
    (h_frames : ∀ sp_end, SCompactMapTail k sp_land sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v →
    ∀ sp_e, SCompactMapTail k sp_v sp_e →
      ResumeFrames (SLYamlStream sp_start) ks sp_e :=
  resumeMapRouteF h_ind h_frames

-- … and the `?` frame's value-line face, which is the one that keeps the
-- explicit entry open across the sibling.
example {sp_start sp_land sp_key : SurfPos} {k nv : Nat} {ks : List FrameLevel}
    (h_ind : SIndent k sp_land sp_key)
    (h_frames : ∀ sp_end, SCompactMapTail k sp_land sp_end →
      KeyFrames (ExplValueLine sp_start nv) ks sp_end) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v →
    ∀ sp_e, SCompactMapTail k sp_v sp_e →
      KeyFrames (ExplValueLine sp_start nv) ks sp_e :=
  resumeMapRouteK h_ind h_frames

/-! ## §3 The two new fields SUBSUME the two closes they ride beside

This is why `pendingContent`'s `h_closable` and `h_vpack` do not move: each is
its face's `ks`-closed reading.  A park that pays a frames face therefore owes
nothing new, and a park that punts loses nothing. -/

example {sp_start sp_scan : SurfPos} {ks : List FrameLevel}
    (h : ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      ResumeFrames (SLYamlStream sp_start) ks sp_mid) :
    ∀ sp_mid, SSLComments sp_scan sp_mid → SLYamlStream sp_start sp_mid :=
  fun sp_mid h_ssl => (h sp_mid h_ssl).close

example {sp_start sp_scan : SurfPos} {nv : Nat} {ks : List FrameLevel}
    (h : ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      KeyFrames (ExplValueLine sp_start nv) ks sp_mid) :
    ∀ sp_mid sp_i sp_c : SurfPos, SSLComments sp_scan sp_mid →
      SIndent nv sp_mid sp_i → GLit ':' sp_i sp_c →
      ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v :=
  fun sp_mid sp_i sp_c h_ssl h_ind h_lit sp_v h_sbi =>
    (h sp_mid h_ssl).close sp_i sp_c h_ind h_lit sp_v h_sbi

/-! ## §4 The park's payment: the SAME node both closures wrap

The producer hands the value node — completed on the landing's
`[79] s-l-comments` — to the pending's transport faces instead of to their
closes.  Nothing is re-derived, which is what makes the field free at the three
value-completion sites and `Or.inr trivial` everywhere else. -/

-- Item 152 appended the cover conjunct to both faces, so the payment carries a
-- third component; the node the closure wraps is unchanged, which is why that
-- item costs these producers one `Or.imp` and nothing else.
example {sc : ScannerState} {sp_start sp_scan : SurfPos} {n nv : Nat} {ks : List FrameLevel}
    (build : ∀ sp_mid, SSLComments sp_scan sp_mid → SBlockNode n .blockIn sp_scan sp_mid)
    (closeFV : ∀ sp_mid, SBlockNode n .blockIn sp_scan sp_mid →
      KeyFrames (ExplValueLine sp_start nv) ks sp_mid) :
    (∃ (nv : Nat) (ks : List FrameLevel),
      ((∃ lo n : Nat, Floor lo n ks ∧ Covered lo ks sc) ∨ True) ∧
      ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      KeyFrames (ExplValueLine sp_start nv) ks sp_mid) ∨ True :=
  Or.inl ⟨nv, ks, Or.inr trivial, fun sp_mid h_ssl => closeFV sp_mid (build sp_mid h_ssl)⟩

/-! ## §5 The landing's context, read at the entries level

`resumectx_of_landing` takes the landing the caller already closed with — not a
fresh derivation of it — because the frames are stated over the park's own
`[79] s-l-comments` and a second witness could not be joined to the first. -/

example {sc s_prep : ScannerState} {c : Char}
    {sp_start sp_scan sp_mid sp_prep : SurfPos}
    (hcol_mid : sp_mid.col = 0)
    (h_ws : GStar SSWhite sp_mid sp_prep)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_fS : (∃ ks : List FrameLevel,
        ((∃ lo n : Nat, Floor lo n ks ∧
          Covered lo ks sc) ∨ True) ∧
        ∀ sp_m : SurfPos, SSLComments sp_scan sp_m →
        ResumeFrames (SLYamlStream sp_start) ks sp_m) ∨ True)
    (h_fV : (∃ (nv : Nat) (ks : List FrameLevel),
        ((∃ lo n : Nat, Floor lo n ks ∧
          Covered lo ks sc) ∨ True) ∧
        ∀ sp_m : SurfPos, SSLComments sp_scan sp_m →
        KeyFrames (ExplValueLine sp_start nv) ks sp_m) ∨ PackAlt sc)
    (h_pay : ∀ (w : Nat) (ks ks' : List FrameLevel),
        ((∃ lo n : Nat, Floor lo n ks ∧
          Covered lo ks sc) ∨ True) →
        FrameLevel.map w ∈ ks → ResumeWidths ks ks' w → s_prep.col = w →
        ((∃ lo : Nat, Floor lo w (FrameLevel.map w :: ks') ∧
          Covered lo (FrameLevel.map w :: ks') s_prep) ∨ True))
    -- Item 374: the sentinel base, for the sequence-top face the declined resume now carries.
    (h_base : L4YAML.Proofs.IndentStackBase.SentinelBase sc) :
    ResumeKeyCtx s_prep sp_start sp_prep :=
  resumectx_of_landing (h_base := h_base) hcol_mid h_ws h_ssl h_preprocess hcorr_prep h_fS h_fV h_pay
    -- Item 168: this guard is about the two FRAMED lanes; the sequence face punts.
    (Or.inr trivial)

-- **The LEFT disjunct is inhabitable, from exactly the data a paying park has.**
-- A `∨ True` cannot be interrogated after the fact (proof irrelevance), so the
-- check that matters is that the informative side is reachable at all: the
-- landing's line start, `[63]`'s spaces, a fresh at-position save, and a stack
-- whose widths include the landing's.  `resumectx_of_landing` assembles this
-- and nothing else.
-- 2026-11-10 (item 471, option (A)): the level constructors' bound and the park faces read `≤` (the root frame
-- stands under a column-0 opener's own level), `ResumeWidths` names the survivors positionally and `ResumeWidths.lt`
-- is `ResumeWidths.le`; the rows below restate the faces they mirror — a shape move, no obligation changed.
example {sp_start sp_land sp_prep : SurfPos} {k : Nat} {ks : List FrameLevel}
    {s_prep : ScannerState}
    (hcol0 : sp_land.col = 0) (h_ind : SIndent k sp_land sp_prep)
    (h_fr : ResumeFrames (SLYamlStream sp_start) ks sp_land) (hmem : FrameLevel.map k ∈ ks)
    (h_poss : s_prep.simpleKey.possible = true)
    (h_pos : s_prep.simpleKey.pos = s_prep.currentPos) 
    (h_alt : PackAlt s_prep) :
    ResumeKeyCtx s_prep sp_start sp_prep :=
  match h_fr.resumeAt hmem with
  | ⟨ks', h_w, cont⟩ =>
      -- Item 374: the framed lane is the context's first disjunct.
      Or.inl (Or.inl ⟨⟨k, ks', sp_land, hcol0, h_ind, h_w.le, Or.inr trivial, cont,
        Or.inr h_alt,
        -- Item 168: the sequence face is the third lane and punts here.
        Or.inr trivial⟩, h_poss, h_pos⟩)

/-! ## §6 The discrimination: what the resumed route does NOT need

`rootMapRoute` takes `SLYamlStream sp_start sp_land` — the stream CLOSED at the
landing — and that hypothesis is exactly what forces `[211]`'s
`implicitContinue`: having closed, the only way back in is a new document.  The
resumed route takes no such hypothesis.  The examples in §2 are already stated
without one; this one says it the other way round, by deriving `rootMapRoute`'s
own conclusion from frames alone in a context where no closed stream is
available at the landing at all. -/

example {sp_start sp_land sp_key : SurfPos} {k : Nat} {ks : List FrameLevel}
    (h_ind : SIndent k sp_land sp_key)
    -- The ONLY thing known about `sp_land`: the levels open there.  No
    -- `sp_land.col = 0`, no `SLYamlStream sp_start sp_land`.
    (h_frames : ∀ sp_end, SCompactMapTail k sp_land sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end)
    {sp_v : SurfPos} (h_entry : SBlockMapEntry k sp_key sp_v) :
    SLYamlStream sp_start sp_v :=
  resumeMapRoute h_ind h_frames sp_v h_entry

-- And the payoff, at its type: after the sibling the `?` entry is STILL owed
-- its value line — which is what `? a: b⏎  c: d⏎: e`'s `: e` supplies.
example {sp_start sp_land sp_key : SurfPos} {k nv : Nat}
    (h_ind : SIndent k sp_land sp_key)
    (h_frames : ∀ sp_end, SCompactMapTail k sp_land sp_end →
      KeyFrames (ExplValueLine sp_start nv) [] sp_end)
    {sp_v : SurfPos} (h_entry : SBlockMapEntry k sp_key sp_v)
    {sp_e : SurfPos} (h_tail : SCompactMapTail k sp_v sp_e) :
    ExplValueLine sp_start nv sp_e :=
  (resumeMapRouteK h_ind h_frames sp_v h_entry sp_e h_tail).close

/-! ## §7 What this item does NOT close

* `pendingBlockContent` — the entry-parked completed content — keeps the root
  context; its own producers' payments are not made here.  (CLOSED by item 110,
  which needed no new field: `h_closeF` was already sized at the entry level.
  ~~`- a: b⏎  c: d`~~ was the wrong input to name for it — that one parks
  `pendingContent`, the `b` being a completed mapping value; the entry-parked
  family is `k:⏎  - a⏎b: 2`.)
* The PROPS landing.  `content_dispatch_routed`'s `h_props_key` still reads
  only the root key context, so a landed `&p c: d` sibling re-opens at the root
  as before; `PropsKeyPack` carries no resume twin to spend.  (CLOSED by item
  111: the pack gains items 99/108's twins and `h_props_key` resumes first.)
* The block-scalar value arms of the two `accum_content_on_pendingMapValue`
  (one lemma since item 179)
  lemmas punt their frames: the node there is complete at the park rather than
  at the landing, so the transport face does not apply unchanged.  (CLOSED by
  item 112 — item 95's absorption closure re-reads the node TO the landing and
  every face takes the re-read.  ~~`? a: |⏎  x⏎  c: d`~~ was also mis-indented
  for the family: the body must clear its entry's width, and as spelled the
  input is refused; the honest spelling is `? a: |⏎    x⏎  c: d⏎: v`.)
* The construction sites themselves.  `SLYamlStream.implicitContinue` still
  takes `GOpt SLAnyDocument` where `[211]` writes `l-explicit-document?` after a
  prefix-only continuation; tightening the CONSTRUCTOR is row 19's own step, and
  what this item removes is the reason the landing skeleton needed it. -/

end L4YAML.Tests.Guards.ScannerLandedSiblingResumes

end Blanket
