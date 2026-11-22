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

/-! # The landing's MARKER arm (DOCS item 137)

Item 136 gave the landing's route face its HEAD arm and paid it at all four of
the virgin park's landings, leaving one sentence that was too strong: that the
families still reaching the fallback need no fourth ROUTE.  One of them does.

**`pendingDocStart` is a park with an OPEN document, and the fallback closes
it.**  `[208] l-explicit-document ::= c-directives-end ( l-bare-document |
( e-node s-l-comments ) )` — when `---` is scanned the document it opens is not
finished, and the node on the next line is that document's own content.  The
fallback takes the other alternative: it closes the marker's document with
`e-node`, then appends the landed node as a SECOND, bare document through
`[211]`'s implicit continuation.  The parser emits one document for every one
of these inputs (§1), so the reading was over-approximating in exactly the
place row 19's 1c tightening removes — and unlike the other fallback families,
this one has had the honest route on the park since item 135 reshaped
`h_doc_route` into one.

**Four landings, one park — the same shape as item 136's, and two were already
paid.**  The content dispatch's INLINE arm (`--- a`) has routed through
`h_doc_route` since item 43, and the flow open (`--- [1]`, `---⏎[1, 2]`) since
item 56.  This item pays the other two:

* the block `-`, `:` and `?` — `accum_block_on_closeThenBlock`, whose sequence
  route becomes `markerSeqRoute` and whose `[188]` entry routes become
  `markerMapRoute`/`markerMapRouteF` (`---⏎- a`, `---⏎: v`, `---⏎? k`);
* the content dispatch's LANDED arm — `accum_content_pending`'s shared
  skeleton, where the anchor moves from the landing back to the marker's park
  and `content_dispatch_routed` takes the anchor as a parameter (`---⏎hello`,
  `---⏎a: 1`).

**Why the sequence route is stated over the ENTRIES.**  `[199]
s-l+block-collection` puts `s-l-comments` in FRONT of the entries, so the break
this landing crossed belongs INSIDE the node the marker's document wants.  A
route taking a finished `SBlockNode` at the landing — which is what
`suffixNodeRoute` and `nodocNodeRoute` are — can no longer absorb it.  Hence
`MarkerNodeRoute`: the marker's park and the landing's comments as a pair, with
`markerSeqRoute`/`markerMapRoute` supplying the comments to `rootBlockSeq` and
`rootBlockMap` where the other three routes supply `sslComments_refl_of_col0`.

**Measured, both directions.**  A reference-count walk over the elaborated
terms gives `accum_block_on_closeThenBlock` from `rootBlockSeq = 3` to
`rootBlockSeq = 1, markerSeqRoute = 1`, `accum_content_pending` from
`content_dispatch_routed = 3` to `= 5`, and `colon_open_map`,
`question_open_map` and `content_dispatch_routed` each gaining the `marker`
twins beside the `root`, `suffix` and `nodoc` ones.  The `implicitContinue`
application count is UNMOVED at eleven (NINE since item 209) and the
constructor flip still gives
nine errors at the same nine lemmas: this item moves callers, it deletes no
site.  What it does delete is a family — `pendingDocStart` no longer reaches
any fallback arm from any landing.

No runtime file is touched, so every verdict in §1 is the one the pipelines
already gave.

§1 is the family at the runtime; §2–§4 are the builds at their types; §5 is
what remains. -/

namespace L4YAML.Tests.Guards.StreamMarkerLandingFace

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
  L4YAML.Proofs.NodeProduction L4YAML.Proofs.PreprocessProduction

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-! ## §1 The marker's landings at the runtime

Every one of them is ONE explicit document — a single `+DOC ---` … `-DOC` pair
with the landed node inside it.  That is the whole of the claim: the fallback
these landings used to take emits the node as a second document, and no input
here has two. -/

-- The block landings.  `-` opens `[183]` inside the marker's document; `:` and
-- `?` open `[187]`'s two keyless entries there.
#guard emits "---\n- a\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "---\n: v\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "---\n? k\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :k", "=VAL :", "-MAP", "-DOC", "-STR"]
-- The content dispatch's LANDED arm: a plain scalar document, and a mapping
-- opened by an implicit key (which is the marker KEY CONTEXT, §3).
#guard emits "---\nhello\n" ["+STR", "+DOC ---", "=VAL :hello", "-DOC", "-STR"]
#guard emits "---\na: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- The two landings that were already routed: the flow open (item 56) and the
-- content dispatch's inline arm (item 43).
#guard emits "---\n[1, 2]\n"
  ["+STR", "+DOC ---", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard emits "---\n{a: b}\n"
  ["+STR", "+DOC ---", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "---\n[1]: b\n"
  ["+STR", "+DOC ---", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
#guard emits "--- a\n" ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]

-- The `[79] s-l-comments` the landing crosses is what `MarkerNodeRoute`
-- carries, and `[199]` is where it goes: a comment line and blank lines in
-- front of the landing leave one document, not two.
#guard emits "---\n# c\n- a\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "---\n\n\n- a\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "---\n# c\na: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "---\n\nhello\n" ["+STR", "+DOC ---", "=VAL :hello", "-DOC", "-STR"]

-- A DIRECTIVE document's `---` parks the same constructor
-- (`structural_dispatch_after_directives`), so its landings take the same arm
-- — with `[209] l-directive-document` in the route's `[210]` slot instead of
-- `[208]`, which is the producer's business and not the landing's.
#guard emits "%YAML 1.2\n---\n- a\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "%YAML 1.2\n---\na: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]

-- The boundaries.  A marker with NOTHING after it keeps the `( e-node
-- s-l-comments )` alternative — `close_with_ssl`'s `GAlt.right`, untouched
-- here — and a second `---` really is a second document.
#guard emits "---\n...\n" ["+STR", "+DOC ---", "=VAL :", "-DOC ...", "-STR"]
#guard emits "---\n- a\n---\n- b\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC",
   "+DOC ---", "+SEQ", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "a: 1\n---\n- b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC",
   "+DOC ---", "+SEQ", "=VAL :b", "-SEQ", "-DOC", "-STR"]
-- …and the marker's own line takes no implicit key at all, which is why the
-- inline arm's key context punts where the landed arms' does not.
#guard refuses "--- a: 1\n"

/-! ## §2 The marker routes at their types

`MarkerNodeRoute` is a PAIR — the marker's park and the landing's comments —
because the comments have to reach `[199]`, which sits inside the node.  That
is the one structural difference from the head and suffix arms, whose witnesses
travel alone. -/

-- The carrier, and the two ways `pendingDocStart` pays it: the landing's own
-- `[79] s-l-comments` in front of the park's route.
example {sp_start sp_scan sp_land : SurfPos}
    (h_doc_route : ∀ sp_end,
      GAlt SLBareDocument (GSeq SENode SSLComments) sp_scan sp_end →
      SLYamlStream sp_start sp_end)
    (h_ssl : SSLComments sp_scan sp_land) :
    MarkerNodeRoute sp_start sp_land :=
  ⟨sp_scan, h_ssl, fun sp h_bn =>
    h_doc_route sp (GAlt.left sp_scan sp (SLBareDocument.mk sp_scan sp h_bn))⟩

-- `markerSeqRoute` — the landed `-`'s entries, wrapped as `[183]` inside the
-- marker's own `[207] l-bare-document`.
example {sp_start sp_land sp_e : SurfPos} {k : Nat}
    (h_mk : MarkerNodeRoute sp_start sp_land)
    (h_entries : SBlockSeqEntries k sp_land sp_e) :
    SLYamlStream sp_start sp_e :=
  markerSeqRoute h_mk sp_e h_entries

-- `markerMapRoute` and its entries-level twin — the landed `:`/`?`/key's
-- entry, wrapped as `[187]` in the same place.  Neither takes `sp_land.col = 0`:
-- the landing's `SSLComments` already ends where `[63] s-indent(k)` begins.
example {sp_start sp_land sp_key sp_v : SurfPos} {k : Nat}
    (h_mk : MarkerNodeRoute sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key)
    (h_entry : SBlockMapEntry k sp_key sp_v) :
    SLYamlStream sp_start sp_v :=
  markerMapRoute h_mk h_ind sp_v h_entry

example {sp_start sp_land sp_key sp_v sp_e : SurfPos} {k : Nat}
    (h_mk : MarkerNodeRoute sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key)
    (h_entry : SBlockMapEntry k sp_key sp_v)
    (h_tail : SCompactMapTail k sp_v sp_e) :
    ResumeFrames (SLYamlStream sp_start) [] sp_e :=
  markerMapRouteF h_mk h_ind sp_v h_entry sp_e h_tail

-- The head twin beside it, at the same conclusion — the difference is the
-- witness and the `[211]` arm it reaches, never the entry.
example {sp_start sp_land sp_key sp_v : SurfPos} {k : Nat}
    (hcol0 : sp_land.col = 0)
    (h_nodoc : GStar SLDocumentPrefix sp_start sp_land)
    (h_ind : SIndent k sp_land sp_key)
    (h_entry : SBlockMapEntry k sp_key sp_v) :
    SLYamlStream sp_start sp_v :=
  nodocMapRoute hcol0 h_nodoc h_ind sp_v h_entry

-- And the reason a marker NODE route in `suffixNodeRoute`'s shape does not
-- exist: `[199]`'s comments slot is inside the node, so a node already built
-- at the landing has nowhere to put them.  What the marker CAN take is the
-- node built at its own park — which is what the flow open (item 56) and the
-- content dispatch's landed arm hand it, both by moving the ANCHOR.
example {sp_start sp_land sp : SurfPos}
    (h_mk : MarkerNodeRoute sp_start sp_land)
    (h_bn : SBlockNode 0 .blockIn h_mk.choose sp) :
    SLYamlStream sp_start sp :=
  h_mk.choose_spec.2 sp h_bn

/-! ## §3 The marker key context, and the cascade arm that spends it

`markerctx_of_landing` is `suffixctx_of_landing` with the marker's route in the
suffix run's place — the same three facts off the same landing, and the fourth
context `content_dispatch_routed`'s cascade prefers over the bare one. -/

example {sc s_prep : ScannerState} {c : Char}
    {sp_start sp_scan sp_mid sp_prep : SurfPos}
    (hcol_mid : sp_mid.col = 0)
    (h_ws : GStar SSWhite sp_mid sp_prep)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_mk : (∀ sp_m : SurfPos, SSLComments sp_scan sp_m →
        MarkerNodeRoute sp_start sp_m) ∨ True) :
    ((∃ (k : Nat) (sp_land : SurfPos),
        sp_land.col = 0 ∧ MarkerNodeRoute sp_start sp_land ∧
        SIndent k sp_land sp_prep) ∧
      s_prep.simpleKey.possible = true ∧
      s_prep.simpleKey.pos = s_prep.currentPos) ∨ True :=
  markerctx_of_landing hcol_mid h_ws h_ssl h_preprocess h_mk

-- The cascade's body at this arm, verbatim: the ctx in, the marker twins out.
example {sp_start sp_prep : SurfPos}
    (h : ∃ (k : Nat) (sp_land : SurfPos),
      sp_land.col = 0 ∧ MarkerNodeRoute sp_start sp_land ∧
      SIndent k sp_land sp_prep) :
    ∃ k : Nat,
      (∀ sp_v, SBlockMapEntry k sp_prep sp_v → SLYamlStream sp_start sp_v) ∧
      (∀ sp_v, SBlockMapEntry k sp_prep sp_v →
        ∀ sp_e, SCompactMapTail k sp_v sp_e →
        ResumeFrames (SLYamlStream sp_start) [] sp_e) :=
  match h with
  | ⟨k, _, _, h_mk, h_ind⟩ =>
    ⟨k, markerMapRoute h_mk h_ind, markerMapRouteF h_mk h_ind⟩

-- The FOUR routes a landed `[188]` entry can now take, side by side.  They
-- agree on the entry and on the key's `[63] s-indent(k)`, and differ only in
-- which `[211]` arm the document they build lands in: `implicitContinue`'s
-- slot, `suffixContinue`'s, `single`'s, or the marker's own `[210]`.
example {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (hcol0 : sp_land.col = 0)
    (h_ind : SIndent k sp_land sp_key)
    (h_mk : MarkerNodeRoute sp_start sp_land)
    (h_nodoc : GStar SLDocumentPrefix sp_start sp_land)
    (h_sfx : SuffixRun sp_start sp_land)
    (h_stream : SLYamlStream sp_start sp_land) :
    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧
    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧
    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧
    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) :=
  ⟨markerMapRoute h_mk h_ind,
   nodocMapRoute hcol0 h_nodoc h_ind,
   suffixMapRoute hcol0 h_sfx h_ind,
   rootMapRoute hcol0 h_stream h_ind⟩

/-! ## §4 The park's arm at each landing

One field — `pendingDocStart.h_doc_route` — stated over every landing the park
may reach, exactly as the `...` park's suffix arm is (item 117/118). -/

-- The block dispatch's arm (`accum_block_on_closeThenBlock`).
example {sp_start sp_scan : SurfPos}
    (h_doc_route : ∀ sp_end,
      GAlt SLBareDocument (GSeq SENode SSLComments) sp_scan sp_end →
      SLYamlStream sp_start sp_end) :
    (∀ sp_m, SSLComments sp_scan sp_m → MarkerNodeRoute sp_start sp_m) ∨ True :=
  Or.inl (fun _sp_m h_ssl => ⟨sp_scan, h_ssl, fun sp h_bn =>
    h_doc_route sp (GAlt.left sp_scan sp (SLBareDocument.mk sp_scan sp h_bn))⟩)

-- The content skeleton's arm (`accum_content_pending`'s `h_defer_split`), at
-- the identical type: the two landings share one payment.
example {sp_start sp_scan : SurfPos}
    (h_doc_route : ∀ sp_end,
      GAlt SLBareDocument (GSeq SENode SSLComments) sp_scan sp_end →
      SLYamlStream sp_start sp_end) :
    (∀ sp_m : SurfPos, SSLComments sp_scan sp_m →
      MarkerNodeRoute sp_start sp_m) ∨ True :=
  Or.inl (fun _sp_m h_ssl => ⟨sp_scan, h_ssl, fun sp h_bn =>
    h_doc_route sp (GAlt.left sp_scan sp (SLBareDocument.mk sp_scan sp h_bn))⟩)

-- What the content skeleton then does with it: the anchor moves back to the
-- park, so the landing's comments ride in `[80] s-separate-lines(0)` and the
-- node `content_dispatch_routed` builds starts where `---` ended.
-- (It needs no `sp_mid.col = 0`: `[63] s-indent(0)` is empty at any column,
-- and the landing's column-0 fact is spent by the key context instead.)
example {sp_mk sp_mid sp_prep : SurfPos}
    (h_ssl_mk : SSLComments sp_mk sp_mid)
    (h_ws : GStar SSWhite sp_mid sp_prep) :
    SSeparateLines 0 sp_mk sp_prep :=
  SSeparateLines.commented 0 sp_mk sp_mid sp_prep h_ssl_mk
    (SFlowLinePrefix.mk 0 sp_mid sp_mid sp_prep (SIndent.zero sp_mid)
      (L4YAML.Proofs.ScalarProduction.gstar_sswhite_to_gopt_sep h_ws))

-- The close the marker park still makes when NOTHING lands — `[208]`'s other
-- alternative, which is what `---⏎...` and `---` at end of input take.
example {sc : ScannerState} {sp_start sp_block sp_scan sp_mid : SurfPos}
    (h_pending : PendingNode sc false sp_start sp_block sp_scan)
    (h_stream : SLYamlStream sp_start sp_block)
    -- Item 157: the close's new premise; a `...` park never reads it.
    (h_nd : danglingNodePos? sc = none)
    -- Item 275: §8.1's silence, carried beside it.
    (h_ui : underIndentedFlowValuePos? sc = none)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_noflow : sc.inFlow = false) :
    SLYamlStream sp_start sp_mid :=
  h_pending.close_with_ssl h_stream h_nd h_ui h_noflow h_ssl

/-! ## §5 What remains

The face has four arms now — resume (item 109), suffix (item 117), head (item
136) and marker (this item) — and `pendingDocStart` is off the fallback at
every landing it reaches.

What still writes `∨ True` is the fallback, and it is still `rootMapRoute`'s
implicit continuation.  Two families reach it, and item 136's sentence holds
for both once the marker is subtracted:

* the landing skeletons' non-`...`, non-`---` arms — `pendingContent`,
  `pendingProps`, `pendingBlockContent`, `pendingBlock`, `pendingMapValue`,
  `pendingFlow` — where the park closed a node INSIDE a document that is
  already finished;
* `accum_flow_open_depth0`'s shared `main` and
  `content_dispatch_after_close`'s two indented callers, which are the same
  state one dispatch later.

None of these has a document to hand the node to.  Where a level is open the
honest answer is the resume arm `content_dispatch_routed` already prefers;
where none is and no `...` and no `---` intervened, §9.2 refuses the input
outright (items 132–134).  So what the fallback arm needs is still the
refutation threaded to the accumulation as a contradiction — with one family
fewer to argue about.

**Half PAID by DOCS item 139** (2026-09-10), which threaded it — and which
corrects the paragraph above in the one place it could not have known.  Where a
level IS open the input is not served by the resume arm either: it is a DANGLING
run, and `danglingNodePos?` reads the run off the TOKEN ARRAY, so the scanner
cannot refuse it until the run has been scanned.  The step therefore runs, the
park it makes owes a stream, and the fallback genuinely serves it.  Only the
sentinel-alone half is refutable at the landing, and that is the half item 139
refutes; see `StreamBareDocumentFallback` §1 for the split, measured on the real
scanner.

`pendingDirective`'s `[209]` witness and the `SLAnyDocument.explicit` wrapper
stand where item 135 left them. -/

end L4YAML.Tests.Guards.StreamMarkerLandingFace

end Blanket
