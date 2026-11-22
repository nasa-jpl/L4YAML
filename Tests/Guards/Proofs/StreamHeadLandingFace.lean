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

/-! # The landing's HEAD arm (DOCS item 136)

Item 135 measured the swap surface row 19's 1c breaks and found the seven
`SLAnyDocument.bare` sites waiting on ONE carrier rather than seven edits: the
landings' route face, today `SuffixRun sp_start sp_land ∨ True`, made into a
real disjunction over the three honest routes — the stream's HEAD, an open
SUFFIX run, a level RESUMED — with the fourth case refused at the scanner by
items 132–134 rather than carried.

This item builds the head arm and pays it.  The suffix arm has stood since item
117 and the resume arm since item 109; what was missing was the one a park that
has started NO document can pay, which is where `rootMapRoute`'s implicit
continuation is at its least honest — it appends a document to a stream that
has none.

**Four landings, one park.**  `noPending.h_nodoc` (item 116) carries `[202]
l-document-prefix*` behind a virgin block-context park, and item 135 made it
spendable by dropping the premise no producer used.  The park reaches four
landings, and item 135 paid one of them (the block `-`).  The other three are
this item:

* the block `:` and `?` — `colon_open_map`/`question_open_map`, whose entry
  routes become `nodocMapRoute`/`nodocMapRouteF` (`: v`, `? k`);
* the content dispatch — `accum_content_on_noPending`, which stops going
  through `content_dispatch_after_close` altogether and routes the parked node
  by `nodocNodeRoute` (`hello`, `a: 1`);
* the flow open — `accum_flow_open_depth0`'s virgin arm, whose collection
  routes by `nodocFlowResumeSep` and whose key routes by `nodocMapRoute`
  (`[1, 2]`, `[1]: b`).

Two of the four routes are new (`nodocNodeRoute`, `nodocFlowResumeSep`); the
other two are item 116's `nodocMapRoute`/`nodocMapRouteF`, which stood
nineteen items with no consumer and have four between them now.

**Measured, not asserted.**  A reference walk over the elaborated terms in
`StreamAccum`, counting each route constant's occurrences inside its holder,
gives the A/B: `accum_content_on_noPending` goes from
`content_dispatch_after_close = 2` to `nodocNodeRoute = 2`;
`accum_flow_open_depth0` from `topLevelFlowResumeSep = 2` to
`topLevelFlowResumeSep = 1, nodocFlowResumeSep = 1`; and `colon_open_map`,
`question_open_map`, `flowKeyRoute_of_root` and `content_dispatch_routed` each
gain the `nodoc` twins beside the `root` and `suffix` ones they already carried.

The `implicitContinue` application count is UNMOVED at eleven — this item adds
routes and moves callers, it deletes no site.  The seven bare sites are the
fallback ARMS of shared lemmas, and an arm goes only when its last caller can
pay something else; three of the four families that reach them still cannot.

No runtime file is touched, so every verdict in §1 is the one the pipelines
already gave.

§1 is the family at the runtime; §2–§4 are the builds at their types; §5 is
what remains. -/

namespace L4YAML.Tests.Guards.StreamHeadLandingFace

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
  L4YAML.Proofs.NodeProduction

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-! ## §1 The four landings at the runtime

Every one of them is the stream's FIRST document, which is the whole of the
claim: `[211]`'s `single` takes it, and `single`'s `l-any-document?` slot is
the one 1c leaves alone. -/

-- The block `:` landing — `[189]`'s empty-key entry (`colon_open_map`).
#guard emits ": v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- The block `?` landing — `[186]`'s explicit-key entry (`question_open_map`).
#guard emits "? k\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :", "-MAP", "-DOC", "-STR"]
-- The content dispatch — a plain scalar document and a mapping opened by an
-- implicit key (`accum_content_on_noPending`).
#guard emits "hello\n" ["+STR", "+DOC", "=VAL :hello", "-DOC", "-STR"]
#guard emits "a: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- The flow open — the collection itself, and the collection AS a key
-- (`nodocFlowResumeSep` and `flowKeyRoute_of_root`'s head arm).
#guard emits "[1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard emits "{a: b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "[1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
-- And item 135's landing, the fourth: the block `-`.
#guard emits "- a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]

-- Every `[202] l-document-prefix` run the witness crosses to reach the
-- landing: a comment line, a byte order mark, blank lines.  This is
-- `ssl_comments_extend_prefixes` at the runtime — the arm §4 hands each
-- landing is the park's witness extended over exactly these.
#guard emits "# c\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "\n\n? k\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :", "-MAP", "-DOC", "-STR"]
#guard emits "﻿: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "﻿hello\n" ["+STR", "+DOC", "=VAL :hello", "-DOC", "-STR"]
#guard emits "# c\n[1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b", "-MAP",
   "-DOC", "-STR"]
#guard emits "# c\n{a: b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]

-- The boundary, and it is the point of the arm being a DISJUNCTION rather
-- than a fact: the same landings behind a `...` are NOT the stream's head, and
-- take the suffix arm (item 117/118) instead.
#guard emits "a: 1\n...\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "a: 1\n...\n[1, 2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
-- …and with NEITHER a head nor a suffix behind them there is no third reading
-- to reach for: §9.2 refuses the input at the scanner (items 132–134), which
-- is what makes the fourth arm of the face a refutation rather than a route.
#guard refuses "a: 1\nb\n"
#guard refuses "hello\n# c\nworld\n"

/-! ## §2 The two new head twins

Both are their suffix twin with `[202] l-document-prefix*` where the open
suffix run stood, and `[211]`'s `single` where `suffixContinue` stood.  Neither
takes a stream: that is the content of "the park has started no document". -/

-- `nodocNodeRoute` — a completed top-level node.
example {sp_start sp_anchor sp_m : SurfPos}
    (h_nodoc : GStar SLDocumentPrefix sp_start sp_anchor)
    (h_bn : SBlockNode 0 .blockIn sp_anchor sp_m) :
    SLYamlStream sp_start sp_m :=
  nodocNodeRoute h_nodoc sp_m h_bn

-- …beside the suffix twin it mirrors, at the same conclusion.
example {sp_start sp_anchor sp_m : SurfPos}
    (h_sfx : SuffixRun sp_start sp_anchor)
    (h_bn : SBlockNode 0 .blockIn sp_anchor sp_m) :
    SLYamlStream sp_start sp_m :=
  suffixNodeRoute h_sfx sp_m h_bn

-- `nodocFlowResumeSep` — a completed top-level flow collection, with the
-- leading separation riding in the document's own `flowInBlock` slot.
example {sp_start sp_mid sp_br sp_ne sp_m : SurfPos}
    (h_nodoc : GStar SLDocumentPrefix sp_start sp_mid)
    (h_sep : SSeparateLines 0 sp_mid sp_br)
    (h_content : SFlowContent 0 .flowOut sp_br sp_ne)
    (h_ssl : SSLComments sp_ne sp_m) :
    SLYamlStream sp_start sp_m :=
  nodocFlowResumeSep h_nodoc h_sep sp_ne sp_m h_content h_ssl

example {sp_start sp_mid sp_br sp_ne sp_m : SurfPos}
    (h_sfx : SuffixRun sp_start sp_mid)
    (h_sep : SSeparateLines 0 sp_mid sp_br)
    (h_content : SFlowContent 0 .flowOut sp_br sp_ne)
    (h_ssl : SSLComments sp_ne sp_m) :
    SLYamlStream sp_start sp_m :=
  suffixFlowResumeSep h_sfx h_sep sp_ne sp_m h_content h_ssl

/-! ## §3 The head key context, and the cascade arm that spends it

`keyctx_of_preprocess` hands the landed key the STREAM closed at a column-0
line start — one route, and the over-approximating one.  `nodocctx_of_preprocess`
hands it the prefix run instead, and the arm below is the cascade's body
verbatim: the ctx in, item 116's twins out. -/

example {sp_start sp_prep : SurfPos}
    (h : ∃ (k : Nat) (sp_land : SurfPos),
      sp_land.col = 0 ∧ GStar SLDocumentPrefix sp_start sp_land ∧
      SIndent k sp_land sp_prep) :
    ∃ k : Nat,
      (∀ sp_v, SBlockMapEntry k sp_prep sp_v → SLYamlStream sp_start sp_v) ∧
      (∀ sp_v, SBlockMapEntry k sp_prep sp_v →
        ∀ sp_e, SCompactMapTail k sp_v sp_e →
        ResumeFrames (SLYamlStream sp_start) [] sp_e) :=
  match h with
  | ⟨k, _, hcol0, h_nodoc, h_ind⟩ =>
    ⟨k, nodocMapRoute hcol0 h_nodoc h_ind, nodocMapRouteF hcol0 h_nodoc h_ind⟩

-- The three contexts differ in the WITNESS and agree on everything else — the
-- column-0 landing, the `[63] s-indent(k)` in front of the key, and the route
-- they produce.  That is why the cascade can prefer one over another without
-- the consumer knowing which fired.
example {sp_start sp_land sp_key : SurfPos} {k : Nat}
    (hcol0 : sp_land.col = 0)
    (h_ind : SIndent k sp_land sp_key)
    (h_nodoc : GStar SLDocumentPrefix sp_start sp_land)
    (h_sfx : SuffixRun sp_start sp_land)
    (h_stream : SLYamlStream sp_start sp_land) :
    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧
    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧
    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) :=
  ⟨nodocMapRoute hcol0 h_nodoc h_ind,
   suffixMapRoute hcol0 h_sfx h_ind,
   rootMapRoute hcol0 h_stream h_ind⟩

/-! ## §4 The park's witness at each of the four landings

One field, extended over the landing's own `[79] s-l-comments` where the
landing is reached across a break, and spent as it stands where the park IS
the line start (the flow open's arm). -/

-- The block `:`/`?` arm — what `indicator_open_map` now takes, and what
-- `accum_block_on_noPending` pays it with.
example {sc : ScannerState} {sp_start sp sp_land : SurfPos}
    (h_nodoc : sc.inFlow = false → GStar SLDocumentPrefix sp_start sp)
    (h_block : sc.inFlow = false)
    (h_ssl : SSLComments sp sp_land)
    (h_col0 : sp.col = 0) :
    GStar SLDocumentPrefix sp_start sp_land ∨ True :=
  Or.inl (ssl_comments_extend_prefixes (h_nodoc h_block) h_col0 h_ssl)

-- The flow KEY's face — `flowKeyRoute_of_root`'s new argument, stated over
-- every landing the open may reach, as the suffix face beside it is.
example {sc : ScannerState} {sp_start sp : SurfPos}
    (h_nodoc : sc.inFlow = false → GStar SLDocumentPrefix sp_start sp)
    (h_block : sc.inFlow = false)
    (h_col0 : sp.col = 0) :
    (∀ sp_m, SSLComments sp sp_m → GStar SLDocumentPrefix sp_start sp_m) ∨ True :=
  Or.inl (fun _ h_ssl => ssl_comments_extend_prefixes (h_nodoc h_block) h_col0 h_ssl)

-- The flow OPEN's own route, which needs no landing: the park is the line
-- start, and the separation preprocessing crossed rides in the document.
example {sc : ScannerState} {sp_start sp sp_br : SurfPos}
    (h_nodoc : sc.inFlow = false → GStar SLDocumentPrefix sp_start sp)
    (h_block : sc.inFlow = false)
    (h_sep : SSeparateLines 0 sp sp_br) :
    ∀ sp_ne sp_m, SFlowContent 0 .flowOut sp_br sp_ne →
      SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m :=
  nodocFlowResumeSep (h_nodoc h_block) h_sep

-- The content dispatch's route, which anchors at the park itself.
example {sc : ScannerState} {sp_start sp : SurfPos}
    (h_nodoc : sc.inFlow = false → GStar SLDocumentPrefix sp_start sp)
    (h_block : sc.inFlow = false) :
    ∀ sp_m, SBlockNode 0 .blockIn sp sp_m → SLYamlStream sp_start sp_m :=
  nodocNodeRoute (h_nodoc h_block)

/-! ## §5 What remains

The face is half real.  Its suffix arm (item 117) and its head arm (this item)
are both routes now, and its resume arm (item 109) was one already; what is
still written `∨ True` is the fallback, and the fallback is still
`rootMapRoute`'s implicit continuation.

Three families reach it and none of them can pay a head:

* the landing skeletons' non-`...` arms — `accum_block_on_closeThenBlock` and
  `accum_content_pending` — where the park that closed HAS started a document;
* `content_dispatch_after_close`'s three remaining callers, two of them
  landings inside an open level (`accum_content_on_pendingBlock_indented`,
  `accum_content_on_pendingMapValue_indented`) and one the skeleton again;
* `accum_flow_open_depth0`'s shared `main`, whose three parks
  (`pendingContent`, `pendingBlockContent`, `pendingFlow`) are the same
  completed-document state.

For the first two the honest answer is the level they land in — the resume arm,
which `content_dispatch_routed` already prefers where the park kept its frames
— and where no level is open and no `...` intervened, §9.2 refuses the input
outright (§1's last two pins).  ~~So what the fallback arm needs is not a fourth
route but the refutation items 132–134 made available at the scanner, threaded
to the accumulation as a contradiction rather than carried as a document.  That
is the next item, and it is what empties the `∨ True`.~~

**One of them did need a fourth route** (item 137, correcting the sentence
above).  `pendingDocStart` is in the first family, and a `---` park has a
document that is still OPEN: the node its landing starts is that document's own
content, not a second document and not a level to resume.  The park has carried
the route since item 135; `StreamMarkerLandingFace` pays it at the two landings
that were still on the fallback.  What is left of the sentence holds for the
rest — see that file's §5.

~~`pendingDirective`'s `[209]` witness~~ and the `SLAnyDocument.explicit` wrapper
stand where item 135 left them: the first is a missing witness, the second
comes off at flip time.  (**The witness is PAID by item 138**; the wrapper still
comes off at flip time.)

**And the "resume arm" half of the paragraph above is wrong too** (item 139,
correcting it here where it was written).  Where a level IS open the input is
not served by the resume arm either: it is a DANGLING run, and
`danglingNodePos?` reads the run off the TOKEN ARRAY, so the scanner cannot
refuse it until the run has been scanned.  The step therefore runs and the
fallback genuinely serves it.  What holds is the OTHER half — no level open, no
`...`, no `---` — and that is exactly what item 139 refutes; see
`StreamBareDocumentFallback` §1 for the split, measured on the real scanner. -/

end L4YAML.Tests.Guards.StreamHeadLandingFace

end Blanket
