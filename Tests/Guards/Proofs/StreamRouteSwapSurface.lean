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

/-! # The swap surface (DOCS item 135)

Row 19's 1c tightens `[211]`'s `implicitContinue` from `GOpt SLAnyDocument` to
`GOpt SLExplicitDocument`, which is what stops the grammar admitting a second
BARE document with no `...` in front of it.  Item 110 built the tightening and
measured the sites it breaks: **16, every one in `StreamAccum`**.  The ledger has
carried "the 16 fallback swaps" as the step before the constructor ever since.

**Re-measured here, and the number moved.**  Two instruments agree: an
environment scan over the elaborated terms (which `SLYamlStream.implicitContinue`
applications exist, and what each passes in the `l-any-document?` slot), and the
tightening itself, built and reverted.  The compiler names **nine** sites, and
they are not one kind of problem:

* **seven** pass `SLAnyDocument.bare` — the fallback proper, each needing the
  route decision the remaining items owe: the stream's own head (`single`), the
  slot a `...` opens (`suffixContinue`), a level resumed through `ResumeFrames`,
  or the refusal M1–M3 landed at items 132–134;
* **one** passes `SLAnyDocument.explicit` — `[208]` is exactly what the
  tightened arm takes, so the wrapper comes off at flip time and nothing is
  decided (`DocumentProduction.stream_implicit_continue` is the same edit, one
  module downstream);
* **one** passes `SLAnyDocument.directive` — `[209] l-directive-document` is
  neither a bare nor an explicit document, so the implicit continuation is the
  wrong arm for it outright.  The runtime already refuses the third reading
  (§1's last pin), so what is missing is a witness, not a refusal.

Item 135 is what took 16 to 9:

* **two sites were dead.**  `flowSeq_extends_stream` and `flowMap_extends_stream`
  extended the stream with a completed top-level flow node as a bare document;
  the flow-open stack has carried that job since items 44–46, and an environment
  scan for consumers finds neither lemma referenced by any declaration in the
  closure.  Deleted.
* **three were one field read wrong.**  `pendingDocStart` handed back an
  `SLAnyDocument` and left `close_with_ssl`, `accum_flow_open_depth0` and
  `accum_content_pending` to append it with `implicitContinue` — three copies of
  a term built from a document whose `[210]` alternative only the PRODUCER knows.
  The field is a ROUTE now (§2), the three consumers apply it, and the two
  producers spend the arm each of them can actually justify.
* **two were the seed's own root sequence.**  `accum_block_on_noPending`'s `-`
  arm opened `[183]` under a bare document appended to the accumulated stream.
  A block-context `noPending` is the stream's seed, so the region behind it is
  `[202] l-document-prefix*` and the sequence heads the stream's FIRST document:
  `[211]`'s `single`, whose `l-any-document?` slot the tightening leaves
  untouched (§4).  What made the park's `h_nodoc` spendable was dropping its
  `documentEverStarted = false` premise (§3) — a premise no producer used and no
  consumer could discharge.

No runtime file is touched, so every verdict below is the one the pipelines
already gave.

§1 is the family at the runtime; §2–§4 are the three builds at their types; §5
is the surface that remains. -/

namespace L4YAML.Tests.Guards.StreamRouteSwapSurface

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
  L4YAML.Proofs.NodeProduction L4YAML.Proofs.FlowAdjacency

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

/-! ## §1 The family at the runtime

The seed's root sequence — the two sites §4 re-reads through `single` — with
every prefix run `[202]` admits in front of it. -/

#guard emits "- a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "# c\n- a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "﻿- a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "\n\n- a\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
-- The tail rides the same route: the entries chain closes at `single` too.
#guard emits "- a\n- b\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :a", "=VAL :b", "-SEQ", "-DOC", "-STR"]
#guard emits "- a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ", "-DOC", "-STR"]

-- The document-start park's own arms, §2's route at each of its two producers.
-- `[208] l-explicit-document` — the arm the implicit continuation takes at any
-- point in the stream…
#guard emits "---\n- a\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "a: 1\n---\n- b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC",
   "+DOC ---", "+SEQ", "=VAL :b", "-SEQ", "-DOC", "-STR"]
-- …the empty body (`close_with_ssl`'s branch, the `GAlt.right` one)…
#guard emits "---\n" ["+STR", "+DOC ---", "=VAL :", "-DOC", "-STR"]
-- …and the one-line body (`accum_content_pending`'s, the `GAlt.left` one).
#guard emits "--- a\n" ["+STR", "+DOC ---", "=VAL :a", "-DOC", "-STR"]
-- The flow node behind the marker is `accum_flow_open_depth0`'s route.
#guard emits "--- [1, 2]\n"
  ["+STR", "+DOC ---", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]

-- `[209] l-directive-document` — the residue arm.  Legal at the stream's head
-- and after a `...`…
#guard emits "%YAML 1.2\n---\n- a\n"
  ["+STR", "+DOC ---", "+SEQ", "=VAL :a", "-SEQ", "-DOC", "-STR"]
#guard emits "a: 1\n...\n%YAML 1.2\n---\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC ---", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- …and REFUSED where the implicit continuation would have to carry it, which
-- is why the residue is a missing witness and not a missing refusal.
#guard refuses "a: 1\n%YAML 1.2\n---\nb: 2\n"

-- The two deleted extenders' family, carried by the flow-open stack since
-- items 44–46: a completed top-level flow collection is still a document.
#guard emits "[1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard emits "{a: b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "# c\n[1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]

/-! ## §2 `pendingDocStart` carries a ROUTE

The field's type is the whole of the change: given the content evidence after
`---`, it produces the extended STREAM rather than the document the consumers
then had to place. -/

example {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}
    (h_doc_route : ∀ sp_end,
      GAlt SLBareDocument (GSeq SENode SSLComments) sp_scan sp_end →
      SLYamlStream sp_start sp_end)
    (h_nic : sc.needIndentCheck = false)
    (h_real : LastTokenReal sc.tokens)
    (h_marker_tail : ∃ t, lastRealToken? sc.tokens = some t ∧
      t.val = .documentStart ∧ t.pos.line = sc.line)
    -- Item 293: the armed half alone — the `---` scan re-arms and clears.
    (h_arm : sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false)
    -- Item 138: and the park's directive face — `scanDocumentStart` clears the
    -- flag, so a `---` park is not directive-eligible.
    (h_nodir : sc.allowDirectives = false)
    -- Item 207: and the park's own indent check, which both producers pay from
    -- `[203]`'s three columns.
    (h_nic0 : sp_scan.col = 0 → sc.needIndentCheck = true)
    -- Item 299: and the marker's line as the scanner's field reads it.
    (h_docline : sc.docStartLine = some sc.line)
    -- Item 320: and the dead register the marker leaves (lane (e)'s field).
    (h_noek : sc.explicitKeyLine = none)
    (h_next : sc.inFlow = false → NextIsSep sc) (h_ntop : sc.currentIndent < 0) :
    PendingNode sc false sp_start sp_block sp_scan :=
  PendingNode.pendingDocStart (h_next := h_next) (h_ntop := h_ntop) sp_start sp_block sp_scan h_doc_route
    h_nic h_real h_marker_tail h_arm h_nodir h_nic0 h_docline h_noek

-- The `[208]` producer's own payment: `l-explicit-document` is what the
-- implicit continuation takes, so this arm spends the constructor and stays
-- legal under the tightening.
example {sp_start sp_block sp' : SurfPos}
    (h_stream : SLYamlStream sp_start sp_block)
    (h_marker : SCDirectivesEnd sp_block sp') :
    ∀ sp_end, GAlt SLBareDocument (GSeq SENode SSLComments) sp' sp_end →
      SLYamlStream sp_start sp_end :=
  fun sp_end h_content =>
    SLYamlStream.implicitContinue sp_start sp_block sp_block sp_end sp_end
      h_stream (GStar.nil _)
      (GOpt.some sp_block sp_end
        (SLAnyDocument.explicit sp_block sp_end
          (SLExplicitDocument.withContent sp_block sp' sp_end h_marker h_content)))
      (GStar.nil _)

-- The consumers' interface did not move: closing a park on `[79] s-l-comments`
-- still takes the stream and the comments and returns the stream.  What moved
-- is that the `pendingDocStart` arm now APPLIES the route instead of rebuilding
-- `[211]`'s term around a document it cannot classify.
-- [Item 157 adds the park's FACE to the close: a `pendingContent` whose run
-- is §9.2-dangling has no `[211]` reading, so the premise states the landing
-- has already refused it.  Every other constructor ignores it.]
example {sc : ScannerState} {sp_start sp_block sp_scan sp_mid : SurfPos}
    (h_pending : PendingNode sc false sp_start sp_block sp_scan)
    (h_stream : SLYamlStream sp_start sp_block)
    (h_nd : danglingNodePos? sc = none)
    -- Item 275: §8.1's silence, carried beside it.
    (h_ui : underIndentedFlowValuePos? sc = none)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_noflow : sc.inFlow = false) :
    SLYamlStream sp_start sp_mid :=
  h_pending.close_with_ssl h_stream h_nd h_ui h_noflow h_ssl

/-! ## §3 `h_nodoc` without the flag premise

Item 116 wrote `inFlow = false → documentEverStarted = false → …` because the
two premises name the constructor's two producer families.  They do — but the
seven flow-interior sites refute on `inFlow` ALONE and the seed pays
unconditionally, so the second premise was load-bearing at neither producer,
while at every consumer it is a scanner-state fact nothing threads.  Off it
comes, and the field becomes spendable. -/

example {sc : ScannerState} {sp_start sp : SurfPos}
    (h_col : sp.col = 0 ∨ sc.inFlow = true)
    (h_arm : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ sc.inFlow = true)
    (h_nodoc : sc.inFlow = false → GStar SLDocumentPrefix sp_start sp)
    -- Item 186: and the register face, the same premise on the scanner side.
    (h_noek : sc.inFlow = false → sc.explicitKeyLine = none)
    -- Item 208: and the stack face, paid by the same split of the same eight.
    (h_ntop : sc.inFlow = false → sc.currentIndent < 0)
    (h_gate : sc.inFlow = false → sp.col ≠ 0 → ¬(Proofs.ScannerCoupling.CommentOk sc ∧ sc.peek? = some '#')) :
    PendingNode sc false sp_start sp sp :=
  PendingNode.noPending sp_start sp h_col h_arm h_nodoc h_noek h_ntop h_gate

-- The flow producers pay exactly as before, from the one fact all seven hold.
example {sc : ScannerState} {n : Nat} {sp_start sp : SurfPos}
    (h_fl1 : sc.flowLevel = n + 1) :
    sc.inFlow = false → GStar SLDocumentPrefix sp_start sp :=
  nodoc_of_flowLevel_succ h_fl1

-- The seed pays the real witness, the premise ignored.
example (input : String) :
    ∃ sp, GStar SLDocumentPrefix ⟨input.toList, 0⟩ sp ∧
          SLYamlStream ⟨input.toList, 0⟩ sp := by
  obtain ⟨sp, h_stream, -, -, h_prefix⟩ := initial_stream_and_prefix input
  exact ⟨sp, h_prefix, h_stream⟩

/-! ## §4 The seed's root sequence, through `single`

Both faces `accum_block_on_noPending` builds — the entry alone and the entry
with its `[186]` tail — reach the stream without `implicitContinue`: the
prefixes ARE the whole region in front, so `[211]`'s first alternative carries
the document and no earlier document has to be invented to continue from. -/

example {sp_start sp_block sp_mid sp_final : SurfPos} {k : Nat}
    (h_nodoc : GStar SLDocumentPrefix sp_start sp_block)
    (h_ssl : SSLComments sp_block sp_mid)
    (h_entries : SBlockSeqEntries k sp_mid sp_final) :
    SLYamlStream sp_start sp_final :=
  SLYamlStream.single sp_start sp_block sp_final sp_final
    h_nodoc
    (GOpt.some sp_block sp_final
      (SLAnyDocument.bare sp_block sp_final
        (SLBareDocument.mk sp_block sp_final (rootBlockSeq k h_ssl h_entries))))
    (GStar.nil _)

-- And the witness reaches the landing over the same `[79] s-l-comments` the
-- park's own close absorbs (item 116's extension, now with one premise fewer
-- in front of it).
example {sc : ScannerState} {sp_start sp sp_land : SurfPos}
    (h_nodoc : sc.inFlow = false → GStar SLDocumentPrefix sp_start sp)
    (h_block : sc.inFlow = false)
    (h_ssl : SSLComments sp sp_land)
    (h_col0 : sp.col = 0) :
    GStar SLDocumentPrefix sp_start sp_land :=
  ssl_comments_extend_prefixes (h_nodoc h_block) h_col0 h_ssl

/-! ## §5 The surface that remains

Seven `SLAnyDocument.bare` applications, each owing a route decision:

* `topLevelFlowResumeSep` — the completed top-level flow node.  Its suffix twin
  exists (`suffixFlowResumeSep`, item 118); ~~the head twin does not~~ **the
  head twin is `nodocFlowResumeSep`, item 136**, and the virgin park's flow open
  spends it.
* `rootMapRoute` and `rootMapRouteF` — the fallback every punting park uses.
  BOTH twins exist on both faces (`nodocMapRoute`/`nodocMapRouteF`, item 116;
  `suffixMapRoute`/`suffixMapRouteF`, item 117) ~~and neither `nodoc` twin has a
  consumer yet: what is missing is the FACE at the landing, a real disjunction
  where `h_sfx_land` today carries `SuffixRun … ∨ True`~~ — **item 136 gave the
  landing its HEAD arm** (`colon_open_map`/`question_open_map` take it,
  `flowKeyRoute_of_root` takes it, `content_dispatch_routed`'s cascade prefers
  the matching key context), so both `nodoc` twins have consumers.  What is
  still `∨ True` is the FALLBACK, and what it owes is not a fourth route but
  items 132–134's refusal.
* `accum_block_on_closeThenBlock` and `content_dispatch_after_close` — the two
  landing skeletons, whose suffix arm routes through `suffixNodeRoute` and whose
  other arm is the bare document.
* `accum_content_pending`, twice — the same landing at the two column cases.

Plus the two that decide nothing: `structural_dispatch_after_directives` passes
`[209]`, which wants the head or the suffix arm and carries no witness of either
(`pendingDirective` records none — its producers hold the stream and nothing
else); and `structural_dispatch_to_pending` passes `[208]` through the
`SLAnyDocument.explicit` wrapper, which the flip deletes.

What the seven are waiting on is one carrier, not seven: the landings' `∨ True`
made into a three-way face — the stream's head, an open suffix run, or a level
resumed — with the fourth case refuted rather than carried.  That fourth case is
what items 132–134 made refusable: a completed root node followed by content
with no marker between is `invalidBareDocument` at the SCANNER now.

**Item 136 built the head arm and paid it**; the count stayed at nine, because
the seven are the fallback ARMS of lemmas several families share and an arm goes
only when its last caller can pay something else.  See `StreamHeadLandingFace`
for what each of the three remaining families is, and why the refutation rather
than a fourth route is what they owe. -/

end L4YAML.Tests.Guards.StreamRouteSwapSurface

end Blanket
