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

/-! # The suffix state's mirror carrier (DOCS item 117)

Item 116 paid the "no document started" carrier and named its residue in the
paid carrier's place: a `...` parks `pendingDocEnd`, whose close folds the
marker into `[211]`'s `suffixContinue` with the `l-any-document?` slot
already empty — so the next bare document could only ride `implicitContinue`
as a document the parser never starts (1c's over-approximation, again).

**The build holds the suffix arm OPEN across the landing.**  The landing
skeleton (`h_defer_split`) takes a third face beside item 109's two: `h_sfx :
(∀ sp_m, SSLComments sp_scan sp_m → SuffixRun sp_start sp_m) ∨ True`, where
`SuffixRun` is `( l-document-suffix+ l-document-prefix* l-any-document? … )`
decomposed with its document slot not yet filled — a stream, `[205]`'s
`GPlus`, and `[202] l-document-prefix*`.  Only `pendingDocEnd` pays: the
marker it carries plus the landing's own `[79] s-l-comments` IS
`l-document-suffix`, and the stream behind the marker is the invariant's
own.  The spend is three twins beside `rootMapRoute`: `suffixMapRoute` /
`suffixMapRouteF` (the key-pack faces) and `suffixNodeRoute` (the completed
top-level node), each landing the document in `suffixContinue`'s own slot —
which row 19's 1c leaves untouched — and `content_dispatch_routed` prefers
the suffix context over the root one at both pack assemblies, exactly as it
prefers item 109's resume context.  Unlike item 116's, this carrier is
CONSUMED today: `...⏎a: 1`'s map, `...⏎hello`'s scalar and `...⏎&a x: 1`'s
props run all route through the open arm.  Zero runtime edits.

§1 is the family at the runtime; §2–§4 are the decomposition, the park's
payment and the landing extension at their types; §5 is the spend; §6 is
what this item does not close. -/

namespace L4YAML.Tests.Guards.ScannerSuffixRunCarrier

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

-- §1 The family the carrier serves: a bare document landing after a suffix
-- run.  Item 116 pinned the first three as its residue; they are the open
-- arm's own inhabitants now.
#guard emits "...\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "...\n...\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "a: 1\n...\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The landing may cross comment lines and blank lines — `[202]`'s prefixes,
-- the decomposition's third leg…
#guard emits "...\n# c\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "...\n\n\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- …the run may hold more than one marker (`[205]`'s `GPlus` is per park:
-- each `...` chains its own `suffixContinue`, the LAST one open)…
#guard emits "a: 1\n...\n...\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- …and the marker's own line takes a comment (`[204] s-l-comments`).
#guard emits "a: 1\n... # done\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
-- The stream behind the marker is whatever accumulated: explicit documents,
-- repeated suffix arms, a BOM seed.
#guard emits "---\na: 1\n...\nb: 2\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]
#guard emits "a: 1\n...\nb: 2\n...\nc: 3\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC ...",
   "+DOC", "+MAP", "=VAL :c", "=VAL :3", "-MAP", "-DOC", "-STR"]
#guard emits "﻿...\na: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- The content dispatch's OTHER document shapes ride the same open arm
-- through `suffixNodeRoute` and the props context: a plain-scalar document
-- and a props-headed mapping.
#guard emits "...\nhello\n"
  ["+STR", "+DOC", "=VAL :hello", "-DOC", "-STR"]
#guard emits "...\n&a x: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :x", "=VAL :1", "-MAP", "-DOC", "-STR"]
-- A suffix run with NO next document is `close_with_ssl`'s empty-slot fold,
-- which stays honest — the arm's slot is `l-any-document?`.
#guard emits "...\n" ["+STR", "-STR"]

-- The parks a suffix does NOT feed keep their own routes: an explicit `---`
-- (its document survives 1c's tightening in `implicitContinue`'s slot) and a
-- directive document (`...` re-arms `allowDirectives`).
#guard emits "...\n---\na: 1\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC", "-STR"]
#guard emits "a: 1\n...\n%YAML 1.2\n---\nb: 2\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC ---", "+MAP", "=VAL :b", "=VAL :2", "-MAP", "-DOC", "-STR"]

-- §1-residue: a suffix followed by a BLOCK-INDICATOR or FLOW document lands
-- through the other dispatches (`accum_block_on_closeThenBlock`, the flow
-- open), which still fold the park and ride `implicitContinue`.  Pinned as
-- ACCEPTED: 1c residue families, not refusals.
-- (CLOSED by item 118 — the same face read at both skeletons; see
-- `ScannerSuffixCollectionLanding`.)
#guard emits "- x\n...\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :x", "-SEQ", "-DOC ...",
   "+DOC", "+SEQ", "=VAL :y", "-SEQ", "-DOC", "-STR"]
#guard emits "...\n[1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]

-- What the scanner refuses around the marker: content on the marker's line,
-- and a bare document glued to it (a col-0 plain scalar behind a started
-- document is §9.2's refusal, not a suffix at all).
#guard refuses "a: 1\n... x\nb: 2\n"
#guard refuses "a: 1\n...x\n"

/-! ## §2 The decomposition: `[211]`'s suffix arm held open

`SuffixRun` is the arm's three consumed legs with the `l-any-document?` slot
not yet filled — exactly what `suffixContinue` takes before its last two
arguments. -/

example {sp_start sp₁ sp₂ sp : SurfPos}
    (h_stream : SLYamlStream sp_start sp₁)
    (h_plus : GPlus SLDocumentSuffix sp₁ sp₂)
    (h_pre : GStar SLDocumentPrefix sp₂ sp) :
    SuffixRun sp_start sp :=
  ⟨sp₁, sp₂, h_stream, h_plus, h_pre⟩

-- Closing the open run with an empty slot recovers exactly what
-- `close_with_ssl`'s fold produces — holding it open loses nothing.
example {sp_start sp : SurfPos} (h_sfx : SuffixRun sp_start sp) :
    SLYamlStream sp_start sp :=
  match h_sfx with
  | ⟨sp₁, sp₂, h_stream, h_plus, h_pre⟩ =>
    SLYamlStream.suffixContinue sp_start sp₁ sp₂ sp sp sp
      h_stream h_plus h_pre (GOpt.none _) (GStar.nil _)

/-! ## §3 The park's payment

The `...` park pays the skeleton's face from the two things it stands on:
its own marker, and the stream the invariant threads behind it.  The
landing's `[79] s-l-comments` completes `[205] l-document-suffix` — this is
the same closing data `close_with_ssl` folds, handed over undischarged. -/

example {sp_start sp_block sp_scan : SurfPos}
    (h_stream : SLYamlStream sp_start sp_block)
    (h_marker : SCDocumentEnd sp_block sp_scan) :
    ∀ sp_m, SSLComments sp_scan sp_m → SuffixRun sp_start sp_m :=
  fun sp_m h_ssl =>
    ⟨sp_block, sp_m, h_stream,
     GPlus.mk sp_block sp_m sp_m
       (SLDocumentSuffix.mk sp_block sp_scan sp_m h_marker h_ssl) (GStar.nil _),
     GStar.nil _⟩

/-! ## §4 The landing extension

Comment lines crossed after the suffix are `[202] l-document-prefix`'s own —
the decomposition's prefix leg absorbs them and the run stays open,
`ssl_comments_extend_prefixes`' shape on the third leg. -/

example {sp_start sp sp_land : SurfPos}
    (h_sfx : SuffixRun sp_start sp)
    (h_ssl : SSLComments sp sp_land)
    (h_col0 : sp.col = 0) :
    SuffixRun sp_start sp_land :=
  ssl_comments_extend_suffixRun h_sfx h_col0 h_ssl

/-! ## §5 The spend: `rootMapRoute`'s interfaces off the open arm

The route chain, end to end: from the park's marker, the stream BEHIND it
and the landing, all three of the root context's faces — the map route, its
resume twin and the completed-node route — with the landing's FOLDED stream
(`SLYamlStream sp_start sp_land`) nowhere in the derivation.  Where the fold
could only append the next document as `implicitContinue`'s unmarked
continuation, these land it in `suffixContinue`'s own `l-any-document?`
slot, which 1c's tightening leaves untouched.  This is the route
`content_dispatch_routed` now prefers over the root context whenever the
park that closed at the landing was a `...`. -/

example {sp_start sp_block sp_scan sp_land sp_key : SurfPos} {k : Nat}
    (h_stream : SLYamlStream sp_start sp_block)
    (h_marker : SCDocumentEnd sp_block sp_scan)
    (h_ssl : SSLComments sp_scan sp_land)
    (hcol0 : sp_land.col = 0)
    (h_ind : SIndent k sp_land sp_key) :
    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧
    (∀ sp_v, SBlockMapEntry k sp_key sp_v →
     ∀ sp_e, SCompactMapTail k sp_v sp_e →
     ResumeFrames (SLYamlStream sp_start) [] sp_e) ∧
    (∀ sp_m, SBlockNode 0 .blockIn sp_land sp_m → SLYamlStream sp_start sp_m) :=
  have h_sfx : SuffixRun sp_start sp_land :=
    ⟨sp_block, sp_land, h_stream,
     GPlus.mk sp_block sp_land sp_land
       (SLDocumentSuffix.mk sp_block sp_scan sp_land h_marker h_ssl) (GStar.nil _),
     GStar.nil _⟩
  ⟨suffixMapRoute hcol0 h_sfx h_ind,
   suffixMapRouteF hcol0 h_sfx h_ind,
   suffixNodeRoute h_sfx⟩

/-! ## §6 What this item does NOT close

* The BLOCK-INDICATOR landing after a suffix.  `...⏎- y` and `...⏎? a`
  reach `accum_block_on_closeThenBlock`, which folds the park through
  `close_with_ssl` before the entry routes are built — the sequence document
  still rides `implicitContinue` (§1's `- x⏎...⏎- y` pin).  Paying it is
  the same face read at the block skeleton.
  (CLOSED by item 118 — `h_docRoute` plus the openers' suffix faces; see
  `ScannerSuffixCollectionLanding`.)
* The FLOW open after a suffix.  `...⏎[1, 2]` folds the park at the `[` and
  the completed collection re-enters through `topLevelFlowResumeSep` — 67b's
  rows, one more reason the flow base routes are a carrier question.
  (CLOSED by item 118 — `suffixFlowResumeSep` + `flowKeyRoute_of_root`'s
  landing face, without touching 67b's rider.)
* The EOF close.  `close_with_ssl`'s `pendingDocEnd` arm keeps the
  empty-slot fold — honest, because there IS no next document (§2's second
  example is that fold recovered from the open run).
* The 16 sites and the constructor.  `rootMapRoute` and its kin still spend
  `implicitContinue`'s bare slot wherever no suffix (and no virgin-stream
  witness, item 116) serves; 1c's tightening stays LAST, its raised-flag
  fallback now split between this carrier (a suffix intervened) and the
  scanner's refusals (none did). -/

end L4YAML.Tests.Guards.ScannerSuffixRunCarrier

end Blanket
