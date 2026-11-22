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

/-! # The block/flow landings after a suffix (DOCS item 118)

Item 117 held the `...` park's suffix arm open across the CONTENT landing and
named its residue at the other skeletons: a block indicator or a flow bracket
after a suffix reached `accum_block_on_closeThenBlock` or the flow open
(`accum_flow_open_depth0`), both of which folded the park through
`close_with_ssl` — slot already empty — before any route was built, so the
collection document could only ride `implicitContinue` as a document the
parser never starts (1c's over-approximation at those dispatches).

**The build reads item 117's face at both skeletons.**
`accum_block_on_closeThenBlock` takes the same `h_sfx` the content skeleton
does and hoists ONE document route at the landing (`h_docRoute` — the open
arm's slot for a `...` park, the fresh bare document otherwise); the landed
`-`'s three completions spend it, and the landed `:`/`?` hand the
instantiated face through `indicator_open_map` into `colon_open_map` /
`question_open_map`, whose entry routes are `suffixMapRoute` /
`suffixMapRouteF` off the face (`rootMapRoute`'s body was inlined there
before the twins existed).  The flow open's `main` takes the face, its value
route is the new `suffixFlowResumeSep` — `topLevelFlowResumeSep` with
`SuffixRun` in the stream hypothesis's place — and the root-key reading
(`...⏎[1]: b`) chooses `suffixMapRoute` inside `flowKeyRoute_of_root`'s
landing arm.  Only `pendingDocEnd`'s arms pay, with the SAME payment as the
content skeleton's: the marker plus the landing's `[79] s-l-comments` is
`[205] l-document-suffix`.  Zero runtime edits.

§1 is the family at the runtime; §2–§3 are the two route chains at their
types, with the landing's FOLDED stream nowhere in the derivation; §4 is
what this item does not close. -/

namespace L4YAML.Tests.Guards.ScannerSuffixCollectionLanding

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

-- §1 The block-indicator families: a `-`, `:` or `?` document after a
-- suffix run.  The first two were items 116/117's pinned residue; they land
-- through `h_docRoute`'s open arm now.
#guard emits "...\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :y", "-SEQ", "-DOC", "-STR"]
#guard emits "- x\n...\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :x", "-SEQ", "-DOC ...",
   "+DOC", "+SEQ", "=VAL :y", "-SEQ", "-DOC", "-STR"]
#guard emits "...\n- y\n- z\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :y", "=VAL :z", "-SEQ", "-DOC", "-STR"]
-- Multi-marker runs chain per park (item 117's reading, unchanged here) and
-- the landing may cross comment lines — `[202]`'s prefixes.
#guard emits "...\n...\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :y", "-SEQ", "-DOC", "-STR"]
#guard emits "...\n# c\n- y\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :y", "-SEQ", "-DOC", "-STR"]
#guard emits "---\na: 1\n...\n- y\n"
  ["+STR", "+DOC ---", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+SEQ", "=VAL :y", "-SEQ", "-DOC", "-STR"]
-- …and the sequence document may itself end on a marker.
#guard emits "...\n- y\n...\n"
  ["+STR", "+DOC", "+SEQ", "=VAL :y", "-SEQ", "-DOC ...", "-STR"]
-- The `:`/`?` openers: `[189]`'s empty-key entry and `[186]`'s explicit key,
-- routed through `colon_open_map`/`question_open_map`'s suffix faces.
#guard emits "...\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "...\n? k\n: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "...\n? k\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :", "-MAP", "-DOC", "-STR"]

-- The FLOW families: a bracketed document after a suffix, landed through
-- `suffixFlowResumeSep` at the flow open.
#guard emits "...\n[1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard emits "a: 1\n...\n[1, 2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard emits "...\n{a: b}\n"
  ["+STR", "+DOC", "+MAP {}", "=VAL :a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "...\n# c\n[1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
#guard emits "...\n...\n[1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
-- An indented bracket still lands: the whites ride the bare document's
-- separator slot, exactly as at a fresh stream.
#guard emits "...\n  [1, 2]\n"
  ["+STR", "+DOC", "+SEQ []", "=VAL :1", "=VAL :2", "-SEQ", "-DOC", "-STR"]
-- The collection as the next document's KEY — `flowKeyRoute_of_root`'s
-- landing arm off the face (`suffixMapRoute` in `rootMapRoute`'s place).
#guard emits "...\n[1]: b\n"
  ["+STR", "+DOC", "+MAP", "+SEQ []", "=VAL :1", "-SEQ", "=VAL :b",
   "-MAP", "-DOC", "-STR"]

-- A block-scalar document after a suffix needs NOTHING from this item: the
-- content skeleton's routed dispatch parks its completion on the `h_route`
-- item 117 already switched, so these compose since that item.
#guard emits "...\n|\n  x\n"
  ["+STR", "+DOC", "=VAL |x\\n", "-DOC", "-STR"]
#guard emits "a: 1\n...\n|\n  x\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-DOC ...",
   "+DOC", "=VAL |x\\n", "-DOC", "-STR"]

-- What the scanner refuses: an indicator or bracket on the marker's OWN line
-- (`[204]` ends it with `s-l-comments`)…
#guard refuses "... - y\n"
#guard refuses "... [1, 2]\n"
#guard refuses "... : v\n"
-- …and a marker GLUED to a bracket is no marker at all — `[206] c-forbidden`
-- wants a break, a white or EOF after `...`, so the plain walk absorbs the
-- whole line as a scalar.
#guard emits "...[1, 2]\n"
  ["+STR", "+DOC", "=VAL :...[1, 2]", "-DOC", "-STR"]

/-! ## §2 The block route chain

From the park's marker, the stream BEHIND it and the landing: a root
sequence's entries land in `suffixContinue`'s own `l-any-document?` slot —
`h_docRoute`'s open arm is `suffixNodeRoute` over `rootBlockSeq`, and the
landing's FOLDED stream (`SLYamlStream sp_start sp_land`) is nowhere in the
derivation. -/

example {sp_start sp_block sp_scan sp_land : SurfPos} {k : Nat}
    (h_stream : SLYamlStream sp_start sp_block)
    (h_marker : SCDocumentEnd sp_block sp_scan)
    (h_ssl : SSLComments sp_scan sp_land)
    (hcol0 : sp_land.col = 0) :
    ∀ sp_e, SBlockSeqEntries k sp_land sp_e → SLYamlStream sp_start sp_e :=
  have h_sfx : SuffixRun sp_start sp_land :=
    ⟨sp_block, sp_land, h_stream,
     GPlus.mk sp_block sp_land sp_land
       (SLDocumentSuffix.mk sp_block sp_scan sp_land h_marker h_ssl) (GStar.nil _),
     GStar.nil _⟩
  fun sp_e h_entries =>
    suffixNodeRoute h_sfx sp_e
      (rootBlockSeq k (sslComments_refl_of_col0 hcol0) h_entries)

-- The `:`/`?` openers and the flow-key reading spend the SAME twins the
-- content landing spends (`suffixMapRoute`/`suffixMapRouteF`, guard 117 §5)
-- — what this item wired is the face that REACHES them, not a new route.

/-! ## §3 The flow route chain

`suffixFlowResumeSep`, end to end: the completed flow collection wrapped as
`[195] s-l+flow-in-block` inside the bare document the open suffix arm
awaits — again with the folded stream nowhere. -/

example {sp_start sp_block sp_scan sp_land sp_br : SurfPos}
    (h_stream : SLYamlStream sp_start sp_block)
    (h_marker : SCDocumentEnd sp_block sp_scan)
    (h_ssl : SSLComments sp_scan sp_land)
    (h_sep : SSeparateLines 0 sp_land sp_br) :
    ∀ sp_ne sp_m, SFlowContent 0 .flowOut sp_br sp_ne →
      SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m :=
  suffixFlowResumeSep
    ⟨sp_block, sp_land, h_stream,
     GPlus.mk sp_block sp_land sp_land
       (SLDocumentSuffix.mk sp_block sp_scan sp_land h_marker h_ssl) (GStar.nil _),
     GStar.nil _⟩
    h_sep

/-! ## §4 What this item does NOT close

* The raised-flag REFUSAL half.  1c's tightening splits `implicitContinue`'s
  old fallback between the suffix carrier (a `...` intervened — items 117 and
  this one) and the scanner's own refusals (none did → §9.2's
  `trailingContent` family); the refusal half has no carrier yet and is the
  tightening's remaining prerequisite beside the constructor.
* The 16 sites and the constructor (LAST — item 110's measurement).
  `rootMapRoute` and its kin still spend `implicitContinue`'s bare slot
  wherever no suffix and no virgin-stream witness (item 116) serves.
* The EOF close stays the honest empty-slot fold — there IS no next document
  (guard 117 §2). -/

end L4YAML.Tests.Guards.ScannerSuffixCollectionLanding

end Blanket
